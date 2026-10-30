#!/usr/bin/env python3
"""Build the default input bundle from the byte-preserved benchmark evidence."""
from __future__ import annotations
import argparse
import ast
import csv
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True) + '\n').encode()


def integer(value):
    return {'op': 'int', 'value': str(value)}


def operation(op, *nodes):
    args = []
    for node in nodes:
        args.extend(node['args'] if node['op'] == op else [node])
    return {'op': op, 'args': args}


def constant(node):
    op = node['op']
    if op == 'int':
        return Fraction(int(node['value']))
    if op == 'rat':
        return Fraction(int(node['numerator']), int(node['denominator']))
    if op == 'add':
        return sum((constant(x) for x in node['args']), Fraction())
    if op == 'mul':
        value = Fraction(1)
        for arg in node['args']:
            value *= constant(arg)
        return value
    if op == 'pow':
        return constant(node['base']) ** node['exponent']
    raise ValueError('A polynomial denominator must be a nonzero rational constant')


def polynomial(text, variables):
    """Parse an audited arithmetic grammar; never execute a string or use eval."""
    def convert(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return integer(node.value)
        if isinstance(node, ast.Name) and node.id in variables:
            return {'op': 'var', 'name': node.id}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = convert(node.operand)
            return value if isinstance(node.op, ast.UAdd) else operation('mul', integer(-1), value)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                if not isinstance(node.right, ast.Constant) or type(node.right.value) is not int or node.right.value < 0:
                    raise ValueError('Only nonnegative integer polynomial exponents are supported')
                return {'op': 'pow', 'base': convert(node.left), 'exponent': node.right.value}
            left, right = convert(node.left), convert(node.right)
            if isinstance(node.op, ast.Add):
                return operation('add', left, right)
            if isinstance(node.op, ast.Sub):
                return operation('add', left, operation('mul', integer(-1), right))
            if isinstance(node.op, ast.Mult):
                return operation('mul', left, right)
            if isinstance(node.op, ast.Div):
                value = 1 / constant(right)
                factor = integer(value.numerator) if value.denominator == 1 else {
                    'op': 'rat', 'numerator': str(value.numerator), 'denominator': str(value.denominator)}
                return operation('mul', left, factor)
        raise ValueError('Unsupported polynomial syntax or undeclared variable')
    if not isinstance(text, str):
        raise ValueError('Polynomial text must be a string')
    return convert(ast.parse(text.replace('^', '**'), mode='eval').body)


def convert_input(source):
    variables = source['variables']
    if not isinstance(variables, list) or not all(isinstance(x, str) and x.isidentifier() for x in variables) or len(set(variables)) != len(variables):
        raise ValueError('Invalid or duplicate declared variable names')
    variable_set = set(variables)
    polys = [polynomial(s, variable_set) for s in source['polynomials']]
    clauses = source['clauses']
    if not isinstance(clauses, list) or not all(isinstance(c, list) for c in clauses):
        raise ValueError('Invalid clause list')
    for clause in clauses:
        for atom in clause:
            if (not isinstance(atom, list) or len(atom) != 2 or type(atom[0]) is not int or
                    type(atom[1]) is not int or not 1 <= atom[0] <= len(polys) or atom[1] not in (-1, 1)):
                raise ValueError('Invalid literal index/sign')
    return {'variables': variables, 'polynomials': polys, 'clauses': clauses}


def build():
    rows = [json.loads(line) for line in (ROOT/'benchmarks/experiment_all.jsonl').read_bytes().splitlines() if line.strip()]
    assert len(rows) == 2171 and len({r['case_id'] for r in rows}) == 2171
    with zipfile.ZipFile(ROOT/'benchmarks/inputs.zip') as old:
        members = {name: old.read(name) for name in old.namelist()}
    for row in rows:
        assert sha(members[row['input_path'].removeprefix('benchmarks/inputs/')]) == row['input_sha256']
    with (ROOT/'data/instances.csv').open(encoding='utf-8', newline='') as stream:
        additional = [r for r in csv.DictReader(stream) if not r['input_container'].endswith('.zip')]
    assert len(additional) == 89 and len({r['input_container'] for r in additional}) == 1
    required = {r['prepared_input_member']: r for r in additional}
    converted, mapping = {}, []
    with tarfile.open(ROOT/additional[0]['input_container'], 'r:gz') as archive:
        for member in archive:
            if member.name not in required:
                continue
            ref = required[member.name]
            raw = archive.extractfile(member).read()
            assert sha(raw) == ref['input_sha256']
            original = json.loads(raw)
            assert original['case_id'] == ref['case_id']
            data = convert_input(original)
            name = 'SMTLIB/additional/' + ref['case_id'] + '.json'
            assert name not in members
            normalized = encoded(data)
            converted[name] = normalized
            mapping.append(dict(case_id=ref['case_id'], source_container=ref['input_container'],
                source_member=member.name, source_sha256=sha(raw), prepared_member=name,
                prepared_sha256=sha(normalized), conversion='restricted_exact_arithmetic_to_AST_v1'))
            rows.append(dict(case_id=ref['case_id'], benchmark_group='SMTLIB',
                family=original['group'], expected_status='unknown', availability='ready',
                input_path='benchmarks/inputs/'+name, input_sha256=sha(normalized),
                variable_count=len(data['variables']), polynomial_count=len(data['polynomials']),
                clause_count=len(data['clauses']), source_input_sha256=sha(raw)))
    assert len(converted) == 89 and len(rows) == len({r['case_id'] for r in rows}) == 2260
    members.update(converted)
    bundle = io.BytesIO()
    with zipfile.ZipFile(bundle, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
        for name in sorted(members):
            info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, members[name], compresslevel=6)
    mapping.sort(key=lambda r: r['case_id'])
    return {'benchmarks/experiment_default.jsonl': b''.join(encoded(r) for r in rows),
            'benchmarks/default_inputs.zip': bundle.getvalue(),
            'benchmarks/default_input_map.json': encoded(dict(schema_version=1,
                original_inputs=2171, additional_inputs=89, default_inputs=2260,
                source_index='data/instances.csv', conversion_records=mapping))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-root', type=Path, default=ROOT)
    args = parser.parse_args()
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
    for name, raw in build().items():
        path = args.output_root/name
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists():
            if path.read_bytes() != raw:
                raise ValueError('Existing derived bundle differs; choose a new --output-root: '+name)
        else:
            with path.open('xb') as stream:
                stream.write(raw)
        print(json.dumps(dict(path=name, bytes=len(raw), sha256=sha(raw))))


if __name__ == '__main__':
    main()
