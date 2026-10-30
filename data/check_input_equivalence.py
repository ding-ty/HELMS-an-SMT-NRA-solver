"""Read-only exact checks of prepared input representations.

Run from any directory with ``python data/check_input_equivalence.py``.
Only the Python standard library is needed. This checks prepared CNFs and their
byte identities; it does not re-establish an upstream SMT2 conversion.
"""
import argparse
from collections import defaultdict
import csv
from fractions import Fraction
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tarfile
import zipfile


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, label):
    if not condition:
        raise ValueError(label)


def local_path(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root), 'Input path is outside the repository')
    return path


def read_csv(path):
    with path.open(encoding='utf-8-sig', newline='') as stream:
        return list(csv.DictReader(stream))


def tar_payloads(root, container, members):
    """Read only requested members, without filesystem extraction."""
    found = {}
    with tarfile.open(local_path(root, container), 'r|*') as archive:
        for entry in archive:
            if entry.name not in members:
                continue
            require(entry.isfile(), 'Requested archive member is not a file')
            require(entry.name not in found, 'Duplicate requested archive member')
            with archive.extractfile(entry) as stream:
                found[entry.name] = stream.read()
            if len(found) == len(members):
                break
    require(set(found) == set(members), 'A requested archive input is missing')
    return found


def multiply(left, right):
    """Multiply sparse polynomials over Q with named-variable monomials."""
    product = defaultdict(Fraction)
    for a, coefficient_a in left.items():
        for b, coefficient_b in right.items():
            powers = dict(a)
            for name, exponent in b:
                powers[name] = powers.get(name, 0) + exponent
            monomial = tuple(sorted(powers.items()))
            product[monomial] += coefficient_a * coefficient_b
    return {key: value for key, value in product.items() if value}


def coefficients(node, names):
    """Expand an audited exact arithmetic AST to its unique Q coefficient map."""
    operation = node['op']
    if operation == 'int':
        value = Fraction(int(node['value']))
        return {(): value} if value else {}
    if operation == 'rat':
        value = Fraction(int(node['numerator']), int(node['denominator']))
        return {(): value} if value else {}
    if operation == 'var':
        require(node['name'] in names, 'Undeclared polynomial variable')
        return {((node['name'], 1),): Fraction(1)}
    if operation == 'pow':
        exponent = node['exponent']
        require(type(exponent) is int and exponent >= 0, 'Invalid polynomial exponent')
        base = coefficients(node['base'], names)
        result = {(): Fraction(1)}
        while exponent:
            if exponent & 1:
                result = multiply(result, base)
            exponent >>= 1
            if exponent:
                base = multiply(base, base)
        return result
    require(operation in ('add', 'mul'), 'Unsupported polynomial AST operation')
    # Flatten the same operation before expansion. Left-associated sums from
    # original input conversion must not create quadratic copying or deep calls.
    pending = list(node['args'])
    if operation == 'add':
        result = defaultdict(Fraction)
        while pending:
            child = pending.pop()
            if child['op'] == operation:
                pending.extend(child['args'])
            else:
                for monomial, value in coefficients(child, names).items():
                    result[monomial] += value
        return {key: value for key, value in result.items() if value}
    result = {(): Fraction(1)}
    while pending:
        child = pending.pop()
        if child['op'] == operation:
            pending.extend(child['args'])
        else:
            result = multiply(result, coefficients(child, names))
    return result


def verify(root=None):
    root = Path(root or Path(__file__).resolve().parent.parent).resolve()
    index = json.loads((root / 'data/index.json').read_bytes())
    primary = read_csv(local_path(root, 'data/' + index['instances']))
    representations = read_csv(local_path(root, 'data/' + index['input_representations']))
    require(len(primary) == 2260, 'Expected 2260 primary inputs')
    require(len(representations) == 2349, 'Expected 2349 input representations')
    primary_by_case = {row['case_id']: row for row in primary}
    require(len(primary_by_case) == 2260, 'Duplicate primary case identity')
    by_case = defaultdict(list)
    for row in representations:
        by_case[row['case_id']].append(row)
    require(set(by_case) == set(primary_by_case), 'Representation case identities differ')
    require(len({(row['case_id'], row['input_sha256']) for row in representations}) == 2349,
            'Duplicate input representation')
    extra = []
    for case_id, variants in by_case.items():
        original = primary_by_case[case_id]
        originals = [row for row in variants if row['input_sha256'] == original['input_sha256']]
        require(len(originals) == 1,
                'Primary input representation is missing or duplicated')
        require(all(originals[0][key] == original[key] for key in
                    ('benchmark', 'input_container', 'prepared_input_member')),
                'Primary representation location differs from the primary index')
        require(all(row['benchmark'] == original['benchmark'] for row in variants),
                'Input representation benchmark differs')
        extra.extend(row for row in variants if row['input_sha256'] != original['input_sha256'])
    require(len(extra) == 89, 'Expected 89 alternative input encodings')
    nested = {(row['input_container'], row['input_zip_member']) for row in extra}
    require(len(nested) == 1, 'Expected one measured input ZIP')
    container, zip_member = next(iter(nested))
    if container.endswith('.zip') and not zip_member:
        nested_raw = local_path(root, container).read_bytes()
    else:
        require(bool(zip_member), 'Missing measured input ZIP member')
        nested_raw = tar_payloads(root, container, {zip_member})[zip_member]

    mapping = json.loads((root / 'benchmarks/default_input_map.json').read_bytes())
    conversions = {row['case_id']: row for row in mapping['conversion_records']}
    require(set(conversions) == {row['case_id'] for row in extra}, 'Default conversion scope differs')
    # Reuse the released restricted arithmetic parser; strings are not executed.
    saved_bytecode = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec = importlib.util.spec_from_file_location(
            '_helms_exact_input_parser', root / 'runner/prepare_default_inputs.py')
        parser = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(parser)
    finally:
        sys.dont_write_bytecode = saved_bytecode

    source_groups = defaultdict(set)
    for row in extra:
        original = primary_by_case[row['case_id']]
        source_groups[original['input_container']].add(original['prepared_input_member'])
    source_bytes = {}
    for source_container, members in source_groups.items():
        for member, raw in tar_payloads(root, source_container, members).items():
            source_bytes[source_container, member] = raw

    polynomial_count = 0
    unchanged = 0
    with zipfile.ZipFile(io.BytesIO(nested_raw)) as measured_zip, \
            zipfile.ZipFile(root / 'benchmarks/default_inputs.zip') as default_zip, \
            zipfile.ZipFile(root / 'benchmarks/inputs.zip') as original_zip:
        require(len(measured_zip.namelist()) == 2260, 'Measured ZIP input count differs')
        require(len(set(measured_zip.namelist())) == 2260, 'Duplicate measured ZIP member')
        for row in primary:
            if row['case_id'] in conversions:
                continue
            require(row['input_container'] == 'benchmarks/inputs.zip',
                    'Unexpected original input container')
            member = row['prepared_input_member']
            original_raw = original_zip.read(member)
            require(digest(original_raw) == row['input_sha256'], 'Original input hash mismatch')
            require(measured_zip.read(member) == original_raw, 'Measured original input differs')
            require(default_zip.read(member) == original_raw, 'Default original input differs')
            unchanged += 1
        for measured in extra:
            case_id = measured['case_id']
            original = primary_by_case[case_id]
            conversion = conversions[case_id]
            source_raw = source_bytes[original['input_container'], original['prepared_input_member']]
            require(digest(source_raw) == original['input_sha256'] == conversion['source_sha256'],
                    'Original alternative input hash mismatch')
            rebuilt = parser.convert_input(json.loads(source_raw))
            default_raw = default_zip.read(conversion['prepared_member'])
            require(parser.encoded(rebuilt) == default_raw, 'Restricted source conversion differs')
            require(digest(default_raw) == conversion['prepared_sha256'], 'Default AST hash mismatch')
            measured_raw = measured_zip.read(measured['prepared_input_member'])
            require(digest(measured_raw) == measured['input_sha256'], 'Measured AST hash mismatch')
            formula = json.loads(measured_raw)
            require(formula['variables'] == rebuilt['variables'], 'Variable order differs')
            require(formula['clauses'] == rebuilt['clauses'], 'Clause structure or order differs')
            require(len(formula['polynomials']) == len(rebuilt['polynomials']), 'Polynomial count differs')
            names = frozenset(rebuilt['variables'])
            for left, right in zip(rebuilt['polynomials'], formula['polynomials']):
                require(coefficients(left, names) == coefficients(right, names),
                        'Exact polynomial coefficient maps differ')
                polynomial_count += 1
    require(unchanged == 2171 and polynomial_count == 106151, 'Exact comparison scope differs')
    return {
        'passed': True,
        'distinct_inputs': 2260,
        'input_representations': 2349,
        'byte_identical_inputs': unchanged,
        'reencoded_inputs': len(extra),
        'polynomials_exactly_compared': polynomial_count,
        'variables_and_clauses_identical': True,
        'source_conversions_regenerated_byte_identically': True,
        'all_representation_payload_hashes_verified': True,
        'method': 'Restricted source parser and exact sparse polynomial coefficient maps over Q',
        'scope': 'Prepared CNFs and input encodings',
        'records_modified': False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, help='Repository root (defaults to this file location)')
    args = parser.parse_args()
    root = Path(args.root or Path(__file__).resolve().parent.parent).resolve()
    try:
        result = verify(root)
    except Exception as error:
        result = {'passed': False, 'error_type': type(error).__name__,
                  'error': str(error).replace(str(root), '<repository>')}
    print(json.dumps(result, indent=2))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
