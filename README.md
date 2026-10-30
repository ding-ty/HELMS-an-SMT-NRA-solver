# HELMS

Mathematica 14.0; Python 3.11+ for data verification.

```wolfram
Get["solvers/paper solvers/HELMS.wl"];
Clear[x, y];
HELMS`Solve[(x^2 + y^2 < 1 || x - y > 2) && (x > 0 || y > 0), {x, y}]
```

[Data](data/README.md) · [Evidence](data/evidence/index.json)

```text
python data/check_evidence.py
```
