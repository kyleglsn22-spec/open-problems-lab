#!/usr/bin/env python3
"""Generate the solution table for Lab/QuantumCoupon/Data.lean.

For each nonempty S of {0..5}, solve (sum_{i in S} X_i) w_S = v exactly,
with X_i = wt_i * u_i u_i^T + (1/100) I and v = (4,1,3).  The Lean file then
checks X_S w_S = v by kernel computation, so this script is not trusted.
"""
from fractions import Fraction as F
import sys

U = [(-1, 2, 1), (0, -3, 1), (-3, -2, 0), (2, -2, -2), (-1, 0, 2), (-1, 3, 0)]
WT = [10, 10, 100, 100, 100, 100]
EPS = F(1, 100)
V = (4, 1, 3)


def X(i):
    u, w = U[i], WT[i]
    return [[F(w * u[r] * u[c]) + (EPS if r == c else 0) for c in range(3)] for r in range(3)]


def solve(A, b):
    M = [row[:] + [F(b[r])] for r, row in enumerate(A)]
    for c in range(3):
        p = next(r for r in range(c, 3) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [M[r][k] - f * M[c][k] for k in range(4)]
    return [M[r][3] / M[r][r] for r in range(3)]


def lit(q):
    q = F(q)
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} / {q.denominator} : ℚ)"


rows, total = [], F(0)
for mask in range(64):
    if mask == 0:
        rows.append("![0, 0, 0]")
        continue
    S = [i for i in range(6) if mask >> i & 1]
    A = [[sum(X(i)[r][c] for i in S) for c in range(3)] for r in range(3)]
    w = solve(A, V)
    total += (-1) ** (len(S) + 1) * sum(V[k] * w[k] for k in range(3))
    rows.append("![" + ", ".join(lit(x) for x in w) + "]")
print(f"-- quadratic form value ~ {float(total)}", file=sys.stderr)
print("def solTable : List (Fin 3 → ℚ) := [\n  " + ",\n  ".join(rows) + "]")
