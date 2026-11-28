#!/usr/bin/env python3
"""Independent exact check of QC-1 (Sra's quantum coupon-collector conjecture).

Builds the six 3x3 matrices X_i = w_i u_i u_i^T + I/100, checks each is
positive definite (leading principal minors), forms Q_6 with exact adjugate
inverses of every subset sum, and evaluates v^T Q_6 v for v = (4, 1, 3).
Uses only fractions.Fraction; it does not read the Lean file.
"""
from fractions import Fraction as F
from itertools import combinations

U = [(-1, 2, 1), (0, -3, 1), (-3, -2, 0), (2, -2, -2), (-1, 0, 2), (-1, 3, 0)]
W = [10, 10, 100, 100, 100, 100]
V = (4, 1, 3)


def mat(i):
    return [[F(W[i] * U[i][r] * U[i][c]) + (F(1, 100) if r == c else 0) for c in range(3)] for r in range(3)]


def det(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def inv(a):
    d = det(a)
    assert d != 0
    cof = [[(-1) ** (r + c) * det2(a, r, c) for c in range(3)] for r in range(3)]
    return [[cof[c][r] / d for c in range(3)] for r in range(3)]


def det2(a, r, c):
    m = [[a[i][j] for j in range(3) if j != c] for i in range(3) if i != r]
    return m[0][0] * m[1][1] - m[0][1] * m[1][0]


def pd(a):
    return all(a[r][c] == a[c][r] for r in range(3) for c in range(3)) and \
        a[0][0] > 0 and a[0][0] * a[1][1] - a[0][1] * a[1][0] > 0 and det(a) > 0


Xs = [mat(i) for i in range(6)]
assert all(pd(x) for x in Xs)
Q = [[F(0)] * 3 for _ in range(3)]
for k in range(1, 7):
    for S in combinations(range(6), k):
        A = [[sum(Xs[i][r][c] for i in S) for c in range(3)] for r in range(3)]
        B = inv(A)
        for r in range(3):
            for c in range(3):
                Q[r][c] += (-1) ** (k + 1) * B[r][c]
val = sum(V[r] * Q[r][c] * V[c] for r in range(3) for c in range(3))
assert -96 < val < -95, float(val)
print("all X_i positive definite; v^T Q_6 v =", float(val), "(exact value in (-96, -95))")
print("leading minors of Q_6:", float(Q[0][0]), float(Q[0][0] * Q[1][1] - Q[0][1] * Q[1][0]), float(det(Q)))
