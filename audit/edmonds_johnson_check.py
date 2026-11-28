#!/usr/bin/env python3
"""Independent exact-arithmetic check of the Edmonds–Johnson results in Lab/EdmondsJohnson/.

Written separately from the Lean generator (explorer/edmonds-johnson/). Standard library only.
For each matrix A in {A6, A6+, A7} and the data (b, c, l, u, z) used in the Lean files it checks:

1. z lies in P(A; b, c, l, u).
2. z lies in the Chvátal closure, by the paper's criterion (Del Pia, Lemma 3.2, which rests on
   Appa–Kotnyek): every side has slack 1/3 or >= 1 at z, and the sides with slack 1/3 have
   pairwise distinct nonzero normals mod 2. (The Lean proof uses a different, duality-free route.)
   As a further cross-check, for every integral w in [-R, R]^n (R = 3 for n = 6, R = 2 for n = 7)
   it computes max_P w.x exactly over all vertices and checks floor(max) >= w.z.
3. z is not in the integer hull: it lists all integral points of P and checks the separating
   inequality w0.x <= r0 used in Lean holds for all of them, while w0.z > r0.
4. A is totally half-modular: every nonsingular square submatrix has a half-integral inverse
   (exact Gaussian elimination over the rationals).
"""
from fractions import Fraction as Fr
from itertools import combinations, product
from math import floor

def gauss_inverse(S):
    k = len(S)
    M = [[Fr(x) for x in row] + [Fr(int(i == j)) for j in range(k)] for i, row in enumerate(S)]
    for col in range(k):
        piv = next((r for r in range(col, k) if M[r][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        p = M[col][col]
        M[col] = [x / p for x in M[col]]
        for r in range(k):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [row[k:] for row in M]

def solve(S, rhs):
    inv = gauss_inverse(S)
    if inv is None:
        return None
    return [sum(inv[i][j] * rhs[j] for j in range(len(rhs))) for i in range(len(rhs))]

def sides(A, b, c, l, u):
    n = len(A[0])
    out = []
    for i, row in enumerate(A):
        out.append((list(row), Fr(c[i])))
        out.append(([-x for x in row], Fr(-b[i])))
    for j in range(n):
        e = [0] * n; e[j] = 1
        out.append((e, Fr(u[j])))
        out.append(([-x for x in e], Fr(-l[j])))
    return out

def dot(a, x):
    return sum(Fr(p) * q for p, q in zip(a, x))

def check(name, A, b, c, l, u, z, w0, r0):
    n = len(A[0])
    S = sides(A, b, c, l, u)
    slacks = [h - dot(nv, z) for nv, h in S]
    assert all(s >= 0 for s in slacks), "z not in P"
    tight = [tuple(x % 2 for x in nv) for (nv, h), s in zip(S, slacks) if s == Fr(1, 3)]
    assert all(s == Fr(1, 3) or s >= 1 for s in slacks), "slack condition fails"
    assert all(any(t) for t in tight) and len(set(tight)) == len(tight), "mod-2 condition fails"
    # vertices
    verts = set()
    for comb in combinations(range(len(S)), n):
        x = solve([S[i][0] for i in comb], [S[i][1] for i in comb])
        if x is not None and all(dot(nv, x) <= h for nv, h in S):
            verts.add(tuple(x))
    R = 3 if n <= 6 else 2
    for w in product(range(-R, R + 1), repeat=n):
        mx = max(dot(w, v) for v in verts)
        assert floor(mx) >= dot(w, z), ("CG cut violated", w)
    # integer hull
    pts = [x for x in product(*[range(l[j], u[j] + 1) for j in range(n)])
           if all(dot(nv, x) <= h for nv, h in S)]
    assert all(dot(w0, x) <= r0 for x in pts) and dot(w0, z) > r0, "separation fails"
    # total half-modularity
    m = len(A); nonsing = 0; total = 0
    for k in range(1, min(m, n) + 1):
        for R in combinations(range(m), k):
            for C in combinations(range(n), k):
                total += 1
                inv = gauss_inverse([[A[r][cc] for cc in C] for r in R])
                if inv is not None:
                    nonsing += 1
                    assert all((2 * x).denominator == 1 for row in inv for x in row), ("not THM", R, C)
    print(f"{name}: OK  ({len(verts)} vertices, {len(tight)} sides of slack 1/3, "
          f"{len(pts)} integral points, {total} square submatrices / {nonsing} nonsingular, "
          f"all half-integral)")

A6 = [[0,0,1,-1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
A6p = [[0,0,1,1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
A7 = [[0,0,1,-1,2,-2,2],[0,1,1,0,2,0,0],[0,1,0,1,0,2,0],[1,0,1,0,2,0,0],[1,0,0,1,0,2,0]]
t = lambda *ks: [Fr(k, 3) for k in ks]
check("A6", A6, [0,2,1,1,0], [2,4,3,3,2], [-1,0,-1,0,-1,-1], [1,2,1,2,2,2],
      t(2,1,2,1,2,1), [1,-1,0,0,0,0], 0)
check("A6+", A6p, [-2,-2,-1,-1,0], [0,0,1,1,2], [-1,-2,-1,0,-1,-1], [1,0,1,2,2,2],
      t(-2,-1,-2,1,1,1), [-1,1,0,0,0,0], 0)
check("A7", A7, [-1,-2,-2,-1,-1], [1,0,0,1,1], [-1,-2,-1,-1,-1,-1,-1], [1,0,1,1,2,2,2],
      t(-2,-1,-2,-2,1,1,1), [-1,1,0,-1,1,-1,1], 1)
