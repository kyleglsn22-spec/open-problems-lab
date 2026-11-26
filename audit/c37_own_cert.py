"""Auditor's own certificate for claim C37-1 (Koshta 2026, degree 4, sensitivity 10).

Standard library only, exact arithmetic. Written from the definitions by the in-house Auditor,
without using PR 5's code. The multipliers were found by `c37_find_own_cert.py` (scipy LP,
then rationalised) and differ from PR 5's, which is a second, independent certificate.

Setup. Suppose q : {0,1}^10 -> {0,1}, deg q <= 4, q(0) = 0, q(e_i) = 1 for all i.
Write q = sum_S c_S x^S; every c_S is an integer (Moebius inversion). Split the
coordinates into A = {1..8} and B = {9,10}. For a + b <= 4 let C[a,b] = sum of c_S over
|S∩A| = a, |S∩B| = b (an integer). The average of q over the points with i ones in A and
j ones in B is avg(i,j) = sum C[a,b] binom(i,a) binom(j,b) / (binom(8,a) binom(2,b)),
and 0 <= avg(i,j) <= 1 because q is 0/1-valued. Also C[0,0]=0, C[1,0]=8, C[0,1]=2.
Below, two nonnegative combinations of these facts give C[1,2] >= 14/3 and C[1,2] <= 14/3,
so C[1,2] = 14/3, not an integer: no such q exists.
"""
from fractions import Fraction as F
from math import comb
nA, nB, d = 8, 2, 4
V = [(a, b) for b in range(nB + 1) for a in range(nA + 1) if a + b <= d]
T = (1, 2)
FIX = {(0, 0): 0, (1, 0): nA, (0, 1): nB}
# (form, point, multiplier). form "lo": avg >= 0 ; form "hi": 1 - avg >= 0
CERT = {
 ">=": [("hi",(0,2),"37/9"),("hi",(1,1),"16"),("hi",(2,0),"140/9"),("lo",(3,2),"56/9"),
        ("lo",(5,0),"28/9"),("hi",(6,2),"28/9"),("hi",(8,0),"5/9"),("lo",(8,2),"1")],
 "<=": [("hi",(1,1),"1040/21"),("hi",(2,0),"296/3"),("lo",(3,2),"104/15"),("lo",(4,1),"98/3"),
        ("lo",(5,0),"148/15"),("hi",(6,2),"40/3"),("hi",(7,1),"64/7"),("hi",(8,1),"1/7"),
        ("lo",(8,2),"32/5")],
}
def avg_form(i, j):
    coef = {v: F(0) for v in V}; const = F(0)
    for (a, b) in V:
        w = F(comb(i, a) * comb(j, b), comb(nA, a) * comb(nB, b))
        if (a, b) in FIX: const += w * FIX[(a, b)]
        else: coef[(a, b)] += w
    return coef, const
bounds = {}
for sense, items in CERT.items():
    tot = {v: F(0) for v in V}; k = F(0)
    for form, (i, j), m in items:
        m = F(m); assert m > 0
        co, cst = avg_form(i, j)
        s, kk = (1, cst) if form == "lo" else (-1, 1 - cst)
        for v in V: tot[v] += m * s * co[v]
        k += m * kk
    nz = {v: x for v, x in tot.items() if x}
    assert list(nz) == [T] and abs(nz[T]) == 1, nz      # combination is ±C[1,2] + k >= 0
    bounds[sense] = -k if nz[T] > 0 else k
    print("C[1,2]", sense, bounds[sense], "using", len(items), "multipliers")
assert bounds[">="] == bounds["<="] == F(14, 3)
print("C[1,2] = 14/3 is forced, not an integer: no degree-4 q with q(0)=0, q(e_i)=1 on 10 bits.")
print("Total multipliers:", sum(len(x) for x in CERT.values()))
