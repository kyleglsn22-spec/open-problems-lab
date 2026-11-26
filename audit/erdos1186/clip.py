# Independent exact limit-density checker: polygon clipping of the arrangement
# u + i t = m/K (i=0..3) in [0,1]^2 with Fractions. Written from scratch for audit.
import json, sys, math
from fractions import Fraction as F
from collections import defaultdict
import numpy as np

def split(poly, A, B, C):
    """split convex polygon by A u + B t + C = 0; return (neg, pos) parts (may be None)."""
    vals = [A*u + B*t + C for (u, t) in poly]
    if all(v >= 0 for v in vals): return None, poly
    if all(v <= 0 for v in vals): return poly, None
    neg, pos = [], []
    n = len(poly)
    for k in range(n):
        P, Q = poly[k], poly[(k+1) % n]
        vp, vq = vals[k], vals[(k+1) % n]
        if vp <= 0: neg.append(P)
        if vp >= 0: pos.append(P)
        if (vp < 0 < vq) or (vq < 0 < vp):
            s = vp / (vp - vq)
            X = (P[0] + s*(Q[0]-P[0]), P[1] + s*(Q[1]-P[1]))
            neg.append(X); pos.append(X)
    return neg, pos

def area(poly):
    s = F(0)
    n = len(poly)
    for k in range(n):
        (x1, y1), (x2, y2) = poly[k], poly[(k+1) % n]
        s += x1*y2 - x2*y1
    return abs(s) / 2

def cells(K):
    polys = [[(F(0),F(0)),(F(1),F(0)),(F(1),F(1)),(F(0),F(1))]]
    lines = []
    for i in range(4):
        for m in range(1, (1+i)*K):
            lines.append((F(1), F(i), F(-m, K)))   # u + i t - m/K = 0
    for (A, B, C) in lines:
        new = []
        for P in polys:
            a, b = split(P, A, B, C)
            for q in (a, b):
                if q is not None and area(q) > 0: new.append(q)
        polys = new
    W = defaultdict(F)
    for P in polys:
        cu = sum(p[0] for p in P) / len(P); ct = sum(p[1] for p in P) / len(P)
        lab = []
        for i in range(4):
            s = cu + i*ct
            k = math.floor(s)
            j = math.floor(K*(s - k))
            # interior check: point must not lie on a line
            assert K*s != math.floor(K*s)
            lab.append((k, j))
        W[tuple(lab)] += area(P)
    assert sum(W.values()) == 1
    return W, len(polys)

def density(G, r, W):
    b, K = G.shape
    a0 = np.arange(b)[:, None]; d0 = np.arange(b)[None, :]
    tot = F(0)
    for lab, ar in W.items():
        cs = [G[(a0 + i*d0 - r*lab[i][0]) % b, lab[i][1]] for i in range(4)]
        n = int(((cs[0]==cs[1]) & (cs[0]==cs[2]) & (cs[0]==cs[3])).sum())
        tot += ar * F(n, b*b)
    return tot

if __name__ == "__main__":
    for K in (1, 2, 3):
        W, nc = cells(K)
        print(f"K={K}: {nc} polygons, {len(W)} label classes, total area 1")
    # Lu-Peng B20
    W1, _ = cells(1)
    B20 = np.array([1,1,1,0,1,1,0,1,1,1,0,0,0,1,0,0,1,0,0,0]).reshape(20, 1)
    vals = {r: density(B20, r, W1) for r in range(20) if math.gcd(r, 20) == 1}
    print("B20:", {r: str(v) for r, v in vals.items()})
    for fn in sys.argv[1:]:
        c = json.load(open(fn)); b, K = c["b"], c["K"]
        W, _ = cells(K)
        units = [r for r in range(b) if math.gcd(r, b) == 1]
        assert sorted(map(int, c["tables"])) == units
        worst = F(0)
        for r in units:
            s = c["tables"][str(r)]; assert len(s) == b*K and set(s) <= set("01")
            G = np.array(list(map(int, s))).reshape(b, K)
            v = density(G, r, W); worst = max(worst, v)
            print(f"  {fn} r={r}: {v} = {float(v):.9f}")
        print(f"{fn}: max = {worst} ({float(worst):.9f}); claimed {c['claimed_max']}; match={worst==F(c['claimed_max'])}")
