"""Exact limit density of monochromatic 4-APs for 'residue + position' colourings of Z_p.

Colouring (p prime, p = r mod b):  c(x) = G[x mod b, floor(K*x/p)]  for 0 <= x < p.
A 4-AP is any pair (a, d) in Z_p^2 (Lu-Peng convention; d = 0 included, it is O(1/p)).

For 0 <= a, d < p write u = a/p, t = d/p.  The i-th term is y_i = a + i*d - p*k_i with
k_i = floor(u + i t), and its position index is j_i = floor(K * frac(u + i t)).
So y_i mod b = (a mod b) + i (d mod b) - r k_i  (mod b).  The vector (k, j) is constant on
cells of the arrangement of lines u + i t = m/K (i = 0..3) in the unit square, and

  m4(Z_p, c) -> sum_cells area(cell) * #{(a0,d0) in Z_b^2 : the 4 colours agree} / b^2.

Cell areas are computed exactly: every crossing of two arrangement lines (or of a line with
the square's sides) has t in (1/(6K))Z, so on each strip m/(6K) < t < (m+1)/(6K) the cut points
in u move linearly and keep their order; the midpoint rule is then exact.
"""
from fractions import Fraction as Fr
import math
import numpy as np


def patterns(K):
    """dict (k0,j0,k1,j1,k2,j2,k3,j3) -> exact area (Fraction); areas sum to 1."""
    W = {}
    N = 6 * K
    for m in range(N):
        t = Fr(2 * m + 1, 2 * N)
        w = Fr(1, N)
        cuts = {Fr(0), Fr(1)}
        for i in range(4):
            for k in range(0, 4 * K + 1):
                v = Fr(k, K) - i * t
                v -= math.floor(v)
                if 0 < v < 1:
                    cuts.add(v)
        cuts = sorted(cuts)
        for lo, hi in zip(cuts, cuts[1:]):
            um = (lo + hi) / 2
            key = []
            for i in range(4):
                s = um + i * t
                kap = math.floor(s)
                key += [kap, math.floor((s - kap) * K)]
            key = tuple(key)
            W[key] = W.get(key, 0) + (hi - lo) * w
    assert sum(W.values()) == 1
    return W


def exact_density(G, r):
    """Exact limit density (Fraction) for colouring table G (b x K, entries 0/1), p = r mod b."""
    G = np.asarray(G)
    b, K = G.shape
    total = Fr(0)
    for key, area in patterns(K).items():
        kap, j = key[0::2], key[1::2]
        n = 0
        for a0 in range(b):
            for d0 in range(b):
                cols = {int(G[(a0 + i * d0 - r * kap[i]) % b, j[i]]) for i in range(4)}
                n += len(cols) == 1
        total += area * Fr(n, b * b)
    return total


class FastEval:
    """Floating-point version of exact_density for searches."""

    def __init__(self, b, K, r):
        self.b = b
        W = patterns(K)
        a0 = np.arange(b)[:, None]
        d0 = np.arange(b)[None, :]
        self.items = []
        for key, area in W.items():
            kap, j = key[0::2], key[1::2]
            idx = [((a0 + i * d0 - r * kap[i]) % b, j[i]) for i in range(4)]
            self.items.append((float(area), idx))

    def __call__(self, G):
        tot = 0.0
        for area, idx in self.items:
            c = [G[x, j] for x, j in idx]
            tot += area * ((c[0] == c[1]) & (c[0] == c[2]) & (c[0] == c[3])).sum()
        return tot / (self.b * self.b)


def count_mono(col):
    """Brute force: number of (a, d) in Z_p^2, d != 0, with c(a)=...=c(a+3d).  O(p^2)."""
    col = np.asarray(col, dtype=np.int8)
    p = len(col)
    a = np.arange(p)
    m = 0
    for d in range(1, p):
        c1, c2, c3 = col[(a + d) % p], col[(a + 2 * d) % p], col[(a + 3 * d) % p]
        m += int(((col == c1) & (col == c2) & (col == c3)).sum())
    return m


def dump_patterns(K, f):
    W = patterns(K)
    f.write(f"{len(W)}\n")
    for key, area in W.items():
        f.write(f"{float(area):.17g} " + " ".join(map(str, key)) + "\n")


if __name__ == "__main__":
    import sys
    dump_patterns(int(sys.argv[1]), sys.stdout)
