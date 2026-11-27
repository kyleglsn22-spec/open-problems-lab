"""Erdős #757 upper bound via 3-AP hypergraphs (hypergraph-first search).

A (4,5)-set A is determined, for Sidon purposes, by its 3-AP hypergraph H (edges (a, b, c) with middle b):
Sidon subsets of A = H-independent sets. Conversely, given an abstract H (each vertex the middle of at most one
edge), take a GENERIC point of the linear space {x : x_a + x_c = 2 x_b for every edge}. It is a (4,5)-set with
3-AP hypergraph exactly H iff no further difference coincidence x_a - x_b = x_c - x_d is forced. We test this
with a random point over a large prime field (a forced relation always shows up; an unforced one shows up
with probability about n^4/p). Any hit found here must then be re-verified over Q with an explicit integer set.

Search: simulated annealing over H on n vertices, minimising alpha(H) (computed exactly by SAT), keeping H
realizable. Target: alpha(H)/n < 5/9.
"""
import itertools
import random
import sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

P = (1 << 61) - 1


def nullspace_point(n, edges, rng):
    # rows: x_a - 2 x_b + x_c = 0 mod P ; return a random point of the solution space
    rows = []
    for (a, b, c) in edges:
        r = [0] * n
        r[a] = (r[a] + 1) % P; r[c] = (r[c] + 1) % P; r[b] = (r[b] - 2) % P
        rows.append(r)
    piv_cols = []
    M = [r[:] for r in rows]
    rk = 0
    for col in range(n):
        pr = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if pr is None:
            continue
        M[rk], M[pr] = M[pr], M[rk]
        inv = pow(M[rk][col], P - 2, P)
        M[rk] = [v * inv % P for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col]
                M[i] = [(vi - f * vr) % P for vi, vr in zip(M[i], M[rk])]
        piv_cols.append(col)
        rk += 1
    free = [c for c in range(n) if c not in piv_cols]
    x = [0] * n
    for c in free:
        x[c] = rng.randrange(P)
    for i, col in enumerate(piv_cols):
        x[col] = (-sum(M[i][c] * x[c] for c in free)) % P
    return x


def realizable(n, edges, rng):
    x = nullspace_point(n, edges, rng)
    if len(set(x)) < n:
        return False
    allowed = set()
    for (a, b, c) in edges:
        allowed.add(frozenset([(b, a), (c, b)]))
        allowed.add(frozenset([(a, b), (b, c)]))
    seen = {}
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            d = (x[a] - x[b]) % P
            if d in seen:
                pairs = seen[d]
                for (c, e) in pairs:
                    if frozenset([(a, b), (c, e)]) not in allowed:
                        return False
                pairs.append((a, b))
            else:
                seen[d] = [(a, b)]
    return True


def alpha(n, edges):
    lo, hi = 0, n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        s = Cadical153()
        pool = IDPool(start_from=n + 1)
        for (a, b, c) in edges:
            s.add_clause([-(a + 1), -(b + 1), -(c + 1)])
        s.append_formula(CardEnc.atleast(list(range(1, n + 1)), bound=mid, vpool=pool,
                                         encoding=EncType.seqcounter).clauses)
        if s.solve():
            lo = mid
        else:
            hi = mid - 1
    return lo


def try_add(n, edges, rng):
    used_mid = {b for (_, b, _) in edges}
    pairs = set()
    for (a, b, c) in edges:
        pairs |= {frozenset((a, b)), frozenset((b, c)), frozenset((a, c))}
    for _ in range(50):
        b = rng.randrange(n)
        if b in used_mid:
            continue
        a, c = rng.sample([v for v in range(n) if v != b], 2)
        if any(frozenset(p) in pairs for p in ((a, b), (b, c), (a, c))):
            continue
        return edges + [(min(a, c), b, max(a, c))]
    return None


def anneal(n, steps, rng, T0=0.6):
    edges = []
    cur_alpha = n
    best = (n, [])
    for step in range(steps):
        T = T0 * (1 - step / steps) + 0.02
        r = rng.random()
        if edges and r < 0.2:
            new = edges[:]
            new.pop(rng.randrange(len(new)))
        elif edges and r < 0.6:
            new = edges[:]
            new.pop(rng.randrange(len(new)))
            new = try_add(n, new, rng)
            if new is None:
                continue
        else:
            new = try_add(n, edges, rng)
            if new is None:
                continue
        if not realizable(n, new, rng):
            continue
        a = alpha(n, new)
        delta = a - cur_alpha - 0.01 * (len(new) - len(edges))
        if delta <= 0 or rng.random() < pow(2.718, -delta / T):
            edges, cur_alpha = new, a
            if a < best[0]:
                best = (a, edges[:])
    return best


if __name__ == "__main__":
    n = int(sys.argv[1]); steps = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    rng = random.Random(seed)
    for rep in range(10**6):
        a, E = anneal(n, steps, rng)
        flag = " <-- BELOW 5/9" if 9 * a < 5 * n else ""
        print(f"n={n} rep={rep}: alpha={a} ratio={a/n:.4f} edges={len(E)}{flag}", flush=True)
        if flag:
            print("EDGES", E, flush=True)
