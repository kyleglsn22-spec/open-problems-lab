"""Search edge-gadgets: triangulation J with an edge bc. Profile p'(X)=p_J(X)-|X|, k=|J|-2.
Excess at lambda: e(X) = p'(X) - lambda*k.  Keep Pareto-minimal (e0, e_b, e_c, e_bc) up to swapping b,c.
usage: gadgets.py nmin nmax iters seed lamnum lamden"""
import sys, random, json
import networkx as nx
from fd import fd
from anneal_tri import random_triangulation, flip


def profile(J, b, c):
    out = {}
    for X in [(), (b,), (c,), (b, c)]:
        fixed = {b: int(b in X), c: int(c in X)}
        v, _ = fd(J, None, fixed=fixed, time_limit=30)
        out[X] = (v - len(X)) if v is not None else -99
    return out[()], out[(b,)], out[(c,)], out[(b, c)]


def main():
    nmin, nmax, iters, seed = map(int, sys.argv[1:5])
    ln, ld = int(sys.argv[5]), int(sys.argv[6])
    rng = random.Random(seed)
    front = []  # (vec, n, g6, b, c, prof)
    seen = set()
    for it in range(iters):
        n = rng.randint(nmin, nmax)
        J = random_triangulation(n, rng)
        for _ in range(rng.randint(5, 60)):
            J = flip(J, rng)
        key = nx.weisfeiler_lehman_graph_hash(J, iterations=4)
        if key in seen:
            continue
        seen.add(key)
        k = n - 2
        done = set()
        for (b, c) in J.edges():
            # cheap symmetry: skip edges with same (deg b, deg c) multiset pattern + common nbr degs
            sig = tuple(sorted([J.degree(b), J.degree(c)])) + tuple(sorted(J.degree(w) for w in nx.common_neighbors(J, b, c)))
            if sig in done:
                continue
            done.add(sig)
            p = profile(J, b, c)
            e = [ld * x - ln * k for x in p]  # scaled by ld
            vec = (e[0], max(e[1], e[2]), min(e[1], e[2]), e[3])
            if any(all(o[i] <= vec[i] for i in range(4)) for o, *_ in front):
                continue
            front = [f for f in front if not all(vec[i] <= f[0][i] for i in range(4))]
            g6 = nx.to_graph6_bytes(J, header=False).decode().strip()
            front.append((vec, n, g6, b, c, p))
            print("NEW", vec, "n", n, "prof", p, g6, b, c, flush=True)
    print("FRONT")
    for f in sorted(front):
        print(f)


if __name__ == '__main__':
    main()
