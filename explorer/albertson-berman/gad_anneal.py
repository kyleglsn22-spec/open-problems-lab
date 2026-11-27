"""Anneal an edge gadget (triangulation J, edge bc) to minimise the best template ratio.
Templates (all designated edges get a copy of J, either orientation choice per copy is ignored -> use profile symmetrised by worst case? no: we use given orientation consistently):
  hub3: G52 skeleton (7 vertices, 3 designated edges b_i c_i)
  tri : triangle, 3 designated edges
  edge: single edge with m copies (m=1..4)
usage: gad_anneal.py n iters seed"""
import sys, random, math, itertools
import networkx as nx
from fd import fd
from anneal_tri import random_triangulation, flip
from skel import induced_forests
from fractions import Fraction


def profile(J, b, c):
    out = []
    for X in [(), (b,), (c,), (b, c)]:
        fixed = {b: int(b in X), c: int(c in X)}
        v, _ = fd(J, None, fixed=fixed, time_limit=30)
        out.append(v - len(X) if v is not None else -99)
    return tuple(out)


def hub3():
    H = nx.Graph()
    D = []
    for i in range(3):
        j = (i + 1) % 3
        H.add_edges_from([('z', f'b{i}'), ('z', f'c{i}'), (f'b{i}', f'c{i}'), (f'b{i}', f'c{j}'), (f'c{i}', f'c{j}')])
        D.append((f'b{i}', f'c{i}'))
    return H, D


def tri():
    H = nx.Graph([(0, 1), (1, 2), (2, 0)])
    return H, [(0, 1), (1, 2), (2, 0)]


TEMPL = []
for H, D in [hub3(), tri()]:
    TEMPL.append((H, D, induced_forests(H)))
for mlt in range(1, 5):
    H = nx.Graph([(0, 1)])
    TEMPL.append((H, [(0, 1)] * mlt, induced_forests(H)))


def best_ratio(p, k):
    best = None
    for H, D, F in TEMPL:
        a = 0
        for S in F:
            v = len(S)
            for (u, w) in D:
                iu, iw = u in S, w in S
                v += p[3] if iu and iw else p[1] if iu else p[2] if iw else p[0]
            a = max(a, v)
        r = Fraction(a, H.number_of_nodes() + k * len(D))
        if best is None or r < best[0]:
            best = (r, H.number_of_nodes(), len(D))
    return best


def main():
    n, iters, seed = map(int, sys.argv[1:4])
    rng = random.Random(seed)
    J = random_triangulation(n, rng)
    e = rng.choice(list(J.edges()))

    def ev(J, e):
        p = profile(J, *e)
        return best_ratio(p, n - 2), p

    (r, p) = ev(J, e)
    best = r
    T = 0.02
    for it in range(iters):
        if rng.random() < 0.3:
            J2, e2 = J, rng.choice(list(J.edges()))
        else:
            J2 = J
            for _ in range(rng.randint(1, 2)):
                J2 = flip(J2, rng)
            e2 = e if J2.has_edge(*e) else rng.choice(list(J2.edges()))
        r2, p2 = ev(J2, e2)
        if r2[0] <= r[0] or rng.random() < math.exp(-float(r2[0] - r[0]) / T):
            J, e, r, p = J2, e2, r2, p2
            if r[0] < best[0]:
                best = r
                print(f"it {it} ratio {r[0]} ~{float(r[0]):.4f} templ {r[1:]} prof {p} g6 {nx.to_graph6_bytes(J, header=False).decode().strip()} edge {e}", flush=True)
        T = max(0.002, T * 0.9995)
    print("BEST", best)


if __name__ == '__main__':
    main()
