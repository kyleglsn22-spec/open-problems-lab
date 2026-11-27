"""Simulated annealing over planar triangulations on n vertices minimising f_d(G)/n.
usage: anneal_tri.py n d iters seed"""
import sys, random, math
import networkx as nx
from fd import fd


def random_triangulation(n, rng):
    G = nx.Graph([(0, 1), (1, 2), (0, 2)])
    faces = [(0, 1, 2), (0, 2, 1)]
    for v in range(3, n):
        i = rng.randrange(len(faces))
        a, b, c = faces.pop(i)
        G.add_edges_from([(v, a), (v, b), (v, c)])
        faces += [(a, b, v), (b, c, v), (c, a, v)]
    return G


def flip(G, rng):
    ok, emb = nx.check_planarity(G)
    edges = list(G.edges())
    for _ in range(50):
        u, v = rng.choice(edges)
        if G.degree(u) <= 3 or G.degree(v) <= 3:
            continue
        w = emb[u][v]['cw']
        x = emb[u][v]['ccw']
        if w == x or G.has_edge(w, x):
            continue
        H = G.copy()
        H.remove_edge(u, v)
        H.add_edge(w, x)
        return H
    return G


def score(G, d):
    return fd(G, d, time_limit=30)[0]


def main():
    n, d, iters, seed = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    d = None if d == 'a' else int(d)
    rng = random.Random(seed)
    G = random_triangulation(n, rng)
    s = score(G, d)
    best = (s, G)
    T = 0.6
    for it in range(iters):
        H = G
        for _ in range(rng.randint(1, 3)):
            H = flip(H, rng)
        t = score(H, d)
        if t <= s or rng.random() < math.exp(-(t - s) / T):
            G, s = H, t
            if s < best[0]:
                best = (s, G)
                print(f"it {it} n={n} d={d} f={s} ratio={s/n:.4f} g6={nx.to_graph6_bytes(G, header=False).decode().strip()}", flush=True)
        T = max(0.05, T * 0.999)
    print("BEST", best[0], best[0] / n)


if __name__ == '__main__':
    main()
