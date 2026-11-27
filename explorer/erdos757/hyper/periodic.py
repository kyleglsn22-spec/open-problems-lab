"""Periodic 3-AP hypergraphs for Erdős #757 (a structured family, different from self-similar gadget chains).

Vertices (k, i), k in Z (period index), i in [w]. A pattern is (i1, d1, i, i3, d3): for every k the triple
((k+d1, i1), (k, i), (k+d3, i3)) is a 3-AP with middle (k, i). Each class i is the middle of at most one
pattern. The window of K periods gives a finite hypergraph; it is realized by a generic point of its linear
space (see hsearch.py). The Sidon density is estimated by (alpha(K2) - alpha(K1)) / ((K2 - K1) w).
Target: density < 5/9. Any hit must be re-checked over Q and for all K (not done here).
"""
import random
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from hsearch import realizable, alpha


def window(w, pats, K):
    idx = lambda k, i: k * w + i
    E = []
    for (i1, d1, i, i3, d3) in pats:
        for k in range(K):
            k1, k3 = k + d1, k + d3
            if 0 <= k1 < K and 0 <= k3 < K:
                a, b, c = idx(k1, i1), idx(k, i), idx(k3, i3)
                E.append((min(a, c), b, max(a, c)))
    return K * w, E


def linear(E):
    seen = set()
    for (a, b, c) in E:
        for p in ((a, b), (b, c), (a, c)):
            q = frozenset(p)
            if q in seen:
                return False
            seen.add(q)
    return len({b for (_, b, _) in E}) == len(E)


def evaluate(w, pats, rng, K1=4, K2=8):
    n, E = window(w, pats, K2)
    if not linear(E) or not realizable(n, E, rng):
        return None
    a2 = alpha(n, E)
    n1, E1 = window(w, pats, K1)
    a1 = alpha(n1, E1)
    return (a2 - a1) / ((K2 - K1) * w), a1, a2


def random_pat(w, i, rng, D):
    while True:
        i1, i3 = rng.randrange(w), rng.randrange(w)
        d1, d3 = rng.randint(-D, D), rng.randint(-D, D)
        if (i1, d1) != (i, 0) and (i3, d3) != (i, 0) and (i1, d1) != (i3, d3):
            return (i1, d1, i, i3, d3)


def anneal(w, steps, rng, D=2, init=None):
    pats = dict(init) if init else {}
    cur = 1.0
    best = (1.0, None)
    for step in range(steps):
        T = 0.05 * (1 - step / steps) + 0.003
        new = dict(pats)
        i = rng.randrange(w)
        if i in new and rng.random() < 0.25:
            del new[i]
        else:
            new[i] = random_pat(w, i, rng, D)
        r = evaluate(w, list(new.values()), rng)
        if r is None:
            continue
        dens = r[0] - 0.001 * len(new)
        if dens <= cur or rng.random() < pow(2.718, -(dens - cur) / T):
            pats, cur = new, dens
            if r[0] < best[0]:
                best = (r[0], list(new.values()), r[1:])
                if r[0] < 5 / 9 - 1e-9:
                    print('CANDIDATE', r, list(new.values()), flush=True)
    return best


FIVE_NINTHS = [(0, 0, 1, 4, 0), (0, 0, 2, 5, 0), (0, 0, 8, 6, -1), (1, 0, 3, 7, 0), (1, 0, 5, 8, 0),
               (2, 0, 4, 6, 0), (2, 0, 7, 8, 0), (4, -1, 0, 3, 0), (5, 0, 6, 7, 0)]  # reader's 5/9 family, w = 9

if __name__ == "__main__":
    w = int(sys.argv[1]); steps = int(sys.argv[2]); seed = int(sys.argv[3])
    seeded = len(sys.argv) > 4 and sys.argv[4] == "seed"
    rng = random.Random(seed)
    init = {p[2]: p for p in FIVE_NINTHS} if seeded else None
    for rep in range(10**6):
        d, pats, al = anneal(w, steps, rng, D=1 if seeded else 2, init=init)
        flag = " <-- BELOW 5/9" if d < 5 / 9 - 1e-9 else ""
        print(f"w={w} rep={rep}: density~{d:.4f} alphas={al} pats={pats}{flag}", flush=True)
