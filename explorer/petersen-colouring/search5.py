"""Search small cubic 5-poles M such that ring3 with M replacing one / two / three copies of F has no P-colouring.
usage: search5.py iters seed kmax"""
import sys, random, pickle, itertools
from collections import defaultdict
import networkx as nx
from pcol import pcol_set, colourable, STAR
from multi import MP, W, F, disjoint, ring3

STARS = set(frozenset(s) for s in STAR)
cols = pickle.load(open('cols.pkl', 'rb'))
CF = cols['F']


def index_r(C):
    d = defaultdict(list)
    for c in C:
        d[(c[0], c[1])].append(c)
    return d


def ring_ok(C1, C2, C3, cross=False):
    """True if some compatible colouring exists."""
    I2, I3 = index_r(C2), index_r(C3)
    def rk(b):
        return (b[1], b[0]) if cross else b
    for c1 in C1:
        for c2 in I2.get(rk((c1[2], c1[3])), ()):
            for c3 in I3.get(rk((c2[2], c2[3])), ()):
                if rk((c3[2], c3[3])) == (c1[0], c1[1]) and len({c1[4], c2[4], c3[4]}) == 3 \
                        and frozenset((c1[4], c2[4], c3[4])) in STARS:
                    return True
    return False


PIECES = {
    'W': lambda: W(),
    'V': lambda: MP(1, [], [0, 0, 0]),
}


def petersen_minus_vertex():
    import networkx as nx
    from pcol import P
    G = P.copy(); nb = list(P[0]); G.remove_node(0)
    m = {x: i for i, x in enumerate(sorted(G))}
    return MP(9, [(m[a], m[b]) for a, b in G.edges()], [m[x] for x in nb])


PIECES['Pv'] = petersen_minus_vertex


def random_5pole(rng, kmax):
    for _ in range(1000):
        pieces = []
        size = 0
        while True:
            name = rng.choice(['W', 'W', 'V', 'V', 'V', 'Pv'])
            M = PIECES[name]()
            if size + M.n > kmax:
                break
            pieces.append(M); size += M.n
            if rng.random() < 0.25:
                break
        if not pieces:
            continue
        n, edges, dang, offs = disjoint(*pieces)
        dang = dang[:]
        rng.shuffle(dang)
        # join random pairs until 5 remain
        if (len(dang) - 5) % 2 or len(dang) < 5:
            continue
        E = set(tuple(sorted(e)) for e in edges)
        ok = True
        while len(dang) > 5:
            a = dang.pop()
            choices = [i for i, b in enumerate(dang) if b != a and tuple(sorted((a, b))) not in E]
            if not choices:
                ok = False; break
            i = rng.choice(choices); b = dang.pop(i)
            E.add(tuple(sorted((a, b)))); edges.append((a, b))
        if not ok:
            continue
        G = nx.MultiGraph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
        if not nx.is_connected(G):
            continue
        return MP(n, edges, dang)
    return None


def main():
    iters, seed, kmax = map(int, sys.argv[1:4])
    rng = random.Random(seed)
    seen = set()
    for it in range(iters):
        M = random_5pole(rng, kmax)
        if M is None:
            continue
        C = pcol_set(*M.as_edges())
        if not C:
            continue  # uncolourable pole: composite has bridges? skip (would be trivial / non-bridgeless check below)
        key = (M.n, len(C))
        for perm in itertools.permutations(range(5)):
            Cp = set(tuple(c[p] for p in perm) for c in C)
            for cross in (False, True):
                for combo, name in (((Cp, CF, CF), 'MFF'), ((Cp, Cp, CF), 'MMF'), ((Cp, Cp, Cp), 'MMM')):
                    nn = {'MFF': M.n + 35, 'MMF': 2 * M.n + 18, 'MMM': 3 * M.n + 1}[name]
                    if nn >= 52:
                        continue
                    if not ring_ok(*combo, cross=cross):
                        Mp = MP(M.n, M.edges, [M.dang[p] for p in perm])
                        f = F()
                        parts = {'MFF': (Mp, f, f), 'MMF': (Mp, Mp, f), 'MMM': (Mp, Mp, Mp)}[name]
                        n, E = ring3(*parts, cross=cross)
                        G = nx.MultiGraph(E)
                        bl = nx.is_k_edge_connected(nx.Graph(G), 2) and not any(
                            True for _ in nx.bridges(nx.Graph(G))) and G.number_of_edges() == nx.Graph(G).number_of_edges()
                        col = colourable(n, E)
                        print("CANDIDATE", name, cross, 'n', n, 'simple+bridgeless', bl, 'colourable', col,
                              'M', M.n, M.edges, M.dang, perm, flush=True)
        if it % 200 == 0:
            print('it', it, flush=True)


if __name__ == '__main__':
    main()
