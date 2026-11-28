"""Petersen colouring tools. A cubic multipole is given as (n, edges) where an edge is (u, v) with
v = None for a dangling edge. P-colouring: phi: E -> E(P), each vertex's 3 edges map onto the 3 edges
at some vertex of P."""
import itertools, json
import networkx as nx
from pysat.solvers import Cadical153
from pysat.card import CardEnc

P = nx.petersen_graph()
PE = [tuple(sorted(e)) for e in P.edges()]
PEi = {e: i for i, e in enumerate(PE)}
STAR = [[PEi[tuple(sorted((w, x)))] for x in P[w]] for w in range(10)]


def encode(n, edges):
    """Return (clauses, x) where x[e][f] is the var for edge e coloured f."""
    cnt = [0]

    def new():
        cnt[0] += 1
        return cnt[0]
    x = [[new() for f in range(15)] for e in edges]
    y = [[new() for w in range(10)] for v in range(n)]
    cl = []
    for e in range(len(edges)):
        cl.append(x[e][:])
        for f, g in itertools.combinations(range(15), 2):
            cl.append([-x[e][f], -x[e][g]])
    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        if v is not None:
            inc[v].append(i)
    for v in range(n):
        assert len(inc[v]) == 3, (v, inc[v])
        cl.append(y[v][:])
        for w in range(10):
            S = set(STAR[w])
            for e in inc[v]:
                # y[v][w] -> x[e] in S
                cl.append([-y[v][w]] + [x[e][f] for f in S])
            # distinct
            for a, b in itertools.combinations(inc[v], 2):
                for f in S:
                    cl.append([-y[v][w], -x[a][f], -x[b][f]])
    return cl, x, cnt[0]


def colourable(n, edges, assume=None):
    cl, x, _ = encode(n, edges)
    s = Cadical153(bootstrap_with=cl)
    # symmetry: Aut(P) is transitive on 3-arcs; fix vertex 0's edges if no assumptions
    asm = []
    if assume is None:
        inc0 = [i for i, (u, v) in enumerate(edges) if u == 0 or v == 0]
        st = STAR[0]
        asm = [x[inc0[0]][st[0]], x[inc0[1]][st[1]], x[inc0[2]][st[2]]]
    r = s.solve(assumptions=asm)
    s.delete()
    return r


def pcol_set(n, edges):
    """All tuples of colours on dangling edges (in edge order)."""
    cl, x, _ = encode(n, edges)
    dang = [i for i, (u, v) in enumerate(edges) if v is None]
    s = Cadical153(bootstrap_with=cl)
    out = set()
    while s.solve():
        m = set(l for l in s.get_model() if l > 0)
        t = tuple(next(f for f in range(15) if x[e][f] in m) for e in dang)
        out.add(t)
        s.add_clause([-x[e][t[k]] for k, e in enumerate(dang)])
    s.delete()
    return out


def graph_edges(G):
    G = nx.convert_node_labels_to_integers(G)
    return G.number_of_nodes(), [(u, v) for u, v in G.edges()]


def hog(path):
    d = json.load(open(path))
    adj = d['adjacencyList']; adj = json.loads(adj) if isinstance(adj, str) else adj
    G = nx.Graph()
    for u, nb in enumerate(adj):
        for v in nb:
            G.add_edge(u, v)
    return G


if __name__ == '__main__':
    print('Petersen', colourable(*graph_edges(P)))
    for id in [57244, 57278]:
        G = hog(f'hog_{id}.json')
        print(id, G.number_of_nodes(), nx.is_k_edge_connected(G, 2), colourable(*graph_edges(G)))
