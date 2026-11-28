"""Build W, F, G52 from the paper's description; multipole assembly helper."""
import networkx as nx
from pcol import colourable, pcol_set, P


class MP:
    """Cubic multipole: n vertices, internal edges, dangling: list of vertices (one dangling edge each, ordered)."""
    def __init__(self, n, edges, dang):
        self.n, self.edges, self.dang = n, list(edges), list(dang)

    def as_edges(self):
        return self.n, self.edges + [(d, None) for d in self.dang]


def W():
    # P minus adjacent u=0, v=1 (networkx petersen: 0-1 edge)
    G = P.copy()
    u, v = 0, 1
    nu = [x for x in P[u] if x != v]
    nv = [x for x in P[v] if x != u]
    G.remove_nodes_from([u, v])
    G = nx.relabel_nodes(G, {x: i for i, x in enumerate(sorted(G))})
    m = {x: i for i, x in enumerate(sorted(set(P) - {u, v}))}
    # dangling order (i1, i2, o1, o2): i1,o1 at u ; i2,o2 at v
    return MP(8, list(G.edges()), [m[nu[0]], m[nv[0]], m[nu[1]], m[nv[1]]])


def disjoint(*mps):
    off = 0
    edges, dang, offs = [], [], []
    for M in mps:
        offs.append(off)
        edges += [(a + off, b + off) for a, b in M.edges]
        dang += [d + off for d in M.dang]
        off += M.n
    return off, edges, dang, offs


def F():
    w = W()
    n, edges, dang, offs = disjoint(w, w)
    i1t, i2t, o1t, o2t, i1b, i2b, o1b, o2b = dang
    edges.append((o2t, i1b))  # e_L
    s = n  # subdivision vertex
    edges += [(o1t, s), (s, i2b)]
    # dangling order (r1, r2, b1, b2, e)
    return MP(n + 1, edges, [i1t, o2b, i2t, o1b, s])


def ring3(A, B, C, cross=False):
    """Three 5-poles (r1,r2,b1,b2,e) joined B_i -> R_{i+1}, e's to a central vertex."""
    n, edges, dang, offs = disjoint(A, B, C)
    d = [dang[5 * i:5 * i + 5] for i in range(3)]
    for i in range(3):
        j = (i + 1) % 3
        if cross:
            edges += [(d[i][2], d[j][1]), (d[i][3], d[j][0])]
        else:
            edges += [(d[i][2], d[j][0]), (d[i][3], d[j][1])]
    c = n
    edges += [(d[i][4], c) for i in range(3)]
    return n + 1, edges


if __name__ == '__main__':
    f = F()
    for cross in (False, True):
        n, E = ring3(f, f, f, cross)
        G = nx.Graph(E)
        print('cross', cross, n, len(E), nx.is_k_edge_connected(G, 2), 'colourable:', colourable(n, E))
