"""Independent cross-check of the data behind claim AB-1 (Lab/AlbertsonBerman/).
1. G29 from paper_graphs.json is planar and a(G29) = 14 (exact solver).
2. The integer drawing g29_coords.json has no crossings (same orientation tests as the Lean file).
3. For each side (Q: 12 vertices, R: 15) and each port set X in {}, {27}, {28}, {27,28}, every k-subset of
   the side together with X contains one of the listed cycles of g29_cycles.json, and each listed
   cycle really is a cycle of G29.
Vertex numbering: paper_graphs.json labels renumbered in sorted order (as in the Lean file)."""
import json, os, itertools
import networkx as nx
from fd import fd

H = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(H, 'paper_graphs.json')))
G = nx.convert_node_labels_to_integers(nx.Graph([tuple(e) for e in d['G29']['edges']]), ordering='sorted')
assert G.number_of_nodes() == 29 and G.number_of_edges() == 80 and nx.check_planarity(G)[0]
print('a(G29) =', fd(G)[0])

P = {int(k): tuple(v) for k, v in json.load(open(os.path.join(H, 'g29_coords.json'))).items()}
def orient(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])
E = list(G.edges())
assert len(set(P[v] for v in G)) == 29
for e, f in itertools.combinations(E, 2):
    sh = set(e) & set(f)
    if sh:
        v = sh.pop(); x = e[0] if e[1] == v else e[1]; y = f[0] if f[1] == v else f[1]
        assert orient(P[v], P[x], P[y]) != 0
    else:
        a, b = e; c, dd = f
        assert orient(P[a], P[b], P[c]) * orient(P[a], P[b], P[dd]) > 0 or \
            orient(P[c], P[dd], P[a]) * orient(P[c], P[dd], P[b]) > 0
print('drawing: no crossings among', len(E), 'edges')

cyc = json.load(open(os.path.join(H, 'g29_cycles.json')))
QI = [1, 2, 3, 4, 7, 8, 9, 10, 16, 17, 18, 19]
RI = [0, 5, 6, 11, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26]
for key, (k, cs) in cyc.items():
    side, X = key.split('|')
    X = [int(x) for x in X.split(',')] if X else []
    I = QI if side == 'Q' else RI
    for c in cs:
        assert len(set(c)) == len(c) >= 3 and all(G.has_edge(c[i], c[(i + 1) % len(c)]) for i in range(len(c)))
    for B in itertools.combinations(I, k):
        S = set(B) | set(X)
        assert any(set(c) <= S for c in cs)
    print(side, X, 'every', k, '-subset hit by', len(cs), 'cycles')
print('bound: |F| <= 14 in all four port cases (6+8, 6+7+1, 6+7+1, 5+7+2)')
