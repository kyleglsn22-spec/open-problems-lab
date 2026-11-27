"""Recompute a(G) and f_d(G), d = 2..6, for the gadgets and graphs of arXiv 2608.23260
(edge lists transcribed from the paper's TikZ figures into paper_graphs.json)."""
import json, os
import networkx as nx
from fd import fd

data = json.load(open(os.path.join(os.path.dirname(__file__), 'paper_graphs.json')))
for name, g in data.items():
    G = nx.Graph([tuple(e) for e in g['edges']])
    n = G.number_of_nodes()
    assert nx.check_planarity(G)[0]
    row = []
    for d in [None, 6, 5, 4, 3, 2]:
        v = fd(G, d)[0]
        thr = n / 2 if d is None else 2 * d * n / (4 * d + 1)
        row.append(f"{'a' if d is None else 'f_' + str(d)}={v} (bound {thr:.2f})")
    print(name, n, '; '.join(row))
