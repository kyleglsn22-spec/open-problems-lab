import sys, random, networkx as nx
from pcol import colourable
from multi import MP, W, F, disjoint
from search5 import petersen_minus_vertex
it_max, seed, nmin, nmax = map(int, sys.argv[1:5])
rng = random.Random(seed)
PIECES = [('F', F, 17), ('W', W, 8), ('V', lambda: MP(1, [], [0, 0, 0]), 1), ('Pv', petersen_minus_vertex, 9)]
tested = 0
for it in range(it_max):
    target = rng.randint(nmin, nmax)
    if target % 2: target += 1
    if target > nmax: target -= 2
    pieces = []; size = 0
    weights = [3, 4, 2, 1]
    while size < target:
        name, fn, sz = rng.choices(PIECES, weights)[0]
        if size + sz > target:
            if target - size >= 1:
                pieces.append(PIECES[2][1]()); size += 1
            continue
        pieces.append(fn()); size += sz
    n, edges, dang, offs = disjoint(*pieces)
    if len(dang) % 2: continue
    ok = False
    for attempt in range(50):
        d = dang[:]; rng.shuffle(d)
        E = set(tuple(sorted(e)) for e in edges); new = []
        good = True
        while d:
            a = d.pop()
            ch = [i for i, b in enumerate(d) if b != a and tuple(sorted((a, b))) not in E]
            if not ch: good = False; break
            b = d.pop(rng.choice(ch)); E.add(tuple(sorted((a, b)))); new.append((a, b))
        if good: ok = True; break
    if not ok: continue
    allE = edges + new
    G = nx.Graph(allE)
    if G.number_of_nodes() != n or G.number_of_edges() != len(allE): continue
    if not nx.is_connected(G) or any(True for _ in nx.bridges(G)): continue
    tested += 1
    if not colourable(n, allE):
        cyc4 = nx.edge_connectivity(G)
        print('UNCOLOURABLE n', n, 'edge-conn', cyc4, 'pieces', [p.n for p in pieces], 'edges', allE, flush=True)
    if tested % 200 == 0: print('tested', tested, flush=True)
