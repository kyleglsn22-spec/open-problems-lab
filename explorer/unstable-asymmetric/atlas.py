import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
def naut(G, cap):
    c=0
    for _ in GraphMatcher(G,G).isomorphisms_iter():
        c+=1
        if c>cap: break
    return c
cnt=0; asym=0; found=[]
for G in nx.graph_atlas_g():
    n=G.number_of_nodes()
    if n<2 or not nx.is_connected(G) or nx.is_bipartite(G): continue
    nb=[frozenset(G[v]) for v in G]
    if len(set(nb))<n: continue
    cnt+=1
    if naut(G,1)>1: continue
    asym+=1
    D=nx.tensor_product(G, nx.complete_graph(2))
    a=naut(D,2)
    if a>2:
        L={len(c) for c in nx.simple_cycles(G)}
        ok=any(k in L and 2*k in L for k in range(3,n+1,2))
        found.append((n,sorted(G.edges()),sorted(L),ok))
print('candidates',cnt,'asymmetric',asym,'asym unstable',len(found))
for f in found: print(f)
