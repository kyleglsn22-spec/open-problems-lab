"""Exhaustive search for asymmetric unstable graphs on n = 8 and 9 vertices.
Every graph on n vertices is a one-vertex extension of a graph on n-1 vertices, so testing all extensions
(with repeats) of all (n-1)-vertex graphs covers every n-vertex graph."""
import sys, pickle, os, itertools, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
from multiprocessing import Pool
OUT=os.path.dirname(os.path.abspath(__file__))
def naut(G, cap):
    c=0
    for _ in GraphMatcher(G,G).isomorphisms_iter():
        c+=1
        if c>cap: break
    return c
def extensions(G):
    n=G.number_of_nodes()
    for mask in range(1<<n):
        H=G.copy(); H.add_node(n)
        H.add_edges_from((i,n) for i in range(n) if mask>>i&1)
        yield H
def test(H):
    n=H.number_of_nodes()
    if not nx.is_connected(H) or nx.is_bipartite(H): return None
    if len({frozenset(H[v]) for v in H})<n: return None
    if naut(H,1)>1: return None
    D=nx.tensor_product(H, nx.complete_graph(2))
    if naut(D,2)>2:
        L={len(c) for c in nx.simple_cycles(H)}
        return (n,sorted(H.edges()),sorted(L),any(k in L and 2*k in L for k in range(3,n+1,2)))
    return 'asym'
def work(G):
    res=[]; a=0
    for H in extensions(G):
        r=test(H)
        if r=='asym': a+=1
        elif r is not None: res.append(r)
    return a,res
def dedupe(graphs):
    buckets={}
    for H in graphs:
        h=nx.weisfeiler_lehman_graph_hash(H,iterations=4)
        b=buckets.setdefault(h,[])
        if not any(nx.is_isomorphic(H,K) for K in b): b.append(H)
    return [H for b in buckets.values() for H in b]
if __name__=='__main__':
    g7=[G for G in nx.graph_atlas_g() if G.number_of_nodes()==7]
    g7=[nx.convert_node_labels_to_integers(G) for G in g7]
    with Pool(4) as p:
        R=p.map(work,g7,chunksize=20)
    a=sum(r[0] for r in R); found=[x for r in R for x in r[1]]
    print('n=8 asym(with repeats)',a,'asym unstable',len(found),flush=True)
    for f in found[:20]: print(f,flush=True)
    p8=os.path.join(OUT,'g8.pkl')
    if os.path.exists(p8): g8=pickle.load(open(p8,'rb'))
    else:
        g8=dedupe([H for G in g7 for H in extensions(G)])
        pickle.dump(g8,open(p8,'wb'))
    print('graphs on 8 vertices',len(g8),flush=True)
    with Pool(4) as p:
        R=p.map(work,g8,chunksize=50)
    a=sum(r[0] for r in R); found=[x for r in R for x in r[1]]
    print('n=9 asym(with repeats)',a,'asym unstable',len(found),flush=True)
    for f in found[:50]: print(f,flush=True)
    pickle.dump(found,open(os.path.join(OUT,'found9.pkl'),'wb'))
