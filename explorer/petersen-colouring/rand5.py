"""Random 5-poles X (k vertices) tested as replacement for one F in G52: success iff for some
ordering of X's dangling edges, Col(X) avoids S (boundary colourings extendable to the rest)."""
import sys,random,pickle,itertools,time,networkx as nx
from pcol import pcol_set
S=pickle.load(open('S1.pkl','rb'))
seed,kmin,kmax,iters=map(int,sys.argv[1:5])
rng=random.Random(seed)
perms=list(itertools.permutations(range(5)))
tested=0;t0=time.time()
for it in range(iters):
    k=rng.randrange(kmin,kmax+1,2)
    stubs=[v for v in range(k) for _ in range(3)]
    rng.shuffle(stubs)
    dang=stubs[:5]; rest=stubs[5:]
    E=[];ok=True;seen=set()
    for i in range(0,len(rest),2):
        a,b=rest[i],rest[i+1]
        if a==b or (min(a,b),max(a,b)) in seen: ok=False;break
        seen.add((min(a,b),max(a,b)));E.append((a,b))
    if not ok: continue
    G=nx.MultiGraph(); G.add_nodes_from(range(k)); G.add_edges_from(E)
    if not nx.is_connected(G): continue
    # glued graph must be bridgeless: X plus one vertex per dangling edge joined in a cycle-free way is
    # not enough; test X + a 5-cycle-free hub: replace rest of G52 by a K4-like 2-connected stand-in
    H=nx.Graph(E)
    hub=[('h',i) for i in range(5)]
    for i in range(5): H.add_edge(dang[i],hub[i]); H.add_edge(hub[i],hub[(i+1)%5])
    if H.number_of_edges()!=len(E)+10 or not nx.is_k_edge_connected(H,2): continue
    C=pcol_set(k,E+[(d,None) for d in dang])
    if not C: continue
    tested+=1
    for p in perms:
        if not any(tuple(c[p[i]] for i in range(5)) in S for c in C):
            print('HIT k',k,'E',E,'dang',dang,'perm',p,flush=True)
            break
    if tested%200==0: print('tested',tested,'k~',k,'|C|',len(C),round(time.time()-t0),flush=True)
