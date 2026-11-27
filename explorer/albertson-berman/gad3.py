import sys, random, itertools, networkx as nx
from fd import fd
from anneal_tri import random_triangulation, flip
SUBS=[(),(0,),(1,),(2,),(0,1),(0,2),(1,2)]
def faces(G):
    ok,emb=nx.check_planarity(G); fs=set()
    for u,v in G.edges():
        for a,b in ((u,v),(v,u)):
            f=emb.traverse_face(a,b); 
            if len(f)==3: fs.add(tuple(sorted(f)))
    return list(fs)
def prof3(J,f):
    out=[]
    for X in SUBS:
        fixed={f[i]:int(i in X) for i in range(3)}
        v=fd(J,None,fixed=fixed)[0]; out.append(v-len(X))
    return tuple(out)
def canon(p):
    # min over the 6 port permutations
    best=None
    for perm in itertools.permutations(range(3)):
        q=tuple(p[SUBS.index(tuple(sorted(perm[i] for i in X)))] for X in SUBS)
        if best is None or q<best: best=q
    return best
if __name__=='__main__':
    nmin,nmax,iters,seed,ln,ld=map(int,sys.argv[1:7]); rng=random.Random(seed)
    seen=set(); front=[]
    Js=[nx.icosahedral_graph()]
    for it in range(iters):
        if it<len(Js): J=Js[it]
        else:
            n=rng.randint(nmin,nmax); J=random_triangulation(n,rng)
            for _ in range(rng.randint(3,60)): J=flip(J,rng)
        key=nx.weisfeiler_lehman_graph_hash(J,iterations=4)
        if key in seen: continue
        seen.add(key); n=J.number_of_nodes(); k=n-3; done=set()
        for f in faces(J):
            sig=tuple(sorted(J.degree(x) for x in f))
            if sig in done: continue
            done.add(sig)
            p=canon(prof3(J,f)); e=tuple(ld*x-ln*k for x in p)
            if any(all(o[i]<=e[i] for i in range(7)) for o,*_ in front): continue
            front=[F for F in front if not all(e[i]<=F[0][i] for i in range(7))]
            front.append((e,n,p,nx.to_graph6_bytes(J,header=False).decode().strip(),f))
            print("NEW",e,n,p,front[-1][3],f,flush=True)
    print("FRONT"); [print(F) for F in sorted(front)]
