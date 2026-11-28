import itertools, networkx as nx, pickle
from pcol import pcol_set, colourable
from multi import MP, W, F, disjoint, ring3
CW = pickle.load(open('cols.pkl','rb'))['W']
res=[]
for k in range(2,7,2):
    seen=[]
    allE=list(itertools.combinations(range(k),2))
    for mask in range(1<<len(allE)):
        E=[allE[i] for i in range(len(allE)) if mask>>i&1]
        deg=[0]*k
        for a,b in E: deg[a]+=1; deg[b]+=1
        if any(d>3 for d in deg) or sum(3-d for d in deg)!=4: continue
        G=nx.Graph(); G.add_nodes_from(range(k)); G.add_edges_from(E)
        if not nx.is_connected(G): continue
        if any(nx.is_isomorphic(G,H) for H in seen): continue
        seen.append(G)
        dang=[v for v in range(k) for _ in range(3-deg[v])]
        M=MP(k,E,dang)
        C=pcol_set(*M.as_edges())
        best=None
        for perm in set(itertools.permutations(range(4))):
            Cp={tuple(c[p] for p in perm) for c in C}
            if Cp<=CW: best=perm; break
        print(k,E,dang,'|Col|',len(C),'subset of W' if best else '',best,flush=True)
        res.append((k,E,dang,len(C),best))
pickle.dump(res,open('small4.pkl','wb'))
