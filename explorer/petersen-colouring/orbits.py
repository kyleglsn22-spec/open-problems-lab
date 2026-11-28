import pickle,itertools,networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
from pcol import pcol_set,P,PE,PEi
S=pickle.load(open('S1.pkl','rb')); CF=pickle.load(open('cols.pkl','rb'))['F']
# tree: vertices 0-1-2 path, dangling 0,0,1,2,2 -> need order; universe independent of order? use generic
T=pcol_set(3,[(0,1),(1,2),(0,None),(0,None),(1,None),(2,None),(2,None)])
print('|U tree(0,0,1,2,2)|',len(T))
# universe across all possible: union over orders of trees
U=set()
for perm in set(itertools.permutations([0,0,1,2,2])):
    pass
auts=[m for m in GraphMatcher(P,P).isomorphisms_iter()]
print('auts',len(auts))
emap=[[PEi[tuple(sorted((a[u],a[v])))] for (u,v) in PE] for a in auts]
def orb(t): return frozenset(tuple(m[x] for x in t) for m in emap)
def orbits(C):
    seen=set();res=[]
    for t in C:
        if t in seen: continue
        o=orb(t); seen|=o; res.append(o)
    return res
print('S orbits',[len(o) for o in orbits(S)])
print('F orbits',[len(o) for o in orbits(CF)])
# all 5-tuples realizable: build by brute: tuples from both
