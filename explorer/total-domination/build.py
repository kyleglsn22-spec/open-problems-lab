import itertools, json
E14 = [(0,1),(0,2),(0,7),(0,3)] + [tuple(map(int,p.split('/'))) for p in "0/4, 0/5, 0/6, 1/2, 1/7, 1/8, 1/9, 2/3, 2/8, 2/10, 2/11, 3/4, 3/11, 4/5, 4/11, 4/12, 5/6, 5/12, 6/7, 6/10, 6/12, 6/13, 7/9, 7/13, 8/9, 8/10, 8/13, 9/13, 10/11, 10/12, 10/13, 11/12".split(', ')]
assert len(E14)==36 and len(set(frozenset(e) for e in E14))==36
# B: copies i=1,2,3 ; identifications
ident = {(1,0):'a',(2,1):'a',(3,0):'a',(1,1):'b',(2,0):'b',(3,2):'b',(1,2):'z2',(2,2):'z2',(2,7):'z3',(3,1):'z3'}
names=[]
def nm(i,j):
    return ident.get((i,j), f"{i}_{j}")
for i in (1,2,3):
    for j in range(14):
        n=nm(i,j)
        if n not in names: names.append(n)
print(len(names))
idx={n:k for k,n in enumerate(names)}
EB=set()
for i in (1,2,3):
    dele = {0,1} if i in (1,2) else {0,2}
    for (x,y) in E14:
        if {x,y}==dele: continue
        u,v=idx[nm(i,x)],idx[nm(i,y)]
        assert u!=v
        EB.add(frozenset((u,v)))
EB.add(frozenset((idx['a'],idx['b'])))
EB=sorted(tuple(sorted(e)) for e in EB)
print("edges",len(EB), "3n-6 =",3*36-6)
adj={v:set() for v in range(36)}
for u,v in EB: adj[u].add(v); adj[v].add(u)
print("min deg",min(len(adj[v]) for v in adj))
# embeddings iota_i : Fin14 -> Fin36
iota={i:[idx[nm(i,j)] for j in range(14)] for i in (1,2,3)}
json.dump({"names":names,"edges":EB,"iota":iota,"E14":E14},open("B.json","w"))
# partner colouring search: colours 0..3, partner x^1
order=sorted(range(36), key=lambda v: 0)
# order by BFS for pruning
import collections
seen=[idx['a']]; 
while len(seen)<36:
    best=max((v for v in range(36) if v not in seen), key=lambda v: len(adj[v]&set(seen)))
    seen.append(best)
col={}
count=[0,0]
def rec(k):
    if k==36:
        count[0]+=1
        if all(any(col[u]==col[v]^1 for u in adj[v]) for v in range(36)):
            count[1]+=1
        return
    v=seen[k]
    for c in range(4):
        if all(col.get(u)!=c for u in adj[v]):
            col[v]=c; rec(k+1); del col[v]
rec(0)
print("proper 4-colourings",count[0],"partner colourings",count[1])
