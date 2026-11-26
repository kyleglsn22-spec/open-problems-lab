import itertools
# vertices: block i in 0..3 -> a=5i, b=5i+1, terminal to j: 5i+2+idx
def term(i,j): return 5*i+2+(j if j<i else j-1)
E=[]
for i in range(4):
    for j in range(4):
        if j!=i:
            E.append((5*i,term(i,j))); E.append((5*i+1,term(i,j)))
            if i<j: E.append((term(i,j),term(j,i)))
E=[tuple(sorted(e)) for e in E]; assert len(set(E))==30
deg=[0]*20
for u,v in E: deg[u]+=1;deg[v]+=1
assert all(d==3 for d in deg)
full={1,2,3,4,5}
def blk(v): return v//5
L={}
for v in range(20): L[('v',v)]=full-{blk(v)+1}
for e in E:
    u,v=e
    if blk(u)==blk(v): L[('e',e)]=full-{blk(u)+1}
    else:
        i,j=sorted((blk(u)+1,blk(v)+1))
        if (i,j) in [(1,3),(2,4)]: L[('e',e)]=full-{5}
        else:
            # edge between i and i+1 cyclic, list minus i+2 cyclic
            if (i,j)==(1,4): lo=4
            else: lo=i
            m=(lo+2-1)%4+1
            L[('e',e)]=full-{m}
for k,v in L.items(): assert len(v)==4
# conflicts
items=list(L)
conf={x:set() for x in items}
def add(x,y): conf[x].add(y); conf[y].add(x)
for u,v in E: add(('v',u),('v',v)); add(('v',u),('e',(u,v))); add(('v',v),('e',(u,v)))
for e in E:
    for f in E:
        if e<f and set(e)&set(f): add(('e',e),('e',f))
# DFS with ordering by most constrained
import sys
sys.setrecursionlimit(10000)
col={}
nodes=0
def dfs():
    global nodes; nodes+=1
    best=None;bc=None
    for x in items:
        if x in col: continue
        avail=[c for c in L[x] if all(col.get(y)!=c for y in conf[x])]
        if best is None or len(avail)<len(bc): best,bc=x,avail
    if best is None: return True
    for c in bc:
        col[best]=c
        if dfs(): return True
        del col[best]
    return False
print("colourable from L:",dfs(),"nodes",nodes)
for e in E:
    if blk(e[0])!=blk(e[1]): print(e,(blk(e[0])+1,blk(e[1])+1),sorted(L[('e',e)]))
