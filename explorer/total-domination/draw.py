import json, itertools
from fractions import Fraction
d=json.load(open("B.json")); names=d["names"]; E=[tuple(e) for e in d["edges"]]
idx={n:k for k,n in enumerate(names)}
n=36
adj={v:set() for v in range(n)}
for u,v in E: adj[u].add(v); adj[v].add(u)
outer=[idx['a'],idx['b'],idx['1_7']]
assert all(outer[(i+1)%3] in adj[outer[i]] for i in range(3))
# Tutte: exact rational solve
pos={outer[0]:(0,0),outer[1]:(1,0),outer[2]:(Fraction(1,2),1)}
inner=[v for v in range(n) if v not in outer]
m=len(inner); ii={v:k for k,v in enumerate(inner)}
A=[[Fraction(0)]*m for _ in range(m)]; bx=[Fraction(0)]*m; by=[Fraction(0)]*m
for v in inner:
    A[ii[v]][ii[v]]=Fraction(len(adj[v]))
    for u in adj[v]:
        if u in ii: A[ii[v]][ii[u]]-=1
        else:
            bx[ii[v]]+=Fraction(pos[u][0]); by[ii[v]]+=Fraction(pos[u][1])
def solve(A,b):
    M=[row[:]+[b[i]] for i,row in enumerate(A)]
    for c in range(m):
        p=next(r for r in range(c,m) if M[r][c]!=0); M[c],M[p]=M[p],M[c]
        for r in range(m):
            if r!=c and M[r][c]!=0:
                f=M[r][c]/M[c][c]; M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    return [M[i][m]/M[i][i] for i in range(m)]
X=solve(A,bx); Y=solve(A,by)
P={**{v:(float(pos[v][0]),float(pos[v][1])) for v in outer},**{v:(float(X[ii[v]]),float(Y[ii[v]])) for v in inner}}
def orient(a,b,c): return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def good(P,e,f):
    a,b=e; c,dd=f
    sh=set(e)&set(f)
    if sh:
        v=sh.pop(); x=a if b==v else b; y=c if dd==v else dd
        return orient(P[v],P[x],P[y])!=0
    return orient(P[a],P[b],P[c])*orient(P[a],P[b],P[dd])>0 or orient(P[c],P[dd],P[a])*orient(P[c],P[dd],P[b])>0
for S in [10**3,10**4,10**5,10**6]:
    Q={v:(round(P[v][0]*S),round(P[v][1]*S)) for v in range(n)}
    ok = len(set(Q.values()))==n and all(good(Q,e,f) for e,f in itertools.combinations(E,2))
    print(S, ok)
    if ok:
        json.dump({str(v):Q[v] for v in range(n)},open("P.json","w")); break
