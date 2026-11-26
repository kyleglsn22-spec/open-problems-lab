# Auditor's independent "no mixing" check for the 5/9 family (written without reusing PR 15 code).
# Claim: no relation sum c_i x_i = 0 with (c) in {(1,1,-1,-1) distinct x, (1,1,-2) distinct x}
# among points of S_inf uses depths 0 and >= 2 (after normalising the minimum depth to 0).
# Method: depth-first refinement. A slot is either a concrete point (depth <= m) or a symbolic
# "deep" point of depth > m, which lies in the closed interval J_{m+1} = phi^{m+1}([0,269]).
# Branch on the deep slot with the smallest m. Interval test prunes.
from fractions import Fraction as F
from itertools import product
O=[F(x) for x in [0,49,75,83,98,101,117,119,121,159,269]]
phi=lambda x: 101+F(18,269)*x
def it(f,x,k):
    for _ in range(k): x=f(x)
    return x
J=lambda m:(it(phi,F(0),m),it(phi,F(269),m))
level={}  # depth -> points of exactly that depth
seen=set()
for k in range(12):
    level[k]=[x for x in (it(phi,o,k) for o in O) if x not in seen]
    seen|=set(level[k])
# slot: ('pt', value, depth) or ('deep', m)  meaning depth > m
nodes=0; maxdepth=0
def possible(T,slots):
    lo=hi=F(0)
    for c,s in zip(T,slots):
        if s[0]=='pt': lo+=c*s[1]; hi+=c*s[1]
        else:
            a,b=J(s[1]+1)
            lo+=c*(a if c>0 else b); hi+=c*(b if c>0 else a)
    return lo<=0<=hi
def rec(T,slots):
    global nodes,maxdepth; nodes+=1
    pts=[s[1] for s in slots if s[0]=='pt']
    if len(set(pts))<len(pts): return []
    if not possible(T,slots): return []
    deep=[i for i,s in enumerate(slots) if s[0]=='deep']
    if not deep: return [tuple(pts)]  # an actual relation
    i=min(deep,key=lambda i:slots[i][1]); m=slots[i][1]+1
    maxdepth=max(maxdepth,m); assert m<11
    out=[]
    for x in level[m]: out+=rec(T,slots[:i]+[('pt',x,m)]+slots[i+1:])
    out+=rec(T,slots[:i]+[('deep',m)]+slots[i+1:])
    return out
found=[]
for T in [(1,1,-1,-1),(1,1,-2)]:
    n=len(T)
    # slots: choose for each position a depth class: concrete at depth 0, concrete at depth 1, or deep (>1);
    # require >=1 depth-0 point and >=1 deep slot.
    for cls in product([0,1,'d'],repeat=n):
        if 0 not in cls or 'd' not in cls: continue
        choices=[ [('pt',x,0) for x in level[0]] if c==0 else [('pt',x,1) for x in level[1]] if c==1 else [('deep',1)] for c in cls]
        for slots in product(*choices):
            found+=rec(T,list(slots))
print("nodes",nodes,"deepest level refined",maxdepth,"mixing relations found:",found)
assert not found
# brute-force corroboration on S_10: every relation spans depths within {d,d+1}
dep={x:k for k in level for x in level[k]}
P=sorted(x for k in range(11) for x in level[k]); S=set(P)
bad=0
from itertools import combinations
sums={}
for i,j in combinations(range(len(P)),2): sums.setdefault(P[i]+P[j],[]).append((P[i],P[j]))
for s,l in sums.items():
    for (a,b),(c,d) in combinations(l,2):
        ds=[dep[a],dep[b],dep[c],dep[d]]
        if max(ds)-min(ds)>=2: bad+=1
    if s/2 in S:
        for (a,b) in l:
            ds=[dep[a],dep[b],dep[s/2]]
            if max(ds)-min(ds)>=2: bad+=1
print("brute force S_10 (",len(P),"points): mixing relations =",bad)
