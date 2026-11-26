# Independent exact checker. Rebuilds every class constraint by brute force over the cube (no binomial formulas).
import json, sys, itertools
from fractions import Fraction as F
cert=json.load(open(sys.argv[1]))
parts=cert['parts']; d=cert['degree']; n=sum(parts)
blocks=[]; s=0
for a in parts: blocks.append(list(range(s,s+a))); s+=a
def pattern(mask): return tuple(sum(1 for i in B if mask>>i&1) for B in blocks)
# representative subset for each pattern with |S|<=d
rep={}
for k in range(d+1):
    for S in itertools.combinations(range(n),k):
        m=sum(1<<i for i in S); p=pattern(m)
        rep.setdefault(p,m)
classes={}
for x in range(1<<n): classes.setdefault(pattern(x),[]).append(x)
def row(w):
    # N(w) = sum_p C_p * #{x in class w : rep_p ⊆ x}, by symmetry within blocks this count is the same for every S of pattern p,
    # but we compute it as (#pairs (S,x), S of pattern p, S⊆x, x in class) / #S of pattern p  -- fully brute force.
    coef={}
    xs=classes[tuple(w)]
    for p,m in rep.items():
        Ss=[S for S in range(1<<n) if bin(S).count('1')==sum(p) and pattern(S)==p] if sum(p)<=d else []
        tot=sum(1 for S in Ss for x in xs if S & x == S)
        coef[p]=F(tot,len(Ss))
    return coef,len(xs)
known={}
for p in rep:
    if sum(p)==0: known[p]=0
    elif sum(p)==1: known[p]=parts[p.index(1)]   # f(e_i)=1 for all i, f(0)=0
target=tuple(cert['target_pattern'])
bounds={}
cache={}
for name,sgn in [('lower',1),('upper',-1)]:
    agg={}; rhs=F(0)
    for e in cert['combinations'][name]:
        w=tuple(e['class']); y=F(e['mult']); assert y>0
        if w not in cache: cache[w]=row(w)
        coef,cap=cache[w]
        # side N<=cap :  sum coef*C <= cap ;  side N>=0 : -sum coef*C <= 0
        s= 1 if e['side']=='N<=cap' else -1
        r= cap if s==1 else 0
        const=sum(coef[p]*known[p] for p in known)
        for p,c in coef.items():
            if p in known: continue
            agg[p]=agg.get(p,0)+y*s*c
        rhs+=y*(r - s*const)
    # need agg == -sgn * e_target  =>  -sgn*C_t <= rhs
    for p,v in agg.items():
        want = -sgn if p==target else 0
        assert v==want, (name,p,v)
    bounds[name]= -rhs if sgn==1 else rhs   # lower: C_t >= -rhs ; upper: C_t <= rhs
lo,hi=bounds['lower'],bounds['upper']
import math
print('target',target,'in [',lo,',',hi,']')
ok= math.floor(hi) < math.ceil(lo)
print('NO INTEGER VALUE POSSIBLE -> no such function' if ok else 'interval contains an integer: certificate does not prove infeasibility')
