import itertools, sys, pickle
from minors import ops as _ops
def canon(X):
    m=len(X); n=len(X[0]) if m else 0
    if m==0 or n==0: return (m,n,())
    # column invariant: sorted abs values + multiset of row-invariants of its nonzero rows
    rinv=[tuple(sorted(abs(x) for x in r)) for r in X]
    cinv=[(tuple(sorted(abs(X[i][j]) for i in range(m))), tuple(sorted(rinv[i] for i in range(m) if X[i][j]))) for j in range(n)]
    classes={}
    for j in range(n): classes.setdefault(cinv[j],[]).append(j)
    keys=sorted(classes)
    groups=[classes[k] for k in keys]
    best=None
    for perms in itertools.product(*[itertools.permutations(g) for g in groups]):
        perm=[j for p in perms for j in p]
        for signs in itertools.product((1,-1),repeat=n):
            rows=[]
            for r in X:
                row=[signs[k]*r[perm[k]] for k in range(n)]
                for t in row:
                    if t!=0:
                        if t<0: row=[-x for x in row]
                        break
                rows.append(tuple(row))
            key=(tuple(keys),tuple(sorted(rows)))
            if best is None or key<best: best=key
    return (m,n,best)
def closure(A0, targets):
    seen={canon(A0):A0}; stack=[A0]
    while stack:
        X=stack.pop()
        for Y in _ops(X):
            if Y and len(Y[0])==0: Y=()
            c=canon(Y) if Y else (len(Y),0,())
            if c not in seen: seen[c]=Y; stack.append(Y)
        if len(seen)%500==0: print(len(seen),file=sys.stderr)
    return seen,{k:(canon(v) in seen) for k,v in targets.items()}
A6=((0,0,1,-1,0,0),(0,1,1,0,2,0),(0,1,0,1,0,2),(1,0,1,0,2,0),(1,0,0,1,0,2))
A6p=((0,0,1,1,0,0),(0,1,1,0,2,0),(0,1,0,1,0,2),(1,0,1,0,2,0),(1,0,0,1,0,2))
A7=((0,0,1,-1,2,-2,2),(0,1,1,0,2,0,0),(0,1,0,1,0,2,0),(1,0,1,0,2,0,0),(1,0,0,1,0,2,0))
A3=((1,2,0),(1,2,2),(1,0,2)); A4=((2,1,1,0),(2,1,0,1),(2,0,1,1))
T={'A3':A3,'A4':A4,'A6':A6,'A6p':A6p,'A7':A7}
which=sys.argv[1]
seen,res=closure({'A6':A6,'A6p':A6p,'A7':A7}[which],T)
from collections import Counter
mx=max([abs(x) for v in seen.values() for r in v for x in r]+[0])
print(which,'classes',len(seen),'max entry',mx,res)
pickle.dump(seen,open(f'minors_{which}.pkl','wb'))
