import itertools, sys
A6=((0,0,1,-1,0,0),(0,1,1,0,2,0),(0,1,0,1,0,2),(1,0,1,0,2,0),(1,0,0,1,0,2))
A3=((1,2,0),(1,2,2),(1,0,2))
A4=((2,1,1,0),(2,1,0,1),(2,0,1,1))
def canon(X):
    m=len(X); n=len(X[0]) if m else 0
    if m==0 or n==0: return (m,n,())
    best=None
    for perm in itertools.permutations(range(n)):
        for signs in itertools.product((1,-1),repeat=n):
            rows=[]
            for r in X:
                row=[signs[k]*r[perm[k]] for k in range(n)]
                for t in row:
                    if t!=0:
                        if t<0: row=[-x for x in row]
                        break
                rows.append(tuple(row))
            key=tuple(sorted(rows))
            if best is None or key<best: best=key
    return (m,n,best)
def ops(X):
    m=len(X); n=len(X[0]) if m else 0
    out=[]
    for i in range(m): out.append(X[:i]+X[i+1:])
    for j in range(n): out.append(tuple(r[:j]+r[j+1:] for r in X))
    for i in range(m):
        if all(x%2==0 for x in X[i]) and any(X[i]):
            out.append(X[:i]+(tuple(x//2 for x in X[i]),)+X[i+1:])
    for i in range(m):
        for j in range(n):
            if X[i][j] in (1,-1):
                Y=[list(r) for r in X]
                if X[i][j]==-1: Y[i]=[-x for x in Y[i]]
                beta=Y[i]
                Z=[r[:] for r in Y]
                Z[i][j]=-1
                for r in range(m):
                    if r==i: continue
                    a=Y[r][j]
                    for c in range(n):
                        if c==j: continue
                        Z[r][c]=Y[r][c]-a*beta[c]
                out.append(tuple(tuple(r) for r in Z))
    return out
if __name__=="__main__":
    seen={canon(A6):A6}; stack=[A6]
    maxe=0
    while stack:
        X=stack.pop()
        for Y in ops(X):
            if Y and len(Y[0])==0: Y=()
            maxe=max([maxe]+[abs(x) for r in Y for x in r])
            c=canon(Y) if Y else (len(Y),0,())
            if c not in seen:
                seen[c]=Y; stack.append(Y)
        if len(seen)%200==0: print(len(seen),file=sys.stderr)
    print('classes',len(seen),'max entry',maxe)
    print('A3 in', canon(A3) in seen, 'A4 in', canon(A4) in seen)
    from collections import Counter
    print(Counter((k[0],k[1]) for k in seen))
    import pickle; pickle.dump(seen,open('minors.pkl','wb'))
