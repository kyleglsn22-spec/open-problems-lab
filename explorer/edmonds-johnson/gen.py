from fractions import Fraction as F
import itertools, math, sys
import numpy as np
from scipy.optimize import linprog

def solve(M, r):
    n=len(M); A=[[F(x) for x in row]+[F(rr)] for row,rr in zip(M,r)]
    for col in range(n):
        piv=next((i for i in range(col,n) if A[i][col]!=0),None)
        if piv is None: return None
        A[col],A[piv]=A[piv],A[col]
        for i in range(n):
            if i!=col and A[i][col]!=0:
                f=A[i][col]/A[col][col]; A[i]=[a-f*b for a,b in zip(A[i],A[col])]
    return [A[i][n]/A[i][i] for i in range(n)]

def analyse(A,b,c,l,u,z):
    m=len(A); n=len(A[0])
    S=[]
    for i in range(m): S.append((A[i],c[i])); S.append(([-a for a in A[i]],-b[i]))
    for j in range(n):
        e=[0]*n; e[j]=1; S.append((e,u[j])); S.append(([-t for t in e],-l[j]))
    dot=lambda a,x: sum(F(p)*q for p,q in zip(a,x))
    inP=lambda x: all(dot(nn,x)<=h for nn,h in S)
    V=set()
    for comb in itertools.combinations(range(len(S)),n):
        M=np.array([S[i][0] for i in comb],dtype=float)
        if abs(np.linalg.det(M))<1e-9: continue
        x=solve([S[i][0] for i in comb],[S[i][1] for i in comb])
        if x is not None and inP(x): V.add(tuple(x))
    V=sorted(V)
    D=math.lcm(*[t.denominator for v in V for t in v])
    assert inP(z)
    # box bounds for w: w.(v-z) <= 2/3 - 1/D
    Dm=np.array([[float(vi-zi) for vi,zi in zip(v,z)] for v in V]); bound=2/3-1/D
    box=[]
    for j in range(n):
        lo=hi=None
        for s in (1,-1):
            cc=np.zeros(n); cc[j]=-s
            r=linprog(cc,A_ub=Dm,b_ub=np.full(len(V),bound),bounds=[(None,None)]*n)
            val=-r.fun
            if s==1: hi=math.floor(val+1e-9)
            else: lo=-math.floor(val+1e-9)
        box.append((lo,hi))
    # brute check the integer statement on the box
    for w in itertools.product(*[range(lo,hi+1) for lo,hi in box]):
        k=math.ceil(dot(w,z))
        assert max(dot(w,v) for v in V)>=k, w
    # hull separator
    rng=[range(int(l[j]),int(u[j])+1) for j in range(n)]
    pts=[x for x in itertools.product(*rng) if all(b[i]<=sum(a*t for a,t in zip(A[i],x))<=c[i] for i in range(m)) ]
    sep=None
    for w0 in sorted(itertools.product(range(-2,3),repeat=n),key=lambda w:sum(map(abs,w))):
        if not any(w0): continue
        r0=max(sum(a*t for a,t in zip(w0,x)) for x in pts)
        if dot(w0,z)>r0: sep=(w0,r0); break
    return V,D,box,sep,len(pts)

if __name__=='__main__':
    A6=[[0,0,1,-1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
    z=[F(2,3),F(1,3)]*3
    V,D,box,sep,np_=analyse(A6,[0,2,1,1,0],[2,4,3,3,2],[-1,0,-1,0,-1,-1],[1,2,1,2,2,2],z)
    print(len(V),D,box,math.prod(h-l+1 for l,h in box),sep,np_)
