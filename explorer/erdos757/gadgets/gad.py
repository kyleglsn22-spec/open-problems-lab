import random, sys, itertools, math
import numpy as np
from fractions import Fraction as F

def nullspace(n, edges):
    # rows: x_i + x_k - 2 x_j = 0 ; exact fractions, returns integer basis vectors
    rows=[]
    for (i,j,k) in edges:
        r=[F(0)]*n; r[i]+=1; r[k]+=1; r[j]-=2; rows.append(r)
    piv=[]; R=[]
    for r in rows:
        r=r[:]
        for (pc,pr) in zip(piv,R):
            if r[pc]!=0:
                f=r[pc]; r=[a-f*b for a,b in zip(r,pr)]
        nz=[c for c in range(n) if r[c]!=0]
        if not nz: continue
        c=nz[0]; f=r[c]; r=[a/f for a in r]
        # eliminate from existing
        R=[[a-pr[c]*b for a,b in zip(pr,r)] if pr[c]!=0 else pr for pr in R]
        piv.append(c); R.append(r)
    free=[c for c in range(n) if c not in piv]
    basis=[]
    for fc in free:
        v=[F(0)]*n; v[fc]=F(1)
        for pc,pr in zip(piv,R): v[pc]=-pr[fc]
        l=math.lcm(*[x.denominator for x in v]); basis.append([int(x*l) for x in v])
    return basis, len(piv)

def realize(n, edges, rng=random):
    basis,rank=nullspace(n,edges)
    y=[0]*n
    for b in basis:
        r=rng.randint(-10**9,10**9)
        y=[a+r*c for a,c in zip(y,b)]
    return y

def check(n, edges, y):
    if len(set(y))<n: return False
    E=set(edges); mids={}
    pairs=set()
    for (i,j,k) in edges:
        for pr in ((i,j),(j,k),(i,k)):
            pr=tuple(sorted(pr))
            if pr in pairs: return False
            pairs.add(pr)
    sums={}
    for i in range(n):
        for k in range(i+1,n):
            s=y[i]+y[k]
            if s in sums:
                for (a,b) in sums[s]:
                    if len({a,b,i,k})==4: return False
                sums[s].append((i,k))
            else: sums[s]=[(i,k)]
    ap=0
    for j in range(n):
        for (i,k) in sums.get(2*y[j],[]):
            if j in (i,k): continue
            ap+=1
    return ap==len(edges)

def masks_indep(n, edges):
    M=np.arange(1<<n,dtype=np.int64)
    ok=np.ones(1<<n,dtype=bool)
    for e in edges:
        em=sum(1<<v for v in e); ok &= (M & em)!=em
    idx=M[ok]; sz=np.zeros(len(idx),dtype=np.int64)
    for v in range(n): sz+= (idx>>v)&1
    return idx, sz

def growth(n, edges, y, idx=None, sz=None):
    if idx is None: idx,sz=masks_indep(n,edges)
    order=sorted(range(n),key=lambda v:y[v]); lo,hi=order[0],order[-1]
    best=(9e9,None)
    bits=[(idx>>v)&1 for v in range(n)]
    for (a,b) in ((lo,hi),(hi,lo)):
      base=sz-bits[a]-bits[b]; kin=2*bits[a]+bits[b]
      for p in range(n):
        for q in range(n):
          if p==q or {p,q}=={a,b}: continue
          key=kin*4+2*bits[p]+bits[q]
          W=np.full(16,-10**9,dtype=np.int64); np.maximum.at(W,key,base)
          W=W.reshape(4,4)
          # max cycle mean over 4 nodes
          g=-1e9
          for L in range(1,5):
            for cyc in itertools.product(range(4),repeat=L):
              if cyc[0]!=min(cyc): continue
              s=sum(W[cyc[t],cyc[(t+1)%L]] for t in range(L))
              g=max(g,s/L)
          if g<best[0]: best=(g,(a,b,p,q))
    return best

if __name__=="__main__":
    O=[0,49,75,83,98,101,117,119,121,159,269]
    st=set(O); n=len(O)
    E=[(O.index(a),O.index((a+c)//2),O.index(c)) for a,c in itertools.combinations(O,2) if (a+c)%2==0 and (a+c)//2 in st]
    y=realize(n,E); print(check(n,E,y), nullspace(n,E)[1], growth(n,E,y))

def in_rowspan(n, edges, rel):
    """exact: is the relation (dict v->coef) a rational combination of the edge relations?"""
    rows=[]
    for (i,j,k) in edges:
        r=[F(0)]*n; r[i]+=1; r[k]+=1; r[j]-=2; rows.append(r)
    def rank(R):
        R=[r[:] for r in R]; rk=0; col=0
        for c in range(n):
            piv=next((i for i in range(rk,len(R)) if R[i][c]!=0),None)
            if piv is None: continue
            R[rk],R[piv]=R[piv],R[rk]
            for i in range(len(R)):
                if i!=rk and R[i][c]!=0:
                    f=R[i][c]/R[rk][c]; R[i]=[a-f*b for a,b in zip(R[i],R[rk])]
            rk+=1
        return rk
    v=[F(0)]*n
    for a,c in rel.items(): v[a]+=c
    return rank(rows)==rank(rows+[v])
