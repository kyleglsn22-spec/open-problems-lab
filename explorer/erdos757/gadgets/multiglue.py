# Multi-point self-similar gluing: S_{K+1} = O ∪ φ(S_K), φ affine contraction mapping >=2 points of O into O.
import sys, itertools
from fractions import Fraction as F
def aps(A):
    S=set(A); L=sorted(A); out=[]
    for i,a in enumerate(L):
        for c in L[i+1:]:
            m=(a+c)/2
            if m in S: out.append((a,m,c))
    return out
def is45(A):
    L=sorted(A); S=set(L); sums={}
    for i,a in enumerate(L):
        for b in L[i+1:]:
            s=a+b
            if s in sums: return False
            sums[s]=(a,b)
    # pair sums distinct also kills 2a=b+c? no: that is an AP (a,a) not counted. check APs sharing 2 pts
    seen={}
    for t in aps(L):
        for pr in itertools.combinations(t,2):
            if pr in seen: return False
            seen[pr]=t
    return True
def apfree_sets(O):
    n=len(O); idx={x:i for i,x in enumerate(O)}
    masks=[(1<<idx[a])|(1<<idx[b])|(1<<idx[c]) for a,b,c in aps(O)]
    res=[]
    def rec(i,m):
        if i==n: res.append(m); return
        rec(i+1,m)
        m2=m|(1<<i)
        if all((m2&t)!=t for t in masks): rec(i+1,m2)
    rec(0,0); return res
def karp(W,N):
    # max cycle mean, W[s][t] or None
    INF=float('-inf'); best=None
    D=[[INF]*N for _ in range(N+1)]
    for s0 in range(N): D[0][s0]=0
    for k in range(1,N+1):
        for t in range(N):
            D[k][t]=max((D[k-1][s]+W[s][t] for s in range(N) if W[s][t] is not None and D[k-1][s]>INF),default=INF)
    for v in range(N):
        if D[N][v]==INF: continue
        m=min((F(D[N][v]-D[k][v],N-k) for k in range(N) if D[k][v]>INF),default=None)
        if m is not None and (best is None or m>best): best=m
    return best
def phi_of(a,b,p,q):
    r=F(q-p)/F(b-a); return lambda x: p+(x-a)*r, r
def analyze(O, verbose=False, target=F(5,9)):
    O=sorted(F(x) for x in O); n=len(O); Oset=set(O); idx={x:i for i,x in enumerate(O)}
    sets=apfree_sets(O); found=[]
    for a,b in itertools.combinations(O,2):
        for p,q in itertools.permutations(O,2):
            if abs(q-p)>=b-a: continue
            ph,r=phi_of(a,b,p,q)
            im=[ph(x) for x in O]
            G=[y for y in im if y in Oset]           # shared, in parent coords
            if len(G)<2: continue
            Gp=[x for x in O if ph(x) in Oset]        # shared, in child coords
            if set(G)&set(Gp): continue
            im2=set(ph(y) for y in im)
            if im2&Oset: continue
            k=len(G); gi=[idx[g] for g in G]; gpi=[idx[g] for g in Gp]
            # state = bits over Gp order; child's incoming state = parent's outgoing bits mapped by phi
            # parent outgoing bits on G: G[j]=ph(Gp[j]) since built in O order
            N=1<<k; W=[[None]*N for _ in range(N)]
            for m in sets:
                s=sum(1<<j for j,i in enumerate(gpi) if m>>i&1)
                t=sum(1<<j for j,x in enumerate(Gp) if m>>idx[ph(x)]&1)
                val=bin(m).count('1')-bin(s).count('1')
                if W[s][t] is None or val>W[s][t]: W[s][t]=val
            # transition: copy's t (bits on its G, indexed by Gp order j) -> child's s with same bits
            g=karp(W,N); ratio=g/(n-k)
            found.append((ratio,k,(a,b,p,q),g))
    return found
def chain(O,a,b,p,q,K):
    ph,_=phi_of(F(a),F(b),F(p),F(q)); S=set(F(x) for x in O)
    for _ in range(K): S=set(F(x) for x in O)|set(ph(y) for y in S)
    return S
if __name__=='__main__':
    pass
