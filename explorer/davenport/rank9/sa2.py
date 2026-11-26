# General: lower = nW copies of W (C_6^4 each) + t box coords with cap 4; L u-terms with u=1.
import itertools, numpy as np, sys, math
from sig import reach, W
seed=int(sys.argv[4]); rng=np.random.default_rng(seed)
nW=int(sys.argv[1]); t=int(sys.argv[2]); L=int(sys.argv[3]); iters=int(sys.argv[5]) if len(sys.argv)>5 else 300000
R=reach(W,4); MISS=~R
pw=np.array([1,6,36,216])
subs=[I for s in range(6,L+1,6) for I in itertools.combinations(range(L),s)]
A=np.zeros((len(subs),L),np.int64)
for r,I in enumerate(subs): A[r,list(I)]=1
C=4*nW+t
X=rng.integers(0,6,(L,C))
S=(A@X)%6
def blocked(S):
    bl=np.zeros(len(S),bool)
    for b in range(nW):
        e=((-S[:,4*b:4*b+4])%6)@pw; bl|=MISS[e]
    if t: bl|=(S[:,4*nW:]==1).any(1)
    return bl
cost=(~blocked(S)).sum(); best=cost
for it in range(iters):
    T=1.5*(1-it/iters)+0.02
    i=rng.integers(L); j=rng.integers(C); v=rng.integers(6); old=X[i,j]
    if v==old: continue
    S2=S.copy(); S2[:,j]=(S[:,j]+A[:,i]*(v-old))%6
    c2=(~blocked(S2)).sum()
    if c2<=cost or rng.random()<math.exp((cost-c2)/T):
        X[i,j]=v; S=S2; cost=c2; best=min(best,cost)
        if cost==0: break
print(nW,t,L,seed,"best",best,"final",cost,flush=True)
if cost==0: print(X.tolist())
