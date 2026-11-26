import itertools, numpy as np
n=6
def reach(seq, r):
    # Σ0 over C_n^r, as boolean array indexed by mixed radix
    N=n**r; R=np.zeros(N,bool); R[0]=True
    idx=np.arange(N); digs=np.array([(idx//n**j)%n for j in range(r)])
    for g in seq:
        sh=sum(((digs[j]+g[j])%n)*n**j for j in range(r))
        R2=R.copy(); R2[sh[R]]=True; R=R2
    return R
k=3; z=(1,1,1,(1-3*k)%n); f=(0,0,0,1)
W=[z]+[f]*3
for j in range(3):
    e=[0]*4; e[j]=1; W+= [tuple(e)]*2; e[3]=1; W+=[tuple(e)]*3
R=reach(W,4); print(len(W), R.sum(), "of", n**4, "reachable incl 0")
