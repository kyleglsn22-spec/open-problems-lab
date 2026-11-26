import numpy as np, itertools
n=6
def sigma0(W,r):
    N=n**r; idx=np.arange(N); digs=np.array([(idx//n**j)%n for j in range(r)])
    enc=lambda D: sum((np.asarray(D[j])%n)*n**j for j in range(r))
    R=np.zeros(N,bool); R[0]=True
    for g in W:
        assert not R[enc([-x for x in g])], "not zero-sumfree"
        sh=enc([digs[j]+g[j] for j in range(r)]); R2=R.copy(); R2[sh[R]]=True; R=R2
    return R,digs
def targets(W,r):
    # A = { v : -v in Miss } = { v: -v not in Sigma0 }
    R,digs=sigma0(W,r)
    M=np.nonzero(~R)[0]
    return sorted(tuple(int((-digs[j][m])%n) for j in range(r)) for m in M)
def ggwz4():
    z=(1,1,1,4); f=(0,0,0,1); W=[z]+[f]*3
    for j in range(3):
        e=[0]*4; e[j]=1; W+= [tuple(e)]*2; e[3]=1; W+=[tuple(e)]*3
    return W
