import numpy as np, itertools
n=6
def check(W,r):
    N=n**r; idx=np.arange(N); digs=np.array([(idx//n**j)%n for j in range(r)])
    enc=lambda D: sum((np.asarray(D[j])%n)*n**j for j in range(r))
    R=np.zeros(N,bool); R[0]=True
    for g in W:
        if R[enc([-x for x in g])]: return "not zsf"
        sh=enc([digs[j]+g[j] for j in range(r)]); R2=R.copy(); R2[sh[R]]=True; R=R2
    M=set(np.nonzero(~R)[0].tolist())
    sub=lambda a,b: int(enc([digs[j][a]-digs[j][b] for j in range(r)]))
    addv=lambda a,b: int(enc([digs[j][a]+digs[j][b] for j in range(r)]))
    for P in M:
      for T in M:
        if sub(T,P) in M:
          for Q in M:
            if sub(addv(P,T),Q) in M: return ("OK",[tuple(digs[:,v]) for v in (P,T,Q)])
    return ("no",len(M))
z=(1,1,1,4); f=(0,0,0,1)
W=[z]+[f]*3
for j in range(3):
    e=[0]*4; e[j]=1; W+= [tuple(e)]*2; e[3]=1; W+=[tuple(e)]*3
print(check(W,4))
