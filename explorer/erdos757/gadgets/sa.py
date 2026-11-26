import random, sys, itertools, time, json
import numpy as np
from gad import realize, check, masks_indep, nullspace
CYC=[]
for L in range(1,5):
    for cyc in itertools.product(range(4),repeat=L):
        if cyc[0]!=min(cyc): continue
        CYC.append(([cyc[t]*4+cyc[(t+1)%L] for t in range(L)],L))
CI=np.zeros((len(CYC),16)); 
for r,(ix,L) in enumerate(CYC):
    for t in ix: CI[r,t]+=1.0/L
def growth(n,edges,y):
    idx,sz=masks_indep(n,edges)
    order=sorted(range(n),key=lambda v:y[v]); lo,hi=order[0],order[-1]
    bits=np.array([(idx>>v)&1 for v in range(n)]).T.astype(bool)  # sets x n
    best=(9e9,None)
    for (a,b) in ((lo,hi),(hi,lo)):
        base=(sz-bits[:,a]-bits[:,b]).astype(np.float64)
        W=np.full((n,n,16),-1e6)
        for sa_ in (0,1):
          for sb in (0,1):
            sel=(bits[:,a]==sa_)&(bits[:,b]==sb)
            if not sel.any(): continue
            B=bits[sel]; bs=base[sel]
            for tp in (0,1):
              for tq in (0,1):
                mp=(B==tp); mq=(B==tq)
                M=np.where(mp[:,:,None]&mq[:,None,:], bs[:,None,None], -1e6).max(0)
                W[:,:,(2*sa_+sb)*4+2*tp+tq]=M
        G=W@CI.T
        G=G.max(2)
        for v in range(n): G[v,v]=9e9
        G[a,b]=G[b,a]=9e9
        p,q=np.unravel_index(np.argmin(G),G.shape)
        if G[p,q]<best[0]-1e-9: best=(float(G[p,q]),(a,b,int(p),int(q)))
    return best, int(sz.max())
def run(n, seed, iters, T0=0.3):
    rng=random.Random(seed)
    mid=[None]*n; edges=[]
    cur=(9e9,); bestv=9e9; bestrec=None
    def edges_of(mid): return [(i,j,k) for j,(ik) in enumerate(mid) if ik for (i,k) in [ik]]
    for it in range(iters):
        new=mid[:]
        j=rng.randrange(n)
        if new[j] and rng.random()<0.15: new[j]=None
        else:
            i,k=rng.sample([v for v in range(n) if v!=j],2); new[j]=(min(i,k),max(i,k))
        E=edges_of(new)
        y=realize(n,E,rng)
        if not check(n,E,y): continue
        (g,ports),al=growth(n,E,y)
        val=g/(n-2) - 0.001*len(E)
        T=T0*(1-it/iters)+1e-3
        if val<=cur[0] or rng.random()<np.exp(-(val-cur[0])/T*10):
            mid=new; cur=(val,)
            if g/(n-2)<bestv-1e-9:
                bestv=g/(n-2); bestrec=dict(n=n,edges=E,y=y,g=g,ports=ports,alpha=al)
                print(f"n={n} seed={seed} it={it} growth={g}/{n-2}={g/(n-2):.4f} alpha(O)={al} m={len(E)}",flush=True)
                if bestv<5/9-1e-9:
                    print("BEAT", json.dumps(bestrec,default=int),flush=True)
    return bestrec
if __name__=="__main__":
    n=int(sys.argv[1]); seeds=int(sys.argv[2]); iters=int(sys.argv[3])
    for s in range(seeds):
        r=run(n,s+1000*n,iters)
        print("END",n,s,r['g'] if r else None,json.dumps(r,default=int),flush=True)
