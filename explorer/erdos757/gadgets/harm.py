import numpy as np, random, sys, json, itertools, time
from sa import CI
from gad import masks_indep
def solve(n, P):
    # vertices 0 (val 0), 1 (val 1); interior v: x_v = (x_i+x_k)/2
    A=np.zeros((n,n)); rhs=np.zeros(n)
    A[0,0]=1; A[1,1]=1; rhs[1]=1
    for v in range(2,n):
        i,k=P[v]; A[v,v]+=1; A[v,i]-=0.5; A[v,k]-=0.5
    try: y=np.linalg.solve(A,rhs)
    except np.linalg.LinAlgError: return None
    if not np.all(np.isfinite(y)): return None
    return y
IU=None
def violations(n,P,y,tol=1e-9):
    bad=0
    # linearity
    cnt={}
    for v in range(2,n):
        i,k=P[v]
        for pr in ((min(i,v),max(i,v)),(min(k,v),max(k,v)),(min(i,k),max(i,k))):
            cnt[pr]=cnt.get(pr,0)+1
    bad+=sum(c-1 for c in cnt.values() if c>1)
    ys=np.sort(y); bad+=int(np.sum(np.diff(ys)<tol))*3
    iu=np.triu_indices(n,1)
    s=y[iu[0]]+y[iu[1]]; o=np.argsort(s); ss=s[o]
    close=np.where(np.diff(ss)<tol)[0]
    for c in close:
        a=o[c]; b=o[c+1]
        if len({iu[0][a],iu[1][a],iu[0][b],iu[1][b]})==4: bad+=1
    # unintended APs: 2y_j equals some sum not the designated
    for j in range(n):
        d=2*y[j]; lo=np.searchsorted(ss,d-tol); hi=np.searchsorted(ss,d+tol)
        for c in range(lo,hi):
            a=o[c]; i,k=iu[0][a],iu[1][a]
            if j in (i,k): continue
            if j<2 or set(P[j])!={i,k}: bad+=1
    # also values must be strictly inside (0,1) for interior
    bad+=int(np.sum((y[2:]<tol)|(y[2:]>1-tol)))*3
    return bad
def growth(n,edges,a,b):
    idx,sz=masks_indep(n,edges)
    bits=np.array([(idx>>v)&1 for v in range(n)]).T.astype(bool)
    best=(9e9,None)
    for (a,b) in ((a,b),(b,a)):
        base=(sz-bits[:,a]-bits[:,b]).astype(np.float64)
        W=np.full((n,n,16),-1e6)
        for sa_ in (0,1):
          for sb in (0,1):
            sel=(bits[:,a]==sa_)&(bits[:,b]==sb)
            B=bits[sel]; bs=base[sel]
            for tp in (0,1):
              for tq in (0,1):
                mp=(B==tp); mq=(B==tq)
                W[:,:,(2*sa_+sb)*4+2*tp+tq]=np.where(mp[:,:,None]&mq[:,None,:], bs[:,None,None], -1e6).max(0)
        G=(W@CI.T).max(2)
        for v in range(n): G[v,v]=9e9
        G[a,:]=9e9; G[:,a]=9e9; G[b,:]=9e9; G[:,b]=9e9  # ports interior
        p,q=np.unravel_index(np.argmin(G),G.shape)
        if G[p,q]<best[0]-1e-9: best=(float(G[p,q]),(a,b,int(p),int(q)))
    return best, int(sz.max())
def edges_of(n,P): return [(P[v][0],v,P[v][1]) for v in range(2,n)]
def score(n,P):
    y=solve(n,P)
    if y is None: return 1e6,None,None
    bad=violations(n,P,y)
    if bad: return 100+bad*10,y,None
    (g,ports),al=growth(n,edges_of(n,P),0,1)
    return g/(n-2),y,(g,ports,al)
def rand_pair(n,v,rng):
    i,k=rng.sample([u for u in range(n) if u!=v],2); return (i,k)
def run(n,seed,iters,target):
    rng=random.Random(seed)
    P=[None,None]+[rand_pair(n,v,rng) for v in range(2,n)]
    cur,_,_=score(n,P); best=9e9
    for it in range(iters):
        Q=list(P); v=rng.randrange(2,n); Q[v]=rand_pair(n,v,rng)
        if rng.random()<0.3:
            v2=rng.randrange(2,n); Q[v2]=rand_pair(n,v2,rng)
        sc,y,info=score(n,Q)
        T=0.02+0.5*(1-it/iters)
        if sc<=cur or rng.random()<np.exp(-(sc-cur)/T):
            P=Q; cur=sc
            if info and sc<best-1e-9:
                best=sc
                print(f"n={n} seed={seed} it={it} growth={info[0]}/{n-2}={sc:.4f} alpha(O)={info[2]} ports={info[1]}",flush=True)
                if sc<target-1e-9:
                    print("CANDIDATE",json.dumps(dict(n=n,P=P,y=list(y),info=info)),flush=True)
    return best
if __name__=="__main__":
    n=int(sys.argv[1]); seeds=int(sys.argv[2]); iters=int(sys.argv[3])
    for s in range(seeds):
        b=run(n,s*7919+n,iters,5/9)
        print("END seed",s,b,flush=True)
