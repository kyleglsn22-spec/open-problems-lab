import numpy as np, sys, re, json, math, time
from numba import njit

def parse(fn):
    G=None; pairs=[]
    for line in open(fn):
        if line.startswith('G '):
            p=line.split(' ',3); G=(p[1],int(p[2]),json.loads(p[3]))
        elif line.startswith('P '):
            m=re.match(r'P (\d+) (\d+) (\[.*\]) (\[.*\])\s*$',line)
            pairs.append((int(m.group(1)),int(m.group(2)),json.loads(m.group(3)),json.loads(m.group(4))))
    return G,pairs

def closure(gens,n):
    e=np.arange(n,dtype=np.int16)
    gens=[np.array(g,dtype=np.int16)-1 for g in gens]
    seen={e.tobytes():e}; frontier=[e]
    while frontier:
        nf=[]
        for x in frontier:
            for g in gens:
                y=g[x]  # x*g in GAP convention: (x*g)[i]=g[x[i]]
                k=y.tobytes()
                if k not in seen: seen[k]=y; nf.append(y)
        frontier=nf
    return np.array(list(seen.values()))

def mul(a,b):  # GAP a*b
    return b[a]

def build(Hel,Jel):
    """rows: y in J, cols: z in H; x=y*z. returns d,w,lc,rc arrays"""
    nJ,nH=len(Jel),len(Hel)
    X=Hel[None,:,:][np.zeros(nJ,int)]  # placeholder
    # x[yi,zi] = z[y]
    X=np.take_along_axis(Hel[None,:,:].repeat(nJ,0), Jel[:,None,:].repeat(nH,1).astype(np.int64),axis=2)
    dcid={}; sizes=[]
    d=np.zeros((nJ,nH),np.int64); lc=np.zeros((nJ,nH),np.int64); rc=np.zeros((nJ,nH),np.int64)
    lcid={}; rcid={}
    for a in range(nJ):
        for b in range(nH):
            x=X[a,b]; k=x.tobytes()
            if k not in dcid:
                # H x J : (h*x*j)[i]=j[x[h[i]]]
                hx=x[Hel]              # (nH,n): rows h*x
                hxj=Jel[:,hx].transpose(1,0,2).reshape(-1,x.shape[0]) if False else None
                # compute h*x*j = j[hx]
                allp=np.take(Jel, hx, axis=1) # shape (nJ, nH, n)
                allp=allp.reshape(-1,x.shape[0])
                u=np.unique(allp,axis=0)
                idx=len(sizes); sizes.append(len(u))
                for row in u: dcid[row.tobytes()]=idx
            d[a,b]=dcid[k]
            xj=Jel[:,x] if False else np.take(Jel,x,axis=1).T  # x*j = j[x] -> rows
            # xJ: set {j[x]} for j in J -> canonical min
            m=np.take(Jel,x,axis=1)  # (nJ, n)  each row j[x]? take(Jel,x,axis=1)[j,i]=Jel[j,x[i]] = (x*j)[i]
            key=min(r.tobytes() for r in m)
            lc[a,b]=lcid.setdefault(key,len(lcid))
            mh=x[Hel]  # (h*x)[i]=x[h[i]]
            key=min(r.tobytes() for r in mh)
            rc[a,b]=rcid.setdefault(key,len(rcid))
    return d,np.array(sizes,np.int64),lc,rc

@njit(cache=True)
def score(rows,cols,d,w,lc,rc,nJ,nH,nd,nl,nr):
    # rows/cols: boolean arrays
    seenD=np.zeros(nd,np.bool_); seenL=np.zeros(nl,np.bool_); seenR=np.zeros(nr,np.bool_)
    S=0; NL=0; NR=0
    for a in range(len(rows)):
        if rows[a]:
            for b in range(len(cols)):
                if cols[b]:
                    k=d[a,b]
                    if not seenD[k]: seenD[k]=True; S+=w[k]
                    k=lc[a,b]
                    if not seenL[k]: seenL[k]=True; NL+=1
                    k=rc[a,b]
                    if not seenR[k]: seenR[k]=True; NR+=1
    if S==0: return -1e9,0,0,0,0,0
    N2=0
    tmp=np.zeros(nd,np.bool_)
    for a in range(len(rows)):
        if rows[a]:
            tmp[:]=False; s=0
            for b in range(len(cols)):
                if cols[b]:
                    k=d[a,b]
                    if not tmp[k]: tmp[k]=True; s+=w[k]
            if s>N2: N2=s
    N3=0
    for b in range(len(cols)):
        if cols[b]:
            tmp[:]=False; s=0
            for a in range(len(rows)):
                if rows[a]:
                    k=d[a,b]
                    if not tmp[k]: tmp[k]=True; s+=w[k]
            if s>N3: N3=s
    N1=NL*nJ; N4=NR*nH
    val=3*math.log(S)-math.log(N1)-math.log(N2)-math.log(N3)-math.log(N4)
    return val,S,N1,N2,N3,N4

@njit(cache=True)
def anneal(d,w,lc,rc,nJ,nH,nd,nl,nr,iters,seed,T0):
    np.random.seed(seed)
    R=d.shape[0]; C=d.shape[1]
    rows=np.random.random(R)<0.3; cols=np.random.random(C)<0.3
    rows[0]=True; cols[0]=True
    cur=score(rows,cols,d,w,lc,rc,nJ,nH,nd,nl,nr)[0]
    best=cur; br=rows.copy(); bc=cols.copy()
    for it in range(iters):
        T=T0*(1-it/iters)+1e-4
        if np.random.random()<0.5:
            i=np.random.randint(R); rows[i]=not rows[i]
            v=score(rows,cols,d,w,lc,rc,nJ,nH,nd,nl,nr)[0]
            if v>=cur or np.random.random()<math.exp((v-cur)/T): cur=v
            else: rows[i]=not rows[i]
        else:
            i=np.random.randint(C); cols[i]=not cols[i]
            v=score(rows,cols,d,w,lc,rc,nJ,nH,nd,nl,nr)[0]
            if v>=cur or np.random.random()<math.exp((v-cur)/T): cur=v
            else: cols[i]=not cols[i]
        if cur>best: best=cur; br=rows.copy(); bc=cols.copy()
    return best,br,bc

def run(fn,iters=20000,restarts=4,maxpairs=10**9):
    G,pairs=parse(fn); name,order,gg=G; n=len(gg[0])
    t=time.time(); out=[]
    for pi,(h,j,hg,jg) in enumerate(pairs[:maxpairs]):
        Hel=closure(hg,n); Jel=closure(jg,n)
        # put identity first
        def idfirst(E):
            e=np.arange(n); k=[i for i in range(len(E)) if (E[i]==e).all()][0]
            E=E.copy(); E[[0,k]]=E[[k,0]]; return E
        Hel=idfirst(Hel); Jel=idfirst(Jel)
        d,w,lc,rc=build(Hel,Jel)
        nd=len(w); nl=lc.max()+1; nr=rc.max()+1
        bestv=-1e9
        for s in range(restarts):
            v,br,bc=anneal(d,w,lc,rc,len(Jel),len(Hel),nd,nl,nr,iters,s+1,0.05)
            if v>bestv: bestv=v; B=(br,bc)
        sc=score(B[0],B[1],d,w,lc,rc,len(Jel),len(Hel),nd,nl,nr)
        out.append((bestv,pi,h,j,sc[1:],int(B[0].sum()),int(B[1].sum())))
    out.sort(reverse=True)
    print(name,order,'pairs',len(pairs),'time %.1f'%(time.time()-t))
    for o in out[:5]: print('  ratio %.5f'%math.exp(o[0]),o[1:])
    return out

if __name__=='__main__':
    run(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 20000, maxpairs=int(sys.argv[3]) if len(sys.argv)>3 else 10**9)
