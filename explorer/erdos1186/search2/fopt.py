import json,sys,numpy as np
from scipy.optimize import minimize
from rc import word_arcs
from rcf import dens
def unpack(x,n):
    inner=np.sort(np.clip(x[:n-1],0,1)); q=np.clip(x[n-1:],0,1)
    return np.concatenate([[0],inner,[1]]),q
def f(x,n): return dens(*unpack(x,n))
def local(x,n,h=1e-7,maxiter=1000):
    def fg(x):
        f0=f(x,n); g=np.empty_like(x)
        for i in range(len(x)):
            e=np.zeros_like(x);e[i]=h; g[i]=(f(x+e,n)-f(x-e,n))/(2*h)
        return f0,g
    r=minimize(fg,x,jac=True,method='L-BFGS-B',bounds=[(0,1)]*len(x),options={'maxiter':maxiter,'ftol':1e-15,'gtol':1e-11})
    return r.x,r.fun
if __name__=='__main__':
    d=json.load(open('zp_k4_c.json'))
    bp,c=word_arcs(d['2998']['word']); n=len(c)
    x=np.concatenate([bp[1:-1],np.array(c,float)])
    # stage 1: breakpoints only (values fixed 0/1) via same optimizer but values bounded tightly
    x,v=local(x,n); print('stage1 (values free from start)',v,flush=True)
    bpq=unpack(x,n); print('values',np.round(bpq[1],4))
    np.save('fopt1.npy',x)
    # stage 2: split every arc into 3 with free values
    bp,q=bpq; nb=[];nq=[]
    for g in range(n):
        L,H=bp[g],bp[g+1]; e=min(0.002,(H-L)/4)
        nb+= [L, L+e, H-e]; nq+=[q[g]]*3
    nb.append(1.0); n2=len(nq)
    x2=np.concatenate([nb[1:-1],nq]); print('split start',f(x2,n2),flush=True)
    rng=np.random.default_rng(0)
    x2,v2=local(x2,n2); print('stage2',v2,flush=True)
    for h in range(int(sys.argv[1]) if len(sys.argv)>1 else 10):
        y=x2.copy(); y[n2-1:]=np.clip(y[n2-1:]+rng.normal(0,0.2,n2)*(rng.random(n2)<0.15),0,1)
        y,w=local(y,n2)
        if w<v2-1e-13: x2,v2=y,w; print('hop',h,v2,flush=True)
    np.save('fopt2.npy',x2); b2,q2=unpack(x2,n2)
    print('final',v2); print('values',np.round(q2,4)); print('lengths',np.round(np.diff(b2),5))
