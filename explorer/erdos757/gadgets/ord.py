# usage: python3 ord.py n num den [time_limit_s shard nshards PM]
import sys, time, json, itertools
from itertools import combinations
from fractions import Fraction as Fr
from pysat.solvers import Cadical153, Glucose4
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from ortools.linear_solver import pywraplp
from cegar import violation
from gad import realize

class Ordered:
    def __init__(self,n):
        self.n=n; self.pool=IDPool(); self.ev={}
        for j in range(1,n-1):
            for i in range(j):
                for k in range(j+1,n): self.ev[(i,j,k)]=self.pool.id(('e',i,j,k))
        self.base=[]; self.conflicts=[]  # conflicts stored as canonical (relative) patterns
        n=self.n
        for j in range(1,n-1):
            lits=[self.ev[(i,j,k)] for i in range(j) for k in range(j+1,n)]
            self.base+=CardEnc.equals(lits,1,vpool=self.pool,encoding=EncType.seqcounter).clauses
        pe={}
        for e,x in self.ev.items():
            for pr in combinations(e,2): pe.setdefault(pr,[]).append(x)
        self.pe=pe
        for pr,l in pe.items():
            if len(l)>1: self.base+=CardEnc.atmost(l,1,vpool=self.pool,encoding=EncType.seqcounter).clauses
    def growth_clauses(self,p,q,num,den,PM):
        """den*W[s][t] <= num + pi_t - pi_s ; a=0,b=n-1"""
        n=self.n; a,b=0,n-1; pool=self.pool; cl=[]
        for x in self.pe.get((a,b),[]):
            for z in self.pe.get(tuple(sorted((p,q))),[]): cl.append([-x,-z])
        P={(s,v):pool.id(('P',p,q,num,den,s,v)) for s in range(4) for v in range(1,PM+1)}
        ge=lambda s,v: True if v<=0 else (False if v>PM else P[(s,v)])
        for s in range(4):
            for v in range(2,PM+1): cl.append([-P[(s,v)],P[(s,v-1)]])
        cl.append([-P[(s,1)] for s in range(4)])
        D={}
        def Dlit(s,t,d):
            if (s,t,d) in D: return D[(s,t,d)]
            x=pool.id(('D',p,q,num,den,s,t,d)); D[(s,t,d)]=x
            for v in range(0,PM+1):
                A=ge(s,v); B=ge(t,v+d)
                if A is False or B is True: continue
                c=[-x]
                if A is not True: c.append(-A)
                if B is not False: c.append(B)
                cl.append(c)
            return x
        byset={}
        for e,x in self.ev.items(): byset.setdefault(frozenset(e),[]).append(x)
        others=[v for v in range(1,n-1) if v not in (p,q)]
        for s in range(4):
            Sab=[v for v,bit in ((a,s>>1),(b,s&1)) if bit]
            for t in range(4):
                forced=[v for v,bit in ((p,t>>1),(q,t&1)) if bit]
                for k in range(len(forced), len(forced)+len(others)+1):
                    d=den*k-num   # independent X of size k requires pi_t-pi_s >= d
                    if d<=-PM: continue
                    need=k-len(forced)
                    for X in combinations(others,need):
                        Y=set(X)|set(forced)|set(Sab)
                        lits=[x for tr,xs in byset.items() if tr<=Y for x in xs]
                        if d<=PM: lits.append(Dlit(s,t,d))
                        cl.append(lits)
        return cl
    def lifted(self,pattern):
        """pattern: list of edges on relative vertices 0..c-1 ; return clauses for all order-preserving maps"""
        c=1+max(max(e) for e in pattern); out=[]
        for S in combinations(range(self.n),c):
            cls=[]
            ok=True
            for (i,j,k) in pattern:
                e=(S[i],S[j],S[k])
                if e not in self.ev: ok=False; break
                cls.append(-self.ev[e])
            if ok: out.append(cls)
        return out

def exact_solve(n,E):
    # x0=0, x_{n-1}=1, x_j=(x_i+x_k)/2
    A=[[Fr(0)]*n for _ in range(n)]; r=[Fr(0)]*n
    A[0][0]=Fr(1); A[n-1][n-1]=Fr(1); r[n-1]=Fr(1)
    for (i,j,k) in E: A[j][j]+=1; A[j][i]-=Fr(1,2); A[j][k]-=Fr(1,2)
    # gaussian
    M=[row[:]+[rr] for row,rr in zip(A,r)]
    for c in range(n):
        pv=next(rw for rw in range(c,n) if M[rw][c]!=0); M[c],M[pv]=M[pv],M[c]
        f=M[c][c]; M[c]=[x/f for x in M[c]]
        for rw in range(n):
            if rw!=c and M[rw][c]!=0:
                g=M[rw][c]; M[rw]=[x-g*y for x,y in zip(M[rw],M[c])]
    return [M[i][n] for i in range(n)]
def lp_feasible(n,E):
    s=pywraplp.Solver.CreateSolver('GLOP'); x=[s.NumVar(-1e7,1e7,'') for _ in range(n)]
    for i in range(n-1): s.Add(x[i+1]-x[i]>=1)
    for (i,j,k) in E: s.Add(x[i]+x[k]-2*x[j]==0)
    return s.Solve()==pywraplp.Solver.OPTIMAL
def holds_rel(n,E,rel):
    from gad import in_rowspan
    return in_rowspan(n,E,rel)
def conflict(n,E):
    y=exact_solve(n,E)
    if any(y[i+1]<=y[i] for i in range(n-1)):
        cur=list(E)
        for e in list(cur):
            t=[z for z in cur if z!=e]
            if not lp_feasible(n,t): cur=t
        return cur,y
    l=1
    for v in y: l=l*v.denominator//__import__('math').gcd(l,v.denominator)
    yi=[int(v*l) for v in y]
    rel=violation(n,E,yi)
    if rel is None: return None,yi
    cur=list(E)
    for e in list(cur):
        t=[z for z in cur if z!=e]
        if holds_rel(n,t,rel): cur=t
    return cur,yi
def relpattern(conf):
    vs=sorted(set(v for e in conf for v in e)); m={v:i for i,v in enumerate(vs)}
    return [tuple(m[v] for v in e) for e in conf]

def search(n,num,den,ports,PM=4,maxit=10**7,conf_db=None,verbose=True,tlim=None):
    O=Ordered(n); conf_db=conf_db if conf_db is not None else []
    results={}
    for (p,q) in ports:
        t0=time.time()
        S=(Glucose4 if tlim else Cadical153)(bootstrap_with=O.base+O.growth_clauses(p,q,num,den,PM))
        for pat in conf_db:
            for c in O.lifted(pat): S.add_clause(c)
        it=0; res='?'
        while it<maxit:
            it+=1
            if tlim:
                import threading
                tm=threading.Timer(tlim,lambda: S.interrupt()); tm.start()
                r=S.solve_limited(expect_interrupt=True); tm.cancel(); S.clear_interrupt()
                if r is None: res='TIMEOUT'; break
            else: r=S.solve()
            if not r: res='UNSAT'; break
            m=set(l for l in S.get_model() if l>0)
            E=[e for e,x in O.ev.items() if x in m]
            conf,y=conflict(n,E)
            if conf is None:
                res=('REALIZABLE',E,y); break
            pat=relpattern(conf); conf_db.append(pat)
            for c in O.lifted(pat): S.add_clause(c)
        results[(p,q)]=res
        if verbose: print(f"n={n} G={num}/{den} ports=({p},{q}) -> {res if isinstance(res,str) else res[0]} iters={it} conflicts={len(conf_db)} {time.time()-t0:.1f}s",flush=True)
        if not isinstance(res,str):
            print("FOUND",json.dumps(dict(n=n,G=[num,den],ports=[0,n-1,p,q],edges=res[1],y=[int(v) for v in res[2]])),flush=True)
    return results,conf_db
if __name__=="__main__":
    n,num,den=map(int,sys.argv[1:4])
    ports=[(p,q) for p in range(1,n-1) for q in range(1,n-1) if p!=q]
    # reflection symmetry: (p,q) ~ (n-1-q, n-1-p)
    seen=set(); P2=[]
    for (p,q) in ports:
        r=(n-1-q,n-1-p)
        if r in seen: continue
        seen.add((p,q)); P2.append((p,q))
    tl=float(sys.argv[4]) if len(sys.argv)>4 and float(sys.argv[4])>0 else None
    if len(sys.argv)>6:
        sh,nsh=int(sys.argv[5]),int(sys.argv[6]); P2=P2[sh::nsh]
    pm=int(sys.argv[7]) if len(sys.argv)>7 else 4
    search(n,num,den,P2,PM=pm,tlim=tl)
