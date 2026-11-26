# variant: allow up to `slack` interior vertices that are not middles (flexible realizations)
import sys, time, json, random, math
from fractions import Fraction as Fr
from itertools import combinations
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from ortools.linear_solver import pywraplp
import ord as OR
from gad import nullspace
from cegar import violation

class Ordered2(OR.Ordered):
    def __init__(self,n,slack):
        self.n=n; self.pool=OR.IDPool(); self.ev={}
        for j in range(1,n-1):
            for i in range(j):
                for k in range(j+1,n): self.ev[(i,j,k)]=self.pool.id(('e',i,j,k))
        self.base=[]
        midv=[]
        for j in range(1,n-1):
            lits=[self.ev[(i,j,k)] for i in range(j) for k in range(j+1,n)]
            self.base+=CardEnc.atmost(lits,1,vpool=self.pool,encoding=EncType.seqcounter).clauses
            mj=self.pool.id(('mid',j)); midv.append(mj)
            self.base.append([-mj]+lits)
            for l in lits: self.base.append([-l,mj])
        self.base+=CardEnc.atleast(midv,n-2-slack,vpool=self.pool,encoding=EncType.totalizer).clauses
        pe={}
        for e,x in self.ev.items():
            for pr in combinations(e,2): pe.setdefault(pr,[]).append(x)
        self.pe=pe
        for pr,l in pe.items():
            if len(l)>1: self.base+=CardEnc.atmost(l,1,vpool=self.pool,encoding=EncType.seqcounter).clauses

def lp_point(n,E):
    s=pywraplp.Solver.CreateSolver('GLOP'); x=[s.NumVar(0,1e6,'') for _ in range(n)]
    s.Add(x[0]==0)
    for i in range(n-1): s.Add(x[i+1]-x[i]>=1)
    for (i,j,k) in E: s.Add(x[i]+x[k]-2*x[j]==0)
    # aim for interior: maximize nothing special
    s.Minimize(x[n-1])
    if s.Solve()!=pywraplp.Solver.OPTIMAL: return None
    return [Fr(v.solution_value()).limit_denominator(10**6) for v in x]

def generic_increasing(n,E,rng):
    basis,rank=nullspace(n,E)
    # find increasing point in V: combine basis with LP over coefficients
    d=len(basis)
    s=pywraplp.Solver.CreateSolver('GLOP'); c=[s.NumVar(-1e6,1e6,'') for _ in range(d)]
    for i in range(n-1): s.Add(sum(c[t]*(basis[t][i+1]-basis[t][i]) for t in range(d))>=1)
    if s.Solve()!=pywraplp.Solver.OPTIMAL: return None
    c0=[Fr(v.solution_value()).limit_denominator(1000) for v in c]
    for _ in range(20):
        cc=[ci*3+Fr(rng.randint(-10**6,10**6),10**6) for ci in c0]
        y=[sum(cc[t]*basis[t][i] for t in range(d)) for i in range(n)]
        if all(y[i+1]>y[i] for i in range(n-1)):
            l=1
            for v in y: l=l*v.denominator//math.gcd(l,v.denominator)
            return [int(v*l) for v in y]
    return None

def conflict2(n,E,rng):
    y=generic_increasing(n,E,rng)
    if y is None:
        cur=list(E)
        for e in list(cur):
            t=[z for z in cur if z!=e]
            if not OR.lp_feasible(n,t): cur=t
        return cur,None
    rel=violation(n,E,y)
    if rel is None: return None,y
    if not OR.holds_rel(n,E,rel):
        # accidental; resample a few times
        for _ in range(5):
            y=generic_increasing(n,E,rng); rel=violation(n,E,y)
            if rel is None: return None,y
            if OR.holds_rel(n,E,rel): break
        else: return 'skip',None
    cur=list(E)
    for e in list(cur):
        t=[z for z in cur if z!=e]
        if OR.holds_rel(n,t,rel): cur=t
    return cur,y

def search2(n,num,den,ports,slack=1,PM=4):
    rng=random.Random(1)
    O=Ordered2(n,slack); db=[]
    for (p,q) in ports:
        t0=time.time()
        S=Cadical153(bootstrap_with=O.base+O.growth_clauses(p,q,num,den,PM))
        for pat in db:
            for c in O.lifted(pat): S.add_clause(c)
        it=0; res='?'
        while True:
            it+=1
            if not S.solve(): res='UNSAT'; break
            m=set(l for l in S.get_model() if l>0)
            E=[e for e,x in O.ev.items() if x in m]
            conf,y=conflict2(n,E,rng)
            if conf is None: res=('REALIZABLE',E,y); break
            if conf=='skip':
                S.add_clause([-O.ev[e] for e in E]); continue
            pat=OR.relpattern(conf); db.append(pat)
            for c in O.lifted(pat): S.add_clause(c)
        print(f"[slack{slack}] n={n} G={num}/{den} ports=({p},{q}) -> {res if isinstance(res,str) else res[0]} iters={it} conflicts={len(db)} {time.time()-t0:.1f}s",flush=True)
        if not isinstance(res,str):
            print("FOUND",json.dumps(dict(n=n,G=[num,den],ports=[0,n-1,p,q],edges=res[1],y=res[2])),flush=True)
if __name__=="__main__":
    n,num,den,slack=map(int,sys.argv[1:5])
    seen=set(); P2=[]
    for p in range(1,n-1):
        for q in range(1,n-1):
            if p==q: continue
            if (n-1-q,n-1-p) in seen: continue
            seen.add((p,q)); P2.append((p,q))
    search2(n,num,den,P2,slack)
