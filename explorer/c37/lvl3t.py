# Level-3 type counting for profile C* (n=14,d=5).
import itertools, sys, time, os
from math import comb
from ortools.sat.python import cp_model
from lvl1 import split_types
from lvl2 import pair_types, enum_all, level1_solutions
n,d=14,5
C=[0,14,-91,224,-231,84]
def setup(nn,dd,CC):
    global n,d,C
    n,d,C=nn,dd,CC
def triple_types(t,P):
    # t[0..2]: singleton type vectors (T2..T5); P[(0,1)],P[(0,2)],P[(1,2)] pair vectors (T2..T5 of the pair)
    M=cp_model.CpModel()
    Q={l:M.NewIntVar(-10**5,10**5,f"Q{l}") for l in range(3,d+1)}
    def Tv(B,l):
        if l>d or l<len(B): return 0
        if len(B)==0: return C[l]
        if len(B)==1: return 1 if l==1 else t[B[0]][l-2]
        if len(B)==2: return P[B][l-2] if l>=2 else 0
        return Q[l]
    A=(0,1,2); m=n-3
    D={}
    for r in range(4):
        for B in itertools.combinations(A,r):
            rest=[a for a in A if a not in B]
            for l0 in range(0,d-r+1):
                l=l0+r; e=0
                for s in range(len(rest)+1):
                    for E in itertools.combinations(rest,s):
                        e+=(-1)**s*Tv(tuple(sorted(B+E)),l)
                D[l0,B]=e
    for r in range(4):
        for X in itertools.combinations(A,r):
            for w0 in range(m+1):
                e=0
                for rb in range(r+1):
                    for B in itertools.combinations(X,rb):
                        for l0 in range(0,min(w0,d-rb)+1):
                            e+=D[l0,B]*comb(m-l0,w0-l0)
                cap=comb(m,w0)
                if isinstance(e,int):
                    if not 0<=e<=cap: return []
                else: M.Add(e>=0); M.Add(e<=cap)
    return enum_all(M,[Q[l] for l in range(3,d+1)])
def main(tl):
    TY=split_types(n,d,C); K=len(TY)
    PT={}
    for a in range(K):
        for b in range(a,K):
            PT[a,b]=pair_types(n,d,C,TY[a],TY[b]); PT[b,a]=PT[a,b]
    use=[a for a in range(K) if PT[a,a] or any(PT[a,b] for b in range(K) if b!=a)]
    print('usable types',[TY[a] for a in use],flush=True)
    # triple classes keyed by ordered (a,b,c,Pab,Pac,Pbc)
    TT={}
    for a,b,c in itertools.product(use,repeat=3):
        for Pab in PT[a,b]:
            for Pac in PT[a,c]:
                for Pbc in PT[b,c]:
                    key=(a,b,c,Pab,Pac,Pbc)
                    tt=triple_types([TY[a],TY[b],TY[c]],{(0,1):Pab,(0,2):Pac,(1,2):Pbc})
                    if tt: TT[key]=tt
    print('triple classes',len(TT),'triple vectors',sum(len(v) for v in TT.values()),flush=True)
    sols=[s for s in level1_solutions(n,d,C,TY) if all(s[a]==0 for a in range(K) if a not in use)]
    print('multiplicity solutions',len(sols),flush=True)
    for mult in sols:
        r=check(mult,TY,PT,TT,use,tl); print(mult,r,flush=True)
        if r!='INFEASIBLE': return r
    return 'INFEASIBLE'
def check(m,TY,PT,TT,use,tl):
    idx=[a for a in use if m[a]>0]
    M=cp_model.CpModel()
    x={}
    for a in idx:
        for b in idx:
            for P in PT[a,b]: x[a,b,P]=M.NewIntVar(0,n*n,"")
            M.Add(sum(x[a,b,P] for P in PT[a,b])==m[a]*(m[b]-(a==b)))
        for li,l in enumerate(range(2,d+1)):
            M.Add(sum(x[a,b,P]*P[li] for b in idx for P in PT[a,b])==m[a]*(l-1)*TY[a][li])
    for (a,b,P),v in list(x.items()):
        if a<b: M.Add(v==x[b,a,P])
    w={}
    for key,qs in TT.items():
        a,b,c=key[:3]
        if a in idx and b in idx and c in idx:
            for Q in qs: w[key,Q]=M.NewIntVar(0,n**3,"")
    # permutation consistency
    for (key,Q),v in w.items():
        a,b,c,Pab,Pac,Pbc=key
        k2=(b,a,c,Pab,Pbc,Pac); k3=(a,c,b,Pac,Pab,Pbc)
        for kk in (k2,k3):
            if (kk,Q) in w: M.Add(v==w[kk,Q])
            else: M.Add(v==0)
    # edge sums
    for a in idx:
        for b in idx:
            for P in PT[a,b]:
                for c in idx:
                    M.Add(sum(v for (key,Q),v in w.items() if key[0]==a and key[1]==b and key[3]==P and key[2]==c)==x[a,b,P]*(m[c]-(c==a)-(c==b)))
                for li,l in enumerate(range(3,d+1)):
                    M.Add(sum(v*Q[li] for (key,Q),v in w.items() if key[0]==a and key[1]==b and key[3]==P)==x[a,b,P]*(l-2)*P[l-2])
                # local configuration for one ordered pair of this class, if any
                on=M.NewBoolVar(""); M.Add(x[a,b,P]>=1).OnlyEnforceIf(on); M.Add(x[a,b,P]==0).OnlyEnforceIf(on.Not())
                y={}
                for (key,Q) in w:
                    if key[0]==a and key[1]==b and key[3]==P: y[key,Q]=M.NewIntVar(0,n,"")
                for c in idx:
                    M.Add(sum(v for (key,Q),v in y.items() if key[2]==c)==m[c]-(c==a)-(c==b)).OnlyEnforceIf(on)
                for li,l in enumerate(range(3,d+1)):
                    M.Add(sum(v*Q[li] for (key,Q),v in y.items())==(l-2)*P[l-2]).OnlyEnforceIf(on)
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=int(os.environ.get('W','2'))
    return S.StatusName(S.Solve(M))
if __name__=='__main__':
    t=time.time(); print('RESULT',main(float(sys.argv[1])),round(time.time()-t),flush=True)
