import sys, itertools
from fractions import Fraction as F
from itertools import combinations
from ortools.sat.python import cp_model

def aps(A):
    st=set(A); return [(a,(a+c)/2,c) for a,c in combinations(A,2) if (a+c)/2 in st]
def is45(A):
    A=sorted(A); seen={}
    for i in range(len(A)):
        for j in range(i+1,len(A)):
            s=A[i]+A[j]
            if s in seen:
                for (k,l) in seen[s]:
                    if len({i,j,k,l})==4: return False
                seen[s].append((i,j))
            else: seen[s]=[(i,j)]
    E=aps(A); cnt={}
    for e in E:
        for pr in combinations(e,2):
            if pr in cnt: return False
            cnt[pr]=1
    return True
def alpha(A, E=None):
    if E is None: E=aps(A)
    m=cp_model.CpModel(); idx={a:i for i,a in enumerate(A)}
    x=[m.NewBoolVar('') for _ in A]
    for e in E: m.AddBoolOr([x[idx[v]].Not() for v in e])
    m.Maximize(sum(x)); s=cp_model.CpSolver(); s.parameters.num_workers=1
    s.Solve(m); return int(s.ObjectiveValue())
def chain(O, a,b,p,q,K):
    phi=lambda x: p+(q-p)*(x-a)/(b-a)
    S=set(O); cur=list(O)
    for k in range(K):
        cur=[phi(x) for x in cur]; S|=set(cur)
    return sorted(S)
if __name__=="__main__":
    O=[F(int(t)) for t in open(sys.argv[1]).read().split()]
    n=len(O); best=[]
    for (a,b) in itertools.permutations(O,2):
      for (p,q) in itertools.permutations(O,2):
        if (a,b)==(p,q) or (b,a)==(p,q): continue
        if a>b and p>q: continue  # same map as swapped
        S1=chain(O,a,b,p,q,1)
        if len(S1)!=2*n-2 or not is45(S1): continue
        al1=alpha(S1)
        best.append((al1,a,b,p,q))
    best.sort()
    print(n, "alpha(O)=",alpha(O),"candidates",len(best))
    for al1,a,b,p,q in best[:15]:
        S=[chain(O,a,b,p,q,K) for K in range(1,5)]
        if not all(len(s)==n+K*(n-2) and is45(s) for K,s in zip(range(1,5),S)): 
            print("bad at higher K",a,b,p,q); continue
        als=[alpha(s) for s in S]
        print(f"a={a} b={b} p={p} q={q} alphas={als} incr/(n-2)={(als[3]-als[1])/2}/{n-2}")
