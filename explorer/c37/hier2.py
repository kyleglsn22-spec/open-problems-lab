import sys, time, itertools
from ortools.sat.python import cp_model
from hier import build
from lvl1 import profiles
def run(n,d,k,C,tl=60,workers=4,lex=True):
    M,T=build(n,d,k)
    for l in range(2,d+1): M.Add(T[(),l]==C[l])
    if lex and k>=1:
        # lexicographic order of singleton vectors (T_2..T_d) : encode as weighted sum (values bounded)
        B=4096
        keys=[]
        for j in range(n):
            ks=0
            for l in range(2,d+1):
                ks=ks*B+(T[(j,),l]+B//2)
            keys.append(ks)
        for j in range(n-1):
            M.Add(keys[j]<=keys[j+1])
        for j in range(n):
            for l in range(2,d+1):
                M.Add(T[(j,),l]>=-B//2+1); M.Add(T[(j,),l]<=B//2-1)
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=workers
    return S.StatusName(S.Solve(M))
if __name__=='__main__':
    n,d,k,tl=map(int,sys.argv[1:5])
    P=profiles(n,d)
    res={}
    for C in P:
        t=time.time(); r=run(n,d,k,C,tl); res[r]=res.get(r,0)+1
        print(C,r,round(time.time()-t,1),flush=True)
    print(res)
