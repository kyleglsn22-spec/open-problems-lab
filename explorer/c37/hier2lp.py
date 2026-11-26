import sys,time
from ortools.sat.python import cp_model
from hier import build
def run(n,d,k,C,tl,workers=4,lin=2):
    M,T=build(n,d,k)
    for l in range(2,d+1): M.Add(T[(),l]==C[l])
    B=4096
    keys=[]
    for j in range(n):
        ks=0
        for l in range(2,d+1): ks=ks*B+(T[(j,),l]+B//2)
        keys.append(ks)
        for l in range(2,d+1): M.Add(T[(j,),l]>=-B//2+1); M.Add(T[(j,),l]<=B//2-1)
    for j in range(n-1): M.Add(keys[j]<=keys[j+1])
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=workers
    S.parameters.linearization_level=lin
    return S.StatusName(S.Solve(M))
if __name__=='__main__':
    C=[int(x) for x in sys.argv[1].split(',')]; t=time.time()
    print(C,run(14,5,2,C,float(sys.argv[2]),lin=int(sys.argv[3])),round(time.time()-t),flush=True)
