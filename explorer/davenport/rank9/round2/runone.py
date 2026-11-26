import sys, time
from satmodel import *; from lib import *
A4=targets(ggwz4(),4); F=(1,[(1,)]); F2=(1,[(1,),(2,)])
cfgs={'c11':([(4,A4)]+[F]*4,11),'r8':([(4,A4)]+[F]*3,10),'r7':([(4,A4)]+[F]*2,9),'r10':([(4,A4)]*2+[F],9),
      'r8b':([(4,A4)]+[F2,F,F],11),'r9d':([(4,A4)]+[F2,F2],10)}
name=sys.argv[1]; comps,m=cfgs[name]
ok,res,dt,nv,nc=run(comps,m); print(name,"SAT" if ok else "UNSAT",round(dt,1),nv,nc,flush=True)
if res:
    for r in res: print(r)
