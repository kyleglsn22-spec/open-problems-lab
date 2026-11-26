from satmodel import *; from lib import *
A4=targets(ggwz4(),4)
for comps,m,name in [([(4,A4)]*2,8,"2xGGWZ4 m=8"),([(4,A4)]*2+[(1,[(1,)])],9,"2xGGWZ4+F m=9"),([(4,A4)]+[(1,[(1,)])]*2,9,"GGWZ4+2F m=9 (rank 7)"),([(4,A4)]+[(1,[(1,)])]*3,10,"GGWZ4+3F m=10 (rank 8)")]:
    ok,res,dt,nv,nc=run(comps,m); print(name,ok,round(dt,1),nv,nc,flush=True)
    if res:
        for r in res: print(r)
