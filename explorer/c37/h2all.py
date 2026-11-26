import sys, time, os
from hier2 import run
from lvl1 import profiles
n,d,k,tl=map(int,sys.argv[1:5]); shard=int(os.environ.get('SHARD',0)); nsh=int(os.environ.get('NSH',1))
for i,C in enumerate(profiles(n,d)):
    if i%nsh!=shard: continue
    t=time.time(); r=run(n,d,k,C,tl,workers=int(os.environ.get('W','1')))
    print(C,r,round(time.time()-t,1),flush=True)
