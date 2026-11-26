import sys
from lib import *
def write(fn,m,comps):
    with open(fn,'w') as f:
        f.write(f"{m} {len(comps)}\n")
        for b,A in comps:
            f.write(f"{b} {len(A)}\n"); 
            for a in A: f.write(" ".join(map(str,a))+"\n")
A4=targets(ggwz4(),4); F=(1,[(1,)]); F2=(1,[(1,),(2,)])
write('ggwz.cfg',11,[(4,A4)]*3+[F,F])
write('r9a.cfg',11,[(4,A4)]+[F]*4)
write('r9b.cfg',10,[(4,A4)]+[F2,F,F])   # rank 8 actually (4+3+1)
write('r9c.cfg',9,[(4,A4)]*2+[F])  # rank 10
