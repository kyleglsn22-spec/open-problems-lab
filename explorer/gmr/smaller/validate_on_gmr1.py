# Sanity check for the pattern finder: rebuild the GMR-1 group (order 2^17) as a permutation
# group on 2^11 cosets, compute the double-coset label matrix for H = V1, J = V2, and check
# that sat.solve_shape re-finds the three 3x3 blocks and that the exact ratio is 1372/1369-type.
import numpy as np, itertools, math, time
from ev import build, score
from sat import solve_shape, exact
blocks=[[2,3,4,5,7,8,9,10,12],[6,11,15,17,19,21,23,24,26],[1,13,14,16,18,28,29,30,31]]
def find(Ls):
    for a,b,c,d in itertools.product(range(1,32),repeat=4):
        L=[a,b,a^b,c,d,c^d,a^c,b^d,a^b^c^d]
        if sorted(L)==sorted(Ls): return (a,b,c,d)
Ms=[find(L) for L in blocks]
om=[[0]*6 for _ in range(6)]
for i,(a,b,c,d) in enumerate(Ms):
    om[2*i][2*i]=a; om[2*i][2*i+1]=b; om[2*i+1][2*i]=c; om[2*i+1][2*i+1]=d
def omega(y,z):
    v=0
    for i in range(6):
        if y>>i&1:
            for j in range(6):
                if z>>j&1: v^=om[i][j]
    return v
OM=[[omega(y,z) for z in range(64)] for y in range(64)]
# right cosets of V1: point (b,w); right action of (c2,b2,w2): (b,w) -> (b^b2, w^w2^OM[b][c2])
def perm(c2,b2,w2):
    p=np.zeros(2048,np.int16)
    for b in range(64):
        for w in range(32):
            p[b|w<<6]=(b^b2)|((w^w2^OM[b][c2])<<6)
    return p
Hel=np.array([perm(c,0,0) for c in range(64)]); Jel=np.array([perm(0,b,0) for b in range(64)])
d,w,lc,rc=build(Hel,Jel)
t=time.time(); st,rows,cols=solve_shape(d,3,3,3,tlimit=60,workers=4)
ex=exact(d,w,lc,rc,rows,cols)
print('shape (3,3,3):',st,'%.2fs'%(time.time()-t),'ratio',math.exp(ex[0]),'(S,N1,N2,N3,N4)=',ex[2])
for sh in [(5,2,2),(13,1,1)]:
    print('shape',sh,solve_shape(d,*sh,tlimit=60,workers=4)[0])
