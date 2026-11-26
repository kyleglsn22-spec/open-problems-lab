# T^2 colourings F(u,v) = S_{j(v)}(u), v split into m2 equal strips; continuum in u.
import ctypes,os,numpy as np
lib=ctypes.CDLL(os.path.abspath('librc4.so')); lib.density4.restype=ctypes.c_double
C=[(0,0,0,0),(0,0,0,1),(0,0,1,1),(0,0,1,2),(0,1,1,1),(0,1,1,2),(0,1,2,2),(0,1,2,3)]
Wt=[2,1,2,1,1,2,1,2]
def dens2(S):
    m2=len(S); ns=[len(c) for _,c in S]; a=[];off=[];col=[]
    for bp,c in S: off.append(len(a)); a+=list(bp); col+=list(c)
    I=ctypes.c_int*m2; nsA=I(*ns); offA=I(*off); aA=(ctypes.c_double*len(a))(*a); cA=(ctypes.c_int*len(col))(*col)
    cache={}; tot=0.0
    for c,w in zip(C,Wt):
        for j0 in range(m2):
            for d in range(m2):
                key=tuple((j0+i*d+c[i])%m2 for i in range(4))
                if key not in cache: cache[key]=lib.density4(nsA,aA,offA,cA,(ctypes.c_int*4)(*key))
                tot+=w*cache[key]
    return tot/(12*m2*m2)
