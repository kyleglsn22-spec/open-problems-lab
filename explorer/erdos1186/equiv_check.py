"""Exact check: the residue colouring c(x)=G_r[x mod b][floor(Kx/p)] equals, after the dilation
x -> x * b^{-1} mod p (a bijection of Z_p that maps 4-APs to 4-APs), the plain block colouring
of the circle with the bK-block word W[t*K+j] = G_r[s][j], where t = (-s * r^{-1}) mod b."""
import json,sys,time,os
import os
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from family import exact_density
import numpy as np
cert=json.load(open(os.path.join(HERE,'cert_44_3.json')))
b,K=cert['b'],cert['K']
def word_for(r):
    T=cert['tables'][str(r)]; rinv=pow(r,-1,b); W=['']*b
    for s in range(b): W[(-s*rinv)%b]=T[K*s:K*s+K]
    return ''.join(W)
# 1) direct brute-force identity on a real prime: colours agree after dilation
for p in [100003, 100019]:
    r=p%b; T=cert['tables'][str(r)]; W=word_for(r); lam=pow(b,-1,p)
    ok=all(int(T[K*(x%b)+(K*x)//p])==int(W[(b*K*((lam*x)%p))//p]) for x in range(p))
    print('prime',p,'r',r,'pointwise identical after dilation:',ok)
# 2) exact limit of the plain word equals the certificate value
t=time.time(); W=word_for(1)
v=exact_density(np.array([[int(c) for c in W]]),0); print('exact plain-word value',v,'claimed',cert['claimed_max'],time.time()-t)
