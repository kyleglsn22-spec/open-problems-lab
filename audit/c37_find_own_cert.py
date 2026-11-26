# Auditor helper (needs scipy): finds the multipliers stored in c37_own_cert.py.
# Auditor's own exact Farkas certificates for the 8+2 LP: C[1,2] <= 14/3 and C[1,2] >= 14/3.
# Constraint forms (all must hold for any Boolean q of degree<=4 with q(0)=0, q(e_i)=1):
#   g_p(C) = avg_p(C) >= 0,  h_p(C) = 1 - avg_p(C) >= 0,  and C00=0, C10=8, C01=2.
from fractions import Fraction as F
from math import comb
import numpy as np
from scipy.optimize import linprog
nA,nB,d=8,2,4
V=[(a,b) for b in range(nB+1) for a in range(nA+1) if a+b<=d]
n=len(V); T=V.index((1,2))
pts=[(i,j) for i in range(nA+1) for j in range(nB+1)]
def row(i,j): return [F(comb(i,a)*comb(j,b),comb(nA,a)*comb(nB,b)) for a,b in V]
# affine forms as (coef vector, const): value = coef.C + const >= 0
ineq=[]
for p in pts:
  r=row(*p); ineq.append(('avg>=0',p,r,F(0))); ineq.append(('avg<=1',p,[-t for t in r],F(1)))
eqs=[((0,0),0),((1,0),nA),((0,1),nB)]
def solve(sign):
  # want sum y_k*form_k + sum z_e*(C_e - val_e) == sign*(C_T) + K  with y>=0, then C_T bound = ...
  # i.e. sum y_k coef_k + z = sign*e_T  ; minimise number via LP on floats, then exact rationalise
  m=len(ineq)
  A=np.zeros((n,m+3)); 
  for k,(_,_,c,_) in enumerate(ineq): A[:,k]=[float(t) for t in c]
  for e,(v,_) in enumerate(eqs): A[V.index(v),m+e]=1
  b=np.zeros(n); b[T]=sign
  k0s=[float(t[3]) for t in ineq]
  res=linprog(np.r_[k0s,[-float(v) for _,v in eqs]],A_eq=A,b_eq=b,bounds=[(0,None)]*m+[(None,None)]*3,method='highs')
  return res.x
for sign in (+1,-1):
  y=solve(sign)
  yr=[F(t).limit_denominator(10**6) for t in y]
  m=len(ineq)
  # exact check: sum y coef + z e = sign*e_T
  tot=[F(0)]*n; const=F(0)
  for k,(_,_,c,k0) in enumerate(ineq):
    assert yr[k]>=0
    for t in range(n): tot[t]+=yr[k]*c[t]
    const+=yr[k]*k0
  for e,(v,val) in enumerate(eqs):
    tot[V.index(v)]+=yr[m+e]; const-=yr[m+e]*val
  assert all(tot[t]==(sign if t==T else 0) for t in range(n)), tot
  # so 0 <= sum = sign*C_T + const  =>  sign*C_T >= -const
  used=[(ineq[k][0],ineq[k][1],str(yr[k])) for k in range(m) if yr[k]]
  print(("C12 >= " if sign>0 else "C12 <= "), (-const if sign>0 else const), "| multipliers used:",len(used))
  for u in used: print("   ",u)
  print("    equality multipliers:",[str(t) for t in yr[m:]])
