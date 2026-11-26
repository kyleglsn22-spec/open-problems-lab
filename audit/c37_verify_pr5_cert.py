# Auditor re-check of PR 5 certificate file. Usage: python3 -I c37_verify_pr5_cert.py <cert.json>
# Auditor re-verification of PR 5's certificate file using the Auditor's own forms (not PR 5 code).
import json,sys
from fractions import Fraction as F
from math import comb, floor, ceil
c=json.load(open(sys.argv[1]))
nA,nB=c['parts']; d=c['degree']; T=tuple(c['target_pattern'])
V=[(a,b) for b in range(nB+1) for a in range(nA+1) if a+b<=d]
fixed={(0,0):F(0),(1,0):F(nA),(0,1):F(nB)}
def N(i,j):  # N(i,j) = number of ones of q at weight class (i,j), affine in the free C's
  coef={v:F(0) for v in V}; const=F(0)
  for (a,b) in V:
    w=F(comb(nA,i)*comb(nB,j)*comb(i,a)*comb(j,b),comb(nA,a)*comb(nB,b))
    if (a,b) in fixed: const+=w*fixed[(a,b)]
    else: coef[(a,b)]+=w
  return coef,const
def combine(items):
  tot={v:F(0) for v in V}; k=F(0)
  for it in items:
    i,j=it['class']; m=F(it['mult']); assert m>0
    co,cst=N(i,j); cap=comb(nA,i)*comb(nB,j)
    if it['side']=='N>=0': s=1; kk=cst            # form = N >= 0
    elif it['side']=='N<=cap': s=-1; kk=cap-cst   # form = cap - N >= 0
    else: raise ValueError(it['side'])
    for v in V: tot[v]+=m*s*co[v]
    k+=m*kk
  return tot,k   # sum = tot.C + k >= 0
lo_t,lo_k=combine(c['combinations']['lower'])
hi_t,hi_k=combine(c['combinations']['upper'])
for name,(t,k) in [('lower',(lo_t,lo_k)),('upper',(hi_t,hi_k))]:
  nz={v:x for v,x in t.items() if x}
  assert list(nz)==[T], (name,nz)
  print(name, "form:", nz[T],"* C",T,"+",k,">= 0  =>  C",T, ">=" if nz[T]>0 else "<=", -k/nz[T])
lo=-lo_k/lo_t[T]; hi=-hi_k/hi_t[T]
print("interval",lo,hi,"contains integer?", ceil(lo)<=floor(hi))
assert ceil(lo)>floor(hi)
print("PR 5 certificate VERIFIED by auditor's independent forms")
