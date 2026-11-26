# Auditor (in-house), 2026-11-25: own max-plus transfer matrix for the 5/9 family (independent of PR 13).
# Auditor: own max-plus transfer computation for the 5/9 family, from the definitions.
from itertools import combinations
O=[0,49,75,83,98,101,117,119,121,159,269]; a,b,p,q=0,269,101,119
S=set(O)
def sidon(J):
    s=[x+y for i,x in enumerate(J) for y in J[i:]]; return len(s)==len(set(s))
NEG=-10**9
M=[[NEG]*4 for _ in range(4)]; first=[NEG]*4
st=lambda J,u,v:2*(u in J)+(v in J)
for r in range(len(O)+1):
  for J in combinations(O,r):
    if not sidon(list(J)): continue
    Js=set(J); si,so=st(Js,a,b),st(Js,p,q)
    M[si][so]=max(M[si][so],len(Js-{a,b})); first[so]=max(first[so],len(Js))
print("first copy vector",first); print("M",M)
v=first
for K in range(1,13):
  v=[max(v[i]+M[i][j] for i in range(4)) for j in range(4)]
  print(K,max(v),7+5*K, [x-5*K for x in v])
