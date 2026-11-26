# Auditor (in-house), 2026-11-25. Claim 757-2 witness (Ma–Tang 14-point set). Independent of check_n14.py.
# Independent Auditor check, Erdős #757 witness. Written from the definitions only.
# Sidon here: all pairwise differences x-y (x>y) are distinct  (equivalent to the sum form).
from fractions import Fraction
A=[0,136,200,243,246,249,272,286,298,323,400,528,596,1056]
n=len(A); assert len(set(A))==n==14
# (4,5): at least 5 distinct positive differences among the 6
cnt=0
for m in range(1<<n):
    if bin(m).count('1')!=4: continue
    B=[A[i] for i in range(n) if m>>i&1]
    pos={x-y for x in B for y in B if x>y}
    assert len(pos)>=5,B; cnt+=1
    assert len({x-y for x in B for y in B})==2*len(pos)+1
print("4-subsets ok:",cnt)
def sidon(S):
    d=[x-y for x in S for y in S if x>y]; return len(d)==len(set(d))
best=0;ex=None
for m in range(1<<n):
    S=[A[i] for i in range(n) if m>>i&1]
    if len(S)>best and sidon(S): best=len(S);ex=S
print("max Sidon:",best,ex)
assert best==8
# also the sum-form definition on the 8-subsets, to cross-check equivalence
def sidon_sum(S):
    for a in S:
     for b in S:
      for c in S:
       for d in S:
        if a+b==c+d and not ((a==c and b==d) or (a==d and b==c)): return False
    return True
for m in range(1<<n):
    S=[A[i] for i in range(n) if m>>i&1]
    assert sidon(S)==sidon_sum(S)
print("difference-form == sum-form on all 4096 subsets")
# 3-APs in A
aps=[(a,b,c) for a in A for b in A for c in A if a<c<b and a+b==2*c]
print(len(aps),"3-APs:",aps)
print("4/7:", Fraction(8,14)==Fraction(4,7))
