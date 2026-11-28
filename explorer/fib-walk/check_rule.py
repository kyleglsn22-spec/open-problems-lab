"""Check the exact local rule of valleys.md against the CGS representation for all 2 <= n < LIM.
Rule: for each t >= 2 there is exactly one integer solution (a, b) of a f_t + b f_{t-1} = n with
0 <= Q = phi*b - a < phi^t; n is a member of family t iff 1 <= a <= b <= f_t. Equivalently, with
delta = {phi n} and Q = phi^t delta (t even) or phi^t (1 - delta) (t odd):
  n/(phi f_{t+1}) <= Q,  Q <= (phi n - phi^t)/f_{t-1},  Q <= phi^t - n/f_t."""
import sys
from decimal import Decimal, getcontext
getcontext().prec=80
phi=(1+Decimal(5).sqrt())/2
fib=[0,1]
while len(fib)<90: fib.append(fib[-1]+fib[-2])
def fams_lattice(n):
    out=[]
    for t in range(2,80):
        ft,f1=fib[t],fib[t-1]
        if ft+f1>n: break
        for b in range(1,ft+1) if ft<=2 else [(n*pow(f1,-1,ft))%ft, (n*pow(f1,-1,ft))%ft+ft]:
            if 1<=b<=ft and (n-b*f1)%ft==0 and 1<=(n-b*f1)//ft<=b: out.append(t)
    return out
def fams_delta(n):
    d=(n*phi)%1; out=[]
    for t in range(2,80):
        if fib[t]+fib[t-1]>n: break
        Q=phi**t*(d if t%2==0 else 1-d); e=Decimal(10)**-50  # equality cases (a = 1, a = b, b = f_t) need a tolerance
        if Decimal(n)/(phi*fib[t+1])-e<=Q<=(phi*n-phi**t)/fib[t-1]+e and Q<=phi**t-Decimal(n)/fib[t]+e: out.append(t)
    return out
LIM=int(sys.argv[1]) if len(sys.argv)>1 else 20000
bad=[n for n in range(2,LIM) if len(fams_lattice(n))!=1 or fams_lattice(n)!=fams_delta(n)]
print('mismatches below',LIM,':',bad[:20],len(bad))
