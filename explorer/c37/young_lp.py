import itertools
from math import comb, prod
import numpy as np
from scipy.optimize import linprog
def build(parts,d):
    m=len(parts)
    ls=[l for l in itertools.product(*[range(min(a,d)+1) for a in parts]) if sum(l)<=d]
    var=[l for l in ls if sum(l)>=2]
    rows=[]
    for w in itertools.product(*[range(a+1) for a in parts]):
        const=0; coef=[0]*len(var)
        for l in ls:
            if all(l[t]<=w[t] for t in range(m)):
                c=prod(comb(parts[t]-l[t],w[t]-l[t]) for t in range(m))
                s=sum(l)
                if s==1: const+=parts[l.index(1)]*c
                elif s>=2: coef[var.index(l)]+=c
        cap=prod(comb(parts[t],w[t]) for t in range(m))
        rows.append((w,const,coef,cap))
    return var,rows
