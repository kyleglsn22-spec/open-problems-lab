# Generate a self-describing exact certificate: LP over Young-subgroup (a,b) orbit sums forces var into an open integer gap.
import json, itertools, sys
from fractions import Fraction as F
from math import comb, prod
import numpy as np
from scipy.optimize import linprog
from young_lp import build
def gen(parts,d,target):
    var,rows=build(parts,d)
    A=[];b=[];lab=[]
    for w,c0,co,cap in rows:
        A.append(co); b.append(cap-c0); lab.append((list(w),'N<=cap'))
        A.append([-x for x in co]); b.append(c0); lab.append((list(w),'N>=0'))
    vi=var.index(target); n=len(var); out={}
    for sgn,name in [(1,'lower'),(-1,'upper')]:
        obj=[0]*n; obj[vi]=sgn
        r=linprog(obj,A_ub=A,b_ub=b,bounds=[(None,None)]*n,method='highs')
        y=[F(v).limit_denominator(10**6) if v>1e-12 else F(0) for v in (-np.array(r.ineqlin.marginals))]
        out[name]=[{'class':lab[i][0],'side':lab[i][1],'mult':str(y[i])} for i in range(len(y)) if y[i]]
    return {'parts':list(parts),'degree':d,'n':sum(parts),'target_pattern':list(target),
            'claim':'every LP-feasible point has target orbit sum strictly between consecutive integers',
            'combinations':out}
if __name__=='__main__':
    c=gen((8,2),4,(1,2))
    json.dump(c,open('results/cert_n10_d4_split8_2.json','w'),indent=1)
    print(len(c['combinations']['lower']),len(c['combinations']['upper']))
