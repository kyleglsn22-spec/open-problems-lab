# multistart search over antipodal circle colourings with many arcs, then free polish
import sys,json,time,numpy as np
from scipy.optimize import minimize
from rc import density
def full_from_half(h):  # h: sorted breakpoints in (0,1/2), odd number of arcs on half => len(h) even
    hb=np.concatenate([[0],np.sort(np.clip(h,0,0.5)),[0.5]])
    nh=len(hb)-1
    bp=np.concatenate([hb,hb[1:]+0.5]); col=[g%2 for g in range(2*nh)]
    return list(bp),col
def fh(h):
    bp,col=full_from_half(h); return density(0,[(bp,col)])
def fg(fun,x,h=1e-7):
    f0=fun(x); g=np.empty_like(x)
    for i in range(len(x)):
        e=np.zeros_like(x);e[i]=h; g[i]=(fun(x+e)-fun(x-e))/(2*h)
    return f0,g
def loc(fun,x,ub):
    r=minimize(lambda y:fg(fun,y),x,jac=True,method='L-BFGS-B',bounds=[(0,ub)]*len(x),options={'maxiter':2000,'ftol':1e-15,'gtol':1e-11})
    return r.x,r.fun
