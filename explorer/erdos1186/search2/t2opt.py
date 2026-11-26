import sys,json,numpy as np
from scipy.optimize import minimize
from t2c import dens2
m2=int(sys.argv[1]); seed=int(sys.argv[2]); amp=float(sys.argv[3])
J=json.load(open('marquardt_continuum.json')); n=26; inner=np.array(J['breakpoints_inner']); col=[int(v) for v in J['values']]
def unpack(x):
    return [(list(np.concatenate([[0],np.sort(np.clip(x[j*(n-1):(j+1)*(n-1)],0,1)),[1]])),col) for j in range(m2)]
f=lambda x: dens2(unpack(x))
def fg(x,h=1e-7):
    f0=f(x); g=np.empty_like(x)
    for i in range(len(x)):
        e=np.zeros_like(x); e[i]=h; g[i]=(f(x+e)-f(x-e))/(2*h)
    return f0,g
print('T1 value',f(np.tile(inner,m2)),flush=True)
rng=np.random.default_rng(seed)
x=np.tile(inner,m2)+rng.normal(0,amp,(n-1)*m2)
print('perturbed',f(x),flush=True)
r=minimize(fg,x,jac=True,method='L-BFGS-B',bounds=[(0,1)]*len(x),options={'maxiter':3000,'ftol':1e-15,'gtol':1e-11})
print('opt',r.fun,flush=True)
X=r.x.reshape(m2,n-1); print('max strip spread of breakpoints',np.max(np.ptp(np.sort(X,axis=1),axis=0)))
np.save(f't2opt_{m2}_{seed}.npy',r.x)
