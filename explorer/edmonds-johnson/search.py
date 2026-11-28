from fractions import Fraction as F
import itertools, numpy as np, math, sys, pickle
from scipy.optimize import linprog
def run(A, nx, name):
    m=len(A); n=len(A[0])
    found=[]
    thirds=[F(k,3) for k in range(-3,7)]
    xopts=[F(k,3) for k in range(-2,6) if k%3!=0]
    for zx in itertools.product(xopts,repeat=nx):
      for zy in itertools.product([F(k,3) for k in range(-1,4)],repeat=n-nx):
        z=list(zx)+list(zy)
        b=[];c=[];tight=[]
        ok=True
        for i,r in enumerate(A):
            s=sum(F(a)*t for a,t in zip(r,z))
            f=s-math.floor(s)
            if f==F(1,3): b.append(s-F(1,3)); c.append(b[-1]+2); tight.append(tuple(x%2 for x in r))
            elif f==F(2,3): c.append(s+F(1,3)); b.append(c[-1]-2); tight.append(tuple(x%2 for x in r))
            else: ok=False;break
        if not ok: continue
        l=[];u=[]
        for j in range(n):
            e=tuple(1 if k==j else 0 for k in range(n))
            f=z[j]-math.floor(z[j])
            if j<nx:
                if f==F(1,3): l.append(z[j]-F(1,3)); u.append(l[-1]+2)
                else: u.append(z[j]+F(1,3)); l.append(u[-1]-2)
                tight.append(e)
            else:
                l.append(math.floor(z[j])-1); u.append(math.ceil(z[j])+1)
                if z[j]==math.floor(z[j]): l[-1]=z[j]-1;u[-1]=z[j]+1
        if len(set(tight))<len(tight) or any(not any(t) for t in tight): continue
        # integer points
        rng=[range(int(l[j]),int(u[j])+1) for j in range(n)]
        pts=[x for x in itertools.product(*rng) if all(b[i]<=sum(a*t for a,t in zip(A[i],x))<=c[i] for i in range(m))]
        if not pts: continue
        # is z in conv(pts)? LP feasibility
        P=np.array(pts,dtype=float).T
        res=linprog(np.zeros(len(pts)),A_eq=np.vstack([P,np.ones(len(pts))]),b_eq=np.array([float(t) for t in z]+[1.0]),bounds=[(0,None)]*len(pts))
        if res.status==2:
            found.append((z,[int(t) for t in b],[int(t) for t in c],[int(t) for t in l],[int(t) for t in u]))
            print(name,[str(t) for t in z],[int(t) for t in b],[int(t) for t in c],[int(t) for t in l],[int(t) for t in u]); sys.stdout.flush()
            if len(found)>=3: return found
    return found
A6p=[[0,0,1,1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
A7=[[0,0,1,-1,2,-2,2],[0,1,1,0,2,0,0],[0,1,0,1,0,2,0],[1,0,1,0,2,0,0],[1,0,0,1,0,2,0]]
A6=[[0,0,1,-1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
which=sys.argv[1]
r=run({'A6':A6,'A6p':A6p,'A7':A7}[which],4,which)
pickle.dump(r,open(f'found_{which}.pkl','wb'))
