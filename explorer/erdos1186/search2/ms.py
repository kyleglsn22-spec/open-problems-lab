from mslib import *
import sys,json,time,numpy as np
seed=int(sys.argv[1]); rng=np.random.default_rng(seed); out=open(f'ms_{seed}.jsonl','a')
best=1
t0=time.time()
while time.time()-t0<float(sys.argv[2]):
    nh=int(rng.choice(range(9,33,2)))   # arcs on half circle (odd); total arcs 2nh = 18..62
    h=np.sort(rng.dirichlet(np.ones(nh)*rng.choice([1,3,10])).cumsum()[:-1]*0.5)
    x,v=loc(fh,h,0.5)
    # hops
    for k in range(6):
        y=np.sort(np.clip(x+rng.normal(0,0.004,len(x)),0,0.5)); y,w=loc(fh,y,0.5)
        if w<v-1e-12: x,v=y,w
    bp,col=full_from_half(x)
    nz=int(np.sum(np.diff(bp)>1e-6))
    rec={'seed':seed,'nh':nh,'v':v,'arcs_eff':nz,'half':list(x)}
    out.write(json.dumps(rec)+'\n'); out.flush()
    if v<best: best=v; print('best',v,nh,nz,flush=True)
