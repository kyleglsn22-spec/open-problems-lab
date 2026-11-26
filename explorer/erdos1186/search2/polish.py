import sys,json,glob,numpy as np
from mslib import full_from_half, fh, loc
from rc import density
R=[json.loads(l) for f in glob.glob('ms_*.jsonl') for l in open(f)]
R.sort(key=lambda r:r['v']); r=R[int(sys.argv[1])]
x=np.array(r['half']); v=fh(x); print('start',v,flush=True)
# drop near-zero arcs (merge): remove pairs of breakpoints closer than 1e-6
rng=np.random.default_rng(int(sys.argv[1])+100)
for k in range(int(sys.argv[2])):
    sc=rng.choice([0.0005,0.002,0.006])
    y=np.sort(np.clip(x+rng.normal(0,sc,len(x)),0,0.5)); y,w=loc(fh,y,0.5)
    if w<v-1e-13: x,v=y,w; print('hop',k,v,flush=True)
bp,col=full_from_half(x); arcs=np.diff(bp)
print('final',v,'arcs',int((arcs>1e-7).sum()),'min arc',arcs[arcs>1e-7].min())
json.dump({'v':v,'half':list(x)},open(f'pol_{sys.argv[1]}.json','w'))
