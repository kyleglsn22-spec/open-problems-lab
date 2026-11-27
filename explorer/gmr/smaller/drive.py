import sys, numpy as np, math, time, json
from ev import parse, closure, build
from sat import solve_shape, exact
base=[(13,1,1),(8,1,2),(7,1,3),(6,1,4),(6,1,5),(5,1,6),(5,1,7),(5,2,2),(4,2,3),(3,2,5),(3,3,3),(2,4,6),(2,5,5)]
shapes=[]
for (m,k,l) in base:
    shapes.append((m,k,l))
    if k!=l: shapes.append((m,l,k))
shapes.sort(key=lambda s:(s[0]*s[1]*s[2]))
def run(fn,minsz=10,tl=4):
    G,pairs=parse(fn); name,order,gg=G; n=len(gg[0])
    global shapes
    if name in ('M12','A6xA6','S4wrS3','S3wrD5','S5xS6','PSL253'):
        shapes=[(2,4,6),(2,6,4),(2,5,5),(2,4,7),(2,7,4),(2,5,6),(2,6,5),(3,3,3)]
    log=open('sat_'+name+'.log','w')
    t0=time.time(); hits=0; tested=0
    for pi,(h,j,hg,jg) in enumerate(pairs):
        if h<minsz or j<minsz: continue
        Hel=closure(hg,n); Jel=closure(jg,n)
        e=np.arange(n)
        def idfirst(E):
            k=[i for i in range(len(E)) if (E[i]==e).all()][0]
            E=E.copy(); E[[0,k]]=E[[k,0]]; return E
        Hel=idfirst(Hel); Jel=idfirst(Jel)
        d,w,lc,rc=build(Hel,Jel)
        # also try swapped orientation implicitly via shapes (k,l) and (l,k)
        infeas=[]; tested+=1
        for (m,k,l) in shapes:
            if m*k>len(Jel)-1 or m*l>len(Hel)-1: continue
            if any(m>=a and k>=b and l>=c for (a,b,c) in infeas): continue
            st,rows,cols=solve_shape(d,m,k,l,tlimit=tl)
            if st=='SAT':
                ex=exact(d,w,lc,rc,rows,cols)
                hits+=1
                rec=dict(pair=pi,H=h,J=j,shape=(m,k,l),ratio=math.exp(ex[0]),e=ex[1],vals=[int(x) for x in ex[2]],
                         rows=np.nonzero(rows)[0].tolist(),cols=np.nonzero(cols)[0].tolist(),Hg=hg,Jg=jg)
                log.write(json.dumps(rec)+'\n'); log.flush()
            elif st=='INFEASIBLE':
                infeas.append((m,k,l))
            else:
                log.write(json.dumps(dict(pair=pi,shape=(m,k,l),status=st))+'\n'); log.flush()
    log.write('DONE %s order %d tested %d hits %d time %.0f\n'%(name,order,tested,hits,time.time()-t0)); log.close()
if __name__=='__main__': run(sys.argv[1])
