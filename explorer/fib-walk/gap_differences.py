import numpy as np, sys
LIM=int(sys.argv[1]); LMAX=int(sys.argv[2])
fib=[0,1]
while fib[-1]<10*LIM: fib.append(fib[-1]+fib[-2])
kind=np.full(LIM+1,-1,dtype=np.int8)
for t in range(2,len(fib)-1):
    ft,f1=fib[t],fib[t-1]
    if ft+f1>LIM: break
    for a in range(1,ft+1):
        if a*(ft+f1)>LIM: break
        bmax=min(ft,(LIM-a*ft)//f1)
        if bmax<a: continue
        kind[a*ft+np.arange(a,bmax+1)*f1]=t%2
D=np.nonzero(kind==0)[0]; U=np.nonzero(kind==1)[0]
for l in range(1,LMAX+1):
    gd=D[l:]-D[:-l]; gu=U[l:]-U[:-l]
    sd=set(np.unique(gd).tolist()); su=set(np.unique(gu).tolist())
    if sd!=su:
        info=[]
        for g in sorted(su-sd):
            idx=np.nonzero(gu==g)[0]; info.append(('U',g,len(idx),int(U[idx[0]]),int(U[idx[-1]])))
        for g in sorted(sd-su):
            idx=np.nonzero(gd==g)[0]; info.append(('D',g,len(idx),int(D[idx[0]]),int(D[idx[-1]])))
        print(l,info)
