import numpy as np, json
C=[(0,0,0,0),(0,0,0,1),(0,0,1,1),(0,0,1,2),(0,1,1,1),(0,1,1,2),(0,1,2,2),(0,1,2,3)]
Wt=np.array([2,1,2,1,1,2,1,2])/12
def D_and_grad(q):
    M=len(q); p=1-q; D=0.0; g=np.zeros(M)
    idx=np.arange(M)
    for c,w in zip(C,Wt):
        for d in range(M):
            I=[(idx+i*d+c[i])%M for i in range(4)]
            Q=[q[I[i]] for i in range(4)]; P=[p[I[i]] for i in range(4)]
            prodq=Q[0]*Q[1]*Q[2]*Q[3]; prodp=P[0]*P[1]*P[2]*P[3]
            D+=w*(prodq.sum()+prodp.sum())
            for i in range(4):
                oq=np.ones(M); op=np.ones(M)
                for j in range(4):
                    if j!=i: oq=oq*Q[j]; op=op*P[j]
                np.add.at(g,I[i],w*(oq-op))
    return D/M**2, g/M**2
if __name__=='__main__':
    import sys
    # argv[1]: Marquardt's results/zp_k4_c.json (github.com/incrediblecrab/erdos-problems, p1186)
    d=json.load(open(sys.argv[1]))
    w=d['496']['word']; q=np.array([int(ch) for ch in w],float)
    D,g=D_and_grad(q); print(D, d['496']['value_float'])
    # variation: flipping fully costs g*(1-2q) ; report min of g*(1-2q) (negative => improving flip direction)
    v=g*(1-2*q); print('min first-order change per unit',v.min(), (v<0).sum())
