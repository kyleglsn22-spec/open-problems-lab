// Fractional circle colourings: arcs [a_g,a_{g+1}) with P(colour 1)=q_g. Returns
// D = E_{(u,t)} [prod q + prod (1-q)] over the 4 terms frac(u+it).
#include <math.h>
#define MAXV 64
typedef struct {double x[MAXV], y[MAXV]; int n;} poly;
static int N; static const double *A,*Q; static double total;
static void clip(const poly *p, poly *q, double au, double at, double c){
  q->n=0;
  for(int i=0;i<p->n;i++){int k=(i+1)%p->n;
    double fi=au*p->x[i]+at*p->y[i]-c, fk=au*p->x[k]+at*p->y[k]-c;
    if(fi>=0){q->x[q->n]=p->x[i];q->y[q->n]=p->y[i];q->n++;}
    if((fi>=0)!=(fk>=0)){double s=fi/(fi-fk);
      q->x[q->n]=p->x[i]+s*(p->x[k]-p->x[i]); q->y[q->n]=p->y[i]+s*(p->y[k]-p->y[i]); q->n++;}}
}
static double area(const poly *p){double s=0;for(int i=0;i<p->n;i++){int k=(i+1)%p->n;s+=p->x[i]*p->y[k]-p->x[k]*p->y[i];}return 0.5*fabs(s);}
static void rec(int j,const poly *p,double pq,double pp){
  if(j==4){total+=area(p)*(pq+pp);return;}
  double lo=1e9,hi=-1e9;
  for(int i=0;i<p->n;i++){double v=p->x[i]+j*p->y[i]; if(v<lo)lo=v; if(v>hi)hi=v;}
  int w0=(int)floor(lo); if(w0<0)w0=0; int w1=(int)floor(hi); if(w1>j)w1=j;
  for(int w=w0;w<=w1;w++) for(int g=0;g<N;g++){
    double L=A[g]+w,H=A[g+1]+w; if(H<=lo||L>=hi)continue;
    double nq=pq*Q[g], np=pp*(1-Q[g]); if(nq+np==0) continue;
    poly q1,q2; const poly *cur=p;
    if(L>lo){clip(cur,&q1,1,j,L); if(q1.n<3)continue; cur=&q1;}
    if(H<hi){clip(cur,&q2,-1,-j,-H); if(q2.n<3)continue; cur=&q2;}
    rec(j+1,cur,nq,np);
  }
}
double dens(int n,const double*a,const double*q){N=n;A=a;Q=q;poly sq={{0,1,1,0},{0,0,1,1},4};total=0;rec(0,&sq,1,1);return total;}
