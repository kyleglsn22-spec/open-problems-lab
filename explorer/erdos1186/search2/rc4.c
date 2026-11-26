// Float evaluator: residue-class circle colourings of Z_p, limit density of mono 4-APs.
// Colouring for p = r mod b: c(x) = S_{x mod b}(x/p), S_s given by breakpoints
// 0=a_{s,0}<...<a_{s,n_s}=1 and colour col_{s,g} of arc [a_{s,g},a_{s,g+1}).
// Density = (1/b^2) sum_{a0,d0} area{(u,t) in [0,1)^2 : colours of terms agree},
// term j: real position y=u+j t, wrap w=floor(y), residue (a0+j d0 - r w) mod b, colour S_res(y-w).
#include <math.h>
#include <string.h>
#define MAXV 64
#define K 4
static int B, R; static const int *IDX;
static const int *NS; static const double *A; static const int *OFF; static const int *COL;
static double total;
typedef struct {double x[MAXV], y[MAXV]; int n;} poly;
// keep points with ax*u + ay*t >= c  (ax for u, ay for t)
static void clip(const poly *p, poly *q, double au, double at, double c){
  q->n=0;
  for(int i=0;i<p->n;i++){
    int k=(i+1)%p->n;
    double fi=au*p->x[i]+at*p->y[i]-c, fk=au*p->x[k]+at*p->y[k]-c;
    if(fi>=0){q->x[q->n]=p->x[i];q->y[q->n]=p->y[i];q->n++;}
    if((fi>=0)!=(fk>=0)){double s=fi/(fi-fk);
      q->x[q->n]=p->x[i]+s*(p->x[k]-p->x[i]); q->y[q->n]=p->y[i]+s*(p->y[k]-p->y[i]); q->n++;}
  }
}
static double area(const poly *p){double s=0;for(int i=0;i<p->n;i++){int k=(i+1)%p->n;s+=p->x[i]*p->y[k]-p->x[k]*p->y[i];}return 0.5*fabs(s);}
static void rec(int j,const poly *p,int colour,int a0,int d0){
  if(j==K){total+=area(p);return;}
  double lo=1e9,hi=-1e9;
  for(int i=0;i<p->n;i++){double v=p->x[i]+j*p->y[i]; if(v<lo)lo=v; if(v>hi)hi=v;}
  int w0=(int)floor(lo); if(w0<0)w0=0; int w1=(int)floor(hi); if(w1>j)w1=j;
  for(int w=w0;w<=w1;w++){
    int s=IDX[j];
    const double *a=A+OFF[s]; const int *cl=COL+OFF[s]-s; int n=NS[s];
    for(int g=0;g<n;g++){
      if(j>0 && cl[g]!=colour) continue;
      double L=a[g]+w, H=a[g+1]+w;
      if(H<=lo||L>=hi) continue;
      poly q1,q2; const poly *cur=p;
      if(L>lo){clip(cur,&q1,1,j,L); if(q1.n<3)continue; cur=&q1;}
      if(H<hi){clip(cur,&q2,-1,-j,-H); if(q2.n<3)continue; cur=&q2;}
      rec(j+1,cur,j==0?cl[g]:colour,a0,d0);
    }
  }
}
// ns[s]: arcs in residue s; a: concatenated breakpoint arrays (ns[s]+1 each), off[s] start index into a;
// col: concatenated colours (ns[s] each), col for residue s starts at off[s]-s.
double density(int b,int r,const int*ns,const double*a,const int*off,const int*col){
  B=b;R=r;NS=ns;A=a;OFF=off;COL=col;
  double tot=0;
  for(int a0=0;a0<b;a0++)for(int d0=0;d0<b;d0++){
    poly sq={{0,1,1,0},{0,0,1,1},4}; total=0; rec(0,&sq,-1,a0,d0); tot+=total;}
  return tot/(b*(double)b);
}
double density4(const int*ns,const double*a,const int*off,const int*col,const int*idx){
  B=1;R=0;NS=ns;A=a;OFF=off;COL=col;IDX=idx;
  poly sq={{0,1,1,0},{0,0,1,1},4}; total=0; rec(0,&sq,-1,0,0); return total;
}
