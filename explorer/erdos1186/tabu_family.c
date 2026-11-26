/* Tabu search over colourings c(x) = G[x mod b][floor(K x / p)] of Z_p, p = r (mod b).
   Reads the exact cell table (from family.py: dump_patterns) on stdin:
     n  then n lines: area k0 j0 k1 j1 k2 j2 k3 j3
   Usage: tabu_family b K r iters restarts seed   (prints best density and G row-major). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int b,K,r,n; double *ar; int (*kj)[8]; unsigned char *G; int *off; /* precomputed index tables */
double eval(void){ double tot=0;
  for(int c=0;c<n;c++){ long cnt=0; const int *o=off+(long)c*b*b*4;
    for(int q=0;q<b*b;q++){ unsigned char x=G[o[4*q]]; if(G[o[4*q+1]]==x&&G[o[4*q+2]]==x&&G[o[4*q+3]]==x) cnt++; }
    tot+=ar[c]*cnt; }
  return tot/((double)b*b); }
int main(int argc,char**argv){
  b=atoi(argv[1]);K=atoi(argv[2]);r=atoi(argv[3]); long iters=atol(argv[4]); int R=atoi(argv[5]); srand(atoi(argv[6]));
  if(scanf("%d",&n)!=1) return 1; ar=malloc(sizeof(double)*n); kj=malloc(sizeof(int[8])*n);
  for(int c=0;c<n;c++){ scanf("%lf",&ar[c]); for(int i=0;i<8;i++) scanf("%d",&kj[c][i]); }
  off=malloc(sizeof(int)*(long)n*b*b*4);
  for(int c=0;c<n;c++) for(int a0=0;a0<b;a0++) for(int d0=0;d0<b;d0++) for(int i=0;i<4;i++){
    long y=((long)a0+(long)i*d0-(long)r*kj[c][2*i])%b; if(y<0)y+=b;
    off[(((long)c*b*b)+a0*b+d0)*4+i]=y*K+kj[c][2*i+1]; }
  int N=b*K; G=malloc(N); unsigned char *best=malloc(N); double gbest=1e9; unsigned char *gb=malloc(N);
  long *tab=malloc(sizeof(long)*N); double *vals=malloc(sizeof(double)*N);
  for(int rs=0;rs<R;rs++){
    for(int i=0;i<N;i++){G[i]=rand()&1;tab[i]=0;} double cur=eval(), bst=cur; memcpy(best,G,N);
    for(long it=1;it<=iters;it++){
      for(int i=0;i<N;i++){G[i]^=1;vals[i]=eval();G[i]^=1;}
      int bi=-1; double bv=1e9; int ties=0;
      for(int i=0;i<N;i++){ if(tab[i]>=it && !(vals[i]<bst-1e-12)) continue;
        if(vals[i]<bv-1e-12){bv=vals[i];bi=i;ties=1;} else if(vals[i]<bv+1e-12){ties++; if(rand()%ties==0) bi=i;} }
      if(bi<0) continue; G[bi]^=1; cur=bv; tab[bi]=it+N/5+2+rand()%3;
      if(cur<bst-1e-12){bst=cur;memcpy(best,G,N);} }
    fprintf(stderr,"restart %d best %.6f\n",rs,bst);
    if(bst<gbest){gbest=bst;memcpy(gb,best,N);} }
  printf("%d %d %d %.9f ",b,K,r,gbest); for(int x=0;x<b;x++) for(int j=0;j<K;j++) putchar('0'+gb[x*K+j]); putchar('\n');
}
