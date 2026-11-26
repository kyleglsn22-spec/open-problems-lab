// local search: m top items, components with target sets; minimize # 6-subsets not blocked
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static uint64_t s[2]={0x1234567,0x89abcdef};
static inline uint64_t rnd(){uint64_t s1=s[0];const uint64_t s0=s[1];s[0]=s0;s1^=s1<<23;s[1]=s1^s0^(s1>>17)^(s0>>26);return s[1]+s0;}
double urand(){return (rnd()>>11)*(1.0/9007199254740992.0);}
int m, ncomp, rk[16], off[16], C; char tgt[16][1296];
int nT; int Ts[20000][6]; int tsz=6;
int t[24][64]; int S[20000][64]; int st[20000][16]; int cov[20000]; int bad;
int incl[24][20000], ninc[24];
int enc(int T,int j){int v=0,p=1; for(int c=0;c<rk[j];c++){v+=S[T][off[j]+c]*p;p*=6;} return v;}
void full(){ bad=0; for(int T=0;T<nT;T++){ for(int c=0;c<C;c++){int x=0; for(int q=0;q<6;q++) x+=t[Ts[T][q]][c]; S[T][c]=x%6;} cov[T]=0; for(int j=0;j<ncomp;j++){st[T][j]=tgt[j][enc(T,j)]; cov[T]+=st[T][j];} if(!cov[T]) bad++; } }
int main(int argc,char**argv){
  // input file: m ncomp ; per comp: rank ntargets then targets as digits
  FILE*fp=fopen(argv[1],"r"); s[0]^=atol(argv[2])*2654435761ULL; long iters=atol(argv[3]); double T0=atof(argv[4]);
  fscanf(fp,"%d %d",&m,&ncomp); C=0;
  for(int j=0;j<ncomp;j++){int nt; fscanf(fp,"%d %d",&rk[j],&nt); off[j]=C; C+=rk[j]; memset(tgt[j],0,1296); for(int q=0;q<nt;q++){int v=0,p=1; for(int c=0;c<rk[j];c++){int d; fscanf(fp,"%d",&d); v+=d*p; p*=6;} tgt[j][v]=1;}}
  nT=0; int a[6]; for(a[0]=0;a[0]<m;a[0]++)for(a[1]=a[0]+1;a[1]<m;a[1]++)for(a[2]=a[1]+1;a[2]<m;a[2]++)for(a[3]=a[2]+1;a[3]<m;a[3]++)for(a[4]=a[3]+1;a[4]<m;a[4]++)for(a[5]=a[4]+1;a[5]<m;a[5]++){ for(int q=0;q<6;q++){Ts[nT][q]=a[q]; incl[a[q]][ninc[a[q]]++]=nT;} nT++; }
  int best=1<<30;
  for(long restart=0;;restart++){
    for(int i=0;i<m;i++) for(int c=0;c<C;c++) t[i][c]= i==0?0: rnd()%6;
    full(); 
    double temp=T0;
    for(long it=0;it<iters;it++){
      if(bad==0) break;
      int i=1+rnd()%(m-1); int c=rnd()%C; int nv=rnd()%6; int ov=t[i][c]; if(nv==ov) continue;
      int j=0; while(!(c>=off[j]&&c<off[j]+rk[j])) j++;
      int d=(nv-ov+6)%6; int delta=0;
      for(int q=0;q<ninc[i];q++){int T=incl[i][q]; int old=S[T][c]; S[T][c]=(old+d)%6; int ns=tgt[j][enc(T,j)]; int nc=cov[T]-st[T][j]+ns; delta+=(nc==0)-(cov[T]==0); S[T][c]=old;}
      if(delta<=0 || urand()<exp(-delta/temp)){
        t[i][c]=nv;
        for(int q=0;q<ninc[i];q++){int T=incl[i][q]; S[T][c]=(S[T][c]+d)%6; int ns=tgt[j][enc(T,j)]; int wasbad=cov[T]==0; cov[T]+=ns-st[T][j]; st[T][j]=ns; bad+= (cov[T]==0)-wasbad;}
      }
      temp*=0.9999995; if(temp<0.05) temp=0.05;
    }
    if(bad<best){best=bad; printf("restart %ld best %d\n",restart,best); fflush(stdout);}
    if(bad==0){ for(int i=0;i<m;i++){for(int c=0;c<C;c++) printf("%d ",t[i][c]); printf("\n");} return 0;}
    if(restart>=atol(argv[5])) break;
  }
}
