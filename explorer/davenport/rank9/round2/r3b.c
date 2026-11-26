#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define N 216
int add[N][N], neg_[N], dbl_[N], wt[N];
static uint64_t s[2]={0x1234567,0x89abcdef};
static inline uint64_t rnd(){uint64_t s1=s[0];const uint64_t s0=s[1];s[0]=s0;s1^=s1<<23;s[1]=s1^s0^(s1>>17)^(s0>>26);return s[1]+s0;}
int main(int argc,char**argv){
  s[0]^=atoi(argv[1])*2654435761ULL; long iters=atol(argv[2]); int maxd=atoi(argv[3]);
  for(int g=0;g<N;g++){int a=g%6,b=g/6%6,c=g/36; neg_[g]=((6-a)%6)+6*((6-b)%6)+36*((6-c)%6); dbl_[g]=(2*a%6)+6*(2*b%6)+36*(2*c%6); wt[g]=(a!=0)+(b!=0)+(c!=0);
    for(int h=0;h<N;h++){int x=h%6,y=h/6%6,z=h/36; add[g][h]=(a+x)%6+6*((b+y)%6)+36*((c+z)%6);}}
  long valid=0;
  for(long it=0;it<iters;it++){
    int nd=2+rnd()%(maxd-1); int el[16], mu[16];
    // start with basis e1,e2,e3 always (WLOG up to GL? not exactly) then random others
    el[0]=1; el[1]=6; el[2]=36; for(int i=3;i<nd+3;i++){ el[i]=1+rnd()%(N-1);} nd+=3;
    // random multiplicities summing to 14, each >=0
    for(int i=0;i<nd;i++) mu[i]=0;
    for(int t=0;t<14;t++) mu[rnd()%nd]++;
    char R[N]; memset(R,0,N); R[0]=1; int bad=0;
    for(int i=0;i<nd&&!bad;i++) for(int m=0;m<mu[i];m++){int g=el[i]; if(R[neg_[g]]){bad=1;break;} char R2[N]; memcpy(R2,R,N); for(int x=0;x<N;x++) if(R[x]) R2[add[g][x]]=1; memcpy(R,R2,N);}
    if(bad) continue; valid++;
    int M[N],nm=0; for(int x=0;x<N;x++) if(!R[x]) M[nm++]=x;
    char hd[N]; memset(hd,0,N); for(int i=0;i<nm;i++) hd[dbl_[M[i]]]=1;
    int hit=0;
    for(int i=0;i<nm&&!hit;i++)for(int j=0;j<nm&&!hit;j++)for(int k=0;k<nm&&!hit;k++){int t=add[add[M[i]][M[j]]][neg_[M[k]]]; if(hd[t]) hit=1;}
    if(hit){printf("FOUND:"); for(int i=0;i<nd;i++) if(mu[i]) printf(" %dx%d",mu[i],el[i]); printf("\n"); fflush(stdout); return 0;}
  }
  printf("done none, valid %ld\n",valid);
}
