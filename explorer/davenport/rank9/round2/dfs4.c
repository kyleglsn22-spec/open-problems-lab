// randomized DFS: zero-sumfree length L in C6^r, test 5-condition (or 3-condition) on Miss
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
int r,N,L,cond; int *addT,*negT,*wtT;
static uint64_t s[2]={0x1234567,0x89abcdef};
static inline uint64_t rnd(){uint64_t s1=s[0];const uint64_t s0=s[1];s[0]=s0;s1^=s1<<23;s[1]=s1^s0^(s1>>17)^(s0>>26);return s[1]+s0;}
int dig(int g,int j){for(int i=0;i<j;i++) g/=6; return g%6;}
char R[40][1296]; int seq[40]; long leaves=0, nodes=0; int wbias;
int test(char*Rr){
  int M[1296],nm=0; for(int x=0;x<N;x++) if(!Rr[x]) M[nm++]=x;
  if(cond==5){
    for(int i=0;i<nm;i++){int x=M[i],nx=negT[x]; for(int a=0;a<nm;a++)for(int b=a;b<nm;b++){int uv=addT[M[a]*N+M[b]]; int t1=addT[uv*N+nx]; if(Rr[t1]) continue; int t2=addT[t1*N+nx]; if(!Rr[t2]) {printf("x=%d u=%d v=%d\n",x,M[a],M[b]); return 1;}}}
  } else { // 3-condition: P,Q,R in Miss with P+Q+R in 2G
    char twoG[1296]; memset(twoG,0,N); for(int g=0;g<N;g++) twoG[addT[g*N+g]]=1;
    for(int a=0;a<nm;a++)for(int b=a;b<nm;b++)for(int c=b;c<nm;c++) if(twoG[addT[addT[M[a]*N+M[b]]*N+M[c]]]) return 1;
  }
  return 0;
}
long budget;
int dfs(int d,int minidx){
  if(++nodes>budget) return -1;
  if(d==L){ leaves++; if(test(R[d])){ printf("FOUND:"); for(int i=0;i<L;i++) printf(" %d",seq[i]); printf("\n"); fflush(stdout); return 1;} return 0;}
  // candidate list: elements g>=minidx (multiset order) with -g not in R
  int cand[1296],nc=0; for(int g=minidx; g<N; g++) if(g && !R[d][negT[g]]) cand[nc++]=g;
  if(!nc) return 0;
  // try a few random children, biased toward repeats/low weight
  int tries=2;
  for(int t=0;t<tries;t++){
    int g;
    if(d>0 && rnd()%2 && !R[d][negT[seq[d-1]]]) g=seq[d-1]; else { g=cand[rnd()%nc]; if(wbias) for(int q=0;q<wbias;q++){int h=cand[rnd()%nc]; if(wtT[h]<wtT[g]) g=h;} }
    seq[d]=g; memcpy(R[d+1],R[d],N); for(int x=0;x<N;x++) if(R[d][x]) R[d+1][addT[g*N+x]]=1;
    int res=dfs(d+1,g); if(res) return res;
  }
  return 0;
}
int main(int argc,char**argv){
  r=atoi(argv[1]); L=atoi(argv[2]); s[0]^=atoi(argv[3])*2654435761ULL; long iters=atol(argv[4]); cond=atoi(argv[5]); wbias=atoi(argv[6]);
  N=1; for(int i=0;i<r;i++) N*=6;
  addT=malloc(sizeof(int)*N*N); negT=malloc(4*N); wtT=malloc(4*N);
  for(int g=0;g<N;g++){ int ng=0,p=1,w=0; for(int j=0;j<r;j++){int a=dig(g,j); ng+=((6-a)%6)*p; w+=(a!=0); p*=6;} negT[g]=ng; wtT[g]=w;
    for(int h=0;h<N;h++){int v=0;p=1; for(int j=0;j<r;j++){v+=((dig(g,j)+dig(h,j))%6)*p;p*=6;} addT[g*N+h]=v;}}
  for(long it=0;it<iters;it++){ memset(R[0],0,N); R[0][0]=1; nodes=0; budget=2000; int res=dfs(0,1); if(res==1) return 0; }
  printf("none leaves=%ld\n",leaves);
}
