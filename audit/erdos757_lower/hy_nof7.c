// Exhaustive check of 17*tau <= 5n+3m over all labeled linear F7-free 3-uniform
// hypergraphs on exactly n labeled vertices (isolated vertices allowed).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int n, T; int tri[128][3]; int pairIdx[16][16];
uint64_t hit[128][8]; // subsets hitting triple i
uint64_t layer[17][8];
// F7 copies indexed by max edge
int *cop[128]; int ncop[128]; int capc[128];
u128 used; // edges present
int pairUsed[16][16];
long long cnt=0, viol=0; int minslack=1<<30; long long eqcnt=0;
int maxm=0;
int f7e[5][3]={{0,1,2},{0,3,4},{0,5,6},{1,3,5},{2,4,6}};
int triIndex(int a,int b,int c){int x[3]={a,b,c};for(int i=0;i<3;i++)for(int j=i+1;j<3;j++)if(x[j]<x[i]){int t=x[i];x[i]=x[j];x[j]=t;}
 for(int i=0;i<T;i++) if(tri[i][0]==x[0]&&tri[i][1]==x[1]&&tri[i][2]==x[2]) return i; return -1;}
void addcopy(int *es){int mx=0;for(int k=0;k<5;k++) if(es[k]>mx) mx=es[k];
 if(ncop[mx]+4>capc[mx]){capc[mx]=capc[mx]*2+64;cop[mx]=realloc(cop[mx],capc[mx]*sizeof(int));}
 int j=0; for(int k=0;k<5;k++) if(es[k]!=mx) cop[mx][ncop[mx]++]=es[k], j++; }
u128 seen_dummy;
void genCopies(){ // all injective g: Fin7 -> [n]; dedupe by sorting edge sets via hash set
 int g[7]; int sz=1<<22; u128 *hs=calloc(sz,sizeof(u128)); char*occ=calloc(sz,1);
 int idx[7]; 
 // iterate all 7-permutations
 int N=1; for(int i=0;i<7;i++) N*=n; 
 for(long code=0; code<(long)N; code++){ long c=code; int ok=1; int mask=0;
  for(int i=0;i<7;i++){g[i]=c%n;c/=n; if(mask>>g[i]&1){ok=0;break;} mask|=1<<g[i];}
  if(!ok) continue; int es[5]; u128 key=0;
  for(int k=0;k<5;k++){es[k]=triIndex(g[f7e[k][0]],g[f7e[k][1]],g[f7e[k][2]]); key|=((u128)1)<<es[k];}
  uint64_t h=(uint64_t)(key*0x9E3779B97F4A7C15ULL ^ (key>>64)*0xC2B2AE3D27D4EB4FULL); h^=h>>29; unsigned p=h&(sz-1);
  int dup=0; while(occ[p]){ if(hs[p]==key){dup=1;break;} p=(p+1)&(sz-1);} if(dup) continue; occ[p]=1; hs[p]=key; addcopy(es);} }
int curTau;
void evalNode(uint64_t *valid,int m,int tau){ cnt++; int slack=5*n+3*m-17*tau; if(slack<0){viol++; if(viol<5){printf("VIOLATION n=%d m=%d tau=%d edges:",n,m,tau); for(int i=0;i<T;i++) if(used>>i&1) printf(" %d%d%d",tri[i][0],tri[i][1],tri[i][2]); printf("\n");}}
 if(slack<minslack){minslack=slack;eqcnt=0;} if(slack==minslack) eqcnt++; if(m>maxm)maxm=m; }
void dfs(int i,uint64_t *valid,int m,int tau){
 for(int j=i;j<T;j++){ int a=tri[j][0],b=tri[j][1],c=tri[j][2];
  if(pairUsed[a][b]||pairUsed[a][c]||pairUsed[b][c]) continue;
  // F7 check with max edge j
  int bad=0; for(int k=0;k<ncop[j];k+=4){ int *q=cop[j]+k; if((used>>q[0]&1)&&(used>>q[1]&1)&&(used>>q[2]&1)&&(used>>q[3]&1)){bad=1;break;} }
  if(bad) continue;
  uint64_t nv[8]; int W=((1<<n)+63)/64; for(int w=0;w<W;w++) nv[w]=valid[w]&hit[j][w];
  int t=tau; for(;;t++){int nz=0; for(int w=0;w<W;w++) if(nv[w]&layer[t][w]){nz=1;break;} if(nz)break;}
  used|=((u128)1)<<j; pairUsed[a][b]=pairUsed[a][c]=pairUsed[b][c]=1;
  evalNode(nv,m+1,t); dfs(j+1,nv,m+1,t);
  used&=~(((u128)1)<<j); pairUsed[a][b]=pairUsed[a][c]=pairUsed[b][c]=0; }
}
int main(int argc,char**argv){ n=atoi(argv[1]); T=0;
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++){tri[T][0]=a;tri[T][1]=b;tri[T][2]=c;T++;}
 int S=1<<n; for(int s=0;s<S;s++){ int pc=__builtin_popcount(s); layer[pc][s/64]|=1ULL<<(s%64);
  for(int i=0;i<T;i++) if(s&((1<<tri[i][0])|(1<<tri[i][1])|(1<<tri[i][2]))) hit[i][s/64]|=1ULL<<(s%64);}
 if(n>=7 && argc<3) genCopies();
 long tot=0; for(int i=0;i<T;i++) tot+=ncop[i]/4; fprintf(stderr,"n=%d triples=%d F7copies=%ld\n",n,T,tot);
 uint64_t v[8]; memset(v,0,sizeof v); for(int s=0;s<S;s++) v[s/64]|=1ULL<<(s%64);
 evalNode(v,0,0); dfs(0,v,0,0);
 printf("n=%d hypergraphs=%lld violations=%lld minslack=%d (count %lld) maxm=%d\n",n,cnt,viol,minslack,eqcnt,maxm); }
