// structured family: basis e_1..e_{b-1}, f (last coord). For each j: e_j^{m1} (e_j+lam f)^{m2}; f^alpha; one z.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int r,N; int *addT,*negT; int pw[6];
int dig(int g,int j){return g/pw[j]%6;}
int test(char*Rr,int cond){
  static int M[1296]; int nm=0; for(int x=0;x<N;x++) if(!Rr[x]) M[nm++]=x;
  if(cond==5){
    for(int i=0;i<nm;i++){int x=M[i],nx=negT[x]; for(int a=0;a<nm;a++)for(int b=a;b<nm;b++){int uv=addT[M[a]*N+M[b]]; int t1=addT[uv*N+nx]; if(Rr[t1]) continue; int t2=addT[t1*N+nx]; if(!Rr[t2]) return 1;}}
  } else {
    static char twoG[1296]; memset(twoG,0,N); for(int g=0;g<N;g++) twoG[addT[g*N+g]]=1;
    for(int a=0;a<nm;a++)for(int b=a;b<nm;b++)for(int c=b;c<nm;c++) if(twoG[addT[addT[M[a]*N+M[b]]*N+M[c]]]) return 1;
  }
  return 0;
}
int main(int argc,char**argv){
  r=atoi(argv[1]); int zmode=atoi(argv[2]);
  N=1; for(int i=0;i<r;i++){pw[i]=N; N*=6;} pw[r]=N;
  addT=malloc(sizeof(int)*N*N); negT=malloc(4*N);
  for(int g=0;g<N;g++){ int ng=0; for(int j=0;j<r;j++){ng+=((6-dig(g,j))%6)*pw[j];} negT[g]=ng;
    for(int h=0;h<N;h++){int v=0; for(int j=0;j<r;j++) v+=((dig(g,j)+dig(h,j))%6)*pw[j]; addT[g*N+h]=v;}}
  int L=5*r-1; int nb=r-1; int f=pw[r-1];
  // patterns per j: (m1,lam,m2) with lam in1..5, m2>=1, m1+m2 in {3,4,5}; or (m,0,0) m in 3..5
  int P[200][3],np=0;
  for(int s=3;s<=5;s++){ P[np][0]=s;P[np][1]=0;P[np][2]=0;np++; for(int lam=1;lam<6;lam++) for(int m2=1;m2<=s;m2++){P[np][0]=s-m2;P[np][1]=lam;P[np][2]=m2;np++;}}
  long cnt=0,zsf=0,h3=0,h5=0;
  int idx[4]={0,0,0,0};
  char R[1296],R2[1296];
  // iterate nondecreasing pattern indices for j
  int total=1; for(int j=0;j<nb;j++) total*=np;
  for(int code=0;code<total;code++){
    int c=code, ok=1; for(int j=0;j<nb;j++){idx[j]=c%np;c/=np;} for(int j=1;j<nb;j++) if(idx[j]<idx[j-1]) ok=0; if(!ok) continue;
    int len=0; for(int j=0;j<nb;j++) len+=P[idx[j]][0]+P[idx[j]][2];
    int alpha=L-1-len; if(alpha<0||alpha>5) continue;
    // base sequence
    int base[40],bl=0;
    for(int j=0;j<nb;j++){ int e=pw[j]; for(int q=0;q<P[idx[j]][0];q++) base[bl++]=e; int el=addT[e*N+ (P[idx[j]][1]*f)]; for(int q=0;q<P[idx[j]][2];q++) base[bl++]=el; }
    for(int q=0;q<alpha;q++) base[bl++]=f;
    // Sigma0 of base
    memset(R,0,N); R[0]=1; int bad=0;
    for(int i=0;i<bl&&!bad;i++){int g=base[i]; if(R[negT[g]]){bad=1;break;} memcpy(R2,R,N); for(int x=0;x<N;x++) if(R[x]) R2[addT[g*N+x]]=1; memcpy(R,R2,N);}
    if(bad) continue;
    for(int z=1;z<N;z++){
      if(zmode==1){ int okz=1; for(int j=0;j<nb;j++){int d=dig(z,j); if(!(d==0||d==1||d==5)) okz=0;} if(!okz) continue; }
      cnt++;
      if(R[negT[z]]) continue;
      memcpy(R2,R,N); for(int x=0;x<N;x++) if(R[x]) R2[addT[z*N+x]]=1;
      zsf++;
      int t3=test(R2,3); if(t3){h3++; int t5=test(R2,5); if(t5){h5++; printf("FOUND5 pats"); for(int j=0;j<nb;j++) printf(" (%d,%d,%d)",P[idx[j]][0],P[idx[j]][1],P[idx[j]][2]); printf(" alpha=%d z=%d\n",alpha,z); fflush(stdout);} else if(h3<=3){printf("cond3 example pats"); for(int j=0;j<nb;j++) printf(" (%d,%d,%d)",P[idx[j]][0],P[idx[j]][1],P[idx[j]][2]); printf(" alpha=%d z=%d\n",alpha,z);} }
    }
  }
  printf("r=%d checked=%ld zsf=%ld cond3=%ld cond5=%ld\n",r,cnt,zsf,h3,h5);
}
