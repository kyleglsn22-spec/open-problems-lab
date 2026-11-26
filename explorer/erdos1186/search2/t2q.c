// Colouring c(x)=F[floor(Mu*x/p)][floor(Mw*frac(x^2/p))]. Limit density of mono 4-APs.
// linear coord: b_i = b0 + i*del + C[c][i] (mod Mu), weights Wn/12, b0,del uniform.
// quad coord: j0,j1,j2 uniform, j3 = j0-3j1+3j2+kap (mod Mw), kap weight PK/54.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const int C[8][4]={{0,0,0,0},{0,0,0,1},{0,0,1,1},{0,0,1,2},{0,1,1,1},{0,1,1,2},{0,1,2,2},{0,1,2,3}};
static const int Wn[8]={2,1,2,1,1,2,1,2};
static const int PK[7]={1,6,12,16,12,6,1};
static int Mu,Mw,inv3; static unsigned char *F;
static inline int md(int a,int m){a%=m; return a<0?a+m:a;}
long long full(void){
  long long tot=0;
  for(int c=0;c<8;c++)for(int k=0;k<7;k++){long long s=0; int kap=k-3;
    for(int b0=0;b0<Mu;b0++)for(int d=0;d<Mu;d++){
      int u0=b0,u1=md(b0+d+C[c][1],Mu),u2=md(b0+2*d+C[c][2],Mu),u3=md(b0+3*d+C[c][3],Mu);
      for(int j0=0;j0<Mw;j0++)for(int j1=0;j1<Mw;j1++)for(int j2=0;j2<Mw;j2++){
        int j3=md(j0-3*j1+3*j2+kap,Mw);
        int v0=F[u0*Mw+j0],v1=F[u1*Mw+j1],v2=F[u2*Mw+j2],v3=F[u3*Mw+j3];
        s+=(v0==v1&&v1==v2&&v2==v3);}}
    tot+=s*Wn[c]*PK[k];}
  return tot;
}
// enumerate APs containing cell (X,J) at position i, count once (first position hit)
long long delta(int X,int J){
  long long tot=0; int cell=X*Mw+J;
  for(int c=0;c<8;c++)for(int k=0;k<7;k++){long long s=0;int kap=k-3;
    for(int i=0;i<4;i++)for(int d=0;d<Mu;d++){
      int b0=md(X-i*d-C[c][i],Mu); int u[4];
      for(int q=0;q<4;q++)u[q]=md(b0+q*d+C[c][q],Mu);
      for(int a=0;a<Mw;a++)for(int bb=0;bb<Mw;bb++){
        int j[4];
        if(i==0){j[0]=J;j[1]=a;j[2]=bb;}
        else if(i==1){j[0]=a;j[1]=J;j[2]=bb;}
        else if(i==2){j[0]=a;j[1]=bb;j[2]=J;}
        else {j[0]=a;j[1]=bb;j[2]=md((J-a+3*bb-kap)*inv3,Mw);}
        j[3]=md(j[0]-3*j[1]+3*j[2]+kap,Mw);
        int idx[4],dup=0,v[4],w[4];
        for(int q=0;q<4;q++)idx[q]=u[q]*Mw+j[q];
        for(int q=0;q<i;q++) if(idx[q]==cell) dup=1;
        if(dup) continue;
        for(int q=0;q<4;q++){v[q]=F[idx[q]]; w[q]=(idx[q]==cell)?1-v[q]:v[q];}
        s+=(w[0]==w[1]&&w[1]==w[2]&&w[2]==w[3])-(v[0]==v[1]&&v[1]==v[2]&&v[2]==v[3]);}}
    tot+=s*Wn[c]*PK[k];}
  return tot;
}
int main(int argc,char**argv){
  Mu=atoi(argv[1]);Mw=atoi(argv[2]);int iters=atoi(argv[3]);srand(atoi(argv[4]));
  if(Mw%3==0){fprintf(stderr,"Mw must be coprime to 3\n");return 1;}
  inv3=1; while((3*inv3)%Mw!=1%Mw) inv3++;
  int n=Mu*Mw; F=malloc(n);
  for(int i=0;i<n;i++)F[i]=rand()&1;
  if(argc>5 && argv[5][0]!='-'){ // init from linear word of length Mu (copied across w)
    for(int u=0;u<Mu;u++)for(int w=0;w<Mw;w++)F[u*Mw+w]=argv[5][u]-'0';}
  double norm=12.0*54*Mu*Mu*(double)Mw*Mw*Mw;
  long long cur=full(),best=cur; printf("start %.9f\n",cur/norm);fflush(stdout);
  unsigned char*bestF=malloc(n);memcpy(bestF,F,n);int*tabu=calloc(n,sizeof(int));int ten=n/10+2;
  for(int it=1;it<=iters;it++){
    long long bd=1LL<<60;int bi=-1;
    for(int i=0;i<n;i++){long long d=delta(i/Mw,i%Mw); if((tabu[i]<it||cur+d<best)&&d<bd){bd=d;bi=i;}}
    F[bi]^=1;cur+=bd;tabu[bi]=it+ten+rand()%ten;
    if(cur<best){best=cur;memcpy(bestF,F,n);printf("it %d best %.9f\n",it,best/norm);fflush(stdout);}
  }
  memcpy(F,bestF,n);long long chk=full();
  printf("FINAL %d %d %.12f check %.12f\n",Mu,Mw,best/norm,chk/norm);
  for(int u=0;u<Mu;u++){for(int w=0;w<Mw;w++)putchar('0'+F[u*Mw+w]);putchar('\n');}
}
