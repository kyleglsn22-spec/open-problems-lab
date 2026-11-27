# usage: set G, name, then Read("pairs.g")
# writes JSON-like lines: group gens, then pairs (Hgens,Jgens)
PermToList:=function(p,n) return ListPerm(p,n); end;
DumpPairs:=function(G,name,fn,minO,maxO,maxPairs)
  local n,cls,reps,out,i,j,H,N,cl,orbs,J,cnt,gl;
  n:=LargestMovedPoint(G);
  gl:=function(K) local g; g:=SmallGeneratingSet(K); if g=[] then g:=[()]; fi; return List(g,x->PermToList(x,n)); end;
  cls:=Filtered(ConjugacyClassesSubgroups(G),c->Size(Representative(c))>=minO and Size(Representative(c))<=maxO);
  out:=OutputTextFile(fn,false); SetPrintFormattingStatus(out,false);
  PrintTo(out,""); AppendTo(out,"G ",name," ",Size(G)," ",gl(G),"\n");
  cnt:=0;
  for i in [1..Length(cls)] do
    H:=Representative(cls[i]); N:=Normalizer(G,H);
    for j in [i..Length(cls)] do
      cl:=AsList(cls[j]);
      orbs:=OrbitsDomain(N,cl,OnPoints);
      for J in List(orbs,o->o[1]) do
        if Size(Intersection(H,J))=1 then
          cnt:=cnt+1;
          if cnt<=maxPairs then AppendTo(out,"P ",Size(H)," ",Size(J)," ",gl(H)," ",gl(J),"\n"); fi;
        fi;
      od;
    od;
  od;
  CloseStream(out);
  return cnt;
end;
