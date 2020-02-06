`is_element/YC` := (N::posint) -> (A::set) -> proc(x)
 local a,i,j,t,G,J,E,B;
 global reason;

 if not(type(x,table)) then
  reason := [convert(procname,string),"x is not a table",x];
  return false;  
 fi;

 if map(op,{indices(x)}) <> A then
  reason := [convert(procname,string),"x is not indexed by A",x,A];
  return false;
 fi;

 for a in A do
  if not `is_element/R`(N)(x[a]) then
   reason := [convert(procname,string),"x[a] is not in R^N",a,x[a],N];
   return false;
  fi;
 od;

 for i from 1 to N do
  if min(seq(x[a][i],a in A)) <> 0 then
   reason := [convert(procname,string),"min(x[i]) <> 0",i,x];
   return false;
  fi;
 od;
 
 G := `gaps/F`(N)(A)(x);

 if max(G) <> 1 then
  reason := [convert(procname,string),"max(G) <> 1",G];
  return false;
 fi;
 
 J := select(j -> G[j] = 1,[seq(k,k=1..N)]);
 E := {seq(seq([a,b],b in A),a in A)};
 for j in J do
  t := table();
  for a in A do t[a] := x[a][j]; od;
  B := blur_preorder(A)(t,1);
  E := E intersect B intersect `op/preord`(A)(B);
 od:

 if E <> {seq([a,a],a in A)} then
  reason := [convert(procname,string),"E <> Delta",E];
  return false;
 fi;
 
 return true;
end;

`is_equal/YC` := (N::posint) -> (A::set) -> proc(x,y)
 local a;
 global reason;

 for a in A do
  if x[a] <> y[a] then
   reason := [convert(procname,string),"x[a] <> y[a]",a,x[a],y[a]];
   return false;
  fi;
 od;

 return true;
end;

`inc/YC/F` := (N::posint) -> (A::set) -> (x) -> x;

`mu_bar/YC/PP` := (N::posint) -> (A::set) -> proc(x)
 local i,j,k,p,m,a,b,L,A0,T0,g0,g,t,s,AA,R,RR;

# DEBUG();
 
 L := NULL;
 m := nops(A);

 for i from 1 to N do
  A0 := sort([op(A)],(a,b) -> x[a][i] <= x[b][i]);
  T0 := [seq(x[A0[j]][i],j=1..m)];
  for j from 1 to m-1 do 
   L := L,[i,A0[j],A0[j+1],T0[j+1]-T0[j]];
  od;  
 od;

 L := sort([L],(a,b) -> a[4] <= b[4]);
 k := nops(L);

 R := table():
 t := table():

 R[1] := `mu/F/PP`(N)(A)(x);
 t[1] := L[1][4];
 s := table():
 s[R[1]] := t[1];

 AA := {seq(seq([a,b],b in A),a in A)};

 for p from 2 to k do
  i,a,b,g := op(L[p-1]);
  RR := R[p-1][i];
  RR := RR union select(xy -> member([xy[1],b],RR) and member([a,xy[2]],RR),AA);
  R[p] := [seq(R[p-1][j],j=1..i-1),RR,seq(R[p-1][j],j=i+1..N)];
  t[p] := L[p][4] - L[p-1][4];
  if t[p] > 0 then s[R[p]] := t[p]; fi;
 od;

 return eval(s);
end:

`sigma_bar/PP/YC` := (N::posint) -> (A::set) -> proc(t)
 local x,y,a,C,s,R;
 
 x := table();
 for a in A do x[a] := [0$N]; od;

 C := map(op,[indices(t)]);
 for R in C do
  s := t[R];
  y := `sigma/PP/F`(N)(A)(R);
  for a in A do
   x[a] := x[a] +~ s *~ y[a];
  od;
 od;

 return eval(x);
end:
