######################################################################
# F(N)(A) is Inj(A,RR^N) modulo translation and scaling.
#
# Elements are represented as tables indexed by A, whose values 
# are lists of length N of real numbers.  The equivalence relation
# is built into the definition of the function `is_equal/F` rather
# than the representation of the elements.

`is_element/F` := (N::posint) -> (A::set) -> proc(x)
 local a;
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

 if nops(map(op,{entries(x)})) <> nops(A) then
  reason := [convert(procname,string),"x is not injective",x];
  return false;  
 fi;

 return true;
end;

######################################################################
# This function normalises the infinity norm.  This is convenient
# because it preserves rationality, but it is geometrically unpleasant.

`normalise/F` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,r,a;

 x0 := table();
 u := [0$N];

 for a in A do
  x0[a] := x[a];
  u := u +~ x[a];
 od;
 u := u /~ nops(A);
 r := 0;
 for a in A do
  x0[a] := x0[a] -~ u;
  r := max(r,op(map(abs,x0[a])));
 od;
 for a in A do
  x0[a] := x0[a] /~ r;
 od;

 return(eval(x0));
end;

######################################################################
# This function normalises the euclidean norm
`normalise_2/F` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,r2,r,a;

 x0 := table();
 u := [0$N];

 for a in A do
  x0[a] := x[a];
  u := u +~ x[a];
 od;
 u := u /~ nops(A);
 r2 := 0;
 for a in A do
  x0[a] := x0[a] -~ u;
  r2 := r2 + `norm_2/R`(N)(x0[a])^2;
 od;
 r := sqrt(r2);

 for a in A do
  x0[a] := x0[a] /~ r;
 od;

 return(eval(x0));
end;

######################################################################

`is_equal/F` := (N::posint) -> (A::set) -> proc(x,y) 
 local x0,y0,a;
 global reason;

 x0 := `normalise/F`(N)(A)(x);
 y0 := `normalise/F`(N)(A)(y);

 for a in A do
  if not(`is_equal/R`(N)(x0[a],y0[a])) then
   reason := [convert(procname,string),"x0[a] <> y0[a]",a,x0[a],y0[a]];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_leq/F` := NULL;

######################################################################

`random_element/F` := (N::posint) -> (A::set) -> proc()
 local ok,x,a;

 ok := false;
 while not(ok) do
  x := table();
  for a in A do
   x[a] := `random_element/R`(N)();
  od:
  ok := `is_element/F`(N)(A)(x);
 od;

 return eval(x);
end;

######################################################################

`list_elements/F` := NULL;

######################################################################

`count_elements/F` := NULL;

######################################################################

`separation_infinity/F` := (N::posint) -> (A::set) -> proc(x)
 local x0,d,n,i,j;

 x0 := `normalise/F`(N)(A)(x);
 d := 2;
 n := nops(A);

 for i from 1 to n-1 do 
  for j from i+1 to n do
   d := min(d,`d_infinity/R`(N)(x0[A[i]],x0[A[j]]));
  od;
 od;

 return d;
end;

######################################################################

`fatten/F` := (N::posint) -> (A::set) -> proc(x)
 local x0,d,m,a,i,e,u;

 x0 := `normalise/F`(N)(A)(x);
 d := `separation_infinity/F`(N)(A)(x0);
 m := 0;
 for a in A do
  for i from 1 to N do
   m := max(m,d/2+abs(x0[a][i]));
  od;
 od;
 
 e := [1 $ N];

 for a in A do
  u[a] := [((x0[a] -~ ((d/2) *~ e)) /~ m +~ e) /~ 2,
           ((x0[a] +~ ((d/2) *~ e)) /~ m +~ e) /~ 2];
 od;

 return eval(u);
end;

######################################################################

`inc/F/Fbar` := (N::posint) -> (A::set) -> proc(x)
 local y,P,T,t;

 y := table();

 P := `list_elements/big_subsets`(A);

 for T in P do
  y[T] := table([seq(t = x[t],t in T)]);
 od:

 return eval(y);
end;

######################################################################

`gaps/F` := (N::posint) -> (A::set) -> proc(x)
 local G,V,W,m,i,j,a;
 
 G := NULL;
 m := nops(A);
 
 for i from 1 to N do 
  V := sort([seq(x[a][i],a in A)]);
  W := [seq(V[j+1] - V[j],j = 1 .. m-1)];
  G := G,max(W);
 od;

 G := [G];
 return G;
end;

######################################################################

`gap/F` := (N::posint) -> (A::set) -> proc(x)
 return max(`gaps/F`(N)(A)(x));
end;

######################################################################

`normalise_gap/F` := (N::posint) -> (A::set) -> proc(x)
 local m,g,x0,a,i;
 
 m := [seq(min(seq(x[a][i],a in A)),i=1..N)];
 g := `gap/F`(N)(A)(x);
 
 x0 := table();
 for a in A do
  x0[a] := (x[a] -~ m) /~ g;
 od;

 return eval(x0);
end;

######################################################################

`delta/F` := (N::posint) -> (A::set) -> (a,b) -> proc(x)
 local u,n,i;
 u := x[b] -~ x[a];
 n := sqrt(add(u[i]^2,i=1..N));
 return u /~ n;
end:

######################################################################

`draw_unnormalised/F` := (A::set) -> proc(x)
 local a;
 display(seq(point(x[a]),a in A),scaling=constrained,axes=none);
end;

######################################################################

`draw/F` := (A::set) -> proc(x)
 display(`draw_unnormalised/F`(A)(`normalise/F`(2)(A)(x)),view=[-1..1,-1..1]);
end;

