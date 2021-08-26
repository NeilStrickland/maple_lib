`is_element/tree_Fbar_alt` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local TT1,P,children,T,UU,UU1;
 global reason;

 TT1 := select(T -> nops(T) > 1,TT);

 if not(type(x,table)) then
  reason := [convert(procname,string),"x is not a table",x];  
  return false;
 fi;

 P := sort(map(sort,map(op,{indices(x)})));

 if P <> TT1 then
  reason := [convert(procname,string),"x is not indexed by the big sets in TT",P,TT1];  
  return false;
 fi;

 children := children_map(A)(TT);
 
 for T in TT1 do
  UU := children[T];
  UU1 := select(U -> (nops(U) > 1),UU);
 
  if not(`is_element/D/Fbar`(N)(UU1,UU)(x[T])) then
   reason := [convert(procname,string),"x[T] is not in D(C1,C)",x[T],N,T,reason];  
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_equal/tree_Fbar_alt` := (N::posint) -> (A::set) -> (TT) -> proc(x,y)
 local TT1,P,children,T,UU,UU1;

 TT1 := select(T -> nops(T) > 1,TT);

 children := children_map(A)(TT);
 
 for T in TT1 do
  UU := children[T];
  UU1 := select(U -> (nops(U) > 1),UU);
 
  if not(`is_equal/D/Fbar`(N)(UU1,UU)(x[T],y[T])) then
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`random_element/tree_Fbar_alt` := (N::posint) -> (A::set) -> (TT) -> proc()
 local x,TT1,children,T,UU,UU1;

 x := table();

 TT1 := select(T -> nops(T) > 1,TT);
 children := children_map(A)(TT);

 for T in TT1 do
  UU := children[T];
  UU1 := select(U -> (nops(U) > 1),UU);
  x[T] := `random_element/D/Fbar`(N)(UU1,UU)();
 od;

 return eval(x);
end;

######################################################################
# From tree_Fbar_alt to tree_Fbar

`theta/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(ty)
 local TT1,children,z,t,y,C,n,pi,w,w0,a,m,T,U;

 TT1 := select(T -> nops(T) > 1,TT);
 TT1 := sort([op(TT1)],(U1,U2) -> (nops(U1) < nops(U2)));
 children := children_map(A)(TT);
 z := table();
 t := table();
 y := table();

 for T in TT1 do 
  z[T] := table();
  t[T],y[T] := op(ty[T]);
  C := children[T];
  n := combine(simplify(sqrt(add(`norm_2/R`(N)(y[T][a])^2,a in C))));
  pi := table();
  for U in C do 
   for a in U do 
    pi[a] := U;
   od;
  od;
  w := table();
  w0 := [0$N];
  for a in T do 
   w[a] := y[T][pi[a]];
   w0 := combine(simplify(w0 +~ w[a]));
  od;
  w0 := combine(simplify(w0 /~ nops(T)));
  for a in T do 
   w[a] := combine(simplify(w[a] -~ w0));
  od;
  m := combine(simplify(sqrt(add(`norm_2/R`(N)(w[a])^2,a in T))));
  if is(m > 0) then
   for a in T do 
    w[a] := combine(simplify((n/m) *~ w[a]));
   od;
  fi;
  for U in C do 
   if nops(U) > 1 then
    for a in U do
     w[a] := combine(simplify(w[a] +~ t[T][U] *~ z[U][a]));
    od;
   fi;
  od;
  z[T] := eval(w);
 od:

 return eval(z);
end;

######################################################################
# From tree_Fbar to tree_Fbar_alt

`phi/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local TT1,children,x1,t,y0,y,ty,C,C1,n,m,T,U,a;

 TT1 := select(T -> nops(T) > 1,TT);
 children := children_map(A)(TT);
 x1 := table();
 t  := table();
 y0 := table();
 y  := table();
 ty := table();

 for T in TT1 do 
  x1[T] := `normalise_2/SW`(N)(T)(x[T]);
  t[T]  := table();
  y0[T] := table();
  y[T]  := table();
  C := children[T];
  C1 := select(U -> nops(U) > 1,C);
  n := 0;
  for U in C do 
   y0[T][U] := simplify(expand(`sum/vector_functions`(N)(U)(x1[T]) /~ nops(U)));
   n := simplify(expand(n + `norm_2/R`(N)(y0[T][U])^2));
   if nops(U) > 1 then 
    t[T][U]  := simplify(expand(sqrt(add(`norm_2/R`(N)(x1[T][a] -~ y0[T][U])^2,a in U))));
   fi;
  od;
  if is(n > 0) then
   y[T] := `normalise_2/SW`(N)(C)(y0[T]);
   m := combine(simplify(expand(rationalize(sqrt(1 - add(t[T][U]^2,U in C1))))));
   for U in C do 
    y[T][U] := combine(simplify(expand(m *~ y[T][U])));
   od;
  else
   for U in C do 
    y[T][U] := [0$N];
   od;
  fi;
  ty[T] := [eval(t[T]),eval(y[T])];
 od:

 return eval(ty);
end:
