######################################################################
# Fbar(N)(A) is the Fulton-MacPherson compactification of F(N)(A),
# defined in terms of coherent families as in the LaTeX document.

`is_element/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local TT1,B,C,P,Q,T,U;
 global reason;

 if not(type(x,table)) then
  reason := [convert(procname,string),"x is not a table",x];  
  return false;
 fi;

 P := sort(map(sort,map(op,{indices(x)})));
 TT1 := select(T -> nops(T) > 1,TT);

 if P <> TT1 then
  reason := [convert(procname,string),"x is not indexed by the big sets in TT",P,TT1];  
  return false;
 fi;

 C := children_map(A)(TT);
 
 for T in P do 
  if not(`is_element/SW`(N)(T)(x[T])) then
   reason := [convert(procname,string),"x[T] is not in SW(N)(T)",eval(x[T]),N,T,reason];  
   return false;
  fi;

  for U in C[T] do  
   if nops(U) > 1 and not(`is_element/SWW`(N)(T,U)([x[T],x[U]])) then
    reason := [convert(procname,string),"(x[T],x[U]) is not in SWW(N)(T,U)",eval(x[T]),eval(x[U]),N,T,U,reason];  
    return false;
   fi;
  od;
 od;

 return true;
end;

######################################################################

`random_element/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc()
 local TT1,children,x,C,U,m,c,a,T;
 
 TT1 := select(T -> nops(T) > 1,TT);
 children := children_map(A)(TT);
 TT1 := sort([op(TT1)],(T,U) -> nops(T) < nops(U));

 x := table();

 for T in TT1 do
  x[T] := `random_element/vector_functions`(N)(T)();
  C := select(U -> nops(U) > 1,children[T]);
  for U in C do
   m := rand(0..6)()/rand(1..10)();
   c := `random_element/R`(N)();
   for a in U do
    x[T][a] := m *~ x[U][a] +~ c;
   od;
  od;
 od;

 return eval(x);
end;

######################################################################

`normalise/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local x0,T,P;

 x0 := table();
 P := select(T -> nops(T) > 1,TT);

 for T in P do x0[T] := `normalise/SW`(N)(T)(x[T]); od;
 return eval(x0);
end;

######################################################################

`bottom_normalise/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local x0,T,P;

 x0 := table();
 P := select(T -> nops(T) > 1,TT);

 for T in P do x0[T] := `bottom_normalise/SW`(N)(T)(x[T]); od;
 return eval(x0);
end;

######################################################################

`is_equal/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x,y)
 local T,P;
 global reason;

 P := select(T -> nops(T) > 1,TT);

 for T in P do 
  if not(`is_equal/SW`(N)(T)(x[T],y[T])) then
   reason := [convert(procname,string),"x[T] <> y[T]",T,x[T],y[T],reason];  
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`dist/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x,y)
 local T,TT1,d;
 global reason;

 TT1 := select(T -> nops(T) > 1,TT);

 d := 0;
 
 for T in TT1 do
  d := d + `dist/SW`(N)(T)(x[T],y[T]); 
 od;

 return d;
end;

######################################################################

`is_leq/tree_Fbar` := NULL;

######################################################################

`is_interior/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local V;

 V := map(a -> x[A][a],A);
 return evalb(nops(V) = nops(A));
end;

######################################################################

`inc/F/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(u)
 local x,P,T,t;
 
 x := table();
 P := select(T -> nops(T) > 1,TT);
 for T in P do
  x[T] := table();
  for t in T do
   x[T][t] := u[t];
  od;
 od;

 return eval(x);
end:

######################################################################

`res/tree_Fbar/F` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 if not(`is_interior/tree_Fbar`(N)(A)(TT)(x)) then
  return FAIL;
 fi;

 return x[A];
end;

######################################################################

`res/Fbar/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local TT1,y,T;

 TT1 := select(T -> nops(T) > 1,TT);

 y := table():
 for T in TT1 do y[T] := eval(x[T]); od;

 return eval(y);
end:

######################################################################

`ext/tree_Fbar/Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local TT1,UU,TU,T,U,m,v,ok,a,y;

 TT1 := select(T -> nops(T) > 1,TT);
 UU := `list_elements/big_subsets`(A);
 
 for U in UU do 
  TU := select(T -> U minus T = {},TT1);
  m := min(op(map(nops,TU)));
  TU := select(U -> nops(U) = m,TU);
  T := TU[1];
  y[U] := table();
  v := x[T][U[1]];
  ok := false;
  for a in U do
   y[U][a] := x[T][a];
   if not(`is_equal/R`(N)(x[T][a],v)) then
    ok := true;
   fi;
  od:

  if not(ok) then return FAIL; fi;
 od;

 return eval(y);
end:

######################################################################

`perturb/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x,epsilon)
 local UU,n,y,i,a,f;
 
 UU := sort([op(TT)],(T,U) -> nops(T) > nops(U));
 UU := select(U -> nops(U) > 1,UU);
 n := nops(UU);
 y := table();
 for i from 1 to n do
  y[i] := `normalise/SW`(N)(UU[i])(x[UU[i]]);
  for a in A minus UU[i] do
   y[i][a] := [0$N];
  od;
 od:
 f := table():
 for a in A do
  f[a] := [0$N];
  for i from 1 to n do
   f[a] := combine(simplify(expand(f[a] +~ epsilon^(i-1) *~ y[i][a])));
  od:
 od:

 return `res/Fbar/tree_Fbar`(N)(A)(TT)(`inc/F/Fbar`(N)(A)(f));
end:

######################################################################

`list_elements/tree_Fbar` := NULL;
`count_elements/tree_Fbar` := NULL;

