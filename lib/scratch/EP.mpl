`is_element/EP/Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 global reason;
 local TT1,C,P,Q,T;

 TT1 := `big_sets/trees`(TT);
 if not is_table_on(TT1)(x) then
  reason := [convert(procname,string),"x is not a table on TT1",x,TT1];
  return false;
 fi;

 C := children_map(TT);
 for T in TT1 do
  Q := C[T];
  P := select(U -> nops(U) > 1,Q);
  if not `is_element/D/Fbar`(N)(P,Q)(x[T]) then
   reason := [convert(procname,string),"x[T] is not in D/Fbar(N)(P,Q)",x[T],P,Q,reason];
   return false;
  fi;
 od;

 return true;
end:

######################################################################

`is_equal/EP/Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(x,y)
 local TT1,C,P,Q,T,U;

 TT1 := `big_sets/trees`(TT);

 C := children_map(TT);
 for T in TT1 do
  Q := C[T];
  P := select(U -> nops(U) > 1,Q);
  if not `is_equal/E/Fbar`(N)(P,Q)(x[T],y[T]) then
   return false;
  fi;
 od;

 return true;
end:

######################################################################

`theta/EP/tree_Fbar_alt` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local TT1,C,P,Q,T,U,y;

 TT1 := `big_sets/trees`(TT);

 y := table();
 C := children_map(TT);
 for T in TT1 do
  Q := C[T];
  P := select(U -> nops(U) > 1,Q);
  y[T] := `theta/E/Fbar`(N)(P,Q)(x[T],y[T]);
 od;

 return eval(y);
end:

######################################################################

`phi/EP/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(tpqx)
 local s,t,p,q,x,y,z,t0,x0,C,P,TT1,UU,VV,T,U,V,u,y0,n0,r;
 t := table();
 p := table();
 q := table();
 x := table();

 C := children_map(TT);
 P := parent_map(TT);
 TT1 := `big_sets/trees`(TT);

 for T in TT1 do 
  t0[T],p[T],q[T],x0[T] := op(tpqx[T]);
  for U in C[T] do
   x[U] := x0[T][U];
   if nops(U) > 1 then t[U] := t0[T][U]; fi;
  od;
 od; 

 s := table();

 for T in TT1 do
  UU := select(U -> (U minus T = {}),TT1);
  for U in UU do
   VV := select(V -> (U minus V = {}),UU);
   VV := sort([op(VV)],(V1,V2) -> evalb(nops(V1) < nops(V2)));
   r := nops(VV) - 1;
   s[T,U] := q[U] * mul(p[VV[i]],i=2..r+1) * mul(t[V[i]],i=1..r); 
  od;
 od;

 y := table();
 for T in TT do
  y[T] := table();
  for u in A do y[T][u] := 0; od;
  for U in C[T] do
   for u in U do
    y[T][u] := x[T][U];
   od;
  od;
  y0 := `sum/vector_function`(N)(T)(y[T]) /~ nops(T);
  for u in T do y[T][u] := y[T][u] -~ y0; od;
  n0 := `norm/vector_functions`(y[T]);
  for u in T do y[T][u] := y[T][u] /~ n0; od;
 od;

 z := table();
 for T in TT1 do
  z[T] := table();
  for u in T do z[T][u] := [0$N]; od:

  UU := select(U -> (U minus T = {}),TT1);
  for U in UU do
   for u in U do
    z[T][u] := z[T][u] +~ s[T,U] *~ y[U][u];
   od;
  od;
 od;

 return eval(z);
end:
