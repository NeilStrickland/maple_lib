######################################################################

`is_element/stasheff_star` := (A::set) -> proc(Rt)
 local R,t,n,JJ,TT,J,u;
 global reason;

 if not(type(Rt,list) and nops(Rt) = 2) then 
  reason := [convert(procname,string),"Rt cannot be split as [R,t]",Rt];
  return false;
 fi;

 R,t := op(Rt);

 if not(`is_element/ord`(A)(R)) then
  reason := [convert(procname,string),"R is not an order on A",R,A,reason];
  return false;
 fi;

 n := nops(A);
 JJ := {seq(seq({seq(R[k],k=i..j)},j=i..n),i=1..n)};

 if not(type(t,table)) then
  reason := [convert(procname,string),"t is not a table",t];
  return false;
 fi;

 if map(op,{indices(t)}) <> JJ then
  reason := [convert(procname,string),"t is not indexed by the set of R-intervals",t,R,JJ];
  return false;
 fi;

 TT := NULL;

 for J in JJ do
  u := t[J];

  if not (`is_element/RR`(u) and u >= 0 and u <= 1) then
   reason := [convert(procname,string),"t[J] is not in the unit interval",J,t[J]];
   return false;
  fi;

  if (nops(J) = 1 and u <> 1) then
   reason := [convert(procname,string),"t[{a}] <> 1",op(J),t[J]];
   return false;
  fi;

  if (nops(J) = 1 or nops(J) = n) and u <> 1 then
   reason := [convert(procname,string),"t[A] <> 1",A,t[J]];
   return false;
  fi;

  if u > 0 then TT := TT,J; fi;
 od;

 TT := {TT};

 if not(`is_element/trees`(A)(TT)) then
  reason := [convert(procname,string),"TT is not a tree",TT,reason];
  return false;
 fi;

 return true;
end;

######################################################################

`is_equal/stasheff_star` := (A::set) -> proc(Rt1,Rt2)
 local R1,R2,t1,t2,n,JJ,J;

 R1,t1 := op(Rt1);
 R2,t2 := op(Rt2);

 if not(`is_equal/ord`(A)(R1,R2)) then
  return false;
 fi;
 
 n := nops(A);
 JJ := {seq(seq({seq(R1[k],k=i..j)},j=i..n),i=1..n)};

 for J in JJ do
  if t1[J] <> t2[J] then return false; fi;
 od;

 return true;
end:

######################################################################

`is_leq/stasheff_star` := NULL;

######################################################################
# Covariant functoriality for bijections p : A -> B.

`act/stasheff_star` := (A::set,B::set) -> (p) -> proc(Rt)
 local R,t,S,u,JJ,J,J1;

 R,t := op(Rt);
 S := map(a -> p[a],R);
 u := table();
 JJ := map(op,[indices(t)]);
 for J in JJ do 
  J1 := map(a -> p[a],J);
  u[J1] := t[J];
 od:
 return [S,eval(u)];
end:

######################################################################

`random_element/stasheff_star` := (A::set) -> proc()
 local R,t0,JJ0,J0,t,J;

 R := `random_element/ord`(A)();
 t0 := `random_element/standard_stasheff_star`(nops(A))();

 JJ0 := map(op,[indices(t0)]);
 t := table();
 for J0 in JJ0 do
  J := map(i -> R[i],J0);
  t[J] := t0[J0];
 od:

 return [R,eval(t)];
end:

######################################################################

`list_elements/stasheff_star` := NULL;
`count_elements/stasheff_star` := NULL;

######################################################################

`phi/stasheff_trees/stasheff_star` := (A::set) -> proc(RTT)
 local R,TT,n,JJ,J,t;

 R,TT := op(RTT);

 n := nops(R);
 JJ := {seq(seq({seq(R[k],k=i..j)},j=i..n),i=1..n)};
 t := table();

 for J in JJ do t[J] := 0; od;
 for J in TT do t[J] := 1; od;

 return [R,eval(t)];
end;

######################################################################

`phi/realisation/stasheff_trees/stasheff_star` := (A::set) -> proc(x)
 local y,C,R,n,JJ,J,RTT,t,TT,z;

 y := table();
 C := map(op,[indices(x)]);
 R := C[1][1];
 n := nops(A);
 JJ := {seq(seq({seq(R[k],k=i..j)},j=i..n),i=1..n)};

 for J in JJ do y[J] := 0; od;
 
 for RTT in C do
  t := x[RTT];
  TT := RTT[2];
  z := `phi/stasheff_trees/stasheff_star`(A)(TT);
  for J in JJ do y[J] := y[J] + t * z[J]; od;
 od;

 return eval(y);
end:

######################################################################

`phi/stasheff_star/ord_simplex_interior` := (A::set) -> proc(Rt)
 local R,t,JJ,JS,Ja,J,lambda,mu,a,children;

 R,t := op(Rt);
 JJ := select(J -> t[J] > 0, map(op,{indices(t)}));
 children := `children_map`(A)(JJ);
 JS := sort([op(JJ),(U,V) -> nops(U) < nops(V)]);

 lambda := table();
 for J in JS do
  if nops(J) = 1 then
   lambda[J] := 1;
  else
   lambda[J] := add(lambda[K]^(1-t[K]),K in children[J]);
  fi;
 od;

 mu := table();
 for a in A do
  Ja := select(J -> member(a,J),JJ);
  mu[a] := mul(lambda[J]^(-t[J]),J in Ja);
 od;

 return [R,eval(mu)];
end;

######################################################################

`phi/stasheff_star/one_cubes_prime` := (A::set) -> proc(Rt)
 `phi/ord_simplex_interior/one_cubes_prime`(A)(
  `phi/stasheff_star/ord_simplex_interior`(A)(Rt));
end;

######################################################################

`proj/stasheff_star/ord` := (A::set) -> (Rt) -> Rt[1];

######################################################################

`describe/stasheff_star` := (A::set) -> proc(Rt)
 local R,t,n,r,i,TT;
 R,t := op(Rt);
 n := nops(A);
 r := table();
 for i from 1 to n do r[R[i]] := i; od:

 TT := map(op,[indices(t)]);
 TT := select(J -> (t[J] > 0 and nops(J) > 1),TT);
 TT := map(J -> [op(J)],TT);
 TT := map(sort,TT,(a,b) -> (r[a] < r[b]));
 TT := sort(TT,(J0,J1) -> (
        (nops(J0) < nops(J1)) or 
        ((nops(J0) = nops(J1)) and (r[J0[1]] < r[J1[1]]))));
 return sprintf("%A",map(J -> (J=t[{op(J)}]),TT));
end;