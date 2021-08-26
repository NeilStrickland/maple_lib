######################################################################

`is_element/partord` := (A::set) -> proc(R)
 global reason;

 if not `is_element/autorel`(A)(R) then
  reason := ["is_element/partord","R is not a relation on A",R,A,reason];
  return false;
 fi;

 if not(`is_reflexive/autorel`(A)(R)) then
  reason := ["is_element/partord","R is not reflexive",R];
  return false;
 fi;
 
 if not(`is_transitive/autorel`(A)(R)) then
  reason := ["is_element/partord","R is not transitive",R];
  return false;
 fi;
 
 if not(`is_separated/autorel`(A)(R)) then
  reason := ["is_element/partord","R is not separated",R];
  return false;
 fi;
 
 return true;
end;

######################################################################

`is_equal/partord`     := eval(`is_equal/autorel`);
`is_leq/partord`       := eval(`is_leq/autorel`);
`is_separated/partord` := eval(`is_separated/autorel`);

######################################################################

`op/partord` := eval(`op/autorel`);

######################################################################

`random_element/partord` := (A::set) -> proc()
 local M,B,E,RB,RA,DS,xy,x,y,d,m,a,e;
 if nops(A) <= 1 then return {seq([a,a],a in A)}; fi;

 M := `random_element/nonempty_subsets`(A)();
 B := A minus M;
 RB := `random_element/partord`(B)();
 DS := `list_elements/subsets`(B);
 for xy in RB do
  x,y := op(xy);
  if x <> y then 
   DS := select(S -> (member(x,S) or not(member(y,S))),DS);
  fi;
 od;
 d := nops(DS);
 RA := RB union {seq([m,m],m in M)};
 for m in M do
  E := DS[rand(1..d)()];
  RA := RA union {seq([e,m],e in E)};
 od;

 return RA;
end:

######################################################################

`top_element/partord` := (A) -> proc(R)
 local n,a,U;
 n := nops(A);
 for a in A do
  U := select(e -> e[2] = a,R);
  if nops(U) = n then 
   return a;
  fi;
 od:

 return FAIL;
end:

######################################################################

`bottom_element/partord` := (A) -> proc(R)
 local n,a,U;
 n := nops(A);
 for a in A do
  U := select(e -> e[1] = a,R);
  if nops(U) = n then 
   return a;
  fi;
 od:

 return FAIL;
end:

######################################################################

`rank_table/partord` := (A::set) -> proc(R)
 local pi,pi0,a,b,r,k,B;
 
 r := table():
 for a in A do
  r[a] := nops(select(x -> member([x,a],R),A)) - 1;
 od;

 return eval(r);
end;

######################################################################

`hasse_diagram/partord` := (A::set) -> proc(R)
 local R1,R2;
 R1 := R minus `id/autorel`(A);
 R2 := `o/autorel`(A)(R1,R1);
 return R1 minus R2;
end:

######################################################################

`maximal_chains/partord` := (A::set) -> proc(R)
 local H,LC,UC,a,C,C0,extra,c,u;

 H := `hasse_diagram/partord`(A)(R);
 LC := table():
 UC := table():
 for a in A do
  LC[a] := map(e -> e[1],select(e -> e[2] = a,H));
  UC[a] := map(e -> e[2],select(e -> e[1] = a,H));
 od:
 
 C := map(a -> [a],select(a -> LC[a] = {},A));
 extra := true;
 while extra do
  extra := false;
  C0 := C;
  C := NULL;
  for c in C0 do
   u := UC[c[-1]];
   if u = {} then
    C := C,c;
   else
    C := C,seq([op(c),a],a in u);
    extra := true;
   fi;
  od:
  C := {C};
 od;

 return C;
end:

######################################################################

`partord_is_leq` := (A::set) -> (R) -> (a,b) -> member([a,b],R);

######################################################################

`partord_is_equiv` := (A::set) -> (R) -> (a,b) ->
  member([a,b],R) and member([b,a],R);

######################################################################

`partord_is_less` := (A::set) -> (R) -> (a,b) ->
  member([a,b],R) and not(member([b,a],R));

######################################################################
# Returns [A0,R0] where A0 is of the form {1,...,n} and
# (A0,R0) is isomorphic to (A,R).

`skeleton/partord` := (A::set) -> proc(R)
 local n,i,A0,Ai,R0;
 n := nops(A);
 A0 := {seq(i,i=1..n)};
 Ai := table():
 for i from 1 to n do Ai[A[i]] := i; od;
 R0 := map(u -> [Ai[u[1]],Ai[u[2]]],R);
 return [A0,R0];
end:

######################################################################

`partord/from_comparator` := (A::set) -> proc(C)
 local R,a,b;
 
 R := {seq(seq([a,b],b in A),a in A)};
 R := select(ab -> C(op(ab)),R);

 return [A,R];
end:

######################################################################

`skeleton/partord/from_comparator` := (A::{set,list}) -> proc(C)
 local n,i,j,A0,R0;

 n := nops(A);
 A0 := {seq(i,i=1..n)};
 R0 := {seq(seq([i,j],j = 1..n),i = 1..n)};
 R0 := select(ij -> C(A[ij[1]],A[ij[2]]),R0);

 return [A0,R0];
end:

######################################################################

`homology/partord` := (A::set) -> proc(R,p::nonnegint := 0)
 local U,C,Cn,Ci,dM,rdM,BN,H,c,c1,d,d_max,a,i,i1,j,k,t;

 U := table():
 for a in A do
  U[a] := select(b -> (b <> a and member([a,b],R)),A):
 od:
 C[0] := [seq(chain(a),a in A)]:
 d := 0;
 while C[d] <> [] do
  d := d+1;
  C[d] := [seq(seq(chain(op(c),a),a in U[op(d,c)]),c in C[d-1])]:
 od:
 d_max := d - 1;
 for d from 0 to d_max do 
  Cn[d] := nops(C[d]):
  Ci[d] := table():
  for i from 1 to nops(C[d]) do
   Ci[d][C[d][i]] := i;
  od:
 od:

 dM := table():
 rdM := table():
 rdM[0] := 0;
 rdM[d_max+1] := 0;
 
 for d from 1 to d_max do
  dM[d] := Matrix(Cn[d-1],Cn[d]);
  for i from 1 to Cn[d] do
   c := [op(C[d][i])];
   for j from 0 to d do
    c1 := chain(seq(c[k+1],k=0..j-1),seq(c[k+1],k=j+1..d));
    i1 := Ci[d-1][c1];
    dM[d][i1,i] := (-1)^j;
   od:
  od:
  if p = 0 then 
   rdM[d] := LinearAlgebra[Rank](dM[d]);
  else
   rdM[d] := LinearAlgebra[Modular][Rank](p,dM[d]);
  fi;
 od:

 BN := table():
 for d from 0 to d_max do
  BN[d] := Cn[d] - rdM[d] - rdM[d+1]; 
 od:
 
 H := table():
 H["characteristic"] := p;
 H["dim"] := d_max;
 H["chains"] := eval(C);
 H["chain_index"] := eval(Ci);
 H["differential_matrix"] := eval(dM);
 H["chain_number"] := eval(Cn);
 H["betti_number"] := eval(BN):
 H["poincare_series"] := unapply(add(BN[i]*t^i,i=0..d_max),t);
 H["euler_characteristic"] := add((-1)^d * BN[d],d = 0..d_max):
 
 return eval(H):
end:

######################################################################

`simplex/partord` := proc(n)
 local i,j;
 return [{seq(i,i=0..n)},{seq(seq([i,j],j=i..n),i=0..n)}];
end:

`crown/partord` := proc(n)
 local A,R,i;
 A := {seq(i,i=1..2*n)};
 R := {seq([i,i],i=1..2*n),
       seq([2*i-1,2*i],i=1..n),
       seq([2*i+1,2*i],i=1..n-1),
       [1,2*n]};
 return [A,R];
end:

`saw/partord` := proc(n)
 local A,R,i;
 A := {seq(i,i=1..n)};
 R := {seq([i,i],i=1..n),
       seq([2*i-1,2*i],i=1..floor(n/2)),
       seq([2*i+1,2*i],i=1..floor((n-1)/2))};
 return [A,R];
end:

`diamond/partord` := proc(n)
 local A,R,i,j;

 A := {seq(i,i=1..2*n)};
 R := {seq([i,i],i=1..2*n),
       seq(seq([2*i-1,j],j=2*i+1..2*n),i=1..n),
       seq(seq([2*i  ,j],j=2*i+1..2*n),i=1..n)};
 return [A,R];
end: