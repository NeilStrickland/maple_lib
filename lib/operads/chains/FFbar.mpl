`is_element/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 local B,C,P,P1;
 global reason;

 P := {op(`list_elements/big_subsets`(A))};

 if not(is_table_on(P)(Q)) then
  reason := [convert(procname,string),"Q is not a table indexed by big subsets of A",eval(Q)];  
  return false;
 fi;

 for B in P do 
  if not(`is_element/SCP`(N)(B)(Q[B])) then
   reason := [convert(procname,string),"Q[B] is not in SCP(N)(B)",eval(Q[B]),N,B,reason];  
   return false;
  fi;

  P1 := {op(`list_elements/big_subsets`(B))} minus {B};

  for C in P1 do
   if not(`is_element/SCP2`(N)(B,C)([Q[B],Q[C]])) then
    reason := [convert(procname,string),"(Q[B],Q[C]) is not in SCP(N)(B,C)",
               eval(Q[B]),eval(Q[C]),N,B,C,reason];  
    return false;
   fi;
  od;
 od;

 return true;
end;

######################################################################

`is_equal/FFbar` := (N::posint) -> (A::set) -> proc(Q0,Q1)
 local B,P;
 global reason;

 P := `list_elements/big_subsets`(A);

 for B in P do 
  if not(`is_equal/SCP`(N)(B)(Q0[B],Q1[B])) then
   reason := [convert(procname,string),"Q0[B] <> Q1[B]",B,Q0[B],Q1[B],reason];  
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_leq/FFbar` := (N) -> (A) -> proc(Q0,Q1)
 local B,P;
 global reason;

 P := `list_elements/big_subsets`(A);

 for B in P do 
  if not(`is_leq/SCP`(N)(B)(Q0[B],Q1[B])) then
   reason := [convert(procname,string),"Q0[B] is not <= Q1[B]",B,Q0[B],Q1[B],reason];  
   return false;
  fi;
 od;

 return true;

end;

######################################################################

`build/FFbar` := (N::posint) -> (A::set) -> proc(RTTu)
 local R,TT,i,j,k,n,m,ij,A0,C,TT1,TTS,TTc,T,Q,Q0,D,u,v,M,L,M0,M1,RT,BS,UU,U;
 R,TT,u := op(RTTu);
 n := nops(A);
 A0 := {seq(i,i=1..n)};
 C := children_map(A0)(TT);
 TT1 := select(T -> nops(T) > 1,TT);
 TTS := sort(map(T -> sort([op(T)]),[op(TT1)]));
 Q := table():
 for T in TTS do 
  D := sort([op(C[{op(T)}])],(U,V) -> (U[1] <= V[1]));
  D := map(U -> sort([op(U)]),D);
  m := nops(D);
  v := [seq(u[max(D[i])],i=1..nops(D)-1)];
  M := [seq(i,i=1..m)];
  Q0 := `build/ICP`(N)({op(M)})([M,v]);
  L := [];
  for k from 1 to N do
   M0 := Q0[k];
   M1 := NULL;
   for ij in M0 do
    i,j := op(ij);
    M1 := M1,seq(seq([R[a],R[b]],a in D[i]),b in D[j]);
   od;
   M1 := {M1};
   L := [op(L),M1];
  od;
  RT := {seq(R[a],a in T)};
  Q[RT] := L;
 od:
 TT1 := map(op,{indices(Q)});
 BS := {op(`list_elements/big_subsets`(A))};
 TTc := BS minus TT1;
 for T in TTc do
  UU := select(U -> T minus U = {},TT1);
  m := min(map(nops,UU));
  UU := select(U -> nops(U) = m,UU);
  U := UU[1];
  Q[T] := `res/ICP`(N)(U,T)(Q[U]);
 od:
 return eval(Q);
end:

`unbuild/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 local n,R,r,i,TT,TT0,u,a,b,UU,d,U,P,k;
 n := nops(A);
 R := `totalise/FFbar/ord`(N)(A)(Q);
 r := table():
 for i from 1 to n do r[R[i]] := i; od;
 TT := `critical_tree/FFbar`(N)(A)(Q);
 TT0 := map(U -> map(a -> r[a],U),TT);
 u := NULL;
 for i from 1 to n-1 do
  a := R[i];
  b := R[i+1];
  UU := select(U -> member(a,U) and member(b,U),TT);
  d := min(map(nops,UU));
  UU := select(U -> nops(U) = d,UU);
  U := UU[1];
  P := Q[U];
  k := 1;
  while k < N and member([b,a],P[k]) do k := k+1; od;
  u := u,k; 
 od;
 u := [u];
 return [R,TT0,u];
end:

######################################################################

`is_interior/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 return `is_separated/SCP`(N)(A)(Q[N]);
end;

######################################################################

`inc/ICP/FFbar` := (N::posint) -> (A::set) -> proc(Q0)
 local TT,T,Q;
 
 Q := table();
 TT := `list_elements/big_subsets`(A);
 for T in TT do
  Q[T] := `res/ACP`(N)(A,T)(Q0);
 od;

 return eval(Q);
end:

######################################################################

`res/FFbar/ICP` := (N::posint) -> (A::set) -> proc(Q)
 if not(`is_interior/FFbar`(N)(A)(Q)) then
  return FAIL;
 fi;

 return Q[A];
end;

######################################################################
# The functions below could be made much more efficient, but for
# the moment we will stick with the most obvious approach.

`is_critical/FFbar` := (N::posint) -> (A::set) -> proc(Q,U)
 local UU,a;

 UU := `top/autorel`(U);

 for a in A minus U do
  if UU minus Q[U union {a}][N] <> {} then
   return false;
  fi;
 od;

 return true;
end;

##################################################

`critical_tree/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 select(U -> `is_critical/FFbar`(N)(A)(Q,U),
        {op(`list_elements/nonempty_subsets`(A))});
end;

##################################################

`rank/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 local TT,TT1,T;

 TT := `critical_tree/FFbar`(N)(A)(Q);
 TT1 := select(T -> nops(T) > 1,TT);
 return add(`rank/ACP`(N)(T)(Q[T])-1,T in TT1);
end;

##################################################

`totalise/FFbar/ord` := (N::posint) -> (A::set) -> proc(Q)
 local C,P,k;
 C := proc(a,b)
  option remember;
  if a = b then return true; fi;
  P := Q[{a,b}];
  for k from 1 to N do 
   if not(member([b,a],P[k])) then 
    return true;
   fi;
   if not(member([a,b],P[k])) then 
    return false;
   fi;
  od;
  return true;
 end:
 return sort([op(A)],C);
end:

##################################################

`random_element/FFbar` := (N::posint) -> (A::set) -> proc()
 local n,R,TT,u;
 
 n := nops(A);
 R := `random_element/ord`(A)();
 TT := `random_element/standard_stasheff_trees`(n)();
 u := [seq(rand(1..N)(),i=1..n-1)];
 return `build/FFbar`(N)(A)([R,TT,u]);
end:

`list_elements/FFbar` := (N::posint) -> proc(A::set)
 local n,RR,U,i,TTT;
 
 n := nops(A);
 RR := `list_elements/ord`(A);
 U := [[]];
 for i from 1 to n-1 do
  U := [seq(seq([op(u),j],j=1..N),u in U)];
 od;
 TTT := `list_elements/standard_stasheff_trees`(n);

 return([
  seq(seq(seq(
   `build/FFbar`(N)(A)([R,TT,u]),
   u in U),TT in TTT),R in RR)
 ]);
end:

`count_elements/FFbar` := (N::posint) -> (A::set) ->
 nops(A)! * N^(nops(A)-1) *
 `count_elements/standard_stasheff_trees`(nops(A)); 

`list_ordered_elements/FFbar` := (N::posint) -> proc(A::{set,list})
 local n,A0,R,U,i,TTT;
 
 n := nops(A);
 A0 := {op(A)};
 R := [op(A)];
 U := [[]];
 for i from 1 to n-1 do
  U := [seq(seq([op(u),j],j=1..N),u in U)];
 od;
 TTT := `list_elements/standard_stasheff_trees`(n);

 return([
  seq(seq(
   `build/FFbar`(N)(A)([R,TT,u]),
   u in U),TT in TTT)
 ]);
end:

`count_ordered_elements/FFbar` := (N::posint) -> (A::set) ->
 N^(nops(A)-1) *
 `count_elements/standard_stasheff_trees`(nops(A)); 

######################################################################

`eta/FFbar` := (N::posint) -> (A::set) -> `if`(nops(A) = 1,table(),FAIL);

######################################################################

`gamma/FFbar` := (N::posint) -> (A::set,B::set) -> (p) -> proc(Q,P) 
 local R,TT,T,U,M;

 R := table();
 TT := `list_elements/big_subsets`(A);
 
 for T in TT do
  U := map(a -> p[a],T);
  if nops(U) > 1 then
   M := Q[U];
   R[T] := [seq(select(u -> member([p[u[1]],p[u[2]]],M[i]),`top/autorel`(T)),i=1..N)];
  else 
   R[T] := eval(P[op(U)][T]);
  fi;
 od;

 return eval(R);
end;

######################################################################

`mu/Fbar/FFbar` := (N::posint) -> (A::set) -> proc(x)
 local Q,TT,T;
 
 Q := table();

 TT := `list_elements/big_subsets`(A);
 for T in TT do
  Q[T] := `mu/W/ACP`(N)(T)(x[T]);
 od;

 return eval(Q);
end;

######################################################################

`sigma/Fbar/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 local x,TT,T;
 
 x := table();

 TT := `list_elements/big_subsets`(A);
 for T in TT do
  x[T] := `sigma/ACP/W`(N)(T)(Q[T]);
 od;

 return eval(x);
end;

######################################################################

`describe/FFbar` := (N::posint) -> (A::set) -> proc(Q)
 local TT,TT1,T,s;
 TT := `critical_tree/FFbar`(N)(A)(Q);
 TT1 := select(T -> nops(T) > 1,TT);
 TT1 := sort([op(TT1)],(U,V) -> nops(U) >= nops(V));
 s := "";
 for T in TT1 do
  if s <> "" then s := cat(s,"\n"); fi;
  s := cat(s,`describe/ACP`(N)(T)(Q[T]));
 od:
 return s;
end: