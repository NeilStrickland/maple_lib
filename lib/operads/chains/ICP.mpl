######################################################################

`is_element/ICP` := (N::posint) -> (A::set) -> proc(Q)
 local i,U,V;

 global reason;

 if not `is_element/ACP`(N)(A)(Q) then
  reason := [convert(procname,string),"Q in ACP(N)(A)",reason];
  return false;
 fi;

 if not `is_separated/preord`(A)(Q[N]) then
  reason := [convert(procname,string),"Q[N] is not separated",Q[N]];
  return false;
 fi;

 return true;
end:

`is_equal/ICP` := (N::posint) -> (A::set) -> proc(Q1,Q2)
 global reason;

 if Q1 <> Q2 then
  reason := [convert(procname,string),"Q1 <> Q2",Q1,Q2];
  return false;
 fi;

 return true;
end:

`is_leq/ICP` := (N::posint) -> (A::set) -> proc(Q1,Q2)
 local i;

 for i from 1 to N do 
  if Q2[i] minus Q1[i] <> {} then
   return false;
  fi;
 od;

 return true;
end:

######################################################################

`random_element/ICP` := (N::posint) -> (A::set) -> proc()
 local i,j,n,pi,Q,R,S,B,C;

 if nops(A) = 0 then
  return FAIL;
 fi;

 R := `random_element/total_preord`(A)();
 Q := [R];
 for i from 2 to N do 
  pi := `block_partition/preord`(A)(R);
  R := {};
  for B in pi do
   if i < N then
    S := `random_element/total_preord`(B)();
   else
    C := `random_element/ord`(B)();
    n := nops(C);
    S := {seq(seq([C[i],C[j]],j=i..n),i=1..n)};
   fi;
    
   R := R union S;
  od;
  Q := [op(Q),R];
 od;

 return Q;
end:

######################################################################

`build/ICP` := (N::posint) -> (A::set) -> proc(Ru)
 local R,u,n,i,j,p,a,b,aa,bb,Q;
 R,u := op(Ru);
 n := nops(A);
 aa := table():
 bb := table():
 for i from 1 to n do
  for p from 1 to N do
   a := i;
   while a > 1 and u[a-1] > p do a := a - 1; od;
   aa[i,p] := a;
   b := i;
   while b < n and u[b] >= p do b := b + 1; od;
   bb[i,p] := b;
  od:
 od:
 Q := [seq(
  {seq(seq([R[i],R[j]],j=aa[i,p]..bb[i,p]),i=1..n)}
 ,p=1..N)];

 return Q;
end:

######################################################################

`list_elements/ICP` := (N::posint) -> proc(A::set)
 local U,u,n,i,j,RR,R;
 
 U := [[]];
 n := nops(A);
 for i from 1 to n-1 do
  U := [seq(seq([op(u),j],j=1..N),u in U)];
 od:

 RR := `list_elements/ord`(A);

 [seq(seq(`build/ICP`(N)(A)([R,u]),u in U),R in RR)];
end:

`count_elements/ICP` := (N::posint) -> (A::set) ->
 nops(A)! * N^(nops(A) - 1);

######################################################################

`list_ordered_elements/ICP` := (N::posint) -> proc(A::{set,list})
 local U,u,n,i,j,R,A0;
 
 U := [[]];
 n := nops(A);
 for i from 1 to n-1 do
  U := [seq(seq([op(u),j],j=1..N),u in U)];
 od:

 R := [op(A)];
 A0 := {op(A)};

 [seq(`build/ICP`(N)(A0)([R,u]),u in U)];
end:

`count_ordered_elements/ICP` := (N::posint) -> (A::set) ->
 N^(nops(A) - 1);

######################################################################

# Note that we omit the rank of Q[N], because it is always equal to N here.

`rank_vector/ICP` := (N) -> (A) -> proc(Q)
 local i;
 return [seq(`rank/preord`(A)(Q[i])-1,i=1..N-1)];
end;

`rank/ICP` := (N) -> (A) -> proc(Q)
 return `+`(op(`rank_vector/ICP`(N)(A)(Q)));
end;

######################################################################

`phi/SEM/ICP` := (N::posint) -> (A::set) -> proc(eta)
 local A2,a,b,i;

 A2 := {seq(seq([a,b],b in A),a in A)};

 return [seq(select(ab -> `is_preceq/E`(N)(eta[op(ab)],epsilon^i),A2),i=0..N-1)];
end;

`psi/ICP/SEM` := (N::posint) -> (A::set) -> proc(Q)
 local eta,a,b,i;

 eta := table();
 for a in A do
  for b in A do 
   if a = b then 
    eta[a,b] := 0;
   else
    i := 1;
    while (i < N and member([a,b],Q[i]) and member([b,a],Q[i])) do 
     i := i+1;
    od;
    if member([a,b],Q[i]) then
     eta[a,b] :=  epsilon^(i-1);
    else 
     eta[a,b] := -epsilon^(i-1);
    fi;
   fi;
  od;
 od;

 return eval(eta);
end:

######################################################################

`totalise/ICP/ord` := (N::posint) -> (A::set) -> proc(Q)
 local R,T,r,i,a;

 R := `id/autorel`(A);
 for i from 1 to N do
  R := R union (Q[i] minus `op/autorel`(A)(Q[i]));
 od:

 T := table():
 for a in A do
  r := nops(select(x -> member([x,a],R),A));
  T[r] := a;
 od:

 return [seq(T[i],i=1..nops(A))];
end:
 
`res/ICP` := (N::posint) -> (A::set,B::set) -> proc(Q)
 local BB;

 BB := `top/autorel`(B);

 return(map(`intersect`,Q,BB));
end;

######################################################################

`is_fibre_sphere/ICP` := (N::posint) -> (A::set) -> (a,b,Q) -> proc(P)
 local B,i,U,V,L;

 if not(member(a,A)) then error("a not in A"); fi;
 B := A minus {a};

 if not(`is_equal/ICP`(N)(B)(`res/ICP`(N)(A,B)(P),Q)) then
  return false;
 fi;

 i := 1;
 while i < N and member([a,b],P[i]) and member([b,a],P[i]) do
  i := i+1;
 od;

 U := select(x -> member([x,a],P[i]),B);
 V := select(x -> member([a,x],P[i]),B);

 if U intersect V <> {} then return false; fi;
 if member(b,U) then
  L := select(x -> not(member([x,b],P[i])),U);
  if L <> {} then return false; fi;
 fi;
 if member(b,V) then
  L := select(x -> not(member([b,x],P[i])),V);
  if L <> {} then return false; fi;
 fi;

 return true;
end;

######################################################################
# Each of the subsets S_b(Q) is isomorphic to ICP_N({a,b})

`f/fibre_sphere/ICP` := (N::posint) -> (A::set) -> (a,b,Q) -> proc(R)
 local i,e;

 i := 1;
 while member([a,b],R[i]) and member([b,a],R[i]) do
  i := i+1;
 od;
 if member([a,b],R[i]) then
  e := -1;
 else
  e := +1;
 fi;

 return `f_alt/fibre_sphere/ICP`(N)(A)(a,b,Q)([i,e]);
end:

`f_alt/fibre_sphere/ICP` := (N::posint) -> (A::set) -> (a,b,Q) -> proc(ie)
 local i,e,PT,j,x,L,U;

 i,e := op(ie);
 
 PT := table();
 for j from 1 to i-1 do
  PT[j] := {[a,a]} union Q[j];
  for x in Q[j] do
   if x[1] = b then PT[j] := {op(PT[j]),[a,x[2]]}; fi;
   if x[2] = b then PT[j] := {op(PT[j]),[x[1],a]}; fi;
  od;
 od;
 PT[i] := Q[i] union {[a,a]};
 L := select(x -> member([x,b],Q[i]),A);
 U := select(x -> member([b,x],Q[i]),A);
 if e = -1 then
  L := L minus U;
 else 
  U := U minus L;
 fi;
 PT[i] := PT[i] union {seq([x,a],x in L)}
                union {seq([a,x],x in U)};
 for j from i+1 to N do
  PT[j] := Q[j] union {[a,a]};
 od;

 return [seq(PT[j],j=1..N)];
end:

`g/fibre_sphere/ICP` := (N::posint) -> (A::set) -> (a,b,Q) -> proc(P)
 if not(`is_fibre_sphere/ICP`(N)(A)(a,b,Q)(P)) then
  return FAIL;
 fi;
 return `res/ICP`(N)(A,{a,b})(P);
end:

`g_alt/fibre_sphere/ICP` := (N::posint) -> (A::set) -> (a,b,Q) -> proc(P)
 local R,i,e;
 
 R := `g/fibre_sphere/ICP`(N)(A)(a,b,Q)(P);
 if R = FAIL then return FAIL; fi;
 i := 1;
 while member([a,b],R[i]) and member([b,a],R[i]) do
  i := i+1;
 od;
 if member([a,b],R[i]) then
  e := -1;
 else
  e := +1;
 fi;
 return [i,e];
end:

######################################################################
# This function provides a point of intesection between
# S_b(Q) and S_b1(Q), where b1 is the successor of b in the total
# order induced by Q.

`m/fibre_sphere/ICP` := (N::posint) -> (A::set) -> proc(a,b,Q)
 local B,L,n,r,b1,i,R;

 B := A minus {a};
 L := `totalise/ICP/ord`(N)(B)(Q);
 n := nops(B);
 r := table();
 for i from 1 to n do
  r[L[i]] := i;
 od;
 if not(r[b] < n) then
  return FAIL;
 fi;
 b1 := L[r[b]+1];
 i := 0;
 while i < N and member([b1,b],Q[i+1]) do
  i := i+1;
 od;
 R := [{[a,a],[a,b],[b,a],[b,b]}$i,
       {[a,a],[b,a],[b,b]},
       {[a,a],[b,b]}$(N-i-1)];
 return `f/fibre_sphere/ICP`(N)(A)(a,b,Q)(R);
end:

######################################################################

`bump/ICP` := (N::posint) -> (A::set) -> proc(Q)
 local r,n,i,j,R,E,Q1;

 r := `rank_vector/ICP`(N)(A)(Q);
 n := nops(A);
 i := N-1;
 while i > 0 and r[i] = n-1 do 
  i := i - 1;
 od;
 if i = 0 then
  return FAIL;
 fi;
 R := `bump/striped_preord`(A)(Q[i]);
 E := R intersect `op/autorel`(A)(R);
 Q1 := [seq(Q[j],j=1..i-1),
        R,
        seq(Q[j] intersect E,j=i+1..N)];
 return Q1;
end:

######################################################################

`describe/ICP` := eval(`describe/ACP`):

