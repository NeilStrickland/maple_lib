`is_element/cactus_trees` := (A::set) -> proc(J)
 global reason;
 local tag,B,C,E,a,j;

 tag := "is_element/cactus_trees";

 if A = {} then
  reason := [tag,"A is empty"];
  return false;
 fi;

 if not(type(J,set(set)) and map(op,J) minus A = {}) then
  reason := [tag,"J is not a set of subsets of A",J,A];
  return false;
 fi; 

 if min(op(map(nops,J))) < 2 then
  reason := [tag,"J contains a set of size < 2",J];
  return false;
 fi;

 B := {};
 C := {A[1]};
 while nops(B) < nops(C) do
  B := C;
  C := map(op,{B,map(op,select(X -> X intersect B <> {},J))});
 od;
 if C <> A then
  reason := [tag,"The graph is not connected",A,J,C];
  return false;
 fi;

 E := {seq(seq([a,j],a in j),j in J)};
 if nops(E) <> (nops(A) + nops(J) - 1) then
  reason := [tag,"The graph is not a tree",A,E];
  return false;
 fi;

return true;
end:

######################################################################

`is_leq/cactus_trees` := (A::set) -> proc(J0,J1)
 local f,G,j0,j1,jj1,P,Q,p,q,U;

 # f will be the map J0 -> J1 with j0 a subset of f(j0)
 f := table():

 # G(j1) = f^{-1}{j1}
 G := table():
 
 for j1 in J1 do G[j1] := {}; od:

 for j0 in J0 do
  jj1 := select(u -> (j0 minus u) = {},J1);
  # Assuming that J1 really is a cactus tree, the set jj1 will
  # have size 0 or 1.
  if nops(jj1) <> 1 then
   return false;
  fi;
  j1 := op(1,jj1);
  f[j0] := j1;
  G[j1] := {op(G[j1]),j0};
 od:

 for j1 in J1 do
  P := G[j1];
  p := nops(P);
  if p = 0 then return false; fi; # f should be surjective
  Q := {P[1]};
  q := 0;
  while q < nops(Q) do 
   q := nops(Q);
   U := map(op,Q);
   Q := select(j0 -> ((j0 intersect U) <> {}),P);
  od:
  if Q <> P then
   return false;
  fi;
 od;

 return true;
end:

`top/cactus_trees` := proc(A::set)
 if nops(A) > 1 then
  return {A};
 elif nops(A) = 1 then
  return {};
 else
  return FAIL;
 fi;
end:

######################################################################

`random_element/cactus_trees` := (A::set) -> proc()
 local a,b,B,J,K,k;
 
 if nops(A) = 0 then
  return FAIL;
 elif nops(A) = 1 then
  return {};
 elif nops(A) = 2 then
  return {A};
 fi;

 a := random_element_of(A);
 B := A minus {a};
 K := `random_element/cactus_trees`(B)();
 if rand(0..1)() = 0 then
  k := random_element_of(K);
  J := K minus {k} union {k union {a}};
 else
  b := random_element_of(B);
  J := K union {{a,b}};
 fi;

 return J;
end:

######################################################################

`list_elements/cactus_trees` := proc(A::set)
 option remember;
 local n,a,b,u,v,B,PP,pp,K,L,m,M,P,Q,i,k,f;

 n := nops(A);
 if n = 0 then
  return [];
 elif n = 1 then
  return [{}];
 elif n = 2 then
  return [{A}];
 fi;

 a := A[1];
 B := A minus {a};
 PP := map(pp -> [op(pp)],`list_elements/partitions`(B));
 L := NULL;
 for pp in PP do
  m := nops(pp);
  M := map(`list_elements/cactus_trees`,pp);
  P := [seq([seq(seq([K,{b}],b in pp[i]),K in M[i]),
             seq(seq([K,k],k in K),K in M[i])],i=1..m)];
  Q := [[]];
  for i from 1 to m do
   Q := [seq(seq([op(u),v],u in Q),v in P[i])]; 
  od:
  f := (q) -> {seq(op(q[i][1] minus {q[i][2]}),i=1..m),seq({a,op(q[i][2])},i=1..m)};
  L := L,op(map(f,Q));
 od:
 return [L];
end:

######################################################################

# This is A030019 in OEIS

`count_elements/cactus_trees` := proc(A::set)
 local n,i;
 n := nops(A);
 add(Stirling2(n-1, i)*n^(i-1),i=0..n-1);
end:

