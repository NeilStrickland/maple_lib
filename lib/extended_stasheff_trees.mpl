# An extended Stasheff tree is like a standard Stasheff tree, except that we
# are allowed vertices with only one child, which we call nodes.  By deleting
# the nodes we obtain a standard Stasheff tree TT.  For each T in TT we let
# m[T] be the number of nodes lying just below T.  The function m : TT -> N
# is arbitrary and determines the original tree.  We will write n for the
# number of leaves (which are never nodes) and k for the number of vertices
# that are neither leaves nor the root.  Note that the root may or may not
# be a node.
#
# We represent an extended Stasheff tree as the set of pairs [T,m[T]].

`is_element/extended_stasheff_trees` := (n::posint,k::nonnegint) -> proc(UU)
 global reason;
 local TT,T,U,m,kk;

 if not (type(UU,set)) then
  reason := ["is_element/extended_stasheff_trees","UU is not a set",UU];
  return false;
 fi;

 kk := 0;
 TT := NULL;
 
 for U in UU do
  if not(type(U,list) and nops(U) = 2) then
   reason := ["is_element/extended_stasheff_trees","U is not a list of length 2",U,UU];
   return false;
  fi;
  T,m := op(U);
  if not(type(m,nonnegint)) then
   reason := ["is_element/extended_stasheff_trees","m is not a natural number",m,U,UU];
   return false;
  fi;
  kk := kk + m + 1;
  TT := TT,T;
 od:

 TT := {TT};

 if not(`is_element/standard_stasheff_trees`(n)(TT)) then
  reason := ["is_element/extended_stasheff_trees","TT is not a standard Stasheff tree",TT,reason];  
  return false;
 fi;

 kk := kk - n - 1;

 if kk <> k then
  reason := ["is_element/extended_stasheff_trees","wrong number of internal vertices",kk,k,UU];  
  return false;
 fi;

 return true;
end:

`is_equal/extended_stasheff_trees` := (n::posint,k::nonnegint) -> proc(UU0,UU1)
 return evalb(UU0 = UU1);
end:

`is_leq/extended_stasheff_trees` := NULL:

`list_elements/extended_stasheff_trees` := proc(n::posint,k::nonnegint)
 local TTT,TT,T,P,p,i,j,UU,L,u;

 TTT := `list_elements/standard_stasheff_trees`(n);

 L := NULL;
 for TT in TTT do
  p := nops(TT);
  j := k - (p - n - 1);
  if j >= 0 then
   P := `list_elements/nat_partitions`(j,p);
   for u in P do
    UU := {seq([TT[i],u[i]],i=1..p)};
    L := L,UU;
   od:
  fi;
 od:
 return [L];
end:

`random_element/extended_stasheff_trees` := (n::posint,k::nonnegint) -> proc()
 local TT,m,P,UU;

 TT := `random_element/standard_stasheff_trees`(n)();
 while (nops(TT) > n + k + 1) do 
  TT := `random_element/standard_stasheff_trees`(n)();
 od;
 m := nops(TT);
 
 P := `random_element/nat_partitions`(n+k+1-m,m)();
 UU := {seq([TT[i],P[i]],i=1..m)};
 return UU;
end:

`count_elements/extended_stasheff_trees` := (n::posint,k::nonnegint) ->
 binomial(n+k,n)*binomial(n+k,n-1)/(n+k);

`node_count/extended_stasheff_trees` := proc(UU)
 return add(U[2],U in UU);
end:

# This removes the nodes from an extended Stasheff tree to give an
# ordinary Stasheff tree.

`strip/extended_stasheff_tree` := proc(UU)
 map(U -> U[1],UU);
end:

`narayana_path/extended_stasheff_tree` := proc(UU)
 local TT,n,CC,C,m,u,l,UU0;

 TT := `strip/extended_stasheff_tree`(UU);
 n := max(op(map(op,TT)));
 CC := `root_children/standard_stasheff_tree`(n)(TT);

 # Number of nodes under the root
 m := select(U -> nops(U[1])=n,UU)[1][2];
 
 u := 1$m;

 for C in CC do
  l := min(op(C));
  UU0 := select(U -> U[1] minus C = {},UU);
  UU0 := map(U -> [U[1] -~ (l-1),U[2]],UU0);
  u := u,1,op(`narayana_path/extended_stasheff_tree`(UU0)),-1;
 od:
 
 u := u,(-1)$m;
 u := [u];
 return u;
end:

# This takes a pair of extended Stasheff trees and adds an edge
# joining the roots, taking the root of the first one as the root
# of the combined tree.
`splice/extended_stasheff_tree` := (n0,k0) -> (n1,k1) -> proc(UU0,UU1)
 local UU2,R2,m;

 UU2 := map(U -> [U[1] +~ n0,U[2]],UU1);
 R2 := select(U -> nops(U[1]) = n1,UU2)[1];
 m := R2[2];
 if m > 0 then
  UU2 := UU2 minus {R2} union {[R2[1],m-1]};
 else
  UU2 := UU2 minus {R2};
 fi;
 return {op(UU0),op(UU2),[{seq(i,i=1..n0+n1)},0]};
end:

# This adds a new left-most leaf and connects it to the root.
# This is essentially the same as splice(ZZ,UU), where ZZ is
# the 0-corolla, which we have not allowed as an extended
# Stasheff tree.  However, it would be a bad idea to allow ZZ
# here, because sprouting adds a leaf, which is inconsistent with
# the usual effect of splicing on the leaf count.

`sprout/extended_stasheff_tree` := (n,k) -> proc(UU)
 local UU2,R2,m;

 UU2 := map(U -> [U[1] +~ 1,U[2]],UU);
 R2 := select(U -> nops(U[1]) = n,UU2)[1];
 m := R2[2];
 if m > 0 then
  UU2 := UU2 minus {R2} union {[R2[1],m-1]};
 else
  UU2 := UU2 minus {R2};
 fi;
 return {[{1},0],op(UU2),[{seq(i,i=1..n+1)},0]};
end:

# This adds an extra node at the bottom
# This is essentially the same as splice(UU,ZZ), where ZZ is
# the 0-corolla, which we have not allowed as an extended
# Stasheff tree.
`grow/extended_stasheff_tree` := (n::posint,k::nonnegint) -> proc(UU)
 local R;
 R := select(U -> nops(U[1]) = n,UU)[1];
 return (UU minus {R}) union {[R[1],R[2]+1]};
end:

