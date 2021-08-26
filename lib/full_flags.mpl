# A full flag of subspaces in (Z/p)^d is represented by a list
# [w[1],...,w[d]] where the subspace of dimension i is
# spanned by [w[1],...,w[i]] and the last nonzero entry in
# w[i] is a 1 in position h[i] say, and w[i+1],...,w[d]
# all have zero in position h[i].


`count_elements/vectors` := (p,d) -> p^d;

`list_elements/vectors` := proc(p,d)
 local L,i,j,u;
 
 L := [[]];
 for i from 1 to d do
  L := [seq(seq([op(u),j],j=0..p-1),u in L)];
 od:
 return L;
end:

`height/vectors` := (p,d) -> proc(u)
 local h;
 
 h := d;
 while h > 0 and u[h] = 0 do h := h - 1; od;
 return h;
end:

`count_elements/monic_vectors` := (p,d) -> (p^d - 1)/(p - 1);

`list_elements/monic_vectors` := proc(p,d)
 local i,u;
 
 [seq(seq([op(u),1,0$(d-1-i)],u in `list_elements/vectors`(p,i)),i=0..d-1)];
end:

`count_elements/full_flags` := proc(p,d) local i; mul((p^i-1)/(p-1),i=1..d); end:

`list_elements/full_flags` := proc(p,d)
 local L,L1,nL,H,V,i,j,k,u,v,q;
 L := [[]];
 H := [[]];
 
 for i from 1 to d do
  nL := nops(L);
  L1 := L;
  L := [];
  V := `list_elements/monic_vectors`(p,d - i + 1);
  H := map(W -> sort(map(`height/vectors`(p,d),W)),L1);
  for j from 1 to nL do 
   for v in V do
    u := [];
    q := 1;
    for k from 1 to d do
     if member(k,H[j]) then
      u := [op(u),0];
     else
      u := [op(u),v[q]];
      q := q + 1;
     fi;
    od:
    L := [op(L),[op(L1[j]),u]];
   od;
  od:
 od:

 return L;
end:

`random_element/full_flags` := (p,d) -> proc()
 local V,i,v;
 V := table():
 V[0] := `bot/subspaces`(p,d);
 for i from 1 to d do 
  v := [0$d];
  while `is_member/subspaces`(p,d)(v,V[i-1]) do 
   v := [seq(rand(0..p-1)(),i=1..d)];
  od;
  V[i] := `span/subspaces`(p,d)([op(V[i-1][1]),v]);
 end:
 return `from_subspace_list/full_flags`(p,d)([seq(V[i],i=1..d)]);
end:

`is_element/full_flags` := (p,d) -> proc(W)
 local h,i,j;

 if not(type(W,list(list(integer)))) then 
  return false;
 fi;

 if map(nops,W) <> [d$d] then 
  return false;
 fi;

 if W <> modp(W,p) then
  return false;
 fi;

 h := table():
 for i from 1 to d do 
  if W[i] = [0$d] then return false; fi;
  j := d; 
  while W[i][j] = 0 do j := j - 1; od;
  if W[i][j] <> 1 then 
   return false;
  fi;
  h[i] := j;
 od:

 for i from 1 to d do 
  for j from i+1 to d do 
   if W[j][h[i]] <> 0 then return false; fi;
  od;
 od;

 return true;
end:

`count_elements/full_flags` := proc(p,d) local i; mul((p^i-1)/(p-1),i = 1..d); end:

`basepoint/full_flags` := (p,d) -> convert(IdentityMatrix(d),listlist);

`to_subspace_list/full_flags` := (p,d) -> proc(W)
 local i;
 [seq(`span/subspaces`(p,d)([op(1..i,W)]),i=1..d)];
end:

`from_subspace_list/full_flags` := (p,d) -> proc(V)
 local i,j,h,v,W;

 v := V[1][1][1];
 j := d; while j > 0 and v[j] = 0 do j := j - 1; od; 
 v := modp(v /~ v[j],p);
 W := [v];
 h := [j];
 for i from 2 to d do 
  j := 1;
  while j < i and `is_member/subspaces`(p,d)(V[i][1][j],V[i-1]) do 
   j := j + 1;
  od;
  v := V[i][1][j];
  for j from 1 to i-1 do 
   v := modp(v -~ v[h[j]] *~ W[j],p);
  od:
  j := d; while j > 0 and v[j] = 0 do j := j - 1; od; 
  v := modp(v /~ v[j],p);
  W := [op(W),v];
  h := [op(h),j];
 od:
 return W;
end:

# It would be better to do this directly and use it in the
# `from_subspace/full_flags` procedure.
`from_generators/full_flags` := (p,d) -> proc(U)
 local V,i;
 V := [seq(`span/subspaces`(p,d)([op(1..i,U)]),i=1..d)];
 return `from_subspace_list/full_flags`(p,d)(V);
end:

`matrix_act/full_flags` := (p,d) -> proc(g,W)
 local gW,V,i;

 gW := convert(Transpose(Matrix(g) . Transpose(Matrix(W))),listlist);
 V := [seq(`span/subspaces`(p,d)([op(1..i,gW)]),i=1..d)];
 return `from_subspace_list/full_flags`(p,d)(V);
end:

`jordan_permutation/full_flags` := (p,d) -> proc(U,V)
 local U0,V0,UV,UV1,i,j,w;
 U0 := `to_subspace_list/full_flags`(p,d)(U);
 U0 := table([0 = `bot/subspaces`(p,d),seq(i = U0[i],i=1..d)]);
 V0 := `to_subspace_list/full_flags`(p,d)(V);
 V0 := table([0 = `bot/subspaces`(p,d),seq(i = V0[i],i=1..d)]);
 UV := table():
 for i from 0 to d do 
  for j from 0 to d do 
   UV[i,j] := `inter/subspaces`(p,d)(U0[i],V0[j]);
  od;
 od;
 UV1 := table();
 w := table():
 for i from 1 to d do 
  for j from 1 to d do 
   UV1[i,j] := `sum/subspaces`(p,d)(UV[i-1,j],UV[i,j-1]);
   if `dim/subspaces`(p,d)(UV[i,j]) > `dim/subspaces`(p,d)(UV1[i,j]) then
    w[i] := j;
   fi;
  od;
 od;
 return [seq(w[i],i=1..d)];
end:
