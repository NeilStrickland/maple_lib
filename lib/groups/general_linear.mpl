`permutation_matrix` := proc(s)
  local n,g,i;
  
  n := nops(s);
  g := Matrix(n,n);
  for i from 1 to n do
   g[s[i],i] := 1;
  od:
  return g;
end:

`reduced_permutation_matrix` := proc(s)
  local n,g,i,j,k,l;
  
  n := nops(s);
  g := Matrix(n-1,n-1);
  for i from 1 to n-1 do
   j := s[i];
   k := s[i+1];
   if j < k then
    for l from j to k-1 do
     g[l,i] := 1;
    od:
   else
    for l from k to j-1 do
     g[l,i] := -1;
    od:
   fi;
  od:
  return g;
end:

`elementary_matrix/D` := (n) -> proc(i,a)
  local g,k;
  g := Matrix(n,n);
  for k from 1 to n do g[k,k] := 1; od;
  g[i,i] := a;
  return g;
end:

`elementary_matrix/E` := (n) -> proc(i,j,a_)
  local g,k;
  g := Matrix(n,n);
  for k from 1 to n do g[k,k] := 1; od;
  g[i,j] := `if`(nargs > 2,a_,1);
  return g;
end:

`elementary_matrix/F` := (n) -> proc(i,j)
  local g,k;
  g := Matrix(n,n);
  for k from 1 to n do g[k,k] := 1; od;
  g[i,i] := 0; g[j,j] := 0;
  g[i,j] := 1; g[j,i] := 1;
  return g;
end:

make_general_linear := proc(n,p)
  local G,i,j,k,m,g,L,f,u;
  
  m := n^2;
  
  G := table():
  G["p"] := p;
  G["id"] := IdentityMatrix(n);
  G["o"] := (g,h) -> map(mods,g . h,G["p"]);
  G["inv"] := g -> map(mods,1/g,G["p"]);
  G["order"] := mul(p^n - p^i,i = 0..n-1);
  
  L := [[]];
  for i from 1 to m do
   L := [seq(seq([op(u),j],j=0..p-1),u in L)];
  od:

  f := proc(u)
   local i,j,k,g;
   g := Matrix(n,n);
   k := 1;
   for i from 1 to n do
    for j from 1 to n do
     g[i,j] := mods(u[k],p); k := k + 1;
    od:
   od:
   if mods(Determinant(g),p) <> 0 then
    return g;
   else
    return NULL;
   fi;
  end:
  
  G["elements"] := map(f,L);

  return eval(G);
end:

bruhat_permutation := (n,p) -> proc(g)
 local h,i,j,k,a,q,qi;

 if [Dimension(g)] <> [n,n] then
  error("Not an n x n matrix");
 fi;
 
 h := eval(g);
 q := [];
 for i from n to 1 by -1 do
  j := 1;
  while h[i,j] = 0 do j := j+1; od;
  q := [j,op(q)];
  a := mods(1/h[i,j],p);
  h := map(mods,`elementary_matrix/D`(n)(i,a) . h,p);
  for k from 1 to i-1 do
   h := map(mods,`elementary_matrix/E`(n)(k,i,-h[k,j]) . h,p);
  od; 
 od;
 qi := table():
 for i from 1 to n do qi[q[i]] := i; od:
 
 return([seq(qi[i],i=1..n)]);
end:

# This returns a triple [b,w,c] where b is upper triangular,
# w is a permutation matrix, c is upper unitriangular and g = bwc.

bruhat_decomposition := (n,p) -> proc(g) 
 local h,i,j,k,a,b,c,x,q,w;

 if [Dimension(g)] <> [n,n] then
  error("Not an n x n matrix");
 fi;
 
 h := eval(g);
 q := [];
 b := Matrix(n,n);
 for k from 1 to n do b[k,k] := 1; od:

 for i from n to 1 by -1 do
  j := 1;
  while h[i,j] = 0 do j := j+1; od;
  q := [j,op(q)];
  x := mods(1/h[i,j],p);
  b := map(mods, b . `elementary_matrix/D`(n)(i,h[i,j]),p);
  h := map(mods, `elementary_matrix/D`(n)(i,x) . h,p);
  for k from 1 to i-1 do
   b := map(mods,b . `elementary_matrix/E`(n)(k,i,h[k,j]),p);
   h := map(mods,`elementary_matrix/E`(n)(k,i,-h[k,j]) . h,p);
  od; 
 od;
 w := permutation_matrix(q);
 c := w . h;
 return([b,Transpose(w),c]);
end:
