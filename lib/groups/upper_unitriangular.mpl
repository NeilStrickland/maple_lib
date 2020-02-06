make_upper_unitriangular := proc(n,p)
  local G,i,j,k,m,g,L,f;
  
  m := n * (n - 1) / 2;
  
  G := table():
  G["p"] := p;
  G["id"] := IdentityMatrix(n);
  G["o"] := (g,h) -> map(mods,g . h,G["p"]);
  G["inv"] := g -> map(mods,1/g,G["p"]);
  G["order"] := p ^ m;
  
  G["elementary"] := table():
  for i from 1 to n do
   for j from i+1 to n do
    g := Matrix(n,n);
    for k from 1 to n do g[k,k] := 1; od:
    g[i,j] := 1;
    G["elementary"][i,j] := g;
   od:
  od:

  L := [[]];
  for i from 1 to m do
   L := [seq(seq([op(u),j],j=0..p-1),u in L)];
  od:

  f := proc(u)
   local i,j,k,g;
   g := Matrix(n,n);
   for k from 1 to n do g[k,k] := 1; od:
   k := 1;
   for i from 1 to n do
    for j from i+1 to n do
     g[i,j] := mods(u[k],p); k := k + 1;
    od:
   od:
   return g;
  end:
  
  G["elements"] := map(f,L);

  return eval(G);
end: