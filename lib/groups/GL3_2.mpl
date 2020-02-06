make_GL3_2 := proc()
 global GL3_2;
 local G,L,E,f,n,i,j,k,g,h;
 
 G := table():

 L := [[]]:
 for i from 1 to 9 do
  L := [seq(seq([op(u),j],j=0..1),u in L)];
 od:

 # Strange order ensures that 1 comes first, followed by other
 # upper unitriangular matrices.
 f := (u) -> Matrix([[u[7],u[5],u[6]],
                     [u[1],u[8],u[4]],
		     [u[3],u[2],u[9]]]);
 L := select(u -> mods(Determinant(f(u)),2) <> 0,L);
 n := nops(L);
 E := map(f,L);
 
 G["elements"] := E;
 
 G["index"] := table():
 for i from 1 to n do G["index"][convert(E[i],listlist)] := i; od:
 
 G["id"] := IdentityMatrix(3);
 G["o"] := (u,v) -> map(mods,u . v,2);
 G["inv"] := (u) -> map(mods,1 / u,2);

 G["o_table"] := table();
 G["inv_table"] := table();

 for i from 1 to n do
  g := G["elements"][i];
  G["inv_table"][i] := G["index"][convert(G["inv"](g),listlist)];

  for j from 1 to n do
   h := G["elements"][j];
   G["o_table"][i,j] := G["index"][convert(G["o"](g,h),listlist)];
  od:
 od:

 G["ee"] := convert(IdentityMatrix(n),listlist);

 G["ring_id"] := G["ee"][1];
 
 G["antipode"] := proc(u)
  local n,M,w,i,j;
  n := 168;
  M := eval(GL3_2["inv_table"]);
  w := [seq(u[M[i]],i=1..n)];
  return w;
 end:
 
 G["convolve"] := proc(u,v)
  local n,J,M,w,i,j,ii;
  n := 168;
  J := eval(GL3_2["inv_table"]);
  M := eval(GL3_2["o_table"]);
  w := [0$n];
  for i from 1 to n do
    if u[i] <> 0 then
    ii := J[i];
    w := w +~ [seq(u[i] * v[M[ii,j]],j=1..n)];
   fi;
  od;

  return w;
 end:

 G["borel_elements"] :=
   [seq(seq(seq(Matrix([[1,i,j],[0,1,k],[0,0,1]]),i=0..1),j=0..1),k=0..1)]:
 G["borel_indices"] :=
   map(b -> G["index"][convert(b,listlist)],G["borel_elements"]);
 G["borel_sum"] := [0$168]:
 for i in G["borel_indices"] do
  G["borel_sum"] := G["borel_sum"] +~ G["ee"][i]:
 od:

 G["coxeter_elements"] := map(permutation_matrix,combinat[permute](3)):
 G["coxeter_indices"] := map(w -> G["index"][convert(w,listlist)],G["coxeter_elements"]):
 G["signed_coxeter_sum"] := [0$168]:
 for i in G["coxeter_indices"] do
  G["signed_coxeter_sum"] := G["signed_coxeter_sum"] +~ Determinant(E[i]) *~ G["ee"][i]:
 od:

 G["steinberg_idempotent"] :=
  G["convolve"](G["signed_coxeter_sum"], G["borel_sum"]) / 21;
  
 GL3_2 := eval(G);
 return(eval(G));
end:

