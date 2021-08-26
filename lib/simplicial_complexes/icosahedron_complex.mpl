make_icosahedron_complex := proc()
 global icosahedron_complex,dodecahedron_complex;
 local IC,DC,tau,vI,vD,i;

 IC := table():
 DC := table():
 
 IC["vertices"] := [seq(i,i=1..12)];
 DC["vertices"] := [seq(i,i=1..20)];

 IC["faces"] := [
  [ 1, 2, 9], [ 1, 2,11], [ 1, 5, 6], [ 1, 5, 9], [ 1, 6,11],
  [ 2, 7, 8], [ 2, 7, 9], [ 2, 8,11], [ 3, 4,10], [ 3, 4,12],
  [ 3, 5, 6], [ 3, 5,10], [ 3, 6,12], [ 4, 7, 8], [ 4, 7,10],
  [ 4, 8,12], [ 5, 9,10], [ 6,11,12], [ 7, 9,10], [ 8,11,12]
 ];

 IC["edges"] := {op(map(op,map(f -> [[f[1],f[2]],[f[1],f[3]],[f[2],f[3]]],IC["faces"])))};
 IC["edges"] := sort([op(IC["edges"])]);

 IC["max_simplices"] := IC["faces"];
 
 tau := (1+sqrt(5))/2;

 IC["embedding_dim"] := 3;

 vI := table([
   1 = [   0,   1, tau],
   2 = [   0,  -1, tau],
   3 = [   0,   1,-tau],
   4 = [   0,  -1,-tau],
   5 = [   1, tau,   0],
   6 = [  -1, tau,   0],
   7 = [   1,-tau,   0],
   8 = [  -1,-tau,   0],
   9 = [ tau,   0,   1],
  10 = [ tau,   0,  -1],
  11 = [-tau,   0,   1],
  12 = [-tau,   0,  -1]
 ]):

 for i from 1 to 12 do vI[i] := simplify(rationalize(vI[i] /~ tau^2)); od;

 IC["embedding"] := eval(vI);
 IC["normalised_embedding"] := table([
  seq(i = evalf(vI[i] /~ sqrt(5-2*sqrt(5))),i = 1..12)
 ]);

 IC["edge_centres"] :=
  map(e -> (vI[e[1]] +~ vI[e[2]]) /~ 2,IC["edges"]);

 IC["face_centres"] :=
  map(f -> (vI[f[1]] +~ vI[f[2]] +~ vI[f[3]]) /~ 3, IC["faces"]);

 `plot/simplicial_complex`(IC);

 icosahedron_complex := eval(IC);
 dodecahedron_complex := eval(DC);
 return eval(IC);
end:

make_icosahedron_complex():

icosphere_complex := proc(n::nonnegint)
 local T,T0,E,v,x,i,j;
 
 T := eval(icosahedron_complex);

 for i from 1 to n do
  T0 := eval(T);
  T := eval(`triangular_subdivision/simplicial_complex`(T0));
  T0 := eval(T);
  T := eval(`condense/simplicial_complex`(T0));
  E := T["embedding"];
  for v in T["vertices"] do
   x := E[v];
   x := evalf(x /~ sqrt(add(x[j]^2,j=1..3)));
   E[v] := x;
  od:
 od:

 return eval(T):
end: