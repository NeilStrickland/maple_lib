make_tetrahedron_complex := proc()
 global tetrahedron_complex;
 
 local T,V,E,F,v,f,P2,P3,g,s,x,eqs,sol;
 
 V := [seq(i,i=1..4)];
 E := [seq(seq([i,j],j=i+1..4),i=1..4)];
 F := [seq(seq(seq([i,j,k],k=j+1..4),j=i+1..4),i=1..4)];

 T := table([]);

 T["vertices"] := V;
 T["edges"] := E;
 T["coedges"] := E;
 T["faces"] := F;
 T["max_simplices"] := F;

 T["edge_index"]   := make_index(T["edges"]):
 T["face_index"]   := make_index(T["faces"]):

 T["simplices"] := [map(v -> [v],V),op(E),op(F)];

 T["embedding_dim"] := 3;
 T["embedding"] := table([
  1 = [ 1, 1, 1], 2 = [ 1,-1,-1], 3 = [-1, 1,-1], 4 = [-1,-1, 1]
 ]);
 
 T["axial_embedding"] :=
  table([1 = simplex_embedding([1,0,0,0]),
         2 = simplex_embedding([0,1,0,0]),
	 3 = simplex_embedding([0,0,1,0]),
	 4 = simplex_embedding([0,0,0,1])]);

 v := eval(T["embedding"]);

 T["normalised_embedding"] :=
  table([seq(i = v[i] *~ (sqrt(3)/3), i = 1..4)]);
  
 T["dual_embedding"] := table([seq(i = -~ v[i],i = 1..4)]);
 
 `plot/simplicial_complex`(T);

 T["edge_centres"] :=
  map(e -> (v[e[1]] +~ v[e[2]]) /~ 2,T["edges"]);

 T["face_centres"] :=
  map(f -> (v[f[1]] +~ v[f[2]] +~ v[f[3]]) /~ 3, T["faces"]);

 f := u -> combine(simplify(rationalize(u /~ sqrt(add(u[i]^2,i=1..3)))));
 P2 := [seq(seq(f(v[i] +~ v[j]),j=i+1..4),i=1..3)];
 P3 := [seq(f(v[i]),i=1..4),seq(f(-~ v[i]),i=1..4)];

 T["poles"] := table([2 = P2, 3 = P3]);

 T["planes"] := [
  seq(seq(f(v[i] -~ v[j]),j=i+1..4),i=1..3),
  seq(seq(f(v[j] -~ v[i]),j=i+1..4),i=1..3)
 ];

 T["pole_plots"] := table([
  2 = map(u -> line(1.2 *~ u, -1.2 *~ u,color=green,thickness=4),T["poles"][2]),
  3 = map(u -> line(1.2 *~ u, -1.2 *~ u,color=red  ,thickness=4),T["poles"][3])
 ]);

 T["all_poles_plot"] := display(
  op(T["pole_plots"][2]),op(T["pole_plots"][3]),
  scaling=constrained,axes=none
 );
 
 T["symmetry_group"] := combinat[permute](4);
 T["rotation_group"] :=
  select(s -> mul(mul(s[j] - s[i],j=i+1..4),i=1..3) > 0, T["symmetry_group"]);

 T["symmetry_matrix"] := table():

 for s in T["symmetry_group"] do
  g := Matrix(3,3,[seq(x[i],i=1..9)]);
  eqs := map(op,[seq(convert(g . Vector(v[i]) - Vector(v[s[i]]),list),i = 1..4)]);
  sol := solve(eqs);
  T["symmetry_matrix"][s] := simplify(rationalize(subs(sol,convert(g,listlist))));
 od:

 tetrahedron_complex := eval(T);
 return eval(T);
end:

make_tetrahedron_complex():
