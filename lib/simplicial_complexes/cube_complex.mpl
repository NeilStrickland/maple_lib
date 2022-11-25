cube_complex := proc()
 local T,V,E,F,G0,G1,G,S,r,v,f,i,j,k,s,s1,t,g,h,eqs,sol;

 V := [seq(i,i=1..8)];

 T["vertices"] := V;

 T["short_edges"] := [
  [1,2],[1,3],[1,5],[2,4],[2,6],[3,4],[3,7],[4,8],[5,6],[5,7],[6,8],[7,8]
 ];

 T["long_edges"] := [[1,4],[1,6],[1,7],[2,8],[3,8],[4,8]];
 
 T["edges"] := sort([op(T["short_edges"]),op(T["long_edges"])]);

 T["squares"] := [
  [1,2,3,4],[1,2,5,6],[1,3,5,7],[2,4,6,8],[3,4,7,8],[5,6,7,8]
 ];

 T["faces"] := [
  [1,2,4],[1,3,4],[1,2,6],[1,5,6],[1,3,7],[1,5,7],
  [2,4,8],[2,6,8],[3,4,8],[3,7,8],[5,6,8],[5,7,8]
 ];

 T["max_simplices"] := T["faces"];
 
 T["vertex_index"]     := make_index(T["vertices"]):
 T["short_edge_index"] := make_index(T["short_edges"]):
 T["square_index"]     := make_index(T["squares"]):

 T["embedding_dim"] := 3;
 
 T["embedding"] := table([
  1 = [-1,-1,-1],
  2 = [ 1,-1,-1],
  3 = [-1, 1,-1],
  4 = [ 1, 1,-1],
  5 = [-1,-1, 1],
  6 = [ 1,-1, 1],
  7 = [-1, 1, 1],
  8 = [ 1, 1, 1]
 ]);

 v := eval(T["embedding"]);

 `plot/simplicial_complex`(T);

 S := NULL;
 for i from 1 to nops(T["squares"]) do
  f := T["squares"][i];
  f := [f[1],f[2],f[4],f[3]];
  S := S, polygon(map(j -> T["embedding"][j],f),colour=standard_colour(i));
 od:
 
 T["square_plot"] := display(S,scaling=constrained,axes=none);
 
 T["short_edge_centres"] :=
  map(e -> (v[e[1]] +~ v[e[2]]) /~ 2,T["short_edges"]);

 T["square_centres"] :=
  map(f -> (v[f[1]] +~ v[f[2]] +~ v[f[3]] +~ v[f[4]]) /~ 4, T["squares"]);

 f := (u) -> simplify(u /~ sqrt(add(u[i]^2,i=1..3)));

 T["poles"] := table([
  2 = map(f,T["short_edge_centres"]),
  3 = map(i -> f(v[i]),T["vertices"]),
  4 = map(f,T["square_centres"])
 ]);

 T["pole_plots"] := table([
  2 = map(u -> line(1.6 *~ u, -1.6 *~ u,color=green,thickness=4),T["poles"][2]),
  3 = map(u -> line(1.9 *~ u, -1.9 *~ u,color=red  ,thickness=4),T["poles"][3]),
  4 = map(u -> line(1.2 *~ u, -1.2 *~ u,color=blue ,thickness=4),T["poles"][4])
 ]);

 T["all_poles_plot"] := display(
  op(T["pole_plots"][2]),op(T["pole_plots"][3]),op(T["pole_plots"][4]),
  scaling=constrained,axes=none
 );

 G0 := [];
 G1 := [[2,4,1,3,6,8,5,7],[1,3,5,7,2,4,6,8]];
 G := [[1,2,3,4,5,6,7,8]];

 while G <> G0 do
  G0 := G;
  G := sort([op({seq(seq(`o/permutations`(8)(g,h),g in G1),h in G)})]);
 od:

 T["rotation_group"] := G;

 T["symmetry_group"] :=
   sort([op(G),op(map(s -> `o/permutations`(8)([8,7,6,5,4,3,2,1],s),G))]);

 r := table([1 = 1, 2 = 2, 3 = 3, 4 = 4, 5 = 4, 6 = 3, 7 = 2, 8 = 1]):
 
 T["to_axis_perm"]    := table():
 T["of_axis_perm"]    := table():
 T["symmetry_matrix"] := table():

 for s in T["rotation_group"] do
  s1 := `o/permutations`(8)([8,7,6,5,4,3,2,1],s);
  t := [r[s[1]],r[s[2]],r[s[3]],r[s[4]]];
  T["to_axis_perm"][s]  := t;
  T["to_axis_perm"][s1] := t;
  T["of_axis_perm"][t]  := s;

  g := Matrix(3,3,[seq(x[i],i=1..9)]);
  eqs := map(op,[seq(convert(g . Vector(v[i]) - Vector(v[s[i]]),list),i = 1..8)]);
  sol := solve(eqs);
  T["symmetry_matrix"][s ] := subs(sol,convert( g,listlist));
  T["symmetry_matrix"][s1] := subs(sol,convert(-g,listlist));
 od:

 return eval(T);
end: