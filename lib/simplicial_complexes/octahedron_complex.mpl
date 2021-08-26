make_octahedron_complex := proc()
 global octahedron_complex,cube_complex;
 local OC,CC,vO,vC,vOi,vCi,i,j,k,dp,CF,f,G,G0,G1,r,g,h,eqs,sol,sc,OS,s,t;

 CC := table():
 OC := table():
 
 CC["vertices"] := [seq(i,i=1..8)];
 OC["vertices"] := [seq(i,i=1..6)];

 vO := table([
  1 = [1,0,0], 2 = [0,1,0], 3 = [0,0,1], 4 = [0,0,-1], 5 = [0,-1,0], 6 = [-1,0,0]
 ]);

 vC := table([
  1 = [ 1, 1, 1], 2 = [ 1, 1,-1], 3 = [ 1,-1, 1], 4 = [ 1,-1,-1],
  5 = [-1, 1, 1], 6 = [-1, 1,-1], 7 = [-1,-1, 1], 8 = [-1,-1,-1]
 ]);

 vOi := table():
 vCi := table():

 for i from 1 to 6 do vOi[vO[i]] := i; od;
 for i from 1 to 8 do vCi[vC[i]] := i; od;

 OC["embedding_dim"] := 3;
 CC["embedding_dim"] := 3;

 OC["embedding"]            := eval(vO);
 OC["normalised_embedding"] := copy(vO);
 OC["dual_embedding"]       := copy(vO);

 CC["embedding"]            := eval(vC);
 CC["normalised_embedding"] := table([seq(i = vC[i] *~ (sqrt(3)/3), i = 1 .. 8)]);
 CC["dual_embedding"]       := table([seq(i = vC[i] /~ 3, i = 1 .. 8)]);

 dp := (u,v) -> add(u[i] * v[i],i=1..3);
 
 OC["faces"]   := [seq(select(i -> dp(vO[i],vC[j]) = 1,OC["vertices"]),j = 1..8)];
 CC["squares"] := [seq(select(j -> dp(vO[i],vC[j]) = 1,CC["vertices"]),i = 1..6)];

 OC["edges"] := {op(map(op,map(f -> [[f[1],f[2]],[f[1],f[3]],[f[2],f[3]]],OC["faces"])))};
 OC["edges"] := sort([op(OC["edges"])]);

 CC["short_edges"] := [[1,2],[1,3],[1,5],[1,6],
                      [2,4],[2,6],[3,4],[3,7],[5,6],[5,7],
		      [4,8],[5,8],[6,8],[7,8]];
 
 CC["long_edges"]  := [[1,4],[1,6],[1,7],[2,8],[3,8],[5,8]];

 CC["edges"] := sort([op(CC["short_edges"]),op(CC["long_edges"])]);
 sc := [1,6,4,2,7,5,3,8];
 CC["six_cycle"] := sc;

 CF := NULL;
 OS := NULL;
 for s in CC["squares"] do
  i := op({op(s)} minus {seq(sc[j],j in s)});
  if member(1,s) then
   CF := CF,[1,s[2],s[4]],[1,s[3],s[4]];
   OS := OS,[1,i,sc[i],sc[sc[i]]];
  else
   CF := CF,[s[1],s[2],8],[s[1],s[3],8];
   OS := OS,[sc[sc[i]],sc[i],i,8];
  fi;
 od:
 OS := [OS];
 
 CC["faces"] := sort([CF]);
 CC["oriented_squares"] := OS;
 CC["square_plot"] :=
   display(
    seq(polygon(map(j -> vC[j],OS[i]),colour=standard_colour(i)),i=1..6),
    scaling=constrained,axes=none);

 OC["max_simplices"] := OC["faces"];
 CC["max_simplices"] := CC["faces"];

 OC["edge_index"]   := make_index(OC["edges"]):
 OC["face_index"]   := make_index(OC["faces"]):

 CC["edge_index"]   := make_index(CC["edges"]):
 CC["face_index"]   := make_index(CC["faces"]):

 `plot/simplicial_complex`(OC);
 `plot/simplicial_complex`(CC);

 OC["edge_centres"] :=
  map(e -> (vO[e[1]] +~ vO[e[2]]) /~ 2,OC["edges"]);

 OC["face_centres"] :=
  map(f -> (vO[f[1]] +~ vO[f[2]] +~ vO[f[3]]) /~ 3, OC["faces"]);

 CC["short_edge_centres"] :=
  map(e -> (vC[e[1]] +~ vC[e[2]]) /~ 2,CC["short_edges"]);

 CC["square_centres"] :=
  map(f -> (vC[f[1]] +~ vC[f[2]] +~ vC[f[3]] +~ vC[f[4]]) /~ 4, CC["squares"]);

 f := (u) -> simplify(rationalize(u /~ sqrt(add(u[i]^2,i=1..3))));

 OC["poles"] := table([
  2 = map(f,OC["edge_centres"]),
  3 = map(f,OC["face_centres"]),
  4 = map(i -> f(vO[i]),OC["vertices"])
 ]);

 CC["poles"] := copy(OC["poles"]);
 
 OC["pole_plots"] := table([
  2 = map(u -> line(1.1 *~ u, -1.1 *~ u,color=green,thickness=4),CC["poles"][2]),
  3 = map(u -> line(1.1 *~ u, -1.1 *~ u,color=red  ,thickness=4),CC["poles"][3]),
  4 = map(u -> line(1.2 *~ u, -1.2 *~ u,color=blue ,thickness=4),CC["poles"][4])
 ]);

 OC["all_poles_plot"] := display(
  op(OC["pole_plots"][2]),op(OC["pole_plots"][3]),op(OC["pole_plots"][4]),
  scaling=constrained,axes=none
 );

 CC["pole_plots"] := table([
  2 = map(u -> line(1.6 *~ u, -1.6 *~ u,color=green,thickness=4),CC["poles"][2]),
  3 = map(u -> line(1.9 *~ u, -1.9 *~ u,color=red  ,thickness=4),CC["poles"][3]),
  4 = map(u -> line(1.2 *~ u, -1.2 *~ u,color=blue ,thickness=4),CC["poles"][4])
 ]);

 CC["all_poles_plot"] := display(
  op(CC["pole_plots"][2]),op(CC["pole_plots"][3]),op(CC["pole_plots"][4]),
  scaling=constrained,axes=none
 );

 G0 := [];
 G1 := [[2,4,1,3,6,8,5,7],[1,3,5,7,2,4,6,8]];
 G := [[1,2,3,4,5,6,7,8]];

 while G <> G0 do
  G0 := G;
  G := sort([op({seq(seq(`o/permutations`(8)(g,h),g in G1),h in G)})]);
 od:

 r := table([1 = 1, 2 = 2, 3 = 3, 4 = 4, 5 = 4, 6 = 3, 7 = 2, 8 = 1]):

 CC["vertex_action"]     := table():
 CC["short_edge_action"] := table():
 CC["square_action"]     := table():
 CC["rotation_matrix"]   := table():
 
 OC["vertex_action"]     := table():
 OC["edge_action"]       := table():
 OC["face_action"]       := table():
 OC["rotation_matrix"]   := table():
 
 for s in G do
  t := [r[s[1]],r[s[2]],r[s[3]],r[s[4]]];
  CC["vertex_action"][t] := s;
  OC["face_action"][t]   := s;

  CC["short_edge_action"][t] :=
   map(e -> CC["short_edge_index"][sort([s[e[1]],s[e[2]]])],CC["short_edges"]);

  CC["square_action"][t] :=
   map(e -> CC["square_index"][sort([s[e[1]],s[e[2]],s[e[3]],s[e[4]]])],CC["squares"]);

  OC["vertex_action"][t] := CC["square_action"][t];

  OC["edge_action"][t] :=
   map(e -> OC["edge_index"][sort([s[e[1]],s[e[2]]])],OC["edges"]);

  g := Matrix(3,3,[seq(x[i],i=1..9)]);
  eqs := map(op,[seq(convert(g . Vector(vC[i]) - Vector(vC[s[i]]),list),i = 1..8)]);
  sol := solve(eqs);
  CC["rotation_matrix"][t] := subs(sol,convert( g,listlist));
  OC["rotation_matrix"][t] := CC["rotation_matrix"][s];
 od:
 
 octahedron_complex := eval(OC);
 cube_complex := eval(CC);
 return eval(OC);
end:

make_octahedron_complex():

octosphere_complex := proc(n::nonnegint)
 local T,T0,E,v,x,i,j;
 
 T := eval(octahedron_complex);

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