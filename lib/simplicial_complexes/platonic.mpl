make_platonic := proc()
 global platonic_complexes,tetrahedron_complex,cube_complex,
   octahedron_complex,dodecahedron_complex,icosahedron_complex;
 local AC,TC,CC,OC,DC,IC,t0,t1,t2,s0,s1,AV,p,q,u,v,ui,s,t,n,m,d,M,A5,dp,nm,dd,r,k,i,E,g,
       E0,E1,E2,F1,F2,F3,C0,P0,PP0,PM,pole_colours,c;

 AC := [seq(table(),i=1..5)];
 IC := eval(AC[1]); OC := eval(AC[2]); TC := eval(AC[3]); CC := eval(AC[4]); DC := eval(AC[5]);

 t0 := (sqrt(5) + 1)/2;
 t1 := (sqrt(5) - 1)/2;
 t2 := expand(t1^2);
 s0 := sqrt(2/(5 + sqrt(5)));
 s1 := sqrt(2/(5 - sqrt(5)));
 
 dp := (u,v) -> simplify(expand(add(u[i] * v[i],i=1..3)));
 nm := (u) -> simplify(sqrt(dp(u,u)));
 dd := (u,v) -> nm(u -~ v);
 
 AV := [
 [
  [  0, t2, t1],[  0, t2,-t1],[  0,-t2, t1],[  0,-t2,-t1],
  [ t1,  0, t2],[-t1,  0, t2],[ t1,  0,-t2],[-t1,  0,-t2],
  [ t2, t1,  0],[ t2,-t1,  0],[-t2, t1,  0],[-t2,-t1,  0]
 ],
 [
  [ 1, 0, 0],[ 0, 1, 0],[ 0, 0, 1],
  [ 0, 0,-1],[ 0,-1, 0],[-1, 0, 0]
 ],
 [
  [ 1, 1, 1],[ 1,-1,-1],[-1, 1,-1],[-1,-1, 1]
 ],
 [
  [ 1, 1, 1],[ 1,-1,-1],[-1, 1,-1],[-1,-1, 1],
  [-1, 1, 1],[ 1,-1, 1],[ 1, 1,-1],[-1,-1,-1]
 ],
 [
  [  1,  1,  1],[  1, -1, -1],[ -1,  1, -1],[ -1, -1,  1],
  [  0, t0, t1],[  0, t0,-t1],[  0,-t0, t1],[  0,-t0,-t1],
  [ t1,  0, t0],[-t1,  0, t0],[ t1,  0,-t0],[-t1,  0,-t0],
  [ t0, t1,  0],[ t0,-t1,  0],[-t0, t1,  0],[-t0,-t1,  0],
  [ -1,  1,  1],[  1, -1,  1],[  1,  1, -1],[ -1, -1, -1]
 ]];

 for p from 1 to 5 do
  n := nops(AV[p]);
  AC[p]["num_vertices"] := n;
  AC[p]["vertices"] := [seq(i,i=1..AC[p]["num_vertices"])];
  r := simplify(sqrt(dp(AV[p][1],AV[p][1])));
  AC[p]["vertex_radius"] := r;
  AC[p]["embedding"] := table([seq(i = AV[p][i],i=1..n)]);
  AC[p]["normalised_embedding"] := table([seq(i = evalf(AV[p][i] /~ r),i=1..n)]);
  AC[p]["embedding_index"] := table():
  for i from 1 to n do
   AC[p]["embedding_index"][AV[p][i]] := i;
  od:
 od:
 
 for p from 1 to 5 do
  q := 6 - p;
  u := AV[p]; v := AV[q]; n := nops(u); m := nops(v);
  k := `if`(p = 5,"pentagons",`if`(p = 4,"squares","faces"));
  AC[p][k] := [seq(select(i -> dp(u[i],v[j]) = -1,[seq(i,i=1..n)]),j = 1..m)];
  AC[p][cat("oriented_",k)] :=
   [seq(orient_face(f,AC[p]["embedding"]),f in AC[p][k])];
  AC[p]["facets"] := AC[p][k];
  AC[p]["oriented_facets"] := AC[p][cat("oriented_",k)];
  AC[p][cat("num_",k)] := m;
  AC[p]["num_facets"] := m;
  AC[p]["plot"] := display(
   seq(polygon(map(j -> u[j],AC[p]["oriented_facets"][i]),colour=standard_colour(i)),i=1..m),
   scaling=constrained,axes=none);
  AC[p]["grey_plot"] := display(
   seq(polygon(map(j -> u[j],AC[p]["oriented_facets"][i]),colour=grey),i=1..m),
   scaling=constrained,axes=none);
  AC[p]["wireframe_plot"] := display(
   seq(polygon(map(j -> u[j],AC[p]["oriented_facets"][i]),colour=grey,style=wireframe),i=1..m),
   scaling=constrained,axes=none);
 od;

 for p from 1 to 3 do
  u := AV[p];
  E := {op(map(op,map(f -> [[f[1],f[2]],[f[1],f[3]],[f[2],f[3]]],AC[p]["faces"])))};
  AC[p]["edges"] := sort([op(E)]);
  AC[p]["short_edges"] := AC[p]["edges"];
  AC[p]["long_edges"] := [];
  r := dd(u[E[1][1]],u[E[1][2]]);
  AC[p]["short_edge_length"] := r;
 od:

 u := AV[4];
 r := 2;
 CC["short_edge_length"] := r;
 CC["short_edges"] :=
  select(e -> dd(u[e[1]],u[e[2]]) = r,[seq(seq([i,j],j=i+1..8),i=1..8)]);
 CC["long_edges"] := [[1,2],[1,3],[1,4],[5,8],[6,8],[7,8]];
 CC["edges"] := sort([op(CC["short_edges"]),op(CC["long_edges"])]);
 CC["faces"] := [];
 
 u := AV[5];
 r := sqrt(5) - 1;
 DC["short_edge_length"] := r;
 DC["short_edges"] :=
  select(e -> dd(u[e[1]],u[e[2]]) = 2,[seq(seq([i,j],j=i+1..20),i=1..20)]);

 A5 := eval(alternating_five);

 for p from 1 to 5 do
  u := AV[p];
  ui := AC[p]["embedding_index"];
  AC[p]["rotation_group"] := NULL;
  AC[p]["vertex_permutation"] := table();
  for g in A5["elements"] do
   M := Matrix(A5["matrix"][g]);
   s := [seq(ui[expand(convert(M . Vector(u[i]),list))],i=1..nops(u))];
   if type(s,list(posint)) then
    AC[p]["rotation_group"] := AC[p]["rotation_group"],g;
    AC[p]["vertex_permutation"][g] := s;
   fi;
  od:
  AC[p]["rotation_group"] := [AC[p]["rotation_group"]];
 od:

 for p from 2 to 4 do
  AC[p]["poles"] := table([2 = {}, 3 = {}, 5 = {}]);

  for g in AC[p]["rotation_group"] do
   if g = [1,2,3,4,5] then continue; fi;
   d := A5["element_order"][g];
   AC[p]["poles"][d] := {op(AC[p]["poles"][d]),A5["axis"][g],-~ A5["axis"][g]};
  od;

  for d in [2,3,5] do
   AC[p]["poles"][d] := [op(AC[p]["poles"][d])];
  od:
 od:

 PM := [1,-1];
 IC["poles"] := table():
 IC["poles"][2] := [
  [1,0,0],[0,1,0],[0,0,1],[-1,0,0],[0,-1,0],[0,0,-1],
  seq(seq(seq([i,j * t1,k * t0]/~2,k in PM),j in PM),i in PM),
  seq(seq(seq([k * t0,i,j * t1]/~2,k in PM),j in PM),i in PM),
  seq(seq(seq([j * t1,k * t0,i]/~2,k in PM),j in PM),i in PM)
 ];

 IC["poles"][3] := expand([seq(DC["embedding"][i] *~ sqrt(3)/3,i=1..20)]);

 IC["poles"][5] := [
  [  0, s0, s1],[  0, s0,-s1],[  0,-s0, s1],[  0,-s0,-s1],
  [ s1,  0, s0],[-s1,  0, s0],[ s1,  0,-s0],[-s1,  0,-s0],
  [ s0, s1,  0],[ s0,-s1,  0],[-s0, s1,  0],[-s0,-s1,  0]
 ];

 DC["poles"] := copy(IC["poles"]);
 
 E0 := NULL:
 E1 := NULL:
 E2 := NULL:
 F1 := NULL:
 F2 := NULL:
 F3 := NULL:
 for s in DC["rotation_group"] do 
  t := DC["vertex_permutation"][s];
  E0 := E0,sort([t[1],t[ 5]]);
 od:
 for s in CC["rotation_group"] do 
  t := DC["vertex_permutation"][s];
  E1 := E1,sort([t[1],t[10]]);
  E2 := E2,sort([t[1],t[17]]);
  F1 := F1,sort([t[1],t[ 9],t[10]]);
  F2 := F2,sort([t[1],t[ 5],t[17]]);
  F3 := F3,sort([t[1],t[10],t[17]]);
 od:
 E0 := sort([op({E0})]);
 E1 := sort([op({E1})]);
 E2 := sort([op({E2})]);
 F1 := sort([op({F1})]);
 F2 := sort([op({F2})]);
 F3 := sort([op({F3})]);

 DC["short_edges"] := E0;
 DC["long_edges_a"] := E1;
 DC["long_edges_b"] := E2;
 DC["edges"] := sort([op(E0),op(E1),op(E2)]);

 DC["faces_a"] := F1;
 DC["faces_b"] := F2;
 DC["faces_c"] := F3;
 DC["faces"] := sort([op(F1),op(F2),op(F3)]);

 DC["inscribed_cubes"] := [
  [3, 5, 8, 10, 11, 13, 16, 18], 
  [4, 5, 8,  9, 12, 14, 15, 19],
  [2, 6, 7,  9, 12, 13, 16, 17], 
  [1, 6, 7, 10, 11, 14, 15, 20], 
  [1, 2, 3,  4, 17, 18, 19, 20] 
 ];

 v := DC["embedding"];
 
 DC["all_edges_plot"] := 
  display(
   seq(line(v[e[1]],v[e[2]],colour=blue) ,e in DC["short_edges"]),
   seq(line(v[e[1]],v[e[2]],colour=red)  ,e in DC["long_edges_a"]),
   seq(line(v[e[1]],v[e[2]],colour=green),e in DC["long_edges_b"]),
   scaling=constrained,axes=none
  );

 DC["triangle_plot"] := 
  display(
   seq(polygon([v[e[1]],v[e[2]],v[e[3]]],colour=blue ),e in DC["faces_a"]),
   seq(polygon([v[e[1]],v[e[2]],v[e[3]]],colour=red  ),e in DC["faces_b"]),
   seq(polygon([v[e[1]],v[e[2]],v[e[3]]],colour=green),e in DC["faces_c"]),
   scaling=constrained,axes=none
  );

 PP0 := NULL:
 for k from 1 to 5 do 
  C0 := DC["inscribed_cubes"][k];
  E0 := [seq(seq([C0[i],C0[j]],j=i+1..8),i=1..7)]:
  E0 := select(e -> simplify(expand(dd(v[e[1]],v[e[2]]))) = 2,E0);
  P0 := display(seq(line(v[e[1]],v[e[2]],colour=standard_colour(k)),e in E0),
                scaling=constrained,axes=none);
  PP0 := PP0,P0;
 od:
 DC["cubes_plot"] := display(DC["grey_plot"],PP0);

 pole_colours := table([2 = green, 3 = red, 5 = blue]):
 
 IC["pole_length"] := table([2 = 0.8, 3 = 0.8, 5 = 0.9]):
 OC["pole_length"] := table([2 = 1.2, 3 = 0.8, 5 = 0.9]):
 TC["pole_length"] := table([2 = 1.3, 3 = 1.2, 5 = 0.9]):
 CC["pole_length"] := table([2 = 1.3, 3 = 2.0, 5 = 0.9]):
 DC["pole_length"] := table([2 = 2.0, 3 = 2.0, 5 = 1.7]):

 for p from 1 to 5 do 
  AC[p]["unit_pole_plot"] := table():
  AC[p]["pole_plot"] := table():
  for d in [2,3,5] do 
   r := AC[p]["pole_length"][d];
   c := pole_colours[d];
   AC[p]["pole_plot"][d] := 
     map(u -> line(-r *~ u,r *~u,colour = c,thickness=4),AC[p]["poles"][d]);
   AC[p]["unit_pole_plot"][d] := 
     map(u -> line(-1.1 *~ u,1.1 *~u,colour = c,thickness=4),AC[p]["poles"][d]);
  od:
  AC[p]["all_poles_plot"] := 
   display(seq(op(AC[p]["pole_plot"][d]),d in [2,3,5]),
	   scaling=constrained,axes=none);
  AC[p]["all_unit_poles_plot"] := 
   display(seq(op(AC[p]["unit_pole_plot"][d]),d in [2,3,5]),
	   scaling=constrained,axes=none);
  if p >= 2 and p <= 4 then 
   AC[p]["sample_poles_plot"] := 
    display(AC[p]["pole_plot"][2][1],
	    AC[p]["pole_plot"][3][1],
	    scaling=constrained,axes=none);
  else
   AC[p]["sample_poles_plot"] := 
    display(AC[p]["pole_plot"][2][1],
	    AC[p]["pole_plot"][3][1],
	    AC[p]["pole_plot"][5][1],
	    scaling=constrained,axes=none);
  fi:
 od:

 IC["dual_factor"] := 3;
 OC["dual_factor"] := 3;
 TC["dual_factor"] := 3;
 CC["dual_factor"] := 1;
 DC["dual_factor"] := 5 - 2 * sqrt(5);

 for p from 1 to 5 do 
  q := 6 - p;
  v := AC[q]["embedding"];
  m := nops(AC[q]["oriented_facets"]);
  r := AC[p]["dual_factor"];

  AC[p]["dual_plot"] := display(
   AC[p]["wireframe_plot"],
   seq(polygon(map(j -> evalf(v[j] /~ (-r)),AC[q]["oriented_facets"][i]),colour=standard_colour(i)),i=1..m),
   scaling=constrained,axes=none
  );
 od:

 platonic_complexes   := eval(AC);
 icosahedron_complex  := eval(IC);
 octahedron_complex   := eval(OC);
 tetrahedron_complex  := eval(TC);
 cube_complex         := eval(CC);
 dodecahedron_complex := eval(DC);
 NULL;
end:
