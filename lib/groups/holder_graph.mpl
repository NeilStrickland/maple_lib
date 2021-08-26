# The groupoid of sets of size 6 is equivalent to a certain groupoid of graphs which
# we have called Holder graphs.  Specifically, if A is a set of size 6, then we write
# DA for the set of subsets of size two, and we draw an edge between such subsets iff
# they are disjoint; this gives a Holder graph.  The code below sets up the
# relevant definitions.

`is_element/holder_graphs` := (V::set) -> proc(E)
 local non_edges,pentads,E0,e;
 
 if nops(V) <> 15 then
  return false;
 fi;

 if not `is_element/graphs`(V)(E) then
  return false;
 fi;
 
 if map(v -> nops(select(e -> e[1] = v,E)),V) <> {6} then
  return false;
 fi;

 non_edges := `top/autorel`(V) minus `id/autorel`(V) minus E;
 non_edges := map(e -> {op(e)},non_edges);

 pentads := combinat[choose](V,5);
 E0 := map(e -> {op(e)},E);

 for e in E0 do
  pentads := select(p -> e minus p <> {},pentads);
 od:

 for e in non_edges do
  if nops(select(p -> e minus p = {},pentads)) <> 1 then
   return false;
  fi;
 od;

 return true;
end:

`D/holder_graph` := proc(A::set)
 local V,E,v,w;
 
 if nops(A) <> 6 then
  error("A does not have size six");
 fi;

 V := combinat[choose](A,2);
 E := {seq(seq([v,w],w in V),v in V)};
 E := select(e -> e[1] intersect e[2] = {},E);
 return [V,E];
end:

`T/holder_graph` := (V::set) -> proc(E)
 local T,F,t,u;
 
 T := combinat[choose](V,3);
 T := select(t -> member([t[1],t[2]],E) and
                  member([t[2],t[3]],E) and
		  member([t[3],t[1]],E),T);

 F := {seq(seq([t,u],u in T),t in T)};
 F := select(e -> e[1] <> e[2],F);
 F := select(e -> e[1] intersect e[2] <> {},F);
 return [T,F];
end:

`P/holder_graph` := (V) -> proc(E)
 local P,E0,e;
 
 P := combinat[choose](V,5);
 E0 := map(e -> {op(e)},E);

 for e in E0 do
  P := select(p -> e minus p <> {},P);
 od:

 return P;
end:

`alpha/holder_graph` := (A) -> proc(a)
 local b;
 {seq({a,b},b in A minus {a})};
end:

`beta/holder_graph` := (V) -> (E) -> proc(v)
 local P;
 
 P := `P/holder_graph`(V)(E);

 return select(p -> member(v,p),P);
end:

`gamma/holder_graph` := (V) -> (E) -> proc(v)
 local T,F;
 
 T,F := op(`T/holder_graph`(V)(E));
 return select(t -> member(v,t),T);
end:

check_holder_graph := proc()
 local A0,A1,V0,V1,V2,V3,E0,E1,E2,E3,v,beta_table,gamma_table;

 A0 := {1,2,3,4,5,6};
 V0,E0 := op(`D/holder_graph`(A0)):
 _ASSERT(
  `is_element/holder_graphs`(V0)(E0),
  "D sends sets of size six to Holder graphs"
 );

 A1 := `P/holder_graph`(V0)(E0):
 _ASSERT(
  evalb(nops(A1) = 6),
  "P sends Holder graphs to sets of size six"
 );

 _ASSERT(
  evalb(map(`alpha/holder_graph`(A0),A0) = A1),
  "alpha : A -> PDA is bijective"
 );

 V1,E1 := op(`D/holder_graph`(A1)):

 _ASSERT(
  `is_element/holder_graphs`(V1)(E1),
  "DP sends Holder graphs to Holder graphs"
 );

 beta_table := table():
 for v in V0 do beta_table[v] := `beta/holder_graph`(V0)(E0)(v); od:
 _ASSERT(
  evalb(map(v -> beta_table[v],V0) = V1) and
  evalb(map(e -> [beta_table[e[1]],beta_table[e[2]]],E0) = E1),
  "beta : G -> DPG is an isomorphism"
 );

 V2,E2 := op(`T/holder_graph`(V0)(E0)):

 _ASSERT(
  `is_element/holder_graphs`(V2)(E2),
  "T sends Holder graphs to Holder graphs"
 );

 V3,E3 := op(`T/holder_graph`(V2)(E2)):
 _ASSERT(
  `is_element/holder_graphs`(V3)(E3),
  "T^2 sends Holder graphs to Holder graphs"
 );

 gamma_table := table():
 for v in V0 do gamma_table[v] := `gamma/holder_graph`(V0)(E0)(v); od:
 _ASSERT(
  evalb(map(v -> gamma_table[v],V0) = V3) and
  evalb(map(e -> [gamma_table[e[1]],gamma_table[e[2]]],E0) = E3),
  "gamma : G -> T^2G is an isomorphism"
 );
end:

# The code below is older.  It partially duplicates the code above and then
# sets up an embedding of a Holder graph in R^3 u {infinity}

make_holder_graph := proc()
 local i,j,k,l,ii,jj,kk,
  v,v_index,num_vertices,
  e,e_index,num_edges,
  t,t_index,num_triangles,
  col,vv,vi,ww,a,b,c,d,
  pol,draw_edge,sub_graph,full_sub_graph,G;

 i := 0:
 for j from 0 to 4 do
  for k from j+1 to 5 do
   v[i] := {j,k}:
   v_index[{j,k}] := i:
   i := i+1:
  od:
 od:
 num_vertices := i;

 i := 0:
 for j from 0 to num_vertices-2 do
  for k from j+1 to num_vertices-1 do
   if v[j] intersect v[k] = {} then
    e[i] := {j,k}:
    e_index[{j,k}] := i:
    i := i+1:
   fi:
  od:
 od:
 num_edges := i;

 i := 0:
 for j from 0 to num_vertices-1 do
  for k from j+1 to num_vertices-1 do
   for l from k+1 to num_vertices-1 do
    if nops({op(v[j]),op(v[k]),op(v[l])}) = 6 then
     ii := e_index[{j,k}]:
     jj := e_index[{j,l}]:
     kk := e_index[{k,l}]:
     t[i] := {ii,jj,kk}:
     t_index[{ii,jj,kk}] := i:
     col[ii] := i;
     col[jj] := i;
     col[kk] := i;
     i := i+1:
    fi:
   od:
  od:
 od:
 num_triangles := i;

 a := 0.3: b := 2: c := sqrt(3*b^2 - a^2): d := 1.5:

 t[0] := {};

 # Coordinates for a 3D picture
 vv[ 0] := infinity:
 vv[ 1] := [-b,-b, b]:
 vv[ 2] := [ b,-b,-b]:
 vv[ 3] := [-b, b,-b]:
 vv[ 4] := [ b, b, b]:
 vv[ 5] := [ b, b,-b]:
 vv[ 6] := [-b, b, b]:
 vv[ 7] := [ b,-b, b]:
 vv[ 8] := [-b,-b,-b]:
 vv[ 9] := [ 0,-c,-a]:
 vv[10] := [-c,-a, 0]:
 vv[11] := [-a, 0, c]:
 vv[12] := [-a, 0,-c]:
 vv[13] := [ c,-a, 0]:
 vv[14] := [ 0, c,-a]:

 vi[ 9] := [ 0, 0,-d]:
 vi[10] := [ 0,-d, 0]:
 vi[11] := [-d, 0, 0]:
 vi[12] := [-d, 0, 0]:
 vi[13] := [ 0,-d, 0]:
 vi[14] := [ 0, 0,-d]:

 # Coordinates for a planar picture
 pol := (r,t) -> simplify([r * cos(Pi/6*t), r * sin(Pi/6*t)]);

 ww[ 0] := pol(1, 0):
 ww[10] := pol(1, 1):
 ww[ 4] := pol(1, 2):
 ww[ 6] := pol(1, 3):
 ww[14] := pol(1, 4):
 ww[ 1] := pol(1, 5):
 ww[12] := pol(1, 6):
 ww[ 8] := pol(1, 7):
 ww[ 9] := pol(1, 8):
 ww[ 3] := pol(1, 9):
 ww[ 5] := pol(1,10):
 ww[13] := pol(1,11):
 ww[11] := pol(3, 0):
 ww[ 2] := pol(3, 4):
 ww[ 7] := pol(3, 8):

 G := table():

 G["v"] := eval(v);
 G["e"] := eval(e);
 G["t"] := eval(t);
 G["v_index"] := eval(v_index);
 G["e_index"] := eval(e_index);
 G["t_index"] := eval(t_index);
 G["num_vertices"] := num_vertices;
 G["num_edges"] := num_edges;
 G["num_triangles"] := num_triangles;
 G["col"] := eval(col);
 G["vv"] := eval(vv);
 G["vi"] := eval(vi);
 G["ww"] := eval(ww);

 draw_edge := proc(i)
  local u,p,q,r;
  u := e[i];
  p := vv[u[1]];
  q := vv[u[2]];
  if (p = infinity) then
   r := vi[u[2]];
   return(CURVES([q,[d*q[1],d*q[2],d*q[3]]],COLOR(HUE,col[i] * 0.07)));
  elif (p[1]*q[1] + p[2] * q[2] + p[3] * q[3] > 0) then
   return(great_arc(p,q,col[i] * 0.07));
  else 
   return(CURVES([p,q],COLOR(HUE,col[i] * 0.07)));
  fi;
 end:

 sub_graph := proc(edge_test) 
  local ee,i;
  ee := [];
  for i from 0 to num_edges-1 do
   if (edge_test(i)) then
    ee := [op(ee),i]; 
   fi;
  od:
  plots[display](PLOT3D(op(map(draw_edge,ee)),THICKNESS(3)),axes=none):
 end: 

 full_sub_graph := proc(vertex_test) 
  sub_graph(i -> vertex_test(e[i][1]) and vertex_test(e[i][2]));
 end:

 G["full_graph"] :=
  plots[display](PLOT3D(seq(draw_edge(i),i=0..num_edges-1),THICKNESS(3)),axes=none):

 G["outer_shell"] := full_sub_graph(i -> evalb(i < 9)):
 G["inner_shell"] := sub_graph(i -> evalb(e[i][1] > 8 and e[i][2] > 8)):
 G["joins"]       := sub_graph(i -> evalb(e[i][1] > 0 and e[i][1] < 9 and e[i][2] > 8)):

 G["plane_plot"] :=
  plots[display](
   seq(line(ww[e[i][1]],ww[e[i][2]]),i=0..num_edges-1),
   axes = none
  );

 return eval(G);
end:
