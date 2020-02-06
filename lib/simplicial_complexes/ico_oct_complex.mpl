make_ico_oct_complex := proc()
 global ico_oct_complex, ico_oct_complex1;
 local n,T,T0,T1,m,v,w,vo,vi,i,j,k,E,F,e,f,nm;

 n := 102;
 T["vertices"] := [seq(i,i=1..n)];
 T["embedding_dim"] := 3;

 m := (i,j) -> 3 + 20 * i + modp(j,20):
 v := table():
 
 v[1] := [0,0,1]:
 v[2] := [0,0,-1]:

 for i from 0 to 19 do 
  v[m(0,i)] := evalf([cos(Pi*i/10)  ,sin(Pi*i/10)  , 2] /~ sqrt(5));
  v[m(2,i)] := evalf([cos(Pi*i/10)  ,sin(Pi*i/10)  , 0]);
  v[m(4,i)] := evalf([cos(Pi*i/10)  ,sin(Pi*i/10)  ,-2] /~ sqrt(5));
 od:

 for i from 0 to 4 do 
  v[m(1,4*i)]   := evalf([cos(Pi*4*i/10)*2,sin(Pi*4*i/10)*2, 1] /~ sqrt(5));
  v[m(3,4*i+2)] := evalf([cos(Pi*(4*i+2)/10)*2,sin(Pi*(4*i+2)/10)*2, -1] /~ sqrt(5));
 od:

 nm := (x) -> x /~ sqrt(add(x[i]^2,i=1..3));
 
 for i from 0 to 4 do
  v[m(1,4*i+2)] := nm(v[m(1,4*i  )] +~ v[m(1,4*i+4)]);
  v[m(3,4*i  )] := nm(v[m(3,4*i-2)] +~ v[m(3,4*i+2)]);
 od:
 
 for i from 0 to 4 do
  v[m(1,4*i+1)] := nm(v[m(1,4*i  )] +~ v[m(1,4*i+2)]);
  v[m(1,4*i+3)] := nm(v[m(1,4*i+2)] +~ v[m(1,4*i+4)]);
  v[m(3,4*i+1)] := nm(v[m(3,4*i  )] +~ v[m(3,4*i+2)]);
  v[m(3,4*i+3)] := nm(v[m(3,4*i+2)] +~ v[m(3,4*i+4)]);
 od:
 
 vo := table():
 for i from 1 to n do
  vo[i] := v[i] /~ `+`(op(map(abs,v[i])));
 od:
 
 T["embedding"] := eval(v);
 T["sphere_embedding"] := eval(v);
 T["octahedron_embedding"] := eval(vo);
 T["normal"] := copy(v);
 
 E := [
  seq([ 1  , m(0,i)],i=0..19),
  seq(seq([m(j,i),m(j+1,i)],i=0..19),j=0..3),
  seq([m(4,i),2],i=0..19),
  seq(seq([m(j,i),m(j,i+1)],i=0..19),j=0..4),
  seq([m(0,i),m(1,i+1)],i=1..19,2),
  seq([m(0,i),m(1,i-1)],i=1..19,2),
  seq([m(1,i+1),m(2,i)],i=1..19,2),
  seq([m(1,i-1),m(2,i)],i=1..19,2),
  seq([m(2,i),m(3,i+1)],i=1..19,2),
  seq([m(2,i),m(3,i-1)],i=1..19,2),
  seq([m(3,i+1),m(4,i)],i=1..19,2),
  seq([m(3,i-1),m(4,i)],i=1..19,2),
  NULL
 ]:

 E := sort([op(map(e -> sort([op(e)]),E))]);
 
 T["edges"] := E;
 
 F := NULL;
 for e in T["edges"] do
  i,j := op(e);
  for k from max(i,j)+1 to n do
   if k <> i and k <> j and member([i,k],E) and member([j,k],E) then
    F := F,[i,j,k];
   fi;
  od:
 od:

 F := [F];
 T["faces"] := F;
 T["max_simplices"] := T["faces"];

 T["octahedron_edges"] := [
  seq([ 1  , m(0,i)],i=0..19,5),
  seq(seq([m(j,i),m(j+1,i)],i=0..19,5),j=0..3),
  seq([m(4,i),2],i=0..19,5),
  seq([m(2,i),m(2,i+1)],i=0..19),
  NULL
 ]:

 T["octahedron_edges"] := sort(map(sort,T["octahedron_edges"])):
 
 T["octahedron_basic_vertices"] :=
  sort([1,2,m(2,0),m(2,5),m(2,10),m(2,15)]);
  
 T["octahedron_basic_edges"] := [
  seq([1,m(2,5*i)],i=0..3),
  seq([m(2,5*i),m(2,5*(i+1))],i=0..3),
  seq([m(2,5*i),2],i=0..3)
 ]:

 T["octahedron_basic_edges"] := sort(map(sort,T["octahedron_basic_edges"])):

 T["octahedron_basic_faces"] := [
  seq([1,m(2,5*i),m(2,5*(i+1))],i=0..3),
  seq([2,m(2,5*i),m(2,5*(i+1))],i=0..3)
 ]:

 T["octahedron_basic_faces"] := sort(map(sort,T["octahedron_basic_faces"])):

 T["icosahedron_edges"] := [
  seq([ 1  , m(0,4*i)],i=0..4),
  seq([m(0,4*i),m(1,4*i)],i=0..4),
  seq([m(1,4*i),m(2,4*i+1)],i=0..4),
  seq([m(1,4*i),m(2,4*i-1)],i=0..4),
  seq([m(2,4*i+1),m(3,4*i+2)],i=0..4),
  seq([m(2,4*i-1),m(3,4*i-2)],i=0..4),
  seq([m(3,4*i+2),m(4,4*i+2)],i=0..4),
  seq([m(4,4*i+2),2],i=0..4),
  seq([m(1,i),m(1,i+1)],i=0..19),
  seq([m(3,i),m(3,i+1)],i=0..19),
  NULL
 ]:

 T["icosahedron_edges"] := sort(map(sort,T["icosahedron_edges"])):

 T["icosahedron_basic_vertices"] :=
  sort([1,2,seq(m(1,4*i),i=0..4),seq(m(3,4*i+2),i=0..4)]);
  
 T["icosahedron_basic_edges"] := [
  seq([ 1  , m(1,4*i)],i=0..4),
  seq([m(1,4*i),m(3,4*i+2)],i=0..4),
  seq([m(1,4*i),m(3,4*i-2)],i=0..4),
  seq([m(3,4*i+2),2],i=0..4),
  seq([m(1,4*i),m(1,4*(i+1))],i=0..4),
  seq([m(3,4*i+2),m(3,4*i-2)],i=0..4),
  NULL
 ]:

 T["icosahedron_basic_edges"] := sort(map(sort,T["icosahedron_basic_edges"])):

 T["icosahedron_basic_faces"] := [
  seq([1,m(1,4*i),m(1,4*(i+1))],i=0..4),
  seq([m(1,4*i),m(3,4*i+2),m(1,4*i+4)],i=0..4),
  seq([m(3,4*i-2),m(1,4*i),m(3,4*i+2)],i=0..4),
  seq([2,m(3,4*i+2),m(3,4*i-2)],i=0..4),
  NULL
 ]:

 T["icosahedron_basic_faces"] := sort(map(sort,T["icosahedron_basic_faces"])):

 w := table():

 for k from 1 to 20 do 
  f := T["icosahedron_basic_faces"][k];
  w[k] := (v[f[1]] +~ v[f[2]] +~ v[f[3]]) /~ 3;
  w[k] := w[k] /~ add(w[k][i]^2,i=1..3);
 od:
 
 T["icosahedron_forms"] := eval(w):

 T["icosahedron_norm"] := (x) ->
  max(seq(add(x[i]*w[j][i],i=1..3),j=1..20));

 vi := table():

 for i from 1 to n do
  vi[i] := v[i] /~ T["icosahedron_norm"](v[i]);
 od:

 T["icosahedron_embedding"] := eval(vi);

 ico_oct_complex := eval(T):

 return eval(T);
end:

`subdivide/ico_oct_complex` := proc(T)
 local T0,T1,ix,n0,V0,i,x;
 
 T0 := `triangular_subdivision/simplicial_complex`(T):
 `normalise_embedding/simplicial_complex`(T0):
 T0["normal"] := copy(T0["embedding"]):

 T0["octahedron_edges"]  := select(e -> nops(e[1]) = 1 and member(e[2],T["octahedron_edges"] ),T0["edges"]):
 T0["icosahedron_edges"] := select(e -> nops(e[1]) = 1 and member(e[2],T["icosahedron_edges"]),T0["edges"]):
 ix := table():
 V0 := T0["vertices"]:
 n0 := nops(V0):
 for i from 1 to n0 do ix[V0[i]] := i; od:
 T1 := table():
 T1["vertices"] := [seq(i,i=1..n0)]:
 T1["edges"] := map(e -> [ix[e[1]],ix[e[2]]],T0["edges"]):
 T1["faces"] := map(f -> [ix[f[1]],ix[f[2]],ix[f[3]]],T0["faces"]):
 T1["max_simplices"] := T1["faces"]:
 T1["octahedron_edges"]  := map(e -> [ix[e[1]],ix[e[2]]],T0["octahedron_edges"]):
 T1["icosahedron_edges"] := map(e -> [ix[e[1]],ix[e[2]]],T0["icosahedron_edges"]):
 T1["octahedron_basic_vertices"]  := T["octahedron_basic_vertices"]:
 T1["octahedron_basic_edges"]     := T["octahedron_basic_edges"]:
 T1["octahedron_basic_faces"]     := T["octahedron_basic_faces"]:
 T1["icosahedron_basic_vertices"] := T["icosahedron_basic_vertices"]:
 T1["icosahedron_basic_edges"]    := T["icosahedron_basic_edges"]:
 T1["icosahedron_basic_faces"]    := T["icosahedron_basic_faces"]:

 T1["icosahedron_forms"] := copy(T["icosahedron_forms"]):
 T1["icosahedron_norm"]  := copy(T["icosahedron_norm"]):

 T1["embedding_dim"] := 3:
 T1["embedding"] := table():
 T1["normal"] := table():
 T1["sphere_embedding"]      := table():
 T1["octahedron_embedding" ] := table():
 T1["icosahedron_embedding"] := table():

 for i from 1 to n0 do 
  x := T0["embedding"][V0[i]];
  x := x /~ evalf(sqrt(add(x[i]^2,i=1..3)));
  T1["embedding"][i]        := x;
  T1["normal"][i]           := x;
  T1["sphere_embedding"][i] := x;
  x := x /~ add(abs(x[i]),i=1..3);
  T1["octahedron_embedding"][i] := x;
  x := x /~ T1["icosahedron_norm"](x);
  T1["icosahedron_embedding"][i] := x;
 od:

 return eval(T1):
end:

`find_paths/ico_oct_complex` := proc(T)
 local k,E,P,E0,e,e0;
 
 for k in ["octahedron","icosahedron"] do 
  E := {op(T[cat(k,"_edges")])};
  P := NULL:

  while E <> {} do 
   e := E[1];
   E := E minus {e};
   E0 := select(e0 -> member(e[-1],e0),E);
   while E0 <> {} do
    e0 := E0[1];
    if e0[1] = e[-1] then
     e := [op(e),e0[2]];
    else 
     e := [op(e),e0[1]];
    fi;
    E := E minus {e0};
    E0 := select(e0 -> member(e[-1],e0),E);
   od;
   P := P,e;
  od:
  T[cat(k,"_paths")] := [P];
 od:
end:

`make_plots/ico_oct_complex` := proc(T)
 local v;
 
 T["embedding"] := copy(T["octahedron_embedding"]);
 `plot/simplicial_complex`(T):
 `surface_plot/simplicial_complex`(T):
 T["octahedron_plot"] := T["plot"];
 T["octahedron_surface_plot"] := T["surface_plot"];
 
 T["embedding"] := copy(T["icosahedron_embedding"]);
 `plot/simplicial_complex`(T):
 `surface_plot/simplicial_complex`(T):
 T["icosahedron_plot"] := T["plot"];
 T["icosahedron_surface_plot"] := T["surface_plot"];
 
 T["embedding"] := copy(T["sphere_embedding"]);
 `plot/simplicial_complex`(T):
 `surface_plot/simplicial_complex`(T):
 T["sphere_plot"] := T["plot"];
 T["sphere_surface_plot"] := T["surface_plot"];

 v := eval(T["embedding"]);
 
 T["octahedron_arc_plot"] :=
  display(
   seq(line(v[e[1]],v[e[2]],colour=blue,thickness=4),e in T1["octahedron_edges"]),
   scaling=constrained,axes=none);

 T["icosahedron_arc_plot"] :=
  display(
   seq(line(v[e[1]],v[e[2]],colour=green,thickness=4),e in T1["icosahedron_edges"]),
   scaling=constrained,axes=none);

 T["octahedron_line_plot"] :=
  display(
   seq(line(v[e[1]],v[e[2]],colour=blue,thickness=4),e in T1["octahedron_basic_edges"]),
   scaling=constrained,axes=none);

 T["icosahedron_line_plot"] :=
  display(
   seq(line(v[e[1]],v[e[2]],colour=green,thickness=4),e in T1["icosahedron_basic_edges"]),
   scaling=constrained,axes=none);

end:

`make_javascript/ico_oct_complex` := proc(T)
 local shift,s,E,i,n;

 shift := proc(u)
  if type(u,list) then
   return map(shift,u);
  else
   return u - 1;
  fi;
 end:
 
 n := nops(T["vertices"]);

 s := [
  ["vertices",                    sprintf("%A",[seq(i,i=0..n-1)])],
  ["edges",                       sprintf("%A",shift(T["edges"]))],
  ["faces",                       sprintf("%A",shift(T["faces"]))],
  ["octahedron_edges",            sprintf("%A",shift(T["octahedron_edges"]))],
  ["icosahedron_edges",           sprintf("%A",shift(T["icosahedron_edges"]))],
  ["octahedron_paths",            sprintf("%A",shift(T["octahedron_paths"]))],
  ["icosahedron_paths",           sprintf("%A",shift(T["icosahedron_paths"]))],
  ["octahedron_basic_vertices",   sprintf("%A",shift(T["octahedron_basic_vertices"]))],
  ["octahedron_basic_edges",      sprintf("%A",shift(T["octahedron_basic_edges"]))],
  ["octahedron_basic_faces",      sprintf("%A",shift(T["octahedron_basic_faces"]))],
  ["icosahedron_basic_vertices",  sprintf("%A",shift(T["icosahedron_basic_vertices"]))],
  ["icosahedron_basic_edges",     sprintf("%A",shift(T["icosahedron_basic_edges"]))],
  ["icosahedron_basic_faces",     sprintf("%A",shift(T["icosahedron_basic_faces"]))]
 ]:

 E := copy(T["sphere_embedding"]):
 for i from 1 to n do E[i] := evalf[3](E[i]): od:
 s := [op(s),["sphere_embedding",sprintf("%A",[seq(E[i],i=1..n)])]]:
 E := copy(T["octahedron_embedding"]):
 for i from 1 to n do E[i] := evalf[3](E[i]): od:
 s := [op(s),["octahedron_embedding",sprintf("%A",[seq(E[i],i=1..n)])]]:
 E := copy(T["icosahedron_embedding"]):
 for i from 1 to n do E[i] := evalf[3](E[i]): od:
 s := [op(s),["icosahedron_embedding",sprintf("%A",[seq(E[i],i=1..n)])]]:

 s := map(u -> sprintf("\"%s\" : %s,\n",u[1],u[2]),s);
 s := cat("{\n",op(s),sprintf("\"num_vertices\" : %d\n}\n",n));

 T["javascript"] := s;
 return s;
end:



ico_oct_complex := make_ico_oct_complex():
