# A raw simplicial complex is a set of nonempty finite sets, no two
# of which are  contained in each other.  We take this as representing
# a simplicial complex, with the specified sets as the maximal simplices.
#
# A (cooked) simplicial complex is a table with various fields which
# gives a more structured representation of the data.

`is_element/raw_simplicial_complexes` := proc(K)
 global reason;
 local n,i,j;

 if not(type(K,set(set)) or type(K,set(list)) or type(K,list(set)) or type(K,list(list))) then 
  reason := ["is_element/raw_simplicial_complexes","K is not a set/list of set/lists",K];
  return false;
 fi;

 if member({},K) or member([],K) then
  reason := ["is_element/raw_simplicial_complexes","K contains the empty set",K];
  return false;
 fi;

 n := nops(K);

 for i from 1 to n-1 do 
  for j from i+1 to n do
   if {op(K[i])} minus {op(K[j])} = {} then
    reason := ["is_element/raw_simplicial_complexes","K[i] and K[j] are nested",i,j,K];
    return false;
   fi;
  od;
 od;

 return true;
end:

`vertices/raw_simplicial_complex` := (K) -> map(op,{op(K)});

`is_simplex/raw_simplicial_complex` := proc(K,s)
 local s0,u;
 
 if not(type(s,{list,set})) then return false; fi;
 
 s0 := {op(s)};
 if s0 = {} then return false; fi;
 
 for u in K do
  if s0 minus {op(u)} = {} then
   return true;
  fi;
 od:
 return false;
end:

`is_element/simplicial_complexes` := proc(T)
 if not(type(T,table)) then
  return false;
 fi;

 if not(`is_element/raw_simplicial_complexes`(T["max_simplices"])) then
  return false;
 fi;

 if T["vertices"] <> `vertices/raw_simplicial_complex`(T["max_simplices"]) then
  return false;
 fi;

 return true;
end:

`is_simplex/simplicial_complex` := proc(T,s)
 return `is_simplex/raw_simplicial_complex`(T["max_simplices"],s);
end:

`all_simplices/raw_simplicial_complex` := proc(K)
 local V,K0;
 V := `vertices/raw_simplicial_complex`(K);
 K0 := map(s -> {op(s)},{op(K)});
 K0 := map(op,map(combinat[powerset],K0)) minus {{}};
 K0 := map(s -> sort([op(s)]),K0);
 return K0;
end;

`normalise/raw_simplicial_complex` := proc(K)
 local K0,K1,n,i,j,ok;
 K0 := [op(K)];
 K0 := map(s -> {op(s)},K0);
 K0 := sort(K0,(s,t) -> nops(s) <= nops(t));
 n := nops(K0);
 K1 := NULL;
 for i from 1 to n do
  ok := true;
  for j from i + 1 to n do
   if K0[i] minus K0[j] = {} then
    ok := false;
    break;
   fi;
  od;
  if ok then K1 := K1,K0[i]; fi;
 od;
 K1 := [K1];
 K1 := map(s -> sort([op(s)]),K1);
 return K1;
end:

`cook/raw_simplicial_complex` := proc(K)
 local T;

 T := table();
 T["vertices"] := `vertices/raw_simplicial_complex`(K);
 T["max_simplices"] := K;

 return eval(T);
end;

`edges/raw_simplicial_complex` := proc(K)
 {seq(seq(seq({s[i],s[j]},j=i+1..nops(s)),i=1..nops(s)),s in K)};
end:

`faces/raw_simplicial_complex` := proc(K)
 {seq(seq(seq(seq({s[i],s[j],s[k]},k=j+1..nops(s)),j=i+1..nops(s)),i=1..nops(s)),s in K)};
end:

`components/simplicial_complex` := proc(T)
 local P,Q,R,s;
 
 P := {seq({v},v in T["vertices"])};
 for s in T["max_simplices"] do
  Q,R := selectremove(c -> c intersect {op(s)} = {},P);
  P := {map(op,R),op(Q)};
 od:
 T["components"] := P;
 return P;
end:

`reindex/simplicial_complex` := proc(T,f)
 local T0,v;
 
 T0 := table();
 T0["vertices"] := map(f,T["vertices"]);
 T0["max_simplices"] := map(s -> map(f,s),T["max_simplices"]);

 if member(["embedding"],[indices(T)]) then
  T0["embedding_dim"] = T["embedding_dim"];
  for v in T["vertices"] do
   T0["embedding"][f(v)] := T["embedding"][v];
  od:
 fi;

 return eval(T0);
end:

`set_edges/simplicial_complex` := proc(T,force := false)
 if type(T["edges"],{list,set}) and not force then
  return T["edges"];
 fi;
 T["edges"] := `edges/raw_simplicial_complex`(T["max_simplices"]);
 return T["edges"];
end:

`set_faces/simplicial_complex` := proc(T,force := false)
 if type(T["faces"],{list,set}) and not force then
  return T["faces"];
 fi;
 T["faces"] := `faces/raw_simplicial_complex`(T["max_simplices"]);
 return T["faces"];
end:

`set_all_simplices/simplicial_complex` := proc(T,force := false)
 local K,d,i;

 if (type(T["all_simplices"],{list,set}) and not(force)) then
  return T["all_simplices"];
 fi;
 
 K := T["max_simplices"];
 T["all_simplices"] := `all_simplices/raw_simplicial_complex`(K);
 d := `dim/raw_simplicial_complex`(K);
 T["dim"] := d;
 T["simplices_by_dim"] := table():
 for i from 0 to d do
  T["simplices_by_dim"][i] :=
   select(s -> nops(s) = i + 1,T["all_simplices"]);
 od:
 return T["all_simplices"];
end:

`dim/raw_simplicial_complex` := (K) -> max(map(nops,K)) - 1;

`dim/simplicial_complex` := proc(T)
 local d;
 d := `dim/raw_simplicial_complex`(T["maximal_simplices"]);
 T["dim"] := d;
 return d;
end:

`euler_characteristic/raw_simplicial_complex` := proc(K)
 local L;
 
 L := `all_simplices/raw_simplicial_complex`(K);
 L := [op(L)];
 L := map(s -> (-1)^(nops(s)+1),L);
 return `+`(op(L));
end:

`euler_characteristic/simplicial_complex` := proc(T)
 local L;
 
 if not(type(T["all_simplices"],{set,list})) then
  T["all_simplices"] := `all_simplices/raw_simplicial_complex`(T["max_simplices"]);
 fi;
  
 L := T["all_simplices"];
 L := [op(L)];
 L := map(s -> (-1)^(nops(s)+1),L);
 return `+`(op(L));
end:

`has_embedding/simplicial_complex` := proc(T)
 if type(T["embedding"],table) then
  if not(type(T["embedding_dim"],nonnegint))
     and nops(T["vertices"]) > 0 then
   T["embedding_dim"] := nops(T["embedding"][T["vertices"][1]]);
  fi;
  return true;
 else
  return false;
 fi;
end:

# Condensation replaces a raw simplicial complex by an equivalent one in
# which the vertex set has the form {1,...,n} for some n.

`is_condensed/raw_simplicial_complex` := proc(K)
 local V,n;
 V := `vertices/raw_simplicial_complex`(K);
 n := nops(V);
 return evalb(V = {seq(i,i=1..n)});
end;

`condense/raw_simplicial_complex` := proc(K)
 local V,ix,n,i,L;
 V := `vertices/raw_simplicial_complex`(K);
 n := nops(V);
 for i from 1 to n do
  ix[V[i]] := i;
 od:
 L := map(s -> map(v -> ix[v],s),K);
 return L;
end:

`is_condensed/simplicial_complex` := proc(T)
 local V,n;
 V := {op(T["vertices"])};
 n := nops(V);
 return evalb(V = {seq(i,i=1..n)});
end;

`condense/simplicial_complex` := proc(T)
 local V,T0,n,i;

 T0 := table():
 V := T["vertices"];
 n := nops(V);
 
 T0["max_simplices"] := `condense/raw_simplicial_complex`(T["max_simplices"]);
 T0["vertices"] := {seq(i,i=1..n)};

 if `has_embedding/simplicial_complex`(T) then
  T0["embedding_dim"] := T["embedding_dim"];
  T0["embedding"] := table();
  for i from 1 to n do
   T0["embedding"][i] := T["embedding"][V[i]];
  od;
 fi;

 return eval(T0);
end:

`restrict/simplicial_complex` := proc(T,V0)
 local V1,T0,K0,P0,P,v;
 
 V1 := {op(V0)};
 if V1 minus {op(T["vertices"])} <> {} then
  error "V0 is not a subset of the vertex set";
 fi;

 T0 := table();
 T0["vertices"] := V0;
 K0 := map(s -> {op(s)} intersect V1,T["max_simplices"]);
 K0 := `normalise/raw_simplicial_complex`(K0);
 T0["max_simplices"] := K0;

 P := T["embedding"];
 if type(P,table) then
  T0["embedding_dim"] := T["embedding_dim"];
  P0 := table():
  for v in V0 do
   P0[v] := P[v];
  od:
  T0["embedding"] := eval(P0);
 fi;

 return eval(T0);
end:

`disjoint_union/simplicial_complex` := proc(T,U)
 local n,U0,TU,v;
 
 if `is_condensed/simplicial_complex`(T) and
    `is_condensed/simplicial_complex`(U) then
  n := nops(T["vertices"]);
  U0 := `reindex/simplicial_complex`(U,i -> i + n);
 else
  if {op(T["vertices"])} intersect {op(U["vertex_set"])} <> {} then
   error "Vertex sets are not disjoint";
  fi;
  U0 := eval(U);
 fi;

 TU := table();
 TU["vertices"] := [op(T["vertices"]),op(U0["vertices"])];
 TU["max_simplices"] := [op(T["max_simplices"]),op(U0["max_simplices"])];

 if `has_embedding/simplicial_complex`(T) and
    `has_embedding/simplicial_complex`(U0) and
    T["embedding_dim"] = U0["embedding_dim"] then
  TU["embedding_dim"] := T["embedding_dim"];
  TU["embedding"] := table();
  for v in T["vertices"] do
   TU["embedding"][v] := T["embedding"][v];
  od;
  for v in U0["vertices"] do
   TU["embedding"][v] := U0["embedding"][v];
  od;
 fi;

 return eval(TU);
end:

`join/simplicial_complex` := proc(T,U)
 local n,m,U0,TU,v;
 
 if `is_condensed/simplicial_complex`(T) and
    `is_condensed/simplicial_complex`(U) then
  n := nops(T["vertices"]);
  U0 := `reindex/simplicial_complex`(U,i -> i + n);
 else
  if {op(T["vertices"])} intersect {op(U["vertex_set"])} <> {} then
   error "Vertex sets are not disjoint";
  fi;
  U0 := eval(U);
 fi;

 TU := table();
 TU["vertices"] := [op(T["vertices"]),op(U0["vertices"])];
 TU["max_simplices"] := [
  op(T["max_simplices"]),
  op(U0["max_simplices"]),
  seq(seq([op(s),op(t)],t in U0["max_simplices"]),s in T["max_simplices"])
 ];

 if `has_embedding/simplicial_complex`(T) and
    `has_embedding/simplicial_complex`(U0) then
  n := T["embedding_dim"];
  m := U0["embedding_dim"];
  TU["embedding_dim"] := n+m+1;
  TU["embedding"] := table();
  for v in T["vertices"] do
   TU["embedding"][v] := [op(T["embedding"][v]),0$(m+1)];
  od;
  for v in U0["vertices"] do
   TU["embedding"][v] := [0$n,1,op(U0["embedding"][v])];
  od;
 fi;

 return eval(TU);
end:


# The following function checks whether we have an embedding of a raw
# simplicial complex K in R^d.  The argument d is the embedding dimension.
# The argument a should be a list or table, so that a[i] is an element
# of R^d for each index i appearing in K.

`is_embedding/raw_simplicial_complex` := proc(K,d,a)
 global reason;
 local m,Kl,Ka,i,j,k,eqd,bc,rr,AA,BB,u,v,w,p,M;
 
 m := nops(K);
 Kl := [op(K)];
 Ka := map(s -> [seq(a[i],i in s)],Kl);

 for u in Ka do
  if not `is_element/simplices`(d)(u) then
   reason := ["is_embedding/simplicial_complex","u is not a simplex in R^d",u,d,reason];
   return false;
  fi;
 od;

 eqd := evalb({d+1,op(map(nops,Kl))} = {d+1});
 
 bc := map(`barycentre/simplex`(d),Ka):
 rr := map(`radius/simplex`(d),Ka):

 if eqd then
  AA := map(`primal_matrix/simplex`(d),Ka):
  BB := map(A -> 1/A,AA):
 fi;

 for i from 1 to m-1 do
  for j from i+1 to m do
   u := Ka[i];
   v := Ka[j];
   p := {op(K[i])} intersect {op(K[j])};
   w := {seq(a[k],k in p)};
   if not(nops(w) = nops(p) and
          w = {op(u)} intersect {op(v)}) then
    return false;
   fi;
   if evalf(`d_2/R`(d)(bc[i],bc[j]) - rr[i] - rr[j]) <= 0 then
    if eqd then
     M := <BB[i].AA[j],BB[j].AA[j]>;
     if min(seq(max(seq(M[i,j],j=1..d+1)),i=1..2*d+2)) >= 0 then
      if not(`intersect_nicely/simplices`(d)(u,v)) then
       reason := ["is_embedding/simplicial_complex","bad intersection",u,v];
       return false;
      fi;
     fi;
    else
     if not(`intersect_nicely/simplices`(d)(u,v)) then
      reason := ["is_embedding/simplicial_complex","bad intersection",u,v];
      return false;
     fi;
    fi;
   fi;
  od;
 od;

 return true;
end:


`star/simplicial_complex` := proc(T,s)
 local K,P,K0,T0,P0,s0,v;

 K := T["max_simplices"];
 K := map(u -> {op(u)},{op(K)});
 if `is_simplex/raw_simplicial_complex`(K,s) then 
  s0 := {op(s)};
 elif member(s,T["vertices"]) then
  s0 := {s};
 else
  error "Second argument is not a vertex or simplex";
 fi;
 
 K0 := select(u -> s0 minus u = {},K);
 T0 := `cook/raw_simplicial_complex`(K0);

 P := T["embedding"];
 if type(P,table) then
  T0["embedding_dim"] := T["embedding_dim"];
  P0 := table():
  for v in T0["vertices"] do
   P0[v] := P[v];
  od:
  T0["embedding"] := eval(P0);
 fi;

 return eval(T0);
end:

`link/simplicial_complex` := proc(T,s)
 local K,s0,T0,T1;

 K := T["max_simplices"];
 K := map(u -> {op(u)},{op(K)});
 if `is_simplex/raw_simplicial_complex`(K,s) then 
  s0 := {op(s)};
 elif member(s,T["vertices"]) then
  s0 := {s};
 else
  error "Second argument is not a vertex or simplex";
 fi;

 T0 := `star/simplicial_complex`(T,s);
 T1 := `restrict/simplicial_complex`(T0,{op(T0["vertices"])} minus s0);
 return eval(T1);
end:

# For a connected one-manifold (possibly with boundary), list the
# vertices in natural order.  If the complex is a circle, then
# the first vertex in the list is repeated at the end.

`track/simplicial_complex` := proc(T,v_)
 local V,K,L,E,v,w,t,xx;
 
 if nops(T["vertices"]) <= 1 then
  return [op(T["vertices"])];
 fi;
 
 if `dim/simplicial_complex`(T) > 1 then
  error "Dimension is bigger than one";
 fi;

 if nops(`components/simplicial_complex`(T)) > 1 then
  error "Complex is not connected";
 fi;

 V := T["vertices"];
 if type(V,set) then V := sort([op(V)]); fi;
 
 K := {op(map(s -> {op(s)},T["max_simplices"]))};
 L := table();

 for v in V do
  L[v] := select(u -> u <> v and member({u,v},K),V);
 od;

 if max(seq(nops(L[v]),v in V)) > 2 then
  error "Complex is branched";
 fi;

 E := select(v -> nops(L[v]) = 1, V);
 if E = [] then
  if nargs > 1 then
   if member(v_,V) then
    v := v_;
   else
    error "Invalid starting point";
   fi;
  else
   v := V[1];
  fi;
 else
  if nargs > 1 then
   if member(v_,E) then
    v := v_;
   else
    error "Invalid starting point";
   fi;
  else
   v := E[1];
  fi;
 fi;
 
 w := L[v][-1];
 t := [v,w];
 xx := {op(L[w])} minus {op(t)};
 while xx <> {} do
  w := xx[1];
  t := [op(t),w];
  xx := {op(L[w])} minus {op(t)};
 od;

 if E = [] then t := [op(t),t[1]]; fi;
 
 return t;
end:

`barycentric_subdivision/raw_simplicial_complex` := proc(K)
 local V,n,i,j,P,L,d,s,t,p;
 
 V := `all_simplices/raw_simplicial_complex`(K);

 n := max(map(nops,V));
 for i from 1 to n do
  P[i] := combinat[permute](i);
 od:

 L := NULL;
 for s in K do
  d := nops(s);
  for p in P[d] do
   t := {seq(sort([seq(s[p[i]],i=1..j)]),j=1..d)};
   L := L,t
  od;
 od;

 return({L});
end:

`barycentric_subdivision/simplicial_complex` := proc(T)
 local K,E,K0,V0,T0,E0,d,s,x,v;

 K := T["max_simplices"];
 K0 := `barycentric_subdivision/raw_simplicial_complex`(K);
 V0 := `vertices/raw_simplicial_complex`(K0);
 T0 := table():
 T0["vertices"] := V0;
 T0["max_simplices"] := K0;

 E := T["embedding"];
 if type(E,table) then
  d := T["embedding_dim"];
  T0["embedding_dim"] := d;
  E0 := table();
  for s in V0 do
   x := [0$d];
   for v in s do x := x +~ E[v]; od;
   x := x /~ nops(s);
   E0[s] := x;
  od;
  T0["embedding"] := eval(E0);
 fi;

 return eval(T0);
end:

`triangular_subdivision/simplicial_complex` := proc(T)
 local V,E,F,V0,E0,E1,E2,F0,T0,v,e,f,d,P,P0;

 if `dim/simplicial_complex`(T) > 2 then
  error "Triangular subdivision is only for complexes of dimension <= 2";
  # There is a version for dimension 3, with an extra simplex at the
  # barycentre of each tetrahedron as well as each edge, but we have
  # not coded it yet.  Perhaps there is a version where we adjoin the
  # barycentre of each simplex of odd dimension?  Note that even in
  # dimension two, this triangular subdivision is different from, and
  # more symmetrical than, the edgewise subdivision.  The edgewise
  # subdivision needs some kind of order on the vertices.
 fi;
 V := T["vertices"];
 E := `edges/raw_simplicial_complex`(T["max_simplices"]);
 F := `faces/raw_simplicial_complex`(T["max_simplices"]);
 E := map(e -> sort([op(e)]),E);
 E := sort([op(E)]);
 F := map(f -> sort([op(f)]),F);
 F := sort([op(F)]);
 
 V0 := [seq([v],v in V),seq(sort([op(e)]),e in E)];
 E0 := [seq(op([[[e[1]],e],[[e[2]],e]]), e in E),
        seq(op([
	 [[f[1],f[2]],[f[1],f[3]]],
	 [[f[1],f[2]],[f[2],f[3]]],
	 [[f[1],f[3]],[f[2],f[3]]]	 
	]), f in F)
       ];
 F0 := [seq(op([
         [[f[1]],[f[1],f[2]],[f[1],f[3]]],
         [[f[2]],[f[1],f[2]],[f[2],f[3]]],
         [[f[3]],[f[1],f[3]],[f[2],f[3]]],
	 [[f[1],f[2]],[f[1],f[3]],[f[2],f[3]]]
        ]),f in F)];

 T0 := table():
 T0["vertices"] := V0;
 T0["edges"] := E0;
 T0["faces"] := F0;

 E1 := {op(map(f -> op({[f[1],f[2]],[f[1],f[3]],[f[2],f[3]]}),F0))};
 E2 := {op(E0)} minus E1;
 E2 := [op(E2)];
 T0["max_simplices"] := [op(E2),op(F0)];

 P := T["embedding"];
 if type(P,table) then
  d := T["embedding_dim"];
  T0["embedding_dim"] := d;
  P0 := table();
  for v in V do
   P0[[v]] := P[v];
  od:

  for e in E do
   P0[e] := (P[e[1]] +~ P[e[2]]) /~ 2;
  od:
  T0["embedding"] := eval(P0);
 fi;

 return T0;
end:

`star_subdivide/simplicial_complex` := proc(T,s)
 local n,V,K,K1,S0,S1,S2,s0,s1,s2,u,P,d,x,v;

 if nops(s) = 1 then return; fi;
 
 n := nops(T["vertices"]);
 V := [seq(i,i=1..n)];
 if {op(T["vertices"])} <> {op(V)} then
  error "Star subdivision is only implemented for condensed complexes";
 fi;

 K := T["max_simplices"];
 K := map(u -> {op(u)},{op(K)});
 
 s0 := {op(s)};
 S1,S0 := selectremove(u -> s0 minus {op(u)} = {},K);
 S2 := {seq(seq(u minus {v},v in s),u in S1)};

 K1 := {op(S0),seq({op(u),n+1},u in S2)};
 K1 := map(u -> sort([op(u)]),K1);
 K1 := sort([op(K1)]);
 
 T["vertices"] := [seq(i,i=1..n+1)];
 T["max_simplices"] := K1;

 P := T["embedding"];
 if type(P,table) then
  d := T["embedding_dim"];
  x := [0$d];
  for v in s do x := x +~ P[v]; od;
  x := evalf(x /~ nops(s));
  P[n+1] := x;
 fi;
end:

# This function can be applied to a simplicial surface T with a
# vertex v whose link is an octagon, thought of as a bisected
# square.  The vertex w is the midpoint of one edge of the square.
# This function performs a subdivision that affects the star of v
# by adding four new vertices at the midpoints of the edges
# joining v to the corners of the square.  It returns a new vertex
# w', so that the process can be repeated using v and w'.
`square_refine/simplicial_complex` := proc(T,v,w)
 local n,K,L,W,P,old_faces,new_faces;
 if not(`is_condensed/simplicial_complex`(T)) then
  error "Complex is not condensed";
 fi;

 n := nops(T["vertices"]);
 L := `link/simplicial_complex`(T,v);
 W := `track/simplicial_complex`(L,w);

 if nops(W) <> 9 then
  error "Link is not square";
 fi;

 old_faces := {seq({v,W[i],W[i+1]},i=1..8)};
 new_faces := {
  {v,W[1],n+1},{v,n+1,W[3]},{v,W[3],n+2},{v,n+2,W[5]},
  {v,W[5],n+3},{v,n+3,W[7]},{v,W[7],n+4},{v,n+4,W[1]},
  {W[1],W[2],n+1},{W[2],W[3],n+1},{W[3],W[4],n+2},{W[4],W[5],n+2},
  {W[5],W[6],n+3},{W[6],W[7],n+3},{W[7],W[8],n+4},{W[8],W[1],n+4}
 };

 T["vertices"] := [seq(i,i=1..n+4)];
 K := T["max_simplices"];
 K := {op(map(s -> {op(s)},K))};
 K := (K minus old_faces) union new_faces;
 K := map(s -> sort([op(s)]),K);
 K := sort([op(K)]);
 T["max_simplices"] := K;

 if `has_embedding/simplicial_complex`(T) then
  P := T["embedding"];
  P[n+1] := (P[v] +~ P[W[2]]) /~ 2;
  P[n+2] := (P[v] +~ P[W[4]]) /~ 2;
  P[n+3] := (P[v] +~ P[W[6]]) /~ 2;
  P[n+4] := (P[v] +~ P[W[8]]) /~ 2;
 fi;

 return n+1;
end:

`normalise_embedding/simplicial_complex` := proc(T)
 local d,P,v,x;
 
 d := T["embedding_dim"];
 P := T["embedding"];
 for v in T["vertices"] do
  x := evalf(P[v]);
  if not(type(x,[numeric $d])) then
   print([v,x]);
   error "Bad vertex position";
  fi;
  x := evalf(x /~ sqrt(add(x[i]^2,i=1..d)));
  P[v] := x;
 od:
end:

`plot/raw_simplicial_complex` := proc(K,d,a)
 local V,E,F,e,f,P;

 V := `vertices/raw_simplicial_complex`(K);
 E := `edges/raw_simplicial_complex`(K);
 F := `faces/raw_simplicial_complex`(K);

 P :=
  seq(point(a[v]),v in V),
  seq(line(a[e[1]],a[e[2]]),e in E),
  seq(polygon([a[f[1]],a[f[2]],a[f[3]]],colour=red),f in F);

 return display(P,scaling=constrained,axes=none):
end:

`plot/simplicial_complex` := proc(T)
 local V,E,F,a;
 
 `set_edges/simplicial_complex`(T);
 `set_faces/simplicial_complex`(T);
 V := T["vertices"];
 E := T["edges"];
 F := T["faces"];
 a := T["embedding"];
 T["plot"] := display(
  seq(point(a[v]),v in V),
  seq(line(a[e[1]],a[e[2]]),e in E),
  seq(polygon([a[f[1]],a[f[2]],a[f[3]]],colour=red),f in F),
  scaling=constrained,axes=none):
 return T["plot"];
end:

`surface_plot/simplicial_complex` := proc(T)
 local V,E,F,a;
 
 `set_faces/simplicial_complex`(T);
 F := T["faces"];
 a := T["embedding"];
 T["surface_plot"] := display(
  seq(polygon([a[f[1]],a[f[2]],a[f[3]]],style=patchnogrid),f in F),
  scaling=constrained,axes=none):
 return T["surface_plot"];
end:

`vertex_labels/simplicial_complex` := proc(T)
 if T["embedding_dim"] = 2 then
  display(seq(textplot([op(T["embedding"][v]),sprintf("%A",v)]),v in T["vertices"]),
          axes=none,scaling=constrained);
 elif T["embedding_dim"] = 3 then
  display(seq(textplot3d([op(T["embedding"][v]),sprintf("%A",v)]),v in T["vertices"]),
          axes=none,scaling=constrained);
 else
  error "No 2 or 3 dimensional embedding";
 fi;
end:

`set_javascript/simplicial_complex` := proc(T)
 local V,F,F1,P,N,V_string,N_string,F_string,T_string,f,f1,n1,n2;
 
 if not(`has_embedding/simplicial_complex`(T)) then
  error "Complex has no embedding data";
 fi;

 if T["embedding_dim"] <> 3 then
  error "Complex is not in R3";
 fi;

 V := T["vertices"];
 P := eval(T["embedding"]);
 `set_faces/simplicial_complex`(T);
 F := T["faces"];
 F := sort([op(map(f -> sort([op(f)]),F))]);
 
 V_string :=
  cat("[",StringTools[Join]([seq(sprintf("%A",P[v]),v in V)],","),"]");

 if type(T["normal"],table) then
  N := eval(T["normal"]);
  N_string := 
   cat("[",StringTools[Join]([seq(sprintf("%A",N[v]),v in V)],","),"]");
  F1 := NULL;
  for f in F do
   n1 := cross_product(P[f[2]] -~ P[f[1]],P[f[3]] -~ P[f[1]]);
   n2 := N[f[1]] +~ N[f[2]] +~ N[f[3]];
   if add(n1[i] * n2[i],i=1..3) > 0 then 
    f1 := [f[1]-1,f[2]-1,f[3]-1];
   else 
    f1 := [f[1]-1,f[3]-1,f[2]-1];
   fi;
   F1 := F1,f1;
  od:
  F1 := [F1];
  F_string := 
   cat("[",StringTools[Join]([seq(sprintf("%A",f),f in F1)],","),"]");
  T_string :=
   sprintf("object_data = {\npositions:\n%s,\nnormals:\n%s,indices:\n%s }",
           V_string,N_string,F_string);
 else
  F_string := 
   cat("[",StringTools[Join]([seq(sprintf("%A",f),f in F)],","),"]");
  T_string :=
   sprintf("object_data = {\npositions:\n%s,indices:\n%s }",
           V_string,F_string);
 fi;

 T["javascript"] := T_string;
 
 return T_string;
end:
