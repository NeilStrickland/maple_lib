`is_element/digraphs` := (V::set) -> proc(E)
 if not(`is_element/autorel`(V)(E)) then
  return false;
 fi;

 if not(`is_antisymmetric/autorel`(V)(E)) then
  return false;
 fi;

 return true;
end:

`is_leq/digraphs` := (V::set) -> (E0,E1) -> evalb(E0 minus E1 = {}):

`list_elements/digraphs` := proc(V::set)
 local n,EE,i,j,a,b;
 
 n := nops(V);
 EE := [{}];
 for i from 1 to n-1 do
  for j from i+1 to n do
   a := V[i];
   b := V[j];
   EE := [op(EE),
          seq(E union {[a,b]},E in EE),
          seq(E union {[b,a]},E in EE)];
  od;
 od;

 return EE; 
end:

`count_elements/digraphs` := (V::set) -> 3^(nops(V)*(nops(V)-1)/2);

`random_element/digraphs` := (V::set) -> proc()
 local n,E,r,i,j,a,b,x;
 
 n := nops(V);
 E := NULL;
 r := rand(-1..1);
 for i from 1 to n-1 do
  for j from i+1 to n do
   a := V[i];
   b := V[j];
   x := r();
   if x = -1 then
    E := E,[b,a];
   elif x = 1 then
    E := E,[a,b];
   fi;
  od;
 od;

 return {E}; 
end:

`neighbour_table/digraphs` := (V) -> proc(E)
 local N,v,e;
 
 N := table();
 for v in V do N[v] := {}; od:
 for e in E do
  N[e[1]] := {op(N[e[1]]),e[2]};
  N[e[2]] := {op(N[e[2]]),e[1]};
 od:

 return eval(N);
end:

`in_neighbour_table/digraphs` := (V) -> proc(E)
 local N,v,e;
 
 N := table();
 for v in V do N[v] := {}; od:
 for e in E do
  N[e[2]] := {op(N[e[2]]),e[1]};
 od:

 return eval(N);
end:

`out_neighbour_table/digraphs` := (V) -> proc(E)
 local N,v,e;
 
 N := table();
 for v in V do N[v] := {}; od:
 for e in E do
  N[e[1]] := {op(N[e[1]]),e[2]};
 od:

 return eval(N);
end:

`component_relation/digraphs` := (V) -> (E) ->
 `transitive_closure/autorel`(V)(
  E union `op/autorel`(V)(E) union `id/autorel`(V)
 );

`components/digraphs` := (V) -> (E) ->
 `block_partition/equiv`(`component_relation/graphs`(V)(E));

`is_connected/digraphs` := (V) -> (E) -> 
 evalb(`component_relation/digraphs`(V)(E) = `top/autorel`(V));

`skeleton/digraphs` := (V::set) -> proc(E)
 local n,V0,E0,ix,i;
 
 n := nops(V);
 V0 := {seq(i,i=1..n)};
 ix := table():
 for i from 1 to n do ix[V[i]] := i; od;
 E0 := map(e -> [ix[e[1]],ix[e[2]]],E);
 return [V0,E0];
end:

`is_element/dipaths` := (V) -> (E) -> proc(p)
 local i,n;
 
 if not type(p,list) then
  return false;
 fi;

 n := nops(p) - 1;

 if n < 0 then 
  return false;
 fi;

 if {op(p)} minus V <> {} then
  return false;
 fi;

 for i from 1 to n do
  if not(member([p[i],p[i+1]],E)) then
   return false;
  fi;
 od;

 return true;
end:

`is_small_element/dipaths` := (V) -> (E) -> (n::nonnegint) -> proc(p)
 return evalb(`is_element/dipaths`(V)(E)(p) and (nops(p) = n+1));
end:

`random_small_element/dipaths` := (V) -> (E) -> (n::nonnegint) -> proc(num_tries := 10)
 local k,p,F;

 if n = 0 then
  if V = {} then
   return FAIL;
  else
   return [random_element_of(V)()];
  fi;
 elif n = 1 then
  if E = {} then
   return FAIL;
  else
   return random_element_of(E)();
  fi;
 fi;
 
 k := num_tries;

 while k > 0 do
  k := k-1;
  p := `random_small_element/dipaths`(V)(E)(n-1)();
  if p <> FAIL then
   F := select(e -> e[2] = p[1],E);
   if F <> {} then
    return [random_element_of(F)()[1],op(p)];
   fi;
  fi;
 od;

 return FAIL;
end:

`list_small_elements/dipaths` := (V) -> (E) -> proc(n::nonnegint)
 option remember;
 local P,Q,p,v,F;
 
 if n = 0 then
  return map(v -> [v],V);
 else
  P := `list_small_elements/dipaths`(V)(E)(n-1);
  Q := NULL;
  for p in P do
   v := p[1];
   F := select(e -> e[2] = v,E);
   Q := Q,seq([e[1],op(p)],e in F);
  od:
  return [Q];
 fi;
end:

`is_leq/dipaths` := NULL;
`count_elements/dipaths` := NULL:
`count_small_elements/dipaths` := NULL:

`length/dipaths` := (V) -> (E) -> (p) -> nops(p) - 1;

`is_trail/dipaths` := proc(p)
 local n,e;
 n := nops(p) - 1;
 e := {seq([p[i],p[i+1]],i=1..n)};
 return evalb(nops(e) = n);
end:

`is_cycle/dipaths` := proc(p)
 local n;
 n := nops(p) - 1;
 return evalb(p[1] = p[n+1] and nops({seq(p[i],i=1..n)}) = n);
end:

`is_small_element/ditrails` := (V) -> (E) -> (n::nonnegint) -> proc(p)
 if not `is_small_element/dipaths`(V)(E)(n)(p) then
  return false;
 fi;

 return `is_trail/dipaths`(p);
end:

`is_element/ditrails` := (V) -> (E) -> proc(p)
 if not `is_element/dipaths`(V)(E)(p) then
  return false;
 fi;

 return `is_trail/dipaths`(p);
end:

`list_small_elements/ditrails` := (V) -> (E) -> proc(n)
 option remember;
 local E0,E1,P,Q,p,v,F;

 if n = 0 then
  return map(v -> [v],V);
 else
  P := `list_small_elements/ditrails`(V)(E)(n-1);
  Q := NULL;
  for p in P do
   E0 := {seq([p[i],p[i+1]],i=1..n-1)};
   E1 := E minus E0;
   v := p[1];
   F := select(e -> e[2] = v,E1);
   Q := Q,seq([e[1],op(p)],e in F);
  od:
  return [Q];
 fi;
end:

`random_small_element/ditrails` := (V) -> (E) -> (n) -> proc(num_tries := 10)
 local k,p,E0,E1,v,F,e;
 
 k := num_tries;

 if n = 0 then
  if V = {} then
   return FAIL;
  else 
   return [random_element_of(V)()];
  fi;
 elif n = 1 then
  if E = {} then
   return FAIL;
  else
   return random_element_of(E)();
  fi;
 fi;
 
 while k > 0 do
  p := `random_small_element/ditrails`(V)(E)(n-1)();
  k := k - 1;
  if p <> FAIL then
   E0 := {seq([p[i],p[i+1]],i=1..n-1)};
   E1 := E minus E0;
   v := p[1];
   F := select(e -> e[2] = v,E1);
   if F <> {} then
    e := random_element_of(F)();
    return [e[1],op(p)];
   fi;
  fi;
 od;

 return FAIL;
end:

`is_leq/ditrails` := NULL:
`count_elements/ditrails` := NULL:
`count_small_elements/ditrails` := NULL:

`roots/digraphs` := (V) -> proc(E)
 V minus map(e -> e[2],E);
end:

`root/digraphs` := (V) -> proc(E)
 local R;
 R := `roots/digraphs`(V)(E);
 if nops(R) = 1 then
  return R[1];
 else
  error "Digraph does not have a unique root";
 fi;
end:

`leaves/digraphs` := (V) -> proc(E)
 V minus map(e -> e[1],E);
end:

`is_forest/digraphs` := (V::set) -> proc(E)
 local NI,NO,R,v,U,U1;
 
 NI := `in_neighbour_table/digraphs`(V)(E);
 NO := `out_neighbour_table/digraphs`(V)(E);
 R := NULL;

 for v in V do
  if nops(NI[v]) > 1 then
   return false;
  elif NI[v] = {} then
   R := R,v;
  fi;
 od;

 R := {R};

 U := R;
 U1 := {op(U),seq(op(NO[v]),v in U)};
 while nops(U1) > nops(U) do
  U := U1;
  U1 := {op(U),seq(op(NO[v]),v in U)};
 od:

 if U <> V then return false; fi;

 return true;
end:

`is_tree/digraphs` := (V) -> (E) ->
 nops(`roots/digraphs`(V)(E)) = 1 and 
  `is_forest/digraphs`(V)(E);

`level_table/forest_digraphs` := (V) -> proc(E)
 local X,N,L,k,v;
 
 X := `roots/digraphs`(V)(E);
 N := `out_neighbour_table/digraphs`(V)(E);
 L := table():
 k := 0;
 while X <> {} do
  for v in X do L[v] := k; od:
  X := map(v -> op(N[v]),X);
  k := k+1;
 od:

 return eval(L);
end:

`shadow_table/forest_digraphs` := (V) -> proc(E)
 local X,Y,Z,S,x,z,N;

 X := `leaves/digraphs`(V)(E);
 Y := V minus X;
 S := table():
 for x in X do S[x] := {x}; od:
 N := `out_neighbour_table/digraphs`(V)(E);
 while Y <> {} do
  Z := select(y -> ((N[y] minus X) = {}),Y);
  if Z = {} then
   error "Something wrong";
  fi;
  z := Z[1];
  S[z] := map(op,{seq(S[u],u in N[z])});
  X := X union {z};
  Y := Y minus {z};
 od:
 return eval(S);
end:

`shadow_set/forest_digraphs` := (V) -> proc(E)
 local S;
 S := `shadow_table/forest_digraphs`(V)(E);
 return {seq(S[v],v in V)};
end:

`is_element/stasheff_digraphs` := (V::set) -> proc(EL)
 local E,L,L0,r,i,TT,rTT;
 if not (type(EL,list) and nops(EL) = 2) then
  return false;
 fi;

 E,L := op(EL);

 if not(`is_tree/digraphs`(V)(E)) then
  return false;
 fi;

 L0 := `leaves/digraphs`(V)(E);
 if not({op(L)} = L0 and nops(L0) = nops(L)) then
  return false;
 fi;

 r := table();
 for i from 1 to nops(L) do r[L[i]] := i; od;

 TT := `shadow_set/forest_digraphs`(V)(E);
 rTT := map(T -> map(v -> r[v],T),TT);

 return `and`(op(map(`is_element/posint_intervals`,rTT)));
end:
