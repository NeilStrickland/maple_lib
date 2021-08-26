`is_element/graphs` := (V::set) -> proc(E)
 if not(`is_element/autorel`(V)(E)) then
  return false;
 fi;

 if not(`is_symmetric/autorel`(V)(E)) then
  return false;
 fi;

 if not(`is_irreflexive/autorel`(V)(E)) then
  return false;
 fi;

 return true;
end:

`is_leq/graphs` := (V::set) -> (E0,E1) -> evalb(E0 minus E1 = {}):

`list_elements/graphs` := proc(V::set)
 local n,E0,EE,i,j;
 
 n := nops(V);
 E0 := {seq(seq([V[i],V[j]],j=i+1..n),i=1..n-1)};
 EE := `list_elements/subsets`(E0);
 EE := map(E -> E union `op/autorel`(V)(E),EE);
 return EE;
end:

`count_elements/graphs` := (V::set) -> 2^(nops(V)*(nops(V)-1)/2);

`random_element/graphs` := (V::set) -> proc()
 local n,E0,E,i,j;
 
 n := nops(V);
 E0 := {seq(seq([V[i],V[j]],j=i+1..n),i=1..n-1)};
 E := `random_element/subsets`(E0)();
 E := E union `op/autorel`(V)(E);
 return E;
end:

`neighbour_table/graphs` := (V) -> proc(E)
 local N,v,e;
 
 N := table();
 for v in V do N[v] := {}; od:
 for e in E do
  N[e[1]] := {op(N[e[1]]),e[2]};
 od:

 return eval(N);
end:

`component_relation/graphs` := (V) -> (E) ->
 `transitive_closure/autorel`(V)(
  E union `id/autorel`(V)
 );

`components/graphs` := (V) -> (E) ->
 `block_partition/equiv`(`component_relation/graphs`(V)(E));

`is_connected/graphs` := (V) -> (E) -> 
 evalb(`component_relation/graphs`(V)(E) = `top/autorel`(V));

`is_forest/graphs` := (V) -> proc(E)
 local CC,V0,E0;
 
 CC := `components/graphs`(V)(E);

 for V0 in CC do
  E0 := select(e -> member(e[1],V0),V0);

  if nops(E0) <> nops(V0) - 1 then
   return false;
  fi;
 od:

 return true;
end:

`is_tree/graphs` := (V) -> proc(E)
 `is_connected/graphs`(V)(E) and
  nops(E) = nops(V) - 1;
end:

`skeleton/graphs` := (V::set) -> proc(E)
 local n,V0,E0,ix,i;
 
 n := nops(V);
 V0 := {seq(i,i=1..n)};
 ix := table():
 for i from 1 to n do ix[V[i]] := i; od;
 E0 := map(e -> [ix[e[1]],ix[e[2]]],E);
 return [V0,E0];
end:

`is_element/paths` := (V) -> (E) -> proc(p)
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

`is_small_element/paths` := (V) -> (E) -> (n::nonnegint) -> proc(p)
 return evalb(`is_element/paths`(V)(E)(p) and (nops(p) = n+1));
end:

`random_small_element/paths` := (V) -> (E) -> (n::nonnegint) -> proc()
 local v,p,e,i;
 
 if E = {} then
  if V = {} or n > 0 then
   return FAIL;
  else
   return [random_element_of(V)()];
  fi;
 fi;

 v := random_element_of(E)()[1];
 p := v;
 for i from 1 to n do
  e := random_element_of(select(e -> member(v,e),E))();
  v := op({op(e)} minus {v});
  p := p,v;
 od;
 return [p];
end:

`list_small_elements/paths` := (V) -> (E) -> proc(n::nonnegint)
 option remember;
 local P,Q,p,v,F,e;
 
 if n = 0 then
  return map(v -> [v],V);
 else
  P := `list_small_elements/paths`(V)(E)(n-1);
  Q := NULL;
  for p in P do
   v := p[1];
   F := select(e -> e[2] = v,E);
   Q := Q,seq([e[1],op(p)],e in F);
  od:
  return [Q];
 fi;
end:

`is_leq/paths` := NULL;
`count_elements/paths` := NULL:
`count_small_elements/paths` := NULL:

`length/paths` := (V) -> (E) -> (p) -> nops(p) - 1;

`is_trail/paths` := proc(p)
 local n,e,i;
 n := nops(p) - 1;
 e := {seq([p[i],p[i+1]],i=1..n)};
 return evalb(nops(e) = n);
end:

`is_cycle/paths` := proc(p)
 local n,i;
 n := nops(p) - 1;
 return evalb(p[1] = p[n+1] and nops({seq(p[i],i=1..n)}) = n);
end:

`is_small_element/trails` := (V) -> (E) -> (n) -> proc(p)
 if not `is_small_element/paths`(V)(E)(n)(p) then
  return false;
 fi;

 return `is_trail/paths`(p);
end:

`is_element/trails` := (V) -> (E) -> proc(p)
 if not `is_element/paths`(V)(E)(p) then
  return false;
 fi;

 return `is_trail/paths`(p);
end:

`list_small_elements/trails` := (V) -> (E) -> proc(n)
 option remember;
 local E0,E1,P,Q,p,v,F,i,e;

 if n = 0 then
  return map(v -> [v],V);
 else
  P := `list_small_elements/trails`(V)(E)(n-1);
  Q := NULL;
  for p in P do
   E0 := {seq([p[i],p[i+1]],i=1..n-1),seq([p[i+1],p[i]],i=1..n-1)};
   E1 := E minus E0;
   v := p[1];
   F := select(e -> e[2] = v,E1);
   Q := Q,seq([e[1],op(p)],e in F);
  od:
  return [Q];
 fi;
end:

`random_small_element/trails` := (V) -> (E) -> (n) -> proc(num_tries := 10)
 local k,p,E0,E1,v,F,e,i;
 
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
  p := `random_small_element/trails`(V)(E)(n-1)();
  k := k - 1;
  if p <> FAIL then
   E0 := {seq([p[i],p[i+1]],i=1..n-1),seq([p[i+1],p[i]],i=1..n-1)};
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

`is_leq/trails` := NULL:
`count_elements/trails` := NULL:
`count_small_elements/trails` := NULL:

######################################################################