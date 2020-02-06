######################################################################
# prime_simplex(A) is the set of maps x : A -> [0,1] with max = 1.

`is_element/prime_simplex` := (A::set) -> proc(x)
 local a,u,v;
 global reason;

 if not type(x,table) then
  reason := [convert(procname,string),"x is not a table",x];
  return false;
 fi;

 if map(op,{indices(x)}) <> A then
  reason := [convert(procname,string),"x is not indexed by A",x,A];
  return false;
 fi;

 v := 0;

 for a in A do
  u := x[a];

  if not (`is_element/RR`(u) and u >= 0 and u <= 1) then
   reason := [convert(procname,string),"x[a] is not in the unit interval",a,u];
   return false;
  fi;

  v := max(u,v);
 od;

 if simplify(v - 1) <> 0 then
  reason := [convert(procname,string),"max(x[a] : a in A) <> 1",a,v];
  return false;
 fi;

 return true;
end;

`is_equal/prime_simplex` := (A::set) -> proc(x,y)
 local a;
 global reason;

 for a in A do
  if simplify(x[a] - y[a]) <> 0 then
   reason := [convert(procname,string),"x[a] <> y[a]",a,x[a],y[a]];
   return false;
  fi;
 od;

 return true;
end;

`is_leq/prime_simplex` := NULL;

`random_element/prime_simplex` := (A::set) -> proc(d::posint := 5)
 local x,a,r1,r2,u;
 if A = {} then return FAIL; fi;

 r1 := rand(0..d); 
 r2 := rand(1..d);
 x := table();
 u := 0;
 while u = 0 do
  for a in A do 
   x[a] := r1()/r2();
   u := max(u,x[a]);
  od;
 od;

 for a in A do x[a] := x[a]/u; od;

 return eval(x);
end;

`list_elements/prime_simplex` := NULL;
`count_elements/prime_simplex` := NULL;

`phi/nonempty_subsets/prime_simplex` := (A::set) -> proc(U)
 local x,a;

 x := table();
 for a in A do x[a] := 0; od;
 for a in U do x[a] := 1; od;

 return eval(x);
end;

`supp/prime_simplex` := (A::set) -> proc(x)
 select(a -> x[a] > 0,A);
end:

`functor/prime_simplex` := (A::set,B::set) -> (f) -> proc(x)
 local a,b,y;
 
 y := table():
 for b in B do y[b] := 0; od:
 for a in A do y[f[a]] := max(y[f[a]],x[a]); od:
 return eval(y);
end:
