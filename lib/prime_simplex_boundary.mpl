######################################################################
# prime_simplex_boundary(A) is the set of maps x : A -> [0,1] with 
# min = 0 and max = 1.

`is_element/prime_simplex_boundary` := (A::set) -> proc(x)
 local a,u,v,w;
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
 w := 1;

 for a in A do
  u := x[a];

  if not (`is_element/RR`(u) and u >= 0 and u <= 1) then
   reason := [convert(procname,string),"x[a] is not in the unit interval",a,u];
   return false;
  fi;

  v := max(u,v);
  w := min(u,w);
 od;

 if simplify(v - 1) <> 0 then
  reason := [convert(procname,string),"max(x[a] : a in A) <> 1",v];
  return false;
 fi;

 if simplify(w) <> 0 then
  reason := [convert(procname,string),"min(x[a] : a in A) <> 0",w];
  return false;
 fi;

 return true;
end;

######################################################################

`is_equal/prime_simplex_boundary` := (A::set) -> proc(x,y)
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

######################################################################

`is_leq/prime_simplex_boundary` := NULL;

######################################################################

`random_element/prime_simplex_boundary` := (A::set) -> proc(d::posint := 5)
 local x,a,r1,r2,u,v;

 if nops(A) < 2 then return FAIL; fi;

 r1 := rand(0..d); 
 r2 := rand(1..d);
 x := table();
 u := 0;
 v := 0;

 while u = v do
  u := 0;
  v := infinity;
  for a in A do 
   x[a] := r1()/r2();
   u := max(u,x[a]);
   v := min(v,x[a]);
  od;
 od;

 for a in A do x[a] := (x[a]-v)/(u-v); od;

 return eval(x);
end;

######################################################################

`list_elements/prime_simplex_boundary` := NULL;
`count_elements/prime_simplex_boundary` := NULL;

######################################################################

`phi/proper_nonempty_subsets/prime_simplex_boundary` := (A::set) -> proc(U)
 local x,a;

 x := table();
 for a in A do x[a] := 0; od;
 for a in U do x[a] := 1; od;

 return eval(x);
end;


