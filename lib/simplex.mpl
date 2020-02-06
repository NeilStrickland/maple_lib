######################################################################
# simplex(A) is the set of maps x : A -> [0,1] with sum = 1.

`is_element/simplex` := (A::set) -> proc(x)
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

  v := v + u;
 od;

 if simplify(v - 1) <> 0 then
  reason := [convert(procname,string),"entries in x do not sum to 1",x,v];
  return false;
 fi;

 return true;
end;

`is_equal/simplex` := (A::set) -> proc(x,y)
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

`is_leq/simplex` := NULL;

`random_element/simplex` := (A::set) -> proc(d::posint := 5)
 local x,a,r1,r2,u;
 if A = {} then return FAIL; fi;

 r1 := rand(0..d); 
 r2 := rand(1..d);
 x := table();
 u := 0;
 while u = 0 do
  for a in A do 
   x[a] := r1()/r2();
   u := u + x[a];
  od;
 od;

 for a in A do x[a] := x[a]/u; od;

 return eval(x);
end;

`list_elements/simplex` := NULL;
`count_elements/simplex` := NULL;
