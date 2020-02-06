######################################################################
# simplex_interior(A) is the set of maps x : A -> (0,1] with sum = 1.

`is_element/simplex_interior` := (A::set) -> proc(x)
 local a,u;
 global reason;

 if not `is_element/simplex`(A)(x) then
  reason := [convert(procname,string),"x is not in the A-simplex",x,A,reason];
  return false;
 fi;

 for a in A do if x[a] = 0 then
  reason := [convert(procname,string),"x[a] = 0",a];
  return false;
 fi; od;

 return true;
end;

`is_equal/simplex_interior` := (A::set) -> proc(x,y)
 `is_equal/simplex`(A)(x,y);
end;

`is_leq/simplex_interior` := NULL;

`random_element/simplex_interior` := (A::set) -> proc()
 local x,a,r1,r2,u;
 if A = {} then return FAIL; fi;

 r1 := rand(1..5); 
 r2 := rand(1..5);
 x := table();
 u := 0;
 for a in A do 
  x[a] := r1()/r2();
  u := u + x[a];
 od;
 for a in A do x[a] := x[a]/u; od;

 return eval(x);
end;

`list_elements/simplex_interior` := NULL;
`count_elements/simplex_interior` := NULL;
