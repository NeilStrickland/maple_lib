######################################################################
# This section is about the suboperad of little 1-cubes where the 
# subintervals fill the whole interval.

`is_element/one_cubes_prime` := (A::set) -> proc(f)
 local X,n,i;
 global reason;

 if not(`is_element/cubes`(1)(A)(f)) then
  reason := [convert(procname,string),"f is not a 1-cube for A",f,A,reason];
  return false;
 fi;

 X := map(a -> map(op,f[a]),[op(A)]);
 X := sort(X,(u,v) -> evalb(u[1]<v[1]));
 n := nops(A);
 if X[1][1] <> 0 then
  reason := [convert(procname,string),"The first interval does not start at 0",X[1]];
  return false;
 fi;
 if X[n][2] <> 1 then
  reason := [convert(procname,string),"The last interval does not end at 1",X[n]];
  return false;
 fi;

 for i from 1 to n-1 do
  if X[i][2] <> X[i+1][1] then
   reason := [convert(procname,string),"Successive intervals do not touch",X[i],X[i+1]];
   return false;
  fi;
 od;

 return true;
end;

`is_equal/one_cubes_prime` := (A::set) -> proc(f1,f2)
 `is_equal/cubes`(1)(A)(f1,f2);
end:

`is_leq/one_cubes_prime` := NULL;

`random_element/one_cubes_prime` := (A::set) -> proc()
 local d,n,u,i,r,R,xy;

 d := 12;
 n := nops(A);
 u := table();
 u[0] := 0;
 for i from 1 to n do 
  u[i] := u[i-1] + rand(1..d)();
 od;
 r := u[n];
 for i from 1 to n do u[i] := u[i]/r; od;

 R := `random_element/ord`(A)();
 xy := table();
 for i from 1 to n do 
  xy[R[i]] := [[u[i-1]],[u[i]]];
 od;

 return eval(xy);
end;

`list_elements/one_cubes_prime` := NULL;
`count_elements/one_cubes_prime` := NULL;

