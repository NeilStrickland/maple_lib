######################################################################
# Here B is assumed to be a subset of A, and SWW(A,B,N) is the space
# denoted by S(NWA,NWB) in the LaTeX document.

`is_element/SWW` := (N::posint) -> (A::set,B::set) -> proc(xy)
 local x,y,x0,y0,a,b,r;
 global reason;
 
 if not(type(xy,list) and nops(xy) = 2) then
  reason := [convert(procname,string),"xy cannot be split as [x,y]",xy];
  return false;
 fi;

 x,y := op(xy); 
 if not(`is_element/SW`(N)(A)(x)) then
  reason := [convert(procname,string),"x is not in SW(N)(A)",x,N,A];
  return false;
 fi;

 if not(`is_element/SW`(N)(B)(y)) then
  reason := [convert(procname,string),"y is not in SW(N)(B)",y,N,B];
  return false;
 fi;

 x0 := table();
 for b in B do x0[b] := x[b]; od;
 x0 := `normalise/W`(N)(B)(x0);
 y0 := `normalise/SW`(N)(B)(y);

 r := 0;
 for b in B do r := max(r,op(map(abs,x0[b]))); od;
 if r = 0 then return true; fi;
 for b in B do
  if simplify(x0[b] -~ r *~ y0[b]) <> [0$N] then
   reason := [convert(procname,string),"x0 and y0 are incompatible at b",x0,y0,b,r];
   return false;
  fi;
 od;

 return true;
end;

`normalise/SWW` := (N::posint) -> (A::set,B::set) -> proc(xy)
 [`normalise/SW`(N)(A)(xy[1]),
  `normalise/SW`(N)(B)(xy[2])];
end;

`is_equal/SWW` := (N::posint) -> (A::set,B::set) -> proc(x,y) 
 local p,q,r,s;
 global reason;

 p,q := op(`normalise/SWW`(N)(A,B)(x));
 r,s := op(`normalise/SWW`(N)(A,B)(y));

 if not `is_equal/SW`(N)(A)(p,r) then
  reason := [convert(procname,string),"p <> r",p,r,reason];
  return false;
 fi;

 if not `is_equal/SW`(N)(B)(q,s) then
  reason := [convert(procname,string),"q <> s",q,s,reason];
  return false;
 fi;

 return true;
end;

`is_leq/SWW` := NULL;

`random_element/SWW` := (N::posint) -> (A::set,B::set) -> proc()
 local x,y,b,u,c;

 x := `random_element/SW`(N)(A)();

 if rand(1..3)() = 1 then
  u := `random_element/R`(N)();

  for b in B do
   x[b] := u;
  od;
  y := `random_element/SW`(N)(B)();
 else 
  y := `rho/W`(A,B)(x);
  if `is_zero/W`(N)(B)(y) then
   y := `random_element/SW`(N)(B)();
  fi;
 fi;

 return [eval(x),eval(y)];
end;

`list_elements/SWW` := NULL;
`count_elements/SWW` := NULL;
