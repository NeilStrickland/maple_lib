######################################################################

`is_element/ord_simplex_interior` := (A::set) -> proc(Rx)
 local R,x;
 global reason;

 if not(type(Rx,list) and nops(Rx) = 2) then 
  reason := [convert(procname,string),"Rx cannot be split as [R,x]",Rx];  
  return false;
 fi;

 R,x := op(Rx);

 if not(`is_element/ord`(A)(R)) then
  reason := [convert(procname,string),"R is not an order on A",R,A,reason];
  return false;
 fi;

 if not(`is_element/simplex_interior`(A)(x)) then
  reason := [convert(procname,string),"x is not in the interior of the A-simplex",x,A,reason];
  return false;
 fi;

 return true;
end;

`is_equal/ord_simplex_interior` := (A::set) -> proc(Rx,Sy)
 global reason;

 if not `is_equal/ord`(A)(Rx[1],Sy[1]) then
  reason := [convert(procname,string),"R <> S",Rx[1],Sy[1],reason];
  return false;
 fi;

 if not `is_equal/simplex`(A)(Rx[2],Sy[2]) then
  reason := [convert(procname,string),"x <> y",Rx[2],Sy[2],reason];
  return false;
 fi;

 return true;
end;

`is_leq/ord_simplex_interior` := NULL;

`random_element/ord_simplex_interior` := (A::set) -> proc(d::posint := 5)
 [`random_element/ord`(A)(),
  `random_element/simplex_interior`(A)(d)];
end;

`list_elements/ord_simplex_interior` := NULL;
`count_elements/ord_simplex_interior` := NULL;

`phi/ord_simplex_interior/one_cubes_prime` := (A::set) -> proc(Rx)
 local R,x,y,n,i,p,q;

 R,x := op(Rx);
 y := table();
 n := nops(R);

 for i from 1 to n do
  p := add(x[R[j]],j=1..i-1);
  q := p + x[R[i]];
  y[R[i]] := [[p],[q]];
 od;

 return [R,eval(y)];
end;

