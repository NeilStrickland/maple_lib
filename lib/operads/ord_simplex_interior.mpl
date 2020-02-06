######################################################################

`eta/ord_simplex_interior` := proc(A::set) 
 if nops(A) <> 1 then return FAIL; fi;
 
 return [`eta/ord`(A),`eta/simplex_interior`(A)];
end;

`gamma/ord_simplex_interior` := (A::set,B::set) -> (p) -> proc(U,V)
 local RU,RV,xU,xV;

 RU := U[1];
 RV := table([seq(b = eval(V[b][1]),b in B)]);
 xU := U[2];
 xV := table([seq(b = eval(V[b][2]),b in B)]);
 return [`gamma/ord`(A,B)(p)(RU,RV),
         `gamma/simplex_interior`(A,B)(p)(xU,xV)];
end;
