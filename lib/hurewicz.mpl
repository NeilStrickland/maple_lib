# Simplicial constructions for a proof of the Hurewicz theorem

`is_element/K/hurewicz` := (A::set) -> (d::posint) -> proc(x)
 if not(`is_element/prime_simplex`(A)(x)) then
  return false;
 fi;

 if nops(select(a -> x[a]>0,A)) > d then
  return false;
 fi;

 return true;
end:

`random_element/K/hurewicz` := (A::set) -> (d::posint) -> proc()
 local k,i,B,x,a;
 k := rand(1..min(nops(A),d))();
 B := {};
 for i from 1 to k do
  B := {op(B),random_element_of(A minus B)};
 od:
 x := `random_element/prime_simplex`(B)();
 for a in A minus B do x[a] := 0; od;
 return eval(x);
end:

`list_elements/K_hurewicz` := NULL:
`count_elements/K_hurewicz` := NULL:

######################################################################

`is_element/L/hurewicz` := (A::set) -> (d::posint) -> proc(tx)
 local t,x;
 
 if not(type(tx,list)) and nops(tx) = 2 then
  return false;
 fi;

 t,x := op(tx);

 if not(type(t,realcons) and is(t >= 0) and is(t <= 1)) then
  return false;
 fi;
 
 if not(`is_element/prime_simplex`(A)(x)) then
  return false;
 fi;

 if t = 1 then
  return true;
 fi;

 if `is_element/K/hurewicz`(A)(d)(x) then
  return true;
 fi;

 return false;
end:

`random_element/L/hurewicz` := (A::set) -> (d::posint) -> proc()
 if rand(1..2)() = 1 then
  return [1,`random_element/prime_simplex`(A)()];
 else
  return [rand(0..12)()/12,`random_element/K/hurewicz`(A)(d)()];
 fi;
end:

`list_elements/L_hurewicz` := NULL:
`count_elements/L_hurewicz` := NULL:

######################################################################

`u1/hurewicz` := (A::set) -> (d::posint) -> proc(x)
 local JJ,J,j;
 if nops(A) <= d then return 0; fi;
 JJ := combinat[choose](A,nops(A) - d);
 return min(seq(max(seq(x[j],j in J)),J in JJ));
end:

`w1/hurewicz` := (A::set) -> (d::posint) -> proc(tx)
 local t,x,u1;
 t,x := op(tx);
 u1 := `u1/hurewicz`(A)(d)(x);
 return min(u1+(1+t)/2,1);
end:

`f1/hurewicz` := (A::set) -> (d::posint) -> proc(tx)
 local t,x,y,a;
 t,x := op(tx);
 y := table():
 for a in A do
  y[a] := max(0,x[a]-(1-t)/2,2*x[a]-1);
 od:
 return eval(y);
end:

`h1/hurewicz` := (A::set) -> (d::posint) -> proc(tx)
 return [`w1/hurewicz`(A)(d)(tx),`f1/hurewicz`(A)(d)(tx)];
end:

