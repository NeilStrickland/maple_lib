######################################################################

# Complex numbers

`is_element/CC` := (x) -> type(x,constant):

`is_equal/CC` := (x,y) -> evalb(simplify(y-x) = 0):

`is_leq/CC` := NULL;

`is_leq_lex/CC` := proc(x,y)
 local z;
 z := simplify(y - x);
 if is(Re(z) > 0) then
  return true;
 elif is(Re(z) < 0) then
  return false;
 elif is(Im(z) > 0) then
  return true;
 elif is(Im(z) < 0) then
  return false;
 fi;
 return true;
end:

`random_element/CC` := proc()
 rand(-720..720)()/(360) + rand(-720..720)()/(360) * I;
end:

`list_elements/CC` := NULL;
`count_elements/CC` := NULL;

######################################################################
# C(N) is the vector space CC^N

`is_element/C` := (N::posint) -> (x) -> type(x,[constant$N]);

`is_equal/C` := (N::posint) -> (x,y) -> evalb(simplify(x -~ y) = [0$N]);

`is_leq/C` := NULL;

`is_leq_lex/C` := (N::posint) -> proc(x,y)
 local i,z;
 for i from 1 to n do
  z := simplify(y[i] - x[i]);
  if is(Re(z) > 0) then
   return true;
  elif is(Re(z) < 0) then
   return false;
  elif is(Im(z) > 0) then
   return true;
  elif is(Im(z) < 0) then
   return false;
  fi;
 od;
 return true;
end:

`is_zero/C` := (N::posint) -> (x) -> evalb(simplify(x) = [0$N]);

`norm_2/C` := (N::posint) -> (x) -> sqrt(add(abs(x[i])^2,i=1..N));

`dot/C` := (N::posint) -> (x,y) -> add(x[i]*conjugate(y[i]),i=1..N);

`d_2/C` := (N::posint) -> (x,y) -> `norm_2/C`(N)(x -~ y);

`random_element/C` := (N::posint) -> proc() [seq(`random_element/CC`(),i=1..N)] end;

`list_elements/C` := NULL;
`count_elements/C` := NULL;