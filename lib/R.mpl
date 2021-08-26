######################################################################

# Real numbers

`is_element/RR` := (x) -> type(x,realcons):

`is_equal/RR` := (x,y) -> evalb(simplify(y-x) = 0):

`is_leq/RR` := (x,y) -> is(simplify(y-x) >= 0);

`random_element/RR` := proc() rand(-720..720)()/(360); end:

`list_elements/RR` := NULL;
`count_elements/RR` := NULL;

`random_element/RR_plus` := proc() rand(1..720)()/(360); end:

######################################################################
# R(N) is the vector space RR^N

`is_element/R` := (N::posint) -> (x) -> type(x,[realcons$N]);

`is_equal/R` := (N::posint) -> (x,y) -> evalb(simplify(x -~ y) = [0$N]);

`is_leq/R` := (N::posint) -> proc(x,y) local i; `and`(seq(`is_leq/RR`(x[i],y[i]),i=1..N)); end:

`is_leq_lex/R` := (N::posint) -> proc(x,y)
 local i,z;
 for i from 1 to n do
  z := simplify(y[i] - x[i]);
  if is(z > 0) then
   return true;
  elif is(z < 0) then
   return false;
  fi;
 od;
 return true;
end:

`is_zero/R` := (N::posint) -> (x) -> evalb(simplify(x) = [0$N]);

`norm_2/R` := (N::posint) -> proc(x) local i; sqrt(add(x[i]^2,i=1..N)); end:

`dot/R` := (N::posint) -> proc(x,y) local i; add(x[i]*y[i],i=1..N); end:

`d_2/R` := (N::posint) -> (x,y) -> `norm_2/R`(N)(x -~ y);

`norm_infinity/R` := (N::posint) -> (x) -> max(map(abs,x));

`d_infinity/R` := (N::posint) -> (x,y) -> `norm_infinity/R`(N)(x -~ y);
 
`random_element/R` := (N::posint) -> proc() local i; [seq(`random_element/RR`(),i=1..N)] end;

`list_elements/R` := NULL;
`count_elements/R` := NULL;

`cross_product` := proc(x,y)
 [x[2]*y[3] - x[3]*y[2],
  x[3]*y[1] - x[1]*y[3],
  x[1]*y[2] - x[2]*y[1]];
end: