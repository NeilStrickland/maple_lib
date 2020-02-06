`is_element/prime_W` := (N::posint) -> (A::set) -> proc(x)
 `is_element/vector_functions`(N)(A)(x) and
 `sum/vector_functions`(N)(A)(x) = [0$N];
end;

######################################################################

`is_equal/prime_W` := (N::posint) -> (A::set) -> proc(x,y) 
 return `is_equal/vector_functions`(N)(A)(x,y);
end;

######################################################################

`is_leq/prime_W` := NULL;

######################################################################

`is_zero/prime_W` := (N::posint) -> (A::set) -> proc(x) 
 return `is_zero/vector_functions`(N)(A)(x);
end;

######################################################################

`norm/prime_W` := (N::posint) -> (A::set) -> proc(x) 
 return `norm/vector_functions`(N)(A)(x);
end;

######################################################################

`normalise/prime_W` := (N::posint) -> (A::set) -> proc(x) 
 local r;
 r := `norm/vector_functions`(N)(A)(x);
 if r = 0 then return FAIL; fi;
 return table([seq(a = simplify(x[a] /~ r),a in A)]);
end;

######################################################################

`random_element/prime_W` := (N::posint) -> (A::set) -> proc()
 local x,a,u;

 u := [0$N];
 x := table();
 for a in A do
  x[a] := `random_element/R`(N)();
  u := u +~ x[a];
 od:
 u := u /~ nops(A);
 for a in A do 
  x[a] := x[a] -~ u;
 od;

 return eval(x);
end;

`list_elements/W` := NULL;
`count_elements/W` := NULL;

######################################################################
# Here C is assumed to be a subset of B, and rho is the usual map 
# from W(N,B) to W(N,C).

`rho/prime_W` := (B,C) -> proc(x)
 local y,z,c;

 y := table();
 for c in C do y[c] := x[c]; od;
 z := `normalise/W`(N)(C)(y);
 return eval(z);
end;
