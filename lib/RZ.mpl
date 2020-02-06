######################################################################

# Real numbers mod integers

`is_element/RZ` := (x) -> type(x,realcons):

`is_equal/RZ` := (x,y) -> type(simplify(y-x),integer):

`is_leq/RZ` := NULL:

`normalize/RZ` := (x) -> simplify(x - floor(x)):

`random_element/RZ` := proc() rand(0..719)()/(720); end:

`list_elements/RZ` := NULL;
`count_elements/RZ` := NULL;

`d/RZ` := (x,y) -> abs(x - y - round(x - y));

`eta/RZ` := (x) -> exp(2*Pi*I*x);

`is_cyclic/RZ` := proc(x::list)
 local n,y,z;
 n := nops(x);
 if n <= 2 then return true; fi;
 y := simplify(x -~ x[1]);
 y := simplify(y -~ map(floor,y));
 z := [seq(y[i+1] - y[i],i=1..n-1)];
 return evalb(simplify(min(op(z))) >= 0);
end:

`is_strictly_cyclic/RZ` := proc(x::list)
 local n,y,z;
 n := nops(x);
 if n <= 2 then return true; fi;
 y := simplify(x -~ x[1]);
 y := simplify(y -~ map(floor,y));
 z := [seq(y[i+1] - y[i],i=1..n-1)];
 return evalb(simplify(min(op(z))) >= 0);
end:

