######################################################################
# SW(N)(A) is the sphere associated to the vector space W(N)(A).
# In the main LaTeX document this is called S(NWA).
#
# Elements are represented as nonzero elements of the space W(N)(A),
# with an appropriate equivalence relation built into the definition
# the function `is_equal/SW`.

`is_element/SW` := (N::posint) -> (A::set) -> proc(x)
 local x0,a;
 global reason;

 if not(`is_element/W`(N)(A)(x)) then
  reason := [convert(procname,string),"x is not in W(N)(A)",x,N,A,reason];
  return false;
 fi;

 x0 := `normalise/W`(N)(A)(x);

 for a in A do
  if x0[a] <> [0$N] then return true; fi;
 od;

 reason := [convert(procname,string),"x is zero",x];
 return false;
end;

`normalise/SW` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,r,a;

 x0 := `normalise/W`(N)(A)(x);
 r := max(0,seq(op(map(abs,x0[a])),a in A));
 for a in A do
  x0[a] := x0[a] /~ r;
 od;

 return(eval(x0));
end;

`bottom_normalise/SW` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,r,a;

 x0 := `bottom_normalise/W`(N)(A)(x);
 r := max(0,seq(op(map(abs,x0[a])),a in A));
 for a in A do
  x0[a] := x0[a] /~ r;
 od;

 return(eval(x0));
end;

`is_equal/SW` := (N::posint) -> (A::set) -> proc(x,y) 
 local x0,y0,a;

 x0 := `normalise/SW`(N)(A)(x);
 y0 := `normalise/SW`(N)(A)(y);

 for a in A do
  if not(`is_equal/R`(N)(x0[a],y0[a])) then
   return false;
  fi;
 od;

 return true;
end;

`dist/SW` := (N::posint) -> (A::set) -> proc(x,y) 
 local x0,y0,a,d;

 x0 := `normalise/SW`(N)(A)(x);
 y0 := `normalise/SW`(N)(A)(y);

 d := 0;
 for a in A do
  d := d + `d_infinity/R`(N)(x0[a],y0[a]);
 od;

 return d;
end;

`normalise_2/SW` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,r2,r,a;

 x0 := table();
 u := [0$N];

 for a in A do
  x0[a] := x[a];
  u := u +~ x[a];
 od;
 u := u /~ nops(A);
 r2 := 0;
 for a in A do
  x0[a] := x0[a] -~ u;
  r2 := r2 + `norm_2/R`(N)(x0[a])^2;
 od;
 r := sqrt(r2);

 for a in A do
  x0[a] := x0[a] /~ r;
 od;

 return(eval(x0));
end;

`dist_2/SW` := (N::posint) -> (A::set) -> proc(x,y) 
 local x0,y0,a,d;

 x0 := `normalise_2/SW`(N)(A)(x);
 y0 := `normalise_2/SW`(N)(A)(y);

 d := 0;
 for a in A do
  d := d + `d_2/R`(N)(x0[a],y0[a])^2;
 od;

 d := combine(simplify(expand(d)));
 d := combine(simplify(expand(sqrt(d))));
 return d;
end;

`is_leq/SW` := NULL;

`random_element/SW` := (N::posint) -> (A::set) -> proc()
 local x,ok;

 ok := false;

 while not(ok) do
  x := `random_element/W`(N)(A)();
  ok := `is_element/SW`(N)(A)(x);
 od:

 return eval(x);
end;

`list_elements/SW` := NULL;
`count_elements/SW` := NULL;
