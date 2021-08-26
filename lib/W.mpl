######################################################################
# W(N)(A) is Map(A,R^N)/Const(A,R^N).  
#
# Elements are represented as tables indexed by A, whose values 
# are lists of length N of real numbers.  The equivalence relation
# is built into the definition of the function `is_equal/W` rather
# than the representation of the elements.

`is_element/W` := (N::posint) -> (A::set) -> proc(x)
 `is_element/vector_functions`(N)(A)(x);
end;

######################################################################

`normalise/W` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,a;

 x0 := table();
 u := [0$N];

 for a in A do
  x0[a] := x[a];
  u := u +~ x[a];
 od;
 u := u /~ nops(A);
 for a in A do
  x0[a] := x0[a] -~ u;
 od;
 return(eval(x0));
end;

######################################################################

`bottom_normalise/W` := (N::posint) -> (A::set) -> proc(x)
 local x0,u,a,i;

 u := [seq(min(seq(x[a][i],a in A)),i=1..N)];
 x0 := table():
 for a in A do 
  x0[a] := x[a] -~ u;
 od:
 return(eval(x0));
end;

######################################################################

`is_equal/W` := (N::posint) -> (A::set) -> proc(x,y) 
 local x0,y0,a;

 x0 := `normalise/W`(N)(A)(x);
 y0 := `normalise/W`(N)(A)(y);

 return `is_equal/vector_functions`(N)(A)(x0,y0);
end;

######################################################################

`is_leq/W` := NULL;

######################################################################

`is_zero/W` := (N::posint) -> (A::set) -> proc(x) 
 local x0,a;

 x0 := `normalise/W`(N)(A)(x);
 return `is_zero/vector_functions`(N)(A)(x0);
end;

######################################################################

`norm/W` := (N::posint) -> (A::set) -> proc(x) 
 local x0,a;

 x0 := `normalise/W`(N)(A)(x);
 return `norm/vector_functions`(N)(A)(x0);
end;

######################################################################

`width/W` := (N::posint) -> (A::set) -> proc(x)
 local i,a;
 max(seq(max(seq(x[a][i],a in A)) -  min(seq(x[a][i],a in A)),i=1..N));
end;

######################################################################

`random_element/W` := (N::posint) -> (A::set) -> proc()
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

`rho/W` := (B,C) -> proc(x)
 local y,c;

 y := table();
 for c in C do y[c] := x[c]; od;
 return eval(y);
end;
