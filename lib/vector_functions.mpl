`is_element/vector_functions` := (N::posint) -> (A::set) -> proc(x)
 local a;
 global reason;

 if not(is_table_on(A)(x)) then
  reason := [convert(procname,string),"x is not a table on A",x,A];
  return false;  
 fi;

 for a in A do
  if not `is_element/R`(N)(x[a]) then
   reason := [convert(procname,string),"x[a] is not in R^N",a,x[a],N];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_equal/vector_functions` := (N::posint) -> (A::set) -> proc(x,y) 
 local a;
 global reason;

 for a in A do
  if not(`is_equal/R`(N)(x[a],y[a])) then
   reason := [convert(procname,string),"x[a] <> y[a]",a,x,y];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_nonnegative/vector_functions` := (N::posint) -> (A::set) -> proc(x) 
 local a,i;

 for a in A do
  for i from 1 to N do
   if x[a][i] < 0 then
    return false;
   fi;
  od;
 od;

 return true;
end:

######################################################################

`is_zero/vector_functions` := (N::posint) -> (A::set) -> proc(x) 
 local a,i;

 for a in A do
  for i from 1 to N do
   if x[a][i] <> 0 then
    return false;
   fi;
  od;
 od;

 return true;
end:

######################################################################

`is_leq/vector_functions` := (N::posint) -> (A::set) -> proc(x,y)
 local a,i;

 for a in A do
  for i from 1 to N do 
   if x[a][i] > y[a][i] then
    return false;
   fi;
  od;
 od;

 return true;
end:

######################################################################

`plus/vector_functions` := (N) -> (A::set) -> proc(x,y)
 local z,a;

 z := table();
 for a in A do
  z[a] := x[a] +~ y[a];
 od:

 return eval(z):
end:

######################################################################

`times/vector_functions` := (N) -> (A::set) -> proc(t,x)
 local z,a;

 z := table();
 for a in A do
  z[a] := t *~ x[a];
 od:

 return eval(z):
end:

######################################################################

`norm/vector_functions` := (N::posint) -> (A::set) -> proc(x)
 local a,n;

 n := 0;
 for a in A do n := n + `norm_2/R`(N)(x[a])^2; od;
 
 return sqrt(n);
end:

######################################################################

`sum/vector_functions` := (N::posint) -> (A::set) -> proc(x)
 local a,u;

 u := [0$N];
 for a in A do u := u +~ x[a]; od;
 
 return u;
end:

######################################################################

`average/vector_functions` := (N::posint) -> (A::set) -> proc(x)
 if A = {} then
  return FAIL;
 fi;

 return `sum/vector_functions`(N)(A)(x) /~ nops(A);
end:

######################################################################

`dist/vector_functions` := (N::posint) -> (A::set) -> proc(x,y)
 local a,n;

 n := 0;
 for a in A do n := n + `d_2/R`(N)(x[a],y[a])^2; od;
 
 return sqrt(n);
end:

######################################################################

`dot/vector_functions` := (N::posint) -> (A::set) -> proc(x,y)
 local a,d;

 d := 0;
 for a in A do d := d + `dot/R`(N)(x[a],y[a]); od;
 
 return d;
end:

######################################################################

`random_element/vector_functions` := (N::posint) -> (A::set) -> proc()
 local x,a;

 x := table();
 for a in A do
  x[a] := `random_element/R`(N)();
 od:

 return eval(x);
end;

######################################################################

`list_elements/vector_functions` := NULL;
`count_elements/vector_functions` := NULL;

