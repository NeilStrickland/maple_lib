`is_element/real_functions` := (A::set) -> proc(x)
 local a;
 global reason;

 if not(is_table_on(A)(x)) then
  reason := [convert(procname,string),"x is not a table on A",x,A];
  return false;  
 fi;

 for a in A do
  if not `is_element/RR`(x[a]) then
   reason := [convert(procname,string),"x[a] is not in R",a,x[a]];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_equal/real_functions` := (A::set) -> proc(x,y) 
 local a;
 global reason;

 for a in A do
  if not(`is_equal/RR`(x[a],y[a])) then
   reason := [convert(procname,string),"x[a] <> y[a]",a,x,y];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`random_element/real_functions` := (A::set) -> proc()
 local x,a;

 x := table();
 for a in A do
  x[a] := `random_element/RR`();
 od:

 return eval(x);
end;

######################################################################

`list_elements/real_functions` := NULL;
`count_elements/real_functions` := NULL;

######################################################################

`is_nonnegative/real_functions` := (A::set) -> proc(x) 
 local a;

 for a in A do
  if is(x[a] < 0) then
   return false;
  fi;
 od;

 return true;
end:

######################################################################

`is_leq/real_functions` := (A::set) -> proc(x,y)
 local a;

 for a in A do
  if is(x[a] > y[a]) then
   return false;
  fi;
 od;

 return true;
end:

######################################################################

`norm/real_functions` := (A::set) -> proc(x)
 local a,n;

 n := 0;
 for a in A do n := n + x[a]^2; od;
 
 return sqrt(n);
end:

######################################################################

`sum/real_functions` := (A::set) -> proc(x)
 local a,u;

 u := 0;
 for a in A do u := u + x[a]; od;
 
 return u;
end:

######################################################################

`max/real_functions` := (A::set) -> proc(x)
 local a,u;

 u := -infinity;
 for a in A do u := max(u,x[a]); od;
 
 return u;
end:

######################################################################

`min/real_functions` := (A::set) -> proc(x)
 local a,u;

 u := infinity;
 for a in A do u := min(u,x[a]); od;
 
 return u;
end:

######################################################################

`dist/real_functions` := (A::set) -> proc(x,y)
 local a,n;

 n := 0;
 for a in A do n := n + (x[a]-y[a])^2; od;
 
 return sqrt(n);
end:

######################################################################

`dot/real_functions` := (A::set) -> proc(x,y)
 local a,d;

 d := 0;
 for a in A do d := d + x[a]*y[a]; od;
 
 return d;
end:

######################################################################

`width/real_functions` := (A::set) -> proc(x)
 local V;
 V := map(a -> x[a],A);
 return max(op(V)) - min(op(V));
end:

######################################################################

`gap/real_functions` := (A::set) -> proc(x)
 local V,n,i;
 V := sort([op(map(a -> x[a],A))]);
 n := nops(V);
 return max(0,seq(V[i+1]-V[i],i=1..n-1));
end:

######################################################################

`relative_gap/real_functions` := (A::set) -> proc(x)
 return `gap/real_functions`(A)(x)/`width/real_functions`(A)(x);
end:
