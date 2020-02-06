######################################################################
# W1(A) is Map(A,RR) modulo translation, except that we take
# W1(emptyset) to be empty.
#
# Elements are represented as tables indexed by A, whose values 
# are real numbers.  The equivalence relation
# is built into the definition of the function `is_equal/W1` rather
# than the representation of the elements.

`is_element/W1` := (A::set) -> proc(x)
 local a;
 global reason;

 if A = {} then
  reason := [convert(procname,string),"W1(emptyset) = emptyset"];
  return false;
 fi;

 if not(is_table_on(A)(x)) then
  reason := [convert(procname,string),"x is not a table on A",x,A];
  return false;  
 fi;

 for a in A do
  if not `is_element/RR`(x[a]) then
   reason := [convert(procname,string),"x[a] is not in R",a,x[a],N];
   return false;
  fi;
 od;

 return true;
end;

`is_equal/W1` := (A::set) -> proc(x,y) 
 local a0,u0,a;
 global reason;

 if A = {} then 
  reason := [convert(procname,string),"W1(emptyset) = emptyset"];
  return false;
 fi;

 a0 := A[1];
 u0 := x[a0] - y[a0];

 for a in A do
  if not(`is_equal/RR`(x[a] - y[a],u0)) then
   reason := [convert(procname,string),"x[a] - y[a] <> x[a0] - y[a0]",a,a0];
   return false;
  fi;
 od;

 return true;
end;

`is_leq/W1` := NULL;

`random_element/W1` := (A::set) -> proc()
 local x,a;

 x := table();
 for a in A do
  x[a] := `random_element/RR`();
 od:

 return eval(x);
end;

`list_elements/W1` := NULL;
`count_elements/W1` := NULL;

