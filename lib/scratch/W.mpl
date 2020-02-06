######################################################################
# W(N)(A) is Map(A,RR^N) modulo translation, except that we take
# W(N)(emptyset) to be empty.
#
# Elements are represented as tables indexed by A, whose values 
# are lists of length N of real numbers.  The equivalence relation
# is built into the definition of the function `is_equal/W` rather
# than the representation of the elements.

`is_element/W` := (N::posint) -> (A::set) -> proc(x)
 local a;
 global reason;

 if A = {} then
  reason := [convert(procname,string),"W(N)(emptyset) = emptyset"];
  return false;
 fi;

 if not(type(x,table)) then
  reason := [convert(procname,string),"x is not a table",x];
  return false;  
 fi;

 if map(op,{indices(x)}) <> A then
  reason := [convert(procname,string),"x is not indexed by A",x,A];
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

`is_equal/W` := (N::posint) -> (A::set) -> proc(x,y) 
 local a0,u0,a;
 global reason;

 if A = {} then 
  reason := [convert(procname,string),"W(N)(emptyset) = emptyset"];
  return false;
 fi;

 a0 := A[1];
 u0 := x[a0] -~ y[a0];

 for a in A do
  if not(`is_equal/R`(N)(x[a] -~ y[a],u0)) then
   reason := [convert(procname,string),"x[a] - y[a] <> x[a0] - y[a0]",a,a0];
   return false;
  fi;
 od;

 return true;
end;

`is_leq/W` := NULL;

`random_element/W` := (N::posint) -> (A::set) -> proc()
 local x,a;

 x := table();
 for a in A do
  x[a] := `random_element/R`(N)();
 od:

 return eval(x);
end;

`list_elements/W` := NULL;
`count_elements/W` := NULL;

