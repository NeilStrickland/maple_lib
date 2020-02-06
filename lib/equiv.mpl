######################################################################

`is_element/equiv` := (A::set) -> proc(R)
 global reason;

 if not `is_element/autorel`(A)(R) then
  reason := [convert(procname,string),"R is not a relation on A",R,A,reason];
  return false;
 fi;

 if not(`is_reflexive/autorel`(A)(R)) then
  reason := [convert(procname,string),"R is not reflexive",R];
  return false;
 fi;
 
 if not(`is_symmetric/autorel`(A)(R)) then
  reason := [convert(procname,string),"R is not symmetric",R];
  return false;
 fi;
 
 if not(`is_transitive/autorel`(A)(R)) then
  reason := [convert(procname,string),"R is not transitive",R];
  return false;
 fi;
 
 return true;
end;

`is_equal/equiv`     := eval(`is_equal/autorel`);
`is_leq/equiv`       := eval(`is_leq/autorel`);
`is_separated/equiv` := eval(`is_separated/autorel`);

`is_total/equiv`     := (A::set) -> proc(R)
 local U;

 U := {seq(seq([a,b],b in A),a in A)} minus R;

 return evalb(U = {}); 
end;

`block_partition/equiv` := (A::set) -> proc(R)
 local pi,X,x,B;

 pi := NULL;
 X := A;

 while X <> {} do
  x := X[1];
  B := map(ab -> ab[2],select(ab -> ab[1] = x,R));
  pi := pi,B;
  X := X minus B;
 od:

 pi := {pi};

 return pi;
end:

`block_equiv/partition` := (A::set) -> proc(pi)
 local B,x,y;
 {seq(seq(seq([x,y],y in B),x in B),B in pi)};
end;

`equiv_is_equiv` := (A::set) -> (R) -> (a,b) ->
  member([a,b],R);

`random_element/equiv` := (A::set) -> proc()
 `block_equiv/partition`(A)(`random_element/partitions`(A)());
end;

`list_elements/equiv` := proc(A::set)
 map(`block_equiv/partition`(A),
     `list_elements/partitions`(A));
end:

`count_elements/equiv` := (A::set) -> combinat[bell](nops(A));
