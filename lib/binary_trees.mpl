`is_element/binary_trees` := (A::set) -> proc(TT)
 global reason;
 
 if not(`is_element/full_trees`(A)(TT)) then
  reason := [convert(procname,string),"TT is not a full tree",TT,reason];
  return false;
 fi;

 if not(`is_binary/full_trees`(A)(TT)) then
  reason := [convert(procname,string),"TT is not binary",TT,reason];
  return false;
 fi;
end:

######################################################################

`is_equal/binary_trees` := eval(`is_equal/full_trees`);

######################################################################

`is_leq/binary_trees` := eval(`is_leq/full_trees`);

######################################################################

`list_elements/binary_trees` := proc(A::set) 
 option remember;
 local n,L,P,B,C,UUU,VVV;

 n := nops(A);

 if n = 0 then
  return [];
 elif n = 1 then 
  return [{A}];
 fi;

 L := NULL;
 P := `list_elements/nonempty_subsets`(A minus {A[n]});

 for B in P do
  C := A minus B;
  UUU := `list_elements/binary_trees`(B);
  VVV := `list_elements/binary_trees`(C);
  L := L,seq(seq({op(UU),op(VV),A},VV in VVV),UU in UUU);
 od;
 return [L];
end:

######################################################################

`random_element/binary_trees` := (A::set) -> proc()
 local n,B,C,UU,VV;

 n := nops(A);
 if n = 0 then return FAIL; fi;
 if n = 1 then return {A}; fi;
 B := `random_element/nonempty_subsets`(A minus {A[n]})();
 C := A minus B;
 UU := `random_element/binary_trees`(B)();
 VV := `random_element/binary_trees`(C)();
 return {op(UU),op(VV),A};
end:

######################################################################
# OEIS: A001147
`count_elements/binary_trees` := (A::set) -> mul(2*k-1,k=1..nops(A)-1);

