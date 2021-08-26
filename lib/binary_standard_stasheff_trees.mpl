`is_element/binary_standard_stasheff_trees` := (n::posint) -> proc(TT)
 global reason;
 
 if not(`is_element/standard_stasheff_trees`(n)(TT)) then
  reason := [convert(procname,string),"TT is not a standard Stasheff tree",TT,reason];
  return false;
 fi;

 if not(`is_binary/standard_stasheff_trees`(n)(TT)) then
  reason := [convert(procname,string),"TT is not binary",TT,reason];
  return false;
 fi;

 return true;
end:

`is_equal/binary_standard_stasheff_trees` :=
 eval(`is_equal/standard_stasheff_trees`);

`is_leq/binary_standard_stasheff_trees` :=
 eval(`is_leq/standard_stasheff_trees`);

`list_elements/binary_standard_stasheff_trees` := proc(n::posint) 
 option remember;
 local L,A,UUU,VVV,UU,VV,p,i;

 if n = 0 then
  return [];
 elif n = 1 then 
  return [{{1}}];
 fi;

 L := NULL;
 A := {seq(i,i=1..n)};

 for p from 1 to n-1 do
  UUU := `list_elements/binary_standard_stasheff_trees`(p);
  VVV := `list_elements/binary_standard_stasheff_trees`(n-p);
  VVV := map(VV -> map(V -> map(v -> v+p,V),VV),VVV);
  L := L,seq(seq({op(UU),op(VV),A},VV in VVV),UU in UUU);
 od;
 return [L];
end:

`random_element/binary_standard_stasheff_trees` := (n::posint) -> proc()
 local L;

 L := `list_elements/binary_standard_stasheff_trees`(n);
 L[rand(1..nops(L))()];
end:

`count_elements/binary_standard_stasheff_trees` :=
 (n::posint) -> binomial(2*(n-1),n-1)/n;

