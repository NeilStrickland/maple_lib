`is_element/morse_matchings` := (A::set) -> (R) -> proc(M)
 global reason;
 local e,H,F;
 
 if not(type(M,set)) then
  reason := ["is_element/morse_matchings","M is not a set",M];
  return false;
 fi;

 for e in M do 
  if not(type(e,list)) and nops(e) = 2 then
   reason := ["is_element/morse_matchings","M is not a set of lists of length 2",M,e];
   return false;
  fi;

  if {op(e)} minus A <> {} then
   reason := ["is_element/morse_matchings","M is not a set of lists of length 2 in A",M,e];
   return false;
  fi;
 od:

 H := `hasse_diagram/partord`(A)(R);

 if M minus H <> {} then
  reason := ["is_element/morse_matchings","M is not a subset of the Hasse diagram",M,H];
  return false;
 fi;

 for e in M do
  if select(f -> {op(f)} intersect {op(e)} <> {}, M) <> {e} then
   reason := ["is_element/morse_matchings","edges in M are not disjoint",M,e];
   return false;
  fi;
 od:

 F := M union map(e -> [e[2],e[1]],H minus M);
 F := `transitive_closure/autorel`(A)(F);
 F := F intersect `op/autorel`(A)(F);
 if F minus `id/autorel`(A) <> {} then
  reason := ["is_element/morse_matchings","M has cycles",M,F];
  return false;
 fi;

 return true;
end:
