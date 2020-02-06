######################################################################

`is_element/stasheff_trees` := (A::set) -> proc(RTT)
 local R,TT,r,rf,TT1,T,T1,i;
 global reason;

 if not(type(RTT,list) and nops(RTT) = 2) then
  reason := [convert(procname,string),"RTT cannot be split as [R,TT]",RTT];  
  return false;
 fi;

 R,TT := op(RTT);

 if not(`is_element/ord`(A)(R)) then
  reason := [convert(procname,string),"R is not an ordering",R,reason];
  return false;
 fi;

 if not(`is_element/full_trees`(A)(TT)) then
  reason := [convert(procname,string),"TT is not a full tree",TT,reason];
  return false;
 fi;

 r := table();
 for i from 1 to nops(R) do r[R[i]] := i; od;
 rf := (a) -> r[a];

 for T in TT do
  T1 := map(rf,T);
  if nops(T1) <> (max(T1) - min(T1) + 1) then
   reason := [convert(procname,string),"T is not an R-interval",T,R,T1];
   return false; 
  fi;
 od;

 return true;
end;

`is_equal/stasheff_trees` := (A::set) -> proc(RTT1,RTT2)
 local R1,TT1,R2,TT2;

 R1,TT1 := op(RTT1);
 R2,TT2 := op(RTT2);
 return `is_equal/ord`(A)(R1,R2) and `is_equal/trees`(A)(TT1,TT2);
end:

`is_leq/stasheff_trees` := (A::set) -> proc(RTT1,RTT2)
 local R1,TT1,R2,TT2;

 R1,TT1 := op(RTT1);
 R2,TT2 := op(RTT2);
 return `is_equal/ord`(A)(R1,R2) and `is_leq/trees`(A)(TT1,TT2);
end:

`random_element/stasheff_trees` := (A::set) -> proc()
 local n,R,TT;

 n := nops(A);

 if n = 0 then return FAIL; fi;

 R := `random_element/ord`(A)(); 
 TT := `random_element/standard_stasheff_trees`(n)();
 TT := map(U -> map(u -> R[u],U),TT);

 return([R,TT]);
end;

`list_elements/stasheff_trees` := proc(A::set)
 local n,RR,R,TTT0,TT0,TT,XX;

 n := nops(A);

 RR := `list_elements/ord`(A);
 TTT0 := `list_elements/standard_stasheff_trees`(n);

 XX := NULL;
 for R in RR do
  for TT0 in TTT0 do
   TT := map(U -> map(u -> R[u],U),TT0);
   XX := XX,[R,TT];
  od;
 od;
 return([XX]);
end;

`count_elements/stasheff_trees` := proc(A::set)
 local n,m;
 n := nops(A);
 m := `count_elements/standard_stasheff_trees`(n);
 return n! * m;
end;


