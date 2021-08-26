######################################################################

# A full tree on A is a tree that contains A, and also contains {a}
# for all a in A.
# (Definition defn-full-trees)

`is_element/full_trees` := (A::set) -> proc(TT)
 local a;
 global reason;

 if not(`is_element/trees`(A)(TT)) then
  reason := [convert(procname,string),"TT is not a tree",TT,reason];
  return false;
 fi;
 if not(member(A,TT)) then
  reason := [convert(procname,string),"The full set A is not in TT",A,TT];
  return false;
 fi;

 for a in A do
  if not(member({a},TT)) then
   reason := [convert(procname,string),"The singleton {a} is not in TT",a,TT];
   return false;
  fi;  
 od;

 return true;
end;

`is_equal/full_trees` := eval(`is_equal/trees`);
`is_leq/full_trees` := eval(`is_leq/trees`);

# A full tree TT on A is binary if every non-minimal set in TT has
# precisely two children.  This holds iff |TT| = 2|A|-1.

`is_binary/full_trees` := (A) -> proc(TT)
 return evalb(nops(TT) = 2*nops(A)-1);
end:

`list_elements/full_trees`:= proc(A::set)
 local n,a,A1,TTT1,TTT,TT1,T1;

 # Degenerate cases for small A 
 if A={} then return []; fi;
 if nops(A)=1 then return [{A}]; fi;

 # If A is not too small, we write it as {a} union A1.  Then we recursively
 # choose a random tree on A1, and attach a to it.

 n := nops(A);
 a := A[n];
 A1 := A minus {a};
 TTT1 := `list_elements/full_trees`(A1);

 TTT := [];
 for TT1 in TTT1 do
  for T1 in TT1 do
   TTT := [op(TTT),`attach_to_tree`(A1)(TT1,T1,a,true)];
   if n > 2 and nops(T1) > 1 then
    TTT := [op(TTT),`attach_to_tree`(A1)(TT1,T1,a,false)];
   fi;
  od;
 od;
 
 return TTT;
end:

# A000311 from OEIS

`count_elements/full_trees` := proc(A::set)
 local n,i,j,k;
 n := nops(A);
 if n = 0 then
  return 0;
 elif n  = 1 then
  return 1;
 else
  return 
   add(
    (n+k-1)!*
    add(
     1/(k-j)! * 
     add(
     (2^i*(-1)^(i)*Stirling2(n+j-i-1,j-i))/((n+j-i-1)!*i!),
     i=0..j),
    j=1..k),
   k=1..n-1);
 fi;
end;

`random_element/full_trees`:= (A::set) -> proc()
 local n,a,A1,T0,T1,T,above;

 # Degenerate cases for small A 
 if A={} then return FAIL; fi;
 if nops(A)=1 then return {A}; fi;

 # If A is not too small, we write it as {a} union A1.  Then we recursively
 # choose a random tree on A1, and attach a to it.

 n := nops(A);
 a := A[rand(1..n)()];
 A1 := A minus {a};
 if n = 2 then
  above := true;
 else
  above := evalb(rand(0..1)() = 1);
 fi;

 T0 := `random_element/full_trees`(A1)();
 T1 := select(U -> nops(U) > 1,T0);

 if above then
  T := T0[rand(1..nops(T0))()];
 else
  T := T1[rand(1..nops(T1))()];
 fi;

 T := `attach_to_tree`(A1)(T0,T,a,above);
 
 return T;
end;

