######################################################################

`is_element/linord` := (A::set) -> proc(L)
 global reason;

 if not type(L,list) then
  reason := ["is_element/linord","L is not a list",L];
  return false;
 fi;

 if nops(L) <> nops(A) then 
  reason := ["is_element/linord","L does not the same length as A",L,A];
  return false;
 fi;
 
 if {op(L)} <> A then
  reason := ["is_element/linord","L is not an enumeration of A",L,A];
  return false;
 fi;
 
 return true;
end;

######################################################################

`is_equal/linord` := (A::set) -> proc(L0,L1)
 return evalb(L0 = L1);
end;

######################################################################

`op/linord` := (A::set) -> proc(L)
 local n;
 n := nops(A);
 return [seq(L[n-i],i=0..n-1)];
end;

`res/linord` := (A::set,B::set) -> proc(L)
 return select(a -> member(a,B),L);
end:

######################################################################

`flip/linord` := (A::set) -> (L) -> proc(a)
 local n,i;
 n := nops(L);
 if n <= 1 then return L; fi;
 i := 1;
 while i <= n and L[i] <> a do i := i+1; od;
 if i > n then error("a is not in L"); fi;
 return [op(i..n,L),op(1..i-1,L)];
end:

`loop/linord` := (A::set) -> (L) -> L;

######################################################################

`random_element/linord` := (A::set) -> proc()
 return combinat[randperm](A);
end:

`list_elements/linord` := proc(A::set)
 return combinat[permute](A);
end:

`count_elements/linord` := proc(A::set)
 return nops(A) !;
end:

######################################################################

`linord_is_leq` := (A::set) -> (L) -> proc(a,b)
 local x;
 for x in L do
  if x = a then return true; fi;
  if x = b then return false; fi;
 od;
 error("Neither a nor b is in L");
end:

`linord_is_less` := (A::set) -> (L) -> proc(a,b)
 return evalb((a <> b) and `linord_is_leq`(A)(L)(a,b));
end:


