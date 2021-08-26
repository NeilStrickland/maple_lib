######################################################################

`is_element/cycord` := (A::set) -> proc(C)
 global reason;

 if not type(C,list) then
  reason := ["is_element/cycord","C is not a list",C];
  return false;
 fi;

 if nops(C) <> nops(A) then 
  reason := ["is_element/cycord","C does not the same length as A",C,A];
  return false;
 fi;
 
 if {op(C)} <> A then
  reason := ["is_element/cycord","C is not an enumeration of A",C,A];
  return false;
 fi;
 
 return true;
end;

######################################################################

`is_equal/cycord` := (A::set) -> proc(C0,C1)
 local n,a,i,C2;

 n := nops(A);
 if n <= 2 then
  return true;
 fi;

 a := C0[1];
 i := 1;
 while i < n and C1[i] <> a do i := i+1; od;

 C2 := [op(i..n,C1),op(1..i-1,C1)];
 return evalb(C0 = C2);
end;

`is_leq/cycord` := NULL;

######################################################################

`op/cycord` := (A::set) -> proc(C)
 local n,i;
 n := nops(A);
 return [seq(C[n-i],i=0..n-1)];
end;

`res/cycord` := (A::set,B::set) -> proc(C)
 return select(a -> member(a,B),C);
end:

######################################################################

`random_element/cycord` := (A::set) -> proc()
 return combinat[randperm](A);
end:

`list_elements/cycord` := proc(A::set)
 local a,B;

 a := A[1];
 B := A minus {a};
 return map(C -> [a,op(C)],combinat[permute](B));
end:

`count_elements/cycord` := proc(A::set)
 return max(0,nops(A) - 1) !;
end:

######################################################################

`cut/cycord` := (A::set) -> (C) -> proc(a)
 local n,i;
 n := nops(C);
 if n <= 1 then return C; fi;
 i := 1;
 while i <= n and C[i] <> a do i := i+1; od;
 if i > n then error("a is not in C"); fi;
 return [op(i..n,C),op(1..i-1,C)];
end:

######################################################################

`cycord_is_strictly_cyclic` := (A::set) -> (C) -> proc(x::list)
 local n,S,a,i,y;
 
 n := nops(x);
 S := {op(x)};
 if n < 2 then return true; fi;
 if nops(S) < n then return false; fi;
 if S minus A <> {} then return false; fi;
 y := `cut/cycord`(A)(C)(x[1]);
 y := select(i -> member(i,S),y);
 return evalb(x = y);
end:

######################################################################

`cycord_is_cyclic` := (A::set) -> (C) -> proc(x)
 local n,y,i;
 n := nops(x);
 y := NULL;
 for i from 1 to n do
  if (i = n and x[n] <> x[1]) or (i < n and x[i] <> x[i+1]) then
   y := y,x[i];
  fi;
 od;
 y := [y];
 return `cycord_is_strictly_cyclic`(A)(C)(y);
end:

######################################################################

`open_interval/cycord` := (A::set) -> (C) -> proc(a,b)
 local n,i,J,C0;
 if a = b then return []; fi;
 C0 := `cut/cycord`(A)(C)(a);
 J := NULL;
 i := 2;
 n := nops(C0);
 while i <= n and C0[i] <> b do i := i+1; od;
 return [op(2..i-1,C0)];
end:

`half_open_interval/cycord` := (A::set) -> (C) -> proc(a,b)
 return [a,op(`open_interval/cycord`(A)(C)(a,b))];
end:

`closed_interval/cycord` := (A::set) -> (C) -> proc(a,b)
 return [a,op(`open_interval/cycord`(A)(C)(a,b)),b];
end:

`are_crossed/cycord` := (A::set) -> (C) -> proc(U,V)
 local C0,n,i,j,k;
 if U intersect V <> {} then return true; fi;
 if U = {} or V = {} then return false; fi;
 C0 := `cut/cycord`(A)(C)(U[1]);
 n := nops(C0);
 i := 2;
 while i <= n and not(member(C0[i],V)) do i := i+1; od;
 if i > n then return false; fi;
 j := i+1;
 while j <= n and not(member(C0[j],U)) do j := j+1; od;
 if j > n then return false; fi;
 k := j+1;
 while k <= n and not(member(C0[k],V)) do k := k+1; od;
 if k > n then return false; fi;
 return true;
end:

`is_convex/cycord` := (A::set) -> (C) -> proc(W)
 return not(`are_crossed/cycord`(A)(C)(W,A minus W));
end;