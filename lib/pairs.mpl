######################################################################
# pairs(A) is the set of all pairs (a,b) in A^2 with a <> b

`is_element/pairs` := (A::set) -> proc(ab)
 type(ab,list) and nops(ab) = 2 and
 member(ab[1],A) and member(ab[2],A) and ab[1] <> ab[2];
end;

`is_equal/pairs` := (A::set) -> (ab,cd) -> evalb(ab = cd):

`is_leq/pairs` := NULL;

`random_element/pairs` := (A::set) -> proc()
 local n,r,i,j;
 n := nops(A);

 if n < 2 then return FAIL; fi;

 i := rand(1..n)(); 
 j := rand(1..n-1)();
 if j >= i then j := j+1; fi;

 return [A[i],A[j]];
end;

`list_elements/pairs` := proc(A::set)
 local n,i,j;

 n := nops(A);

 [seq(op([seq([A[i],A[j]],j=1..i-1),seq([A[i],A[j]],j=i+1..n)]),i=1..n)];
end:

`count_elements/pairs` := (A::set) -> nops(A) * (nops(A)-1);
