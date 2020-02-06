######################################################################
# pair_subsets(A) is the set of all subsets B of A with |B| = 2

`is_element/pair_subsets` := (A::set) -> proc(B)
 type(B,set) and B minus A = {} and nops(B) = 2;
end;

`is_equal/pair_subsets` := (A::set) -> (B,C) -> evalb(B = C):

`is_leq/pair_subsets` := NULL;

`random_element/pair_subsets` := (A::set) -> proc()
 local r,B;

 if nops(A) < 2 then return FAIL; fi;

 r := rand(1..nops(A));
 B := {};

 while nops(B) < 2 do
  B := [A[r()],A[r()]];
  B := {op(B)};
 od;

 return B;
end;

`list_elements/pair_subsets` := (A::set) ->
 [seq(seq({A[i],A[j]},j=i+1..nops(A)),i=1..nops(A)-1)];

`count_elements/pair_subsets` := (A::set) -> nops(A) * (nops(A) - 1)/2;
