######################################################################
# proper_nonempty_subsets(A) is the set of all proper nonempty subsets of A

`is_element/proper_nonempty_subsets` := (A::set) -> proc(B)
 type(B,set) and B minus A = {} and nops(B) > 0 and nops(B) < nops(A);
end;

`is_equal/proper_nonempty_subsets` := (A::set) -> (B,C) -> evalb(B = C):

`is_leq/proper_nonempty_subsets` := (A::set) -> (B,C) -> evalb(B minus C = {}):

`random_element/proper_nonempty_subsets` := (A::set) -> proc()
 local n,r,B;

 n := nops(A);

 if n < 2 then return FAIL; fi;

 r := rand(2);
 B := {};

 while nops(B) = 0 or nops(B) = n do
  B := select(a -> (r() = 1),A);
 od;

 return B;
end;

`list_elements/proper_nonempty_subsets` := (A::set) -> 
 sort(map(sort,[op(combinat[powerset](A) minus {{},A})])):

`count_elements/proper_nonempty_subsets` := (A::set) -> 2^nops(A) - 2;
