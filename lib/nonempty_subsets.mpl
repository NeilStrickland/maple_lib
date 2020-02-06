######################################################################
# nonempty_subsets(A) is the set of all nonempty subsets of A

`is_element/nonempty_subsets` := (A::set) -> proc(B)
 type(B,set) and B minus A = {} and nops(B) > 0;
end;

`is_equal/nonempty_subsets` := (A::set) -> (B,C) -> evalb(B = C):

`is_leq/nonempty_subsets` := (A::set) -> (B,C) -> evalb(B minus C = {}):

`random_element/nonempty_subsets` := (A::set) -> proc()
 local r,B;

 if nops(A) = 0 then return FAIL; fi;

 r := rand(2);
 B := {};

 while nops(B) = 0 do
  B := select(a -> (r() = 1),A);
 od;

 return B;
end;

`list_elements/nonempty_subsets` := (A::set) -> 
 sort(map(sort,[op(combinat[powerset](A) minus {{}})])):

`count_elements/nonempty_subsets` := (A::set) -> 2^nops(A) - 1;
