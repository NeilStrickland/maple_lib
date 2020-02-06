######################################################################
# big_subsets(A) is the set of all subsets B of A with |B| > 1

`is_element/big_subsets` := (A::set) -> proc(B)
 type(B,set) and B minus A = {} and nops(B) > 1;
end;

`is_equal/big_subsets` := (A::set) -> (B,C) -> evalb(B = C):

`is_leq/big_subsets` := (A::set) -> (B,C) -> evalb(B minus C = {}):

`random_element/big_subsets` := (A::set) -> proc()
 local r,B;

 if nops(A) < 2 then return FAIL; fi;

 r := rand(2);
 B := {};

 while nops(B) < 2 do
  B := select(a -> (r() = 1),A);
 od;

 return B;
end;

`list_elements/big_subsets` := (A::set) ->
 select(B -> nops(B) > 1,sort(map(sort,[op(combinat[powerset](A))]))):

`count_elements/big_subsets` := (A::set) ->
 2^nops(A) - nops(A) - 1;

