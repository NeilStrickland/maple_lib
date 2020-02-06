######################################################################
# subsets(A) is the set of all subsets of A

`is_element/subsets` := (A::set) -> proc(B)
 type(B,set) and B minus A = {};
end;

`is_equal/subsets` := (A::set) -> (B,C) -> evalb(B = C):

`is_leq/subsets` := (A::set) -> (B,C) -> evalb(B minus C = {}):

`random_element/subsets` := (A::set) -> proc()
 local r,B,a;
 r := rand(2);

 B := select(a -> (r() = 1),A);

 return B;
end;

`list_elements/subsets` := (A::set) -> 
 sort(map(sort,[op(combinat[powerset](A))])):

`count_elements/subsets` := (A::set) -> 2^nops(A);

`functor/subsets` := (A::set,B::set) -> (f) -> proc(T)
 map(t -> f[t],T);
end:

`cofunctor/subsets` := (A::set,B::set) -> (f) -> proc(T)
 select(a -> member(f[a],T),A);
end:
