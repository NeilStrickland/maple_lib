######################################################################
# An ordering of a set A is encoded as a list containing each element 
# of A precisely once.

`is_element/ord` := (A::set) -> proc(R)
 type(R,list) and nops(R) = nops(A) and {op(R)} = A;
end;

`is_equal/ord` := (A::set) -> (R,S) -> evalb(R = S);

`is_leq/ord` := NULL;

`random_element/ord` := (A::set) -> () -> combinat[randperm]([op(A)]);

`list_elements/ord` := (A::set) -> combinat[permute](sort([op(A)]));

`count_elements/ord` := (A::set) -> nops(A)!;

`rank_table/ord` := (A::set) -> proc(R)
 table([seq(R[i] = i, i = 1 .. nops(R))]):
end: