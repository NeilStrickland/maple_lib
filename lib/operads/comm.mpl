######################################################################
# Commutative operad

`is_element/comm` := (A::set) -> (z) -> type(z,identical(0));

`is_equal/comm` := (A::set) -> (x,y) -> true;

`is_leq/comm` := (A::set) -> (x,y) -> true;

`random_element/comm` := (A::set) -> () -> 0;

`list_elements/comm` := (A::set) -> [0];

`count_elements/comm` := (A::set) -> 1;

`eta/comm` := (A::set) -> `if`(nops(A)=1,0,FAIL);

`gamma/comm` := (A::set,B::set) -> (p) -> (z,zz) -> 0;

