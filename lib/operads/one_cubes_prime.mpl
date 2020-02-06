######################################################################

`eta/one_cubes_prime` := (A::set) -> `eta/cubes`(1)(A);

`gamma/one_cubes_prime` :=
 (A::set,B::set) -> (p) -> (U,V) -> `gamma/cubes`(1)(A,B)(p)(U,V);

