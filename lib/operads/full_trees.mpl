######################################################################

`eta/full_trees` := (A::set) -> `eta/trees`(A);

`gamma/full_trees` := (A::set,B::set) -> (p) -> (TT,UU) ->
  `gamma/trees`(A,B)(p)(TT,UU);

