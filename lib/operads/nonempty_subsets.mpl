######################################################################

`eta/nonempty_subsets` := (A::set) -> `if`(nops(A)=1,A,FAIL);

`gamma/nonempty_subsets` := (A::set,B::set) -> (p) -> proc(U,V)
 map(op,map(u -> V[u],U));
end;

