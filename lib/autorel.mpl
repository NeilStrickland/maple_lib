`is_element/autorel` := (A::set) -> proc(R)
 `is_element/rel`(A,A)(R);
end;

`is_equal/autorel` := (A::set) -> (R,S) -> `is_equal/rel`(A,A)(R,S);
`is_leq/autorel`   := (A::set) -> (R,S) -> `is_leq/rel`(A,A)(R,S);
`bot/autorel` := (A::set) -> `bot/rel`(A,A);
`top/autorel` := (A::set) -> `top/rel`(A,A);

`is_a_function/autorel` := (A::set) -> (R) -> `is_a_function/rel`(A,A)(R);
`is_total/autorel` := (A::set) -> (R) -> `is_total/rel`(A,A)(R);

`op/autorel` := (A::set) -> (R) -> `op/rel`(A,A)(R);

`hash/autorel` := (A::set) -> (R) -> `hash/rel`(A,A)(R);
`unhash/autorel` := (A::set) -> (r) -> `unhash/rel`(A,A)(r);

`id/autorel` := (A::set) -> `id/rel`(A);

`o/autorel` := (A::set) -> (S,R) -> `o/rel`(A,A,A)(S,R);

`is_reflexive/autorel` := (A::set) -> proc(R)
 return evalb(`id/autorel`(A) minus R = {});
end;

`is_irreflexive/autorel` := (A::set) -> proc(R)
 return evalb(`id/autorel`(A) intersect R = {});
end;

`is_symmetric/autorel` := (A::set) -> proc(R)
 return evalb(R = `op/autorel`(A)(R));
end;

`is_antisymmetric/autorel` := (A::set) -> proc(R)
 return evalb(R intersect `op/autorel`(A)(R) = {});
end;

`is_transitive/autorel` := (A::set) -> proc(R)
 local RR;
 RR := `o/autorel`(A)(R,R);
 return evalb(`is_leq/autorel`(A)(RR,R));
end;

`is_separated/autorel` := (A::set) -> proc(R)
 return evalb((R intersect `op/autorel`(A)(R)) minus `id/autorel`(A) = {});
end;

`list_elements/autorel` := (A::set) -> `list_elements/rel`(A,A);
`count_elements/autorel` := (A::set) -> 2^(nops(A)^2);

`random_element/autorel` := (A::set) -> (p_) -> `random_element/rel`(A,A)(args);

`transitive_closure/autorel` := (A::set) -> proc(R)
 local S,n0,n1;
 
 S := `id/autorel`(A) union R;
 n0 := 0;
 n1 := nops(S);
 while n1 > n0 do
  n0 := n1;
  S := `o/autorel`(A)(S,S);
  n1 := nops(S);
 od;

 return S;
end;

`cofunctor/autorel` := (A::set,B::set) -> (f) -> proc(R)
 local AA;
 
 AA := `top/autorel`(A);
 return select(aa -> member([f[aa[1]],f[aa[2]]],R),AA);
end;

`reindex_standard/autorel` := (A::set) -> proc(R)
 local n,i,f,N,R0;
 
 n := nops(A);
 f := table();
 for i from 1 to n do f[A[i]] := i; od;
 N := {seq(i,i=1..n)};
 R0 := map(aa -> [f[aa[1]],f[aa[2]]],R);
 return [N,R0];
end;