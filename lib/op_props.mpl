is_left_unit := (A::set) -> (m,e) -> 
 `and`(seq(evalb(m(e,a)=a),a in A));

is_right_unit := (A::set) -> (m,e) -> 
 `and`(seq(evalb(m(a,e)=a),a in A));

is_left_absorbing := (A::set) -> (m,z) -> 
 `and`(seq(evalb(m(z,a)=z),a in A));

is_right_absorbing := (A::set) -> (m,z) -> 
 `and`(seq(evalb(m(a,z)=z),a in A));

is_idempotent := (A::set) -> (m) ->
 `and`(seq(evalb(m(a,a)=a),a in A));

is_commutative := (A::set) -> (m) -> 
 `and`(seq(seq(evalb(m(a,b) = m(b,a)),b in A),a in A));

is_associative := (A::set) -> (m) -> 
 `and`(seq(seq(seq(evalb(m(a,m(b,c))=m(m(a,b),c)),c in A),b in A),a in A));

is_left_distributive := (A::set) -> (m,p) -> 
 `and`(seq(seq(seq(evalb(m(a,p(b,c))=p(m(a,b),m(a,c))),c in A),b in A),a in A));

is_right_distributive := (A::set) -> (m,p) -> 
 `and`(seq(seq(seq(evalb(m(p(a,b),c)=p(m(a,c),m(b,c))),c in A),b in A),a in A));

is_monoid := (A::set) -> (m,e) -> 
 is_left_unit(A)(m,e) and is_right_unit(A)(m,e) and is_associative(A)(m);

is_semiring := (A::set) -> (m,p,e,z) -> 
 is_monoid(A)(m,e) and
 is_monoid(A)(p,z) and
 is_left_absorbing(A)(m,z) and
 is_right_absorbing(A)(m,z) and
 is_left_distributive(A)(m,p) and
 is_right_distributive(A)(m,p);
