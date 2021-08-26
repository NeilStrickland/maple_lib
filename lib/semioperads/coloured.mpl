`is_element/colour_profiles` := (C::set) -> (n::nonnegint) -> proc(c)
 type(c,list) and nops(c) = n and {op(c)} minus C = {};
end:

`is_equal/colour_profiles` := (C::set) -> (n::nonnegint) -> (c,b) -> evalb(c = b);

`list_elements/colour_profiles` := (C::set) -> proc(n::nonnegint)
 local L,i,x,c;
 L := [[]];
 for i from 1 to n do
  L := [seq(seq([op(c),x],x in C),c in L)];
 od:
 return L;
end:

`count_elements/colour_profiles` := (C::set) -> (n::nonnegint) -> nops(C)^n;

`random_element/colour_profiles` := (C::set) -> (n::nonnegint) -> proc()
 local i;
 [seq(random_element_of(C),i=1..n)];
end:

`o/colour_profiles` := proc() map(op,[args]); end:

`gamma/colour_profiles` := (C::set) -> (L::list(nonnegint)) -> proc(c,d)
 map(op,d);
end:

`circ/colour_profiles` := (C::set) -> (i,m,n) -> proc(c,b)
 [op(1..i-1,c),op(b),op(i+1..m,c)];
end:
