`is_element/permutations` := (n::nonnegint) -> proc(s)
 type(s,list(posint)) and
 nops(s) = n and
 min(op(s)) = 1 and
 max(op(s)) = n and 
 nops({op(s)}) = n;
end:

`is_equal/permutations` := (n) -> (s,t) -> evalb(s = t);

`is_leq/permutations` := NULL;

`random_element/permutations` := (n::nonnegint) ->
 combinat[randperm](n);
 
`list_elements/permutations` := (n::nonnegint) ->
 combinat[permute](n);

`count_elements/permutations` := (n::nonnegint) -> n!;

`id/permutations` := (n::nonnegint) -> [seq(i,i=1..n)];

`o/permutations` := (n::nonnegint) -> proc()
 apply_assoc((s,t) -> [seq(s[t[i]],i=1..n)],
             [seq(i,i=1..n)])(args);
end:

`inv/permutations` := (n::nonnegint) -> proc(s)
 local i,t;
 t := table();
 for i from 1 to n do t[s[i]] := i; od;
 return [seq(t[i],i=1..n)];
end:

`length_set/permutations` := (n::nonnegint) -> proc(s)
 local L;

 L := [seq(seq([i,j],j=i+1..n),i=1..n-1)];
 L := select(ij -> s[ij[1]] > s[ij[2]],L);
 return L;
end:

`unordered_length_set/permutations` := (n::nonnegint) -> (s) ->
  map(u -> {op(u)},{op(`length_set/permutations`(n)(s))});

`length/permutations` := (n::nonnegint) -> proc(s)
 nops(`length_set/permutations`(n)(s));
end:

`sgn/permutations` := (n::nonnegint) -> (s) ->
 signum(mul(mul(s[j]-s[i],j=i+1..n),i=1..n-1));

`is_even/permutations` := (n::nonnegint) -> (s) ->
 evalb(`sgn/permutations`(n)(s) =  1);

`is_odd/permutations` := (n::nonnegint) -> (s) ->
 evalb(`sgn/permutations`(n)(s) = -1);

`switch/permutations` := (n::nonnegint) -> proc(i::posint)
  if i >= n then error("Should have 1 <= i < n"); fi;

  return [seq(j,j=1..i-1),i+1,i,seq(j,j=i+2..n)];
end:

# This algorithm does not always produce a reduced word.
# To do that, we would need an algorithm that is more aligned
# with the proof of completeness of the Coxeter relations.
`to_coxeter_word/permutations` := (n::nonnegint) -> proc(w)
 local i,v;
 i := n-1;
 while i > 0 and w[i] < w[i+1] do i := i - 1; od;
 if i = 0 then return []; fi;
 v := `o/permutations`(n)(w,`switch/permutations`(n)(i));
 return [op(`to_coxeter_word/permutations`(n)(v)),i];
end:

`from_coxeter_word/permutations` := (n::nonnegint) -> proc(x)
 `o/permutations`(n)(op(map(`switch/permutations`(n),x)));
end:

# Here are two kinds of Coxeter words that reduce to the identity.
# They are used in the proof of the completeness of the Coxeter relations.

`long_coxeter_rel0/permutations` := (n) -> (l) -> 
  [seq(i,i=l..n-1),seq(i,i=l..n-1),seq(i,i=n-2..l,-1),seq(i,i=n-1..l+1,-1)];

`long_coxeter_rel1/permutations` := (n) -> (k,l) -> 
  `if`(k <= l, 
       [seq(i,i=k..n-1),seq(i,i=l..n-1),seq(i,i=n-2..k,-1),seq(i,i=n-1..l+1,-1)],
       [seq(i,i=k..n-1),seq(i,i=l..n-1),seq(i,i=n-2..k-1,-1),seq(i,i=n-1..l,-1)]):

`coxeter_reduce_once/permutations` := (n) -> proc(x)
 local i,j,k,l,l0,l1,m,p,d,y,z,i0,p0,d0,z0,z1,z2;
 
 # Move s[p] left of s[q] if p < q - 1
 y := x;
 m := nops(y);
 z := [];
 i := 1;
 while i <= m do
  j := i + 1;
  while j <= m and y[j] < y[i] - 1 do
   z := [op(z),y[j]];
   j := j + 1;
  od;
  z := [op(z),y[i]];
  i := j;
 od;
 y := z;
 m := nops(y);
 
 z := [];
 i := 1;
 j := 1;
 while i <= m do 
  while (j < m and y[j+1] = y[i]) do j := j + 1; od;
  if modp(j - i + 1,2) = 1 then z := [op(z),y[i]]; fi;
  i := j + 1;
  j := i;
 od;
 y := z;
 m := nops(y);

 d := table():
 l := table():
 i0 := 0;
 l0 := 0;

 for i from 1 to m do
  if i < m and abs(y[i+1] - y[i]) = 1 then
   d[i] := y[i+1] - y[i];
   j := i + 1;
   while j <= m and y[j] = y[i] + modp(j - i,2) * d[i] do j := j + 1; od;
   l[i] := j - i;
  else
   d[i] := 0;
   l[i] := 1;
  fi;
  if l[i] > l0 then
   i0 := i;
   l0 := l[i];
  fi;
 od:

 if l0 < 3 then return y; fi;

 z0 := [seq(y[i],i=1..i0-1)];
 z2 := [seq(y[i],i=i0+l0..m)];
 l1 := mods(l0,6);
 p0 := y[i0];
 d0 := d[i0];
 
 if   l1 = 0             then z1 := []; 
 elif l1 = 1             then z1 := [p0];  
 elif l1 = 2             then z1 := [p0,p0+d0];
 elif l1 = 3 and d0 =  1 then z1 := [p0,p0+1,p0];
 elif l1 = 3 and d0 = -1 then z1 := [p0-1,p0,p0-1];
 elif l1 = -2            then z1 := [p0+d0,p0];
 elif l1 = -1            then z1 := [p0+d0];
 fi;

 return [op(z0),op(z1),op(z2)];
end:

`coxeter_reduce/permutations` := (n) -> proc(w)
 local u,v;
 u := NULL;
 v := w;
 while u <> v do
  u := v;
  v := `coxeter_reduce_once/permutations`(n)(u);
 od:
 return u;
end: