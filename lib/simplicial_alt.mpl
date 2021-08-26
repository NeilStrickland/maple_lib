# This file sets up the theory of the simplicial category, with simplicial
# maps encoded as lists of values.  This is an alternative to simplicial.mpl,
# where simplicial maps are encoded as tables.  This version is more efficient,
# but suffers from the fact that Maple uses 1-based indexing, so we need a
# lot of extra +1's.

`is_element/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 evalb(type(f,list(nonnegint)) and nops(f) = n+1 and max(op(f)) <= m) 
end:

`is_leq/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f,g)
 evalb( min(op(g -~ f)) >= 0 );
end:

# This assumes that 
# *  p is a subset of {1,...,n} of size k
# *  q is a subset of {0,...,m} of size k+1
# It returns the nondecreasing map f : {0,...,n} -> {0,...,m} such that
# *  The image of f is q
# * { i > 0 : f(i) > f(i-1) } = p.
 
`build/simplicial_maps_alt` :=  (n::nonnegint,m::nonnegint) -> proc(k,p,q)
 local pp,i,j,f;
 pp := [0,op(p),n+1];
 f := NULL;
 i := 0;
 for i from 0 to k do
  for j from pp[i+1] to pp[i+2]-1 do
   f := f,q[i+1];
  od;
 od;

 return [f];
end:

`random_element/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc()
 local p,q,i,j,k,l,f;

 k := rand(0..min(n,m))();
 p := combinat[randcomb](n,k);
 q := combinat[randcomb](m+1,k+1) -~ 1;
 return `build/simplicial_maps_alt`(n,m)(k,p,q);
end:

`list_elements/simplicial_maps_alt` := proc(n::nonnegint,m::nonnegint)
 option remember;
 local i;
 
 if n = 0 then
  return [seq(`C/simplicial_maps_alt`(0,i),i=0..m)];
 else
  if m = 0 then
   return [`C/simplicial_maps_alt`(n,0)];
  else
   return [op(map(`I/simplicial_maps_alt`(n,m-1),
                   `list_elements/simplicial_maps_alt`(n,m-1))),
           op(map(`T/simplicial_maps_alt`(n-1,m),
	           `list_elements/simplicial_maps_alt`(n-1,m)))];
  fi;
 fi;
end:

`count_elements/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> binomial(n+m+1,m);

# Constant maps
`C/simplicial_maps_alt` := proc(n::nonnegint,k::nonnegint)
 [k$(n+1)]
end:

# Inclusion Delta(n,m) -> Delta(n,m+1)
`I/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 f;
end:

# Map Delta(n,m) -> Delta(n+1,m): extend by sending n+1 to m
`T/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 [op(f),m];
end:

# `delta/simplicial_maps_alt`(n)(i) : [n] >-> [n+1]; image omits i 
`delta/simplicial_maps_alt` := proc(n::nonnegint,i::nonnegint)
 local j;
 if i > n+1 then return FAIL; fi;
 return [seq(j,j=0..i-1),seq(j+1,j=i..n)];
end:

# `sigma/simplicial_maps_alt`(n)(i) : [n] ->> [n-1]; takes the value i twice 
`sigma/simplicial_maps_alt` := proc(n::nonnegint,i::nonnegint)
 local j;
 if i > n-1 then return FAIL; fi;
 return [seq(j,j=0..i),seq(j-1,j=i+1..n)];
end:

`id/simplicial_maps_alt` := proc(n::nonnegint)
 local i;
 return [seq(i=i,i=0..n)];
end:

`eval/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> (f) -> (i) -> f[i+1];

# `compose/simplicial_maps`(n,m,p)(f,g) assumes that f:[n] -> [m] and g:[m] -> [p],
# and it returns the composite g o f : [n] -> [p].

`compose/simplicial_maps_alt` := (n::nonnegint,m::nonnegint,p::nonnegint) -> proc(f,g)
 local i;
 [seq(g[f[i+1]+1],i=0..n)];
end:

`is_wide/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 return evalb(f[1] = 0 and f[n+1] = m);
end:

`is_mono/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 evalb(nops({op(f)}) = n+1);
end:

`is_epi/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 local j;
 evalb({op(f)} = {seq(j,j=0..m)});
end:

# This assumes that f : [n] -> [m], and it returns [k,g,h] such that
# g : [n] ->> [k] and h : [k] >-> [m] and f = h o g

`factor/simplicial_maps_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 local K,k,g,h,hi,i;
 
 h := sort([op({op(f)})]);
 k := nops(h) - 1;
 hi := table();
 for i from 0 to k do hi[h[i+1]] := i; od;
 g := [seq(hi[f[i+1]],i=0..n)];
 return [k,g,h];
end:

`describe/simplicial_maps_alt` := (n::nonnegint) -> proc(f)
 local i;
 cat(seq(nat_code[f[i]],i=1..n+1));
end:

######################################################################

`is_element/simplicial_epi_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 global reason;
 
 if not(`is_element/simplicial_maps_alt`(n,m)(f)) then
  reason := [convert(procname,string),"not a simplicial map from [n] to [m]",reason];
  return false;
 fi;

 return `is_epi/simplicial_maps_alt`(n,m)(f);
end:

`is_leq/simplicial_epi_alt` :=  (n::nonnegint,m::nonnegint) -> proc(f,g)
 `is_leq/simplicial_maps_alt`(n,m)(f,g);
end:

`random_element/simplicial_epi_alt` := (n::nonnegint,m::nonnegint) -> proc()
 local p,q,k,f,i;

 if n < m then return FAIL; fi;

 k := m;
 p := combinat[randcomb](n,k);
 q := [seq(i,i=0..m)];
 return `build/simplicial_maps_alt`(n,m)(k,p,q);
end:

`list_elements/simplicial_epi_alt` := proc(n::nonnegint,m::nonnegint) 
 local P,L,S,i,j;

 P := combinat[choose]([seq(i,i=1..n)],m);
 L := map(S -> [0$S[1],seq(j$(S[j+1]-S[j]),j=1..m-1),m$(n+1-S[m])],P);

 return L;
end:

`count_elements/simplicial_epi_alt` := (n::nonnegint,m::nonnegint) -> binomial(n,m);

######################################################################

`is_element/simplicial_mono_alt` := (n::nonnegint,m::nonnegint) -> proc(f)
 global reason;
 
 if not(`is_element/simplicial_maps_alt`(n,m)(f)) then
  reason := [convert(procname,string),"not a simplicial map from [n] to [m]",reason];
  return false;
 fi;

 return `is_mono/simplicial_maps_alt`(n,m)(f);
end:

`is_leq/simplicial_mono_alt` :=  (n::nonnegint,m::nonnegint) -> proc(f,g)
 `is_leq/simplicial_maps_alt`(n,m)(f,g);
end:

`random_element/simplicial_mono_alt` := (n::nonnegint,m::nonnegint) -> proc()
 local p,q,i,j,k,l,f;

 if n > m then return FAIL; fi;

 q := combinat[randcomb](m+1,n+1) -~ 1;
 q := sort([op(q)]);
 return q;
end:

`list_elements/simplicial_mono_alt` := proc(n::nonnegint,m::nonnegint) 
 map(q -> q -~ 1,combinat[choose](m+1,n+1));
end:

`count_elements/simplicial_mono_alt` := (n::nonnegint,m::nonnegint) -> binomial(m+1,n+1);



