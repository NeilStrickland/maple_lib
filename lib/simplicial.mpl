# simplicial_interval(n) is just the set [n] = {0,1,...,n}

`is_element/simplicial_interval` := (n::nonnegint) -> proc(k)
 type(k,nonnegint) and k <= n;
end:

`is_equal/simplicial_interval` := (n::nonnegint) -> (a,b) -> evalb(a = b);

`is_leq/simplicial_interval` := (n::nonnegint) -> (a,b) -> evalb(a <= b);

`list_elements/simplicial_interval` := proc(n::nonnegint)
 local i;
 [seq(i,i=0..n)];
end:

`count_elements/simplicial_interval` := (n::nonnegint) -> n+1;

`random_element/simplicial_interval` := (n::nonnegint) -> proc()
 rand(0..n)();
end:

######################################################################

`is_element/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 global reason;
 local N,M,i;
 
 N := {seq(i,i=0..n)};
 M := {seq(i,i=0..m)};
 
 if not(`is_element/maps`(N,M)(f)) then
  reason := [convert(procname,string),"not a map from [n] to [m]",reason];
  return false;
 fi;

 for i from 0 to n-1 do
  if not(f[i] <= f[i+1]) then
   reason := [convert(procname,string),"f[i+1] > f[i]",i,f[i+1],f[i]];
   return false;
  fi;
 od;

 return true;
end:

`to_list/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 local i;
 return [seq(f[i],i=0..n)];
end:

`is_equal/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f,g)
 evalb(`to_list/simplicial_maps`(n,m)(f) = `to_list/simplicial_maps`(n,m)(g));
end:

`is_leq/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f,g)
 local u;
 u := `to_list/simplicial_maps`(n,m)(g) -~ `to_list/simplicial_maps`(n,m)(f);
 evalb( min(op(u)) >= 0 );
end:

# This assumes that 
# *  p is a subset of {1,...,n} of size k
# *  q is a subset of {0,...,m} of size k+1
# It returns the nondecreasing map f : {0,...,n} -> {0,...,m} such that
# *  The image of f is q
# * { i > 0 : f(i) > f(i-1) } = p.
 
`build/simplicial_maps` :=  (n::nonnegint,m::nonnegint) -> proc(k,p,q)
 local pp,i,j,f;
 pp := [0,op(p),n+1];
 f := table();
 i := 0;
 for i from 0 to k do
  for j from pp[i+1] to pp[i+2]-1 do
   f[j] := q[i+1];
  od;
 od;

 return eval(f); 
end:

`random_element/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc()
 local p,q,i,j,k,l,f;

 k := rand(0..min(n,m))();
 p := combinat[randcomb](n,k);
 q := combinat[randcomb](m+1,k+1) -~ 1;
 return `build/simplicial_maps`(n,m)(k,p,q);
end:

`list_elements/simplicial_maps` := proc(n::nonnegint,m::nonnegint)
 option remember;
 local i;
 
 if n = 0 then
  return [seq(`C/simplicial_maps`(0,i),i=0..m)];
 else
  if m = 0 then
   return [`C/simplicial_maps`(n,0)];
  else
   return [op(map(`I/simplicial_maps`(n,m-1),`list_elements/simplicial_maps`(n,m-1))),
           op(map(`T/simplicial_maps`(n-1,m),`list_elements/simplicial_maps`(n-1,m)))];
  fi;
 fi;
end:

`count_elements/simplicial_maps` := (n::nonnegint,m::nonnegint) -> binomial(n+m+1,m);

# Constant maps
`C/simplicial_maps` := proc(n::nonnegint,k::nonnegint)
 local i;
 table([seq(i=k,i=0..n)]);
end:

# Inclusion Delta(n,m) -> Delta(n,m+1)
`I/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 local i;
 table([seq(i=f[i],i=0..n)]);
end:

# Map Delta(n,m) -> Delta(n+1,m): extend by sending n+1 to m
`T/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 local i;
 table([seq(i=f[i],i=0..n),n+1=m]);
end:

# `delta/simplicial_maps`(n)(i) : [n] >-> [n+1]; image omits i 
`delta/simplicial_maps` := proc(n::nonnegint,i::nonnegint)
 local j;
 if i > n+1 then return FAIL; fi;
 return table([seq(j=j,j=0..i-1),seq(j=j+1,j=i..n)]);
end:

# `sigma/simplicial_maps`(n)(i) : [n] ->> [n-1]; takes the value i twice 
`sigma/simplicial_maps` := proc(n::nonnegint,i::nonnegint)
 local j;
 if i > n-1 then return FAIL; fi;
 return table([seq(j=j,j=0..i),seq(j=j-1,j=i+1..n)]);
end:

`id/simplicial_maps` := proc(n::nonnegint)
 local i;
 return table([seq(i=i,i=0..n)]);
end:

# `compose/simplicial_maps`(n,m,p)(f,g) assumes that f:[n] -> [m] and g:[m] -> [p],
# and it returns the composite g o f : [n] -> [p].

`compose/simplicial_maps` := (n::nonnegint,m::nonnegint,p::nonnegint) -> proc(f,g)
 local i;
 table([seq(i = g[f[i]],i=0..n)]);
end:

`is_wide/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 return evalb(f[0] = 0 and f[n] = m);
end:

`is_mono/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 local i;

 if m < n then return false; fi;
 for i from 0 to n-1 do
  if f[i] = f[i+1] then return false; fi;
 od;
 return true;
end:

`is_epi/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 local i,j;

 if n < m then return false; fi;
 if f[0] <> 0 then return false; fi;
 if f[n] <> m then return false; fi;

 j := 0;
 for i from 1 to n do
  if (f[i] <> j and f[i] <> j+1) then
   return false;
  fi;
  j := f[i];
 od;
 return true;
end:

# This assumes that f : [n] -> [m], and it returns [k,g,h] such that
# g : [n] ->> [k] and h : [k] >-> [m] and f = h o g

`factor/simplicial_maps` := (n::nonnegint,m::nonnegint) -> proc(f)
 local K,k,g,h,hi,i;
 
 K := sort([op({seq(f[i],i=0..n)})]);
 k := nops(K) - 1;
 h := table([seq(i=K[i+1],i=0..k)]);
 hi := table();
 for i from 0 to k do hi[h[i]] := i; od;
 g := table([seq(i = hi[f[i]],i=0..n)]);
 return [k,eval(g),eval(h)];
end:

`describe/simplicial_maps` := (n::nonnegint) -> proc(f)
 local i;
 cat(seq(nat_code[f[i]],i=0..n));
end:

######################################################################

`is_element/simplicial_epi` := (n::nonnegint,m::nonnegint) -> proc(f)
 global reason;
 
 if not(`is_element/simplicial_maps`(n,m)(f)) then
  reason := [convert(procname,string),"not a simplicial map from [n] to [m]",reason];
  return false;
 fi;

 return `is_epi/simplicial_maps`(n,m)(f);
end:

`is_equal/simplicial_epi` :=  (n::nonnegint,m::nonnegint) -> proc(f,g)
 `is_equal/simplicial_maps`(n,m)(f,g);
end:

`is_leq/simplicial_epi` :=  (n::nonnegint,m::nonnegint) -> proc(f,g)
 `is_leq/simplicial_maps`(n,m)(f,g);
end:

`random_element/simplicial_epi` := (n::nonnegint,m::nonnegint) -> proc()
 local p,q,k,f,i;

 if n < m then return FAIL; fi;

 k := m;
 p := combinat[randcomb](n,k);
 q := [seq(i,i=0..m)];
 return `build/simplicial_maps`(n,m)(k,p,q);
end:

`list_elements/simplicial_epi` := proc(n::nonnegint,m::nonnegint) 
 local P,L,S,f,i,j;

 P := combinat[choose]([seq(i,i=1..n)],m);
 L := [];
 for S in P do
  f := table();
  for i from 0 to S[1]-1 do f[i] := 0; od;
  for j from 1 to m-1 do 
   for i from S[j] to S[j+1]-1 do f[i] := j; od;
  od;
  for i from S[m] to n do f[i] := m; od;
  L := [op(L),eval(f)]; 
 od:

 return L;
end:

`count_elements/simplicial_epi` := (n::nonnegint,m::nonnegint) -> binomial(n,m);

######################################################################

`is_element/simplicial_mono` := (n::nonnegint,m::nonnegint) -> proc(f)
 global reason;
 
 if not(`is_element/simplicial_maps`(n,m)(f)) then
  reason := [convert(procname,string),"not a simplicial map from [n] to [m]",reason];
  return false;
 fi;

 return `is_mono/simplicial_maps`(n,m)(f);
end:

`is_equal/simplicial_mono` :=  (n::nonnegint,m::nonnegint) -> proc(f,g)
 `is_equal/simplicial_maps`(n,m)(f,g);
end:

`is_leq/simplicial_mono` :=  (n::nonnegint,m::nonnegint) -> proc(f,g)
 `is_leq/simplicial_maps`(n,m)(f,g);
end:

`random_element/simplicial_mono` := (n::nonnegint,m::nonnegint) -> proc()
 local p,q,i,j,k,l,f;

 if n > m then return FAIL; fi;

 k := n;
 p := [seq(i,i=1..n)];
 q := combinat[randcomb](m+1,k+1) -~ 1;
 return `build/simplicial_maps`(n,m)(k,p,q);
end:

`list_elements/simplicial_mono` := proc(n::nonnegint,m::nonnegint) 
 local P,L,S,f,i,j;

 P := combinat[choose]([seq(i,i=0..m)],n+1);
 L := [];
 for S in P do
  f := table();
  for i from 0 to n do f[i] := S[i+1]; od;
  L := [op(L),eval(f)]; 
 od:

 return L;
end:

`count_elements/simplicial_mono` := (n::nonnegint,m::nonnegint) -> binomial(m+1,n+1);



