# A (p,q)-Steiner system on a set A is a family of subsets of A (called blocks),
# each of size q, such that each subset of size p in A is contained ina unique
# block.

steiner_number_test := proc(p::posint,q::posint,n::posint)
 local i,m;
 for i from 0 to p-1 do
  m := binomial(n-i,p-i)/binomial(q-i,p-i);
  if not(type(m,integer)) then
   return false;
  fi;
 od:
 return true;
end:

`is_element/steiner_systems` := (A::set) -> (p::posint,q::posint) -> proc(S)
 global reason;
 
 local P,B,CC;
 
 if not(type(S,set(set))) then
  reason := ["is_element/steiner_systems","S is not a set of sets",S];
  return false;
 fi;

 if map(op,S) minus A <> {} then
  reason := ["is_element/steiner_systems","S is not a set of subsets of A",S,A];
  return false;
 fi;

 if map(nops,S) <> {q} then
  reason := ["is_element/steiner_systems","S is not a set of sets of size q",S,q];
  return false;
 fi;
 
 P := combinat[choose](A,p);

 for B in P do
  CC := select(C -> B minus C = {},S);
  if nops(CC) <> 1 then
   reason := ["is_element/steiner_systems","The set B is not contained in a unique block",B,CC];
   return false; 
  fi;
 od:

 return true;
end:

`res/steiner_system` := (A::set,B::set) -> proc(S)
 local T;
 
 if B minus A <> {} then
  error("B is not a subset of A");
 fi;

 if nops(S[1]) + nops(B) < nops(A) then
  error("B is too small");
 fi;
 
 T := select(C -> C union B = A,S);
 T := map(C -> C intersect B,T);

 return T;
end:

# A (1,q)-Steiner system on A is just a partition of A into disjoint blocks of
# size q.  There is an obvious way to make such a partition when A = {1,..,m*q}

`steiner_system/congruence` := proc(q,m)
 local i,j;
 [{seq(i,i=1..q*m)},
  {seq({seq(j,j=i*q+1..(i+1)*q)},i=0..m-1)},
  [1,q,m*q]];
end:

# For any prime p, the lines in (Z/p)^2 give a (2,p)-Steiner system.

`steiner_system/affine` := proc(p)
 local V,S,i,j,m,c;
 
 if not(isprime(p)) then
  return FAIL;
 fi;

 V := {seq(seq([i,j],j=0..p-1),i=0..p-1)};
 S := {seq({seq([i,j],j=0..p-1)},i=0..p-1),
       seq(seq({seq([i,modp(m*i+c,p)],i=0..p-1)},c=0..p-1),m=0..p-1)};
 return [V,S,[2,p,p^2]];
end:

