sgn := (s) -> signum(mul(mul(s[j] - s[i],j=i+1..nops(s)),i=1..nops(s))):

######################################################################

is_table_on := (A::set) -> proc(x)
 if not(type(x,table)) then return false; fi;
 if {indices(x)} <> map(a -> [a],A) then
  return false;
 fi;

 return true;
end:

######################################################################

# Return a randomly selected element of a finite set A

random_element_of := proc(A)
 local n,i;

 if not type(A,list) and not type(A,set) then
  error("A is not a list or set");
 fi;

 n := nops(A);
 
 if n = 0 then
  error("A is empty");
 fi;
 
 i := rand(1..n)();
 return A[i];
end:

######################################################################

# Return a randomly selected element of a finite set A

random_subset_of := proc(A,size_::nonnegint)
 local n,i,U,V,r,x;

 if not type(A,list) and not type(A,set) then
  error("A is not a list or set");
 fi;

 n := nops(A);

 if nargs = 1 then
  r := rand(2);
  V := select(a -> (r() = 1),{op(A)});
  return V;
 else
  if size_ > n then
   return FAIL;
  fi;
  U := {op(A)};
  V := {};
  for i from 0 to size_-1 do
   x := U[rand(1..(n-i))()];
   U := U minus {x};
   V := V union {x};
  od:
  return V;
 fi;
end:

######################################################################

# This function converts small numbers to single-character strings,
# which is convenient in some circumstances when we need to display
# a large number of small numbers.
#
#  0 ..  9 become "0" to "9"
# 10 .. 35 become "A" to "Z"
# 36 .. 61 become "a" to "z"

nat_code := table([
 seq(i = convert([48+i],bytes),i=0..9),
 seq(i = convert([65+i-10],bytes),i=10..35),
 seq(i = convert([97+i-36],bytes),i=36..61)
]);

######################################################################

# Return a list of pairs [p[i],v[i]] such that the p[i] are distinct
# primes in increasing order, the v[i] are nonzero integers, and 
# n is the product of the p[i]^v[i].  The real work is done by Maple's
# ifactor() function, we just convert the result to a more convenient
# form.

ifactor_list := proc(n::rational)
 local u;
 if n = 0 then 
  error("Cannot factor zero");
 fi;
 u := ifactor(abs(n));
 if type(u,`*`) then
  u := [op(u)];
 else
  u := [u];
 fi;
 u := map(x -> `if`(type(x,`^`),[op(op(1,x)),op(2,x)],[op(x),1]),u);
 return u;
end:

######################################################################

# Return true iff n = p^k for some prime p and integer k >= 0.

is_prime_power := proc(n::posint)
 not(type(ifactor(n),`*`));
end:

######################################################################

# Return the p-adic valuation of m.

padic_val := proc(m::rational,p)
 local k,l;
 if m = 0 then return infinity; fi;
 if denom(m) <> 1 then
  return padic_val(numer(m),p) - padic_val(denom(m),p);
 fi;
 k := 0;
 l := m;
 while irem(l,p,'l') = 0 do k := k+1; od:
 return k;
end:

######################################################################

# Return the list of the base p digits of n, least significant first.

digit_list := proc(n::nonnegint,p::posint)
 local L,m;
 L := NULL;
 m := n;
 while m > 0 do
  L := L,irem(m,p);
  m := iquo(m,p);
 od:
 return [L];
end:

# Return the sum of the base p digits of n.

digit_sum := (n::nonnegint,p::posint) -> `+`(0,op(digit_list(n,p)));

######################################################################

# If u is an algebraic expression with an overall minus sign, then 
# remove the mius sign.

strip_sign := proc(u)
 if type(u,list) or type(u,set) then
  return map(strip_sign,u);
 elif type(u,`*`) then
  return map(x -> `if`(type(x,numeric),abs(x),x),u);
 else
  return u;
 fi;
end:

######################################################################

# Given a Grobner basis such that the corresponding quotient ring is
# finite-dimensional, return the usual basis for that quotient.

cobasis := proc(basis,vars)
 local lm_basis,B,B0,V,b,i,v;

 lm_basis := map(u -> LeadingMonomial(u,vars), basis);
 B := [1];
 V := [op(vars)];
 for v in V do 
  B0 := B;
  B := NULL;
  for b in B0 do
   i := 0;
   while NormalForm(b*v^i,lm_basis,vars) <> 0 do
    B := B,b*v^i;
    i := i+1;
   od:
  od:
  B := [B];
 od:
 return B;
end:

######################################################################

# Returns the set of monomials occuring in u

monomials := proc(u)
 if type(u,`+`) or type(u,list) or type(u,set) then
  return map(op,map(monomials,{op(u)}));
 elif type(u,`*`) then
  return {remove(type,u,constant)};
 elif type(u,constant) then
  return {1};
 else 
  return {u};
 fi;
end:

######################################################################

# Returns the coefficient in u of the monomial m.
# If u involves variables that do not occur in m, then these will
# be included in the coefficient.

multi_coeff := proc(u,m)
 local c,x;
 c := u;
 for x in indets(m) do
  c := coeff(c,x,degree(m,x));
 od;
 return c;
end:

coeff_list := (u,mm) -> map2(multi_coeff,u,mm);

######################################################################

# This function returns a pair [d,q], where d is the gcd of the integers
# in u, and q is a list of integers such that the sum of the terms
# q[i] * u[i] is equal to d.  Moreover, q is the unique such list with
# 0 <= q[i] < d[i]/d[i-1] for i = 2,...,n, where d[i] is the gcd of
# u[1],...,u[i].  Note that there is no bound on q[1], which will
# typically be large and negative.

igcd_alt := proc(u::list(posint))
 local n,d,e,v,s,t,p,q,m,i;
 n := nops(u);
 d := table():
 e := table():
 v := table():
 d[1] := u[1];
 for i from 2 to nops(u) do
  d[i] := igcdex(d[i-1],u[i],s[i],t[i]);
  e[i-1] := d[i-1]/d[i];
  v[i] := u[i]/d[i];
 od:
 e[n] := d[n];

 p[n] := s[n];
 q[n] := t[n];
 m := iquo(q[n],e[n-1]);
 q[n] := q[n] - m*e[n-1];
 p[n] := p[n] + m*v[n];

 for i from n-1 to 2 by -1 do
  p[i] := s[i]*p[i+1];
  q[i] := t[i]*p[i+1];
  m := floor(q[i]/e[i-1]);
  q[i] := q[i] - m*e[i-1];
  p[i] := p[i] + m*v[i];
 od;

 q[1] := p[2];
 return [d[n],[seq(q[i],i=1..n)]];
end:

######################################################################

# Permutation matrix
# (duplicated in groups/general_linear.mpl)

perm_matrix := proc(s)
 local n,M,i;
 n := nops(s);
 M := Matrix(n,n);
 for i from 1 to n do 
  M[s[i],i] := 1;
 od:
 return M;
end:

######################################################################

# Return u, but with all tiny numerical constants converted to 0.

trim := proc(u,epsilon := 10.^(-90))
 local c,v;
 if type(u,`+`) or type(u,list) or type(u,set) or type(u,Matrix) or type(u,Vector) then
  return map(trim,u,epsilon);
 elif type (u,`*`) then
  c,v := selectremove(type,u,complex(numeric));
  if abs(Re(c)) < epsilon then c := Im(c) * I; fi;
  if abs(Im(c)) < epsilon then c := Re(c); fi;
  return c * v;
 elif type(u,complex(numeric)) then
  c := u;
  if abs(Re(c)) < epsilon then c := Im(c) * I; fi;
  if abs(Im(c)) < epsilon then c := Re(c); fi;
  return c;
 else
  return u;
 fi;
end:

######################################################################

symmetric_difference := (A,B) ->
 {op(A),op(B)} minus ({op(A)} intersect {op(B)});


is_all_zero := proc(x)
 if type(x,{list,set}) then 
  return `and`(op(map(is_all_zero,x)));
 elif type(x,Vector) then 
  return is_all_zero(convert(x,list));
 elif type(x,Matrix) then 
  return is_all_zero(convert(x,listlist));
 else 
  return evalb(x = 0);
 fi;
end:

######################################################################

is_all_zero := proc(x)
 if type(x,{list,set}) then 
  return `and`(op(map(is_all_zero,x)));
 elif type(x,Vector) then 
  return is_all_zero(convert(x,list));
 elif type(x,Matrix) then 
  return is_all_zero(convert(x,listlist));
 else 
  return evalb(x = 0);
 fi;
end:

######################################################################

make_index := proc(L::{list,Vector})
 local L0,T,i;
 
 L0 := L;
 if type(L0,Vector) then L0 := convert(L0,list); fi;

 T := table();
 for i from 1 to nops(L0) do
  T[L0[i]] := i;
 od;

 return eval(T);
end:
