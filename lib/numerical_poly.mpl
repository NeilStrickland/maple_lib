is_numerical_poly := proc(g,u)
 local m,h;

 if not(type(g,polynom(rational,u))) then
  return false;
 fi;
 
 m := degree(g,u);
 h := g;
 while m >= 0 do
  if not(type(subs(u=0,h),integer)) then
   return(false);
  fi;
  h := expand(subs(u=u+1,h)-h);
  m := m-1;
 od:
 return(true);
end:

`b/numerical_poly` := (k::nonnegint,u) -> expand(binomial(u,k));

`alpha/numerical_poly` := proc(i::nonnegint,j::nonnegint,k::nonnegint)
 if i <= k and j <= k and k <= i+j then
  return k!/((k-i)!*(k-j)!*(i+j-k)!);
 else
  return 0;
 fi;
end:

`beta/numerical_poly` := proc(i::nonnegint,j::nonnegint,k::nonnegint)
 local m,n;
 
 add(add(
  (-1)^(m+n)*binomial(i,m)*binomial(j,n)*binomial((i-m)*(j-n),k),
   n=0..j),m=0..i);
   
end:

`Delta/numerical_poly` := proc(f,u)
 subs(u = u+1,f) - f;
end:

`gamma/numerical_poly` := proc(p,n)
 local N;
 N := floor(n/(p-1));
 N + padic_val(N!,p);
end:

`Gamma/numerical_poly` := proc(n::posint)
 local g,i,p;
 g := 1;
 i := 1;
 p := ithprime(i);
 while p <= 2*n do
  g := g * p^`gamma/numerical_poly`(p,n);
  i := i+1;
  p := ithprime(i);
 od;
 return(g);
end:

`Gamma_alt/numerical_poly` := proc(n::posint)
 if modp(n,2) <> 0 then return FAIL; fi;

 return mul(2*denom(bernoulli(2*k)/(2*k)),k=1..n/2);
end:


# There is a canonical basis for the ring of stably numerical
# polynomials, as discussed in the document ImJ.tex.
# The first few basis elements are as follows:

`f/stably_numerical_poly` := table([
  0 = ((u) -> 1),
  1 = ((u) -> (u+1)/2),
  2 = ((u) -> (u^2-1)/24),
  3 = ((u) -> (u^3+u^2-u-1)/48),
  4 = ((u) -> (u^4+70*u^2-71)/5760),
  5 = ((u) -> (u^5+u^4+70*u^3+70*u^2-71*u-71)/11520)
]);

`f_witness/stably_numerical_poly` := table([
 "max_deg" = 5,
 "u_shift" = table([0 = 0,1 = 1,2 = 3,3 = 4,4 = 7,5 = 8]),
 "eval_points"  = [1,-1,7,11,13,17,23,37],
 "split_matrix" =
 [[0, 1, 0, 0, 0, 0, 0, 0],
  [1, -1, 0, 0, 0, 0, 0, 0],
  [-2497, 1127, 5994, -13853, 10734, -1511, 2, 4],
  [-628, 283, 1513, -3505, 2720, -385, 1, 1],
  [-4976, 2245, 11943, -27574, 21348, -2996, 2, 8],
  [-4334, 1955, 10406, -24026, 18599, -2608, 1, 7]]
]):

`find_split_matrix/stably_numerical_poly` := proc()
 local f,W,d,A,m,B,eqs,sol;
 
 f := `f/stably_numerical_poly`;
 W := `f_witness/stably_numerical_poly`;
 d := W["max_deg"];

 A := Transpose(Matrix(
  [seq(map(f[i],W["eval_points"]),i=0..d)]));

 m := nops(W["eval_points"]);
 
 B := Matrix([seq([seq(b[i,j],j=1..m)],i=0..d)]):

 eqs := {op(map(r -> r = 0,map(op,convert(B.A - IdentityMatrix(d+1),listlist))))}:
 sol := isolve(eqs);

 if sol = NULL then return FAIL; fi;

 B := subs(sol,B);
 B := subs(map(u -> u=0,indets(B)),B);

 return B;
end:

######################################################################

`check_witness/stably_numerical_poly` := proc()
 global Z;
 local f,W,d,s,i,j,M,A,B,p;
 
 f := `f/stably_numerical_poly`;
 W := `f_witness/stably_numerical_poly`;
 d := W["max_deg"];

 _ASSERT(type(d,posint),"max_deg is a positive integer");

 for i from 0 to d do
  s := W["u_shift"][i];
  _ASSERT(is_numerical_poly(u^s*f[i](u),u),
          sprintf("f_%d(u) is stably numerical",i));
 od:

 for i from 0 to d do
  M[i] := 1/coeff(f[i](u),u,i);
  _ASSERT(type(M[i],posint),sprintf("Leading coefficient of f_%d(u) is egyptian",i));
  _ASSERT(
   `and`(seq(-1/(2*M[i]) < coeff(f[j](u),u,i) and
             coeff(f[j](u),u,i) <= 1/(2*M[i]),j=i+1..d)),
   sprintf("Coefficient bounds for f_%d(u)",i));
 od:
 
 _ASSERT(type(W["eval_points"],list(integer)),"eval_points is a list of integers");

 for p in W["eval_points"] do
  _ASSERT(p = 1 or p = -1 or (p > d and isprime(p)),
          sprintf("evaluation point %d is +/- 1 or prime and greater than max_deg",p));
 od:

 A := Transpose(Matrix(
  [seq(map(f[i],W["eval_points"]),i=0..d)]));

 B := Matrix(W["split_matrix"]);
 Z := [A,B];

 _ASSERT(Equal(B.A,IdentityMatrix(d+1)),"split_matrix splits");

end:

######################################################################

check_numerical_poly := proc()
 local u,v,i,j,k,ok,err;
 
 _ASSERT(
  `b/numerical_poly`(0,u) = 1,
  "b_0(u) = 1"
 );
 
 _ASSERT(
  `b/numerical_poly`(1,u) = u,
  "b_1(u) = u"
 );

 ok := true;
 for k from 0 to 10 do
  err :=
   `b/numerical_poly`(k,u+v) -
    add(`b/numerical_poly`(i,u) * `b/numerical_poly`(k-i,v),i=0..k);

  err := expand(err);
  if err <> 0 then ok := false; break; fi;
 od:
 _ASSERT(ok,"Formula for b_k(u+v)");

 ok := true;
 for k from 0 to 10 do
  err :=
   `b/numerical_poly`(k,u*v) -
    add(add(
     `beta/numerical_poly`(i,j,k) *
      `b/numerical_poly`(i,u) *
       `b/numerical_poly`(j,v),
    j=0..k),i=0..k);

  err := expand(err);
  if err <> 0 then ok := false; break; fi;
 od:
 _ASSERT(ok,"Formula for b_k(uv)");

 ok := true;
 for i from 0 to 10 do
  for j from 0 to 10 do
   err := `b/numerical_poly`(i,u) * `b/numerical_poly`(j,u) -
    add(
     `alpha/numerical_poly`(i,j,k) * `b/numerical_poly`(k,u),
      k = 0 .. i+j);
   err := expand(err);

   if err <> 0 then ok := false; break; fi;
  od:

  if not(ok) then break; fi;
 od:
 _ASSERT(ok,"Formula for b_i(u) b_j(u)");

 _ASSERT(`Delta/numerical_poly`(`b/numerical_poly`(0,u),u) = 0,"Delta(b_0) = 0");

 _ASSERT(
  `and`(seq(
   expand(`Delta/numerical_poly`(`b/numerical_poly`(i+1,u),u) - `b/numerical_poly`(i,u))=0,
    i=0..10)),
   "Delta(b_{i+1}(u)) = b_i(u)"
 );
 
 _ASSERT(
  `and`(seq(`Gamma_alt/numerical_poly`(2*n) =
            `Gamma/numerical_poly`(2*n),n=1..10)),
  "Gamma in terms of Bernoulli numbers"
 );
end: