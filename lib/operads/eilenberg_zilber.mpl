# The full Eilenberg-Zilber operad EZ has EZ(A) equal to the set of
# natural maps N_*(X) \to N_*(X)^{\otimes A} for simplicial sets X.
# By consideration of universal examples, we see that any such map
# sends N_{\leq n}(X) into (N_{\leq n}(X))^{\otimes A} for all n.
# Thus, if we define EZ_{\leq n}(A) to be the set of natural maps
# N_{\leq n}(X) \to (N_{\leq n}(X))^{\otimes A}, we get a quotient
# operad of EZ.  The group EZ(A) is an infinite product of copies of
# the integers and so is not computationally tractable.  We
# therefore work with EZ_{\leq n} instead.

`is_element/eilenberg_zilber` := (n :: nonnegint) -> (A::set) -> proc(x)
 local y,z,i;
 
 if x = 0 then return true; fi;
 
 if type(x,`+`) then
  return `and`(op(map(`is_element/eilenberg_zilber`(n)(A),[op(x)])));
 fi;

 if type(x,`*`) then
  y,z := selectremove(type,[op(x)],integer);
  return (nops(z) = 1 and `is_element/eilenberg_zilber`(n)(A)(z[1]));
 fi;
 
 if not type(x,specfunc(Z)) then return false; fi;

 if nops(x) = 0 or nops(x) > n+1 then return false; fi;

 for i from 1 to nops(x) do
  if not(`is_element/subsets`(A)(op(i,x))) then
   return false;
  fi;
 od;

 if map(op,{op(x)}) <> A then
  return false;
 fi;
 
 for i from 1 to nops(x) - 1 do
  if op(i,x) intersect op(i+1,x) = {} then return false; fi;
 od;

 return true;
end:

`is_equal/eilenberg_zilber` := (n::nonnegint) -> (A::set) -> (x,y) -> evalb(x = y):

`random_basis_element/eilenberg_zilber` := (n::nonnegint) -> (A) -> proc(m_)
 local m,t,M,a,i;

 if A = {} then
  if nargs = 0 or m_ = 0 then
   return Z({});
  else
   error("A is empty");
  fi;
 fi;
 
 m := `if`(nargs > 0,min(n,m_),rand(0..n)());
 
 t := table():
 M := {seq(i,i=0..m)};
 
 for a in A do t[a] := random_nonempty_subset_of(M); od;

 for i from 0 to m-1 do
  a := random_element_of(A);
  t[a] := t[a] union {i,i+1};
 od:

 return Z(seq(select(a->member(i,t[a]),A),i=0..m));
end:

`random_element/eilenberg_zilber` := (n::nonnegint) -> (A) -> proc(coeff_range_,num_terms_)
 local coeff_range,num_terms;

 coeff_range := -3..3;
 num_terms := 5;
 if nargs > 0 then coeff_range := args[1]; fi;
 if nargs > 1 then num_terms := args[2]; fi;
 
 add(rand(coeff_range)() * `random_basis_element/eilenberg_zilber`(n)(A)(),i=1..num_terms);
end:

`transpose0/eilenberg_zilber` := (A::set) -> proc(x)
 local m,M,t,a;
 
 m := nops(x) - 1;
 M := [seq(i,i=0..m)];
 t := table():
 for a in A do
  t[a] := select(i -> member(a,op(i+1,x)),M);
 od;

 return Zt(eval(t));
end;

`transpose/eilenberg_zilber` := (A::set) ->
 apply_linear(`transpose0/eilenberg_zilber`(A));

`detranspose0/eilenberg_zilber` := (A::set) -> proc(x)
 local t,m;

 t := op(1,x);
 m := max(op(map(op,{{0},seq(t[a],a in A)})));
 return Z(seq(select(a -> member(i,t[a]),A),i=0..m));
end:

`detranspose/eilenberg_zilber` := (A::set) ->
 apply_linear(`detranspose0/eilenberg_zilber`(A));

`eta/eilenberg_zilber` := (n::nonnegint) -> (A::set) ->
 `if`(nops(A)=1,add(Z(A $ k),k=1..(n+1)),FAIL);

`source_degree/eilenberg_zilber` := (A::set) -> proc(x)
 return nops(x) - 1;
end:

`target_degrees/eilenberg_zilber` := (A::set) -> proc(x)
 local xt,d,a;

 xt := op(1,`transpose/eilenberg_zilber`(A)(x));
 d := table();
 for a in A do
  d[a] := nops(xt[a]) - 1;
 od:

 return eval(d);
end:

`gamma0/eilenberg_zilber` := (A::set,B::set) -> (p) -> proc(y,x)
 local F,s,d,t,u,a,b;
 
 F := fibres(A,B)(p);
 s := op(1,`transpose/eilenberg_zilber`(B)(y));
 d := `target_degrees/eilenberg_zilber`(B)(y);
 
 t := table():
 for b in B do
  if `source_degree/eilenberg_zilber`(F[b])(x[b]) <> d[b] then
   return 0;
  fi;

  t[b] := op(1,`transpose/eilenberg_zilber`(F[b])(x[b]));
 od;

 u := table();
 for a in A do
  b := p[a];
  u[a] := [seq(s[b][j+1], j in t[b][a])];
 od;

 return `detranspose/eilenberg_zilber`(A)(Zt(u));
end:

`gamma/eilenberg_zilber` := (n::nonnegint) -> (A::set,B::set) -> (p) -> proc(y,x)
 local c,y1,F,d0,BL,M,t,z,b,m,mt;
 
 if y = 0 then
  return 0;
 elif type(y,`+`) then
  return map(t -> `gamma/eilenberg_zilber`(n)(A,B)(p)(t,x),y);
 fi;

 if type(y,`*`) then
  c,y1 := selectremove(type,y,integer);
 else
  c := 1;
  y1 := y;
 fi;

 if not(type(y1,specfunc(Z))) then
  return FAIL;
 fi;

 F := fibres(A,B)(p);

 d0 := `target_degrees/eilenberg_zilber`(B)(y1);
 
 BL := sort([op(B)]);
 M := [[1]];
 for b in BL do
  t := map(coeff_split,sum_terms(x[b]));
  t := select(u -> `source_degree/eilenberg_zilber`(F[b])(u[2]) = d0[b],t);
  M := [seq(seq([m[1] * u[1],seq(m[i],i=2..nops(m)),u[2]],u in t),m in M)];
 od:

 z := 0;

 for m in M do
  mt := table([seq(BL[i]=m[i+1],i=1..nops(BL))]);
  z := z + c * m[1] * `gamma0/eilenberg_zilber`(A,B)(p)(y1,mt);
 od;

 return z;
end: