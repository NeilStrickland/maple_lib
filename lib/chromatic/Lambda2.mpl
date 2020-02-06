`bideg0/Lambda` := proc(u)
 if type(u,specfunc(nonnegint,lambda)) then
  return [nops(u),`+`(op(u)) + nops(u)];
 else
  return [0,0];
 fi;
end:

`bideg/Lambda` := apply_deg(`bideg0/Lambda`);

`mu0/Lambda` := (u,v) -> `reduce/Lambda`(op(u),op(v));

`mu/Lambda` := apply_linear_assoc_mod(`mu0/Lambda`,lambda(),2);

`is_admissible/Lambda` := proc()
 if nargs = 1 and type(args[1],specfunc(nonnegint,lambda)) then
  return `is_admissible/Lambda`(op(args[1]));
 elif type([args],list(nonnegint)) then
  return evalb(min(op((2 *~ [infinity,args]) -~ [args,0])) >= 0);
 else
  return FAIL;
 fi;
end:

`reduce/Lambda` := proc()
 local K,t,left,right,i,j,n,u,c;
 
 option remember;

 if `is_admissible/Lambda`(args) then
  return lambda(args);
 fi;

 K := [args];
 t := 1;
 while t < nargs and K[t+1] <= 2*K[t] do t := t+1; od;
 left := lambda(seq(K[i],i=1..t-1));
 right := `reduce/Lambda`(seq(K[i],i=t+2..nops(K)));
 i := K[t];
 n := K[t+1] - 2*i - 1;
 u := 0;
 for j from 0 to floor((n-1)/2) do
  c := modp(binomial(n-1-j,j),2);
  if c <> 0 then
   u := modp(u + c * `mu/Lambda`(left,`reduce/Lambda`(i+n-j,2*i+1+j),right),2);
  fi;
 od;
 return u;
end:

`d0/Lambda` := proc(n::nonnegint)
 local u,j,c;
 option remember;

 u := 0;
 for j from 1 to floor(n/2) do
  c := modp(binomial(n-j,j),2);
  if c <> 0 then
   u := u + `reduce/Lambda`(n-j,j-1);
  fi;
 od;
 u := modp(u,2);
 return u;
end:

`d1/Lambda` := proc(u)
 local K,n,v,i,x,y,z;
 option remember;
 
 if not(type(u,specfunc(nonnegint,lambda))) then
  return FAIL;
 fi;
 
 K := [op(u)];
 n := nops(K);
 v := 0;
 for i from 1 to n do
  x := lambda(seq(K[j],j=1..i-1));
  y := `d0/Lambda`(K[i]);
  z := lambda(seq(K[j],j=i+1..n));
  v := modp(v + `mu/Lambda`(x,y,z),2);
 od;
 return v;
end:

`d/Lambda` := apply_linear_mod(`d1/Lambda`,2);

`basis/Lambda` := proc(s::integer,t::integer)
 local B,C,r;
 option remember;
 
 if s < 0 then
  return [];
 elif s = 0 then
  if t = 0 then
   return [lambda()];
  else
   return [];
  fi;
 elif s = 1 then
  if t >= 1 then
   return [lambda(t-1)];
  else
   return [];
  fi;
 else
  B := NULL;
  for r from 0 to t-1 do
   C := `basis/Lambda`(s-1,r);
   C := select(v -> (op(-1,v) >= t-r-1),C);
   C := map(v -> lambda(op(v),t-r-1),C);
   B := B,op(C);
  od;
  return [B];
 fi; 
end:

`vec/Lambda` := (s,t) -> proc(u)
 [seq(modp(coeff(u,m,1),2),m in `basis/Lambda`(s,t))]; 
end:

`d_matrix/Lambda` := proc(s,t)
 local M;
 option remember;

 M := map(m -> `vec/Lambda`(s+1,t)(`d/Lambda`(m)),`basis/Lambda`(s,t));
 M := LinearAlgebra[Modular][Mod](2,Transpose(Matrix(M)),integer[]);
 return M;
end: