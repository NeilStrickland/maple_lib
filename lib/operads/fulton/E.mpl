`is_element/E/Fbar` := (N::posint) -> (A::set,B::set) -> proc(tpqx)
 global reason;
 local t,p,q,x,nt,nx;

 if not(type(tpqx,list) and nops(tpqx) = 4) then
  reason := [convert(procname,string),"tpqx is not a list of length 4",tpqx];
  return false;
 fi;
 
 t,p,q,x := op(tpqx);

 if not (`is_element/real_functions`(A)(t) and
         `is_nonnegative/real_functions`(A)(t)) then
  reason := [convert(procname,string),"t is not a nonnegative real function on A",t,A];
  return false;
 fi;

 nt := `norm/real_functions`(A)(t)^2;

 if simplify(nt - 1) <> 0 then 
  reason := [convert(procname,string),"t is not in normalised",t];
  return false;
 fi;

 if not(`is_element/RR`(p) and 
        `is_element/RR`(q) and 
        p >= 0 and q >= 0 and simplify(p^2+q^2 - 1) = 0) then
  reason := [convert(procname,string),"(p,q) is not in normalised",p,q];
  return false;
 fi;

 if not `is_element/prime_W`(N)(B)(x) then
  reason := [convert(procname,string),"x is not in NWB",x,B,reason];
  return false;
 fi;

 nx := `norm/prime_W`(N)(B)(x)^2;

 if simplify(nx - 1) <> 0 then
  reason := [convert(procname,string),"x is not in normalised",x];
  return false;
 fi;

 return true;
end:

######################################################################

`random_element/E/Fbar` := (N::posint) -> (A::set,B::set) -> proc()
 local t,p,q,x,n,t0,r;

 n := nops(A);
 t0 := map(abs,`random_element/sphere`(n-1)());
 t := table([seq(A[i]=t0[i],i=1..n)]):
 p,q := op(map(abs,`random_element/sphere`(1)()));
 r := 0;
 while r = 0 do 
  x := `random_element/prime_W`(N)(B)();
  r := `norm/prime_W`(N)(B)(x);
 od;
 x := table([seq(b = simplify(x[b] /~ r),b in B)]);
 return [eval(t),p,q,eval(x)];
end:

######################################################################

`is_equal/E/Fbar` := (N::posint) -> (A::set,B::set) -> proc(tpqx1,tpqx2)
 local t1,p1,q1,x1,t2,p2,q2,x2;

 t1,p1,q1,x1 := op(tpqx1);
 t2,p2,q2,x2 := op(tpqx2);

 return `is_equal/real_functions`(A)(t1,t2) and
        `is_equal/RR`(p1,p2) and 
        `is_equal/RR`(q1,q2) and 
        `is_equal/prime_W`(N)(B)(x1,x2);
end:

######################################################################

`theta/E/D/Fbar` := (N::posint) -> (A::set,B::set) -> proc(tpqx)
 local t,p,q,x,u,v,a,b;

 t,p,q,x := op(tpqx);
 u := table();
 v := table();
 for a in A do u[a] := p * t[a]; od;
 for b in B do
  v[b] := q *~ x[b];
 od;

 return [u,v];
end;

######################################################################

`is_leq/E/Fbar` := NULL:
`list_elements/E/Fbar` := NULL:
`count_elements/E/Fbar` := NULL:
