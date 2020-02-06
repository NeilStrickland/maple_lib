# D/Fbar(A,B) is
# D(A,NWB) = {(u,v) in Map(A,[0,infinity)) x NWB : |u|^2 + |v|^2 = 1}

`is_element/D/Fbar` := (N::posint) -> (A::set,B::set) -> proc(uv)
 global reason;
 local u,v,nu,nv;

 if not(type(uv,list) and nops(uv) = 2) then
  reason := [convert(procname,string),"uv is not a list of length 2",uv];
  return false;
 fi;
 
 u,v := op(uv);

 if not (`is_element/real_functions`(A)(u) and 
         `is_nonnegative/real_functions`(A)(u)) then
  reason := [convert(procname,string),"u is not a nonnegative real function on A",u,A];
  return false;
 fi;

 nu := `norm/real_functions`(A)(u)^2;

 if not `is_element/prime_W`(N)(B)(v) then
  reason := [convert(procname,string),"v is not in NWB",v,B];
  return false;
 fi;

 nv := `norm/prime_W`(N)(B)(v)^2;

 if nu + nv <> 1 then
  reason := [convert(procname,string),"(u,v) is not in normalised",u,v];
  return false;
 fi;

 return true;
end:

######################################################################

`is_equal/D/Fbar` := (N::posint) -> (A::set,B::set) -> proc(uv1,uv2)
 local u1,v1,u2,v2;
 u1,v1 := op(uv1);
 u2,v2 := op(uv2);

 return `is_equal/real_functions`(A)(u1,u2) and
        `is_equal/vector_functions`(N)(B)(v1,v2);
end:

######################################################################

`random_element/D/Fbar` := (N::posint) -> (A::set,B::set) -> proc()
 local n,r,u,v,a,b;

 n := nops(A);
 r := 0;

 while r = 0 do 
  u := `random_element/real_functions`(A)();
  v := `random_element/prime_W`(N)(B)();
  r := `norm/real_functions`(A)(u)^2 + 
       `norm/vector_functions`(N)(B)(v)^2;
 od;

 r := sqrt(r);
 for a in A do u[a] := simplify(abs(u[a] / r)); od:
 for b in B do v[b] := simplify(v[b] /~ r); od: 

 return [eval(u),eval(v)];
end:

######################################################################

`is_leq/D/Fbar` := NULL:
`list_elements/D/Fbar` := NULL:
`count_elements/D/Fbar` := NULL:

