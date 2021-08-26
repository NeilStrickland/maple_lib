# P(N) is the set of real polynomials in epsilon of degree less than N

######################################################################

`is_element/P` := (N::posint) -> proc(u)
 global reason;

 if not type(u,polynom(realcons,epsilon)) then 
  reason := [convert(procname,string),"u is not polynomial in epsilon",u];
  return false;
 fi;

 if degree(u,epsilon) >= N then
  reason := [convert(procname,string),"deg(u) >= N",u,N];
  return false;
 fi;

 return true;
end;

`is_leq/P` := (N::posint) -> proc(u,v)
 local w,d,c;

 w := expand(v-u);
 if (w = 0) then return true; fi;
 d := ldegree(w,epsilon);
 c := coeff(w,epsilon,d);
 return evalb(c >= 0);
end:

`random_element/P` := (N::posint) -> proc(d::posint := 4)
 local r,i;
 r := rand(-d^2..d^2);
 add(r()/d * epsilon^i,i=0..N-1);
end;

`list_elements/P` := NULL;
`count_elements/P` := NULL;

