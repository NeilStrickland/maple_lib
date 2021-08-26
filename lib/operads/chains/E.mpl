# E(N) is the set of polynomials of the form 0 or +/- epsilon^d
# with 0 <= d < N.

######################################################################

`is_element/E` := (N::posint) -> proc(u)
 local d;
 global reason;

 if not(`is_element/P`(N)(u)) then
  reason := [convert(procname,string)];
  return false;
 fi;

 if (u = 0) then return true; fi;

 d := degree(u,epsilon);
 if u <> epsilon^d and u <> -epsilon^d then
  reason := [convert(procname,string),"u <> +/- epsilon^d",u,d];
  return false;
 fi;

 return true;
end;

######################################################################
# `is_leq/E`(N)(u,v) is true if v-u is zero or is c epsilon^d + higher
# with c > 0.

`is_leq/E` :=  (N::posint) -> proc(u,v)
 local w,d,c;

 w := expand(v-u);
 if (w = 0) then return true; fi;
 d := ldegree(w,epsilon);
 c := coeff(w,epsilon,d);
 return evalb(c >= 0);
end:

######################################################################

`is_preceq/E` := (N::posint) -> proc(u,v)
 if (u = v) then return true; fi;
 if (u = 0) then return true; fi;
 if (v = 0) then return false; fi;
 return evalb(ldegree(u,epsilon) > ldegree(v,epsilon));
end:

######################################################################

`list_elements/E` := proc(N::posint)
 local i;
 return [seq(-epsilon^i,i=0..N-1),0,seq(epsilon^(N-1-i),i=0..N-1)];
end:

`random_element/E` := (N::posint) -> proc()
 local L;
 L := `list_elements/E`(N);
 L[rand(1..nops(L))()];
end:

######################################################################

`count_elements/E` := (N::posint) -> 2*N+1;

`abs/E` := (N::posint) -> proc(u) 
 if (u = 0) then return 0; fi;
 return epsilon^degree(u,epsilon);
end:

######################################################################

`lambda/P/E` := (N::posint) -> proc(u)
 local c,d;

 if u = 0 then
  return 0;
 else
  d := ldegree(u,epsilon);
  c := coeff(u,epsilon,d);
  return signum(c) * epsilon^d;
 fi;
end:

######################################################################

`delta/P` := (N::posint) -> (u,v) -> `lambda/P/E`(N)(v-u);
