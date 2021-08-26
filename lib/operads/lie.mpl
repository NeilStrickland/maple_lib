# Suppose that u is in Lie(A), and that a is in A.  Then there is a unique
# way to express u as a linear combination of fully right associated words
# with a as the last term.  The function below calculates this.

`comb/lie_operad` := (a) -> proc(u)
 local x,y,z,n,ub,uc,t;
 if u = 0 then
  return 0;
 elif type(u,`+`) or type(u,list) or type(u,set) then
  return map(`comb/lie_operad`(a),u);
 elif type(u,`*`) then
  ub,uc := selectremove(type,[op(u)],specfunc(bracket));
  if nops(ub) <> 1 then
   return FAIL;
  fi;
  ub := ub[1];
  uc := `*`(op(uc));
  return(uc * `comb/lie_operad`(a)(ub));
 elif type(u,specfunc(bracket)) then
  n := nops(u);
  if n = 0 then
   return FAIL;
  fi;
  if n = 1 then
   if op(u) = a then
    return u;
   else
    return FAIL;
   fi;
  else
   x := op(1,u);
   y := op(2,u);
   z := op(3..n,u);
   if x = a then
    if n = 2 then
     return -bracket(y,x);
    else
     return `comb/lie_operad`(a)(bracket(y,bracket(a,z))) -
      eval(subs(t = bracket(y,a),`comb/lie_operad`(t)(bracket(t,z))));
    fi;
   elif has(x,a) then
    return eval(subs(t = `comb/lie_operad`(a)(x),
                     `comb/lie_operad`(t)(bracket(t,y,z))));
   else
    return bracket(x,`comb/lie_operad`(a)(bracket(y,z)));
   fi;
  fi;
 fi;
end:

# This returns the basis consisting of fully right associated words
# ending with a.

`basis/lie_operad` := proc(A::set,a_)
 local a,B;
 
 a := `if`(nargs > 1,a_,A[nops(A)]);
 if not member(a,A) then
  error "a not in A";
 fi;

 B := A minus {a};
 return map(u -> bracket(op(u),a),`list_elements/ord`(B));
end:

`vec0/lie_operad` := (A::set,a) -> proc(u)
 local n,m,ub,uc,T,B,i;
 global `vec_table/lie_operad`;

 n := nops(A);
 m := (n-1)!;
 if u = 0 then
  return [0$m];
 elif type(u,`+`) then
  return map(`vec0/lie_operad`(A,a),u); 
 else
  if type(u,specfunc(bracket)) then
   ub := u;
   uc := 1;
  elif type(u,`*`) then
   ub,uc := selectremove(type,[op(u)],specfunc(bracket));
   if nops(ub) <> 1 then
    return FAIL;
   fi;
   ub := ub[1];
   uc := `*`(op(uc));
  else
   return FAIL;
  fi;
  if not(type(`vec_table/lie_operad`[A,a],table)) then
   T := table():
   B := `basis/lie_operad`(A,a);
   for i from 1 to m do
    T[B[i]] := [0$(i-1),1,0$(m-i)];
   od:
   `vec_table/lie_operad`[A,a] := eval(T);
  fi;
  return uc *~ `vec_table/lie_operad`[A,a][ub];
 fi;
end:

`vec/lie_operad` := (A::set,a) -> proc(u)
 `vec0/lie_operad`(A,a)(`comb/lie_operad`(a)(u));
end:

# This returns an alternative basis for Lie(X[n]), where
# X[n] = {x[1],...,x[n]}.  The basis elements for Lie(X[n]) are
# obtained from those for Lie(X[n-1]) by substitutions of the
# form x[i] |-> [x[i],x[n]].  Note that we use the inert Bracket
# operation to prevent automatic expansion by the Jacobi identity.
# One can convert using eval(subs(Bracket = bracket,...))

`alt_basis/lie_operad` := proc(n::nonnegint)
 option remember;
 local i,u;
 
 if n = 0 then
  return [];
 elif n = 1 then
  return [x[1]];
 else
  return [seq(seq(subs(x[i]=Bracket(x[i],x[n]),u),i=1..n-1),u in `alt_basis/lie_operad`(n-1))];
 fi;
end:
