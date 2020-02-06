######################################################################
# Fbar(N)(A) is the Fulton-MacPherson compactification of F(N)(A),
# defined in terms of coherent families as in the LaTeX document.

`is_element/Fbar` := (N::posint) -> (A::set) -> proc(x)
 local B,C,P,Q;
 global reason;

 P := {op(`list_elements/big_subsets`(A))};

 if not(is_table_on(P)(x)) then
  reason := [convert(procname,string),"x is not a table indexed by big subsets of A",eval(x)];  
  return false;
 fi;

 for B in P do 
  if not(`is_element/SW`(N)(B)(x[B])) then
   reason := [convert(procname,string),"x[B] is not in SW(N)(B)",x[B],N,B,reason];  
   return false;
  fi;

  Q := {op(`list_elements/big_subsets`(B))} minus {B};

  for C in Q do
   if not(`is_element/SWW`(N)(B,C)([x[B],x[C]])) then
    reason := [convert(procname,string),"(x[B],x[C]) is not in SWW(N)(B,C)",x[B],x[C],N,B,C,reason];  
    return false;
   fi;
  od;
 od;

 return true;
end;

######################################################################

`normalise/Fbar` := (N::posint) -> (A::set) -> proc(x)
 local x0,B,P;

 x0 := table();
 P := `list_elements/big_subsets`(A);

 for B in P do x0[B] := `normalise/SW`(N)(B)(x[B]); od;
 return eval(x0);
end;

######################################################################

`bottom_normalise/Fbar` := (N::posint) -> (A::set) -> proc(x)
 local x0,B,P;

 x0 := table();
 P := `list_elements/big_subsets`(A);

 for B in P do x0[B] := `bottom_normalise/SW`(N)(B)(x[B]); od;
 return eval(x0);
end;

######################################################################

`is_equal/Fbar` := (N::posint) -> (A::set) -> proc(x,y)
 local B,P;
 global reason;

 P := `list_elements/big_subsets`(A);

 for B in P do 
  if not(`is_equal/SW`(N)(B)(x[B],y[B])) then
   reason := [convert(procname,string),"x[B] <> y[B]",B,x[B],y[B],reason];  
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_leq/Fbar` := NULL;

######################################################################

`is_interior/Fbar` := (N::posint) -> (A::set) -> proc(x)
 local V;

 V := map(a -> x[A][a],A);
 return evalb(nops(V) = nops(A));
end;

######################################################################

`inc/F/Fbar` := (N::posint) -> (A::set) -> proc(u)
 local x,P,T,t;
 
 x := table();
 P := `list_elements/big_subsets`(A);
 for T in P do
  x[T] := table();
  for t in T do
   x[T][t] := u[t];
  od;
 od;

 return eval(x);
end:

######################################################################

`res/Fbar/F` := (N::posint) -> (A::set) -> proc(x)
 if not(`is_interior/Fbar`(N)(A)(x)) then
  return FAIL;
 fi;

 return x[A];
end;

######################################################################
# The functions below could be made much more efficient, but for
# the moment we will stick with the most obvious approach.

`is_critical/Fbar` := (N::posint) -> (A::set) -> proc(x,U)
 local T,TT;

 if nops(U) = 1 then return true; fi;

 TT := map(E -> sort(U union E), 
           `list_elements/nonempty_subsets`(A minus U));

 for T in TT do
  if not(`is_zero/W`(N)(U)(`rho/W`(T,U)(x[T]))) then
   return false;
  fi;
 od;

 return true;
end;

##################################################

`critical_tree/Fbar` := (N::posint) -> (A::set) -> proc(x)
 select(U -> `is_critical/Fbar`(N)(A)(x,U),
        {op(`list_elements/nonempty_subsets`(A))});
end;

##################################################

`random_element/Fbar` := (N::posint) -> (A::set) -> proc()
 local TT,TS,parent,children,u,v,w,t,y,P,T,U,C;

 TT := `random_element/trees`(A)();
 TS := sort([op(TT)],(A,B) -> (nops(A) < nops(B)));
 parent := `parent_map`(A)(TT);
 children := `children_map`(A)(TT);

 u := table();
 for T in TS do
  u[T] := `random_element/F`(N)(children[T])();
  v[T] := table();
  for C in children[T] do
   y := u[T][C];
   for t in C do
    v[T][t] := y;
   od;
  od;
 od:
 
 w := table();

 P := {op(`list_elements/big_subsets`(A))};

 for U in P do
  for T in TT do
   if U minus T = {} then
    w[U] := table();
    for t in U do
     w[U][t] := v[T][t];
    od;    
    break;
   fi;
  od;
 od;

 return eval(w);
end;

`list_elements/Fbar` := NULL;
`count_elements/Fbar` := NULL;

######################################################################

`eta/Fbar` := (N::posint) -> (A::set) -> `if`(nops(A) = 1,table(),FAIL);

######################################################################

`gamma/Fbar` := (N::posint) -> (A::set,B::set) -> (p) -> proc(y,x) 
 local z,TT,T,U,m,a;

 z := table();
 TT := `list_elements/big_subsets`(A);
 for T in TT do
  U := map(a -> p[a],T);
  if nops(U) > 1 then
   m := y[U];
   z[T] := table({seq(a = m[p[a]],a in T)});
  else 
   z[T] := eval(x[op(U)][T]);
  fi;
 od;

 return eval(z);
end;
