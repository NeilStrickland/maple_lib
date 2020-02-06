`is_element/Xi/generic` := (gen_name,el_test) -> (A::set) -> (TT) -> proc(m)
 global reason;
 local pn,TT1,C,T;
 
 pn := cat("is_element/Phi/",gen_name);
 TT1 := `big_sets/trees`(A)(TT);

 if not is_table_on(TT1,m) then
  reason := [pn,"m is not a table on TT1",m,TT1];
  return false;
 fi;

 C := children_map(A)(TT);

 for T in TT1 do
  if not(el_test(C[T])(m[T])) then
   reason := [pn,"m[T] is not in M(C[T])",m[T],T,C[T]];
   return false;
  fi;
 od;

 return true;
end:

# If E is a strongly reduced operad, then there are natural maps
# \theta : (\Xi E)(TT) -> (\Xi E)(UU) whenever TT and UU are full trees
# on the same set A with UU contained in TT.

`theta/Xi/generic` := (gen_name,eta,gamma) -> (A::set) -> (TT,UU) -> proc(x)
 local VV,CV,CT,X,Y,Z,T,P,Q,p,y,w;
 
 if TT = UU then return x; fi;

 T := (TT minus UU)[1];
 VV := TT minus {T};
 P := parent_map(A)(TT)[T];
 CT := children_map(A)(TT);
 CV := children_map(A)(VV);
 Y := CT[T];
 X := CV[P];
 Z := CT[P];
 p := table();
 for Q in X do
  p[Q] := `if`(member(Q,Y),T,Q);
 od;
 y := table();
 y[T] := x[T];
 for Q in X minus Y do
  y[Q] := eta({Q});
 od;

 w := gamma(X,Z)(p)(x[P],y);
 return `theta/Xi/generic`(gen_name,eta,gamma)(A)(VV,UU)(w);
end: