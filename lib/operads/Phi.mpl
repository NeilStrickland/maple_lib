######################################################################

# General framework for operads freely generated by a strongly 
# reduced Sigma-module.

`is_element/Phi/generic` := (gen_name,el_test) -> (A::set) -> 
proc(TTm)
 local pn,TT,m,TT1,C,T;
 global reason;

 pn := cat("is_element/Phi/",gen_name);
 
 if not(type(TTm,list) and nops(TTm) = 2) then
  reason := [pn,"TTm is not a list of length two"];
  return false;
 fi;

 TT,m := op(TTm);

 if not(`is_element/full_trees`(A)(TT)) then
  reason := [pn,"TT is not a full tree on A",TT,A];
  return false;
 fi;

 if not type(m,table) then
  reason := [pn,"m is not a table"];
  return false;
 fi;

 if map(nops,{indices(m)}) <> {1} then
  reason := [pn,"m is not a unidimensional table"];
  return false;
 fi;
 
 TT1 := map(op,[indices(m)]);
 
 if {op(TT1)} <> select(T -> nops(T) > 1,TT) then
  reason := [pn,"m is not indexed by the big sets in TT",TT1,TT];
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
end;

######################################################################

`is_equal/Phi/generic` :=  (gen_name,eq_test) -> (A::set) -> 
proc(TTm,UUn)
 local pn,TT,m,UU,n,C,TT1,T;
 global reason;

 pn := cat("is_element/realisation/",poset_name);

 TT,m := op(TTm);
 UU,n := op(UUn);

 if not(`is_equal/full_trees`(A)(TT,UU)) then
  reason := [pn,"TT <> UU",TT,UU];
  return false;
 fi;

 C := children_map(A)(TT);
 TT1 := select(T -> nops(T) > 1,TT);

 for T in TT1 do
  if not(eq_test(C[T])(m[T],n[T])) then
   reason := [pn,"m[T] <> n[T]",T,C[T],m[T],n[T]];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`eta/Phi/generic` := (gen_name) -> (A::set) -> `if`(nops(A) = 1,[{A},table()],FAIL);

######################################################################

`gamma/Phi/generic` := (gen_name,action) -> (A::set,B::set) -> (p) -> proc(UUn,TTm)
 local F,FF,UU,UU1,CU,CV,CT,U,U0,Ui,CU0,CU1,TT,T,VV,f,b,m,n,o;
 
 F := fibres(A,B)(p);
 UU,n := op(UUn);
 CU := children_map(B)(UU);
 FF := table();
 for U in UU do
  FF[U] := `union`(seq(F[b],b in U));
 od;
 
 TT := table();
 CT := table();
 m := table();
 
 for b in B do
  TT[b],m[b] := op(TTm[b]);
  CT[b] := children_map(F[b])(TT[b]);
 od;

 VV := `gamma/trees`(A,B)(p)(UU,TT);
 CV := children_map(A)(VV);
 
 o := table();
 UU1 := select(U -> nops(U) > 1,UU);
 for U in UU do
  Ui := FF[U];
  CU0 := CU[U];
  CU1 := CV[Ui];
  f := table();
  for U0 in CU0 do f[U0] := FF[U0]; od;
  o[Ui] := action(CU0,CU1)(f)(n[U]);
 od;

 for b in B do
  for T in TT[b] do
   if nops(T) > 1 then
    o[T] := m[b](T);
   fi;
  od;
 od;

 return(eval([VV,o]));
end:

######################################################################

`zeta/Phi/generic` := (gen_name,action) -> (A::set) -> proc(m)
 local TT,n,f,A1,a;
 
 if nops(A) = 1 then return(`eta/Phi/generic`(gen_name)(A)); fi;

 TT := corolla(A);
 n := table();
 f := table();
 A1 := {seq({a},a in A)};
 for a in A do f[a] := {a}; od;
 n[A] := action(A,A1)(f)(m);
 return eval([TT,n]);
end:

######################################################################

`epsilon/Phi/generic` := (gen_name,eta,gamma) -> (A::set) -> proc(TTm)
 local TT,m;

 TT,m := op(TTm);
 return `theta/Xi/generic`(gen_name,eta,gamma)(A)(TT,corolla(A))(m);
end;