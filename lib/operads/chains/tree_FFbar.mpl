`is_element/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 local TT1,B,C,P,T,U;
 global reason;

 if not(type(Q,table)) then
  reason := [convert(procname,string),"Q is not a table",Q];  
  return false;
 fi;

 P := sort(map(sort,map(op,{indices(Q)})));
 TT1 := select(T -> nops(T) > 1,TT);

 if P <> TT1 then
  reason := [convert(procname,string),"Q is not indexed by the big sets in TT",P,TT1];  
  return false;
 fi;

 C := children_map(A)(TT);
 
 for T in P do 
  if not(`is_element/SCP`(N)(T)(Q[T])) then
   reason := [convert(procname,string),"Q[T] is not in SCP(N)(T)",eval(Q[T]),N,T,reason];  
   return false;
  fi;

  for U in C[T] do  
   if nops(U) > 1 and not(`is_element/SCP2`(N)(T,U)([Q[T],Q[U]])) then
    reason := [convert(procname,string),"(Q[T],Q[U]) is not in SCP2(N)(T,U)",eval(Q[T]),eval(Q[U]),N,T,U,reason];  
    return false;
   fi;
  od;
 od;

 return true;
end;

######################################################################

`random_element/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc()
 `mu/tree_Fbar/tree_FFbar`(N)(A)(TT)(`random_element/tree_Fbar`(N)(A)(TT)());
end;

######################################################################

`is_equal/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(P,Q)
 local T,TT1;
 global reason;

 TT1 := select(T -> nops(T) > 1,TT);

 for T in TT1 do 
  if not(`is_equal/SCP`(N)(T)(P[T],Q[T])) then
   reason := [convert(procname,string),"P[T] <> Q[T]",T,P[T],Q[T],reason];  
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_leq/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(P,Q)
 local T,TT1;
 global reason;

 TT1 := select(T -> nops(T) > 1,TT);

 for T in TT1 do 
  if not(`is_leq/SCP`(N)(T)(P[T],Q[T])) then
   reason := [convert(procname,string),"P[T] is not <= Q[T]",T,P[T],Q[T],reason];  
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_interior/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 return `is_element/ICP`(N)(A)(Q[A]);
end;

######################################################################

`inc/ICP/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q0)
 local Q,TT1,T,t;
 
 Q := table();
 TT1 := select(T -> nops(T) > 1,TT);
 for T in TT1 do
  Q[T] := `top/autorel`(T) intersect Q0;
 od;

 return eval(Q);
end:

######################################################################

`res/tree_FFbar/ICP` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 if not(`is_interior/tree_FFbar`(N)(A)(TT)(Q)) then
  return FAIL;
 fi;

 return Q[A];
end;

######################################################################

`res/FFbar/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 local TT1,Q1,T;

 TT1 := select(T -> nops(T) > 1,TT);

 Q1 := table():
 for T in TT1 do Q1[T] := eval(Q[T]); od;

 return eval(Q1);
end:

######################################################################

`ext/tree_FFbar/FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 local TT1,UU,TU,T,U,m,Q1;

 TT1 := select(T -> nops(T) > 1,TT);
 UU := `list_elements/big_subsets`(A);

 Q1 := table():
 
 for U in UU do 
  TU := select(T -> U minus T = {},TT1);
  m := min(op(map(nops,TU)));
  TU := select(U -> nops(U) = m,TU);
  T := TU[1];
  Q1[U] := [seq(`top/autorel`(U) intersect Q[T][i],i=1..N)];
  if not(`is_element/SCP`(N)(U)(Q1[U])) then
   return FAIL;
  fi;
 od;

 return eval(Q1);
end:

######################################################################

`C/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 local L,TT1,T,G;
 L := NULL;
 TT1 := select(T -> nops(T) > 1,TT);
 for T in TT1 do
  G := `gamma/SCP`(N)(T)(Q[T]);
  L := L,seq(seq([i,op(ab)],ab in G[i]),i=1..N);
 od; 
 return {L};
end:

######################################################################

`list_elements/tree_FFbar` := NULL;
`count_elements/tree_FFbar` := NULL;

######################################################################

`mu/tree_Fbar/tree_FFbar` := (N::posint) -> (A::set) -> (TT) -> proc(x)
 local Q,TT1,T;
 
 TT1 := select(T -> nops(T) > 1,TT);

 Q := table();

 for T in TT1 do
  Q[T] := `mu/W/ACP`(N)(T)(x[T]);
 od;

 return eval(Q);
end;


######################################################################

`sigma/tree_FFbar/tree_Fbar` := (N::posint) -> (A::set) -> (TT) -> proc(Q)
 local x,TT1,T;
 
 TT1 := select(T -> nops(T) > 1,TT);

 x := table();

 for T in TT1 do
  x[T] := `sigma/ACP/W`(N)(T)(Q[T]);
 od;

 return eval(x);
end;