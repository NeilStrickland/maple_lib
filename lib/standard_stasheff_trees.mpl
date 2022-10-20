######################################################################
# A standard Stasheff tree for n is a Stasheff tree for the set
# {1,...,n} with its standard ordering.

`is_element/standard_stasheff_trees` := (n::posint) -> proc(TT)
 local A,T,i;
 global reason;

 A := {seq(i,i=1..n)};

 if not(`is_element/full_trees`(A)(TT)) then
  reason := ["is_element/standard_stasheff_trees","TT is not a full tree",TT,reason];
  return false;
 fi;

 for T in TT do
  if nops(T) <> max(T) - min(T) + 1 then
   reason := ["is_element/standard_stasheff_trees","T is not an interval",T];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_equal/standard_stasheff_trees` := (n::posint) -> proc(TT,UU)
 local A,i;

 A := {seq(i,i=1..n)};
 return `is_equal/trees`(A)(TT,UU);
end;

######################################################################

`is_leq/standard_stasheff_trees` := (n::posint) -> proc(TT,UU)
 local A,i;

 A := {seq(i,i=1..n)};
 return `is_leq/trees`(A)(TT,UU);
end;

######################################################################

`random_element/standard_stasheff_trees` := (n::posint) -> proc()
 local N,pi,TT,UU,U,i;

 if n = 0 then return FAIL; fi;
 if n = 1 then return {{1}}; fi;

 N := {seq(i,i=1..n)};

 pi := {N};
 while nops(pi) = 1 do 
  pi := `random_element/interval_partitions`(n)();
 od;

 TT := N;

 for U in pi do 
  UU := `random_element/standard_stasheff_trees`(nops(U))();

  UU := map(V -> map(v -> v+min(U)-1,V),UU);
  TT := TT,op(UU);
 od;

 TT := {TT};

 return TT;
end;

######################################################################

`list_elements/standard_stasheff_trees` := proc(n::posint)
 option remember;

 local TTT,UUU,TT,UU,N,IP,pi,pi_list,P,B,b,i;
 if n = 0 then return []; fi;
 if n = 1 then return [{{1}}]; fi;

 N := {seq(i,i=1..n)};
 TTT := NULL;
 IP := select(pi -> pi <> {N},`list_elements/interval_partitions`(n));

 for pi in IP do
  pi_list := [op(pi)];
  P := NULL;
  for B in pi_list do
   b := min(op(B));
   UUU := `list_elements/standard_stasheff_trees`(nops(B));
   UUU := map(UU -> map(V -> map(v -> b-1+v,V),UU),UUU);
   P := P,UUU;
  od;
  P := `cartesian_product/lists`(P);
  TTT := TTT,op(map(UU -> {N,op(map(op,UU))},P));
 od:
 return([TTT]);
end:

######################################################################
# This is A001003 in OEIS

`count_elements/standard_stasheff_trees` := proc(n)
 local f,L,i;
 if n = 0 then
  return 0;
 elif n = 1 then 
  return 1;
 else
  f := (k) -> op([seq(i,i=0..k+1),seq(k-i,i=0..k)]); 
  L := [0];
  for i from 1 to n-2 do
   L := map(f,L);
  od;
  return nops(L);
 fi;
end;

# Alternative formula for n > 1:
# add(2^k*3^(n-2-2*k)*binomial(n-2,2*k)*binomial(2*k,k)/(k+1),k=0..floor((n-2)/2));

`dim/standard_stasheff_trees` := (n) -> proc(TT)
 2*n - 1 - nops(TT);
end:

`count_by_dim/standard_stasheff_trees` := proc(n,k)
 if k < 0 or k > n-2 then return 0; fi;

 return binomial(n-2,n-k-2) * binomial(2*n-k-2,n) / (n - k - 1);
end:


######################################################################

`draw/standard_stasheff_trees` := (n::posint) -> proc(TT)
 local p,P,T,U,m,i;
 p := table();
 P := NULL;
 for T in TT do 
  p[T] := [`+`(op(T))/nops(T),nops(T)];
 od;
 
 m := parent_map({seq(i,i=1..n)})(TT);

 for T in TT do
  if nops(T) < n then
   U := m[T];
   P := P,line(p[T],p[U]);
  fi;
 od;
 for T in TT do
  P := P,point(p[T],colour=red,symbol=solidcircle,symbolsize=20);
 od;

 P := display(P,axes=none,scaling=constrained);
 return P;
end:

######################################################################

`root_children/standard_stasheff_tree` := (n::posint) -> proc(TT)
 local C,A,i,XX,X,m;

 if n = 1 then return []; fi;
 
 C := NULL;
 A := {seq(i,i=1..n)};
 while A <> {} do
  i := min(op(A));
  XX := select(X -> member(i,X) and nops(X) < n,TT);
  m := max(op(map(nops,XX)));
  XX := select(X -> nops(X) = m,XX);
  X := XX[1];
  C := C,X;
  A := A minus X;
 od:
 return [C];
end:

######################################################################
# A Stasheff tree TT on A is binary if every non-minimal set in TT has
# precisely two children.  This holds iff |TT| = 2|A|-1.

`is_binary/standard_stasheff_trees` := (n::posint) -> proc(TT)
 return evalb(nops(TT) = 2*n-1);
end:

######################################################################

`e/loday` := (n::posint) -> proc(pq)
 local p,q;
 p,q := op(pq);
 return [0 $ (p-1), 1 $ (q-p), 0 $ (n-q)];
end: 

######################################################################

`m/loday` := (n::posint) -> pq -> (pq[2]-pq[1]+1)*(pq[2]-pq[1])/2;

######################################################################

`p/loday` := (n::posint) -> proc(pq,u)
 local i;
 return add(u[i],i=pq[1]..pq[2]-1) - `m/loday`(n)(pq);
end:

######################################################################

`is_element/PK` := (n::posint) -> proc(u)
 global reason;
 local p,q;
 
 if not `is_element/R`(n-1)(u) then
  reason := [convert(procname,string),"u is not a list of length n-1",u,n-1];
  return false;
 fi;
 
 if `p/loday`(n)([1,n],u) <> 0 then
  reason := [convert(procname,string),"p_A(u) <> 0",u];
  return false;
 fi;

 for p from 1 to n do
  for q from p to n do
   if `p/loday`(n)([p,q],u) < 0 then
    reason := [convert(procname,string),"p_J(u) < 0",u,[p,q]];
    return false;
   fi;
  od;
 od;

 return true;
end;

######################################################################

`tau/loday` := (n::posint) -> proc(u)
 local TT,p,q,i;
 TT := NULL;
 for p from 1 to n do
  for q from p to n do
   if `p/loday`(n)([p,q],u) = 0 then
    TT := TT,{seq(i,i=p..q)};
   fi;
  od;
 od;
 TT := {TT};

 return TT;
end;
 
######################################################################

`is_element/Sigma0_loday` := (n::posint) -> proc(sigma)
 global reason;
 local JJ,J,g,i,j,k;
 
 if not type(sigma,table) then
  reason := [convert(procname,string),"sigma is not a table",sigma];
  return false;
 fi;

 JJ := {seq(seq({seq(k,k=i..j)},j=i+1..n),i=1..n)};
 if map(op,{indices(sigma)}) <> JJ then
  reason := [convert(procname,string),"sigma is not indexed by the appropriate set of intervals",sigma,JJ];
  return false;
 fi;

 for J in JJ do
  g := sigma[J];
  if not (type(g,set) and nops(g) = 2 and max(op(g)) - min(op(g)) = 1) then
   reason := [convert(procname,string),"sigma(J) is not a gap",sigma,J,g];
   return false;
  fi;

  if g minus J <> {} then
   reason := [convert(procname,string),"sigma(J) is not a gap in J",sigma,J,g];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`w0/loday` := (n::posint) -> proc(sigma)
 local v,JJ,J,i,j,k;
 
 v := Vector(n-1);
 JJ := {seq(seq({seq(k,k=i..j)},j=i+1..n),i=1..n)};
 for J in JJ do
  i := min(op(sigma[J]));
  v[i] := v[i] + 1;
 end:

 return convert(v,list);
end;

######################################################################

`pi/loday` := (n::posint) -> (TT) -> proc(J)
 local UU,k;

 UU := select(T -> J minus T = {},TT);
 k := min(map(nops,UU));
 UU := select(U -> nops(U) = k,UU);
 return(UU[1]);
end;

######################################################################

`w/loday` := (n::posint) -> proc(TT)
 local v,JJ,J,P,G,T,S,g,m,i,j,k;
 
 v := Vector(n-1);
 JJ := {seq(seq({seq(k,k=i..j)},j=i+1..n),i=1..n)};
 P := table();
 for J in JJ do
  P[J] := `pi/loday`(n)(TT)(J);
 od;
 G := {seq({i,i+1},i=1..n-1)};
 for J in JJ do 
  T := P[J];
  S[J] := NULL;
  for j from min(J) to max(J)-1 do
   g := {j,j+1};
   if P[g] = T then
    S[J] := S[J],g;
   fi;
  od;
  S[J] := {S[J]};
  m := nops(S[J]);
  for g in S[J] do
   v[min(g)] := v[min(g)] + 1/m;
  od;
 od;
 return convert(v,list);
end:

######################################################################

`w/loday/bin` := (n::posint) -> proc(TT)
 local C,T,v,i;
 C := children_map({seq(i,i=1..n)})(TT);
 v := Vector(n-1);
 for i from 1 to n-1 do
  T := `pi/loday`(n)(TT)({i,i+1});
  v[i] := `*`(op(map(nops,C[T])));
 od;
 return convert(v,list); 
end:

######################################################################

`T/loday` := (n::posint) -> proc(i)
 local j,k;
 {seq({j},j=1..n),{seq(j,j=1..n)},
  seq({seq(k,k=1..j)},j=2..i),
  seq({seq(k,k=j..n)},j=i+1..n-1)
 };
end:

######################################################################

`phi/standard_stasheff_trees/PK` := (n::posint) -> (TT) -> `w/loday`(n)(TT);

######################################################################

`phi/realisation/standard_stasheff_trees/PK` := (n::posint) -> proc(x)
 local C,v,TT;
 
 C := map(op,[indices(x)]);
 v := [0$(n-1)];
 for TT in C do
  v := v +~ x[TT] *~ `phi/standard_stasheff_trees/PK`(n)(TT);
 od;

 return v;
end:
