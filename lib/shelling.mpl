# This follows "On lexicographically shellable posets" (Bjorner and Wachs)

######################################################################
# Shellings of a finite poset

`is_element/shellings` := (A::set) -> (R) -> proc(S)
 global reason;
 local S0,S1,d,n,i,j,k,c,N,K;

 if A = {} then
  reason := ["is_element/shellings","A is empty"];
  return false;
 fi;

 if not type(S,list) then
  reason := ["is_element/shellings","S is not a list",S];
  return false;
 fi;

 S0 := `maximal_chains/partord`(A)(R);

 if {op(S)} <> S0 then
  reason := ["is_element/shellings","S is not an enumeration of the maximal simplices",S,S0];
  return false;
 fi;

 if nops(map(nops,S0)) <> 1 then
  reason := ["is_element/shellings","The maximal simplices are not all of the same dimension",S0];
  return false;
 fi;

 d := nops(S0[1]) - 1;
 n := nops(S);
 S1 := map(c -> {op(c)},S);
 N := table();

 for i from 2 to n do
  N[i] := select(j -> nops(S1[j] intersect S1[i]) = d,{seq(k,k=1..i-1)});
  if N[i] = {} then
   reason := ["is_element/shellings","The initial shelling condition fails for i",S,i];
   return false;
  fi;
 od:

 for i from 1 to n-1 do
  for j from i+1 to n do
   c := S1[i] intersect S1[j];
   K := select(k -> c minus S1[k] = {} ,N[j]);
   if K = {} then
    reason := ["is_element/shellings","The shelling condition fails for (i,j)",S,i,j];
    return false;
   fi;
  od;
 od; 

 return true;
end:

######################################################################

`is_element/edge_lex_labellings` := (A::set) -> (R) -> proc(l)
 global reason;
 local H,C,d,l0,cut,inc,cmp,R0,C0,C1,c0,c1,ab,a,b,u,i;

 if `bottom_element/partord`(A)(R) = FAIL then
  reason := ["is_element/edge_lex_labellings","There is no bottom element",A,R];
  return false;
 fi;

 if `top_element/partord`(A)(R) = FAIL then
  reason := ["is_element/edge_lex_labellings","There is no top element",A,R];
  return false;
 fi;

 H := `hasse_diagram/partord`(A)(R);

 if not(is_table_on(H)(l)) then
  reason := ["is_element/edge_lex_labellings",
             "l is not a table indexed by the edges of the Hasse diagram",l,H];
  return false;
 fi;

 C := `maximal_chains/partord`(A)(R);
 if nops(map(nops,C)) <> 1 then
  reason := ["is_element/shellings","The maximal simplices are not all of the same dimension",C];
  return false;
 fi;

 d := nops(C[1]) - 1;

 l0 := (c) -> [seq(l[[c[i],c[i+1]]],i=1..nops(c)-1)];
 cmp := proc(c,d)
  local u;

  u := select(x -> x <> 0,l0(d) -~ l0(c));
  return evalb(u <> [] and u[1] > 0);
 end:
 
 cut := proc(c,a,b)
  local i,c0;

  i := 1;
  while c[i] <> a do i := i+1; od;
  c0 := NULL;
  while c[i] <> b do 
   c0 := c0,c[i];
   i := i+1;
  od;
  c0 := [c0,b];
  return c0;
 end:

 inc := proc(c)
  local u,v,m;
  u := l0(c);
  v := [op(u),u[-1]] -~ [u[1],op(u)];
  m := min(op(v));
  return evalb(m >= 0); 
 end:

 R0 := select(ab -> ab[1] <> ab[2],R);
 for ab in R0 do
  a,b := op(ab);
  C0 := select(c -> member(a,c) and member(b,c),C);
  C0 := map(cut,C0,a,b);
  C1 := select(inc,C0);

  if nops(C1) <> 1 then
   reason := 
    ["is_element/shellings",
     "The interval [a,b] does not have a unique increasing maximal chain",
     ab,C0,C1];
   return false;
  fi;

  c1 := op(C1);
  for c0 in C0 minus C1 do
   if not cmp(c1,c0) then
    reason := 
     ["is_element/shellings",
      "In the interval [a,b], the increasing chain is not lex-smallest",
      ab,c0,c1];
    return false;
   fi;
  od;
 od:

 return true;
end:
