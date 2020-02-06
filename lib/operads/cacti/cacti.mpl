`is_element/cacti` := (A::set) -> proc(C)
 global reason;
 local tag,n,i,j,a,b,U;

 tag := "is_element/cacti";

 if not(is_table_on(A)(C)) then
  reason := [tag,"C is not a table indexed by A",C,A];
  return false;
 fi;

 for a in A do
  if not(`is_element/cactus_lobes`(C[a])) then
   reason := [tag,"C[a] is not a cactus lobe",a,C[a],reason];
   return false;
  fi;
 od;

 n := nops(A);
 for i from 1 to n do 
  for j from i+1 to n do
   a := A[i];
   b := A[j];
   if `are_crossed/RZ_set`(C[a][2],C[b][2]) then
    reason := [tag,"lobes C[a] and C[b] are crossed",a,b,C[a],C[b]];
    return false;
   fi;
  od;
 od;

 U := `empty/RZ_set`;
 for a in A do
  U := `union/RZ_set`(U,C[a][2]);
 od;

 if U <> `top/RZ_set` then
  reason := [tag,"The lobes do not fill the whole circle",C,U];
  return false;
 fi;

 return true;
end:

`is_equal/cacti` := (A::set) -> proc(C0,C1)
 `and`(seq(evalb(C0[a]=C1[a]),a in A));
end:

`is_leq/cacti` := NULL:

######################################################################

`random_element/cacti` := (A) -> proc()
 local J,s,s1,n,l,m,c,T,i,a,C;

 if nops(A) = 0 then return FAIL; fi;

 J,s := op(`random_element/cactus_planar_trees`(A)());

 if nops(A) = 1 then
  return table([op(A) = `id/cactus_lobes`]);
 fi;
 
 s1 := map(e -> e[1],s);
 n := nops(s1);
 l := [seq(rand(1..6)(),i=1..n)];
 l := l /~ `+`(op(l));
 m := [seq(add(l[i],i=1..j),j=0..n)];
 c := table([seq(a = `random_element/RZ`(),a in A)]);
 T := table([seq(a = [],a in A)]):
 for i from 1 to n do
  T[s1[i]] := [op(T[s1[i]]),m[i],m[i+1]];
 od:
 C := table():
 for a in A do C[a] := [c[a],T[a]]; od:
 C := `source_shift/cacti`(A)(`random_element/RZ`())(C):
 return eval(C);
end:

`list_elements/cacti` := NULL:
`count_elements/cacti` := NULL:

######################################################################
# Here t should be in R/Z

`source_shift/cacti` := (A::set) -> (t) -> proc(C)
 local D,a;

 D := table():
 for a in A do 
  D[a] := `source_shift/cactus_lobes`(t)(C[a]);
 od:
 return eval(D);
end:

######################################################################
# Here t should be a table with indices A and entries in R/Z

`target_shift/cacti` := (A::set) -> (t) -> proc(C)
 local D,a;

 D := table():
 for a in A do 
  D[a] := `target_shift/cactus_lobes`(t[a])(C[a]);
 od:
 return eval(D);
end:

######################################################################
# The standard basepoint for the space of cacti on {1,..,n}

`basepoint/cacti` := proc(n::posint)
 local i,C;
 C := table():
 for i from 1 to n do 
  C[i] := [0,[(i-1)/n,i/n]];
 od:
 return eval(C);
end:

######################################################################
# A path in the space of cacti on {1,..,n}, from the basepoint to 
# its image under the transposition (m,m+1).

`omega/cacti` := (n::posint) -> (m::posint) -> proc(t)
 local A,C,k;
 if m >= n then error("m is out of range"); fi;
 A := {seq(i,i=1..n)};
 C := table():
 for k from 1 to n do
  if k = m then
   C[k] := [0,[m-1+t,m+t] /~ n]
  elif k = m+1 then
   if t = 0 then
    C[k] := [0,[m,m+1] /~ n];
   elif t = 1 then
    C[k] := [0,[m-1,m] /~ n];
   else
    C[k] := [0,[m-1,m-1+t,m+t,m+1] /~ n];
   fi;
  else
   C[k] := [0,[k-1,k] /~ n];
  fi;
 od:
 return eval(C);
end:

######################################################################
# A family of paths in the space of cacti on {1,2,3}

`alpha/cacti` := proc(i,t)
 local L,C;
 if t < 0 or t > 1 then
  error("t out of range");
 fi;
 if t = 0 then
  L := [[1,2] /~ 3,[0,1] /~ 3,[2,3] /~ 3];
 elif t = 1 then
  L := [[0,1] /~ 3,[1,2] /~ 3,[2,3] /~ 3];
 else
  L := [[0,t,1+t,2] /~ 3,[t,1+t] /~ 3,[2,3] /~ 3];
 fi;
 L := map(u -> [0,u],L);
 C := table():
 if i = 1 then
  C[1] := L[1]; C[2] := L[2]; C[3] := L[3]; 
 elif i = 2 then
  C[1] := L[3]; C[2] := L[1]; C[3] := L[2]; 
 elif i = 3 then
  C[1] := L[2]; C[2] := L[3]; C[3] := L[1];
 else
  error("i out of range");
 fi; 
 return eval(C);
end:

######################################################################
# A family of paths in the space of cacti on {1,2,3}

`beta/cacti` := proc(z,i,t)
 local C,w;

 C := `alpha/cacti`(i,t);
 if i = 1 then 
  w := z;
 elif i = 2 then
  w := z - (1+t)/3;
 elif i = 3 then
  w := z + (1+t)/3;
 else
  error("i is out of range");
 fi;

 return `source_shift/cacti`({1,2,3})(w)(C);
end:

######################################################################

`planar_tree/cacti` := (A::set) -> proc(C)
 local S,SI,D,E,E0,E1,EI,J,t0,t1,t,j,jt,u,v,a,ok,s;

 S := table():
 D := table():
 SI := table():

 for a in A do
  S[a] := `starts/RZ_set`(C[a][2]);
  D[a] := `boundary/RZ_set`(C[a][2]);
  for t in S[a] do SI[t] := a; od;
 od:

 E1 := map(op,{seq(S[a],a in A)});
 E1 := sort([op(E1)]);

 J := {};
 E0 := E1;
 EI := table():
 while E0 <> [] do
  t0 := E0[1];
  jt := {t0};
  j := {SI[t0]};
  for t1 in [op(2..-1,E0)] do
   u := `interval/RZ_set`(t0,t1);
   v := `interval/RZ_set`(t1,t0);
   ok := true;
   for a in A do
    if not (`intersect/RZ_set`(u,C[a][2]) = `empty/RZ_set` or 
            `intersect/RZ_set`(v,C[a][2]) = `empty/RZ_set`) then
     ok := false;
     break;
    fi;
   od;
   if ok then
    jt := {op(jt),t1};
    j := {op(j),SI[t1]};
   fi;
  od:
  J := {op(J),j};
  E0 := select(t -> not(member(t,jt)),E0);
  for t in jt do EI[t] := [SI[t],j]; od;
 od:

 s := [seq(EI[t],t in E1)];
 return [J,s];
end:

######################################################################

# This computes the matrix x as in lem-cactus-x

`x/cacti` := (A::set) -> proc(C)
 local x,a,a1;

 x := table();
 for a1 in A do
  for a in A do
   if a1 <> a then
    x[a,a1] := `eval/cactus_lobes`(C[a])(C[a1][2][1]);
   fi;
  od:
 od:

 return eval(x);
end:

######################################################################

`eta/cacti` := (A::set) ->
 `if`(nops(A) = 1,table([op(A) = `id/cactus_lobes`]),FAIL):
 
`gamma/cacti` := (A::set,B::set) -> (p) -> proc(D,C)
 local a,E;

 E := table():
 for a in A do
  E[a] := `o/cactus_lobes`(C[p[a]][a],D[p[a]]);
 od:
 return eval(E);
end:

######################################################################

`phi/ord_simplex_interior/cacti` := (A::set) -> proc(Rx)
 local R,x,n,C,y,i;
 R,x := op(Rx);
 n := nops(R);
 C := table():
 y := [seq(add(x[R[i]],i=1..j),j=0..n)];
 for i from 1 to n do
  C[R[i]] := [0,[y[i],y[i+1]]];
 od:
 return eval(C);
end:

######################################################################

`phi/cacti/simplex_interior` := (A::set) -> proc(C)
 local x,a;
 x := table();
 for a in A do
  x[a] := `length/RZ_set`(C[a][2]);
 od:
 return eval(x):
end: 

######################################################################

`plot/cacti` := (A::set) -> proc(C,r := 1,c := [0,0])
 local n,z;
 n := nops(A);
 z := table([seq(i = `centroid_R2/RZ_set`(C[A[i]][2]),i=1..n)]);
 display(
  seq(`plot/RZ_set`(C[A[i]][2],r,c,colour=standard_colour(i)),i=1..n),
  seq(point(z[i],colour=standard_colour(i)),i=1..n)
 );
end: