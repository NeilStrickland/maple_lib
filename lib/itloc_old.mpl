# Recall that $\Lambda^*$ is defined to be the monoid of lists of
# finite sets of natural numbers.  Such a list can be represented
# in Maple like [{1,4,6},{2,3,4,5},{1}], for example.  Similarly,
# if $N$ is a finite set of natural numbers, then $\Lambda^*[N]$
# is the submonoid generated by the subses of $N$.

# The function `is_element/itloc`(N)(AA) will return true iff
# AA is an element of $\Lambda^*[N]$.

`is_element/itloc` := (N::set) -> proc(AA)
 return type(AA,list(set(nonnegint)));
end:

# The function `is_small_element/itloc`(N)(l)(AA) will return true
# iff AA is an element of $\Lambda^*[N]$ and has length $l$.

`is_small_element/itloc` := (N::set) -> (l::nonnegint) -> proc(AA)
 local A;
 
 if not(`is_element/itloc`(N)(AA)) then
  return false;
 fi;

 if nops(AA) > l then return false; fi;
 A := map(op,{op(AA)});
 if A minus N <> {} then return false; fi;
 return true;
end:

# The function `list_small_elements/itloc`(N)(l) will produce a
# list of all the elements of $\Lambda^*[N]$ that have length l.
# (This will obviously be unmanageably large unless N and l are
# very small.)

`list_small_elements/itloc` := (N::set) -> proc(l::nonnegint)
 option remember;
 local PN,L,i;

 PN := combinat[powerset](N);
 if l = 0 then
  return [[]];
 else
  L := `list_small_elements/itloc`(N)(l-1);
  return [seq(seq([op(AA),A],A in PN),AA in L)];
 fi;
end:

# The function `list_smaller_elements/itloc`(N)(l) lists
# elements of length <= l.

`list_smaller_elements/itloc` := (N::set) -> proc(l::nonnegint)
 [seq(op(`list_small_elements/itloc`(N)(k)),k=0..l)];
end:

# The function `count_small_elements/itloc`(N)(l) returns
# the number of elements of length l.

`count_small_elements/itloc` := (N::set) -> (l::nonnegint) ->
 2^(nops(N) * l);

# The function `random_small_element/itloc`(N)(l)() returns
# a randomly chosen element of $\Lambda^*[N]$ of length l.
# (Note the extra pair of brackets in the syntax.)

`random_small_element/itloc` := (N::set) -> (l::nonnegint) -> proc()
 local r;
 
 r := `random_element/subsets`(N);
 return [seq(r(),i=1..l)];
end:

# The function `o/itloc` is the multiplication law for the
# monoid $\Lambda^*$: so for example `o/itloc`(AA,BB,CC) is
# just the list obtained by concatenating AA, BB and CC.

`o/itloc` := () -> map(op,[args]);

# `id/itloc` is the empty list, which is the identity element
# of the monoid $\Lambda^*$.

`id/itloc` := [];

# `omega/itloc`(AA) is the union of all the sets in the list AA.
# `cap/itloc`(AA,B) is the sequence of intersections of sets in
# AA with the fixed set B. (This is defn-om in the LaTeX file.)

`omega/itloc` := (AA) -> map(op,{op(AA)});
`cap/itloc` := (AA,B) -> map(A -> `intersect`(A,B),AA);

# `sigma/itloc`(N)(AA) is the intersection of all the sets in the
# list AA, to be interpreted as N if the list AA is empty.
# This is essentially the same as in rem-sg-xi in the LaTeX file.

`sigma/itloc` := (N::set) -> (AA) -> `intersect`(N,op(AA));

# `prec/itloc`(A,B) returns true if every element of A is strictly
# less than every element of B.  The function `preceq/itloc`(A,B)
# returns true if every element of A is less than or equal to
# every element of B.  These are in defn-prec in the LaTeX file.
`prec/itloc` := proc(A::set,B::set)
 if A = {} or B = {} then return true; fi;
 return evalb(max(op(A)) < min(op(B)));
end:

`preceq/itloc` := proc(A::set,B::set)
 if A = {} or B = {} then return true; fi;
 return evalb(max(op(A)) <= min(op(B)));
end:

# The next five definitions correspond to defn-reduced in the LaTeX file.

`is_top_reduced/itloc` := proc(AA)
 local t;
 t := map(A -> max(-infinity,op(A)),AA);
 return evalb(t = sort(t));
end:

`is_bottom_reduced/itloc` := proc(AA)
 local b;
 b := map(A -> min(op(A),infinity),AA);
 return evalb(b = sort(b));
end:

`is_unnested/itloc` := proc(AA)
 local r,i;
 r := nops(AA);
 for i from 1 to r-1 do
  if AA[i] minus AA[i+1] = {} then
   return false;
  fi;
  if AA[i+1] minus AA[i] = {} then
   return false;
  fi;
 od;
 return true;
end:

`is_end_reduced/itloc` := proc(AA)
 `is_top_reduced/itloc`(AA) and
 `is_bottom_reduced/itloc`(AA);
end:

`is_reduced/itloc` := proc(AA)
 `is_top_reduced/itloc`(AA) and
 `is_bottom_reduced/itloc`(AA) and
 `is_unnested/itloc`(AA);
end:

# The next three definitions correspond to defn-reductions and
# lem-trimming-confluent
`beta/itloc` := proc(AA)
 local r,i,n,BB;

 r := nops(AA);
 if r = 0 then return []; fi;
 BB := table();
 BB[1] := AA[1];
 for i from 2 to r do 
  if BB[i-1] = [] then 
   return [[]];
  fi;
  n := min(BB[i-1]);
  BB[i] := select(j -> evalb(j >= n),AA[i]);
 od;
 return [seq(BB[i],i=1..r)];
end:

`tau/itloc` := proc(AA)
 local r,i,n,BB;

 r := nops(AA);
 if r = 0 then return []; fi;
 BB := table();
 BB[r] := AA[r];
 for i from r-1 to 1 by -1 do 
  if BB[i+1] = [] then 
   return [[]];
  fi;
  n := max(BB[i+1]);
  BB[i] := select(j -> evalb(j <= n),AA[i]);
 od;
 return [seq(BB[i],i=1..r)];
end:

`delta/itloc` := proc(AA) 
 local r,m,i,BB,CC,Bi,Cm,U,V,ok;

 r := nops(AA);
 if r = 0 then return []; fi;

 ok := false;
 CC := AA;
 while not(ok) do
  BB := CC;
  r := nops(BB);
  CC := [BB[1]];
  m := 1;
  for i from 2 to r do
   Bi := {op(BB[i])};
   Cm := {op(CC[m])};
   U := Bi minus Cm;
   V := Cm minus Bi;
   if U = {} then
    CC := [seq(CC[j],j=1..m-1),BB[i]];
   elif V <> {} then
    CC := [op(CC),BB[i]];
    m := m+1;
   fi;
  od: 
  ok := evalb(CC = BB);
 od;
 
 return BB;
end:

`end_reduce/itloc` := (AA) -> `tau/itloc`(`beta/itloc`(AA)):

`reduce/itloc` := (AA) -> `delta/itloc`(`tau/itloc`(`beta/itloc`(AA))):

`rho/itloc` := eval(`reduce/itloc`):

# `oo/itloc` concatenates its arguments, and then applies the
# reduction map.

`oo/itloc` := proc()
 `reduce/itloc`(`o/itloc`(args));
end:

######################################################################

# The set $\Theta(AA)$ of threads is defined in defn-threads.
# The function `is_element/threads/itloc`(AA)(a) returns true
# iff a is a thread for AA.

`is_element/threads/itloc` := (AA) -> proc(a)
 local r,i;

 r := nops(AA);
 if not(type(a,list) and nops(a) = r) then
  return false;
 fi;

 for i from 1 to r do
  if not(member(a[i],AA[i])) then
   return false;
  fi;
 od;

 if a <> sort(a) then
  return false;
 fi;

 return true;
end:

# The function `is_leq/threads/itloc`(AA)(a,b) returns true iff
# a[i] <= b[i] for all i.

`is_leq/threads/itloc` := (AA) -> proc(a,b)
 local i;
 for i from 1 to nops(AA) do
  if a[i] > b[i] then return false; fi;
 od;
 return true;
end:

# The function `list_elements/threads/itloc`(AA) returns a list
# of all the threads for AA.

`list_elements/threads/itloc` := proc(AA)
 local r,AA0,L0,L,U,a0;

 r := nops(AA);

 if r = 0 then
  return [[]];
 elif r = 1 then
  return [op(map(a -> [a],AA[1]))];
 fi;

 AA0 := [seq(AA[i],i=1..r-1)];
 L0 := `list_elements/threads/itloc`(AA0);
 L := NULL;
 for a0 in L0 do
  U := select(a -> a0[r-1] <= a,AA[r]);
  L := L,seq([op(a0),a],a in U);
 od:
 return [L];
end:

# The function `random_element/threads`(AA)() attempts to return
# a randomly chosen thread for AA.  It is not very intelligent,
# so it may fail to find a thread even if one exists.  It will
# return the symbol FAIL if it does not find a thread.

`random_element/threads/itloc` := (AA) -> proc(num_tries::posint := 10)
 local k,n,a,i,B;

 if min(op(map(nops,AA))) = 0 then return FAIL; fi;

 k := num_tries;
 n := nops(AA);

 while k > 0 do
  k := k-1;
  a := [random_element_of(AA[1])];
  for i from 2 to n do
   B := select(b -> b >= a[-1],AA[i]);
   if B = {} then
    break;
   else
    a := [op(a),random_element_of(B)];
   fi;
  od;
  if nops(a) = n then return a; fi;
 od;

 return FAIL;
end:

# We do not know an efficient method to compute the number of threads,
# so we set `count_elements/threads/itloc` to NULL.  
`count_elements/threads/itloc` := NULL:

# If the poset of threads is nonempty then it will have a smallest
# element, which will be returned by the function
# `bot/threads/itloc`(AA).

`bot/threads/itloc` := proc(AA)
 local BB;
 BB := `beta/itloc`(AA);
 if member({},BB) then
  return FAIL;
 else
  return map(min,BB);
 fi;
end:

# If the poset of threads is nonempty then it will have a largest
# element, which will be returned by the function
# `top/threads/itloc`(AA).

`top/threads/itloc` := proc(AA)
 local CC;
 CC := `tau/itloc`(AA);
 if member({},CC) then
  return FAIL;
 else
  return map(max,BB);
 fi;
end:

# `is_threadable/itloc`(AA) returns true iff AA has a thread
`is_threadable/itloc` :=
 (AA) -> (`bot/threads/itloc`(AA) <> FAIL);

# `min_thread_sets/itloc`(AA) returns the minimal elements of the
# poset of thread sets for AA (as in defn-threads)
`min_thread_sets/itloc` := proc(AA)
 local U,V,W,a,b;
 U := {op(`list_elements/threads/itloc`(AA))};
 U := map(u -> {op(u)},U);
 U := [op(U)];
 U := sort(U,(a,b) -> evalb(nops(a) < nops(b)));
 V := [];
 for a in U do
  W := select(b -> b minus a = {},V);
  if W = [] then V := [op(V),a]; fi;
 od;
 return {op(V)};
end:
 
######################################################################

# $\Phi_0[N]$ is the submonoid of $\Lambda[N]$ generated by the
# functors $L_{K(n)}$.  It bijects naturally with the subset of
# $\Lambda^*[N]$ consisting of the zero element [{}], together
# with all elements [{a[1]},...,{a[r]}] with a[1] <= ... <= a[r].

`is_element/Phi0/itloc` := (N::set(nonnegint)) -> proc(AA)
 local P;
 
 if not(`is_element/itloc`(N)(AA)) then
  return false;
 fi;
 
 if AA = [{}] then return true; fi;

 if {1,op(map(nops,AA))} <> {1} then
  return false; # not all singletons
 fi;

 P := map(op,AA);
 if sort(P) <> P then
  return false;
 fi;
 
 return true;
end:

`is_leq/Phi0/itloc` := (N::set(nonnegint)) -> proc(AA,BB)
 local P,Q;
 
 if AA = [{}] then return true; fi;
 if BB = [{}] then return false; fi;
 P := {op(map(op,AA))};
 Q := {op(map(op,AA))};
 
 return evalb(P minus Q = {});
end:

`list_elements/Phi0/itloc` := proc(N::set(nonnegint))
 local L;
 L := combinat[choose](sort([op(N)]));
 L := map(P -> map(i -> {i},P),L);
 L := [[{}],op(L)];
 return L;
end:

`random_element/Phi0/itloc` := proc(N::set(nonnegint))
 local P,AA;
 
 if rand(1..6)() = 1 then
  return [{}];
 else
  P := sort([op(random_subset_of(N)())]);
  AA := map(u -> {u},P);
  return AA;
 fi;
end:

`count_elements/Phi0/itloc` := proc(N::set(nonnegint))
 1 + 2^nops(N);
end:

`o/Phi0/itloc` := proc()
 local AA,P;

 if member([{}],[args]) then
  return [{}];
 fi;

 AA := map(op,[args]);
 P := map(op,AA);
 if P <> sort(P) then
  return [{}];
 fi;

 return AA;
end:

`id/Phi0/itloc` := [];

######################################################################

# M11/itloc(N)(A) is the set $M'_{N,A}$ from defn-M-prime

`is_element/M11/itloc` := (N::set(nonnegint)) -> (A::set(nonnegint)) -> proc(T)
 evalb(type(T,set) and (T minus N = {}) and (T intersect A <> {})); 
end:

`is_leq/M11/itloc` := (N) -> (A) -> (T0,T1) -> evalb(T0 minus T1 = {}):

`list_elements/M11/itloc` := (N::set(nonnegint)) -> proc(A::set(nonnegint))
 return [op(select(T -> T intersect A <> {},combinat[powerset](N)))];
end:

`random_element/M11/itloc` := (N::set(nonnegint)) -> (A::set(nonnegint)) -> proc()
 local U,V;
 
 U := `random_element/nonempty_subsets`(A)();
 V := `random_element/subsets`(N minus A)();
 return U union V;
end:

`count_elements/M11/itloc` := (N::set(nonnegint)) -> proc(A::set(nonnegint))
 2^nops(N) - 2^nops(N minus A);
end:

######################################################################

# M1/itloc(N)(AA) is the set $M'_{N,AA}$ from defn-M-prime-multi

`is_element/M1/itloc` := (N::set(nonnegint)) -> (AA) -> proc(TT)
 local r,i;

 r := nops(AA);

 if not(type(TT,list(set(nonnegint)))) then
  return false;
 fi;
 
 if nops(TT) <> r then
  return false;
 fi;

 if map(op,{op(TT)}) minus N <> {} then
  return false;
 fi;
 
 for i from 1 to r do
  if TT[i] intersect AA[i] = {} then
   return false;
  fi;
 od;

 for i from 1 to r-1 do
  if not(`preceq/itloc`(TT[i],TT[i+1])) then
   return false;
  fi;
 od;

 return true;
end:

`is_leq/M1/itloc` := (N) -> (AA) -> proc(TT0,TT1) 
 `and`(seq(TT0[i] minus TT1[i] = {},i=1..nops(TT0)));
end:

`list_elements/M1/itloc` := (N::set(nonnegint)) -> proc(AA)
 local r,m,L,L0,L1,L2,AA0,TT0;
 r := nops(AA);
 if r = 0 then
  return [[]];
 fi;

 L1 := `list_elements/M11/itloc`(N)(AA[r]);

 if r = 1 then
  return map(T -> [T],L1);
 fi;

 AA0 := [seq(AA[i],i=1..r-1)];
 L0 := `list_elements/M1/itloc`(N)(AA0);
 L := NULL;
 for TT0 in L0 do
  m := max(TT0[r-1]);
  L2 := select(T -> min(T) >= m,L1);
  L := L,seq([op(TT0),T],T in L2);
 od:
 L := [L];
 return L;
end:

`random_element/M1/itloc` := (N::set(nonnegint)) -> (AA) -> proc(num_tries := 10)
 local r,k,AA0,TT0,m,N0,A0,T;
 r := nops(AA);
 if r = 0 then
  return [];
 fi;

 k := num_tries;
 while k > 0 do
  k := k-1;
  AA0 := [seq(AA[i],i=1..r-1)];
  TT0 := `random_element/M1/itloc`(N)(AA0)(num_tries);
  if TT0 <> FAIL then
   N0 := N;
   if r > 1 then
    m := max(op(TT0[r-1])); 
    N0 := select(i -> (i >= m),N);
   fi;
   A0 := N0 intersect AA[r];
   if A0 <> {} then 
    T := `random_element/M11/itloc`(N0)(A0)();
    if T <> FAIL then
     return [op(TT0),T];
    fi;
   fi;
  fi;
 od;

 return FAIL;
end:

`count_elements/M1/itloc` := NULL:

######################################################################

`is_element/M2/itloc` := (N::set(nonnegint)) -> (AA) -> proc(T::set(nonnegint)) 
 `is_threadable/itloc`(`cap/itloc`(AA,T)) and
 (T minus N) = {};
end:

`is_leq/M2/itloc` := (N::set(nonnegint)) -> (AA) -> proc(T0,T1) 
 evalb(T0 minus T1 = {});
end:

`list_elements/M2/itloc` := (N::set(nonnegint)) -> proc(AA)
 local L;

 L := `list_elements/threads/itloc`(AA);
 L := map(a -> {op(a)},L);
 return [seq(seq(T union U,U in combinat[powerset](N minus T)),T in L)];
end:

`random_element/M2/itloc` := (N::set(nonnegint)) -> (AA) -> proc()
 local a,T;
 a := `random_element/threads/itloc`(AA)();
 if a = FAIL then return FAIL; fi;
 T := {op(a)};
 T := {op(T),op(random_subset_of(N minus T))};
 return T;
end:

`count_elements/M2/itloc` := NULL:

######################################################################

`is_element/M3/itloc` := (N::set(nonnegint)) -> (AA) -> (T) -> proc(TT)
 `is_element/M1/itloc`(N)(AA)(TT) and
  `omega/itloc`(TT) minus T = {};
end:

`is_leq/M3/itloc` := (N::set(nonnegint)) -> (AA) -> (T) -> proc(TT0,TT1)
 `and`(seq(evalb(TT0[i] minus TT1[i] = {}),i=1..nops(TT0)));
end:

`list_elements/M3/itloc` := (N::set(nonnegint)) -> (AA) -> proc(T)
 local BB,L;

 BB := `cap/itloc`(AA,T);
 L := `list_elements/M1/itloc`(T)(BB);
 return L;
end:

`phi/itloc` := (N::set(nonnegint)) -> (AA) -> (T) -> (TT) -> proc(k)
 local r,i,BB,b;
 r := nops(AA);
 if k < 0 or k > 2*r then error("k is out of range"); fi;
 i := ceil(k/2);
 BB := `beta/itloc`(`cap/itloc`(AA,T));
 if member({},BB) then error("T is not a thread set for AA"); fi;
 b := map(min,BB);
 if k = 0 then
  return TT;
 elif k = 2*i then 
  return [seq({b[j]},j=1..i),seq(TT[j],j=i+1..r)];
 else
  return [seq({b[j]},j=1..i-1),TT[i] union {b[i]},seq(TT[j],j=i+1..r)];
 fi;
end: