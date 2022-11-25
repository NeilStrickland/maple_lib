# This file relates to the chromatic splitting conjecture (CSC)

# We work with Morava K-theories K(i) for i < N
N := 4:

# For a subset A of {1,...,N-1} we have an iterated localisation
# functor alpha_A.  If the CSC is true, then alpha_A(S) will be
# an exterior algebra over S generated by certain elements
# x([i,a]) of dimension 1 - 2(a - i) and chromatic height i,
# where 0 <= i < a and a is in A.  There is an element x[i,a]
# for every such pair [i,a], but some of them are zero.  The
# ones that are nonzero form a system of exterior generators.
# Products of these generators are represented by expressions
# like x([1,3],[0,5],[6,7]) (for the product of x([1,3]),
# x([0,5]) and x([6,7])).  In these expressions, the arguments
# are expected to appear in increasing order according to
# the comparison function specified below.

# We will also consider some cubical diagrams, indexed by subsets
# of {0,..,n} (which are represented as increasing lists rather
# than sets).  Basis elements in the term indexed by a list A
# are like ex(A,[i1,a1],...,[ir,ar]).  In some contexts we
# also have terms like zx(U,[i1,a1],...,[ir,ar]) in the term
# indexed by A = [].

# `cmp/csc` is a comparison function used for sorting pairs
# [i,a] with 0 <= i < a as above.  To compare [i,a] with [j,b],
# we first compare a with b, then compare i with j if a = b.
`cmp/csc` := proc(u,v)
 return evalb((u[2] < v[2]) or ((u[2] = v[2]) and (u[1] < v[1])));
end:

# The function `mu/csc` is used to multiply expressions involving
# the generators x([i,a]).  

`mu0/csc` := proc(u,v)
 local w,L,i,j;
 if type(u,rational) or type(v,rational) then 
  return u * v;
 elif type(u,specfunc(list(nonnegint),x)) and 
    type(u,specfunc(list(nonnegint),x)) then
  if {op(u)} intersect {op(v)} <> {} then return 0; fi;
  w := [op(u),op(v)];
  L := [seq(seq([i,j],i=1..j-1),j=1..nops(w))];
  L := select(ij -> `cmp/csc`(w[ij[2]],w[ij[1]]),L);
  w := sort(w,`cmp/csc`);
  return (-1)^nops(L) * x(op(w));
 else
  error("Invalid arguments");
 fi;
end:

`mu/csc`:= apply_linear_assoc(`mu0/csc`,x()):

# The function `deg/csc`(u) returns the degree of u (or FAIL if
# u is not homogeneous).  Here x([i,a]) has degree 1 - 2(a-i) < 0,
# e(A) has degree 0, and z(U) has degree 2(min(U) - max(U)) <= 0.

`deg0/csc` := proc(u)
 local ij,U,A;
 if type(u,rational) then
  return 0;
 elif type(u,specfunc(list(nonnegint),x)) then 
  return add(1 - 2*(ij[2] - ij[1]),ij in [op(u)]);
 elif type(u,specfunc(list(nonnegint),zx)) then
  U := op(1,u);
  return 2 * (op(1,U) - op(-1,U)) +
   add(1 - 2*(ij[2] - ij[1]),ij in [op(2..-1,u)]);
 elif type(u,specfunc(list(nonnegint),ex)) then
  A := op(1,u);
  return add(1 - 2*(ij[2] - ij[1]),ij in [op(2..-1,u)]);
 else
  error("Invalid arguments");
 fi;
end:

`deg/csc` := apply_deg(`deg0/csc`):

# The function `height/csc`(u) returns the chromatic height of an
# element.  The height of x([i1,a1],...,[im,am]) is min(i1,...,im).
# The height of e(A) is min(A), and the height of z(U) is min(U).

`height0/csc` := proc(u)
 local ij;
 if type(u,rational) then
  return N;
 elif type(u,specfunc(list(nonnegint),x)) then 
  return min(seq(ij[1],ij in [op(u)]));
 elif type(u,specfunc(list(nonnegint),zx)) then 
  return op(1,op(1,u));
 elif type(u,specfunc(list(nonnegint),ex)) then 
  return op(1,op(1,u));
 else
  error("Invalid arguments");
 fi;
end:

`height/csc` := apply_deg(`height0/csc`):

# We filter exterior algebras by powers of the augmentation ideal,
# i.e. the number of x terms.  Terms e(A) have filtration zero.
# Terms z(U) are given filtration |U| - 1.
`filt0/csc` := proc(u)
 local ij;
 if type(u,rational) then
  return 0;
 elif type(u,specfunc(list(nonnegint),x)) then 
  return 0;
 elif type(u,specfunc(list(nonnegint),zx)) then 
  return nops(op(1,u)) + nops(u) - 2;
 elif type(u,specfunc(list(nonnegint),ex)) then 
  return nops(u) - 1;
 else
  error("Invalid arguments");
 fi;
end:

`filt/csc` := apply_deg(`filt0/csc`):

# We have a different filtration of cubical diagrams in which terms
# attached to a set A have cofiltration |A|.
`cofilt0/csc` := proc(u)
 local ij;
 if type(u,rational) then
  return 0;
 elif type(u,specfunc(list(nonnegint),x)) then 
  return 0;
 elif type(u,specfunc(list(nonnegint),zx)) then 
  return 0;
 elif type(u,specfunc(list(nonnegint),ex)) then 
  return nops(op(1,u));
 else
  error("Invalid arguments");
 fi;
end:

`cofilt/csc` := apply_deg(`cofilt0/csc`):

# This function gives a condensed string representation of monomials.
`to_string/csc`:= proc(u)
 if type(u,specfunc(list(nonnegint),x)) then 
  if nops(u) = 0 then 
   return "1";
  else
   return cat(op(map(ia -> cat("x",op(ia)),[op(u)])));
  fi;
 elif type(u,specfunc(list(nonnegint),zx)) then 
  return cat("z",op(op(1,u)),op(map(ia -> cat("x",op(ia)),[op(2..-1,u)])));
 elif type(u,specfunc(list(nonnegint),ex)) then 
  return cat("e",op(op(1,u)),op(map(ia -> cat("x",op(ia)),[op(2..-1,u)])));
 else
  error("Invalid arguments");
 fi;
end:

# `is_present/csc`(A)(u) returns true if u can be interpreted as
# a chromatic homotopy element (which may be zero) for alpha_A(S),
# or a set or list of such elements.

`is_present/csc` := (A) -> proc(u)
 local v,w,ia,i,a;
 if type(u,rational) then
  return true;
 elif type(u,`+`) or type(u,list) or type(u,set) then 
  return `and`(seq(`is_present/csc`(A)(v),v in [op(u)]));
 elif type(u,`*`) then 
  v := remove(type,[op(u)],rational);
  if nops(v) = 1 then 
   return `is_present/csc`(A)(v[1]);
  else
   return false;
  fi;
 elif type(u,specfunc(list(nonnegint),x)) then
  for ia in [op(u)] do
   if nops(ia) <> 2 then error("Invalid arguments"); fi;
   i,a := op(ia);
   if not(member(a,A) and i < a) then 
    return false;
   fi;
  od:
  v := [op(u)];
  w := sort([op({op(u)})],`cmp/csc`);
  if v <> w then return false; fi; 
  return true;
 else
  error("Invalid arguments");
 fi;
end:

# `ia_split/csc` converts x([i,a]) or [i,a] to [i,a] (provided that 
# i and a are natural numbers with 0 <= i <a) and generates an
# error if provided with an argument that is not of this form.

`ia_split/csc` := proc(ia)
 local i,a;

 if type(ia,specfunc(list(nonnegint),x)) and nops(ia) = 1 and nops(op(ia)) = 2 then 
  i,a := op(op(ia));
 elif type(ia,list(nonnegint)) and nops(ia) = 2 then 
  i,a := op(ia);
 else
  error("Invalid arguments");
 fi;
 return [i,a];
end:

# `phi_split/csc`(A) requires A to be a nonempty list of natural numbers
# It returns [a,A1], where a is the smallest element in A, and A1
# is the list of all the other elements.

`phi_split/csc` := proc(A) 
 local a,A1;
 if not type(A,list(nonnegint)) then error("Invalid arguments"); fi;
 if nops(A) = 0 then error("Invalid arguments"); fi;

 a := min(op(A));
 A1 := {op(A)} minus {a};
 A1 := sort([op(A1)]);
 return [a,A1];
end:

# In alpha_A(S) we have elements x([i,a]) for all [i,a] with
# 0 <= i < a and a in A; we call these pregenerators.  Some of the
# pregenerators are generators and the others are zero.  The
# function `is_pregenerator/csc`(A)(u) returns true if u is
# a pregenerator.  Here u can be an element x([i,a]) or it can
# be the corresponding pair [i,a].  Similarly,
# `is_generator/csc`(A)(u) returns true if u is a generator.

`is_pregenerator/csc` := (A) -> proc(ia)
 local i,a;

 i,a := op(`ia_split/csc`(ia));
 return evalb(0 <= i and i < a and member(a,A));
end:

`is_generator/csc` := (A) -> proc(ia)
 local i,a;

 i,a := op(`ia_split/csc`(ia));
 if not(member(a,A)) then return false; fi;
 if i < max(0,op(select(b -> b < a,A))) then return false; fi;
 return true;
end:

# `is_basis_element/csc`(A)(u) returns true if u is a basis
# element for alpha_A(S), i.e. a sorted product of distinct
# generators.

`is_basis_element/csc` := (A) -> proc(u::specfunc(list(nonnegint),x))
 if not(`is_present/csc`(A)(u)) then return false; fi;

 return `and`(op(map(`is_generator/csc`(A),[op(u)])));
end:

# The following functions return lists of pregenerators, generators
# and basis elements for alpha_A(S).

`list_pregenerators/csc` := proc(A)
 option remember;
 local i,a;
 [seq(seq(x([i,a]),i=0..a-1),a in sort([op(A)]))];
end: 

`list_generators/csc` := proc(A)
 option remember;
 local i0,L,a,i;
 i0 := 0;
 L := NULL;
 for a in sort([op(A)]) do 
  L := L,seq(x([i,a]),i=i0..a-1);
  i0 := a;
 od:
 return [L];
end:

`list_basis/csc` := proc(A)
 option remember;
 local G;
 G := map(op,`list_generators/csc`(A));
 return map(u -> x(op(u)),combinat[powerset](G));
end:

# For A <> {} with minimum element a, the ring spectrum phi_A(S)
# is an exterior algebra over L_{K(a)}S with generators of the form
# x([i,a]) for certain pairs [i,a].  The function
# `is_phi_generator/csc`(A)(u) returns true if u is one of these
# generators.  Here again u can be an element x([i,a]) or it can
# be the corresponding pair [i,a].

`is_phi_generator/csc` := (A) -> proc(jb)
 local a,A1,j,b;
 a,A1 := op(`phi_split/csc`(A));
 j,b := op(`ia_split/csc`(jb));
 return evalb(`is_generator/csc`(A1)(jb) and j >= a);
end:

# `is_phi_basis_element/csc`(A)(u) returns true if u is a basis
# element for phi_A(S), i.e. a sorted product of distinct
# generators.

`is_phi_basis_element/csc` := (A) -> proc(u::specfunc(list(nonnegint),x))
 local a,A1,j,b;
 a,A1 := op(`phi_split/csc`(A));
 return evalb(`is_basis_element/csc`(A1)(u) and `height/csc`(u) >= a);
end:

# The following functions return lists of generators
# and basis elements for phi_A(S).

`list_phi_generators/csc` := proc(A)
 option remember;
 local a,A1,i,i0,L,a1;

 a,A1 := op(`phi_split/csc`(A));
 i0 := a;
 L := NULL;
 for a1 in sort([op(A1)]) do 
  L := L,seq(x([i,a1]),i=i0..a1-1);
  i0 := a1;
 od:
 return [L];  
end:

`list_phi_basis/csc` := proc(A)
 option remember;
 local G;
 G := map(op,`list_phi_generators/csc`(A));
 return map(u -> x(op(u)),combinat[powerset](G));
end:

# In the associated graded object for our filtration of L_nS, the term
# z(U) can be multiplied by monomials in a certain list of generators.
# The function below returns this list.

`is_R_generator/csc` := (U::list(nonnegint)) -> proc(ia)
 local i,j,a;
 if nops(U) = 0 then error("Invalid arguments"); fi;
 if nops(U) = 1 then return false; fi;
 i,a := op(`ia_split/csc`(ia));
 for j from 2 to nops(U) do 
  if a = U[j] then 
   return evalb(U[j-1] < i and i < U[j]);
  fi;
 od:
 return false;
end:

`list_R_generators/csc` := proc(U::list(nonnegint)) 
 option remember;
 local i,j;
 if nops(U) = 0 then error("Invalid arguments"); fi;
 return [seq(seq(x([i,U[j]]),i=U[j-1]+1..U[j]-1),j=2..nops(U))];
end:

`list_R_basis/csc` := proc(U)
 option remember;
 local G;
 G := map(op,`list_R_generators/csc`(U));
 return map(u -> x(op(u)),combinat[powerset](G));
end:

# This function gives a basis for the associated graded object of L_nS
`list_gr_basis/csc` := proc(n)
 option remember;
 local UU,i,L,U,v;
 UU := combinat[powerset]([seq(i,i=0..n-1)]);
 UU := map(U -> [op(U),n],UU);
 L := NULL;
 for U in UU do
  for v in `list_R_basis/csc`(U) do
   L := L,zx(U,op(v));
  od:
 od:
 return [L];
end:

# This function gives a basis for the associated graded object
# corresponding to a certain filtration of the zero spectrum.
# It is therefore the E_1 page of a spectral sequence converging
# to zero.
`list_grz_basis/csc` := proc(n)
 local P,i,A;
 P := combinat[powerset]([seq(i,i=0..n)]);
 P := select(A -> nops(A) > 0,P);
 [op(`list_gr_basis/csc`(n)),
  seq(op(map(u -> ex(A,op(u)),`list_phi_basis/csc`(A))),A in P)];
end:

# This function expects t0 to be a monomial in the variables x([i,q]),
# possibly multiplied by a term e(A) or z(U), which will be discarded.
# It returns [P,Q,R,S], where P,Q,R,S are sorted lists such that
# {0,..,n} is the disjoint union of the corresponding sets.  The
# details are discussed in a separate LaTeX document.  This all feeds
# into th analysis of the spectral sequence corresponding to our
# filtration of 0.
`PQRS/csc` := (n) -> proc(t0)
 local t,u,v,P,Q,R,S,i,j,a;
 if type(t0,specfunc(list(nonnegint),x)) then 
  t := t0;
 elif type(t0,specfunc(list(nonnegint),zx)) then 
  t := x(op(2..-1,t0));
 elif type(t0,specfunc(list(nonnegint),ex)) then 
  t := x(op(2..-1,t0));
 else
  error("Invalid arguments");
 fi;
 u := map(ia -> ia[2],[op(t)]);
 v := [seq(min(map(ia -> ia[1],select(ia -> ia[2] = a,[op(t)]))),a in u),n];
 P := [seq(i,i=0..v[1])];
 Q := [seq(seq(i,i=v[j]+1..u[j]-1),j=1..nops(u))];
 R := [seq(seq(i,i=u[j]+1..v[j+1]),j=1..nops(u))];
 S := u;
 Q := sort([op({op(Q)})]);
 R := sort([op({op(R)})]);
 S := sort([op({op(S)})]);
 return [P,Q,R,S];
end:

# This calculates what we conjecture to be the differential in the
# spectral sequence mentioned above.  It returns a table indexed
# by 1,..,n+1, where d[r] is itself a table giving the effect of
# the r'th differential on those basis elements that have survived
# to the r'th page and have still not been hit.  As the spectral
# sequence converges to zero, every initial basis element should
# appear precisely once as an index or entry for one of the tables
# d[r].  There should probably be some +/- signs but we have not
# attempted to deal with that.
`diff_grz/csc` := proc(n)
 local d,r,B,u,v,i,j,k,du,U,A,P,Q,R,S,J;

 d := table():
 for r from 1 to n+1 do d[r] := table(): od:
 
 B := `list_grz_basis/csc`(n);
 for u in B do 
  if type(u,specfunc(list(nonnegint),zx)) then
   U := op(1,u);
   k := nops(U);
   v := [seq([U[i],U[i+1]],i=1..k-1),op(2..-1,u)];
   v := sort(v,`cmp/csc`);
   du := ex(U,op(v));
   d[k][u] := du;
  else
   A := op(1,u);
   P,Q,R,S := op(`PQRS/csc`(n)(u));
   j := max(op(P),op(R));
   if not(member(j,A)) then 
    d[1][u] := ex(sort([j,op(A)]),op(2..-1,u));
   fi;
  fi:
 od:

 return eval(d);
end:

######################################################################

`chart/csc` := proc(N0 := N)
 local i,j;
 display(
  seq(line([-0.5,-j],[j+0.5,1],colour="Olive"),j=0..N0),
  seq(line([j+0.5,0],[j+0.5,1],colour="Olive"),j=0..N0-1),
  line([-0.5,-N0],[-0.5,0],colour="Olive"),
  seq(line([j+0.5,-N0],[N0+0.5,-j],colour="Olive"),j=0..N0-1),
  seq(textplot([j-0.5,1.4,typeset(j)],colour="Olive"),j=1..N0+1),
  textplot([-0.6,1.4,"target"],colour="Olive"),
  seq(textplot([-1.2,-j,typeset(-1-2*j)],colour="Red"),j=0..N0),
  textplot([-1.2,-N0-0.5,"dim"],colour="Red"),
  seq(textplot([i,-N0-0.5,typeset(i)],colour="Blue"),i=0..N0),
  textplot([N0/2,-N0-1,"height"],colour="Blue"),
  axes=none,scaling=constrained
 );
end:

`point_grid/csc` := proc(N0 := N)
 local i,j;
 display(seq(seq(point([i,-j],symbol=solidcircle,symbolsize=8,colour="LightGray"),j=0..N0),i=0..N0))
end:

`point/csc`:= proc(ia)
 local i,a;
 if type(ia,specfunc(list(nonnegint),x)) and nops(ia) = 1 and nops(op(ia)) = 2 then 
  i,a := op(op(ia));
 elif type(ia,list(nonnegint)) and nops(ia) = 2 then 
  i,a := op(ia);
 else
  error("Invalid arguments");
 fi;

 return(point([i,i-a+1],args[2..-1]));
end:

`bpoint/csc` := (ia) -> `point/csc`(ia,symbol=solidcircle,symbolsize=7,colour="LightGray"):

`gpoint/csc` := (ia) -> `point/csc`(ia,symbol=solidcircle,symbolsize=10,colour="Black"):

`opoint/csc` := (ia) -> `point/csc`(ia,symbol=circle,symbolsize=10,colour="Orange"):

`qpoint/csc` := (ia) -> `point/csc`(ia,symbol=box,symbolsize=9,colour="Black"):

`gen_chart/csc` := proc(A,N0_)
 local N0;
 if nargs > 1 then 
  N0 := N0_;
 else
  N0 := max(2,op(A));
 fi;

 display(`chart/csc`(N0),map(`gpoint/csc`,`list_generators/csc`(A)));
end:

`pregen_chart/csc` := proc(A,N0_)
 local N0,P,G,L,u;
 if nargs > 1 then 
  N0 := N0_;
 else
  N0 := max(2,op(A));
 fi;

 P := `list_pregenerators/csc`(A);
 G := `list_generators/csc`(A);
 L := NULL;

 for u in P do 
  if member(u,G) then 
   L := L,`gpoint/csc`(u);
  else
   L := L,`opoint/csc`(u);
  fi;
 od:

 display(`chart/csc`(N0),L);
end:

`phi_gen_chart/csc` := proc(A,N0_)
 local N0;
 if nargs > 1 then 
  N0 := N0_;
 else
  N0 := max(2,op(A));
 fi;

 display(`chart/csc`(N0),map(`gpoint/csc`,`list_phi_generators/csc`(A)));
end:

`phi_pregen_chart/csc` := proc(A,N0_)
 local N0,a,A1,i,G,P,L,u;
 if nargs > 1 then 
  N0 := N0_;
 else
  N0 := max(2,op(A));
 fi;

 a,A1 := op(`phi_split/csc`(A));

 G := `list_phi_generators/csc`(A);
 P := `list_pregenerators/csc`(A1);
 L := seq(`qpoint/csc`(x([i,a])),i=0..a-1);
 
 for u in P do 
  if member(u,G) then 
   L := L,`gpoint/csc`(u);
  else
   L := L,`opoint/csc`(u);
  fi;
 od:

 display(`chart/csc`(N0),L);
end:


`plot_gr_basis/csc` := proc(n)
 local G,u,i,j;
 G := `list_gr_basis/csc`(n);
 display(
  seq(seq(point([i,-j],colour="LightGray"),j=0..n^2+1),i=0..n),
  seq(point([`filt/csc`(u),`deg/csc`(u)],symbol=solidcircle,symbolsize=10),u in G), 
  axes=none
 );
end:
