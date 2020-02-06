# A Groebner basis is by definition a set of generators for an ideal
# I in a polynomial ring over a field k.  Given such a set, one can
# deduce a basis for the quotient ring P/I as a vector space over k.
# We call that a cobasis for I.  The function below calculates the
# cobasis, assuming that it is finite.  (It will just give an infinite
# loop if the cobasis is infinite.)

cobasis := proc(basis,vars)
 local lm,nf,L,L0,x,m,i;

 lm := map(LeadingMonomial,basis,vars);
 nf := (u) -> NormalForm(u,lm,vars);
 L := [1];
 for x in [op(vars)] do
  L0 := L;
  L := NULL;
  for m in L0 do
   i := 0;
   while nf(m*x^i) <> 0 do
    L := L,m*x^i;
    i := i+1;
   od;
  od:
  L := [L];
 od:

 return L;
end:
