# This file is about Zagier's proof that every prime congruent to 1 mod 4
# is the sum of two squares.

# The following matrices generate a dihedral group of order 12 that
# acts on Z ^ 3 preserving the quadratic form Q

S := <<-1| 2| 0>,< 0| 1| 0>,< 1|-1| 1>>;
R := << 1| 0| 2>,< 0| 0| 1>,<-1| 1|-1>>;

Q := << 1| 0| 0>,< 0| 0| 2>,< 0| 2| 0>>;
I3 := IdentityMatrix(3);

G := [seq(seq(R ^ i . S ^ j, i = 0..5),j = 0..1)];

_ASSERT("Dihedral relations",
  Equal(S . S, I3) and Equal(R . R . R, -I3) and Equal(S . R . S, 1/R));

_ASSERT("Quadratic form relations",
  Equal(Transpose(S) . Q . S, Q) and Equal(Transpose(R) . Q . R, Q));

# The following map F gives an involution on the set X

F := proc(x)
  if (R . x)[3] > 0 then
    return R . x;
  elif ((1/R) . x)[1] > 0 then
    return (1/R) . x;
  else
    return S . x;
  fi;
end:

p := ithprime(10);

X := select(u -> type(u[3],posint),
  {seq(seq(<i,j,(p - i ^ 2)/(4 * j)>,j=1..p-1),i=1..p-1)}):

_ASSERT("F preserves X",
  evalb(map(convert,map(F,X),list) = map(convert,X,list)));

_ASSERT("F is an involution on X",
  `and`(seq(Equal(F(F(x)),x),x in X)));

_ASSERT("F has a unique fixed point on X",
  evalb(map(convert,select(x -> Equal(F(x),x),X),list) = {[1,1,(p - 1)/4]}));

fix := (T) -> subs(solve(convert(T . <x,y,z> - <x,y,z>,list),{x,y,z}),[x,y,z]);

