#@ Not autoload

# This file relates to the cubic with equation x[1]^3 + x[2]^3 + x[3]^3 = nu * x[1] * x[2] * x[3]

om := exp( 2*Pi*I/3);
ob := exp(-2*Pi*I/3);
R := [1,om,ob];

# The group G acts on affine 3-space, preserving the above cubic.
# The quotient G/Z acts on the projective plane, preserving our cubic curve

id := IdentityMatrix(3);
rho := <<0|0|1>,<1|0|0>,<0|1|0>>:
zeta := DiagonalMatrix([1,om,ob]):

Z := [id,om * id, ob * id];
T := [seq(seq(DiagonalMatrix(rationalize(expand([om^i,om^j,om^(-i-j)]))),j=0..2),i=0..2)]:
S := map(perm_matrix,combinat[permute](3)):
G := [seq(seq(t.s,t in T),s in S)]:

# rho and zeta commute in G/Z 
for i from -1 to 1 do 
 for j from -1 to 1 do 
  g[i,j] := map(rationalize,rho^i . zeta^j);
 od;
od:

# We now define matrices U[i,j] = <e[i,j] | u[i,j] | v[i,j]>
# Each e[i,j] generates a 1-dimensional summand in affine 3-space
# On the complement of the locus where nu = 3 = 0, each pair 
U[0,0] := <<1|1|nu>,<-1|-nu-1|3>,<0|3|nu>>;
for i from -1 to 1 do
 for j from -1 to 1 do
  U[i,j] := map(expand,g[i,j] . U[0,0]);
  e[i,j] := convert(Column(U[i,j],1),list);
  u[i,j] := convert(Column(U[i,j],2),list);
  v[i,j] := convert(Column(U[i,j],3),list);
 od:
od:

