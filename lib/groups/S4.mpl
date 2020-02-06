#@ Not autoload

with(GroupTheory):
with(LinearAlgebra):

S4 := SymmetricGroup(4);

x2 := [[1,2]];
y2 := [[2,3]];
z2 := [[3,4]];
u2 := [[1,2],[3,4]];
v2 := [[1,3],[2,4]];
x3 := [[1,2,3]];
x4 := [[1,3,2,4]];

H[ 1] := Subgroup({},S4);
H[ 2] := Subgroup({x2},S4);
K[ 2] := Subgroup({u2},S4);
H[ 3] := Subgroup({x3},S4);
H[ 4] := Subgroup({x4},S4);
K[ 4] := Subgroup({x2,z2},S4);
L[ 4] := Subgroup({u2,v2},S4);
H[ 6] := Subgroup({x2,x3},S4);
H[ 8] := Subgroup({x2,x4},S4);
H[12] := Subgroup({u2,x3},S4);
H[24] := S4;

S4_subgroups := [H[1],H[2],K[2],H[3],H[4],K[4],L[4],H[6],H[8],H[12],H[24]]:

# Burnside matrix of numbers |Map_G(G/H_i,G/H_j)|
n := nops(S4_subgroups);
M := Matrix(n,n):
for i from 1 to n do
 for j from 1 to n do
  Hi := S4_subgroups[i];
  Zi := {op(Generators(Hi))};
  Hj := S4_subgroups[j];
  C := map(Representative,LeftCosets(Hj,S4));
  M[i,j] := nops(select(c -> `and`(op(map(x -> SubgroupMembership(c^(-1) . x . c,Hj),Zi))),C));
 od:
od:

unassign('C'):

# Skeleton of the poset of conjugacy classes of subgroups
N := {seq(i,i=1..n)};
R := select(ij -> M[ij[1],ij[2]] <> 0,{seq(seq([i,j],j=1..n),i=1..n)});

# Conjugacy classes

C[1] := ConjugacyClass([],S4);
C[2] := ConjugacyClass(x2,S4);
C[3] := ConjugacyClass(u2,S4);
C[4] := ConjugacyClass(x3,S4);
C[5] := ConjugacyClass(x4,S4);

chars := [
 [ 1, 1, 1, 1, 1],
 [ 1,-1, 1, 1,-1],
 [ 2, 0, 2,-1, 0],
 [ 3, 1,-1, 0,-1],
 [ 3,-1,-1, 0, 1]
];

char_names := [1,epsilon,sigma,rho,epsilon*rho];

char_rels := [
 epsilon^2 - 1,
 epsilon * sigma - sigma,
 sigma^2 - 1 - epsilon - sigma,
 sigma * rho - rho - epsilon * rho,
 rho^2 - 1 - sigma - rho - epsilon * rho
];

char_psi_rels := [
 psi(2,epsilon) = 1,
 psi(2,sigma) = 1 - epsilon + sigma,
 psi(3,sigma) = 1 + epsilon,
 psi(2,rho) = 1 + sigma + rho - epsilon * rho,
 psi(3,rho) = 1 + epsilon - sigma + rho
];

char_lambda_rels := [
 lambda(2,sigma) = epsilon,
 lambda(2,rho) = epsilon * rho,
 lambda(3,rho) = epsilon
];