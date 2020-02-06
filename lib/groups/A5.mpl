#@ Not autoload
# This is mostly superseded by alternating_five.mpl but some stuff at the end has not been transferred

with(group):

# Generators

x2 := [[1,2],[3,4]];
y2 := [[1,3],[2,4]];
z2 := [[2,3],[4,5]];
x3 := [[1,2,3]];
x5 := [[1,3,4,2,5]];
y5 := [[1,2,3,4,5]];

A5 := permgroup(5,{y2,x5});

# Subgroups, named according to their order

H[1 ] := permgroup(5,{}): 
H[2 ] := permgroup(5,{x2}):
H[3 ] := permgroup(5,{x3}):
H[4 ] := permgroup(5,{x2,y2}):
H[5 ] := permgroup(5,{x5}):
H[6 ] := permgroup(5,{z2,x3}):
H[10] := permgroup(5,{x2,x5}):
H[12] := permgroup(5,{x2,x3}):
H[60] := A5:

mp := proc()
 if nargs = 0 then
  return [];
 elif nargs = 1 then
  return args[1];
 elif nargs = 2 then
  return mulperms(args);
 else
  return mulperms(args[1],mp(args[2..-1]));
 fi;
end:

ip := invperm:
pp := proc(sigma,n)
 local rho,tau,m;
 if (n >= 0) then
  tau := sigma; m := n;
 else 
  tau := invperm(sigma);
  m := abs(n);
 fi;
 rho := [];
 while m > 0 do
  rho := mulperms(tau,rho);
  m := m-1;
 od;
 return(rho);
end:

ccl := proc(x) map(g->mulperms(mulperms(g,x),invperm(g)),elements(A5)); end:

# Conjugacy classes

C[1] := {[]}:
C[2] := ccl(x2):
C[3] := ccl(x3):
C[4] := ccl(mulperms(x5,x5)):
C[5] := ccl(x5):

tau := (1+sqrt(5))/2;

# Dodecahedron representation

Rx1 := Matrix([[ 1,0,0],[0, 1,0],[0,0, 1]]):
Rx2 := Matrix([[ 1,0,0],[0,-1,0],[0,0,-1]]):
Ry2 := Matrix([[-1,0,0],[0,-1,0],[0,0, 1]]):
Rz2 := map(rationalize,Matrix([[1/tau,-tau,-1],[-tau,-1,1/tau],[-1,1/tau,-tau]])/2):
Rx3 := Matrix([[0,1,0],[0,0,1],[1,0,0]]):
Rx5 := map(rationalize,Matrix([[1/tau,tau,-1],[-tau,1,1/tau],[1,1/tau,tau]])/2):
Ry5 := map(rationalize,Matrix([[tau,-1,-1/tau],[1,1/tau,tau],[-1/tau,-tau,1]])/2):

prels := {
 pp(x2,2),
 pp(y2,2),
 pp(z2,2),
 pp(x3,3),
 pp(x5,5),
 pp(mp(x2,y2),2),
 pp(mp(x2,mp(y2,z2)),3),
 pp(mp(mp(z2,x2),mp(z2,y2)),3),
 pp(mp(x2,z2),5),
 pp(mp(y2,z2),5),
 mp(ip(x3),mp(y2,mp(z2,mp(x2,mp(z2,mp(y2,z2)))))),
 mp(ip(x5),mp(y2,mp(z2,mp(x2,y2)))),
 mp(ip(y5),mp(y2,mp(z2,mp(x2,mp(z2,x2)))))
};

mrels := [
 Rx2^2 - Rx1,
 Ry2^2 - Rx1,
 Rz2^2 - Rx1,
 Rx3^3 - Rx1,
 Rx5^5 - Rx1,
 (Rx2 . Ry2)^2 - Rx1,
 (Rx2 . Ry2 . Rz2)^3 - Rx1,
 (Rz2 . Rx2 . Rz2 . Ry2)^3 - Rx1,
 (Rx2 . Rz2)^5 - 1,
 (Ry2 . Rz2)^5 - 1,
 Rx3 - Ry2 . Rz2 . Rx2 . Rz2 . Ry2 . Rz2,
 Rx5 - Ry2 . Rz2 . Rx2 . Ry2,
 Ry5 - Ry2 . Rz2 . Rx2 . Rz2 . Rx2
]:

mrels := map(M -> map(expand,M),mrels):
rels := {op(map(expand,map(op,map(op,map(convert,mrels,listlist)))))};

ords := [1,2,4,3,6,12,5,10,60];

for n in ords do X[n] := [op(cosets(A5,H[n]))]: od:

is_fixed1 := (g,x,H) -> groupmember(mulperms(mulperms(x,g),invperm(x)),H):

is_fixed := proc(K,x,H)
 local gens,g;
 gens := op(2,K);
 for g in gens do
  if not(is_fixed1(g,x,H)) then return(false); end;
 od;
 return(true);
end:

phi := proc(i,j)
 local m,K,L,Y,y;
 K := H[i];
 L := H[j];
 Y := X[j];
 m := 0;
 for y in Y do
  if is_fixed(K,y,L) then
   m := m+1;
  fi;
 od;
 return(m); 
end:

# Matrix of |(G/H_i)^{H_j}|

M := Matrix(9,9,[seq(seq(phi(ords[i],ords[j]),j=1..9),i=1..9)]);

# Cycle types of products of 5-cycles
P := matrix(12,12,[0$144]):
for i from 1 to 12 do
 for j from 1 to 12 do
  g := mulperms(C[5][i],invperm(C[5][j])):
  P[i,j] := map(nops,g):
 od:
od:

# Edges and faces of the icosahedron
E := []:
F := []:
for i from 1 to 12 do
 for j from i+1 to 12 do
  if (P[i,j] = [3]) then
   E := [op(E),[i,j]]:
   for k from j+1 to 12 do
    if (P[i,k] = [3] and P[j,k] = [3]) then
     F := [op(F),[i,j,k]]:
    fi:
   od: 
  fi:
 od:
od:
E;
F;

# Words for all elements of A5
w[ 1] := []:
w[ 2] := [X2]:
w[ 3] := [Y2]:
w[ 4] := [Z2]:
w[ 5] := [X2,Y2]:
w[ 6] := [X2,Z2]:
w[ 7] := [Y2,Z2]:
w[ 8] := [Z2,X2]:
w[ 9] := [Z2,Y2]:
w[10] := [X2,Y2,Z2]:
w[11] := [X2,Z2,X2]:
w[12] := [X2,Z2,Y2]:
w[13] := [Y2,Z2,X2]:
w[14] := [Y2,Z2,Y2]:
w[15] := [Z2,X2,Y2]:
w[16] := [Z2,X2,Z2]:
w[17] := [Z2,Y2,Z2]:
w[18] := [X2,Y2,Z2,X2]:
w[19] := [X2,Y2,Z2,Y2]:
w[20] := [X2,Z2,X2,Y2]:
w[21] := [X2,Z2,X2,Z2]:
w[22] := [X2,Z2,Y2,Z2]:
w[23] := [Y2,Z2,X2,Y2]:
w[24] := [Y2,Z2,X2,Z2]:
w[25] := [Y2,Z2,Y2,Z2]:
w[26] := [Z2,X2,Y2,Z2]:
w[27] := [Z2,X2,Z2,X2]:
w[28] := [Z2,X2,Z2,Y2]:
w[29] := [Z2,Y2,Z2,X2]:
w[30] := [Z2,Y2,Z2,Y2]:
w[31] := [X2,Y2,Z2,X2,Z2]:
w[32] := [X2,Y2,Z2,Y2,Z2]:
w[33] := [X2,Z2,X2,Z2,X2]:
w[34] := [X2,Z2,X2,Z2,Y2]:
w[35] := [X2,Z2,Y2,Z2,X2]:
w[36] := [X2,Z2,Y2,Z2,Y2]:
w[37] := [Y2,Z2,X2,Z2,X2]:
w[38] := [Y2,Z2,X2,Z2,Y2]:
w[39] := [Y2,Z2,Y2,Z2,X2]:
w[40] := [Y2,Z2,Y2,Z2,Y2]:
w[41] := [Z2,X2,Z2,X2,Y2]:
w[42] := [Z2,X2,Z2,Y2,Z2]:
w[43] := [Z2,Y2,Z2,X2,Y2]:
w[44] := [Z2,Y2,Z2,X2,Z2]:
w[45] := [X2,Y2,Z2,X2,Z2,X2]:
w[46] := [X2,Y2,Z2,X2,Z2,Y2]:
w[47] := [X2,Y2,Z2,Y2,Z2,X2]:
w[48] := [X2,Y2,Z2,Y2,Z2,Y2]:
w[49] := [X2,Z2,X2,Z2,X2,Y2]:
w[50] := [X2,Z2,X2,Z2,Y2,Z2]:
w[51] := [X2,Z2,Y2,Z2,X2,Y2]:
w[52] := [X2,Z2,Y2,Z2,X2,Z2]:
w[53] := [Y2,Z2,X2,Z2,Y2,Z2]:
w[54] := [Y2,Z2,Y2,Z2,X2,Y2]:
w[55] := [Y2,Z2,Y2,Z2,X2,Z2]:
w[56] := [Z2,X2,Z2,Y2,Z2,Y2]:
w[57] := [Z2,Y2,Z2,X2,Z2,X2]:
w[58] := [X2,Y2,Z2,Y2,Z2,X2,Y2]:
w[59] := [Z2,Y2,Z2,Y2,Z2,X2,Z2]:
w[60] := [X2,Z2,Y2,Z2,Y2,Z2,X2,Z2]:

# Rotations for all elements
Rw[1] := IdentityMatrix(3):
for i from 2 to 60 do 
 Rw[i] := map(expand,`.`(op(subs({X2=Rx2,Y2=Ry2,Z2=Rz2},w[i]))));
od:

# Permutations for all elements
Sw[1] := []:
for i from 2 to 60 do 
 Sw[i] := mp(op(subs({X2=x2,Y2=y2,Z2=z2},w[i])));
od:

# Vertices of the icosahedron 

V[ 1] := <   0,   1, tau>: 
V[ 2] := <   0,  -1, tau>:
V[ 3] := <   0,   1,-tau>:
V[ 4] := <   0,  -1,-tau>: 
V[ 5] := <   1, tau,   0>: 
V[ 6] := <  -1, tau,   0>:
V[ 7] := <   1,-tau,   0>:
V[ 8] := <  -1,-tau,   0>:
V[ 9] := < tau,   0,   1>: 
V[10] := < tau,   0,  -1>:
V[11] := <-tau,   0,   1>:
V[12] := <-tau,   0,  -1>:  

for i from 1 to 12 do 
 U := V[i];
 VV[U[1],U[2],U[3]] := i;
od:

Vix := proc(T)
 local T1;
 T1 := map(expand,T);
 return(VV[T1[1],T1[2],T1[3]]);
end:

# Permutation action on vertices

Px2 := convert([seq(Vix(Rx2 . V[i]),i=1..12)],disjcyc);
Py2 := convert([seq(Vix(Ry2 . V[i]),i=1..12)],disjcyc);
Pz2 := convert([seq(Vix(Rz2 . V[i]),i=1..12)],disjcyc);
Px3 := convert([seq(Vix(Rx3 . V[i]),i=1..12)],disjcyc);
Px5 := convert([seq(Vix(Rx5 . V[i]),i=1..12)],disjcyc);
