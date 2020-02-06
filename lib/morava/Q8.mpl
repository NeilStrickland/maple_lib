#@ Not autoload

with(LinearAlgebra):
with(Groebner):

Q8 := table():

Q8["element_names"] := ["1","-1","i","-i","j","-j","k","-k"];
Q8["conjugacy_classes"] := [[1],[2],[3,4],[5,6],[7,8]];
Q8["character_table"] := 
 [[1$8],
  [ 1, 1,-1,-1, 1, 1,-1,-1],
  [ 1, 1, 1, 1,-1,-1,-1,-1],
  [ 1, 1,-1,-1,-1,-1, 1, 1],
  [ 2,-2, 0, 0, 0, 0, 0, 0]];
Q8["character_names"] := [1,alpha,beta,gamma,rho];

Q8["character_relations"] := 
 [alpha^2-1,beta^2-1,gamma^2-1,alpha*beta*gamma-1,
  (alpha-1)*rho,(beta-1)*rho,(gamma-1)*rho,
  rho^2-1-alpha-beta-gamma];

Q8["euler_class"] := table([
 1 = 0,
 alpha = x,
 beta = y,
 gamma = z,
 rho = c2
]):

# Morava K-theory information from the Chern approximations paper

p := 2;
n := 3;
q := p^n;

Q8["morava_K_vars"]     := plex(v,x,y,c2);
Q8["morava_K_vars_alt"] := plex(v,c2,x,y);
 
Q8["morava_K_rels"] := [
 c2^((q^2+q)/2),
 c2^((q^2-q)/2) * x,
 c2^((q^2-q)/2) * y,
 x^2 - v*x,
 y^2 - v*y,
 x*y - v*x - v*y - c2^q,
 v - add(c2^(q^2/2 - 2^i*(q-1)),i=0..n-1)
];

Q8["morava_K_groebner"] :=
 Basis(Q8["morava_K_rels"],Q8["morava_K_vars"],characteristic=p);

Q8["morava_K_basis"] := 
 [seq(c2^i,i=0..(q^2+q)/2-1),
  seq(c2^i*x,i=0..(q^2-q)/2-1),
  seq(c2^i*y,i=0..(q^2-q)/2-1)
 ];

Q8["vec_table"] := table():
d := nops(Q8["morava_K_basis"]):
for i from 1 to d do 
 Q8["vec_table"][Q8["morava_K_basis"][i]] := [0$(i-1),1,0$(d-i)];
od:

Q8["vec"] := proc(u)
 local ub,uc;
 if u = 0 then
  return [0$d];
 elif type(u,`+`) then
  return modp(map(Q8["vec"],u),p); 
 else
  if type(u,`*`) then
   uc,ub := selectremove(type,u,integer);
  else
   ub := u;
   uc := 1;
  fi;
  return modp(uc *~ Q8["vec_table"][u],p);
 fi;
end:

Q8["morava_K_groebner_alt"] :=
 Basis(Q8["morava_K_rels"],Q8["morava_K_vars_alt"],characteristic=p);

Q8["morava_K_basis_alt"] := 
 [seq(seq(seq(x^i*y^j*c2^k,k=0..3),j=0..1),i=0..7),
  seq(seq(y^j*c2^k,k=0..3),j=2..7),
  seq(c2^k,k=4..7)
 ];