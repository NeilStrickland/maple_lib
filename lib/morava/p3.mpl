#@ Not autoload

p := 3;   # the ambient prime
n := 2;   # height
d := 243; # degree of approximate FGL 

# find the FGL
T := make_fgl_Morava(p,n,d):
F_E := eval(T["sum"]);
F_K := eval(T["sum0"]);

# Generators and relations for O_Y, where Y is the scheme defined in 
# Section sec_Y.  Note that the quantities called a,b and c in the 
# main document are aa,bb and cc here.  Note also that we build up 
# the relations in two stages: we first do a preliminary version
# without the condition \psi^4(D) = D, then we add that condition
# as a second step.

vars_Y := plex(aa,bb,cc,c[1],c[3],c[2]):
rels_Y := {
 c[1] - (aa+bb+cc),
 c[2] - (aa*bb+bb*cc+cc*aa),
 c[3] - (aa*bb*cc),
 c[1]^9,c[2]^9,c[3]^9,
 aa + F_K(bb,cc)
}:
basis_Y := Basis(rels_Y,vars_Y,characteristic=p); # Preliminary version

# aa4 = [4](aa), bb4 = [4](bb), cc4 = [4](cc)
aa4 := mods(NormalForm(F_K(aa,aa^(p^n)),basis_Y,vars_Y,characteristic=p),p);
bb4 := mods(NormalForm(F_K(bb,bb^(p^n)),basis_Y,vars_Y,characteristic=p),p);
cc4 := mods(NormalForm(F_K(cc,cc^(p^n)),basis_Y,vars_Y,characteristic=p),p);

# To impose the condition psi^4(D) = D, the elementary symmetric functions
# in aa4, bb4, cc4 must be the same as for aa, bb and cc.
rels_Y := {
 op(basis_Y),
 c[1] - (aa4+bb4+cc4),
 c[2] - (aa4*bb4+bb4*cc4+cc4*aa4),
 c[3] - (aa4*bb4*cc4)
}:

basis_Y := Basis(rels_Y,vars_Y,characteristic=p);
NF_Y := (u) -> mods(NormalForm(u,basis_Y,vars_Y,characteristic=p),p):

# The above Groebner basis includes the variables aa, bb and cc which were
# adjoined to O_Y for convenience.  Because these were placed first in a pure
# lexicographic order, we can obtaina Groebner basis for O_Y itself by simply
# omitting any relations that involve aa, bb or cc.
vars_Y1 := plex(c[1],c[3],c[2]):
basis_Y1 := remove(has,basis_Y,{aa,bb,cc});
cobasis_Y1 := cobasis(basis_Y1,vars_Y1);
nops(cobasis_Y1);

# Definitions of some auxiliary elements

# gamma is used by default for the Euler-Mascheroni constant; we need
# to cancel this.
unprotect('gamma'):

alpha := c[3]^3-c[2]^3*c[3];
beta  := 1 + c[2]^4;
gamma := c[2]^3*c[3]^3;
dd := NF_Y(F_K(aa,-bb));
mm := aa^5*bb^5 + bb^5*cc^5 + cc^5*aa^5;
uu := c[2] + c[2]^2*c[3]^2;
for i from 0 to 18 do 
 s[i] := NF_Y(aa^i + bb^i + cc^i);
od:

# Formulae in the Claim labelled claim-A
_ASSERT(
 map(NF_Y,{
  c[1]+c[3]^3,
  c[1]^3
 }) = {0},
 "claim-A"
):

# Formulae in the Claim labelled claim-B and its proof
_ASSERT(
 map(NF_Y,{
  c[2]^6,
  s[1]-c[1],
  s[2]-(c[1]^2+c[2]),
  s[3],
  s[4]-c[1]*s[3]+c[2]*s[2]-c[3]*s[1],
  s[12]-s[4]^3,
  aa^27,bb^27,cc^27,
  aa4 - (aa + aa^9),
  bb4 - (bb + bb^9),
  cc4 - (cc + cc^9),
  aa4^4 - (aa^4 + aa^12),
  bb4^4 - (bb^4 + bb^12),
  cc4^4 - (cc^4 + cc^12)
 }) = {0},
 "claim-B"
):

# Formulae in the Claim labelled claim-C and its proof
_ASSERT(
 map(NF_Y,{
  c[1]*c[2]                                   - c[2]^3 * (-c[2]*c[3]),
  c[3]^3*c[2]                                 - c[2]^3 * ( c[2]*c[3]),
  aa^3-c[1]*aa^2+c[2]*aa-c[3],
  aa^9 - c[3]^3                               - c[2]^3 * (-aa^3),
  aa^9 + c[1]                                 - c[2]^3 * (-aa^3),
  aa4 - (aa - c[1])                           - c[2]^3 * (-aa^3),
  aa4*bb4*cc4 - (aa-c[1])*(bb-c[1])*(cc-c[1]) - c[2]^3*(-c[2]*c[3]),
  aa4*bb4*cc4 - (c[3]-c[2]*c[1])              - c[2]^3*(-c[2]*c[3]),
  aa4*bb4*cc4 - c[3]
 }) = {0},
 "claim-C"
):

# Formulae in Corollary cor-C and its proof
_ASSERT(
 map(NF_Y,{
  c[3]^6*c[2]^2,
  c[3]^3*c[2]^4,
  c[3]^3*c[2]-c[2]^3*(c[2]*c[3]),
  c[2]^6
 }) = {0},
 "cor-C"
):

# Formulae in the Claim labelled claim-D and its proof
_ASSERT(
 map(NF_Y,{
  c[3]^3*c[2]-c[3]*c[2]^4,
  aa^3-c[1]*aa^2+c[2]*aa-c[3],
  aa^9+c[2]^3*aa^3-c[3]^3,
  aa^9+c[2]^3*aa^3-c[3]^3,
  aa^9-c[2]^3*c[3]^3*aa^2-c[2]^4*aa+c[2]^3*c[3]-c[3]^3,
  F_K(aa,aa^9) - (aa+aa^9),
  F_K(aa,aa^9) - (alpha + beta*aa + gamma*aa^2),
  alpha*beta - alpha,
  beta*gamma - gamma,
  gamma^2,
  alpha^3,
  alpha^2*gamma,
  beta^3 - 1,
  alpha^2*c[1],
  alpha*gamma*c[1]*c[2],
  gamma*c[1]*c[3],
  aa4*bb4*cc4 -
   ((alpha+beta*aa+gamma*aa^2) *
    (alpha+beta*bb+gamma*bb^2) *
    (alpha+beta*cc+gamma*cc^2)),
  aa4*bb4*cc4 - (alpha^2*c[1]+alpha*c[2]+alpha*gama*c[1]*c[2]+c[3]+gamma*c[1]*c[3]),
  alpha^2*c[1],
  -(c[3]^3-c[2]^3*c[3])^2*c[3]^3,
  alpha*gamma*c[1]*c[2],
  gamma*c[1]*c[3],
  aa4*bb4*cc4 - (c[3]+alpha*c[2]),
  alpha*c[2]
 }) = {0},
 "claim-D"
):

# Formulae in the Claim labelled claim-E and its proof
_ASSERT(
 map(NF_Y,{
  c[3]^6-c[2]^5,
  aa4^2 - (aa^2-aa^10+aa^18),
  aa4^2+bb4^2+cc4^2 - (s[2]-s[10]+s[18]),
  s[18],
  s[10],
  aa^9-(alpha+(beta-1)*aa+gamma*aa^2),
  gamma,
  aa^10 - (alpha*aa + (beta-1)*aa^2),
  s[10] - (alpha*s[1] + (beta-1)*s[2]),
  s[10] - (-c[3]^6+c[2]^5)
 }) = {0},
 "claim-E"
):

# Groebner basis for O_Y
_ASSERT(
 mods(basis_Y1,3) = [c[2]^6,c[3]^3*c[2]-c[3]*c[2]^4,c[3]^6-c[2]^5,c[1]+c[3]^3],
 "prop-Y"
):

# Formulae in the Claim labelled claim-F and its proof
_ASSERT(
 map(NF_Y,{
  dd - (aa-bb+aa^6*bb^3-aa^3*bb^6),
  aa^9+c[2]^3*aa^3-c[3]^3,
  bb^9+c[2]^3*bb^3-c[3]^3,
  (c[2]^3)^2,
  c[2]^3*c[3]^3,
  (c[3]^3)^2-c[2]^5,
  aa^9*bb^9 - c[2]^5,
  aa^3-(-c[3]^3*aa^2-c[2]*aa+c[3]),
  aa^12 * bb^9  - c[2]^5*c[3],
  aa^9  * bb^12 - c[2]^5*c[3],
  aa^9 * bb^9 * (bb^3 - aa^3)
 }) = {0},
 "claim-F"
):

# Formulae in the Claim labelled claim-G and its proof
_ASSERT(
 map(NF_Y,{
  c[2] - (-(aa^2+aa*bb+bb^2)-(aa+bb)*c[3]^3),
  c[3] - (-aa*bb*(aa+bb)-aa*bb*c[3]^3),
  aa+bb - (-c[3]^3-cc),
  aa*bb - (cc^2+c[3]^3*cc+c[2]),
  aa^9*bb^9 - c[2]^5,
  (aa-bb)^2 - (-c[2]-(aa+bb)*c[3]^3),
  aa^3-bb^3 - (-c[2]*(aa-bb)-c[3]^3*(aa^2-bb^2)),
  aa^9-bb^9 - c[2]^4*(aa-bb),
  aa+bb+cc-c[1],
  aa+bb+cc+c[3]^3,
  c[2] - (-(aa^2+aa*bb+bb^2)-(aa+bb)*c[3]^3),
  c[3] - (-aa*bb*(aa+bb)-aa*bb*c[3]^3),
  cc^2 + cc * c[3]^3 + c[2] - aa * bb,
  - aa^18 - aa^9 * bb^9 - bb^18,
  aa^18 + bb^18 + c[2]^5
 }) = {0},
 "claim-G"
):

# Formulae in the Claim labelled claim-H
_ASSERT(
 map(NF_Y,{
  s[ 1] - (-c[3]^3),
  s[ 2] - (c[2]+c[2]^5),
  s[ 3],
  s[ 4] - (-c[3]^4-c[2]^2),
  s[ 5] - (c[3]*c[2]),
  s[ 6] - (c[2]^3),
  s[ 7] - (-c[3]^5+c[3]*c[2]^2),
  s[ 8] - (-c[2]^4+c[3]^2*c[2]),
  seq(s[i],i=9..18)
 }) = {0},
 "claim-H"
);

# Formula in the Claim labelled claim-I
_ASSERT(
 NF_Y(
  dd - (aa-bb)*(1-c[3]^2*c[2]+c[3]^2*c[2]^5-c[2]^4-(c[3]*c[2]^2-c[3]^5)*cc-c[2]^3*cc^2)
 ) = 0,
 "claim-I"
);

# Formulae in the Claim labelled claim-J and its proof
_ASSERT(
 map(NF_Y,{
 dd^3 - (aa-bb)^3,
 dd^3 - (-c[3]^3*(aa^2-bb^2)-c[2]*(aa-bb)),
 c[2]^4*dd - c[2]^4*(aa-bb)*(1-c[2]*c[3]^2),
 c[2]^4*dd^4,
 c[2]^4*(aa-bb)^4,
 c[2]^5*dd - c[2]^5*(aa-bb),
 c[2]^5*dd^2,
 dd-(aa-bb) - aa^3*bb^3*(aa^3-bb^3),
 aa^9*bb^9*(aa^9-bb^9),
 c[2]^4*c[3]^3,
 aa^3-bb^3+c[3]^3*(aa^2-bb^2)+c[2]*(aa-bb),
 c[2]^4*(aa^3-bb^3)+c[2]^5*(aa-bb),
 (c[3]^3)                      * c[2]^5,
 (c[2])                        * c[2]^5,
 (aa*bb-cc^2)                  * c[2]^5,
 ((aa*bb)^3-cc^6)              * c[2]^5,
 (cc^3-c[3])                   * c[2]^5,
 (cc^6-c[3]^2)                 * c[2]^5,
 c[2]^4*(aa^3-bb^3)*(aa*bb)^3 + c[2]^5*c[3]^2*(aa-bb),
 (aa-bb)^2+c[2]+(aa+bb)*c[3]^3
 }) = {0},
 "claim-J"
);

points_E := map(NF_Y,[
 F_K(aa,-bb), F_K(bb,-cc), F_K(cc,-aa),
 F_K(bb,-aa), F_K(cc,-bb), F_K(aa,-cc)
]):
f_E := NF_Y(expand(mul(t - u,u in points_E)));

vars_Z := plex(aa,bb,cc,c[1],z,c[3],c[2]):

az := rem(NF_Y(F_K(aa,z)),z^9,z);
bz := rem(NF_Y(F_K(bb,z)),z^9,z);
cz := rem(NF_Y(F_K(cc,z)),z^9,z);

rels_Z := {
 op(basis_Y),
 z^9,
 c[1] - (az+bz+cz),
 c[2] - (az*bz+bz*cz+cz*az),
 c[3] - (az*bz*cz)
}:
basis_Z := Basis(rels_Z,vars_Z,characteristic=p):
NF_Z := (u) -> mods(NormalForm(u,basis_Z,vars_Z,characteristic=p),p):

vars_Z1 := plex(c[1],z,c[3],c[2]):
basis_Z1 := remove(has,basis_Z,{aa,bb,cc});
cobasis_Z1 := cobasis(basis_Z1,vars_Z1);

# Formulae in the Claim labelled claim-K and its proof 
_ASSERT(
 map(NF_Z,{
  t^3 * f_E - (t^9 - c[2]^5*t^7 + c[2]^3 * t^3),
  F_K(aa,-bb) - dd,
  F_K(bb,-aa) - (-dd),
  F_K(aa,-cc) - (-dd+aa^9),
  F_K(cc,-aa) - ( dd-aa^9),
  F_K(cc,-bb) - (-dd-bb^9),
  F_K(bb,-cc) - ( dd+bb^9),
  f_E - (t^2-dd^2)*(t^2-(dd-aa^9)^2)*(t^2-(dd+bb^9)^2),
  (dd-aa^9)^2*(dd+bb^9)^2 - dd^4,
  coeff(f_E,t,4) - (-dd^2-(dd-aa^9)^2-(dd+bb^9)^2),
  coeff(f_E,t,4) - (-c[2]^4*(aa-bb)*dd+c[2]^5),
  c[2]^4*dd-c[2]^4*(aa-bb)*(1-c[2]*c[3]^2),
  (aa-bb)^2+c[2]+(aa+bb)*c[3]^3,
  coeff(f_E,t,4) + c[2]^5,
  coeff(f_E,t,2) - (dd^2*(dd-aa^9)^2+dd^2*(dd+bb^9)^2+(dd-aa^9)^2*(dd+bb^9)^2),
  coeff(f_E,t,2),
  coeff(f_E,t,0) + dd^6
 }) = {0},
 "claim-K"
);

# Formulae in the Claim labelled claim-L and its proof 
_ASSERT(
 map(NF_Z,{
  z^9,
  z^3+(c[2]+c[2]^2*c[3]^2)*z,
  (c[3]^3-c[3]*c[2]^3)*z,
  az - z - aa*(1 - z^3*aa^5 - z^6*aa^2),
  (aa-z)*(bb-z)*(cc-z) -
   c[3]*(1-z^3*aa^5-z^6*aa^2)*
        (1-z^3*bb^5-z^6*bb^2)*
        (1-z^3*cc^5-z^6*cc^2),
  c[2]^3*z^3,
  c[3]-c[2]*z+c[1]*z^2-z^3-(c[3]-c[3]*s[5]*z^3-c[3]*s[2]*z^6-c[3]*mm*z^6),
  s[5]-c[3]*c[2],
  c[2]*z+z^3*(1-c[3]^2*c[2]),
  c[3]^4*c[2]^2*z^3,
  c[3]^2*c[2]^5*z^3,
  (c[2]+c[3]^2*c[2]^2)*z+z^3,
  az^2 - (aa^2-z*aa+z^2+z^3*aa^7+z^4*aa^6+z^6*(aa^12+aa^4)+z^7*aa^3),
  az^2 + bz^2 + cz^2 - (s[2]-z*s[1]+z^3*s[7]+z^6*(s[12]+s[4])+z^7*s[3]),
  -z*s[1]+z^3*s[7]+z^4*s[6]+z^6*(s[12]+s[4])+z^7*s[3],
  -z*s[1]+z^3*s[7]+z^7*s[3],
  s[1]+c[3]^3,
  s[3],
  s[7]-(-c[3]^5+c[3]*c[2]^2),
  z^3+(c[3]^2*c[2]^2+c[2])*z,
  (c[3]^3-c[3]*c[2]^3)*z
 }) = {0},
 "claim-L"
):

vars_ZW := plex(aa,bb,cc,c[1],z,w,c[3],c[2]):
rels_ZW := {
 op(basis_Z),
 op(subs(z = w,basis_Z))
}:
basis_ZW := Basis(rels_ZW,vars_ZW,characteristic=p):
NF_ZW := (u) -> mods(NormalForm(u,basis_ZW,vars_ZW,characteristic=p),p):

vars_ZW1 := plex(c[1],z,w,c[3],c[2]):
basis_ZW1 := remove(has,basis_ZW,{aa,bb,cc});
cobasis_ZW1 := cobasis(basis_ZW1,vars_ZW1);

points_ZW := map(NF_ZW,[
 0,z,-z,w,-w,F_K(z,w),F_K(z,-w),F_K(-z,w),F_K(-z,-w)
]):

f_ZW := t^9 + uu^3*z^2*w^2*t^7 - (uu*z^2*w^2+uu^2*(z^2+w^2))*t^3;

# Formulae in the Claim labelled claim-M and its proof 

### UNFINISHED
_ASSERT(
 map(NF_ZW,{
  f_ZW - mul(t-m,m in points_ZW),
  z^3 + uu*z,
  z^9,
  uu^4*z,
  F_K(z, w) - (z+w)*(1+uu^3*z*w),
  F_K(z,-w) - (z-w)*(1-uu^3*z*w),
  F_K(z, w)^2 - (z+w)^2 - uu^3*z^2*w^2,
  F_K(z,-w)^2 - (z-w)^2 - uu^3*z^2*w^2,
  uu      * z^2*w^2*uu^3,
  z       * z^2*w^2*uu^3,
  w       * z^2*w^2*uu^3
 }) = {0},
 "claim-M"
):

vars_C := vars_ZW:
rels_C := {op(basis_ZW),coeffs(mods(expand(f_ZW - t^3*f_E),p),t)}:
basis_C := Basis(rels_C,vars_C,characteristic=p);
NF_C := (u) -> mods(NormalForm(u,basis_C,vars_C,characteristic=p),p);

vars_C1 := plex(c[1],z,w,c[3],c[2]);
basis_C1 := mods(remove(has,basis_C,{aa,bb,cc}),p);
cobasis_C1 := cobasis(basis_C1,vars_C1);

_ASSERT(nops(cobasis_C1) = 108,"C(K,G) has rank 108");

rels_C1_alt := [
c[3]^6-c[2]^5,
c[3]^3*c[2]-c[3]*c[2]^4,
c[2]^6,
c[3]^3*z-c[3]*c[2]^3*z,
c[2]^4*z,
z^3+c[2]*z+c[3]^2*c[2]^2*z,
c[3]^3*w-c[3]*c[2]^3*w,
c[2]^4*w,
w^3+c[2]*w+c[3]^2*c[2]^2*w,
uu*z^2*w^2+uu^3+uu^2*(z^2+w^2)
]:

map(NF_C,rels_C1_alt);

cza[1] := mods(expand(rem(expand(a + F_E(a,z) + F_E(a,-z)),z^8+3,z)),p^6):
cza[2] := mods(expand(rem(expand(a * F_E(a,z) + a * F_E(a,-z) + F_E(a,z)*F_E(a,-z)),z^8+3,z)),p^6):
cza[3] := mods(expand(rem(expand(a * F_E(a,z) * F_E(a,-z)),z^8+3,z)),p^6):

# Series for [3](x) in terms of y = x(x+_Fz)(x-_Fz) assuming <3>(z)=0
nn := (z,y) -> 
   z^6*y+
28    *y^3-
27*z^2*y^5-
39*z^4*y^7+
 9*z^2*y^13-
27    *y^19+
27*z^4*y^23-
 9*z^6*y^25+
27*z^4*y^31-
27*z^6*y^49-
27*z^6*y^73;

# Series for c_2({x,x+_Fz,x-_Fz}) in terms of y = x(x+_Fz)(x-_Fz) assuming <3>(z)=0
mm := (z,y) -> 
-z^2+
38*z^4*y^2+
35*z^6*y^4+
27    *y^6-
21*z^2*y^8-
 6*z^4*y^10+
 9*z^6*y^12+
18*z^2*y^16+
18*z^6*y^20+
 9    *y^22-
24*z^2*y^24-
15*z^4*y^26+
39*z^6*y^28+
36*z^2*y^32-
 9*z^4*y^34-
27*z^6*y^36+
27*z^2*y^40-
27*z^4*y^42+
27*z^6*y^44+
27    *y^46+
18*z^2*y^48-
36*z^4*y^50+
18*z^6*y^52-
27*z^2*y^56+
27*z^4*y^58;

_ASSERT(
 mods(expand(rem(T["p_series"](a)-nn(z,cza[3]),z^8+3,z)),p^4) = 0,
 "Defining property of nn"
);

# The assertion below actually works mod (p^4,p^3z^6) but for simplicity
# we just check mod p^3.
_ASSERT(
 mods(expand(rem(cza[2]-mm(z,cza[3]),z^8+3,z)),p^3) = 0,
 "Defining property of nn"
);

mu := 1+3^8+3^16+3^18;

# 3-adic square root of -2
rr := 5-3^3+3^5-3^6-3^7+3^11+3^12-3^14-3^15-3^17-3^18+3^20-3^22-3^23-3^24;
nu := mods((rr-2)/(3*mu),p^25);
lm := 1 + 3 * mu * nu;

_ASSERT(
 modp(rem(T["p_series"](x),x^9+3*mu*x,x),p^25) = 0,
 "Defining property of mu"
);

_ASSERT(
 modp(rr^2+2,p^25) = 0,
 "Defining property of rr = sqrt(-2)"
);

_ASSERT(
 mods(rem(rem(nn(z,y),y^3+y*z^6,y),z^8+3,z),p^4) = 0,
 "Consistency check for nn"
);

_ASSERT(
 mods(rem(rem(mm(z,y)+z^2+nu*z^4*y^2,y^3+y*z^6,y),z^8+3,z),p^4) = 0,
 "Consistency check for mm"
);

char0 := proc(t)
 local u,v;
 u := subs(LL = 1+3*MU*NU,t);
 v := 
 [rem(subs({z=0,w=0,c[2]=3*a^2,c[3]=a^3},u),a^9+3*MU*a,a),
  rem(rem(subs({w= 0,c[2]=-NU*z^4*y^2-z^2,c[3]=y},u),y^3+y*z^6,y),z^8+3*MU,z),
  rem(rem(subs({w= z,c[2]=-NU*z^4*y^2-z^2,c[3]=y},u),y^3+y*z^6,y),z^8+3*MU,z),
  rem(rem(subs({w=-z,c[2]=-NU*z^4*y^2-z^2,c[3]=y},u),y^3+y*z^6,y),z^8+3*MU,z),
  rem(rem(subs({z= 0,c[2]=-NU*w^4*y^2-w^2,c[3]=y},u),y^3+y*w^6,y),w^8+3*MU,w)
 ];
 v := simplify(subs(NU = (sqrt(-2)-2)/(3*MU),v));
 return v;
end:

char := proc(t)
 local u;
 u := char0(t);
 [seq(coeff(u[1],a,i),i=0..8),
  seq(seq(seq(coeff(coeff(u[i],y,k),z,j),k=0..2),j=0..7),i=2..4),
      seq(seq(coeff(coeff(u[5],y,k),w,j),k=0..2),j=0..7)];
end:

SS :=
 (3*MU^2*NU^2+2*MU*NU-3)/MU/((1+3*MU*NU)^3-27) * c[3]^2*(c[2]^3-27*c[3]^2) + 
 (3/MU) * c[3]^4 + 
 c[2]^2 +
 w^2*z^2 + 
 (w^2+z^2)*c[2] +
 (NU/(1+3*MU*NU)^2) * (z^2+w^2)*c[2]^2*c[3]^2;

rels_E_lift := [
 (LL+6)*c[2]^6+(-36*LL-192)*c[3]^2*c[2]^3+(3*LL*MU+18*MU)*c[2]^2+(252*LL+864)*c[3]^4,
 (-LL*MU-3*MU)*c[2]^5+(16*LL*MU+68*MU)*c[3]^2*c[2]^2+(-3*LL*MU^2-9*MU^2)*c[2]+(-32*LL-36)*c[3]^6,
 -c[2]^4*c[3]+(4*LL+24)*c[3]^3*c[2]+(36*LL*MU-27*MU)*c[3],
 z*c[3]*(-c[2]^3+(LL+6)*c[3]^2),
 w*c[3]*(-c[2]^3+(LL+6)*c[3]^2),
 z*((c[2]^4+3*MU)-(4*LL+20)/3*c[2]*c[3]^2),
 w*((c[2]^4+3*MU)-(4*LL+20)/3*c[2]*c[3]^2),
 (LL^2*(c[2]+z^2) + (LL-1)/(3*MU)*c[2]^2*c[3]^2)*z,
 (LL^2*(c[2]+w^2) + (LL-1)/(3*MU)*c[2]^2*c[3]^2)*w,
 SS
];

ss := mods(subs({MU = mu,NU = nu},SS),p^25);

_ASSERT(
 {rem(subs({z=0,w=0,c[2]=3*a^2,c[3]=a^3},SS),a^8+3*MU,a),
  rem(rem(subs({w= 0,c[2]=-NU*z^4*y^2-z^2,c[3]=y},SS),y^3+y*z^6,y),z^8+3*MU,z),
  rem(rem(subs({w= z,c[2]=-NU*z^4*y^2-z^2,c[3]=y},SS),y^3+y*z^6,y),z^8+3*MU,z),
  rem(rem(subs({w=-z,c[2]=-NU*z^4*y^2-z^2,c[3]=y},SS),y^3+y*z^6,y),z^8+3*MU,z),
  rem(rem(subs({z= 0,c[2]=-NU*w^4*y^2-w^2,c[3]=y},SS),y^3+y*w^6,y),w^8+3*MU,w)
 } = {0},
 "Character theory relation"
);

vars_E := vars_C1:
rels_E := {op(basis_C1),mods(ss,p)}:
basis_E := Basis(rels_E,vars_E,characteristic=p);
NF_E := (u) -> mods(NormalForm(u,basis_E,vars_E,characteristic=p),p);
cobasis_E := cobasis(basis_E,vars_E);

_ASSERT(nops(cobasis_E) = 105,"E^0(BG) has rank 105");

