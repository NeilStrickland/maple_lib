#@ Not autoload

# (This has been partially converted to autoloadable form, but
# needs more work.)

# This file contains formulae for elliptic curves taken from	
# "Courbes Elliptiques: Formulaire (d'apr\`es J. Tate)"	
# by P. Deligne (pages 53-73 of Modular Functions of One	
# Variable IV, LNM 476, edited by B.J. Birch and W. Kuyk, 1975)

`is_element/weierstrass_vectors` := proc(a,t := constant)
 return type(a,[t $ 5]);
end:

`weierstrass_cubic` := (a) -> proc(xy)
 local a1,a2,a3,a4,a6,x,y;
 a1,a2,a3,a4,a6 := op(a);
 x,y := op(xy);
 return y^2 + a1 * x * y + a3 * y - x^3 - a2 * x^2 - a4 * x - a6;
end:

`homogeneous_cubic` := (a) -> proc(xyz)
 local a1,a2,a3,a4,a6,x,y,z;
 a1,a2,a3,a4,a6 := op(a);
 x,y,z := op(xyz);
 return y^2*z + a1*x*y*z + a3*y*z^2 - x^3 - a2*x^2*z - a4*x*z^2 - a6*z^3;
end:

`a_to_b/weierstrass_vectors` := proc(a)
 local a1,a2,a3,a4,a6,b2,b4,b6,b8;

 a1,a2,a3,a4,a6 := op(a);
 
 b2 := a1^2 + 4 * a2;
 b4 := a1 * a3 + 2 * a4;
 b6 := a3^2 + 4 * a6;
 b8 := a1^2 * a6 - a1 * a3 * a4 + 4 * a2 * a6 + a2 * a3^2 - a4^2;

 return [b2,b4,b6,b8];
end:

`b_to_c/weierstrass_vectors` := proc(b)
 local b2,b4,b6,b8,c4,c6,delta;

 b2,b4,b6,b8 := op(b);
 
 c4 := b2^2 - 24 * b4;
 c6 := - b2^3 + 36 * b2 * b4 - 216 * b6;

 delta := -b2^2 * b8 - 8 * b4^3 - 27 * b6^2 + 9 * b2 * b4 * b6;

 return [c4,c6,delta];
end:

`c_to_j/weierstrass_vectors` := proc(c)
 local c4,c6,delta;

 c4,c6,delta := op(c);

 return c4^3/delta;
end:

`b_to_j/weierstrass_vectors` := proc(b)
 `c_to_j/weierstrass_vectors`(`b_to_c/weierstrass_vectors`(b));
end:

`a_to_c/weierstrass_vectors` := proc(a)
 `b_to_c/weierstrass_vectors`(`a_to_b/weierstrass_vectors`(a));
end:

`a_to_j/weierstrass_vectors` := proc(a)
 `b_to_j/weierstrass_vectors`(`a_to_b/weierstrass_vectors`(a));
end:

`b_rel/weierstrass_vectors` := proc(b)
 local b2,b4,b6,b8;

 b2,b4,b6,b8 := op(b);

 return 4 * b8 - b2 * b6 + b4^2;
end:

`c_rel/weierstrass_vectors` := proc(c)
 local c4,c6,delta;

 c4,c6,delta := op(c);

 return 1728 * delta - c4^3 + c6^2;
end:

`invariant_differential0/weierstrass_vectors` := 
 (a) -> (y * dx - x * dy)/diff(homogeneous_cubic(a)([x,y,z],z);

`invariant_differential1/weierstrass_vectors` := 
 (a) -> (z * dy - y * dz)/diff(homogeneous_cubic(a)([x,y,z],x);

`invariant_differential2/weierstrass_vectors` := 
 (a) -> (x * dz - z * dx)/diff(homogeneous_cubic(a)([x,y,z],y);

######################################################################

`id/weierstrass_group` := [1,0,0,0]:

`o/weierstrass_group` := proc(urst1,urst0)
 local u0,u1,u2,r0,r1,r2,s0,s1,s2,t0,t1,t2;

 u1,r1,s1,t1 := op(urst1);
 u0,r0,s0,t0 := op(urst0);
 u2 := u0 * u1;
 s2 := s1 + s0 * u1;
 r2 := r1 + r0 * u1^2;
 t2 := t1 + t0 * u1^3 + r0 * s1 * u1^2;
 return [u2,r2,s2,t2];
end:

`inv/weierstrass_group` := proc(urst)
 local u,r,s,t;
 u,r,s,t := op(urst);
 return [1/u,-r/u^2,-s/u,(r*s-t)/u^3];
end:

`act/vector/weierstrass_group` := (urst) -> proc(a)
 local u,r,s,t,a1,a2,a3,a4,a6;
 u,r,s,t := op(urst);
 a1,a2,a3,a4,a6 := op(a);
 return [
  a1 * u - 2 * s,
  a2 * u^2 + a1 * s * u - 3 * r - s^2,
  a3 * u^3 - a1 * r * u + 2 * r * s - 2 * t,
  a4 * u^4 + a3 * s * u^3 - 2 * a2 * r * u^2 +
    a1 * (t - 2 * r * s) * u + 3 * r^2 + 2 * r * s^2 - 2 * s * t,
  a6 * u^6 - a4 * r * u^4 +
    a3 * (t - r * s) * u^3 + a2 * r^2 * u^2 +
    a1 * (r^2 * s - r * t) * u + 2 * r * s * t - t^2 - r^2 * s^2 - r^3
 ];
end:

`act/curve/weierstrass_group` := (urst) -> proc(xyz)
 local u,r,s,t,x,y,z;
 u,r,s,t := op(urst);
 x,y,z := op(xyz);
 return [u^2 * x + r * z,u^3 * y + s * u^2 * x + t * z,z];
end:

#### UNFINISHED

# Three expressions for the invariant differential		
alpha0 := (y * dx - x * dy)/diff(HomogeneousCubic,z);
alpha1 := (z * dy - y * dz)/diff(HomogeneousCubic,x);
alpha2 := (x * dz - z * dx)/diff(HomogeneousCubic,y);

eta := y + (a1 * x + a3)/2;
xi  := x + b2 / 12;

WeierstrassCubic2 := eta^2 - x^3 - b2/4 * x^2 - b4/2 * x + b6/4;
WeierstrassCubic6 := eta^2 - xi^3 + c4/48 * xi + c6/864;

Pu := xi;
Pdashu := 2 * eta;
g2 := c4/12;
g3 := c6/216;
du := omega;
dxi := 2 * eta * omega;

                                                                  
# alpha[t_Plus]    := Expand[alpha /@ t]
# alpha[t_Times]   := Expand[alpha /@ t]
# alpha[t_^n_]     := Expand[alpha[t]^n]
# alpha[n_Integer] := n

checkalpha := {
alpha[b2] - (b2 * u^2 - 12 * r),
alpha[b4] - (b4 * u^4 - b2 * r * u^2 + 6 * r^2),
alpha[b6] - (b6 * u^6 - 2 * b4 * r * u^4 + b2 * r^2 * u^2 - 4 * r^3),
alpha[b8] - (b8 * u^8 - 3 * b6 * r * u^6 + 3 * b4 * r^2 * u^4 - b2 * r^3 * u^2 + 3 * r^4),
alpha[c4] - c4 * u^4,
alpha[c6] - c6 * u^6,
alpha[Delta] - Delta * u^12
};

CurveRule := proc(F)
  [a1 =   coeff(coeff(F,x,1),y,1),
   a2 = - coeff(coeff(F,x,2),y,0),
   a3 =   coeff(coeff(F,x,0),y,1),
   a4 = - coeff(coeff(F,x,1),y,0),
   a6 = - coeff(coeff(F,x,0),y,0)
  ]
end:

GenericCubic := y^2 + x * y - x^3 + 36/(jj - 1728) * x + 1/(jj - 1728);

mChord := proc(P,Q)
 (Q[2] - P[2])/(Q[1] - P[1]);
end:

mTangent := proc(P)
 (3 * P[1]^2 + 2 * a2 * P[1] + a4 - a1 * P[2]) / (2 * P[2] + a1 * P[1] + a3);
end:

bChord := proc(P,Q)
 (P[2] * Q[1] - Q[2] * P[1])/(Q[1] - P[1]);
end:

bTangent := proc(P)
 (- P[1]^3 + a4 * P[1] + 2 * a6 - a3 * P[2]) / (2 * P[2] + a1 * P[1] + a3);
end:

EllipticSumChord := proc(P,Q)
 local m,b,x3;
  m := mChord(P,Q);
  b := bChord(P,Q);
  x3 := m^2 + a1 * m - a2 - P[1] - Q[1];
  [x3, -(m + a1) * x3 - b - a3];
end:
 
EllipticSumTangent := proc(P,Q)
 local m,b,x3;
  m := mTangent(P);
  b := bTangent(P);
  x3 := m^2 + a1 * m - a2 - P[1] - Q[1];
  [x3, -(m + a1) * x3 - b - a3]
end:
 
Negate := proc(P)
 if nops(P) = 2 then
  return([P[1],-P[2]-a1*P[1]-a3]); 
 else
  return([P[1],-P[2]-a1*P[1]-a3*P[3],P[3]]);
 fi;
end:

Double := proc(x) 
 (x^4 - b4 * x^2 - 2 * b6 * x - b8)/(4 * x^3 + b2 * x^2 + 2 * b4 * x + b6);
end:

# xTate = sum[q^n u / (1 - q^n u)^2 , {n,-Infinity,Infinity}] -
#         sum[n q^n / (1 - q^n) , {n,1,Infinity}]

# yTate = sum[q^(2 n) u^2 / (1 - q^n u)^3 , {n,-Infinity,Infinity}] +
#         sum[n q^n / (1 - q^n) , {n,1,Infinity}]

# TateCubic = y^2 + x y - x^3 - aTate4 x - aTate6

# aTate4 = - 5 sum[ DivisorSigma[3,n] q^n , {n,1,Infinity}]
# aTate6 = - sum[ (5 DivisorSigma[3,n] + 7 DivisorSigma[5,n])/12 q^n,
#                  {n,1,Infinity}]

# cTate4 = E4 
# cTate6 = -E6

# E4 = 1 + 240 sum[ DivisorSigma[3,n] q^n , {n,1,Infinity}]
# E6 = 1 - 504 sum[ DivisorSigma[5,n] q^n , {n,1,Infinity}]
# DeltaTate = q product[ (1 - q^n)^24 , {n,1,Infinity}]



