#@ Not autoload

# This was originally written for Mathematica, and needs more
# translation.

#**************************************************************
# the rest of this does not appear in Deligne's formulaire.	

# The cubical structure					

#h[{{x0_,y0_,z0_},
#   {x1_,y1_,z1_},
#   {x2_,y2_,z2_}}] := 
#     Det[{{x0,y0,z0},{x1,y1,z1},{x2,y2,z2}}] z0 z1 z2 /
#     ( Det[{{x0,z0},{x1,z1}}] *
#       Det[{{x1,z1},{x2,z2}}] *
#       Det[{{x2,z2},{x0,z0}}] )
     
# z in terms of x where y = 1, valid mod x^10			

#zx = 
#  x^3 - a1 x^4 + a1^2 x^5 + a2 x^5 - a1^3 x^6 - 2 a1 a2 x^6 - a3 x^6 + 
#   a1^4 x^7 + 3 a1^2 a2 x^7 + a2^2 x^7 + 3 a1 a3 x^7 + a4 x^7 - a1^5 x^8 - 
#   4 a1^3 a2 x^8 - 3 a1 a2^2 x^8 - 6 a1^2 a3 x^8 - 3 a2 a3 x^8 - 
#   3 a1 a4 x^8 + a1^6 x^9 + 5 a1^4 a2 x^9 + 6 a1^2 a2^2 x^9 + a2^3 x^9 + 
#   10 a1^3 a3 x^9 + 12 a1 a2 a3 x^9 + 2 a3^2 x^9 + 6 a1^2 a4 x^9 + 
#   3 a2 a4 x^9 + a6 x^9

# Invariant differential mod x^10, where y = 1			

#omx = 
#  dx (-1 + a1 x - a1^2 x^2 - a2 x^2 + a1^3 x^3 + 2 a1 a2 x^3 + 2 a3 x^3 - 
#     a1^4 x^4 - 3 a1^2 a2 x^4 - a2^2 x^4 - 6 a1 a3 x^4 - 2 a4 x^4 + 
#     a1^5 x^5 + 4 a1^3 a2 x^5 + 3 a1 a2^2 x^5 + 12 a1^2 a3 x^5 + 
#     6 a2 a3 x^5 + 6 a1 a4 x^5 - a1^6 x^6 - 5 a1^4 a2 x^6 - 6 a1^2 a2^2 x^6 - 
#     a2^3 x^6 - 20 a1^3 a3 x^6 - 24 a1 a2 a3 x^6 - 6 a3^2 x^6 - 
#     12 a1^2 a4 x^6 - 6 a2 a4 x^6 - 3 a6 x^6)

# The following functions are invertible near [0:1:0], and	
# they satisfy uu ww = vv^3.  Note that vv depends only on y   
# and z.  Moreover, {uu != 0} \cap {x = 0} = {0} as schemes.	

#uu = y^2 + a1 x y - a2 x^2 + a3 y z - a4 x z - a6 z^2
#vv = y^2 + a3 y z - a6 z^2
#ww = a1^2 x^2 y^2 + a2 x^2 y^2 - a1 x y^3 + y^4 + a2 a3 x^2 y z - 
#   2 a1 a4 x^2 y z + a1^2 a2 x y^2 z + a2^2 x y^2 z - a1 a3 x y^2 z + 
#   a4 x y^2 z - a1^3 y^3 z - 2 a1 a2 y^3 z + 2 a3 y^3 z + a4^2 x^2 z^2 - 
#   a2 a6 x^2 z^2 + a2^2 a3 x y z^2 - 2 a1 a2 a4 x y z^2 + a3 a4 x y z^2 + 
#   a1 a6 x y z^2 - 2 a1 a2 a3 y^2 z^2 + a3^2 y^2 z^2 + 3 a1^2 a4 y^2 z^2 + 
#   2 a2 a4 y^2 z^2 - 2 a6 y^2 z^2 + a2 a4^2 x z^3 - a2^2 a6 x z^3 - 
#   a4 a6 x z^3 + 2 a2 a3 a4 y z^3 - 3 a1 a4^2 y z^3 + 2 a1 a2 a6 y z^3 - 
#   2 a3 a6 y z^3 + a4^3 z^4 - 2 a2 a4 a6 z^4 + a6^2 z^4

# We now give some formulae that identify the singular locus.	

#Frule = {F  -> HomogeneousCubic,
#         Fx -> D[HomogeneousCubic,x],
#         Fy -> D[HomogeneousCubic,y],
#         Fz -> D[HomogeneousCubic,z]}

#A0 = 4 F - 2 x Fx - (2 y + a3 z) Fy 
#A1 = - 2 Fx + a1 Fy
#A2 = 4 a2 z F +
#     - ((a1 a3 + a4) z^2 + (a1^2 + 2 a2) x z + 3 x^2 + a1 y z) Fx +
#     - (a2 a3 z^2 + (a1 a2 + 2 a3) x z + 2 a1 x^2 + (2 a2 z + 4 x) y) Fy
#
#AA0 = 2 x^3 - B4 x z^2 - B6 z^3
#AA1 = 6 x^2 + B2 x z + B4 z^2
#AA2 = x^4 - B4 x^2 z^2 - 2 B6 x z^3 - B8 z^4

#Dl = (-7 B2 B4 z^2 + 27 B6 z^2 - 36 B4 x z + 3 B2 x^2) AA0 + 
#     (-8 B4^2 z^3 + 2 B2 B6 z^3 + B2 B4 x z^2 - 9 B6 x z^2 +
#      12 B4 x^2 z - B2 x^3) AA1 +
#      B2^2 z AA2

# The singular point, where Delta = 0 and c4 is invertible.	

#xs = 18 b6 - b2 b4 

#ys = (a1 a4 - 2 a2 a3) b2 + 12 a3 b4 - 9 a1 b6

#zs = c4

# This evaluates to {0,0,0,0}, showing that [xs:ys:zs] is	
# indeed a singular point.					

CheckSingular0 =
({F,Fx,Fy,Fz} /. Frule /. {x->xs,y->ys,z->zs}) - 
 {-c6,36,0,3 b2} Delta 

# The following evaluates to {0,0}.  Because points with z=0	
# are smooth and zs = c4 is assumed invertible, we conclude	
# that every singular point is projectively equivalent to	
# [xs:ys:zs].							

CheckSingular1 =
({-2 b2 z Fx - 
 (6 a1 x + 12 y - a1 b2 z + 18 a3 z) Fy + 
 24 z Fz,
 a1 b2 z Fx + 
 (3 a1^2 x + 6 a1 y + (2 a2 b2 - 3 a1 a3 - 24 a4)z ) Fy - 
 12 a1 z Fz} /. Frule) -
{ (zs x - xs z) z^2 , 
  (zs y - ys z) z^2}

# Grobner basis for the singular points over the locus where	
# c4 = Delta = 2 = 0 (with y > x > a3 > a1 > a6 > a4 > a2)     

AdditiveLocusMod2 = {
 y^2 + x^3 + a2 x^2 + a4 x + a6,
 x^2 y + a4 y + a3 x^2 + a2 a3 x + a1 a6 + a3 a4,
 a3 y + x^3 + a4 x,
 a1 y + x^2 + a4,
 x^4 + a3^2 x + a1^2 a6 + a4^2 + a1 a3 a4 + a2 a3^2,
 a3 x^3 + a1^3 a6 + a1 a4^2 + a1^3 a2 a4,
 a1^2 a4^2 + a3^2 x^2,
 a3 + a1 x,
 a3^3 + a1^2 a3 a4,
 a1 a3^2 + a1^3 a4,
 a1^3 a3,
 a1^4}

ReducedAdditiveLocusMod2 = {y^2 + a2 a4 + a6, x^2 + a4, a1, a3}

AdditiveLocusMod3 = {
 y - a1 x - a3,
 a1^4 - a1^2 a2 + a2^2,
 -a3^2 - a6 - a1 a3 x + a4 x - x^3, 
 a1 a3 - a4 + a1^2 x + a2 x, 
 a1^3 a3 + a1 a2 a3 - a1^2 a4 - a2 a4, 
 -(a1^2 a3^2) - a1 a3 a4 - a4^2, 
 a1^2 a3^2 + a2 a3^2 + a1^2 a6 + a2 a6 - a1 a3 x^2 + a4 x^2}

ReducedAdditiveLocusMod3 = {
 y - a1 x - a3,
 x^3 + a6 + a3^2,
 a4 - a1 a3,
 a2 + a1^2}

ReducedAdditiveLocusRational = {
 y + a1 x/2 + a3/2,
 x^2 - b2 x/6 - b4/6,
 a6 + a3^2/4 - a2^3/27 - a1^2 a2^2/36 - a1^4 a2/144 - a1^6/1728,
 a4 + a1 a3/2 - a2^2/3 - a1^2 a2/6 - a1^4/48}
 

#**************************************************************
# Various quotients of localisations of Z[a1,..,a6] that give	
# etale maps to the elliptic moduli stack (I think)		

# etale1 covers D(6 c6)        				

etale1 = {a1 -> 0, a2 -> 0, a3 -> 0, a6 -> 1}

# etale2 covers D(6 c4)        				

etale2 = {a1 -> 0, a3 -> 0, a2 -> 0, a4 -> 1}

# etale3 covers a neighbourhood of V(2) D(c4)        		

etale3 = {a1 -> 1, a3 -> 0, a2 -> 0, a4 -> 0}

# etale4 covers a neighbourhood of V(3) D(c4)        		

etale4 = {a1 -> 0, a3 -> 0, a2 -> 1, a4 -> 0}

# etale5 covers a neighbourhood of V(2,a1) ; etale over D(3)	

etale5 = {a3 -> 1, a2 -> 0, a4 -> 0, a6 -> 0}

# etale6 covers a neighbourhood of V(3,a2) ; etale over D(2)	

etale6 = {a1 -> 0, a3 -> 0, a4 -> 1, a6 -> 0}

# Det[Jac[etale6,a2]] (for example) is the Jacobian		
# determinant for the map					
#								
#  Z[a1,a2,a3,a4,a6] -> Z[v,r,s,t,a2]				
#								
# (where v = 1/u) given by alpha.  This must be invertible for	
# the map to be etale.						

Jac[er_,aa_] := 
 Outer[D,
  FixedPoint[Expand[# /. er /. u -> 1/v]&, alpha /@ {a1,a3,a2,a4,a6}],
  {v,r,s,t,aa}
 ]

#**************************************************************
# Singular fibres						

# The curve y^2 z + x y z = x^3 is a nodal cubic, with         
# multiplicative formal group.					

multcurve = {a1->1, a3->0, a2->0, a4->0, a6->0}

# There is a birational map f from P^1 to the curve, with	
# inverse g.	This sends both 0 and infinity to the singular  
# point [0:0:1], and the restriction to G_m is a homomorphism. 
# The discriminant is zero and the j invariant is infinite.	

fm[s_,t_] := {s t (s - t), t^2 s, (s - t)^3}

gm[x_,y_,z_] := {y + x, y}

# The curve y^2 = x^3 is a cuspidal cubic, with additive 	
# formal group.						

addcurve = {a1->0, a3->0, a2->0, a4->0, a6->0}

# There is a birational map f from P^1 to the curve, with	
# inverse g.	This sends infinity to the singular point       
# [0:0:1] with multiplicity two, and the restriction to G_a is 
# a homomorphism the discriminant is zero and the j invariant  
# is undefined.						 

fa[s_,t_] := {t^2 s, t^3, s^3}

ga[x_,y_,z_] := {x, y}

#**************************************************************
# Curves with prescribed j invariant				

# This curve is defined if jj - 1728 is invertible, and is     
# nonsingular if jj is also invertible.  It has		
# c4 = - c6 = jj/(jj - 1728) and Delta = jj^2 / (jj - 1728)^3  
# and j = jj (unless jj = 0, in which case j is undefined).    

# jcurve[0] corresponds to the curve (y + x/2)^2 =(x + 1/12)^3 

jcurve[jj_] := 
 {a1 -> 1, a2 -> 0, a3 -> 0, 
  a4 -> 36/(1728 - jj), a6 -> 1/(1728 - jj)}

#**************************************************************
# Legendre curve.  This is defined where 2 is invertible and   
# lm != 0 or 1.  The points of order two are			
# P = [0:0:1] and Q = [1:0:1] and P+Q = [lm:0:1].  An invariant
# differential is given by om = -dx/y.  This is the universal  
# example of a curve with an invariant differential and a      
# level two structure such that x(P) = 0 and x(Q) = 1, where	
# x is the unique choice adapted to om with a1 = a3 = 0.	

# c4    = 16(1 - lm + lm^2)					
# c6    = 32(lm - 2)(lm + 1)(2 lm - 1)				
# Delta = 16 lm^2 (lm - 1)^2					
# j     = 256 (1 - lm + lm^2)^3 / ((lm - 1)^2 lm^2)		

legendre = {a1 -> 0, a3 -> 0, a2 -> -(lm + 1), a4 -> lm, a6 -> 0}

#**************************************************************
# Jacobi quartic.						

# c4    = 2^6 3^4 (dl^2 + 3 ep)				
# c6    = 2^9 3^6 (dl^3 - 9 dl ep)				
# Delta = 2^12 3^12 ep (ep - dl^2)^2				
# j     = 64 (dl^2 + 3 ep)^3 / (ep (ep - dl^2)^2)		

jacobi_rule :=
 {a1 = 0, a3 = 0, a2 = 0, a4 = -108 dl^2 - 324 ep, a6 = 3888 dl ep - 432 dl^3} 

xXY := (6*(-2*dl - dl^2*X^2 + 3*ep*X^2 + 2*dl*Y))/(-1 + dl*X^2 + Y);
yXY := (108*(dl^2 - ep)*X)/(-1 + dl*X^2 + Y);

Xxy = (6*(12*dl - x))/y
Yxy = (2592*dl^3 - 7776*dl*ep + 216*dl^2*x + 648*ep*x - 
       36*dl*x^2 + y^2)/y^2

# In quartic form, the zero element is (0,1).			

jacobiquartic = Y^2 - (1 - 2 dl X^2 + ep X^4)

# invariant differential					

omegaXY = -dX/(6 Y) 

# This can also be written as \sum_n P_n(dl,ep) X^(2n) dX	
# where P_n(dl,ep)=P_n(dl/Sqrt[ep]) ep^(n/2) and P_n(t) is the 
# Legendre polynomial.  These are defined by			
# (1 -2xt +t^2)^(-1/2) = \sum_n P_n(x) t^n			

# There is a canonical point P of order 2: (x,y)=(12 dl,0).	
# Apparently this is the universal example of a curve with an  
# invariant differential and a point of exact order 2 (where   
# 2 is invertible).  Apparently also				
# div(X) = [2]^{-1}[0] - [2]^{-1}[P]				

# It seems that if six is invertible and we have a given point 
# P of order 2, we can put the curve in the form		
# y^2 = x^3 + a4 x + a6 and then P = (12 dl,0) say and we can  
# define ep = -(4 a4 + 432 dl^2)/1296 to put the curve in	
# Jacobi form.  I'm not sure this is right, though.		

#**************************************************************

# Formal group formulae, valid up to terms of weight 7.	

F = x0 + x1 + a1*x0*x1 - a2*x0^2*x1 + 2*a3*x0^3*x1 - 2*a1*a3*x0^4*x1 - 
 2*a4*x0^4*x1 + 2*a1^2*a3*x0^5*x1 + 2*a2*a3*x0^5*x1 + 2*a1*a4*x0^5*x1 - 
 2*a1^3*a3*x0^6*x1 - 4*a1*a2*a3*x0^6*x1 - 2*a3^2*x0^6*x1 - 
 2*a1^2*a4*x0^6*x1 - 2*a2*a4*x0^6*x1 - 3*a6*x0^6*x1 - a2*x0*x1^2 - 
 a1*a2*x0^2*x1^2 + 3*a3*x0^2*x1^2 + a2^2*x0^3*x1^2 - a1*a3*x0^3*x1^2 - 
 4*a4*x0^3*x1^2 + a1^2*a3*x0^4*x1^2 + a1*a4*x0^4*x1^2 - a1^3*a3*x0^5*x1^2 - 
 a1*a2*a3*x0^5*x1^2 - a1^2*a4*x0^5*x1^2 - 9*a6*x0^5*x1^2 + 2*a3*x0*x1^3 + 
 a2^2*x0^2*x1^3 - a1*a3*x0^2*x1^3 - 4*a4*x0^2*x1^3 + a1*a2^2*x0^3*x1^3 + 
 a1^2*a3*x0^3*x1^3 - 2*a2*a3*x0^3*x1^3 - a2^3*x0^4*x1^3 - a1^3*a3*x0^4*x1^3 - 
 2*a1*a2*a3*x0^4*x1^3 + 4*a3^2*x0^4*x1^3 - a1^2*a4*x0^4*x1^3 + 
 4*a2*a4*x0^4*x1^3 - 15*a6*x0^4*x1^3 - 2*a1*a3*x0*x1^4 - 2*a4*x0*x1^4 + 
 a1^2*a3*x0^2*x1^4 + a1*a4*x0^2*x1^4 - a2^3*x0^3*x1^4 - a1^3*a3*x0^3*x1^4 - 
 2*a1*a2*a3*x0^3*x1^4 + 4*a3^2*x0^3*x1^4 - a1^2*a4*x0^3*x1^4 + 
 4*a2*a4*x0^3*x1^4 - 15*a6*x0^3*x1^4 + 2*a1^2*a3*x0*x1^5 + 2*a2*a3*x0*x1^5 + 
 2*a1*a4*x0*x1^5 - a1^3*a3*x0^2*x1^5 - a1*a2*a3*x0^2*x1^5 - 
 a1^2*a4*x0^2*x1^5 - 9*a6*x0^2*x1^5 - 2*a1^3*a3*x0*x1^6 - 
 4*a1*a2*a3*x0*x1^6 - 2*a3^2*x0*x1^6 - 2*a1^2*a4*x0*x1^6 - 2*a2*a4*x0*x1^6 - 
 3*a6*x0*x1^6


logF =
 x - (a1*x^2)/2 + (a1^2*x^3)/3 + (a2*x^3)/3 - (a1^3*x^4)/4 - (a1*a2*x^4)/2 - 
 (a3*x^4)/2 + (a1^4*x^5)/5 + (3*a1^2*a2*x^5)/5 + (a2^2*x^5)/5 + 
 (6*a1*a3*x^5)/5 + (2*a4*x^5)/5 - (a1^5*x^6)/6 - (2*a1^3*a2*x^6)/3 - 
 (a1*a2^2*x^6)/2 - 2*a1^2*a3*x^6 - a2*a3*x^6 - a1*a4*x^6 + (a1^6*x^7)/7 + 
 (5*a1^4*a2*x^7)/7 + (6*a1^2*a2^2*x^7)/7 + (a2^3*x^7)/7 + 
 (20*a1^3*a3*x^7)/7 + (24*a1*a2*a3*x^7)/7 + (6*a3^2*x^7)/7 + 
 (12*a1^2*a4*x^7)/7 + (6*a2*a4*x^7)/7 + (3*a6*x^7)/7

# ms[k] is the [k] series.					

ms[-1] =
 -x + a1*x^2 - a1^2*x^3 + a1^3*x^4 + a3*x^4 - a1^4*x^5 - 3*a1*a3*x^5 + 
 a1^5*x^6 + 6*a1^2*a3*x^6 + a2*a3*x^6 - a1^6*x^7 - 10*a1^3*a3*x^7 - 
 4*a1*a2*a3*x^7 - 2*a3^2*x^7 + a1^7*x^8 + 15*a1^4*a3*x^8 + 
 10*a1^2*a2*a3*x^8 + a2^2*a3*x^8 + 10*a1*a3^2*x^8 + a3*a4*x^8 - a1^8*x^9 - 
 21*a1^5*a3*x^9 - 20*a1^3*a2*a3*x^9 - 5*a1*a2^2*a3*x^9 - 30*a1^2*a3^2*x^9 - 
 5*a2*a3^2*x^9 - 5*a1*a3*a4*x^9

ms[2] = 
 2*x + a1*x^2 - 2*a2*x^3 - a1*a2*x^4 + 7*a3*x^4 + 2*a2^2*x^5 - 6*a1*a3*x^5 - 
 12*a4*x^5 + a1*a2^2*x^6 + 7*a1^2*a3*x^6 + 2*a2*a3*x^6 + 6*a1*a4*x^6 - 
 2*a2^3*x^7 - 8*a1^3*a3*x^7 - 14*a1*a2*a3*x^7 + 4*a3^2*x^7 - 8*a1^2*a4*x^7 + 
 4*a2*a4*x^7 - 54*a6*x^7

ms[3] = 
 3*x + 3*a1*x^2 + a1^2*x^3 - 8*a2*x^3 - 12*a1*a2*x^4 + 39*a3*x^4 - 
 6*a1^2*a2*x^5 + 24*a2^2*x^5 - 9*a1*a3*x^5 - 96*a4*x^5 - a1^3*a2*x^6 + 
 44*a1*a2^2*x^6 + 30*a1^2*a3*x^6 - 57*a2*a3*x^6 - 48*a1*a4*x^6 + 
 30*a1^2*a2^2*x^7 - 72*a2^3*x^7 - 36*a1^3*a3*x^7 - 168*a1*a2*a3*x^7 + 
 234*a3^2*x^7 - 72*a1^2*a4*x^7 + 288*a2*a4*x^7 - 936*a6*x^7

ms[5] =
 5*x + 10*a1*x^2 + 10*a1^2*x^3 - 40*a2*x^3 + 5*a1^3*x^4 - 140*a1*a2*x^4 + 
 310*a3*x^4 + a1^4*x^5 - 222*a1^2*a2*x^5 + 376*a2^2*x^5 + 306*a1*a3*x^5 - 
 1248*a4*x^5 - 205*a1^3*a2*x^6 + 1740*a1*a2^2*x^6 + 620*a1^2*a3*x^6 - 
 2130*a2*a3*x^6 - 3120*a1*a4*x^6 - 120*a1^4*a2*x^7 + 3750*a1^2*a2^2*x^7 - 
 3560*a2^3*x^7 - 90*a1^3*a3*x^7 - 9540*a1*a2*a3*x^7 + 10540*a3^2*x^7 - 
 5800*a1^2*a4*x^7 + 14240*a2*a4*x^7 - 33480*a6*x^7


Null[];
