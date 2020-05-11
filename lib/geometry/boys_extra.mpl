# The block below either calculates or reads from file the alternative
# Boys immersion, calibrated to have special behaviour at the points
# [+/- 1, +/- 1, +/- 1]/sqrt(3).

if false then 
 make_boys_embedding_alt():
 save(boys_M0,boys_M1,boys_a1,boys_embedding_alt,cat(data_dir,"/boys_embedding_alt.m")):
else 
 read(cat(data_dir,"/boys_embedding_alt.m")):
fi:

bef := (x) -> evalf(boys_embedding_alt(x)):

check_bef := proc()
 _ASSERT(
  max(evalf([
  dd(bef(u[0]),u[0]),
  dd(bef(u[1]),u[6]),
  dd(bef(u[2]),u[5]),
  dd(bef(u[3]),u[4]),
  dd(bef(u[4]),u[4]),
  dd(bef(u[5]),u[5]),
  dd(bef(u[6]),u[6]),
  dd(bef(u[7]),u[0])
  ])) < 10^(-6),
  "bef(u[i])=u[j] for expected pairs (i,j)"
 );
end:

# Miscellaneous functions
dp := `dot/R`(3):
dd := `d_2/R`(3):
`mmu/H` := apply_assoc(`mu/H`,[0,0,0,1]):
rot := (x) -> [x[2],x[3],x[1]]:

# Unit quaternions.
ii[1] := [1,0,0,0]: 
ii[2] := [0,1,0,0]: 
ii[3] := [0,0,1,0]: 
ii[4] := [0,0,0,1]:

# Misccellaneous quaternions
zt[1] := [1,1+sqrt(3),1-sqrt(3),0] /~ 3:
zt[2] := [1-sqrt(3),1,1+sqrt(3),0] /~ 3:
zt[3] := [1+sqrt(3),1-sqrt(3),1,0] /~ 3:
al := [ 1, 1, 1, 0] /~ sqrt(3):
om := [ 1, 1, 1, 1] /~ 2:
ob := [-1,-1,-1, 1] /~ 2:

# Various unit vectors in R3.  For each i, the vectors u[i], v[i] and w[i]
# form an orthonormal frame.  z[i] is in the plane spanned by u[0] and u[i]
# and is orthogonal to u[0].

u := table(): v := table(): w := table(): z := table():
u[ 0] := [ 1, 1, 1] /~ sqrt(3): v[ 0] := [ 2,-1,-1] /~ sqrt(6): w[ 0] := [ 0, 1,-1] /~ sqrt(2): 
u[ 1] := [ 1, 1,-1] /~ sqrt(3): v[ 1] := [ 2,-1, 1] /~ sqrt(6): w[ 1] := [ 0,-1,-1] /~ sqrt(2): z[ 1] := [ 1, 1,-2] /~ sqrt(6):
u[ 2] := [ 1,-1, 1] /~ sqrt(3): v[ 2] := [-1, 1, 2] /~ sqrt(6): w[ 2] := [-1,-1, 0] /~ sqrt(2): z[ 2] := [ 1,-2, 1] /~ sqrt(6): 
u[ 3] := [-1, 1, 1] /~ sqrt(3): v[ 3] := [ 1, 2,-1] /~ sqrt(6): w[ 3] := [-1, 0,-1] /~ sqrt(2): z[ 3] := [-2, 1, 1] /~ sqrt(6): 
u[ 4] := [ 1,-1,-1] /~ sqrt(3): v[ 4] := [-1,-2, 1] /~ sqrt(6): w[ 4] := [-1, 0,-1] /~ sqrt(2): z[ 4] := [ 2,-1,-1] /~ sqrt(6): 
u[ 5] := [-1, 1,-1] /~ sqrt(3): v[ 5] := [ 1,-1,-2] /~ sqrt(6): w[ 5] := [-1,-1, 0] /~ sqrt(2): z[ 5] := [-1, 2,-1] /~ sqrt(6): 
u[ 6] := [-1,-1, 1] /~ sqrt(3): v[ 6] := [-2, 1,-1] /~ sqrt(6): w[ 6] := [ 0,-1,-1] /~ sqrt(2): z[ 6] := [-1,-1, 2] /~ sqrt(6): 
u[ 7] := [-1,-1,-1] /~ sqrt(3): v[ 7] := [-2, 1, 1] /~ sqrt(6): w[ 7] := [ 0, 1,-1] /~ sqrt(2):

pol  := unapply(expand(cos(s) *~ u[0] +~ sin(s) *~ (cos(t) *~ v[0] +~ sin(t) *~ w[0])),s,t):
pol0 := (s,t) -> [cos(s),sin(s)*cos(t),sin(s)*sin(t)]:

# The function wave(t) has trigonometric polynomial entries and lies on
# the unit sphere, passing through all the points u[1],...,u[6].
wave := unapply(
(sin(3*t)/3) *~ u[0] +~ 
((sqrt(2)/3-1/2) * sin(5*t)) *~ v[0] +~
((sqrt(2)/3-1/2) * cos(5*t) * (-1)) *~ w[0] +~
((sqrt(2)/3+1/2) * sin(t)) *~ v[0] +~
((sqrt(2)/3+1/2) * cos(t)) *~ w[0],
t):

# wband(t,s) parametrises a band with wave(t) = wband(t,0) at the centre
wave_normal := unapply(combine(expand(simplify(expand(cross_product(wave(t),map(diff,wave(t),t)))))),t):
wband := unapply(sin(s) *~ wave_normal(t) +~ cos(s) *~ wave(t),t,s):

check_wband := proc()
 _ASSERT(
  simplify(expand(dp(wave(t),wave(t)) - 1)) = 0,
  "wave(t) is a unit vector"
 );

 _ASSERT(
  simplify(expand(wave(t - Pi/3) +~ rot(wave(t)))) = [0$3],
  "wave(t) is Z/3-equivariant"
 );

 _ASSERT(
  {seq(simplify(wave((2 * i - 1) * Pi/6) -~ u[[1,4,2,6,3,5][i]]),i=1..6)} = {[0$3]},
  "wave(t) passes through u[1],...,u[6]"
 );
end:

# A band in S2 with central circle perpendicular to u[0]
hband := (t,s) ->
 sin(s) *~ u[0] +~ cos(s) *~ (cos(t) *~ v[0] +~ sin(t) *~ w[0]):

# A family of bands in S2 whose central circles are lines of longitude
# (with u[0] as the North pole).

vband := (p) -> unapply(combine(
                 cos(s) *~ ( cos(t) *~ (cos(p) *~ v[0] +~ sin(p) *~ w[0]) +~ sin(t) *~ u[0]) +~ 
                 sin(s) *~ ( -sin(p) *~ v[0] +~ cos(p) *~ w[0] )),
                t,s):

check_bands := proc()
 _ASSERT(simplify(hband(0,0) -~ vband(0)(0,0)) = [0$3],
  "Intersection of hband and vband(0)");
  
 _ASSERT(simplify(hband(Pi/6,0) -~ vband(Pi/6)(0,0)) = [0$3],
  "Intersection of hband and vband(Pi/6)");
  
 _ASSERT(vband(0)(Pi/2,0) -~ u[0] = [0$3],"u[0] on vband(0)");

 _ASSERT(simplify(vband(0)(Pi-arctan(sqrt(2)/4),0) -~ u[3]) = [0$3],"u[3] on vband(0)");

 _ASSERT(simplify(vband(0)(-arctan(sqrt(2)/4),0) -~ u[4]) = [0$3],"u[4] on vband(0)");

 _ASSERT(vband(Pi/6)(Pi/2,0) -~ u[0] = [0$3],"u[0] on vband(Pi/6)");
 
 _ASSERT({
  simplify(wband(    Pi/6,0) -~ u[1]),
  simplify(wband(3 * Pi/6,0) -~ u[4]),
  simplify(wband(5 * Pi/6,0) -~ u[2]),
  simplify(wband(7 * Pi/6,0) -~ u[6]),
  simplify(wband(9 * Pi/6,0) -~ u[3]),
  simplify(wband(11* Pi/6,0) -~ u[5])} = {[0$3]},
  "u[1],...,u[6] on wband");
  
 _ASSERT({
  simplify(wband(        0,0) -~ hband(15*Pi/6,0)),
  simplify(wband(     Pi/3,0) -~ hband(13*Pi/6,0)),
  simplify(wband( 2 * Pi/3,0) -~ hband(11*Pi/6,0)),
  simplify(wband( 3 * Pi/3,0) -~ hband( 9*Pi/6,0)),
  simplify(wband( 4 * Pi/3,0) -~ hband( 7*Pi/6,0)),
  simplify(wband( 5 * Pi/3,0) -~ hband( 5*Pi/6,0))} = {[0$3]},
  "Intersections of wband with hband");
  
 _ASSERT(
  simplify(expand(hband(t-2*Pi/3,s) -~ rot(hband(t,s)))) = [0$3],
  "hband is Z/3-equivariant");
  
 _ASSERT(
  simplify(expand(hband(t+Pi/3,-s) +~ rot(hband(t,s)))) = [0$3],
  "hband is Z/6-equivariant");
  
 _ASSERT(vband(0)(t+Pi,-s) +~ vband(0)(t,s) = [0$3],
  "vband(0) is Z/2-equivariant");
  
 _ASSERT(vband(Pi/6)(t+Pi,-s) +~ vband(Pi/6)(t,s) = [0$3],
  "vband(Pi/6) is Z/2-equivariant");
 
 _ASSERT(simplify(expand(wband(t-Pi/3,0) +~ rot(wband(t,0)))) = [0$3],
  "wband is Z/6-equivariant");

 _ASSERT(wband(t+Pi,0) +~ wband(t,0) = [0$3],
  "wband is Z/2-equivariant");

end:

# An embedding of the Mobius band in R^3 whose centra curve is
# a circle of radius sqrt(8/9) on S2 passing through u[1],u[2] and u[3],
# and perpendicular to u[0].

triple_mobius := unapply(
(1 + s * cos(3*t)) *~ ((1/3) *~ u[0] +~ sqrt(8/9) *~ (cos(2*t) *~ v[0] +~ sin(2*t) *~ w[0])) +~ 
 (s * sin(3*t) * sqrt(2/27)) *~ [cos(2*t)-2,cos(2*t-2*Pi/3)-2,cos(2*t+2*Pi/3)-2],
t,s):


check_triple_mobius := proc()
 _ASSERT(
  simplify(expand(dp(triple_mobius(t,0),triple_mobius(t,0)) - 1)) = 0,
  "triple_mobius(t,0) is a unit vector");

 _ASSERT(
  expand(dp(triple_mobius(t,0),u[0]) - 1/3) = 0,
  "triple_mobius(t,0) lies in a plane perpendicular to u[0]");

 _ASSERT(
  simplify(expand(dp(map(coeff,expand(triple_mobius(t,s)),s),map(diff,triple_mobius(t,0),t)))) = 0,
  "The triple_mobius() offset vector is perpendicular to the line of the central circle" 
 );

 _ASSERT({
  simplify(triple_mobius(  Pi/6,0) -~ u[1]),
  simplify(triple_mobius(5*Pi/6,0) -~ u[2]),
  simplify(triple_mobius(3*Pi/6,0) -~ u[3])} = {[0$3]},
  "u[1],u[2],u[3] on triple_mobius()");

 _ASSERT(
  abs(twist_number(triple_mobius) - 3) < 10^(-6),
  "triple_mobius() twist number is 3"
 );
end:

# This is a smooth map R -> R^3 whose image is close to an equilateral
# triangle 
smooth_triangle := unapply([
 3 * cos(2*t-  Pi/3) + cos(4*t-5*Pi/3),
 3 * cos(2*t-5*Pi/3) + cos(4*t-  Pi/3),
 3 * cos(2*t-3*Pi/3) + cos(4*t-3*Pi/3)
] /~ (sqrt(27)) +~ u[0]/~3,t):

smooth_triangle_p := Pi/4:

smooth_triangle_offset := 
 unapply(( sin(3*(t-Pi/4))*sqrt(2/3)) *~ [cos(2*t-  Pi/3),cos(2*t-5*Pi/3),cos(2*t-3*Pi/3)] +~
         (-cos(3*(t-Pi/4))) *~ u[0],t):

triangle_mobius := unapply(
 smooth_triangle(t) +~ s *~ smooth_triangle_offset(t),
 t,s
):

check_smooth_triangle := proc()
 local t;

 _ASSERT(
  simplify(expand(smooth_triangle(t-2*Pi/3) -~ rot(smooth_triangle(t)))) = [0$3],
  "smooth_triangle is Z/3-equivariant"
 );
 
 _ASSERT({
  simplify(expand(smooth_triangle(     0) -~ u[1])),
  simplify(expand(smooth_triangle(  Pi/3) -~ u[2])),
  simplify(expand(smooth_triangle(2*Pi/3) -~ u[3]))} = {[0$3]},
  "u[1],u[2],u[3] on smooth_triangle"
 );

 _ASSERT(
  abs(twist_number(triangle_mobius) - 3) < 10^(-6),
  "triangle_mobius() twist number is 3"
 );
end:

make_band_plots := proc()
 global hband_plot,vband_plot,wband_plot,triangle_mobius_plot,usphere_plot,frame_plot;
 local s,t,opts;

 opts := t=0..2*Pi,s=-0.2..0.2,style=patchnogrid,scaling=constrained,axes=none;

 vband_plot := table():
 
 hband_plot       :=  plot3d(hband(t,s),opts);
 vband_plot[0]    :=  plot3d(vband(0)(t,s),opts);
 vband_plot[Pi/6] :=  plot3d(vband(Pi/6)(t,s),opts);
 wband_plot       :=  plot3d(wband(t,s),opts);

 triangle_mobius_plot :=  plot3d(triangle_mobius(t,s),opts);

 usphere_plot := plot3d(
  cos(s) *~ u[0] +~ sin(s) *~ (cos(t) *~ v[0] +~ sin(t) *~ w[0]),
  s=0..Pi,t=0..2*Pi,colour=grey,style=wireframe,
  scaling=constrained,axes=none
 ):

 frame_plot := display(
  usphere_plot,
  point(u[0],colour=red,symbolsize=20),
  seq(point(u[i],colour=blue,symbolsize=20),i=1..3),
  seq(point(u[i],colour=cyan,symbolsize=20),i=4..6),
  point(u[7],colour=magenta,symbolsize=20),
  seq(spacecurve(cos(t) *~ u[0] +~ sin(t) *~ z[i],t=0..arccos(1/3),colour=orange),i=1..3),
  seq(spacecurve(cos(t) *~ u[0] +~ sin(t) *~ z[i],t=arccos(1/3)..Pi,colour=green),i=1..3),
  seq(spacecurve(cos(t) *~ u[7] +~ sin(t) *~ z[i],t=0..arccos(1/3),colour=orange),i=4..6),
  seq(spacecurve(cos(t) *~ u[7] +~ sin(t) *~ z[i],t=arccos(1/3)..Pi,colour=green),i=4..6),
  spacecurve(cos(t) *~ v[0] +~ sin(t) *~ w[0],t=0..2*Pi,colour=cyan),
  seq(point(cos(k*Pi/6) *~ v[0] +~ sin(k*Pi/6) *~ w[0],colour=black,symbolsize=20),k=0..11),
  spacecurve(wave(t),t=0..2*Pi,colour=black),
  scaling=constrained,axes=none
 ):

 save(hband_plot,vband_plot,wband_plot,triangle_mobius_plot,frame_plot,usphere_plot,
      cat(data_dir,"/boys_band_plots.m"));
end:

load_band_plots := proc()
 read(cat(data_dir,"/boys_band_plots.m"));
end:

make_band_be_plots := proc()
 global hband_be_plot,vband_be_plot,wband_be_plot;
 local s,t,opts;

 opts := t=0..Pi,s=-0.2..0.2,numpoints=10000,style=patchnogrid,scaling=constrained,axes=none;

 vband_be_plot := table():
 
 hband_be_plot       :=  plot3d(bef(hband(t,s)),opts);
 vband_be_plot[0]    :=  plot3d(bef(vband(0)(t,s)),opts);
 vband_be_plot[Pi/6] :=  plot3d(bef(vband(Pi/6)(t,s)),opts);
 wband_be_plot       :=  plot3d(bef(wband(t,s)),opts);

 save(hband_be_plot,vband_be_plot,wband_be_plot,
      cat(data_dir,"/boys_band_be_plots.m"));
end:

load_band_be_plots := proc()
 read(cat(data_dir,"/boys_band_be_plots.m"));
end:


# If f : R2 -> R3 with f(t+2*Pi=f(t) this measures the amount of twisting,
# so a standard Mobius band gives 1 and the maps triple_mobius and
# triangle_mobius give 3.

twist_number := proc(f)
 local N,e,a,b,c,z,i;
 N := 24;
 e := 0.001;
 a := table():
 b := table():
 c := table():
 z := table():
 for i from 0 to 2*N-1 do 
  a[i] := evalf(f(i*Pi/N,0));
  b[i] := evalf((f(i*Pi/N,e) -~ f(i*Pi/N,-e))/~e);
  b[i] := b[i] /~ sqrt(dp(b[i],b[i]));
 od:
 a[2*N] := a[0]; a[2*N+1] := a[1]; 
 b[2*N] := b[0]; b[2*N+1] := b[1];

 for i from 0 to 2*N do 
  c[i] := cross_product(u[0],a[i+1] -~ a[i]);
  c[i] := c[i] /~ sqrt(dp(c[i],c[i]));
  z[i] := dp(b[i],c[i]) + I * dp(b[i],u[0]);
 od:

 return evalf(add(argument(z[i+1]/z[i]),i=0..2*N-1) / (2*Pi));
end:

# For a homogeneous quadratic map q : R4 -> R, return the matrix M
# such that q(x) = x^T M x.

quadratic_coeffs := proc(u)
 local M,i,j,c;

 M := Matrix(4,4,shape=symmetric):
 for i from 1 to 4 do M[i,i] := coeff(u,x[i],2); od:
 
 for i from 1 to 3 do 
  for j from i+1 to 4 do 
   c := coeff(coeff(u,x[i],1),x[j],1)/2;
   M[i,j] := c;
   M[j,i] := c;
  od:
 od:

 return M;
end:

# Construct a matrix of coefficients for a discrete Fourier transform.
# This will use 2*N sample points and return a trigonometric polynomial
# of degree d.

set_fourier_matrix := proc(N,d)
 global fourier_N,fourier_d,fourier_matrix;
 local Pi0,T,i,j,k;

 Pi0 := evalf(Pi);
 T := Matrix(2*d+1,2*N):
 for i from 1 to 2*N do 
  T[1,i] := 1/(2*N);
  for k from 1 to d do 
   T[2*k  ,i] := sin(i*k*Pi0/N)/N;
   T[2*k+1,i] := cos(i*k*Pi0/N)/N;
  od:
 od:

 fourier_N := N;
 fourier_d := d;
 fourier_matrix := T;
 return T;
end:

set_fourier_matrix(480,12):

# Calculate an approximate Fourier series for bef o b, for a function
# b : R2 -> S2 with b(t + 2*Pi,s) = b(t,s).  The result is returned as
# a table with many different entries.

fourier_approx := proc(b)
 local t,c,Pi0,d,N,U,F,m,k,e,cxyz,cuvw;

 c := table():
 Pi0 := evalf(Pi);
 d := fourier_d;
 N := fourier_N;
 U := map(evalf,Transpose(Matrix([u[0],v[0],w[0]])));
 e := 10.^(-3);

 c["vals"]    := [seq(evalf(b(i*Pi0/N, 0)),i=1..2*N)];
 c["offset0"] := [seq(evalf(b(i*Pi0/N, e)),i=1..2*N)];
 c["offset1"] := [seq(evalf(b(i*Pi0/N,-e)),i=1..2*N)];

 c["vals_be"]    := map(bef,c["vals"]);
 c["offset0_be"] := map(bef,c["offset0"]);
 c["offset1_be"] := map(bef,c["offset1"]);
 c["vals_dbe"]   :=
  [seq((c["offset0_be"][i] -~ c["offset1_be"][i]) /~ (2*e),i=1..2*N)];
 
 c["coeffs_be"]      := fourier_matrix . Matrix(c["vals_be"]);
 c["uvw_coeffs_be"]  := c["coeffs_be"] . U;
 c["coeffs_dbe"]     := fourier_matrix . Matrix(c["vals_dbe"]);
 c["uvw_coeffs_dbe"] := c["coeffs_dbe"] . U;

 for k in ["coeffs_be","uvw_coeffs_be","coeffs_dbe","uvw_coeffs_dbe"] do
  c[k] := trim(c[k],10.^(-6));
 od:

 F := [1,seq(op([sin(k*t),cos(k*t)]),k=1..d)];
 c["approx_be"]  := unapply(convert(Transpose(Vector(F)) . c["coeffs_be" ],list),t);
 c["approx_dbe"] := unapply(convert(Transpose(Vector(F)) . c["coeffs_dbe"],list),t);
 c["approx"] := unapply(c["approx_be"](t) +~ c["approx_dbe"](t) *~ s,t,s);

 for k in ["coeffs_be","uvw_coeffs_be","coeffs_dbe","uvw_coeffs_dbe"] do
  c[k] := convert(c[k],listlist);
 od:

 return eval(c):
end:

if false then
 vband_approx := table():
 printf("hband\n");
 hband_approx := fourier_approx(hband):
 printf("vband 0\n");
 vband_approx[0] := fourier_approx(vband(0)):
 printf("vband 1\n");
 vband_approx[Pi/6] := fourier_approx(vband(Pi/6)):
 printf("wband\n");
 wband_approx := fourier_approx(wband):
 save(hband_approx,vband_approx,wband_approx,
      cat(data_dir,"/boys_approx.m")):
else
 read(cat(data_dir,"/boys_approx.m")):
fi:

make_approx_plot := proc(a)
 a["plot"] := 
  plot3d(a["approx"](t,s),t=0..2*Pi,s=-0.1..0.1,
         style=patchnogrid,scaling=constrained,axes=none,args[2..-1]):
 return a["plot"];
end:

make_approx_plots := proc()
 global ribbon_plot;
 local opts;
 
 make_approx_plot(hband_approx,numpoints=5000):
 make_approx_plot(vband_approx[0],numpoints=8000):
 make_approx_plot(vband_approx[Pi/6],numpoints=5000):
 make_approx_plot(wband_approx,numpoints=5000):

 opts := t=0..2*Pi,s=-0.02..0.02,numpoints=6000,style=patchnogrid:

 ribbon_plot := 
  display(
   plot3d(vband_approx[0]["approx"](t,s),             opts,colour=red),
   plot3d(rot(vband_approx[0]["approx"](t,s)),        opts,colour=red),
   plot3d(rot(rot(vband_approx[0]["approx"](t,s))),   opts,colour=red),
   plot3d(vband_approx[Pi/6]["approx"](t,s),          opts,colour=blue),
   plot3d(rot(vband_approx[Pi/6]["approx"](t,s)),     opts,colour=blue),
   plot3d(rot(rot(vband_approx[Pi/6]["approx"](t,s))),opts,colour=blue),
   plot3d(hband_approx["approx"](t,s),                opts,colour=green),
   plot3d(wband_approx["approx"](t,s),                opts,colour=magenta),
   scaling=constrained,axes=none
  );

end:

# Given asome approximate Fourier transforms, try to work out the general
# form.  For coefficients of small absolute value, we assume that they
# are really supposed to be zero.  For coefficients that are sufficiently
# cloe, we assume that they should actually be the same.  Signs are
# inserted to ensure that the values of all parameters should be positive.

reset_outline := proc()
 global outline_k,outline_a;
 outline_k := 0;
 outline_a := table():
end:

reset_outline():

make_outline := proc(b)
 global outline_k,outline_a;
 local p,q,i,j,k,m,vp,d,x,F,found;

 p := [op(map(op,b["uvw_coeffs_be"])),
       op(map(op,b["uvw_coeffs_dbe"]))];

 q := NULL:

 for i from 1 to nops(p) do
  vp := p[i];
  if abs(vp) < 0.05 then
   q := q,0;
  else
   found := false;
   for j from 1 to outline_k do 
    if abs(vp - outline_a[j]) < 0.001 then
     q := q,a[j];
     found := true;
     break;
    fi;
    if abs(vp + outline_a[j]) < 0.001 then
     q := q,-a[j];
     found := true;
     break;
    fi;
   od:
   if not(found) then
    outline_k := outline_k + 1;
    outline_a[outline_k] := abs(vp);
    q := q,signum(vp) * a[outline_k];
   fi;
  fi;
 od:
 
 q := [q];
 
 m := nops(q)/6;
 d := (m-1)/2;
 q := [[seq([q[3*i-2],q[3*i-1],q[3*i]],i=1..m)],
       [seq([q[3*i-2],q[3*i-1],q[3*i]],i=m+1..2*m)]];

 b["uvw_coeffs_be_outline"]  := q[1];
 b["uvw_coeffs_dbe_outline"] := q[2];

 x := [0,0,0];
 F := [1,seq(op([sin(k*t),cos(k*t)]),k=1..d)];

 b["outline_be"] := unapply(
 add(F[i] * q[1][i][1],i=1..m) *~ u[0] +~ 
 add(F[i] * q[1][i][2],i=1..m) *~ v[0] +~ 
 add(F[i] * q[1][i][3],i=1..m) *~ w[0],t);

 b["outline_dbe"] := unapply(
 add(F[i] * q[2][i][1],i=1..m) *~ u[0] +~ 
 add(F[i] * q[2][i][2],i=1..m) *~ v[0] +~ 
 add(F[i] * q[2][i][3],i=1..m) *~ w[0],t);
end:

# Here we find the general form of the Fourier coefficients for bef o f
# with f in {hband, vband(0), vband(Pi/6), wband}.  Then we construct a list
# of relations that must be imposed to ensure that the approximations fit
# together correctly and have the expected behaviour at the points u[i].

find_approx_form := proc()
 global approx_form_rels,approx_form_sols;
 local t;
 
 reset_outline():
 make_outline(hband_approx):
 make_outline(vband_approx[0]):
 make_outline(vband_approx[Pi/6]):
 make_outline(wband_approx):

 approx_form_rels := expand(simplify(map(op,expand([
 hband_approx["outline_be"](0) -~ vband_approx[0]["outline_be"](0),
 hband_approx["outline_be"](Pi/6) -~ vband_approx[Pi/6]["outline_be"](0),
 vband_approx[0]["outline_be"](Pi/2) -~ u[0],
 vband_approx[Pi/6]["outline_be"](Pi/2) -~ u[0],
 vband_approx[0]["outline_be"](Pi - arctan(sqrt(2)/4)) -~ u[4],
 vband_approx[0]["outline_be"](   - arctan(sqrt(2)/4)) -~ u[4],
 wband_approx["outline_be"](     Pi/6,0) -~ u[6],
 wband_approx["outline_be"]( 3 * Pi/6,0) -~ u[4],
 wband_approx["outline_be"]( 5 * Pi/6,0) -~ u[5],
 wband_approx["outline_be"]( 7 * Pi/6,0) -~ u[6],
 wband_approx["outline_be"]( 9 * Pi/6,0) -~ u[4],
 wband_approx["outline_be"](11 * Pi/6,0) -~ u[5],
 wband_approx["outline_be"](        0,0) -~ hband_approx["outline_be"](15*Pi/6,0),
 wband_approx["outline_be"](     Pi/3,0) -~ hband_approx["outline_be"](13*Pi/6,0),
 wband_approx["outline_be"]( 2 * Pi/3,0) -~ hband_approx["outline_be"](11*Pi/6,0),
 wband_approx["outline_be"]( 3 * Pi/3,0) -~ hband_approx["outline_be"]( 9*Pi/6,0),
 wband_approx["outline_be"]( 4 * Pi/3,0) -~ hband_approx["outline_be"]( 7*Pi/6,0),
 wband_approx["outline_be"]( 5 * Pi/3,0) -~ hband_approx["outline_be"]( 5*Pi/6,0),
 map(coeffs,expand(hband_approx["outline_be"](t-2/3*Pi)   -~   rot(hband_approx["outline_be" ](t))),{sin(t),cos(t)}),
 map(coeffs,expand(hband_approx["outline_dbe"](t-2/3*Pi)  -~   rot(hband_approx["outline_dbe"](t))),{sin(t),cos(t)}),
 map(coeffs,expand(hband_approx["outline_be"](t+Pi/3)     -~   rot(hband_approx["outline_be" ](t))),{sin(t),cos(t)}),
 map(coeffs,expand(hband_approx["outline_dbe"](t+Pi/3)    +~   rot(hband_approx["outline_dbe"](t))),{sin(t),cos(t)}),
 map(coeffs,expand(vband_approx[0]["outline_be"](t+Pi)    -~ vband_approx[   0]["outline_be" ](t)) ,{sin(t),cos(t)}),
 map(coeffs,expand(vband_approx[0]["outline_dbe"](t+Pi)   +~ vband_approx[   0]["outline_dbe"](t)) ,{sin(t),cos(t)}),
 map(coeffs,expand(vband_approx[Pi/6]["outline_be"](t+Pi) -~ vband_approx[Pi/6]["outline_be" ](t)) ,{sin(t),cos(t)}),
 map(coeffs,expand(vband_approx[Pi/6]["outline_dbe"](t+Pi)-~ vband_approx[Pi/6]["outline_dbe"](t)) ,{sin(t),cos(t)}),
 map(coeffs,expand(wband_approx["outline_be"](t-Pi/3)     -~  rot(wband_approx["outline_be"  ](t))),{sin(t),cos(t)}),
 simplify(expand(dp(hband_approx["outline_dbe"](Pi/12),u[0]))),
 #simplify(expand(dp(wband_approx["outline_dbe"](Pi/12),u[0]))),
 simplify(expand(dp(vband_approx[0]["outline_dbe"](Pi/6),u[0]))),
 simplify(expand(dp(vband_approx[Pi/6]["outline_dbe"](Pi/2),u[0]))),
 NULL])))):

 approx_form_sols := solve(approx_form_rels);
end:

make_boys_cube_complex := proc()
 global boys_cube_complex;
 local N,T,V,P,E,F,C,i,j,k,e,a;
 
 T := table():
 N := 50;
 
 V := [seq(i,i=0..N-1)];
 T["vertices"] := V;

 P := table():
 
 P[ 0] := [ 2, 2, 2]; P[ 1] := [ 2, 2,-2]; P[ 2] := [ 2,-2, 2]; P[ 3] := [-2, 2, 2];
 P[ 4] := [ 2,-2,-2]; P[ 5] := [-2, 2,-2]; P[ 6] := [-2,-2, 2]; P[ 7] := [-2,-2,-2];
 P[ 8] := [ 2, 2, 0]; P[ 9] := [ 2, 0, 2]; P[10] := [ 0, 2, 2]; P[11] := [ 0,-2,-2];
 P[12] := [-2, 0,-2]; P[13] := [-2,-2, 0]; P[14] := [ 2, 0,-2]; P[15] := [ 2,-2, 0];
 P[16] := [ 0,-2, 2]; P[17] := [-2, 0, 2]; P[18] := [-2, 2, 0]; P[19] := [ 0, 2,-2];
 P[20] := [ 2, 0, 0]; P[21] := [ 0, 0, 2]; P[22] := [ 0, 2, 0];
 P[23] := [-2, 0, 0]; P[24] := [ 0, 0,-2]; P[25] := [ 0,-2, 0];
 P[26] := [ 2, 1, 1]; P[27] := [ 2,-1, 1]; P[28] := [ 2,-1,-1]; P[29] := [ 2, 1,-1];
 P[30] := [ 1, 1, 2]; P[31] := [-1, 1, 2]; P[32] := [-1,-1, 2]; P[33] := [ 1,-1, 2];
 P[34] := [ 1, 2, 1]; P[35] := [ 1, 2,-1]; P[36] := [-1, 2,-1]; P[37] := [-1, 2, 1];
 P[38] := [-2,-1,-1]; P[39] := [-2, 1,-1]; P[40] := [-2, 1, 1]; P[41] := [-2,-1, 1];
 P[42] := [-1,-1,-2]; P[43] := [ 1,-1,-2]; P[44] := [ 1, 1,-2]; P[45] := [-1, 1,-2];
 P[46] := [-1,-2,-1]; P[47] := [-1,-2, 1]; P[48] := [ 1,-2, 1]; P[49] := [ 1,-2,-1];

 T["embedding_dim"] := 3;
 T["embedding"] := eval(P);
 T["cube_embedding"] := eval(P);

 T["sphere_embedding"] := table():
 for i in V do
  a := P[i];
  a := a /~ sqrt(add(a[i]^2,i=1..3));
  T["sphere_embedding"][i] := a;
 od:
 
 E := NULL:
 for i from 0 to N-1 do
  for j from i + 1 to N-1 do
   a := sort(map(abs,P[j] -~ P[i]));
   if modp(P[i],2) *~ modp(P[j],2) = [0,0,0] and 
      (a = [0,1,1] or a = [0,0,2]) then 
    E := E,[i,j];
   fi;
  od:
 od:

 E := [E];
 T["edges"] := E;

 F := NULL;
 for e in E do
  for k from e[2] + 1 to N-1 do
   if member([e[1],k],E) and member([e[2],k],E) then
    F := F,[op(e),k];
   fi;
  od:
 od:

 F := [F];
 T["faces"] := F;
 T["max_simplices"] := F;
 
 T["vertex_index"] := table():

 for i in V do
  T["vertex_index"][T["cube_embedding"][i]] := i;
  T["vertex_index"][T["sphere_embedding"][i]] := i;
 od:

 T["hedges"] := [14,28,15,48,16,32,17,40,18,36,19,44,14]:
 T["hedges"] := map(sort,[seq([T["hedges"][i],T["hedges"][i+1]],i=1..nops(T["hedges"])-1)]):

 T["wedges"] := [1,14,4,15,2,16,6,17,3,18,5,19,1]:
 T["wedges"] := map(sort,[seq([T["wedges"][i],T["wedges"][i+1]],i=1..nops(T["wedges"])-1)]):

 C := table():

 for e in T[ "edges"] do C[e] := grey;  od:
 for e in T["hedges"] do C[e] := cyan;  od:
 for e in T["wedges"] do C[e] := black; od:

 C[[ 0, 8]] := orange: C[[ 0, 9]] := orange: C[[ 0,10]] := orange: C[[ 1, 8]] := orange:
 C[[ 2, 9]] := orange: C[[ 3,10]] := orange: C[[ 7,11]] := orange: C[[ 7,12]] := orange:
 C[[ 7,13]] := orange: C[[ 4,11]] := orange: C[[ 5,12]] := orange: C[[ 6,13]] := orange:
 C[[ 0,26]] := green:  C[[ 0,34]] := green:  C[[ 0,20]] := green:  C[[20,26]] := green:
 C[[22,34]] := green:  C[[21,30]] := green:  C[[20,28]] := green:  C[[22,36]] := green:
 C[[21,32]] := green:  C[[ 4,28]] := green:  C[[ 5,36]] := green:  C[[ 6,32]] := green:
 C[[ 1,44]] := green:  C[[ 2,48]] := green:  C[[ 3,40]] := green:  C[[24,44]] := green:
 C[[25,48]] := green:  C[[23,40]] := green:  C[[24,42]] := green:  C[[25,46]] := green:
 C[[23,38]] := green:  C[[ 7,42]] := green:  C[[ 7,46]] := green:  C[[ 7,38]] := green:

 T["edge_colour"] := eval(C):

 T["cube_plot"] := 
 display(
  plot3d([ s, t,-1] *~ 1.99,s=-1..1,t=-1..1,style=patchnogrid,colour=grey),
  plot3d([ s, t, 1] *~ 1.99,s=-1..1,t=-1..1,style=patchnogrid,colour=grey),
  plot3d([ s,-1, t] *~ 1.99,s=-1..1,t=-1..1,style=patchnogrid,colour=grey),
  plot3d([ s, 1, t] *~ 1.99,s=-1..1,t=-1..1,style=patchnogrid,colour=grey),
  plot3d([-1, s, t] *~ 1.99,s=-1..1,t=-1..1,style=patchnogrid,colour=grey),
  plot3d([ 1, s, t] *~ 1.99,s=-1..1,t=-1..1,style=patchnogrid,colour=grey),
  seq(line(P[e[1]],P[e[2]],colour=T["edge_colour"][e]),e in T["edges"]),
  axes=none
 );

 boys_cube_complex := eval(T):
 return eval(T);
end:

refine_boys_cube_complex := proc()
 global refined_boys_cube_complex;
 local T0,TT,S,P,p;
 T0 := `condense/simplicial_complex`(make_boys_cube_complex()):
  `set_edges/simplicial_complex`(T0):
  `set_faces/simplicial_complex`(T0):
  `normalise_embedding/simplicial_complex`(T0):
 T0["boys_embedding"] := map(bef,eval(T0["embedding"])):
 TT := [eval(T0)]:

# P := [0.8,0.6,0.4,0.3]:
 P := [0.8]:
 
 for p in P do 
  S := select(e -> boys_edge_length(T0)(e) > p,T0["edges"]):
  T0 := `partial_triangular_subdivision/simplicial_complex`(T0,S):
  `normalise_embedding/simplicial_complex`(T0):
  T0["sphere_embedding"] := eval(T0["embedding"]):
  T0["boys_embedding"] := map(evalf,map(bef,T0["embedding"])):
  TT := [op(TT),eval(T0)]:
 od:

 refined_boys_cube_complex := eval(T0):

# save(refined_boys_cube_complex,cat(data_dir,"/refined_boys_cube_complex.m")):

 return eval(T0):
end:

edge_length      := (T) -> e -> `d_2/R`(3)(T["embedding"][e[1]],T["embedding"][e[2]]):
boys_edge_length := (T) -> e -> `d_2/R`(3)(T["boys_embedding"][e[1]],T["boys_embedding"][e[2]]):

edge_length_plot      := (T) ->
 listplot(sort(map(edge_length(T),[op(T["edges"])]))):
boys_edge_length_plot := (T) ->
 listplot(sort(map(boys_edge_length(T),[op(T["edges"])]))):

homogeneous_basis := proc(d,x)
 return [seq(seq(x[1]^i*x[2]^j*x[3]^(d-i-j),j=0..d-i),i=0..d)];
end:

extend_cyclic := proc(p)
 local x;

 return unapply([p([x[1],x[2],x[3]]),
                 p([x[2],x[3],x[1]]),
                 p([x[3],x[1],x[2]])],x)
end:

maybe_extend_cyclic := proc(p) 
 if type(p(x),list) then
  return eval(p);
 else
  return extend_cyclic(p);
 fi;
end:

make_quadric := proc()
 global general_quadric0,general_quadric,quadric_point_rels,quadric_point_sol,
  special_quadric0,special_quadric,hband_quadric,vband_quadric;
 local B,x,rels,sol;
 
 B := homogeneous_basis(4,x);
 general_quadric0 := unapply(add(a[i] * B[i],i=1..nops(B)),x):
 general_quadric := extend_cyclic(eval(general_quadric0));

 quadric_point_rels := [
  op(general_quadric(u[0]) -~ u[0]),
  op(general_quadric(u[1]) +~ u[1])
 ]:

 hband_quadric := 
  map(collect,combine(simplify(expand(general_quadric(hband(t,0))))),{seq(cos(k*t),k=1..10),seq(sin(k*t),k=1..10)}):

 vband_quadric[0] := 
  map(collect,combine(simplify(expand(general_quadric(vband(0)(t,0))))),{seq(cos(k*t),k=1..10),seq(sin(k*t),k=1..10)}):

 vband_quadric[Pi/6] := 
  map(collect,combine(simplify(expand(general_quadric(vband(Pi/6)(t,0))))),{seq(cos(k*t),k=1..10),seq(sin(k*t),k=1..10)}):

 quadric_point_sol := solve(quadric_point_rels);

 # We now construct a 6-parameter family of quadrics such that
 # - u[0] maps to u[0], with specified behaviour on the tangent space
 # - u[4] maps to u[4] (which forces u[5] and u[6] to also be fixed, by equivariance)
 # - pol(Pi/3,Pi/6) maps to zero.
 special_quadric := eval(general_quadric):
 rels := simplify(expand({
  op(special_quadric(u[0]) -~ u[0] /~ sqrt(2)), 
  op(map(coeffs,simplify(map(rem,expand(
     special_quadric(u[0] +~ t *~ v[0]) -~ special_quadric(u[0]) -~ t *~ ([-1,2,-1]/~sqrt(2))),t^2,t)),t)),
  op(map(coeffs,simplify(map(rem,expand(
     special_quadric(u[0] +~ t *~ w[0]) -~ special_quadric(u[0]) -~ t *~ ([-1,0,1]*~sqrt(3/2))),t^2,t)),t)),
  op(special_quadric(u[4]) -~ u[4] /~ sqrt(2)),
  op(special_quadric(pol(Pi/3,Pi/6)))
 })):
 sol := solve(rels,{seq(a[i],i=7..15)}):
 special_quadric := unapply(expand(subs(sol,special_quadric(x))),x):
 special_quadric0 := unapply(special_quadric(x)[1],x);
end:

make_sextic := proc()
 global general_sextic0,general_sextic,sextic_point_rels,sextic_point_sol,
  hband_sextic,vband_sextic;
 local B,x;
 
 B := homogeneous_basis(6,x);
 general_sextic0 := unapply(add(a[i] * B[i],i=1..nops(B)),x):
 general_sextic := extend_cyclic(general_sextic0);

 sextic_point_rels := [
  op(general_sextic(u[0]) -~ u[0]),
  op(general_sextic(u[1]) +~ u[1])
 ]:

 hband_sextic := 
  map(collect,combine(simplify(expand(general_sextic(hband(t,0))))),{seq(cos(k*t),k=1..10),seq(sin(k*t),k=1..10)}):

 vband_sextic[0] := 
  map(collect,combine(simplify(expand(general_sextic(vband(0)(t,0))))),{seq(cos(k*t),k=1..10),seq(sin(k*t),k=1..10)}):

 vband_sextic[Pi/6] := 
  map(collect,combine(simplify(expand(general_sextic(vband(Pi/6)(t,0))))),{seq(cos(k*t),k=1..10),seq(sin(k*t),k=1..10)}):

 sextic_point_sol := solve(sextic_point_rels);
end:

check_sextic := proc()
 local x,xx;
 xx := [x[1],x[2],x[3]];
 
 _ASSERT(
  general_sextic(-~xx) -~ general_sextic(xx) = [0$3],
  "general_sextic is Z/2-equivariant"
 );
 
 _ASSERT(
  general_sextic(rot(xx)) -~ rot(general_sextic(xx)) = [0$3],
  "general_sextic is Z/3-equivariant"
 );
end:

make_quadric():
make_sextic():

refine_sextic_a := proc()
 global sextic_a0,sextic_a;
 local sextic_rels,sextic_sol;
 
 sextic_rels := [op(sextic_point_rels),
   seq(coeff(combine(expand(dp(u[0],hband_sextic))),f,1), f in [cos(2*t),sin(4*t),cos(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(v[0],hband_sextic))),f,1), f in [cos(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(w[0],hband_sextic))),f,1), f in [sin(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(u[0],vband_sextic[0]))),f,1), f in [sin(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(v[0],vband_sextic[0]))),f,1), f in [sin(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(w[0],vband_sextic[0]))),f,1), f in [cos(2*t),sin(4*t),cos(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(u[0],vband_sextic[Pi/6]))),f,1), f in [sin(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(v[0],vband_sextic[Pi/6]))),f,1), f in [sin(4*t),sin(6*t),cos(6*t)]),
   seq(coeff(combine(expand(dp(w[0],vband_sextic[Pi/6]))),f,1), f in [cos(2*t),sin(4*t),cos(4*t),sin(6*t),cos(6*t)])
 ]:

 sextic_sol := solve(sextic_rels);
 sextic_a0 := unapply(simplify(expand(subs(sextic_sol,general_sextic0(x)))),x);
 sextic_a  := unapply(simplify(expand(subs(sextic_sol,general_sextic(x)))) ,x);
end:

refine_sextic_b := proc()
 global sextic_b0,sextic_b;
 local sextic_rels,sextic_sol;
 
 sextic_rels := [op(sextic_point_rels),
  op(map(coeffs,expand(simplify(expand(map(convert,map(series,expand(general_sextic(hband(t,s)) -~ triangle_mobius(t,s)),s=0,2),polynom,s)))),{sin(t),cos(t),s}))
 ]:

 sextic_sol := solve(sextic_rels);
 sextic_b0 := unapply(simplify(expand(subs(sextic_sol,general_sextic0(x)))),x);
 sextic_b  := unapply(simplify(expand(subs(sextic_sol,general_sextic(x)))) ,x);
end:

compare_terms := (u,v) -> 
 abs(subs({x[1]=1,x[2]=1,x[3]=1},u)) < abs(subs({x[1]=1,x[2]=1,x[3]=1},v));

sort_terms := proc(p)
 local T;
 T := `if`(type(p,`+`),[op(p)],[p]);
 return sort(T,compare_terms);
end:

# Precompute coefficients for approximate integration over S2 using the
# triangulation T.
int_setup := proc(T)
 local a,b,c,d,f;
 T["face_area"] := table():
 T["face_centre"] := table():
 T["face_centre_be"] := table():
 for f in T["faces"] do
  a,b,c := op(map(i -> T["embedding"][i],f));
  d := a +~ b +~ c;
  d := d /~ `norm_2/R`(3)(d);
  T["face_centre"][f] := d;
  T["face_centre_be"][f] := bef(d);
  T["face_area"][f] := spherical_triangle_area(a,b,c);
 od:
end:

# Integration over S2, normalised to have total area 1.
sphere_int := proc(g,T)
 local u,f;
 u := 0;
 for f in T["faces"] do 
  u := u + (g(T["face_centre"][f]) * T["face_area"][f]);
 od:
 u := evalf(u / (4*Pi));
 return u;
end:

sphere_int_be := proc(g,T)
 local u,f;
 u := [0,0,0];
 for f in T["faces"] do 
  u := u +~ (g(T["face_centre"][f]) * T["face_area"][f]) *~ T["face_centre_be"][f];
 od:
 u := evalf(u / (4*Pi));
 return u;
end:

# Symbolic integration over the sphere, again normalised to have area 1
sint0 := proc(u) 
 option remember;
 local v;
 v := subs({x[1]=sin(s)*cos(t),x[2]=sin(s)*sin(t),x[3]=cos(s)},u) * sin(s)/(4*Pi);
 v := expand(convert(v,exp));
 v := int(v,t=0..2*Pi);
 v := int(v,s=0..Pi);
 return v;
end:

sint := apply_linear(sint0,realcons):

ips := (u,v) -> evalf(sint(expand(u*v))):

# Faster symbolic integration for polynomials
sintp0 := proc(u)
 local c,d,i;
 c := 1;
 for i from 1 to 3 do 
  d[i] := degree(u,x[i]);
 od:
 if u <> x[1]^d[1] * x[2]^d[2] * x[3]^d[3] then
  error("Argument is not monomial");
 fi:
 if modp(d[1],2) = 1 or modp(d[2],2) = 1 or modp(d[3],2) = 1 then
  return 0;
 fi;

 return doublefactorial(d[1]-1) * 
        doublefactorial(d[2]-1) * 
        doublefactorial(d[3]-1) /
        doublefactorial(d[1]+d[2]+d[3]+1);
end:

sintp := apply_linear(sintp0,realcons):

ipsp := (u,v) -> evalf(sintp(expand(u*v))):

make_orthonormal := proc(B,T)
 local Y,i,j;

 Y := table():
 for i from 1 to nops(B) do 
  Y[i] := B[i]:
  for j from 1 to i-1 do 
   Y[i] := expand(Y[i] - sphere_int(unapply(Y[i]*Y[j],x),T) * Y[j]);
  od:
  Y[i] := expand(Y[i] / sqrt(sphere_int(unapply(Y[i]^2,x),T0))):
 od:

 return eval(Y):
end:

make_immersion := proc(p,T_)
 local pp,T,s,t;

 pp := p;
 if not(type(pp,function)) then pp := unapply(pp,x); fi;
 if not(type(pp(x),list)) then
  pp := unapply([pp([x[1],x[2],x[3]]),
                 pp([x[2],x[3],x[1]]),
                 pp([x[3],x[1],x[2]])],x);
 fi;
 
 if nargs > 1 then T := eval(T_) else T := table(): fi;
 T["map"] := eval(pp);
 T["map0"] := unapply(pp(x)[1],x);

 pp := T["map0"](pol(s,t));
 pp := combine(expand(simplify(evalf(expand(pp)))));
 T["pol_map0"] := unapply(pp,s,t);
 T["pol_map"] :=
  unapply(evalf([pp(s,t),pp(s+2*Pi/3,t),pp(s,t-2*Pi/3)]),s,t);

 return eval(T);
end:

make_plots := proc(T)
 local opts,p;
 opts := style=patchnogrid,scaling=constrained,axes=none;
 T["plot"] := plot3d(T["pol_map"](s,t),t=0..2*Pi,s=0..Pi,opts,numpoints=8000);
 T["hband_plot"] := plot3d(T["map"](hband(t,s)),t=0..2*Pi,s=-0.2..0.2,opts,numpoints=8000);
 T["vband_plot"] := table():
 for p in [0,Pi/6] do 
  T["vband_plot"][p] := plot3d(T["map"](vband(p)(t,s)),t=0..2*Pi,s=-0.2..0.2,opts,numpoints=8000);
 od:
 
 return T["plot"];
end:

orth_proj := (x) -> <
 <x[2]^2+x[3]^2|-x[1]*x[2]|-x[1]*x[3]>,
 <-x[1]*x[2]|x[1]^2+x[3]^2|-x[2]*x[3]>,
 <-x[1]*x[3]|-x[2]*x[3]|x[1]^2+x[2]^2>
>;

segment_max := proc(f)
 local T,N,s_step,t_step,m0,s0,t0,i,j,sol;
 T := f(pol(s,t));
 N := 6;
 s_step := evalf(Pi/(2*N)):
 t_step := evalf(2*Pi/(3*N)):
 m0 := 0;
 s0 := 0;
 t0 := 0;
 for i from 0 to N-1 do 
  for j from 0 to N-1 do
   try 
    sol :=   
     NLPSolve(T,[],s=i*s_step..(i+1)*s_step,t=j*t_step..(j+1)*t_step,
              maximize=true,method=sqp);
    if sol[1] > m0 then
     m0 := sol[1];
     s0 := subs(sol[2],s);
     t0 := subs(sol[2],t);
    fi;
   catch:
   end try:
  od:
 od:

 return [m0,s0,t0]
end:

# If p : R^3 -> R^3 then jac(p)(x) is a 3x3 positive semidefinite
# matrix with 0 as one eigenvalue.  The map p is immersive at a
# point x in S2 iff the other two eigenvalues of jac(p)(x) are
# strictly positive.  If p(x) is a homogeneous polynomial of degree
# d in the variables x[i], then jac(p)(x) is homogeneous of degree
# 2 in the coefficients of p, and homogeneous of degree 2d in the
# variables x[i].

jac := proc(p)
 local J0,P,J,x;
 J0 := Matrix([seq([seq(diff(p(x)[i],x[j]),j=1..3)],i=1..3)]):
 P := orth_proj(x);
 J := map(expand,P . Transpose(J0) . J0 . P);
 return unapply(J,x);
end:

jac_det := proc(p)
 local J,f,t,x;
 J := jac(p)(x);
 f := Determinant(t * IdentityMatrix(3) - J);
 return unapply(coeff(f,t,1),x);
end:

jac_det_min := proc(p)
 local f,m0,s0,t0;
 f := unapply(-jac_det(p)(x),x);
 m0,s0,t0 := op(segment_max(f));
 return [-m0,s0,t0];
end:

jac_det_plot := proc(T)
 local p;
 p := T["map"];
 
 T["jac_det_plot"] := 
  display(
   plot3d(0,s=0..Pi/2,t=0..2*Pi/3,colour=grey,style=patchnogrid),
   plot3d(jac_det(p)(pol(s,t)),s=0..Pi/2,t=0..2*Pi/3)
  );
 return T["jac_det_plot"];
end:

# This returns a function of x measuring the failure of p to be
# locally isometric at x.  It is easy to evaluate and integrate,
# but does not strongly penalise points where the Jacobian becomes
# singular.  If p is homogeneous quadric, then jac_dev_a(p)
jac_dev_a := proc(p)
 local J,P,E;
 J := jac(p)(x);
 P := orth_proj(x);
 E := add(add((J[i,j] - P[i,j])^2,j=1..3),i=1..3);
 return unapply(E,x);
end:

# This is a different measure of the failure of p to be a local
# isometry.  It is less easy to compute but strongly penalises
# points where the Jacobian becomes singular.
jac_dev_b := proc(p)
 local J,f,c1,c2,x;
 J := jac(p)(x);
 f := Determinant(t * IdentityMatrix(3) - J);
 c1 := - coeff(f,t,2);
 c2 := coeff(f,t,1);
 return unapply(c1*(1+1/c2),x);
end:

jac_dev_a_max := (p) -> segment_max(jac_dev_a(p));

jac_dev_b_max := (p) -> segment_max(jac_dev_b(p));

# This takes a polynomial map p : R3 -> R3 (which may depend linearly
# on some parameters) and another polynomial map p_start : R3 -> R3
# (with no parameters).  It specialises the parameters in p to make it
# as close as possible (as measured by coefficients) to p_start.
# Starting from there, it adjusts the parameters to minimize the
# value of jac_dev_b_max.
optimise_immersion := proc(p,p_start)
 global F,F_n,F_vars,F_best,F_vals;
 local pp,pp_start,p0,err,sol,aa0;

 pp := maybe_extend_cyclic(p);
 pp_start := maybe_extend_cyclic(p_start);

 F_vars := indets(pp(x)) minus {x[1],x[2],x[3]};
 F_n := nops(F_vars);
 p0 := unapply(subs({seq(F_vars[i] = a[i],i=1..F_n)},pp(x)),x);
 F_vals := table():
 F_best := NULL:

 err := evalf(expand(p0(x)[1] - pp_start(x)[1]));
 err := [coeffs(err,{x[1],x[2],x[3]})];
 err := expand(add(t^2,t in err));
 sol := solve({seq(diff(err,a[i]),i=1..F_n)}):
 aa0 := subs(sol,[seq(a[i],i=1..F_n)]);

 F := proc(aa)
  local p1,m;
  global F_vals,F_best;
  p1 := unapply(evalf(subs({seq(a[i]=aa[i],i=1..F_n)},p0(x))),x);
  m := jac_dev_b_max(p1);
  F_vals := [op(F_vals),[convert(aa,list),m]];
  if F_best = NULL or m[1] < F_best[2][1] then
   F_best := [convert(aa,list),m];
  fi;
  print(m[1]);
  return m[1];
 end:

 NLPSolve(F_n,F,initialpoint=Vector(aa0),method=nonlinearsimplex);
 return unapply(evalf(subs({seq(a[i] = F_best[1][i],i=1..F_n)},p0(x))),x); 
end:

sextics := table():

sextics[1] := make_immersion(
 0.264790817514485*x[2]*x[3]^5 + 
 0.310873678789934*x[2]^5*x[3] + 
 0.314356886190530*x[1]^6 + 
(-0.367461017219878)*x[1]^3*x[2]^3 + 
 0.520593122199589*x[1]^3*x[3]^3 +
 0.576919957376212*x[3]^6 + 
 0.916070813636660*x[1]^4*x[2]*x[3] + 
 1.08011357291557*x[1]*x[2]^4*x[3] + 
(-1.29574375446066)*x[1]^2*x[2]^4 + 
(-1.50136425744714)*x[2]^4*x[3]^2 +
 1.75322964015665*x[2]^3*x[3]^3 + 
 1.83297848992403*x[1]^4*x[3]^2 + 
 1.97193642230680*x[1]^3*x[2]^2*x[3] + 
 3.00614990897844*x[1]^2*x[2]*x[3]^3 + 
 3.14671754019206*x[2]^2*x[3]^4 + 
(-3.31538823843401)*x[1]^3*x[2]*x[3]^2 + 
 3.47953011385635*x[1]*x[2]^3*x[3]^2 +
(-3.48258924201893)*x[1]^2*x[2]^2*x[3]^2 + 
 3.68883801947675*x[1]^2*x[3]^4 + 
(-3.70117135607353)*x[1]*x[2]^2*x[3]^3 + 
 5.13825301199981*x[1]^2*x[2]^3*x[3]):

quadrics := table():

# This map is nice and simple and is equivariant for the full symmetry
# group of the tetrahedron.  There are double points on the intersections
# of the coordinate planes with S2, and the points +/- e[i] are all
# sent to the origin.  The map is not an immersion because the Jacobian
# is zero at [+/-1,+/-1,0]/sqrt(2) and permutations of that. 
quadrics[0] := make_immersion(
 sqrt(2)*x[2]*x[3]*(-2*x[1]^2+x[2]^2+x[3]^2)+(3*sqrt(3))*x[1]^2*x[2]*x[3]
);

quadrics["singular"] := eval(quadrics[0]);

# This is fitted to the original Boys embedding.  The pictures are nice but
# the minimal Jacobian determinant is very small.
quadrics[1] := make_immersion(
 2.22504534947546*x[1]^2*x[2]*x[3]+
 0.458129331010717*x[2]*x[3]^3+
 0.189460510525367*x[1]*x[2]*x[3]^2+
 0.707682203241314*x[2]^3*x[3]+
 0.188439848721650*x[1]*x[2]^2*x[3]+
 0.259985777619243*x[1]^3*x[3]+
 (-0.287042815821211)*x[1]*x[3]^3+
 1.76981740175627*x[1]^2*x[3]^2+
 0.118256474175355*x[2]^2*x[3]^2+
 (-0.478109121568119)*x[1]^3*x[2]+
 0.279208660926366*x[1]*x[2]^3+
 (-1.02732331413132)*x[1]^2*x[2]^2+
 (-0.127292231262611)*x[2]^4+
 0.812016127928750*x[3]^4+
 0.348555338251230*x[1]^4):

quadrics["boys"] := eval(quadrics[1]);

# This is chosen for simplicity.  The pictures are again nice and the minimal
# Jacobian determinant is a bit bigger than for quadric1, but still small.
quadrics[2]  := make_immersion(
 x[1]^2*x[3]*(x[2]+x[3])+(1/2)*(-1+3*sqrt(3))*x[2]*x[3]*(x[2]^2+x[3]^2)+
 sqrt(3)*x[3]^4-(1+sqrt(3))*x[1]^2*x[2]^2):

quadrics["simple"] := eval(quadrics[2]);

# The map quadric3 is a special case of special_quadric0 with
# max(jac_dev_b) minimized.

quadrics_a[3] :=
 [0.439109301326211, 1.00088884489061, 0.276971768183746,
  0.804297719366554, -0.228929556357166, -0.0920206086999537]:

quadrics[3] := make_immersion(
 evalf(sqrt(2) * subs({seq(a[i] = quadrics_a[3][i],i=1..6)},special_quadric0(x))));

quadrics[3]["a"] := quadrics_a[3];

quadrics["best"] := eval(quadrics[3]);

# This is Apery's quadric, up to linear changes of variables in the
# domain and codomain.  It sends u[0] to itself, and u[1] to u[6]
# to the origin.
quadrics[4] := make_immersion((
 (2 + 20*sqrt(2)) * x[1]^4 + 
 (2 - 10*sqrt(2)) * (x[2]^4 + x[3]^4) + 
 (10*sqrt(2) + 13) * x[1]^2 * (x[2]^2 + x[3]^2) + 
 27 * x[1] * x[2] * x[3] * (x[1]+x[2]+x[3]) +
 (13 - 20*sqrt(2)) * x[2]^2 * x[3]^2 + 
 9 * x[1]^3 * (x[2] + x[3]) + 
 9 * x[2] * x[3] * (x[2]^2 + x[3]^2) + 
 9 * x[1] * (x[2]^3 + x[3]^3) + 
 (9 + 20*sqrt(2)) * x[2] * x[3] * (x[2]^2 - x[3]^2) + 
 (10 * sqrt(2) - 9) * x[1] * (x[2]^3-x[3]^3) + 
 (10 * sqrt(2) - 9) * (-x[1]^3) * (x[2] - x[3])) / (20 * sqrt(3)));

quadrics["apery"] := eval(quadrics[4]);

# This is optimised in a similar way to quadric3 but with slightly
# different constraints
quadrics[5] := make_immersion(
 3.25245542513966246*x[1]^2*x[2]*x[3]+
 0.567045610094270236*x[1]^2*x[3]^2+
 0.506746342124321902*x[2]^3*x[3]+
 1.43695065673601552*x[2]*x[3]^3+
 0.506586664999783221*x[3]^4+
 (-1.07154585120271717)*x[1]^2*x[2]^2+
 (-0.137651281752026899)*x[2]^2*x[3]^2+
 (-0.0475300936088673548)*x[2]^4+
 (-0.0729799939799069125)*x[1]*x[3]^3+
 (0.600907939705055405)*x[1]*x[2]*x[3]^2+
 (-0.121589626981102178)*x[1]*x[2]^2*x[3]+
 (0.0173511518008154855)*x[1]*x[2]^3+
 0.194569620961009104*x[1]^3*x[3]+
 (-0.618259091505870884)*x[1]^3*x[2]+
 0.183094951469558120*x[1]^4);

find_double_direction := proc(T,x0,x1)
 local v0,v1,w0,w1,pv0,pv1,pw0,pw1,n0,n1,nn;
 v0 := evalf(u[0] -~ dp(u[0],x0) *~ x0);
 v0 := v0 /~ sqrt(dp(v0,v0));
 w0 := evalf(cross_product(x0,v0));
 v1 := evalf(u[0] -~ dp(u[0],x1) *~ x1);
 v1 := v1 /~ sqrt(dp(v1,v1));
 w1 := evalf(cross_product(x1,v1));
 pv0 := evalf(subs(t = 0,map(diff,T["map"](x0 +~ t *~ v0),t)));
 pw0 := evalf(subs(t = 0,map(diff,T["map"](x0 +~ t *~ w0),t)));
 pv1 := evalf(subs(t = 0,map(diff,T["map"](x1 +~ t *~ v1),t)));
 pw1 := evalf(subs(t = 0,map(diff,T["map"](x1 +~ t *~ w1),t)));
 n0 := cross_product(pv0,pw0);
 n1 := cross_product(pv1,pw1);
 nn := cross_product(n0,n1);
 nn := nn /~ sqrt(dp(nn,nn));
 return nn;
end:

find_double_point := proc(T,x0,y0,u0,d0)
 local pp,eqs,start,sol,xyz;

 pp := T["map"];
 eqs := {
  x[1]^2 + x[2]^2 + x[3]^2 - 1,
  y[1]^2 + y[2]^2 + y[3]^2 - 1,
  op(pp(x) -~ pp(y)),
  dp(pp(x),u0) - d0
 };
 start := {
  seq(x[i] = x0[i],i=1..3),
  seq(y[i] = y0[i],i=1..3)};
 sol := fsolve(eqs,start);
 xyz := evalf(subs(sol,
   [[x[1],x[2],x[3]],[y[1],y[2],y[3]],pp(x)]));
 if not(type(T["double_points"],list)) then
  T["double_points"] := []:
 fi:
 T["double_points"] := [op(T["double_points"]),xyz];
 return xyz;
end:

double_point_step := proc(T,e)
 local p,q,x0,y0,u0,d0;
 p := T["double_points"][-2];
 q := T["double_points"][-1];
 x0 := 2 *~ q[1] -~ p[1];
 y0 := 2 *~ q[2] -~ p[2];
 u0 := q[3] -~ p[3];
 u0 := evalf(u0 /~ sqrt(dp(u0,u0)));
 d0 := dp(q[3],u0) + e;
 return find_double_point(T,x0,y0,u0,d0);
end:

find_seam := proc(T,xyz0,u0,e_min,e_max)
 local pp,z0,z01,z02,r0,r1,c0,c1,dc0,dc1,N,M,F,i,aa,bb,a,b;
 
 pp := T["map"];

 N := 240:
 F := proc(e)
  local i;
  T["double_points"] := evalf([xyz0]):
  find_double_point(T,xyz0[1],xyz0[2],u0,e):
  for i from 1 to N do double_point_step(T,e); od:
  return table(["err" = dp(T["double_points"][N+1][3],u0)]);
 end:

 T["double_point_step_length"] := 
  brent_fsolve(F,e_min,e_max,false,false,10^(-7),10^(-7))[1];

 aa := T["double_points"][1];
 bb := T["double_points"][240];
 
 if evalf(`d_2/R`(3)(bb[1],aa[2])) < evalf(`d_2/R`(3)(bb[1],-~aa[2])) then 
  T["double_points_alt"] := [
   seq(T["double_points"][i][1],i=1..240),
   seq(T["double_points"][i][2],i=1..240),
   seq(-~ T["double_points"][i][1],i=1..240),
   seq(-~ T["double_points"][i][2],i=1..240),
   T["double_points"][1][1]]:
 else
  T["double_points_alt"] := [
   seq(T["double_points"][i][1],i=1..240),
   seq(-~ T["double_points"][i][2],i=1..240),
   seq(-~ T["double_points"][i][1],i=1..240),
   seq(T["double_points"][i][2],i=1..240),
   T["double_points"][1][1]]:
 fi;
 
 M := 20:
 for i from 0 to M do
  a[i] := add(T["double_points_alt"][j+1][1] * evalf(cos(Pi * (2 * i + 1) * j/480)),j=0..959)/480;
  b[i] := add(T["double_points_alt"][j+1][1] * evalf(sin(Pi * (2 * i + 1) * j/480)),j=0..959)/480;
 od:

 T["seam0"] := unapply(
   add(a[i] * cos((2 * i + 1) * t) + b[i] * sin((2 * i + 1) * t),i=0..M),t):

 T["seam"] := unapply([T["seam0"](t),T["seam0"](t+2*Pi/3),T["seam0"](t-2*Pi/3)],t):

 return NULL:
end:

double_points_plot := proc(T)
 local L;
 L := T["double_points"];
 display(
  usphere_plot,
  seq(point(x[1],colour=red),x in L),
  seq(point(x[2],colour=blue),x in L),
  seq(point(-~ x[1],colour=magenta),x in L),
  seq(point(-~ x[2],colour=cyan),x in L),
  axes=none,scaling=constrained
 );
end:

seam_plot := proc(T)
 spacecurve(T["seam"](t),t=0..2*Pi,colour=red,scaling=constrained,axes=none)
end:
