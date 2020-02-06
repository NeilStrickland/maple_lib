euler_angle_matrix := (t) -> 
<<cos(t[2])|
  -cos(t[3])*sin(t[2])|
  sin(t[2])*sin(t[3])>,
 <cos(t[1])*sin(t[2])|
  cos(t[1])*cos(t[2])*cos(t[3])-sin(t[1])*sin(t[3])|
  -cos(t[3])*sin(t[1])-cos(t[1])*cos(t[2])*sin(t[3])>,
 <sin(t[1])*sin(t[2])|
  cos(t[1])*sin(t[3])+cos(t[2])*cos(t[3])*sin(t[1])|
  cos(t[1])*cos(t[3])-cos(t[2])*sin(t[1])*sin(t[3])>
>;

mobius_embedding := (R,r) -> (t,u) ->
 (R + u*r*cos(2*Pi*t)) *~ [cos(4*Pi*t),sin(4*Pi*t),0] +~ [0,0,u *r* sin(2*Pi*t)];

torus_embedding := (R,r) -> (t,u) ->
 (R + r * cos(2*Pi*u)) *~ [cos(2*Pi*t),sin(2*Pi*t),0] +~ [0,0,(r * sin(2*Pi*u))];
 
simplex_embedding := proc(t)
 if nops(t) = 1 then
  return 0;
 elif nops(t) = 2 then
  return 2*t[1]-1;
 elif nops(t) = 3 then
  return [t[1]-t[2]/2-t[3]/2,sqrt(3)/2*(t[2]-t[3])];
 elif nops(t) = 4 then
  return [sqrt(2)*(2*t[2]-t[3]-t[4])/3,
          sqrt(2/3)*(t[3]-t[4]),
	  t[1]-(t[2]+t[3]+t[4])/3];
 else
  error("Simplex embedding only defined in dim <= 3");
 fi;
end:

mobius_arc := (R,r) -> proc(t1,u1,t2,u2)
 local s1,s2;
 if u1 = 0 then
  s2 := t2;
  s1 := t1 - round(2*(t1 - t2))/2;
 elif u2 = 0 then
  s1 := t1;
  s2 := t2 - round(2*(t2 - t1))/2;
 else 
  s1 := t1;
  s2 := t2 - round(t2-t1);
 fi;
 return spacecurve(mobius_embedding(R,r)(s1 + p*(s2-s1),u1 + p*(u2-u1)),p=0..1,args[5..-1]);
end:

sphere_arc := proc(a,b)
 local r,c,d,theta;
 r := evalf(sqrt(add(a[i]^2,i=1..3)));
 c := b -~ a;
 d := b +~ a;
 c := evalf(c *~ (r/sqrt(add(c[i]^2,i=1..3))));
 d := evalf(d *~ (r/sqrt(add(d[i]^2,i=1..3))));
 theta := evalf(arccos(add(a[i] * b[i],i=1..3)/r^2)/2);
 return spacecurve(d *~ cos(t) +~ c *~ sin(t),t = -theta..theta,args[3..-1]); 
end:

simplex_outline := proc(d)
 local e,i,opts;
 if d <> 2 and d <> 3 then
  error("Simplex outline is only defined in dimensions 2 and 3");
 fi;
 
 e := table():
 for i from 0 to d do
  e[i] := simplex_embedding([0$i,1,0$(d-i)]);
 od:

 opts := [];
 if nargs > 1 then opts := [args[2..-1]]; fi;
 if d = 3 and opts = [] then opts := [colour=black]; fi;
 
 return display(seq(seq(line(e[i],e[j],op(opts)),j=i+1..d),i=0..d),
                scaling=constrained,axes=none);
end:

trefoil_embedding := (R,r) -> proc(t,u)
 local x,y,z;
 x := [sin(t) + 2*sin(2*t),cos(t) - 2 * cos(2*t),-sin(3*t)];
 y := [72*sin(2*t)+3*sin(8*t)-13*sin(4*t)+3*sin(7*t)-14*sin(5*t)+3*sin(t),
       3*cos(t)-3*cos(8*t)+3*cos(7*t)-72*cos(2*t)+14*cos(5*t)-13*cos(4*t),
       10*sin(6*t)-34*sin(3*t)];
 z := [-391*cos(t)+2*cos(8*t)-29*cos(7*t)+85*cos(2*t)-99*cos(5*t)+24*cos(4*t)+9*cos(10*t)-9*cos(11*t),
       -9*sin(11*t)+29*sin(7*t)+85*sin(2*t)-9*sin(10*t)+2*sin(8*t)-24*sin(4*t)-99*sin(5*t)+391*sin(t),
       -570-34*cos(3*t)-94*cos(6*t)+18*cos(9*t)];
 y := y /~ sqrt(add(y[i]^2,i=1..3));
 z := z /~ sqrt(add(z[i]^2,i=1..3));
 return R *~ x +~ (r * cos(u)) *~ y +~ (r * sin(u)) *~ z;
end:



trefoil_b := (t) -> [(2+cos(3*t))*cos(2*t),(2+cos(3*t))*sin(2*t),sin(3*t)];

klein_embedding := (t,u) -> 
[(0.1*sin(3*Pi*t)+0.1*sin(Pi*t)+0.4*cos(Pi*t))*sin(2*Pi*u)-0.5*sin(4*Pi*t)+sin(2*Pi*t), 
  0.2*sin(2*Pi*u)*sin(3*Pi*t)+2.*cos(2*Pi*t)+0.5, 
  0.25*cos(2*Pi*u)*sin(2*Pi*t)+0.4*cos(2*Pi*u)];

klein_seam_a := (t) -> [0.8621-0.0015*cos(4*Pi*t)+0.0171*sin(2*Pi*t)-0.0002*sin(6*Pi*t),t];
klein_seam_b := (t) -> [0.1179+0.0031*cos(4*Pi*t)-0.0385*sin(2*Pi*t)+0.0005*sin(6*Pi*t), 
                        -0.25+0.0597*cos(2*Pi*t)-0.0004*cos(6*Pi*t)+0.0049*sin(4*Pi*t)];
klein_seam := (t) -> [-0.2811+0.0051*cos(4*Pi*t)-0.1401*sin(2*Pi*t)+0.0005*sin(6*Pi*t), 
                      1.7871-0.0061*cos(4*Pi*t)+0.3532*sin(2*Pi*t)-0.0005*sin(6*Pi*t), 
                      0.2090*cos(2*Pi*t)-0.0010*cos(6*Pi*t)+0.0086*sin(4*Pi*t)];

orient_face := proc(ii,v)
 local dp,u0,u1,u2,vv,i;
 dp := (x,y) -> add(x[i] * y[i],i=1..3);
 u0 := [0,0,0];
 for i in ii do u0 := u0 +~ v[i]; od;
 u0 := evalf(u0 /~ sqrt(dp(u0,u0)));
 u1 := evalf(v[ii[1]]);
 u1 := u1 -~ dp(u1,u0) *~ u0;
 u1 := evalf(u1 /~ sqrt(dp(u1,u1)));
 u2 := [u0[2] * u1[3] - u0[3] * u1[2],
        u0[3] * u1[1] - u0[1] * u1[3],
        u0[1] * u1[2] - u0[2] * u1[1]];
 vv := map(i -> [evalf(arctan(dp(u2,v[i]),dp(u1,v[i]))),i],ii);
 return map(x -> x[2],sort(vv));
end:
