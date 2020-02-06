# Euler found rational curves on the surface given by
# w+x+y+z = wxyz + a = 0.  The formula here is similar to Euler's
# but simpler, and is taken from slides of Elkies

`f/euler_quartic` := (a,x) -> [add(x[i],i=1..4),mul(x[i],i=1..4)+a];

`g/euler_quartic` := (a,s) -> [
 1/2*s^(-3)*(s^4-4*a)^( 2)*(s^4+12*a)^(-1),
 2*a*s^(-3)*(s^4-4*a)^(-1)*(s^4+12*a)^(-1)*(3*s^4+4*a)^2,
 1/2*s     *               (s^4+12*a)     *(3*s^4+4*a)^(-1),
  -2*s^5   *(s^4-4*a)^(-1)*(s^4+12*a)     *(3*s^4+4*a)^(-1)
];

check_euler_quartic := proc()
 local a,s;

 _ASSERT(
  simplify(`f/euler_quartic`(a,`g/euler_quartic`(a,s))) = [0,0],
  "Euler quartic relation"
 );
end:

