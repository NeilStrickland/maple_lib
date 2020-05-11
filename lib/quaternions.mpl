# We identify R^4 with the quaternions by the rule
# [x1,x2,x3,x4] |-> x1 i + x2 j + x3 k + x4.

`mu/H` := proc(a,b) 
 [  a[1]*b[4] + a[2]*b[3] - a[3]*b[2] + a[4]*b[1] ,
  - a[1]*b[3] + a[2]*b[4] + a[3]*b[1] + a[4]*b[2] ,
    a[1]*b[2] - a[2]*b[1] + a[3]*b[4] + a[4]*b[3] ,
  - a[1]*b[1] - a[2]*b[2] - a[3]*b[3] + a[4]*b[4]
 ];
end:

`conj/H` := proc(a)
 [-a[1],-a[2],-a[3],a[4]];
end:

`square_norm/H` := (a) -> add(a[i]^2,i=1..4);

`norm/H` := (a) -> sqrt(add(a[i]^2,i=1..4));

`inv/H` := (a) -> `conj/H`(a) /~ `square_norm/H`(a);

`phi/angles/H` := (t) ->
 [cos(t[1])*cos(t[2]),cos(t[1])*sin(t[2]),sin(t[1])*cos(t[3]),sin(t[1])*sin(t[3])];

# This is essentially a |-> a * i * (conjugate of a)
hopf_map := (a) -> 
 [a[1]^2-a[2]^2-a[3]^2+a[4]^2,
  2*a[1]*a[2]+2*a[3]*a[4],
  2*a[1]*a[3]-2*a[2]*a[4]];

`rotation_matrix/H` := (a) -> Matrix(
 [[a[1]^2-a[2]^2-a[3]^2+a[4]^2,
   2*a[1]*a[2]-2*a[3]*a[4],
   2*a[1]*a[3]+2*a[2]*a[4]],
  [2*a[1]*a[2]+2*a[3]*a[4],
   -a[1]^2+a[2]^2-a[3]^2+a[4]^2,
   -2*a[1]*a[4]+2*a[2]*a[3]],
  [2*a[1]*a[3]-2*a[2]*a[4],
   2*a[1]*a[4]+2*a[2]*a[3],
   -a[1]^2-a[2]^2+a[3]^2+a[4]^2]]
  ) / add(a[i]^2,i=1..4);

