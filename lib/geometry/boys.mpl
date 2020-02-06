# The Boys embedding, as a map from the Riemann sphere to R^3
 
complex_boys_embedding := proc(z)
 local a,V,M,B,rM;

 if z = 0 then return [0,0,2]; fi;
 
 a := 1/(z^3-1/z^3+sqrt(5)):
 V := [I*(z^2-1/z^2), z^2+1/z^2, 2/3*I*(z^3+1/z^3)]:
 M := map(Re, a *~ V +~ [0, 0, 1/2]):
 rM := add(M[i]^2,i=1..3);
 B := M /~ rM;
 return B;
end:

sphere_reduce0 := (x) -> (u) -> rem(u,x[1]^2+x[2]^2+x[3]^2-1,x[3]);

sphere_reduce1 := (x) -> proc(u)
  local n,d,n0,d0,n1,d1,f;
  if type(u,list) then return map(sphere_reduce1(x),u); fi;

  n := sphere_reduce0(x)(numer(u));
  d := sphere_reduce0(x)(denom(u));
  n0 := coeff(n,x[3],0);
  n1 := coeff(n,x[3],1);
  d0 := coeff(d,x[3],0);
  d1 := coeff(d,x[3],1);
  n := sphere_reduce0(x)(expand(n * (d0 - d1*x[3])));
  d := sphere_reduce0(x)(expand(d * (d0 - d1*x[3])));
  return factor(n/d);
end:

# The map boys_embedding() is the Boys embedding, as a map from the
# round sphere S^2 to R^3.
make_boys_embedding := proc()
 local x,Z,B,BN,dB;
 global boys_embedding0,boys_normal0;
 
 assume(x[1] > 0, x[2] > 0, x[3] > 0);
 Z := (x[1] + I * x[2])/(1 - x[3]);
 B := complex_boys_embedding(Z);
 B := map(sphere_reduce1(x),B);
 dB := denom(B[1]);
 B := factor(dB *~ B);
 B := [op(B),dB];
 boys_embedding0 := unapply(B,x);

 BN := subs({seq(x[i] = t*x[i],i=1..3)},
            [B[1]/B[4],B[2]/B[4],B[3]/B[4]]);
 BN := subs(t = 1, map(diff,BN,t));
 BN := sphere_reduce1(x)(BN);
 BN := expand(factor(BN *~ denom(BN[1]) /~ 480)):
 
 boys_normal0 := unapply(BN,x);
end:

boys_embedding := proc(x)
 local B;
 B := boys_embedding0(x);
 return [B[1]/B[4],B[2]/B[4],B[3]/B[4]];
end:

boys_normal := proc(x)
 local n,M;
 if x = [0,0,1] then return [0,0,1]; fi;
 M := evalf(boys_jacobian_matrix(x));
 n := convert((1/Transpose(Matrix(M))) . Vector(x),list);
 n := n /~ sqrt(add(n[i]^2,i=1..3));
 return n;
end:

make_boys_jacobian := proc()
 local x,p,xred,B,BJM,BJN,BJNP,DBJNP,p_rule,x0,rot;
 global boys_jacobian_matrix,boys_jacobian_square_norm,boys_poly,boys_p0,boys_corners;
 
 B := boys_embedding(x);

 # The embedding map extends naturally over a neighbourhood of S2 in R3,
 # and this is the Jacobian of that extension.
 BJM := [seq([seq(sphere_reduce1(x)(diff(B[i],x[j])),j=1..3)],i=1..3)];
 boys_jacobian_matrix := unapply(BJM,x);

 # This is the square norm of the Jacobian restricted to S2
 BJN := sphere_reduce1(x)(expand(add(add(BJM[i][j]^2,j=1..3),i=1..3) -
                          add(add(BJM[i][j]*x[j],j=1..3)^2,i=1..3))):
 boys_jacobian_square_norm := unapply(BJN,x);

 p_rule := {x[1] = (1-p^2)/(1+p^2)/sqrt(2),
            x[2] = (1-p^2)/(1+p^2)/sqrt(2),
	    x[3] = 2 * p/(1+p^2)};

 BJNP := factor(expand(simplify(subs(p_rule,BJN))));
 DBJNP := factor(expand(diff(BJNP,p)));
 boys_poly := unapply(select(g -> degree(g,p) = 18,{op(numer(DBJNP))})[1],p);
 boys_p0 := fsolve(boys_poly(p),p=0.15..0.16);

 x0 := evalf(subs(p = boys_p0,subs(p_rule,[x[1],x[2],x[3]])));

 rot := (x) -> [(-x[1]-sqrt(3)*x[2])/2,(sqrt(3)*x[1]-x[2])/2,x[3]];
 boys_corners :=
  evalf([x0,rot(x0),rot(rot(x0)),
         -~ x0, -~ rot(x0), -~ rot(rot(x0))]);
end:

