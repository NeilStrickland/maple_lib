check_koszul := proc()
 local A,n,dA,u,J,i;
 
 printf("%a()\n",procname);

 A := <<1|5|4|9>,<2|2|7|5>,<3|9|9|6>,<4|3|2|1>>;
 n := Dimension(A)[1];
 dA := Determinant(A);
 u := [4,5,6,11];

 J := Matrix(n,n);
 for i from 1 to n do J[i,n+1-i] := (-1)^(i-1); od;
 
 _ASSERT(
  Equal(koszul_adjoint(0,A), <<Determinant(A)>>),
  "koszul adjoint(0,A) = det(A)"
 );
 
 _ASSERT(
  Equal(koszul_adjoint(1,A), Adjoint(A)),
  "koszul_adjoint(1,A) = adj(A)"
 );
 
 _ASSERT(
  Equal(koszul_adjoint(n-1,A), Transpose((-1)^(n-1) * J . A . J)),
  "koszul_adjoint(n-1,A) is conjugate to A^T"
 );
 
 _ASSERT(
  Equal(koszul_adjoint(n,A), <<1>>),
  "koszul_adjoint(n,A) = 1"
 );

 _ASSERT(
  `and`(seq(Equal(exterior_power(k,A) . koszul_adjoint(k,A),
                  dA * IdentityMatrix(binomial(n,k))),k=0..n)),
  "exterior_power(k,A) o koszul_adjoint(k,A) = det(A) in all degrees"
 );

 _ASSERT(
  `and`(seq(Equal(koszul_d(k,u) . koszul_d(k+1,u),
                  Matrix(binomial(n,k-1),binomial(n,k+1))),k=1..n-1)),
  "koszul_d ^ 2 = 0"
 );
end:


check_koszul_comparison := proc()
 global v,n,u_vec,v_vec,w_vec,x_vec,x_vars,Iv,Mv,Nv,
        soc_u,soc_v,soc_w,A,B,p;
 
 v := [x[1]^2+x[2]^3,x[1]*x[2]+x[3],x[1]^4-x[3]^2*x[2],x[4]-x[2]^3];
 koszul_setup(v);

 _ASSERT(
  Equal(map(koszul_pmod,map(expand,u_vec)),
        map(koszul_pmod,map(expand,v_vec . A))),
  "u = v . A"
 );
 
 _ASSERT(
  Equal(map(koszul_pmod,map(expand,v_vec)),
        map(koszul_pmod,map(expand,w_vec . B))),
  "v = w . B"
 );
 
 _ASSERT(
   Equal(map(koszul_pmod,map(Nv,soc_v * x_vec)),Transpose(Vector(n))),
   "soc_v is in the socle"
 );

 _ASSERT(
   not(koszul_pmod(Nv(soc_v)) = 0),
   "soc_v is nonzero"
 );

 _ASSERT(
  `and`(seq(
   Equal(map(expand,koszul_d(k,v_vec) . exterior_power(k,A)), 
	 map(expand,exterior_power(k-1,A) . koszul_d(k,u_vec))),
   k=1..n
  )),
  "exterior_power(*,A) is a chain map"
 );

 _ASSERT(
  `and`(seq(
   Equal(map(expand,koszul_d(k,w_vec) . exterior_power(k,B)), 
	 map(expand,exterior_power(k-1,B) . koszul_d(k,v_vec))),
   k=1..n
  )),
  "exterior_power(*,B) is a chain map"
 );

 _ASSERT(
  `and`(seq(
   Equal(map(expand,koszul_d(k,u_vec) . koszul_adjoint(k,A)), 
	 map(expand,koszul_adjoint(k-1,A) . koszul_d(k,v_vec))),
   k=1..n
  )),
  "koszul_adjoint(*,A) is a chain map"
 );

 _ASSERT(
  `and`(seq(
   Equal(map(expand,koszul_d(k,v_vec) . koszul_adjoint(k,B)), 
	 map(expand,koszul_adjoint(k-1,B) . koszul_d(k,w_vec))),
   k=1..n
  )),
  "koszul_adjoint(*,B) is a chain map"
 );

end:
