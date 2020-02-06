with(LinearAlgebra):
with(Groebner):

# Exterior powers of matrices (implicitly using lexicographic ordering
# of the standard bases of exterior powers of R^n).

exterior_power := proc(k::nonnegint,A)
 local m,n,S,T,s,t;
 m,n := Dimension(A);
 S := combinat[choose](m,k);
 T := combinat[choose](n,k);
 Matrix([seq([seq(Determinant(SubMatrix(A,s,t)),t in T)],s in S)]);
end:

# If S is a subset of {1,..,n} then we have an associated shuffle
# permutation of {1,..,n}.  The next function computes the signature.

shuffle_sgn := proc(n,S)
 local k,T,ST;
 k := nops(S);
 T := sort([op({seq(i,i=1..n)} minus S)]);
 ST := [op(S),op(T)];
 return signum(mul(mul(ST[j]-ST[i],j=i+1..n),i=1..n));
end:

# Given a matrix A we get an induced map of Koszul algebras.  Each
# Koszul algebra has a natural Frobenius form, with using which we
# get a kind of dual map in the opposite direction, which is computed
# by the function below.  For a square matrix A, the composite of the
# k'th exterior power and the k'th koszul adjoint (in either order)
# is multiplication by det(A).

koszul_adjoint := proc(k::nonnegint,A)
 local m,n,M,N,S,T,Sc,Tc,Se,Te,s,t,i,j;
 m,n := Dimension(A);
 M := {seq(i,i=1..m)};
 N := {seq(j,j=1..n)};
 S := combinat[choose](m,k);
 T := combinat[choose](n,k);
 Sc := map(s -> sort([op(M minus {op(s)})]),S);
 Tc := map(t -> sort([op(N minus {op(t)})]),T);
 Se := [seq([op(S[i]),op(Sc[i])],i=1..nops(S))];
 Se := map(u -> signum(mul(mul(u[j]-u[i],j=i+1..m),i=1..m)),Se);
 Te := [seq([op(T[i]),op(Tc[i])],i=1..nops(T))];
 Te := map(u -> signum(mul(mul(u[j]-u[i],j=i+1..n),i=1..n)),Te);

 M := Matrix(nops(T),nops(S));
 for i from 1 to nops(S) do
  for j from 1 to nops(T) do
   M[j,i] := Determinant(SubMatrix(A,Sc[i],Tc[j])) * Se[i] * Te[j];
  od:
 od:

 return M;
end:

# A list u of length n in a ring R gives a differential on the
# Koszul algebra of R^n.  The function below gives the matrix of
# this differential with respect to the standard bases of the
# k'th and (k-1)'th exterior powers of R^n.

koszul_d := proc(k::posint,u)
 local n,S,T,s,t,i,j,MT,M;
 n := nops(convert(u,list));
 S := combinat[choose](n,k);
 T := combinat[choose](n,k-1);
 MT := table():
 for s in S do
  for t in T do
   MT[t,s] := 0;
  od:
  for i from 1 to k do
   t := [seq(s[j],j=1..i-1),seq(s[j],j=i+1..k)];
   MT[t,s] := (-1)^(i-1) * u[s[i]];
  od;
 od: 
 M := Matrix([seq([seq(MT[T[i],S[j]],j=1..nops(S))],i=1..nops(T))]);
 return M;
end:

# koszul_p can be set equal to a prime number if we want to work in that
# characteristic.

koszul_p := infinity;

koszul_pmod := (x) -> `if`(koszul_p=infinity,x,mods(x,koszul_p)):

# The function below sets up a number of global variables.  The
# original v can be supplied as a list.  Then v_vec will be the corresponding
# row vector.  Also u_vec will be the vector of variables x[i], and w_vec
# will be the vector of powers x[i]^h, where h is minimal such that x[i]^h
# lies in I = (v[1],...,v[n])  for all i.  Next, A and B will be matrices with
# u_vec = v_vec.A and v_vec = w_vec.B, which witnesses the inclusions
# (x[1]^(h),...,x[n]^(h)) <= I <= (x[1],...,x[n]).  These matrices induce
# morphisms of Koszul complexes alpha : K(u) ->K(v) and beta: K(v)->K(w).  It
# is easy to understand K(u) and K(w) in particular,  they only have  homology
# in degree zero.  All three complexes can be regarded as commutative
# Frobenius algebras in the category of chain complexes, so there are adjoint
# morphisms alpha^! : K(v) -> K(u)  and beta^! : K(w) -> K(v).  The idea is
# to use these to show that K(v) also has homology concentrated in degree zero.

koszul_setup := proc(v)
 global n,u_vec,v_vec,w_vec,x_vec,x_vars,Iv,Mv,Nv,
        soc_u,soc_v,soc_w,A,B,p;
 local a,b,c,i,h,v0,v1,x0,x1,char;
 n := nops(v);
 v_vec := Transpose(Vector(v));
 x_vec := Transpose(<seq(x[i],i=1..n)>);
 w_vec := x_vec;
 soc_w := 1;
 x_vars := tdeg(seq(x[i],i=1..n));

 a := table();
 v0 := v_vec;
 v1 := v_vec;
 for i from n to 1 by -1 do
  v0 := v1;
  v1 := subs(x[i]=0,v1);
  a[i] := koszul_pmod((v0 - v1)/x[i]);  
 od;

 B := Matrix([seq(convert(a[i],list),i=1..n)]);
 soc_v := koszul_pmod(Determinant(B));
 char := `if`(koszul_p=infinity,NULL,characteristic = koszul_p);

 Iv,Mv := Basis(convert(v,list),x_vars,output=extended,char);
 Mv := Transpose(Matrix(Mv));
 Nv := (z) -> koszul_pmod(NormalForm(z,Iv,x_vars,char));

 h := 1;
 x0 := map(Nv,convert(x_vec,list));
 x1 := x0;
 while h < 100 and x1 <> [0$n] do
  h := h+1;
  x1 := map(Nv,x0 *~ x1);
 od;

 if h >= 100 then
  error("Variables are not nilpotent mod given ideal");
 fi;

 u_vec := Transpose(Vector([seq(x[i]^h,i=1..n)]));
 soc_u := mul(x[i]^(h-1),i=1..n);

 a := NULL;
 b := NULL;
 for i from 1 to n do 
  unassign('b');
  c := NormalForm(x[i]^h,Iv,x_vars,b,char);
  a := a,b;
 od;

 A := map(expand,Mv . Transpose(Matrix([a])));
 NULL;
end:
