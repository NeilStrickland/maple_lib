# This code is for the cohomology of F(A,R^3), or F(A,R^{2n+1}) for
# any n > 0.  This is concentrated in even degrees so we do not
# need to worry about sign rules or gradings.

with(Groebner):

`vars/poisson` := proc(A::set)
 [seq(seq(u[a,b],b in A),a in A)];
end:

`rels/poisson` := proc(A::set)
 local n,i,j,k,uf;
 n := nops(A);
 uf := (i,j) -> u[A[i],A[j]];

 return 
  [seq(uf(i,i),i = 1..n),
   seq(seq(uf(i,j)+uf(j,i),j=i+1..n),i=1..n-1),
   seq(seq(uf(i,j)^2,j=1..n),i=1..n),
   seq(seq(seq(
    uf(i,j)*uf(j,k) + uj(j,k)*uf(k,i) + uf(k,i)*uf(i,j),
    k=j+1..n),j=i+1..n),i=1..n)
  ];
end:

`groebner_basis/poisson` := proc(A::set)
 Basis(`rels/poisson`(A),tdeg(`vars/poisson`(A)));
end:

`basis/poisson` := proc(A::set)
 local n,a,B,U,V;
 
 n := nops(A);
 if n <= 1 then
  return [1];
 fi;
 a := A[n];
 B := A minus {a};
 U := `basis/poisson`(A minus {a});
 V := [1,seq(u[x,a],x in B)];
 return map(op,[seq(U *~ v,v in V)]);
end:
