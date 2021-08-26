with(Groebner):
with(Ore_algebra):


find_koszul_homology := proc(rels,vars_,p_)
 local vars,char,A,T,P,ix_P,S,B0,B1,d,i,j,k,u,e_K,e_Z,e_B,de_K,ee_K,dd,K,
  K_basis,K_rank,Z_basis,Z_rank,B_basis,B_rank,BZ_basis,BZ_rank;

 if nargs > 1 then
  vars := vars_;
 else
  vars := [op(indets(rels,symbol))];
 fi;

 if nargs > 2 then
  char := (characteristic = p_);
 else
  char := NULL;
 fi;

 A := poly_algebra(op(vars),e_K,e_Z,e_B,char);
 T := MonomialOrder(A,lexdeg([e_K,e_B],vars,[e_Z]),{e_K,e_Z,e_B});

 d := nops(rels);
 # P = list of all subsets of 1,..,d
 P := combinat[powerset]([seq(i,i=1..d)]);

 # Now build index for P e.g. if {1,4,6} appears as 10th
 # element of P then if_P[{1,4,6}] should be 10.
 ix_P := table():
 for i from 1 to 2^d do ix_P[P[i]] := i; od:

 # de_K[i] will be the differential applied to the i'th basis
 # element of the exterior algebra (for 1 <= i <= 2^d).
 de_K := table():
 for i from 1 to 2^d do
  S := P[i];
  de_K[i] := add((-1)^(j-1) * e_K^ix_P[subsop(j=NULL,S)] * rels[S[j]],j=1..nops(S));
  ee_K[i] := e_K^i + e_K^(2^d+1) * de_K[i];
 od:

 # dd = the differential = linear extension of the map
 # sending e_K^i to de_K[i]
 dd := (u) -> add(coeff(u,e_K,i) * de_K[i],i=1..2^d);

 # Basis() calculates Groebner basis
 B0 := Basis([seq(ee_K[i],i=1..2^d)],T,char);
 K_basis := [seq(e_K^i,i=1..2^d)];
 K_rank  := 2^d;
 Z_basis := select(u -> degree(u,e_K) <= 2^d,B0);
 Z_rank  := nops(Z_basis);
 B_basis := select(u -> u <> 0,expand(map(quo,B0,e_K^(2^d+1),e_K)));
 B_rank  := nops(B_basis);

 B1 := Basis([seq(e_B^i + B_basis[i],i=1..B_rank),
              seq(e_Z^i + Z_basis[i],i=1..Z_rank)],T,char);

 BZ_basis := [seq(NormalForm(e_B^i,B1,T,char),i=1..B_rank)];
 BZ_rank  := nops(BZ_basis);

 K := table():
 K["num_rels"] := d;
 K["A"] := A;
 K["T"] := T;
 K["P"] := P;
 K["ix_P"] := eval(ix_P);
 K["de_K"] := eval(de_K);
 K["K_basis"] := K_basis;
 K["K_rank"]  := K_rank;
 K["Z_basis"] := Z_basis;
 K["Z_rank"]  := Z_rank;
 K["B_basis"] := B_basis;
 K["B_rank"]  := B_rank;
 K["BZ_basis"] := BZ_basis;
 K["BZ_rank"]  := BZ_rank;

 K["Z_basis_matrix"] := 
  Matrix([seq([seq(coeff(u,e_K,i),i=1..2^d)],u in Z_basis)]);
 K["B_basis_matrix"] := 
  Matrix([seq([seq(coeff(u,e_K,i),i=1..2^d)],u in B_basis)]);
 K["BZ_basis_matrix"] := 
  Matrix([seq([seq(coeff(u,e_Z,i),i=1..Z_rank)],u in BZ_basis)]);

 K["B0"] := B0;
 K["B1"] := B1;

 return eval(K);
end:

