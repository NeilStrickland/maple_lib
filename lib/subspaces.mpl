# Subspaces of (Z/p)^d are represented as pairs [U,V], where
# U and V are lists of lists, which correspond to RREF matrices.
# The rows of U are a basis for the subspace, and the rows
# of V are a basis for the annihilator.

`dim/subspaces`   := (p,d) -> U -> nops(U[1]);
`codim/subspaces` := (p,d) -> U -> nops(U[2]);

`span/subspaces` := (p,d) -> proc(U)
 local U0,r,c,i;

 if U = [] then return [[],convert(IdentityMatrix(d),listlist)]; fi;

 U0 := map(modp,U,p);
 if type(U0,list) then U0 := Matrix(U0); fi;
 r,c := Dimension(U0);
 if c <> d then error("Dimension mismatch"); fi;
 r := LinearAlgebra[Modular][MatBasis](p,U0,r,false);
 U0 := Matrix([op(1..r,convert(U0,listlist)),
               seq([0$c],i=1..c-r)]);
 LinearAlgebra[Modular][MatBasis](p,U0,r,true);
 U0 := convert(U0,listlist);
 return [[op(1..r,U0)],[op(r+1..c,U0)]];
end:

`ann/subspaces` := (p,d) -> proc(U)
 local U0;
 U0 := U;
 if type(U,list(list(integer))) then 
  U0 := `span/subspaces`(p,d)(U0);
 fi;
 return `span/subspaces`(p,d)(U0[2]);
end:

`bot/subspaces`   := (p,d) -> [[],convert(IdentityMatrix(d),listlist)];

`top/subspaces`   := (p,d) -> [convert(IdentityMatrix(d),listlist),[]];

`sum/subspaces`   := (p,d) -> (U,V) -> `span/subspaces`(p,d)([op(U[1]),op(V[1])]);

`inter/subspaces` := (p,d) -> (U,V) -> `ann/subspaces` (p,d)([op(U[2]),op(V[2])]);

`is_member/subspaces` := (p,d) -> proc(u,V)
 if V[2] = [] then return true; fi;
 return is_all_zero(map(modp, Matrix(V[2]) . Vector(u),p));
end:

`is_le/subspaces` := (p,d) -> proc(U,V)
  if U[1] = [] or V[2] = [] then return true; fi;
  return is_all_zero(map(modp, Matrix(V[2]) . Transpose(Matrix(U[1])),p)); 
end:

`random_element/subspaces` := (p,d) -> proc()
  local r,U,i,j;
  r := rand(0..d)();
  U := [seq([seq(rand(0..p-1)(),j=1..d)],i=1..r)];
  return `span/subspaces`(p,d)(U);
end:

