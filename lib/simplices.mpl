# An n-simplex in R^d is represented as a length (n+1) list of
# length d lists of real numbers.

`is_element/simplices` := (d::posint) -> (n::nonnegint) -> proc(a)
 global reason;
 local i,A,indep;
 
 if not (type(a,list) and nops(a) = n+1) then
  reason := ["is_element/simplices","a is not a list of length n+1",a,n];
  return false;
 fi;

 for i from 1 to n+1 do
  if not `is_element/R`(d)(a[i]) then
   reason := ["is_element/simplices","a[i] is not in R^d",a,i,d];
   return false;
  fi;
 od;
 
 A := Matrix([seq(a[i] -~ a[n+1],i=1..n)]);
 indep := evalb(NullSpace(Transpose(A)) = {});
 if not indep then
  reason := ["is_element/simplices","a is not affinely independent",a];
  return false;
 fi;

 return true;
end:

`is_equal/simplices` := (d::posint) -> (n::nonnegint) -> proc(a,b)
 return evalb(simplify(a -~ b) = [[0$d]$(n+1)]);
end:

`is_leq/simplices` := NULL;
`list_elements/simplices` := NULL;
`count_elements/simplices` := NULL;

`random_element/simplices` := (d::posint) -> (n::nonnegint) -> proc(m := 100)
 local indep,a,A;

 if n > d then
  error "n cannot be bigger than d";
 fi;
 
 indep := false;
 while not(indep) do
  a := [seq([seq(rand(-m..m)(),j=1..d)],i = 1..n+1)];
  A := Matrix([seq(a[i] -~ a[n+1],i=1..n)]);
  indep := evalb(NullSpace(Transpose(A)) = {});
 od:

 return a;
end:

`barycentre/simplex` := (d::posint)  -> proc(a)
 local n,u,i;

 n := nops(a) - 1;
 u := a[n+1];
 for i from 1 to n do u := u +~ a[i]; od;
 u := u /~ (n+1);
 return u;
end:

`radius/simplex` := (d::posint)  -> proc(a)
 local u,r;
 
 u := `barycentre/simplex`(d)(a);
 r := max(map(v -> add((v[i]-u[i])^2,i=1..d),a));
 return sqrt(r);
end:

# The primal matrix has the vertex vectors as its columns,
# but with an extra row of 1's at the bottom.

`primal_matrix/simplex` := (d::posint)  -> proc(a)
 local n,u,i;

 n := nops(a) - 1;
 return Transpose(Matrix([seq([op(a[i]),1],i=1..n+1)]));
end:

# For a d-simplex in R^d, the dual matrix is the inverse 
# of the primal matrix.

`dual_matrix/simplex` := (d::posint)  -> proc(a)
 if nops(a) <> d+1 then return FAIL; fi;
 
 return 1/`primal_matrix/simplex`(d)(a);
end:

# With two arguments, this returns true iff the intersection 
# of the simplices spanned by a and b is the simplex spanned
# by some subset c of a intersect b.  With a third argument c_,
# we require in addition that c = c_.

`intersect_nicely/simplices` := (d::posint) -> proc(a,b,c_)
 local c,aa,bb,cc,ab,n,m,p,q,e,W_cand,W_new,W_inc,W,WA,WB,A,B,r,C;

 c := {op(a)} intersect {op(b)};
 if nargs > 2 and c <> {op(c_)} then
  return false;
 fi;
 
 aa := [seq([op(z),1,1],z in {op(a)} minus c)];
 bb := [seq([op(-~z),-1,1],z in {op(b)} minus c)];
 cc := [seq([op(z),1,0],z in c)];
 ab := [op(aa),op(bb)];
 n := nops(aa);
 m := nops(bb);
 p := nops(cc);
 e := Vector([0$d,0,1]);
 W_cand := combinat[choose](n+m,min(d+2-p,n+m));
 W_cand := {seq({op(W)},W in W_cand)};
 W_cand := select(
  W -> W <> {} and min(op(W)) <= n and max(op(W)) > n,
  W_cand
 );

 while W_cand <> {} do
  W_new := NULL;
  W_inc := NULL;
  for W in W_cand do 
   q := nops(W);
   A := Transpose(Matrix([seq(ab[w],w in W),
                          op(cc)]));
   B := ReducedRowEchelonForm(<A|e>);
   if Equal(SubMatrix(B,1..d+2,1..p+q),
            <IdentityMatrix(p+q),Matrix(d+2-p-q,p+q)>) then
    r := [seq(B[i,p+q+1],i=1..p+q)];
    if (p+q=d+2 or B[p+q+1,p+q+1] = 0) then 
     if min(seq(r[k],k=1..q)) >= 0 then
      return false;
     fi;
    else
     W_inc := W_inc,W;
    fi;
   else
    WA,WB := selectremove(w -> w <= n,W);
    if nops(WA) > 1 then
     W_new := W_new,seq({op(W)} minus {w},w in WA);
    fi;
    if nops(WB) > 1 then
     W_new := W_new,seq({op(W)} minus {w},w in WB);
    fi;
   fi;
  od;
  W_cand := {W_new};
  for W in W_inc do
   W_cand := remove(U -> U minus W = {},W_cand);
  od:
 od;
 return true;
end:

