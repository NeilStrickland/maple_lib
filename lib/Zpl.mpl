# This is a row reduction algorithm for matrices over the p-local integers.
# It returns a triple [L,P,x].  Here P is an invertible matrix with P.M = L,
# so the row span of L is the same as that of M.  All rows of zeros in L
# appear at the bottom.  Every nonzero row contains an entry called a pivot.
# All pivot entries are powers of p.  If a pivot entry is p^v, then
# + all entries to the left are divisible by p^(v+1)
# + all entries to the right are divisible by p^v
# + all entries above or below are in the range {0,...,p^v - 1}
# These conditions force many entries to be zero.  I think that
# they characterise the result up to reordering the rows.  We use the
# following ordering:
# + If two rows have different valuations, then the one with lower
#    valuation comes first
# + If two rows have the same valuation, then the one with the pivot
#    further to the left comes first.
# The component x in the return value gives information abot the pivots.
# Explicitly, if the i'th entry in x is [j,v] then there is a pivot entry
# of p^v in position (i,j). 

Zpl_reduce := proc(M,p)
 local L,L1,P,P1,r,c,i,j,k,h,m,J,K,v,v_min,v_min_pos,pivots,cmp;
 L := Copy(M);
 r,c := Dimension(M);
 P := Matrix(r,r);
 for i from 1 to r do P[i,i] := 1; od;
 v := Matrix(r,c);
 i := 0;
 J := {seq(j,j=1..r)};
 K := {seq(k,k=1..c)};
 pivots := NULL;
 v_min_pos := [0,0];
 while v_min_pos <> NULL do
  v_min := infinity;
  v_min_pos := NULL;
  for k in K do
   for j in J do
    v[j,k] := padic_val(L[j,k],p);
    if v[j,k] < v_min then
     v_min := v[j,k];
     v_min_pos := [j,k];
    fi;
   od;
  od;
  if v_min_pos = NULL then
   break;
  fi;
  j,k := op(v_min_pos);
  pivots := pivots,[j,k,v_min];
  m := p^v_min/L[j,k];
  RowOperation(L,j,m,inplace=true);
  RowOperation(P,j,m,inplace=true);
  for h from 1 to r do
   if h <> j then
    m := (L[h,k] - modp(L[h,k],p^v_min))/p^v_min;
    RowOperation(L,[h,j],-m,inplace=true);
    RowOperation(P,[h,j],-m,inplace=true);
   fi;
  od;
  J := sort(J minus {j});
  K := sort(K minus {k});
 od;
 cmp := proc(x,y)
  if x[3] < y[3] then return true; fi;
  if x[3] > y[3] then return false; fi;
  return evalb(x[2] < y[2]);
 end:
 pivots := sort([pivots],cmp);
 L1 := convert(L,listlist);
 P1 := convert(P,listlist);
 L1 := Matrix([seq(L1[x[1]],x in pivots),seq(L1[j],j in J)]);
 P1 := Matrix([seq(P1[x[1]],x in pivots),seq(P1[j],j in J)]);
 return [L1,P1,[seq([x[2],x[3]],x in pivots)]];
end:


######################################################################
# This is an implementation of the p-local integers that can be
# used with LinearAlgebra[Generic][SmithForm].  However, Smith
# forms are not unique, and it does not seem easy to control which
# version we get if we use LinearAlgebra[Generic][SmithForm].
# The above function Zpl_reduce does essentially the same job
# but with a more precisely specified result.

Zpl[`0`] := 0;
Zpl[`1`] := 1;
Zpl[`+`] := `+`;
Zpl[`-`] := `-`;
Zpl[`*`] := `*`;
Zpl[`=`] := `=`;

Zpl[Quo] := proc(a,b,r)
 local b0,q0,r0;
 b0 := p^padic_val(b,p);
 r0 := modp(a,b0);
 q0 := (a - r0)/b;
 if nargs >= 3 then r := r0; fi;
 return q0;
end:

Zpl[Rem] := proc(a,b,q)
 local b0,q0,r0;
 b0 := p^padic_val(b,p);
 r0 := modp(a,b0);
 q0 := (a - r0)/b;
 if nargs >= 3 then q := q0; fi;
 return r0;
end:

Zpl[EuclideanNorm] := ((m) -> padic_val(m,p));
Zpl[UnitPart] := ((m) -> m/p^padic_val(m,p));
Zpl[Gcdex] := proc(a,b,s,t)
 local u,v;
 u := padic_val(a,p);
 v := padic_val(b,p);
 if u <= v then
  if nargs >= 4 then
   s := p^u/a; t := 0;
  fi;
  return p^u;
 else
  if nargs >= 4 then
   s := 0; t := p^v/b;
  fi;
  return p^v;
 fi;  
end:
