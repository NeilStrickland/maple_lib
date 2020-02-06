`is_element/raw_matroids` := proc(M)
 global reason;
 local n,s,t,s1,t1,u,a,b;

 if not(type(M,set(set))) then
  reason := ["not a set of sets"];
  return false;
 fi;
 
 n := nops(M);
 for s in M do
  for t in M do
   if s <> t then 
    s1 := s minus t;
    t1 := t minus s;
    if s1 = {} or t1 = {} then
     reason := ["s and t are nested",s,t];
     return false;
    fi;
    for a in s1 do
     u := select(b -> member((s minus {a}) union {b},M),t1);
     if u = {} then
      reason := ["exchange fails",s,t];
      return false;
     fi;
    od;
   fi;
  od;
 od;
 
 return true;
end:

`vertices/raw_matroid` := (M) -> map(op,{op(M)});

`is_basis/raw_matroid` := (M,s) -> member(s,M);

`is_independent/raw_simplicial_complex` := proc(M,s)
 local s0,u;
 
 if not(type(s,{list,set})) then return false; fi;
 
 s0 := {op(s)};
 
 for u in M do
  if s0 minus {op(u)} = {} then
   return true;
  fi;
 od:
 return false;
end:

`is_dependent/raw_simplicial_complex` := proc(M,s)
 local s0,u;
 
 if not(type(s,{list,set})) then return false; fi;
 
 s0 := {op(s)};

 for u in M do
  if s0 minus {op(u)} = {} then
   return false;
  fi;
 od:
 return true;
end:

`is_element/matroids` := proc(T)
 global reason;
 
 if not(type(T,table)) then
  return false;
 fi;

 if not (`is_element/raw_matroids`(T["bases"])) then
  return false;
 fi;

 if `vertices/raw_matroid`(T["bases"]) minus T["vertices"] <> {} then
  reason := ["vertex mismatch",T["vertices"],`vertices/raw_matroid`(T["bases"])];
  return false;
 fi;

 return true;
end:

`cook/raw_matroid` := proc(M,V_)
 local T;

 T := table():
 if nargs > 1 then
  T["vertices"] := V_;
 else
  T["vertices"] := `vertices/raw_matroid`(M);
 fi;
 T["bases"] := M;

end:

`set_rank/matroid` := proc(T)
 local m,r,n,P,A;

 m := nops(T["vertices"]);
 r := table():
 n := table():
 P := combinat[powerset](T["vertices"]);
 for A in P do
  r[A] := max(op(map(s -> nops(s intersect A),T["bases"])));
  n[A] := m - r[A];
 od:

 T["rank"] := eval(r);
 T["nullity"] := eval(r);
end:

`set_closure/matroid` := proc(T)
 local r,V,P,c,A,m;
 
 if not(type(T["rank"],table)) then `set_rank/matroid`(T); fi;
 
 r := eval(T["rank"]);
 V := T["vertices"];
 P := combinat[powerset](T["vertices"]);
 c := table():
 for A in P do
  m := r[A];
  c[A] := A union select(b -> r[A union {b}] = m + 1,V minus A);
 od:

 T["closure"] := eval(c):
 T["flats"] := select(A -> nops(c[A]) = nops(A),P);
end:

`res/matroid` := proc(T,A)
 local U,B,m;
 
 if not(type(A,set) and A minus T["vertices"] = {}) then
  error("A is not a subset of the vertices of T");
 fi;

 U := table():
 U["vertices"] := A;
 B := map(s -> s intersect A,T["bases"]);
 m := max(map(nops,B));
 U["bases"] := select(s -> nops(s) = m,T["bases"]);
end:

uniform_matroid := proc(A_::{nonnegint,set},k)
 local T,A;
 
 if type(A_,nonnegint) then
  A := {seq(i,i=1..A_)};
 else
  A := A_;
 fi;

 T := table():
 T["vertices"] := A;
 T["bases"] := combinat[choose](A,k);

 return eval(T);
end:

linear_matroid := proc(p,d)
 local T,V,i,j,B,f;
 
 V := [[]];

 for i from 1 to d do
  V := [seq(seq([op(v),j],j=0..p-1),v in V)];
 od:

 B := [seq([j],j=2..p^d)];
 for i from 2 to d do
  B := [seq(seq([op(b),j],j=b[-1]+1..p^d),b in B)];
 od:

 f := b -> modp(Determinant(Matrix(map(i -> V[i],b))),p);
 B := select(b -> f(b) <> 0,B);

 T := table():
 T["vectors"] := V;
 T["vertices"] := {seq(i,i=1..p^d)};
 T["bases"] := map(b -> {op(b)},{op(B)});

 return eval(T);
end:

