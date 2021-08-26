# We use the definition below for generalised Narayana numbers because it is
# good for m > 0 and for n = 0.  In the most common case where m = 0 and
# n > 0 it is equivalent to the function narayana_number_basic(n,j).

narayana_number := proc(n,j,m := 0)
 (m+1)/(n+1)*binomial(n+1,j) * binomial(n-m-1,j-1);
end:

narayana_number(0,0) := 1;

narayana_number_basic := (n,j) ->
 binomial(n,j) * binomial(n,j-1) / n;

# This is the sum of narayana_number(n,j,0) x^n y^j for n,j >= 0
narayana_series := (x,y) -> 
 (1 + x*(1-y) - sqrt(1-2*x*(1+y)+x^2*(1-y)^2))/(2*x);

# This is the series used by Stanley which has slightly different
# conventions for n = 0 and so ends up as 1 + narayana_series(x,y)

narayana_series_stanley := (x,y) ->
 (1-x-x*y - sqrt((1-x-x*y)^2-4*x^2*y))/(2*x);

`is_element/narayana_paths` := (len::posint,peaks::posint) -> proc(u)
 local v,w,y,i;
 
 if not(type(u,list(integer))) then
  return false;
 fi;

 if {op(u),1,-1} <> {1,-1} then
  return false;
 fi;
 
 if nops(u) <> 2*len then
  return false;
 fi;

 v := 0;
 y := 0;
 for i from 1 to 2*len do
  y := y + u[i];
  v := v,y;
 od:
 v := [v];
 
 if v[2*len+1] <> 0 then
  return false;
 fi;

 if min(op(v)) < 0 then
  return false;
 fi;

 w := select(i -> (u[i] = 1 and u[i+1] = -1),[seq(i,i=1..2*len-1)]);
 if nops(w) <> peaks then
  return false;
 fi;
 
 return true;
end:

`list_elements/narayana_paths` := proc(len,peaks)
 local A,B,L,a,b,u,ok,y,i;
 A := map(a -> [0,op(a),len+1],combinat[choose](len  ,peaks-1));
 B := map(b -> [0,op(b),len  ],combinat[choose](len-1,peaks-1));
 L := NULL;
 for a in A do
  for b in B do
   u := map(op,[seq([(+1)$(a[i+1]-a[i]),(-1)$(b[i+1]-b[i])],i=1..peaks)]);
   ok := true;
   y := 0;
   for i from 1 to 2*len+1 do
    y := y + u[i];
    if y = 0 then 
     ok := false;
     break;
    fi;
   od:
   if ok then 
    L := L,u[2..-1];
   fi;
  od:
 od:
 return [L];
end:

# This is very unintelligent
`list_elements_basic/narayana_paths` := proc(len,peaks)
 local L,M,i,k,u,h;
 L := [[1]]:
 for i from 1 to 2*len-1 do
  M := NULL;
  for u in L do
   h := `+`(op(u));
   if h > 0 then
    M := M,[op(u),-1],[op(u),1];
   else
    M := M,[op(u),1];
   fi;
  od:
  L := [M];
 od:
 M := NULL;
 for u in L do
  k := nops(select(i -> (u[i]=1 and u[i+1]=-1),[seq(i,i=1..2*len-1)]));
  if k = peaks and `+`(op(u)) = 0 then 
   M := M,u;
  fi;
 od:
 return [M];
end:

`count_elements/narayana_paths` := (len,peaks) ->
 narayana_number(len,peaks);

`plot/narayana_path` := proc(u)
 local P,y,i;
 P := NULL;
 y := 0;
 for i from 1 to nops(u) do
  P := P,line([i-1,y],[i,y+u[i]]);
  y := y + u[i];
 od:
 display(P,scaling=constrained,axes=none);
end:

`digraph/narayana_path` := proc(u)
 local n,y,v,V,E,i,j,h;
 n := nops(u);
 y := 0;
 v := NULL;
 for i from 1 to n do 
  y := y + u[i];
  v := v,y;
 od:
 v := [v];
 V := [0,op(select(i -> u[i] = 1,[seq(i,i=1..n)]))];
 E := NULL;
 for i in V do
  if i = 0 then h := 0; else h := v[i]; fi;
  j := i+1;
  while j <= n and v[j] >= h do
   if v[j] = h + 1 and u[j] = 1 then
    E := E,[i,j];
   fi;
   j := j+1;
  od;
 od:
 return [V,[E]];
end:

`extended_stasheff_tree/narayana_path` := proc(u)
 local n,V,E,L,ix,c,v,e,m,i,T,T0,t,UU;
 n := nops(u);
 V,E := op(`digraph/narayana_path`(u));
 L := select(i -> nops(select(e -> e[1]=i,E))=0,V);

 ix := table():
 for i from 1 to nops(L) do ix[L[i]] := i; od:

 c := table();
 for v in V do
  c[v] := {};
 od:
 c[0] := {};
 for e in E do
  c[e[1]] := {op(c[e[1]]),e[2]}; 
 od:
 m := nops(V);
 for i from m to 1 by -1 do
  v := V[i];
  if member(v,L) then
   T[v] := {v};
  else
   T[v] := map(j -> op(T[j]),c[v]);
  fi;
 od:

 t := table():
 for v in V do
  T0 := T[v];
  if type(t[T0],integer) then
   t[T0] := t[T0] + 1;
  else
   t[T0] := 0;
  fi;
 od:

 UU := NULL;
 for T0 in map(op,[indices(t)]) do
  UU := UU,[map(v -> ix[v],T0),t[T0]];
 od:
 UU := {UU};
 
 return UU;
end:

check_narayana := proc()
 local x,y,d,j,n,m,F0,F1,F2,F3;

 _ASSERT(
  `and`(seq(seq(evalb(narayana_number(n,j) = narayana_number_basic(n,j)),j=0..20),n=1..20)),
  "narayana_number_basic(n,j) = narayana_number(n,j,0) for n > 0"
 );
 
 F0 := narayana_series(x,y);
 _ASSERT(
  simplify(x * F0^2 + (x*y-x-1) * F0 + 1) = 0,
  "Quadratic relation for Narayana series"
 );

 F1 := narayana_series_stanley(x,y);
 
 _ASSERT(
  simplify(F0 - F1 - 1) = 0,
  "narayana_series(x,y) = narayana_series_stanley(x,y) + 1"
 );
 
 d := 9;
 m := 4;
 F2 := expand(convert(expand(series(
  (e*x)^m * narayana_series(e*x,e*y)^(m+1),
  e=0,d+2)),polynom,e));
 F3 := add(add(narayana_number(n,j,m) * x^n * y^j * e^(n+j),j=0..min(n-m,d-n)),n=m..d);
 _ASSERT(simplify(F3 - F2) = 0,"generating function");
end:

