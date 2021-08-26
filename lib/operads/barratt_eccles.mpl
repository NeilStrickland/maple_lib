# This defines the chain complex version of the Barratt-Eccles operad.
# Basis elements of E(A) are represented by expressions T(...), where
# there is at least one argument, each argument is a list containing
# each element of A precisely once, and no two adjacent arguments are
# the same.

`is_element/barratt_eccles` := (A::set) -> proc(x)
 local y,z,i;
 
 if x = 0 then return true; fi;
 
 if type(x,`+`) then
  return `and`(op(map(`is_element/barratt_eccles`(A),[op(x)])));
 fi;

 if type(x,`*`) then
  y,z := selectremove(type,[op(x)],integer);
  return (nops(z) = 1 and `is_element/barratt_eccles`(A)(z[1]));
 fi;
 
 if not type(x,specfunc(T)) then return false; fi;

 if nops(T) = 0 then return false; fi;
 
 for i from 1 to nops(x) do
  if not(`is_element/ord`(A)(op(i,x))) then
   return false;
  fi;
 od;

 for i from 1 to nops(x) - 1 do
  if op(i,x) = op(i+1,x) then return false; fi;
 od;

 return true;
end:

# Auxiliary function feeding into `diff/barratt_eccles`

`diff0/barratt_eccles` := (A::set) -> proc(x)
 local y,n,i;
 
 y := 0;
 n := nops(x);

 for i from 1 to n do
  if 1 < i and i < n and op(i-1,x) = op(i,x) then
   continue;
  fi;

  y := y + (-1)^(i-1) * T(op(1..i-1,x),op(i+1..n,x));
 od;
 
 return y;
end:

# Differential on the chain complex
`diff/barratt_eccles` := (A::set) -> apply_linear(`diff0/barratt_eccles`(A));

# Auxiliary function feeding into `deg/barratt_eccles`
`deg0/barratt_eccles` := (A) -> (x) -> nops(x) - 1;

# Degree function
`deg/barratt_eccles` := (A) -> apply_deg(`deg0/barratt_eccles`(A));

# This is the circle product for the operad structure.
# It is assumed that B is a subset of A and u is in E(A/B) and v is in E(B),
# where A/B is implemented as A \ B u {B}.

`o0/barratt_eccles` := (A,B) -> proc(u,v)
 local d,e,SS,x,s,p,w,u0,v0,w0,i;
 
 d := nops(u) - 1;
 e := nops(v) - 1;
 SS := `list_elements/shuffles`(d,e);

 x := 0;
 
 for s in SS do 
  p := `to_grid_path/shuffles`(d,e)(s);
  w := NULL;
  for i from 0 to d+e do
   u0 := op(p[i][1]+1,u);
   v0 := op(p[i][2]+1,v);
   w0 := subs(B = op(v0),u0);
   w := w,w0;
  od:
  x := x + `sgn/shuffles`(d,e)(s) * T(w);
 od:

 return x;
end:

`o/barratt_eccles` := (A,B) -> apply_bilinear(`o0/barratt_eccles`(A,B));

# We now have various functions related to an interesting filtration
# of the operad.
`flip_count/barratt_eccles` := (A::set) -> proc(x)
 local m,a,b,k,rr,i,r0,r1;
 
 m := table():
 for a in A do
  for b in A do
   m[a,b] := 0;
  od;
 od;

 k := nops(x);
 rr := map(`rank_table/ord`(A),[op(x)]);
 
 for i from 1 to k-1 do
  r0 := rr[i];
  r1 := rr[i+1];
  
  for a in A do
   for b in A do
    if (r1[b] - r1[a]) * (r0[b] - r0[a]) < 0 then
     m[a,b] := m[a,b] + 1;
    fi;
   od;
  od;
 od;

 return eval(m);
end:

`flip_count_matrix/barratt_eccles` := (A::set) -> proc(u,s_)
 local m;
 m := `flip_count/barratt_eccles`(A)(args);
 return Matrix([seq([seq(m[a,b],b in A)],a in A)]);
end:

`max_flip_count/barratt_eccles` := (A::set) -> proc(x)
 local m,mm,a,b;
 
 m := `flip_count/barratt_eccles`(A)(x);

 mm := 0;
 for a in A do
  for b in A do
   mm := max(mm,m[a,b]);
  od;
 od;

 return mm;
end:

`is_member/barratt_eccles_cells` := (A::set) -> proc(ms)
 local m,s,AA,a,b;
 
 if not(type(ms,list) and nops(ms) = 2) then return false; fi;

 m,s := op(ms);

 if not(`is_element/ord`(A)(s)) then return false; fi;
 if not(type(m,table)) then return false; fi;

 AA := {seq(seq([a,b],b in A),a in A)};
 if {indices(m)} <> AA then return false; fi;
 
 for a in A do
  for b in A do
   if not(type(m[a,b],nonnegint)) then return false; fi;
  od:
 od:

 for a in A do
  if m[a,a] <> 0 then return false; fi;
  for b in A do
   if m[a,b] <> m[b,a] then return false; fi;
  od;
 od;

 return true;
end:

`is_cell_member/barratt_eccles` := (A::set) -> (ms) -> proc(x)
 local m0,m1,s,a,b,y,z;

 if x = 0 then return true; fi;
 if type(x,`+`) then
  return `and`(seq(`is_cell_member/barratt_eccles`(A)(ms)(y),y in x));
 fi;
 if type(x,`*`) then
  y,z := selectremove(type,[op(x)],integer);
  if nops(z) = 1 then
   return `is_cell_member/barratt_eccles`(A)(ms)(z[1]);
  else
   return false;
  fi;
 fi;
 
 m0,s := op(ms);
 m1 := `flip_count/barratt_eccles`(A)(T(op(x),s));

 for a in A do
  for b in A do
   if m1[a,b] > m0[a,b] then return false; fi;
  od;
 od;

 return true;
end:

`filtration0/barratt_eccles` := (A::set) -> proc(x)
 local m,m_max,s,rr,k,i,r0,r1,a,b;

 if type(x,integer) then return 0; fi;

 return 1 + `max_flip_count/barratt_eccles`(A)(x);
end:

`filtration/barratt_eccles` := (A::set) ->
 apply_max_deg(`filtration0/barratt_eccles`(A));

