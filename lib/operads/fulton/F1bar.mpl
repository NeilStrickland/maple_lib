`phi/F1bar/ord` := (A::set) -> proc(x)
 return sort([op(A)],(a,b) -> ((a=b) or (op(x[{a,b}][a]) < op(x[{a,b}][b]))));
end:

######################################################################
# Apply the isomorphism R^1 = R

`trim/F1bar` := (A::set) -> proc(x)
 local u,x0,P,T,a;

 x0 := table();
 P := `list_elements/big_subsets`(A);
 for T in P do
  u := `bottom_normalise/SW`(1)(T)(x[T]); 
  x0[T] := table();
  for a in T do 
   x0[T][a] := op(u[a]);
  od;
 od;

 return eval(x0):
end:

######################################################################

`subcritical_tree/F1bar` := (A::set) -> proc(x)
 local x0,R,n,SS,i,j,J,J1,g1,g2,is_subcritical,a,k;

 x0 := `trim/F1bar`(A)(x);

 R := `phi/F1bar/ord`(A)(x);
 n := nops(A);
 SS := seq({a},a in A);

 for i from 1 to n-1 do 
  for j from i+1 to n do
   J := {seq(R[k],k=i..j)};
   is_subcritical := true;
   if i > 1 then
    J1 := {R[i-1],op(J)};
    g1 := `gap/real_functions`(J )(x0[J1]);
    g2 := `gap/real_functions`(J1)(x0[J1]);
    if g2 = g1 then
     is_subcritical := false;
    fi;
   fi;
   if j < n then
    J1 := {op(J),R[j+1]};
    g1 := `gap/real_functions`(J )(x0[J1]);
    g2 := `gap/real_functions`(J1)(x0[J1]);
    if g2 = g1 then
     is_subcritical := false;
    fi;
   fi;

   if is_subcritical then
    SS := SS,J;
   fi;
  od;
 od;
 SS := {SS};
 return SS;
end:

######################################################################

`theta/F1bar/K` := (A::set) -> proc(x)
 local x0,R,n,SS,i,j,k,J,J1,t,parent;

 x0 := `trim/F1bar`(A)(x);
 R := `phi/F1bar/ord`(A)(x);
 SS := `subcritical_tree/F1bar`(A)(x);
 parent := parent_map(A)(SS);
 n := nops(A);
 t := table();

 for i from 1 to n do 
  for j from i to n do 
   J := {seq(R[k],k=i..j)};
   if nops(J) = 1 or nops(J) = n then
    t[J] := 1;    
   elif not(member(J,SS)) then
    t[J] := 0;
   else
    J1 := parent[J];
    t[J] := 1 - `gap/real_functions`(J)(x0[J1])/
                `gap/real_functions`(J1)(x0[J1]);
   fi;
  od;
 od;

 return [R,eval(t)];
end:

######################################################################

`phi/K/F1bar` := (A::set) -> proc(Rt)
 local R,t,n,r,i,j,k,l,x,P,Q,Q1,J,M,M1,m,T,U;

 R,t := op(Rt);
 
 n := nops(A);
 r := table();
 for i from 1 to n do r[R[i]] := i; od;

 x := table();
 m := table();

 P := `list_elements/big_subsets`(A);
 Q := {seq(seq([seq(R[k],k=i..j)],j=i..n),i=1..n)};
 Q1 := select(J -> nops(J)>1,Q);

 for J in Q do
  m[J] := table();
  M := select(U -> ({op(J)} minus {op(U)} <> {}),Q);
  for i from 1 to nops(J) - 1 do
   M1 := select(U -> member(J[i],U) and member(J[i+1],U),M);
   m[J][J[i]] := mul(1-t[{op(U)}],U in M1);
  od;
 od;

 for T in P do 
  x[T] := table();
  i := min(op(map(a -> r[a],T)));
  j := max(op(map(a -> r[a],T)));
  J := [seq(R[k],k=i..j)];
  for k from i to j do
   if member(R[k],T) then
    x[T][R[k]] := [add(m[J][R[l]],l=i..k-1)];
   fi
  od;
 od;

 return eval(x);
end:
