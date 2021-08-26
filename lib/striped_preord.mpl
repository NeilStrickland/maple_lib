# A striped preorder is one for which comparability is an equivalence relation

######################################################################

`is_element/striped_preord` := (A::set) -> proc(R)
 local E;
 global reason;

 if not `is_element/preord`(A)(R) then
  reason := [convert(procname,string),"R is not a preorder on A",R,A,reason];
  return false;
 fi;

 E := R union `op/autorel`(A)(R);
 
 if not(`is_transitive/autorel`(A)(E)) then
  reason := [convert(procname,string),"R u R^op is not transitive",R];
  return false;
 fi;
 
 return true;
end;

######################################################################

`is_equal/striped_preord`     := eval(`is_equal/autorel`);
`is_leq/striped_preord`       := eval(`is_leq/preord`);
`is_separated/striped_preord` := eval(`is_separated/autorel`);

`op/striped_preord` := eval(`op/autorel`);

######################################################################
# A075729

`count_elements/striped_preord` := proc(A::set)
 local n,x,egf;
 n := nops(A);
 egf := convert(series(exp(1/(2-exp(x))-1),x=0,n+1),polynom,x):
 return n! * coeff(egf,x,n);
end:

######################################################################

`list_elements/striped_preord` := proc(A::set)
 local RR,PI,pi,LL,QQ,B,Q,L;

 RR := [];

 PI := `list_elements/partitions`(A);
 for pi in PI do
  LL := [{}];
  for B in pi do
   QQ := `list_elements/total_preord`(B);
   LL := [seq(seq(L union Q,Q in QQ),L in LL)];
  od;
  RR := [op(RR),op(LL)];
 od:

 return RR;
end:

######################################################################
# Note that the function below is not actually a rank function, but
# it is an ingredient in certain rank functions to be defined 
# elsewhere.

`rank/preord` := (A::set) -> proc(R)
 nops(`block_partition/preord`(A)(R));
end:

######################################################################

`random_element/striped_preord` := (A::set) -> proc()
 local pi,Q,B;

 pi := `random_element/partitions`(A)();
 Q := {};
 for B in pi do 
  Q := Q union `random_element/total_preord`(B)();
 od;
 return Q;
end:


######################################################################
# Returns a striped preorder R0 > R with 
# (or FAIL if R is already maximal).

`bump/striped_preord` := (A::set) -> proc(R)
 local pi,B,a,b,B0,R0;

 pi := `block_partition/preord`(A)(R);

 for B in pi do 
  if nops(B) > 1 then
   a := B[1];
   B0 := B minus {a};
   R0 := R minus {seq([b,a],b in B0)};
   return R0;
  fi;
 od;

 return FAIL;
end:

######################################################################
# Returns a striped preorder R1 with R < R0 <= S 
# (or FAIL if this is impossible)

`relative_bump/striped_preord` := (A::set) -> proc(R,S)
 local pi,B,BB,SB,C,a,b,c,B0,R0;

 pi := `block_partition/preord`(A)(R);

 for B in pi do 
  BB := `top/autorel`(B);
  SB := S intersect BB;
  if BB minus S <> {} then
   for a in B do
    C := select(b -> member([b,a],SB) and not(member([a,b],SB)),B);
    if C = {} then
     B0 := B minus {a};
     R0 := R minus {seq([b,a],b in B0)};
     return R0;
    fi;
   od;
   return FAIL; # should not happen
  fi;
 od;

 return FAIL;
end:

######################################################################

`describe/striped_preord` := (A::set) -> proc(R)
 local s0,s1,s2,pi,B,C,r,m,j,k,c;

 s0 := "";
 pi := `block_partition/preord`(A)(R union `op/autorel`(A)(R));
 for B in pi do
  r := `rank_table/preord`(B)(R intersect `top/autorel`(B));
  m := max(map(b -> r[b],B));
  s1 := "";
  for j from 0 to m do 
   C := select(b -> r[b]=j,B);
   s2 := "";
   for k from 1 to nops(C) do 
    s2 := cat(s2,`if`(k>1,"=",""),sprintf("%A",C[k]));
   od:
   s1 := cat(s1,`if`(j>0,"<",""),s2);
  od;
  s0 := cat(s0,`if`(s0="","",","),s1);
 od:

 return s0;
end:
