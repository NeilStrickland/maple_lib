######################################################################

`is_element/rel` := (A::set,B::set) -> proc(R)
 local AB,a,b;

 global reason;

 AB := [seq(seq([a,b],b in B),a in A)];

 if not type(R,set) then
  reason := [convert(procname,string),"R is not a set",R];
  return false;
 fi;

 if R minus {op(AB)} <> {} then
  reason := [convert(procname,string),"R is not a subset of AxB",R,A,B];
  return false;
 fi;

 return true;
end;

`is_equal/rel` := (A::set,B::set) -> proc(R,S)
 global reason;

 if R <> S then
  reason := [convert(procname,string),"R <> S",R,S];
  return false;
 fi;

 return true;
end;

`is_leq/rel` := (A::set,B::set) -> proc(R,S)
 global reason;

 if R minus S <> {} then
  reason := [convert(procname,string),"R is not a subset of S",R,S];
  return false;
 fi;

 return true;
end;

`bot/rel` := (A::set,B::set) -> {};
`top/rel` := (A::set,B::set) -> {seq(seq([a,b],b in B),a in A)};

`is_a_function/rel` := (A::set,B::set) -> proc(R)
 local r,N;

 r := `hash/rel`(A,B)(R);
 N := map(a -> nops(r[a]),A) minus {1};
 return evalb(N = {});
end;

`is_total/rel` := (A::set,B::set) -> (R) -> evalb(R = `top/rel`(A,B));

`op/rel` := (A::set,B::set) -> (R) -> map(ab -> [ab[2],ab[1]],R);

`hash/rel` := (A::set,B::set) -> proc(R)
 local r,a,b,ab;
 
 r := table();
 for a in A do r[a] := {}; od;
 for ab in R do
  a,b := op(ab);
  r[a] := {op(r[a]),b};
 od;

 return eval(r);
end:

`unhash/rel` := (A::set,B::set) -> proc(r)
 {seq(seq([a,b],b in r[a]),a in A)};
end;

`id/rel` := (A::set) -> {seq([a,a],a in A)};

`o/rel` := (A::set,B::set,C::set) -> proc(S,R)
 local r,s,sr,a;
 r := `hash/rel`(A,B)(R);
 s := `hash/rel`(B,C)(S);
 sr := table();
 for a in A do sr[a] := map(op,map(b -> s[b],r[a])); od;
 return `unhash/rel`(A,C)(sr);
end;

`list_elements/rel` := proc(A::set,B::set)
 local AB;
 AB := {seq(seq([a,b],b in B),a in A)};
 `list_elements/subsets`(AB);
end:

`count_elements/rel` := (A::set,B::set) -> 2^(nops(A)*nops(B));

`random_element/rel` := (A::set,B::set) -> proc(p_)
 local AB,p,R,r,ab;
 p := `if`(nargs > 0,p_,0.5);
 r := rand(0..10^6-1);
 AB := {seq(seq([a,b],b in B),a in A)};
 R := NULL;
 for ab in AB do
  if r() < 10^6 * p then R := R,ab; fi;
 od:
 R := {R};
 return R;
end:
