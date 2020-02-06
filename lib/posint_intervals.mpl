######################################################################
# Intervals in the set of positive integers

`is_element/posint_intervals` := proc(J)
 global reason;

 if not(type(J,set(posint)) or type(J,list(posint))) then
  reason := [convert(procname,string),"J is not a list or set of positive integers",J];
  return false;
 fi;

 if nops(J) = 0 or nops(J) <> max(op(J)) - min(op(J)) + 1 then
  reason := [convert(procname,string),"J is not an interval",J];
  return false;
 fi;

 return true;
end;

`is_equal/posint_intervals` := (J,K) -> evalb({op(J)} = {op(K)});

`is_leq/posint_intervals` := (J,K) -> evalb({op(J)} minus {op(K)} = {});

`random_element/posint_intervals` := proc()
 local a,b;
 a := rand(1..10)();
 b := rand(0..9)();
 [seq(i,i=a..a+b)];
end:

`list_elements/posint_intervals` := NULL;
`count_elements/posint_intervals` := NULL;
