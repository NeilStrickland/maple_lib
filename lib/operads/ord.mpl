######################################################################
# Operad of orderings

`eta/ord` := (A::set) -> `if`(nops(A)=1,[op(A)],FAIL);

`gamma/ord` := (A::set,B::set) -> (p) -> proc(R,RR)
 local b;
 if not check_gamma_args(A,B,p,R,RR,`is_element/ord`) then
  return FAIL;
 fi;

 map(op,[seq(RR[b],b in R)]);
end;

