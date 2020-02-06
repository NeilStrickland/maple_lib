`cartesian_product/sets` := proc()
 local A,P,a,p;
 if nargs = 0 then
  return {[]};
 else
  A := args[1];
  if not type(A,set) then
   error "Argument is not a set";
  fi;
  P := `cartesian_product/sets`(args[2..-1]);
  return {seq(seq([a,op(p)],p in P),a in A)};
 fi;
end:

`cartesian_product/lists` := proc()
 local A,P,a,p;
 if nargs = 0 then
  return [[]];
 else
  A := args[1];
  if not type(A,list) then
   error "Argument is not a list";
  fi;
  P := `cartesian_product/lists`(args[2..-1]);
  return [seq(seq([a,op(p)],p in P),a in A)];
 fi;
end:

