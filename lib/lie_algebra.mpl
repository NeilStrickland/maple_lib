# This is a generic bracket operation.  With more than two arguments,
# it represents an iterated bracket associated like [a,[b,[c,[d,e]]]].
# Multilinearity rules are applied automatically, and the Jacobi
# rule is also used automatically to convert other kinds of iterated
# brackets into the fully right associated form.

bracket := proc()
 local n,m,i,j,u,a,b,c,v,ac,av,x,y;
 n := nargs;
 for i from 1 to n do
  u := seq(args[j],j=1..i-1);
  a := args[i];
  v := seq(args[j],j=i+1..n);
  if type(a,`+`) then
   return map(t -> bracket(u,t,v),a);
  elif type(a,`*`) then
   ac,av := selectremove(type,a,rational);
   if ac <> 1 then
    return ac * bracket(u,av,v);
   fi;
  elif type(a,specfunc(bracket)) then
   if i = n then
    return bracket(u,op(a));
   else
    b := op(1,a);
    c := bracket(op(2..-1,a));
    if nops(c) = 1 then c := op(c); fi;
    return bracket(u,b,c,v) - bracket(u,c,b,v);
   fi;
  fi;
 od;

 if type(args[n],specfunc(bracket)) then
  return bracket(args[1..n-1],op(args[n]));
 fi;
 
 return 'procname'(args);
end:

