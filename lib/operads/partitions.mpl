######################################################################

`eta/partitions` := (A::set) -> `if`(nops(A)=1,{A},FAIL);

`gamma/partitions` := (A::set,B::set) -> (p) -> proc(pi,omega)
 local F,rho,u,v,b;

 F := fibres(A,B)(p);

 rho := NULL;
 for u in pi do
  if nops(u) = 1 then
   b := op(u);
   rho := rho,op(omega[b]);
  else
   rho := rho,`union`(seq(F[b],b in u));
  fi;
 od;

 rho := {rho};
 return rho;
end;
