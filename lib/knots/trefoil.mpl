#@ Not autoload

# This gives a two-parameter family of embeddings of the trefoil in R^3

trefoil0 := proc(t,a,b)
 [(1 + a * cos(3 * t)) * cos(2 * t),
  (1 + a * cos(3 * t)) * sin(2 * t),
  b * sin(3 * t)]
end:

# This is a particular embedding from the above family for which the
# speed is just sqrt(8)*(1 + 2/3 * cos(3*t)).  For a typical element
# of the above family, the speed is a much more complicated function.

trefoil := (t) -> trefoil0(t,2/3,2/9*sqrt(7));

Trefoil := table():

Trefoil["x"] := trefoil(t,2/3,2*sqrt(7)/9);
Trefoil["t"] := t;
Trefoil["v"] := combine(simplify(expand(map(diff,Trefoil["x"],t)))) assuming t > 0;
Trefoil["speed"] := combine(simplify(factor(expand(`norm_2/R`(3)(Trefoil["v"]))))) assuming t > 0;
Trefoil["s"] := int(Trefoil["speed"],t);
Trefoil["v_hat"] := combine(factor(expand(Trefoil["v"] /~ Trefoil["speed"]))) assuming t > 0;
Trefoil["T"] := Trefoil["v_hat"];
Trefoil["a"] := map(diff,Trefoil["v"],t);
Trefoil["v_hat_dot"] := combine(factor(expand(map(diff,Trefoil["v_hat"],t)))) assuming t > 0;
Trefoil["curvature"] := combine(simplify(factor(expand(`norm_2/R`(3)(Trefoil["v_hat_dot"]))))) assuming t > 0;
Trefoil["radius_of_curvature"] := simplify(1/Trefoil["curvature"]);
Trefoil["N"] := factor(combine(factor(expand(rationalize(Trefoil["v_hat_dot"] /~ Trefoil["curvature"]))))) assuming t > 0;
Trefoil["B"] := factor(combine(factor(expand(`cross_product`(Trefoil["T"],Trefoil["N"]))))) assuming t > 0;



