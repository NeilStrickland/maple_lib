######################################################################
# Differential geometry of curves in R^3

analyse_curve := proc(x,t)
 local T;
 T := table():
 T["x"] := x;
 T["t"] := t;
 T["v"] := map(diff,x,t);
 T["speed"] := simplify(`norm_2/R`(3)(T["v"]));
 T["s"] := int(T["speed"],t);
 T["v_hat"] := simplify(T["v"] /~ T["speed"]);
 T["T"] := T["v_hat"];
 T["a"] := map(diff,T["v"],t);
 T["v_hat_dot"] := simplify(map(diff,T["v_hat"],t));
 T["curvature"] := simplify(`norm_2/R`(3)(T["v_hat_dot"]));
 T["N"] := simplify(T["v_hat_dot"] /~ T["curvature"]);
 T["radius_of_curvature"] := simplify(1/T["curvature"]);
 T["B"] := `cross_product`(T["T"],T["N"]);
 
 return eval(T);
end: