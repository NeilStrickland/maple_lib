# Elliptic curves in Edwards form
# (This is rudimentary; there is a LaTeX file with much more material.)

`rels/edwards` := (a) -> proc(u)
 [-u[1]^2 + u[2]^2 - u[3]^2 + u[4]^2,a * u[2]*u[4] - u[1]*u[3]];
end: 

`is_element/edwards_curve` := (a) -> proc(u)
 if not(`is_element/CP`(3)(u)) then return false; fi;
 return evalb(simplify(`rels/edwards`(a)(u)) = [0,0]);
end:

