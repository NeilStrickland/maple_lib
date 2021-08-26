N := 3;
A := {1,2,3,4,5,6,7,8};
B := {10,20,30,40};
C := {11,22,33};

check_operad("comm",[],A,B,C);

check_operad("ord",[],A,B,C);

check_operad("nonempty_subsets",[],A,B,C);

check_operad("partitions",[],A,B,C);

check_operad("trees",[],A,B,C);

check_operad("full_trees",[],A,B,C);

check_operad("simplex",[],A,B,C);

check_operad("simplex_interior",[],A,B,C);

check_operad("ord_simplex_interior",[],A,B,C);

check_operad("prime_simplex",[],A,B,C);

check_operad("cubes",[[N]],A,B,C);

check_operad("one_cubes_prime",[],A,B,C);

check_operad("stasheff_trees",[],A,B,C);

check_operad("stasheff_star",[],A,B,C);

# Deferred, because we have not defined `random_element/height_functions`
#check_operad("height_functions",[],A,B,C);
#check_operad("Fbar",[[N]],A,B,C);
