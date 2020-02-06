N := 3;
A := {1,2,3,4,5,6};
TT := `random_element/trees`(A)();

check_map_generic("phi/nonempty_subsets/prime_simplex","nonempty_subsets","prime_simplex",[[A]]);
check_map_generic("centres/cubes","cubes","F",[[N],[A]]);
check_map_generic("fatten/F","F","cubes",[[N],[A]]);
check_map_generic("inc/F/Fbar","F","Fbar",[[N],[A]]);
check_map_generic("extend/tree_height_functions","tree_height_functions","height_functions",
                  [[A],[TT]],[[A],[TT]],[[A]]);
check_map_generic("critical_tree/Fbar","Fbar","full_trees",[[N],[A]],[[N],[A]],[[A]]);

N := 2;
A := {1,2,3,4,5};

check_map_generic("phi/SEM/SCQ","SEM","SCQ",[[N],[A]]);
check_map_generic("psi/SCQ/SEM","SCQ","SEM",[[N],[A]]);
check_map_generic("sigma/SEM/F","SEM","F",[[N],[A]]);
check_map_generic("mu/F/SEM","F","SEM",[[N],[A]]);
check_map_generic("phi2/Fbar/P2","Fbar","P2",[[N],[A]]);
check_map_generic("psi/Fbar/Q","Fbar","Q",[[N],[A]],[[N],[A]],[[A]]);
