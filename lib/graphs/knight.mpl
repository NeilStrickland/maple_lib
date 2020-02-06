knights_tour_map := [
 [ 0, 5, 2,57,62,15,18,21],
 [ 3,56,63,14, 9,20,61,16],
 [ 6, 1, 4,43,58,17,22,19],
 [55,44,27, 8,13,10,39,60],
 [28, 7,42,45,40,59,12,23],
 [51,54,49,26,11,36,33,38],
 [48,29,52,41,46,31,24,35],
 [53,50,47,30,25,34,37,32]
];

knights_tour_pos := table():
knights_tour_opos := table():

for i from 0 to 7 do
 for j from 0 to 7 do
  knights_tour_pos[knights_tour_map[i+1,j+1]] := [i,j];
  knights_tour_opos[knights_tour_map[i+1,j+1]] := [i,j] +~ [0.5,0.5];
 od:
od:
knights_tour_pos[64] := knights_tour_pos[0]:
knights_tour_opos[64] := knights_tour_opos[0]:

chess_grid := display(
 seq(line([i,0],[i,8],colour=grey),i=0..8),
 seq(line([0,i],[8,i],colour=grey),i=0..8),
 scaling=constrained,axes=none
):

shaded_chess_grid := display(
 seq(seq(rectangle([2*i+1,2*j+1],[2*i+2,2*j],colour=grey),j=0..3),i=0..3),
 seq(seq(rectangle([2*i,2*j+2],[2*i+1,2*j+1],colour=grey),j=0..3),i=0..3),
 chess_grid
);

knights_tour_plot := display(
 shaded_chess_grid,
 seq(line(knights_tour_opos[i],knights_tour_opos[i+1],colour=red),i=0..63),
 scaling=constrained,axes=none
);

is_knight_move := (u,v) -> evalb({op(map(abs,u -~ v))} = {1,2});

check_knights_tour := proc()
 evalb(sort(map(op,knights_tour_map)) = [seq(i,i=0..63)]) and
 `and`(seq(is_knight_move(knights_tour_pos[i],knights_tour_pos[i+1]),i=0..63));
end:
