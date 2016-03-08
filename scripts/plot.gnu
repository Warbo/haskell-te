set terminal png
set output ofilename
set yrange [0:*]
plot filename using 1:2 with points
