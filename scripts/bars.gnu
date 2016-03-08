set terminal pngcairo font "arial,10" size 500,500
set output ofilename
set boxwidth 0.75
set style fill solid
set title "ML4HS overhead compared to GHC"
plot filename using 2:xtic(1) with boxes
