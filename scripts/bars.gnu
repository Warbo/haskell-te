set terminal pngcairo font "arial,10" size 500,500
set output ofilename

set boxwidth 0.75 absolute
set style fill solid 1.00 border -1
set style data histogram
set style histogram cluster gap 1
set xtics rotate by -90

set title "ML4HS overhead compared to GHC"
set ylabel "Total time (seconds)"
set xlabel "Package"

plot filename using 2:xtic(1) title col, \
           '' using 3:xtic(1) title col, \
     
