defs: with defs;

let input  = "[ 1.2, 3.4 ]";
    output = parseJSON input;
 in assertMsg (output == [ "1.2" "3.4" ]) "Floats parse as strings"