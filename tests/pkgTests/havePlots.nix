defs: with defs; pkg:

# Render plots of just this one package

let data = { "0" = { label = "Bogus"; size = "123"; throughput = "12.5"; }; };
    plot = plotSizeVsThroughput data;
 in parseJSON (runScript {} ''
      set -e
      echo "Checking plot '${plot}'" 1>&2
      if [[ -f "${plot}" ]]
      then
        echo "true"  > "$out"
      else
        echo "false" > "$out"
      fi
    '')