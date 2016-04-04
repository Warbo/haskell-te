defs: with defs;

let w          = "640";
    h          = "480";
    SvT        = plotSizeVsThroughput { foo = { label      = "FOO";
                                                size       = "123";
                                                throughput = "3.14"; };
                                        bar = { label      = "BAR";
                                                size       = "456";
                                                throughput = "2.72"; }; };
    checkPlot    = plot: assertMsg (pathExists plot)
                                   "Checking if plot '${plot}' exists";
    checkPlotDim = plot: parseJSON (runScript { buildInputs = [ file jq ]; } ''
                     set -e
                     echo "Checking '${plot}' bigger than ${w}x${h}" 1>&2
                     GEOM=$(file "${plot}" | # filename: foo, W x H, baz
                            cut -d : -f 2  | # bar, W x H,baz
                            cut -d , -f 2  ) # W x H
                     W=$(echo "$GEOM" | cut -d x -f 1)
                     H=$(echo "$GEOM" | cut -d x -f 2)

                     echo "Checking '$W'x'$H' against '${w}'x'${h}'" 1>&2
                     jq -n --argjson width  "$W" \
                           --argjson height "$H" \
                           '$width >= ${w} and $height >= ${h}' > "$out"
                   '');
 in all id [ (checkPlot SvT) (checkPlotDim SvT) ]
