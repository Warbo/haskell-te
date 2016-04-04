defs: with defs;

let plot = plotSizeVsThroughput { foo = { label      = "FOO";
                                          size       = "123";
                                          throughput = "3.14"; };
                                  bar = { label      = "BAR";
                                          size       = "456";
                                          throughput = "2.72"; }; };
    checkPlot = assertMsg (pathExists plot) "Checking if plot '${plot}' exists";
 in all id [ checkPlot ]
