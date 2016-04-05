defs: with defs;

let SvT = plotSizeVsThroughput { foo = { label      = "FOO";
                                         size       = "123";
                                         throughput = "3.14"; };
                                 bar = { label      = "BAR";
                                         size       = "456";
                                         throughput = "2.72"; }; };
 in checkPlot SvT
