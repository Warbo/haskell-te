defs: with defs; pkg:

# Render plots of just this one package

let getCvT  = c: data: { label      = pkg.name;
                         size       = c;
                         throughput = floatDiv pkg.equationCount."${c}"
                                               data.mean.estPoint; };
    CvTdata = mapAttrs getCvT pkg.totalWithTime;
    CvT     = plotSizeVsThroughput "Clusters" CvTdata;
 in checkPlot CvT
