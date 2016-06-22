with import ./. {}; with builtins;

let output = tipBenchmarks.process {
               clusters = [ 10 ];
               quick    = true;
               sampleSize = 10;
             };
 in trace (toJSON { inherit (output) rawClustered rawExplored rawReduced; }) "done"
