{ tipBenchmarks }:
with builtins;

let clusters    = [ 1 2 4 8 16 32 ];
     sampleNums = [];#[ 1 2 4 8 16 32 ];

    outputs =
      let runSamples = sampleSize: {
                         name  = toString sampleSize;
                         value = tipBenchmarks.process {
                                   inherit clusters sampleSize;
                                   quick = true;
                                 };
                       };
       in listToAttrs (map runSamples sampleNums);
 in outputs
