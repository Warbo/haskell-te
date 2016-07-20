defs: with defs; with builtins;

let

memLimKb = (import ../nix-support/timeout.nix {
             inherit writeScript;
           }).memLimKb;

strippedContent = f:
  let content  = readFile f;
   in replaceStrings ["\n" " " "\t"]
                     [""   ""  ""]
                     content;

singleClusterFails =
  let output    = tipBenchmarks.process { quick = true; clusters = [ 1 ]; };
      explored  = head output.rawExplored.results."1";
      memUsageS = runScript { buildInputs = [ jq ]; } ''
                    grep -o "MAXMEM [0-9]*" < "${explored.stderr}" |
                    grep -o "[0-9]*" > "$out"
                  '';
      memUsage  = addErrorContext "Parsing number from '${memUsageS}'"
                    (fromJSON memUsageS);
      outOfMem  = memUsage > memLimKb;
      check     = c: m: testDbg c m (toJSON { inherit output memLimKb; });
   in testAll [
        (check output.failed "TIP fails for 1 cluster")

        (check (!output.rawAnnotated.failed) "TIP annotated for 1 cluster")

        (check (!output.rawDump.failed) "TIP dumped for 1 cluster")

        (check (!output.rawClustered.failed) "TIP clustered for 1 cluster")

        (check output.rawExplored.failed "Can't explore 1 TIP cluster")

        (check explored.failed "Can't explore single TIP cluster")

        (check outOfMem "Exploring TIP ran out of memory on 1 cluster")
      ];

multipleClustersPass =
  let num      = 40;

      output   = tipBenchmarks.process { quick = true; clusters = [ num ]; };

      explored = all (n: all (x: strippedContent x != "")
                             output.explored."${n}")
                     (attrNames output.explored);

      haveEqs  = all (n: strippedContent output.equations."${n}" != "")
                     (attrNames output.equations);

      nonZeroEqs = all (n: output.equationCounts."${n}" > 0)
                       (attrNames output.equationCounts);

      check    = c: m: testDbg c m (toJSON { inherit num output; });

   in testAll [
        (check (!output.failed) "Explored TIP with ${toString num} clusters")

        (check explored "Exploring TIP gave output")

        (check haveEqs  "Got TIP equations")

        (check nonZeroEqs "Non-zero equation counts")
      ];

withDbg = dbg: msg: x: addErrorContext dbg (testMsg x msg || trace dbg false);

in testAll [singleClusterFails multipleClustersPass]
