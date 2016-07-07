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
   in all (x: x) [
        (check output.failed "TIP fails for 1 cluster")

        (check (!output.rawAnnotated.failed) "TIP annotated for 1 cluster")

        (check (!output.rawDump.failed) "TIP dumped for 1 cluster")

        (check (!output.rawClustered.failed) "TIP clustered for 1 cluster")

        (check output.rawExplored.failed "Can't explore 1 TIP cluster")

        (check explored.failed "Can't explore single TIP cluster")

        (check outOfMem "Exploring TIP ran out of memory on 1 cluster")
      ];

output = tipBenchmarks.process { quick = true; };

explored = all (n: all (x: strippedContent x != "")
                       output.explored."${n}")
               (attrNames output.explored);

haveEqs = all (n: strippedContent output.equations."${n}" != "")
              (attrNames output.equations);

nonZeroEqs = all (n: output.equationCounts."${n}" > 0)
                 (attrNames output.equationCounts);

withDbg = dbg: msg: x: addErrorContext dbg (testMsg x msg || trace dbg false);

in all (x: x) [

  singleClusterFails

  (testDbg (!output.failed)  "TIP benchmark didn't fail"
           (toJSON { inherit (output) rawDump rawAnnotated rawClustered
                             formatted rawExplored rawReduced; }))

  (testDbg explored          "TIP benchmark explored"
           (toJSON { inherit (output) formatted rawExplored; }))

  (testDbg haveEqs    "Got TIP equations"
           (toJSON { inherit (output) formatted annotated clustered explored
                     equations; }))
  (testDbg nonZeroEqs "Non-zero equation counts"
           (toJSON { inherit (output) equationCounts; }))
]
