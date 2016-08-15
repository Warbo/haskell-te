defs: with defs; with builtins; with lib;

let

memLimKb = (defs.callPackage ../nix-support/timeout.nix {}).memLimKb;

strippedContent = f:
  let content  = readFile f;
   in replaceStrings ["\n" " " "\t"]
                     [""   ""  ""]
                     content;

singleClusterFails =
  let output    = tipBenchmarks.process { quick = true; clusters = [ 1 ]; };
      explored  = head output.rawExplored.results."1";
      memUsageS = runScript { buildInputs = [ jq ]; } ''

                  '';
      memUsage  = addErrorContext "Parsing number from '${memUsageS}'"
                    (fromJSON memUsageS);
   in {
        shouldFail   = testDrvString "true"  output.failed              "TIP fails for 1 cluster";
        ann          = testDrvString "false" output.rawAnnotated.failed "TIP annotated for 1 cluster";
        dump         = testDrvString "false" output.rawDump.failed      "TIP dumped for 1 cluster";
        cluster      = testDrvString "false" output.rawClustered.failed "TIP clustered for 1 cluster";
        noRawExplore = testDrvString "true"  output.rawExplored.failed  "Can't explore 1 TIP cluster";
        noExplore    = testDrvString "true"  explored.failed            "Can't explore single TIP cluster";
        shouldOOM    = testRun "Exploring TIP ran out of memory on 1 cluster" null
                               { inherit (explored) stderr;
                                 limit = toString memLimKb; } ''
                                 MEM=$(grep -o "MAXMEM [0-9]*" < "$stderr" |
                                       grep -o "[0-9]*")

                                 if [[ -n "$MEM" ]]
                                 then
                                   echo "$MEM" > "$out"
                                 else
                                   exit 1
                                 fi
                                 [[ "$memUsage" -gt "$memLimKb" ]] || exit 1
                               '';
      };

multipleClustersPass =
  let num      = 40;

      output   = tipBenchmarks.process { quick = true; clusters = [ num ]; };

      explored = all (n: all (x: strippedContent x != "")
                             output.explored."${n}")
                     (attrNames output.explored);

      haveEqs  = all (n: strippedContent output.equations."${n}" != "")
                     (attrNames output.equations);

      nonZeroEqs = testRec
                     (mapAttrs (n: count:
                                 testRun "${n} equation count nonzero"
                                         null { inherit count; }
                                         ''
                                           X=$(cat "$count")
                                           O=$(echo "$X" | jq -r '. > 0')
                                           echo "count: $count"   1>&2
                                           echo -e "X: $X\nO: $O" 1>&2
                                           [[ "x$O" = "xtrue" ]] || exit 1
                                         '')
                               output.equationCounts);
   in {
        notFail    = testDrvString "false" output.failed
                                   "Explored TIP with ${toString num} clusters";

        explored   = testWrap [ explored   ] "Exploring TIP gave output";

        equations  = testWrap [ haveEqs    ] "Got TIP equations";

        nonZeroEqs = testWrap [ nonZeroEqs ] "Non-zero equation counts";
      };

withDbg = dbg: msg: x: addErrorContext dbg (testMsg x msg || trace dbg false);

in { inherit singleClusterFails multipleClustersPass; }
