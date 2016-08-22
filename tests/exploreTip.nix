defs: with defs; with builtins; with lib;

let

strippedContent = f: drvFromScript { inherit f; } ''
  tr -dc '\n\t ' < "$f" > "$out"
'';

nonEmpty = f: msg: testRun msg null { inherit f; s = strippedContent f; } ''
  C=$(cat "$s")
  echo "Using '$f', stripped '$s', got: $C" 1>&2
  [[ -n "$C" ]] || exit 1
'';

singleClusterFails =
  let output    = tipBenchmarks.process { quick = true; clusters = [ 1 ]; };
      explored  = head output.rawExplored.results."1";
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
                                   [[ "$MEM" -gt "$limit" ]] || exit 1
                                 else
                                   exit 1
                                 fi
                               '';
      };

multipleClustersPass =
  let num    = 10;
      output = tipBenchmarks.process { quick = true; clusters = [ num ]; };
   in trace "FIXME: Test these some other way; they take too long" {
        explored = mapAttrs (n: eqs: testFiles eqs "Non-empty explored"
                                       (writeScript "non-empty" ''
                                         C=$(cat "$1" | tr -dc '\n\t ')
                                         [[ -n "$C" ]] || exit 1
                                       ''))
                            output.explored;

        haveEqs  = mapAttrs (n: eqs: nonEmpty eqs "Non-empty ${n}")
                            output.equations;

        nonZeroEqs = mapAttrs (n: count:
                                testRun "${n} equation count nonzero"
                                        null { inherit count; } ''
                                          X=$(cat "$count")
                                          O=$(echo "$X" | jq -r '. > 0')
                                          echo "count: $count"   1>&2
                                          echo -e "X: $X\nO: $O" 1>&2
                                          [[ "x$O" = "xtrue" ]] || exit 1
                                        '')
                              output.equationCounts;

        notFail    = testDrvString "false" output.failed
                                   "Explored TIP with ${toString num} clusters";
      };

withDbg = dbg: msg: x: addErrorContext dbg (testMsg x msg || trace dbg false);

in { inherit singleClusterFails; }
