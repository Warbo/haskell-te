defs: with defs; with lib; with builtins;

let samples = filter (hasSuffix ".json") (attrNames (readDir ../benchmarks/tip));
    files   = listToAttrs (map (f: { name = f; value = ../benchmarks/tip + "/${f}"; })
                               samples);

    asts = (dumpPackage {
      quick = true;
      src = import (nixedHsPkg "${tipBenchmarks.tip-benchmarks}" null);
    }).stdout;

    testFile = let find = writeScript "find.jq" ''
      def match($x): .name    == $x.name    and
                     .package == $x.package and
                     .module  == $x.module;


    '';
    in f: testRun "${f}" { inherit asts f; } {} ''
      jq -c '.[]' < "${f}" | while read -r OBJ
      do
        jq -e --argjson obj "$OBJ" \
           'map(.name    == $obj.name    and
                .package == $obj.package and
                .module  == $obj.module) | any' < "${asts}" > /dev/null || {
          echo "Sampled name '$OBJ' doesn't appear in '${asts}'" 1>&2
          exit 1
        }
      done
    '';
in {
  benchmarkTests = mapAttrs (_: testFile) files;
}
