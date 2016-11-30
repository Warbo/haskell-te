{ runCmd, checkFailures, drvFromScript, explore, ML4HSFE, runWeka, stdParts,
  storeParts, writeScript }:
with builtins;

let

clusterScript = writeScript "cluster" ''
  set -e
  [[ -n "$WIDTH"  ]] ||  WIDTH=30
  [[ -n "$HEIGHT" ]] || HEIGHT=30
  export WIDTH
  export HEIGHT
  "${ML4HSFE}/bin/ml4hsfe-outer-loop"
'';

cluster = { annotated, clusters }: let

  go = c: drvFromScript { buildInputs = explore.extractedEnv {
                                          #f         = annotated;
                                          extraPkgs = [ runWeka   ];
                                        };
                          inherit annotated;
                          outputs = stdParts; } ''
              set -e
              export CLUSTERS="${toString c}"
              O=$("${runCmd {
                       cmd    = clusterScript;
                   }}" < "$annotated")

              ${storeParts}
            '';

  results = listToAttrs (map (c: { name  = toString c;
                                   value = go c; })
                        clusters);

  result = { inherit results;
             failed = checkFailures "any" results;
           };

  in result;

in { inherit cluster clusterScript; }
