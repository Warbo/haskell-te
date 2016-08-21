{ benchmark, checkFailures, drvFromScript, explore, jq, ML4HSFE, parseJSON,
  runScript, runWeka, stdParts, storeParts, writeScript }:
with builtins;

let

clusterScript = writeScript "cluster" ''
  set -e
  export WIDTH=30
  export HEIGHT=30
  ml4hsfe-outer-loop
'';

cluster = { quick, annotated, clusters }: let

  go = c: drvFromScript { buildInputs = explore.extractedEnv {
                                          #f         = annotated;
                                          extraPkgs = [ runWeka   ];
                                          extraHs   = [ "ML4HSFE" ];
                                        };
                          inherit annotated;
                          outputs = stdParts; } ''
              set -e
              export CLUSTERS="${toString c}"
              O=$("${benchmark {
                       inherit quick;
                       cmd    = clusterScript;
                       #inputs = [annotated];
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

in cluster
