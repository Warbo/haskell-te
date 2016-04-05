{ annotate, bc, buildPackage, cluster, dumpPackage, explore, extractTarball,
  haskellPackages, jq, lib, parseJSON, runScript, timeCalc }:
with builtins;
with lib;
with timeCalc;

{ clusters }:

let processPkg       = name: pkg: rec {
      # Original Haskell fields
      inherit name pkg;
      src = extractTarball pkg.src;

      # Building with regular GHC
      quickBuild = buildPackage { inherit src;
                                  quick = true;
                                  hsEnv = pkg.env; };
      slowBuild  = buildPackage { inherit src;
                                  quick = false;
                                  hsEnv = pkg.env; };

      # AST dumps
      quickDump = dumpPackage { quick = true;  inherit src; };
      slowDump  = dumpPackage { quick = false; inherit src; };

      # Annotated ASTs
      quickAnnotated = annotate { quick   = true;
                                  asts    = dump;
                                  pkgName = name; };
      slowAnnotated  = annotate { quick   = false;
                                  asts    = dump;
                                  pkgName = name; };

      # Clustered ASTs
      quickClustered = cluster { inherit annotated clusters;
                                 quick = true; };
      slowClustered  = cluster { inherit annotated clusters;
                                 quick = false; };

      # Exploration results
      quickExplored = explore { quick = true;  inherit clustered; };
      slowExplored  = explore { quick = false; inherit clustered; };

      # Stick to the quick output, so testing is faster
      dump      = quickDump.stdout;
      annotated = quickAnnotated.stdout;
      clustered = mapAttrs (n: v: v.stdout) quickClustered;
      explored  = mapAttrs (n: v: v.stdout) quickExplored;
      equations = trace "FIXME: Reduce equations" explored;

      # Useful for benchmarking
      equationCount = mapAttrs (_: f: parseJSON (runScript {} ''
        "${jq}/bin/jq" -s 'length' < "${f}" > "$out"
      '')) equations;

      # Total benchmark times (split up according to clusters)
      totalWithTime      = mapAttrs (c: _: sumWithTime [
                                      quickDump.time
                                    ]) equations;
      totalWithCriterion = mapAttrs (c: _: sumWithCriterion [
                                      slowDump.time
                                    ]) equations;
    };
 in mapAttrs processPkg haskellPackages
