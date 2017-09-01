{ bash, genQuickspecRunner, lib, nixify, runCommand, testData, wrap }:

with rec {
  inherit (builtins) attrNames filter getAttr listToAttrs readDir readFile
                     toJSON;
  inherit (lib) genAttrs hasSuffix nameValuePair removeSuffix;

  names = map (removeSuffix ".smt2")
              (filter (hasSuffix ".smt2") (attrNames (readDir ./.)));

  benchmarks = listToAttrs (map (n: nameValuePair n (mkBench n)) names);

  mkBench = n: {
    content      = readFile (./. + "/${n}.smt2");
    ground_truth = readFile (./ground-truth + "/${n}.smt2");
    runner       = runCommand "quickspec-runner-${n}"
      {
        buildInputs = [ genQuickspecRunner ];
        OUT_DIR     = nixify (getAttr n testData.haskellPkgs);
        asts        = getAttr n testData.asts;
      }
      ''
        X=$(genQuickspecRunner < "$asts")
        ln -s "$X" "$out"
      '';

    analyser = wrap {
      name   = "analyser-${n}";
      paths  = [ bash ];
      vars   = rec {
        GROUND_TRUTH = ./ground-truth + "/${n}.smt2";
        TRUTH_SOURCE = GROUND_TRUTH;
      };
      script = ''
        #!/usr/bin/env bash
        set -e
        set -o pipefail
        precision_recall_eqs
      '';
    };
  };
};

toJSON benchmarks
