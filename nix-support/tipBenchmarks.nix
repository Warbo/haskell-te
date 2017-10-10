{ annotated, asv-nix, bash, callPackage, fetchFromGitHub, fetchgit,
  haskellPackages, jq, nix-config, nix-config-src, nixFromCabal, nixpkgs-src,
  runCommand, stable, stdenv, tryElse, writeScript }:

with builtins;
with rec {
  path = tryElse <te-benchmarks> (nix-config.latestGit {
    url    = http://chriswarbo.net/git/theory-exploration-benchmarks.git;
    stable = {
      rev    = "ccf838d";
      sha256 = "1isbzv29903fh3m1sikj6gyaylq6wcw042wxna1g6k8wnlac9xjb";
    };
  });

  tebench  = callPackage path {
    inherit asv-nix haskellPackages nix-config-src;

    # Nixpkgs 17.03 disables Racket on i686, so always use 16.09 (for now)
    pkgsPath = nix-config.repo1609;
  };

  # Tests

  dep = "global746970323031352f62696e5f646973747269622e736d7432706c7573";

  canFindCommutativity = runCommand "can-find-commutativity"
    {
      precRec = runCommand "pr"
        {
          commEqs = runCommand "commutativityEqs.json"
            {
              commRunner = runCommand "commutativityExplorer"
                {
                  commDeps = runCommand "commDeps"
                    (tebench.cache // {
                      getCommDeps = writeScript "getCommDeps.rkt" ''
                        #lang racket
                        (require (file "${path}/scripts/lib/normalise.rkt"))
                        (require (file "${path}/scripts/lib/theorems.rkt"))
                        (for ([dep (theorem-deps-of "tip2015/bin_plus_comm.smt2")])
                             (write (encode-lower-name dep)))
                      '';
                      buildInputs = [ tebench.env ];
                    })
                    ''
                      racket "$getCommDeps" > "$out"
                    '';
                  asts        = testData.asts.teBenchmark;
                  OUT_DIR     = nixify testData.haskellPkgs.teBenchmark;
                  buildInputs = [ filterToSampled genQuickspecRunner jq ];
                }
                ''
                  SAMPLE=$(cat "$commDeps")
                  export SAMPLE

                  R=$(filterToSampled < "$asts" | genQuickspecRunner)
                  ln -s "$R" "$out"
                '';
            }
            ''
              "$commRunner" > "$out"
            '';
          SAMPLED_NAMES = dep;
          buildInputs   = [ tebench.tools ];
        }
        ''
          decode < "$commEqs" | conjectures_for_sample > "$out"
        '';
      buildInputs = [ jq ];
    }
    ''
      set -e
      jq -e '.precision | . > 0' < "$precRec"
      jq -e '.recall    | . > 0' < "$precRec"
      mkdir "$out"
    '';

  checkParamTypes = runCommand "can-find-properties-of-parameterised-types"
    (withNix {
      buildInputs  = [ fail jq tebench.tools ];
      eqs          = testData.eqs.list-full;
      GROUND_TRUTH = ../benchmarks/ground-truth/list-full.smt2;
      TRUTH_SOURCE = ../benchmarks/ground-truth/list-full.smt2;
    })
    ''
      set -e
      set -o pipefail
      RESULT=$(echo "$eqs" | precision_recall_eqs)
      echo "$RESULT" | jq -e '.recall | . > 0' || fail "No recall"
      mkdir "$out"
    '';
};
rec {
  inherit (tebench)
    tip-benchmarks cache env tools tip-benchmark-haskell tip-benchmark-smtlib;
  annotatedAsts = annotated { pkgDir = tip-benchmark-haskell; };
  pkg           = haskellPackages.callPackage pkgDef {};
  pkgDef        = nixFromCabal (toString tip-benchmark-haskell) null;
}
