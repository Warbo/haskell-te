{ allDrvsIn, attrsToDirs, coreutils, extractedEnv,
  extraHaskellPackages, fail, haskellPackages, jq, lib, makeHaskellPkgNixable,
  mkBin, nix, nixEnv, runCommand, testData, timeout, withDeps, wrap,
  writeScript }:
with builtins;
with lib;
with rec {
  untested = mkBin {
    name   = "concurrentQuickspec";
    paths  = [ coreutils ];
    vars   = {
      runner = wrap {
        name   = "explore-runner";
        paths  = [ fail haskellPackages.mlspec jq makeHaskellPkgNixable nix
                   timeout ];
        vars   = nixEnv;
        script = ''
          #!/usr/bin/env bash
          set -e
          set -o pipefail

          function noDepth {
            grep -v "^Depth" || true # Don't abort if nothing found
          }

          function checkForErrors {
            ERR=0
            while read -r LINE
            do
              echo "$LINE"
              if echo "$LINE" | grep "No instance for" > /dev/null
              then
                ERR=1
              fi
            done
            [[ "$ERR" -eq 0 ]] || fail "Haskell error, aborting"
          }

          function nixify {
            for D in "$@"
            do
              makeHaskellPkgNixable "$D" | jq -R '.'
            done | jq -s '.'
          }

          if [[ -n "$OUT_DIRS" ]]
          then
            echo "Using existing OUT_DIRS" 1>&2
          else
            if [[ -n "$IN_BENCHMARK" ]]
            then
              fail "No OUT_DIRS in benchmark, aborting"
            else
              OUT_DIRS=$(nixify "$@")
              export OUT_DIRS
            fi
          fi

          # limit time/memory
          withTimeout MLSpec 2> >(checkForErrors 1>&2) | noDepth | jq -s '.'
        '';
      };
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      if [[ -n "$MAX_SECS" ]]
      then
        timeout "$MAX_SECS" "$runner" "$@"
      else
        "$runner" "$@"
      fi
    '';
  };

  data = mapAttrs
    (n: f: runCommand "data-${n}"
      {
        inherit f;
        buildInputs = [ jq ];
      }
      ''
        set -e
        jq '[map(select(.quickspecable))]' < "$f" > "$out"
      '')
    (testData.asts {});

  mkBuildInputs = args: extractedEnv args ++ [ untested fail ];

  checks = mapAttrs (_: f: mapAttrs f data) {
    exit-success = name: f: runCommand "exploreExitSuccess-${name}"
      {
        inherit f;
        buildInputs = mkBuildInputs {
          inherit f;
          standalone = getAttr name (testData.haskellNixed {});
        };
      }
      ''
        set -e
        OUTPUT=$(concurrentQuickspec < "$f") || {
          echo "$OUTPUT" 1>&2
          fail "Exit failure for '$f'"
        }
        mkdir "$out"
      '';

    find-equations = name: f: runCommand "find-equations-in-${name}"
      {
        inherit f;
        buildInputs = mkBuildInputs {
          inherit f;
          standalone = getAttr name (testData.haskellNixed {});
        };
      }
      ''
        set -e
        set -o pipefail

        DONE=0

        function finish {
          if [[ "$DONE" -eq 0 ]]
          then
            if [[ -e serr ]]
            then
              echo -e "\n\nstderr:\n\n" 1>&2
              cat serr                  1>&2
            else
              echo "No stderr produced" 1>&2
            fi

            echo "COUNT: $COUNT" 1>&2
          fi
        }
        trap finish EXIT

        echo "Exploring '$f'" 1>&2
        RESULT=$(concurrentQuickspec < "$f" 2> serr) || {
          echo "$RESULT" 1>&2
          fail "Equation finding failed for '$f'"
        }

        if grep "No clusters found" < serr
        then
          fail "Did concurrentQuickspec receive any input?"
        fi

        COUNT=$(echo "$RESULT" | jq 'length')

        if [[ "$COUNT" -eq 0 ]]
        then
          fail "Couldn't find any equations in output of '$f'"
        else
          echo "Found '$COUNT' equations for '$f'" 1>&2
        fi

        DONE=1

        mkdir "$out"
      '';

    no-dupes = name: f: runCommand "no-dupes-for-${name}"
      {
        inherit f;
        buildInputs           = mkBuildInputs {};
        nixed                 = [(getAttr name (testData.haskellNixed {}))];
        NIX_EVAL_HASKELL_PKGS = attrsToDirs {
                                  nix-support = ./.;
                                } + "/nix-support/customHs.nix";  # Relativity
      }
      ''
        set -e
        set -o pipefail

        function noDupes {
          echo "Removing dupes" 1>&2
          DUPES=$(grep "^building path.*repo-head" |
                  sed -e 's/.*head-//g'            |
                  sort                             |
                  uniq -D) || DUPES=""
          [[ -z "$DUPES" ]] || {
            echo "Made redundant package lookups: $DUPES" 1>&2
            exit 1
          }
        }

        echo "Exploring '$f'" 1>&2
        OUTPUT=$(concurrentQuickspec "$nixed" < "$f" 2>&1) || {
          echo "$OUTPUT" 1>&2
          fail "Failed to explore '$f'"
        }

        echo "$OUTPUT" | noDupes
        mkdir "$out"
      '';
  };
};
withDeps (allDrvsIn checks) untested
