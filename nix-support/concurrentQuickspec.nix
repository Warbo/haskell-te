{ allDrvsIn, attrsToDirs, checkHsEnv, coreutils, extractedEnv,
  extraHaskellPackages, fail, haskellPackages, jq, lib, mkBin, nix, nixEnv,
  runCommand, testData, timeout, withDeps, wrap, writeScript }:
with builtins;
with lib;
with rec {
  untested = mkBin {
    name   = "concurrentQuickspec";
    paths  = [ coreutils ];
    vars   = {
      runner = wrap {
        name   = "explore-runner";
        paths  = [ fail jq timeout haskellPackages.mlspec nix ];
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

          # limit time/memory
          withTimeout MLSpec "$@" 2> >(checkForErrors 1>&2) | noDepth | jq -s '.'
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
        concurrentQuickspec < "$f" || fail "Exit failure for '$f'"
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

        function finish {
          if [[ -e serr ]]
          then
            echo -e "\n\nstderr:\n\n" 1>&2
            cat serr                  1>&2
          else
            echo "No stderr produced" 1>&2
          fi

          echo "COUNT: $COUNT" 1>&2
        }
        trap finish EXIT

        echo "Exploring '$f'" 1>&2
        RESULT=$(concurrentQuickspec < "$f" 2> serr | tee >(cat 1>&2)) ||
          fail "Equation finding failed for '$f'"

        if grep "No clusters found" < serr
        then
          fail "Did concurrentQuickspec receive any input?"
        fi

        COUNT=$(echo "$RESULT" | jq 'length')

        if [[ "$COUNT" -eq 0 ]]
        then
          echo -e "Couldn't find any equations in output of '$f'" 1>&2
        else
          echo "Found '$COUNT' equations for '$f'" 1>&2
        fi

        mkdir "$out"
      '';

    no-dupes = name: f: runCommand "no-dupes-for-${name}"
      {
        inherit f;
        buildInputs           = mkBuildInputs {};
        NIX_EVAL_HASKELL_PKGS = attrsToDirs {
                                  nix-support = ./.;
                                } + "/nix-support/customHs.nix";  # Relativity
        OUT_DIR               = getAttr name (testData.haskellNixed {});
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
        OUTPUT=$(concurrentQuickspec < "$f" 2>&1 | tee >(cat 1>&2)) ||
        fail "Failed to explore '$f'\nOUTPUT:\n\n$OUTPUT\n\n"

        echo "$OUTPUT" | noDupes
        mkdir "$out"
      '';
  };
};
withDeps (allDrvsIn checks) untested
