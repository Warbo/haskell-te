{}:
{ repetitions ? 2, shuffledPackages }:

let bench = pkg: runScript {} ''
      set -e
      # Check as many pre-conditions as we can here
      for CMD in annotateDb build-env cabal cabal2nix cluster dump-format \
                 dump-package dump-package-env dump-package-name jq \
                 mlspec-bench \
                 nix-shell runAstPlugin time
      do
        command -v "$CMD" > /dev/null || {
          echo "Need '$CMD'" 1>&2
          exit 1
        }
      done

      function pkgInList {
        touch "$CACHE/$2"
        grep -Fx -- "$1" < "$CACHE/$2" > /dev/null
      }

    # Make sure we run all clusters for this package
    while read -r CLUSTERS
    do
        "$BASE/benchmarks/benchmark-explore.sh"  "$DIR" "$CLUSTERS" || {
            echo "$PKG" >> "$CACHE/unexplorable"
            continue
        }
        "$BASE/benchmarks/benchmark-simplify.sh" "$DIR" "$CLUSTERS"
    done < <(clusterNums)

    echo "$PKG" >> "$CACHE/finished"
''
