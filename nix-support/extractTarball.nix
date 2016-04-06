{ gnutar, storeResult, runScript, withNix }:
with builtins;
tarball:

runScript (withNix { buildInputs = [ gnutar ]; })
          ''
            set -e
            # Checking existence in the script avoids 'cannot refer to other
            # paths' errors with pathExists
            [[ -e "${tarball}" ]] || exit 2
            tar xf "${tarball}"
            for D in *
            do
              if [[ -d "$D" ]]
              then
                "${storeResult}" "$D" "$out"
                exit 0
              fi
            done
            exit 3
          ''
