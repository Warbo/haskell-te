{ gnutar, runScript, withNix }:
with builtins;
tarball:

assert pathExists (unsafeDiscardStringContext tarball);
runScript (withNix {
            inherit tarball;
            buildInputs = [ gnutar ];
          })
          ''
            tar xf "$tarball"
            for D in *
            do
              if [[ -d "$D" ]]
              then
                RESULT=$(nix-store --add "$D") || exit 1
                printf '%s' "$RESULT" > "$out"
                exit 0
              fi
            done
            exit 1
          ''
