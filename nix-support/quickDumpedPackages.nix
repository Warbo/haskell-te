{ dumpToNix, runScript, gnutar, haskellPackages, lib, withNix }:
with builtins; with lib;

let extract = tarball:
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
                          '';
    dumpPkg = src: dumpToNix (extract "${src}");
    addDump = pkg: old: old // builtins.listToAttrs [{
                                 name  = pkg;
                                 value = dumpPkg "${haskellPackages."${pkg}".src}";
                               }];
 in fold addDump {}
         (attrNames haskellPackages)
