{ bash, drvFromScript, gnutar }:
with builtins;
tarball:

with {
  extracted = drvFromScript { buildInputs = [ gnutar ]; } ''
    #!${bash}/bin/bash
    set -e

    # Checking existence in the script avoids 'cannot refer to other
    # paths' errors with pathExists
    [[ -e "${tarball}" ]] || exit 2
    tar xf "${tarball}"
    for D in *
    do
      if [[ -d "$D" ]]
      then
        nix-store --add "$D" > "$out"
        exit 0
      fi
    done
    exit 3
  '';
};

import extracted
