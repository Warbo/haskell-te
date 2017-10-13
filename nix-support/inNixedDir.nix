{ mkBin, nix-config }:

mkBin {
  name   = "inNixedDir";
  paths  = [ nix-config.inNixedDir ];
  script = ''
    #!/usr/bin/env bash
    set -e
    if [[ "$SKIP_NIX" -eq 1 ]]
    then
      NAME="nixed-dir"
      [[ -z "$2" ]] || NAME="$2"
      mkdir -p "$NAME"
      pushd "$NAME" > /dev/null
        "$1"
      popd          > /dev/null
      readlink -f "$NAME"
    else
      inNixedDir "$@"
    fi
  '';
}
