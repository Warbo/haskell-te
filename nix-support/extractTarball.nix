{ bash, gnutar, runCommand }:

tarball: runCommand "extract-tarball"
  {
    inherit tarball;
    buildInputs = [ bash gnutar ];
  }
  ''
    #!/usr/bin/env bash
    set -e

    # Checking existence in the script avoids 'cannot refer to other
    # paths' errors with pathExists
    [[ -e "$tarball" ]] || exit 2
    mkdir extracted
    pushd extracted
      tar xf "$tarball"
      for D in *
      do
        if [[ -d "$D" ]]
        then
          mv "$D" "$out"
          exit 0
        fi
      done
    popd
    exit 3
  ''
