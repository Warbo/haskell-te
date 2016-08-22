{ parseJSON, runScript, storeResult, wget, writeScript }:
with builtins;

let listUrl = "http://hackage.haskell.org/packages/index.tar.gz";

    packageList = runScript { buildInputs = [ wget ]; } ''
      set -e
      wget -O "index.tar.gz" "${listUrl}"
      "${storeResult}" index.tar.gz
    '';

    extractVersions = writeScript "extract-versions" ''
      PKG=""
      LATEST=""
      while read -r LINE
      do
        THIS_PKG=$(echo "$LINE" | cut -d / -f 1)
        if ! [[ "x$PKG" = "x$THIS_PKG" ]]
        then
          # Reached a new package; report the latest version of the last one
          [[ -z "$PKG" ]] || echo -e "$PKG\t$LATEST"

          # Start tracking this package instead
          PKG="$THIS_PKG"
        fi

        # Bump the latest version we've seen
        LATEST=$(echo "$LINE" | cut -d / -f 2)
      done < <(tar -zt < "${packageList}" | grep -o '[^/][^/]*/[0-9][^/]*')

      echo -e "$PKG\t$LATEST"
    '';

    shuffled = runScript {} ''
      set -e
      "${extractVersions}" | uniq | shuf > shuffled
      "${storeResult}" shuffled
    '';

    given  = getEnv "SHUFFLED_LIST";
    stored = ../data/shuffled;
    file   = if given == ""
                then if pathExists stored
                        then trace "Using existing packages ${toString stored}"
                                   stored
                        else trace "No package list found, generating new one"
                                   shuffled
                else trace "Using package list from SHUFFLED_LIST ${given}"
                           given;
in parseJSON (runScript {} ''
  set -e
  cut -f 1 < "${file}" | jq -R '.' | jq -s '.' > "$out"
'')
