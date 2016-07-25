#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq

# Try to "realise" (build) each derivation

PKG_PATH=$(nix-instantiate --eval -E "<nixpkgs>")
export PKG_PATH

while read -r DRV
do
    nix-store -r "$DRV" --show-trace -j 1
done < <(./eval.sh 2>/dev/null | jq -sr '.[] | .[] | .drvPath')
