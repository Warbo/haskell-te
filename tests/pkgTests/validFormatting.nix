defs: with defs; pkg:
with lib;
with builtins;

let check = data: drvFromScript { buildInputs = [ jq ]; inherit data; } ''
      set -e
      LENGTH=$(jq -c 'length' < "$data") || {
        echo "Can't read formatted cluster from '$data' for '${pkg.name}'" 1>&2
        exit 2
      }
      touch "$out"
    '';

    checkInner = lst:
      listToAttrs (map (data: { name  = hashString "sha256"
                                          (unsafeDiscardStringContext
                                            data.outPath);
                                value = check data; })
                       lst);

 in mapAttrs (_: checkInner) pkg.formatted
