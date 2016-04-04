defs: with defs; pkg:
with builtins;

let check = c: data: parseJSON (runScript { buildInputs = [ jq ]; } ''
      set -e
      echo "Looking for equations in '${data}'" 1>&2
      grep -c '^' < "${data}" # set -e will treat no matches as an error
      echo "true" > "$out"
    '');
    result   = src: c:
      assertMsg (mapAttrs check src)."${toString c}"
                "Equations for '${pkg.name}' in ''${toString c}' clusters";
    checkAll = src: all (result src) defaultClusters;
 in checkAll pkg.explored && checkAll pkg.preExplored
