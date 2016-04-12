{ benchmark, parseJSON, recurrent-clustering, runScript, withNix }:
with builtins;

{ quick, annotated, clusters }:

let

go = c: parseJSON
          (runScript
            (withNix { buildInputs = [ recurrent-clustering ]; })
            ''
              set -e
              export CLUSTERS="${toString c}"
              "${benchmark quick "cluster" []}" < "${annotated}" > "$out"
            '');

result = listToAttrs (map (c: { name  = toString c;
                                value = go c; })
                     clusters);

in

assert isAttrs result;
assert all (n: isInt (fromJSON n))   (attrNames result);
assert all (n: result.${n} ? stdout) (attrNames result);
assert all (n: result.${n} ? time)   (attrNames result);

result
