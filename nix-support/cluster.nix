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

results = listToAttrs (map (c: { name  = toString c;
                                 value = go c; })
                      clusters);

result = { inherit results;
           failed = any (n: results.${n}.failed) (attrNames results); };

checkedResult = assert isAttrs results;
                assert all (n: isInt (fromJSON n))    (attrNames results);
                assert all (n: results.${n} ? stdout) (attrNames results);
                assert all (n: results.${n} ? time)   (attrNames results);
                result;

in

if result.failed then result
                 else checkedResult
