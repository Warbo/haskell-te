defs: with defs; pkg:
with builtins;

let asts    = quick: downloadAndDump { inherit quick; pkgName = pkg.name; };
    count   = quick: parseJSON (runScript { buildInputs = [ jq ]; } ''
                COUNT=$(jq -r 'length' < "${(asts quick).stdout}")
                if [[ -n "$COUNT" ]]
                then
                  echo "$COUNT" > "$out"
                else
                  echo '"null"' > "$out"
                fi
              '');
    found   = quick: let result  = count quick;
                         resultN = fromJSON result;
                      in testMsg (if resultN == null
                                     then trace "Got null count" false
                                     else resultN > 0)
                                 "Got '${result}' downloaded & dumped ASTs";
 in testAll [(found true) (found false)]
