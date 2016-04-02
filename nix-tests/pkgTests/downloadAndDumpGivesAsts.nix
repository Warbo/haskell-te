defs: with defs; pkgName:

let asts    = quick: downloadAndDump { inherit pkgName quick; };
    count   = quick: parseJSON (runScript { buildInputs = [ jq ]; } ''
                jq -r 'length' < "${(asts quick).stdout}" > "$out"
              '');
    found   = quick: let result = count quick;
                      in assertMsg (fromJSON result > 0)
                                   "Got '${result}' downloaded & dumped ASTs";
 in found true && found false
