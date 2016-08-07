defs: with defs; pkg:
with builtins;

let count = asts: parseJSON (runScript {} ''
              COUNT=$(jq -r 'length' < "${asts.stdout}")
              if [[ -n "$COUNT" ]]
              then
                echo "$COUNT" > "$out"
              else
                echo '"null"' > "$out"
              fi
            '');
    found = quick: let asts    = downloadAndDump {
                                   inherit quick;
                                   pkgName = pkg.name;
                                 };
                       result  = count asts;
                       resultN = fromJSON result;
                    in testDbg (if resultN == null
                                   then trace "Got null count" false
                                   else resultN > 0)
                               "Got downloaded & dumped ASTs"
                               { inherit quick result asts;
                                 inherit (pkg) name };
 in testRec {
      fast = found true;
      slow = found false;
    }
