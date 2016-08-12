defs: with defs; pkg:
with builtins;

let count = asts: drvFromScript { inherit asts; } ''

            '';
    found = quick: let asts = downloadAndDump {
                                inherit quick;
                                pkgName = pkg.name;
                              };
                    in testRun "Got downloaded & dumped ASTs"
                               { inherit quick asts;
                                 inherit (pkg) name; }
                               { inherit (asts) stdout; }
                               ''
                                 COUNT=$(jq -r 'length' < "$stdout")
                                 if [[ -n "$COUNT" ]]
                                 then
                                   if [[ "$COUNT" -gt 0 ]]
                                   then
                                     exit 0
                                   else
                                     echo "Count: $COUNT" 1>&2
                                     exit 1
                                   fi
                                 else
                                   echo "Empty count" 1>&2
                                   exit 1
                                 fi
                               '';
 in {
      fast = found true;
      slow = found false;
    }
