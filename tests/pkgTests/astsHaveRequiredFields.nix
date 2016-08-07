defs: with defs; pkg:
with builtins;
with lib;

let result = asts:
      let str = runScript {
                  buildInputs = [ tests.pkgTests.haveRawAsts."${pkg.name}" ];
                } ''
            RESULTS="{}"
            for FIELD in package module name ast
            do
              # RESULTS accumulates whether all ASTs have each field, and that
              # they're non-empty
              RESULTS=$("${jq}/bin/jq" -n --argfile asts    "${asts}"          \
                                          --argfile results <(echo "$RESULTS") \
                                          --arg     field   "$FIELD"           \
                '$results + {($field) : ($asts                             |
                                         map(has($field) and
                                             (.[$field] | length | . > 0)) |
                                         all)}')
            done
            echo "$RESULTS" > "$out"
          '';
          json = parseJSON str;
       in assert isString asts;
          assert isString str;
          assert isAttrs  json;
          json;
    check = asts: testAll (mapAttrsToList (f: b: testMsg b "Checking for ${f}")
                                          (result asts));
    slow    = processPackages { quick = false; };
    slowPkg = slow."${pkg.name}";
 in testAll (map check [ pkg.dump pkg.rawDump.stdout slowPkg.dump slowPkg.rawDump.stdout ])
