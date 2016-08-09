defs: with defs; pkg:
with builtins;
with lib;

let result = asts: field:
      testRun "Have field ${field}"
              { inherit asts field; }
              { inherit asts field; }
              ''
                R=$(jq -n --argfile asts    "$asts"   \
                          --arg     field   "$field"  \
                          '{($field) : ($asts                             |
                                        map(has($field) and
                                            (.[$field] | length | . > 0)) |
                                        all)}')
                echo "Result: $R" 1>&2
                [[ "x$R" = "xtrue" ]] || exit 1
                touch "$out"
              '';

    check = asts: listToAttrs (map (n: { name = n; value = result asts n; })
                                   ["package" "module" "name" "ast"]);

    slow    = processPackages { quick = false; };
    slowPkg = slow."${pkg.name}";
 in testRec {
   pkgDump        = check     pkg.dump;
   pkgRawDump     = check     pkg.rawDump.stdout;
   slowPkgDump    = check slowPkg.dump;
   slowPkgRawDump = check slowPkg.rawDump.stdout;
 }
