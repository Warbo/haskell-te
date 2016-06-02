defs: with defs;
with builtins;
with lib;

let

ps = processPackages { quick = true; };

required = [ "base" ];

test = p: all id [

    (testMsg (ps ? ${p}) "'${p}' package defined")

    (testMsg (!ps.${p}.failed) "'${p}' package didn't fail")

    (all (f: testMsg (ps.${p} ? ${f}) "'${p}' has field ${f}") [
      "rawDump"
      "failed"
    ])

  ];

in #trace "FIXME: Skipping expensive ghcPackagesDumped test" true
 all test required
