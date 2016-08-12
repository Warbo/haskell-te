defs: with defs;
with builtins;

let deps = [
      mlspec
      mlspec-bench
      haskellPackages.ArbitraryHaskell
      haskellPackages.bench
      haskellPackages.ifcxt
      haskellPackages.mlspec
      haskellPackages.mlspec-bench
      haskellPackages.mlspec-helper
      haskellPackages.nix-eval
      haskellPackages.runtime-arbitrary
      haskellPackages.weigh
    ];
    pkg = buildEnv {
            name  = "testing-dependencies";
            paths = deps;
          };
    # Runs a shell script to check if the output directory of a derivation
    # exists. This will cause the derivation to be built, if it isn't already,
    # and hence will expose any errors in its build/install process.
    # We use this round-about method in preference to 'pathExists', since that
    # will complain about strings containing store paths depending on other
    # store paths ("cannot refer to other paths"), and is defers builds.
    usable = msg: x: testRun msg null {} ''
      set -e
      echo "Checking if package directory '${x}' exists" 1>&2
      [[ -d "${x}" ]] || exit 1
    '';
in {
  pkg  = usable "Usable package" pkg;
  deps = testAll (map (usable "Usable dependency") deps);
}
