defs: with defs; with builtins;

let

# Check the package itself
pkg = tipBenchmarks.pkg;

haveSrc = testMsg (pathExists pkg.src) "Tip module source exists";

# Make sure we can dump the ASTs
quick = true;

dump = dumpPackage { inherit quick; inherit (pkg) src; };

haveDump = testMsg (!dump.failed)           "Tip module dump succeeded" &&
           testMsg (pathExists dump.stdout) "Dumped Tip module";

# Annotation is trickier, so these are mainly regressions tests to ensure that
# our scripts can handle packages taken straight from Cabal directories
asts      = dump.stdout;
pkgName   = pkg.name;
env       = { buildInputs = [ adb-scripts ]; };

ranTypes = parseJSON (runScript env ''
             set -e
             "${runTypesScript { pkgDefFile = tipBenchmarks.pkg.src; }}" \
               "${pkgName}" < "${asts}" > stdout 2> stderr
             CODE="$?"

             STDOUT=$(nix-store --add stdout)
             STDERR=$(nix-store --add stderr)

             printf '{"stdout": "%s", "stderr": "%s", "code": %s}' \
                     "$STDOUT"       "$STDERR"       "$CODE" > "$out"
           '');

canRunTypes = let err = readFile ranTypes.stderr;
                  val = if match ".*error.*" err == null
                           then true
                           else trace (toJSON ranTypes) false;
               in testMsg (ranTypes.code == "0")
                          "Ran runTypesScript on tip module" &&
                  testMsg val "No runTypeScript errors for tip module";

annotatedAsts = runScript env ''
                  set -e
                  "${annotateAstsScript}" < "${ranTypes.stdout}" > out
                  "${storeResult}" out
                '';

canAnnotateAsts = testMsg ("${annotatedAsts}" != "")
                          "Can run annotateAstsScript on tip module";

gotDeps = runScript env ''
            "${getDepsScript}" < "${annotatedAsts}" > out
            "${storeResult}" out
          '';

canGetDeps = testMsg ("${gotDeps}" != "")
                     "Can run getDepsScript on tip module";

# Try the 'annotate' function, which combines the above pieces
annotated = annotate { inherit quick asts pkgName; };

rawAnnotated = testMsg (!annotated.failed) "Tip module annotation succeeded";

# Just to make sure, also check the encapsulated version we actually use
processed = tipBenchmarks.process { inherit quick; };

tipAnnotated = testMsg (!processed.rawAnnotated.failed)
                       "Tip benchmarks annotated";

# Run tests in dependency order
in all (x: x) [
     haveSrc
     haveDump
     canRunTypes
     canAnnotateAsts
     canGetDeps
     rawAnnotated
     tipAnnotated
   ]
