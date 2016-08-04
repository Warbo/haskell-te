defs: with defs; with builtins;

let

# Check the package itself
pkg = tipBenchmarks.pkg;

haveSrc = testRun "Tip module source exists" null { buildInputs = [ pkg ]; }
            ''
              [[ -e "${pkg.src}" ]] || exit 1
            '';

# Make sure we can dump the ASTs
quick = true;

dump = dumpPackage { inherit quick; inherit (pkg) src; };

haveDump = {
  dumpSuccess = testMsg (!dump.failed)           "Tip module dump succeeded";
  haveStdout  = testMsg (pathExists dump.stdout) "Dumped Tip module";
};

# Annotation is trickier, so these are mainly regressions tests to ensure that
# our scripts can handle packages taken straight from Cabal directories
asts      = dump.stdout;
pkgName   = pkg.name;
env       = { buildInputs = [ jq GetDeps utillinux ]; };

ranTypes = parseJSON (runScript env ''
             set -e
             "${runTypesScript {
                  inherit pkg;
                  pkgSrc = pkg.src;
              }}" < "${asts}" > stdout 2> stderr
             CODE="$?"

             STDOUT=$(nix-store --add stdout)
             STDERR=$(nix-store --add stderr)

             printf '{"stdout": "%s", "stderr": "%s", "code": %s}' \
                     "$STDOUT"       "$STDERR"       "$CODE" > "$out"
           '');

checkStderr = parseJSON (runScript {} ''
                if grep -v '<interactive>.*parse error on input' < "${ranTypes.stderr}" |
                   grep "error" 1>&2
                then
                  echo "false" > "$out"
                else
                  echo "true" > "$out"
                fi
              '');

canRunTypes = let err = readFile ranTypes.stderr;
                  val = if checkStderr
                           then true
                           else trace (toJSON ranTypes) false;
               in testAll [
                    (testMsg (ranTypes.code == "0")
                             "Ran runTypesScript on tip module")
                    (testMsg val "No runTypeScript errors for tip module")
                  ];

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
annotated = annotate { inherit quick asts pkg;
                       pkgSrc = pkg.src; };

rawAnnotated = testMsg (!annotated.failed) "Tip module annotation succeeded";

# Just to make sure, also check the encapsulated version we actually use
processed = tipBenchmarks.process { inherit quick; };

tipAnnotated = testMsg (!processed.rawAnnotated.failed)
                       "Tip benchmarks annotated";

in {
  inherit haveSrc haveDump; # canRunTypes canAnnotateAsts canGetDeps rawAnnotated
          #tipAnnotated;
}
