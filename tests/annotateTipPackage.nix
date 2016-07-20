defs: with defs; with builtins;

let

# Check the package itself
pkg = tipBenchmarks.pkg;

haveSrc = testMsg (pathExists pkg.src) "Tip module source exists";

# Make sure we can dump the ASTs
quick = true;

dump = dumpPackage { inherit quick; inherit (pkg) src; };

haveDump = testAll [
             (testRun "Tip module dump succeeded"
                      (toJSON dump)
                      { buildInputs = [ dump jq ]; }
                      ''
                        set -e
                        D=$(benchmarkResult)
                        FAILED=$(jq -r '.failed' "$D/result.json")
                        [[ "x$FAILED" = "xfalse" ]] || exit 1
                      '')
             (testRun "Dumped Tip module"
                      (toJSON dump)
                      { buildInputs = [ dump jq ]; }
                      ''
                        set -e
                        D=$(benchmarkResult)
                        STDOUT=$(jq -r '.stdout' < "$D/result.json"
                        [[ -f "$STDOUT" ]] || exit 1
                      '')
           ];

# Annotation is trickier, so these are mainly regressions tests to ensure that
# our scripts can handle packages taken straight from Cabal directories
pkgName   = pkg.name;
env       = { buildInputs = [ jq getDeps utillinux ]; };

ranTypes = stdenv.mkDerivation {
             name         = "ranTypes";
             buildInputs  = [ jq getDeps utillinux dump ];
             buildCommand = ''
               source $stdenv/setup
               set -e

               D=$(benchmarkResult)
               ASTS="$D/stdout"
               "${runTypesScript {
                    inherit pkg;
                    pkgSrc = pkg.src;
                }}" < "$ASTS" > stdout 2> stderr
               CODE="$?"

               mkdir -p "$out"
               cp stdout "$out/"
               cp stderr "$out/"

               printf '{"stdout": "%s", "stderr": "%s", "code": %s}' \
                       "$STDOUT"       "$STDERR"       "$CODE" > "$out/result.json"
             '';
           };

checkStderr = stdenv.mkDerivation {
                name = "checkStderr";
                buildInputs = [ ranTypes ];
                buildCommand = ''
                  if grep -v '<interactive>.*parse error on input' < "${ranTypes}/stderr" |
                     grep "error" 1>&2
                  then
                    echo "false" > "$out"
                  else
                    echo "true" > "$out"
                  fi
                '';
              };

canRunTypes = let err = readFile ranTypes.stderr;
                  val = if checkStderr
                           then true
                           else trace (toJSON ranTypes) false;
               in testAll [
                    (testRun "Ran runTypesScript on tip module"
                             (toJSON ranTypes)
                             { buildInputs = [ ranTypes jq ]; }
                             ''
                               set -e
                               CODE=$(jq -r '.code' < "${ranTypes}/result.json")
                               [[ "$CODE" -eq 0 ]] || exit 1
                             '')

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
annotated = annotate { inherit quick pkg;
                       pkgSrc = pkg.src;
                       asts   = dump; };

rawAnnotated = testRun "Tip module annotation succeeded"
                       null
                       { buildInputs = [ annotated jq ]; }
                       ''
                         #!/usr/bin/env bash
                         jq < (!annotated.failed)
                       '';

# Just to make sure, also check the encapsulated version we actually use
processed = tipBenchmarks.process { inherit quick; };

tipAnnotated = testMsg (!processed.rawAnnotated.failed)
                       "Tip benchmarks annotated";

# Run tests in dependency order
in testAll [
     haveSrc
     haveDump
     canRunTypes
     canAnnotateAsts
     canGetDeps
     rawAnnotated
     tipAnnotated
   ]
