defs: with defs; with builtins;

let

# Check the package itself
pkg = tipBenchmarks.pkg;

haveSrc = testRun "Tip module source exists" null { buildInputs = [ pkg ]; }
            ''
              [[ -e "${pkg.src}" ]] || exit 1
            '';

# Make sure we can dump the ASTs
dump = dumpPackage { inherit (pkg) src; };

haveDump = {
  dumpSuccess = testRun "Tip module dump succeeded" null
                        { inherit (dump) failed; } ''
                          O=$(cat "$failed")
                          [[ "x$O" = "xfalse" ]] || exit 1
                        '';
  haveStdout  = testRun "Dumped Tip module" null
                        { inherit (dump) stdout; } ''
                          [[ -e "$stdout" ]] || exit 1
                        '';
};

# Annotation is trickier, so these are mainly regressions tests to ensure that
# our scripts can handle packages taken straight from Cabal directories
asts      = dump.stdout;
pkgName   = pkg.name;
env       = { buildInputs = explore.extractedEnv {
                              f          = asts;
                              extraHs    = [ "GetDeps" ];
                              standalone = pkg.src;
                            }; };

ranTypes = drvFromScript (env // { outputs = [ "stdout" "stderr" "code" ];
                                   inherit asts; }) ''
             set -e
             "${runTypesScript {
                  pkgSrc = pkg.src;
              }}" < "$asts" > stdout 2> >(tee stderr >&2)
             CODE="$?"

             echo "$CODE" > "$code"

             cp stdout "$stdout"
             cp stderr "$stderr"
           '';

checkStderr = drvFromScript { inherit (ranTypes) stderr; } ''
                if grep -v '<interactive>.*parse error on input' < "$stderr" |
                   grep "error" 1>&2
                then
                  exit 1
                else
                  echo "true" > "$out"
                  exit 0
                fi
              '';

canRunTypes = let err = readFile ranTypes.stderr;
                  val = checkStderr;
               in testAll [
                    (testDrvString "0" ranTypes.code
                                   "Ran runTypesScript on tip module")
                    val
                  ];

# Try the 'annotate' function, which combines the above pieces
annotated = annotate { inherit asts pkg;
                       pkgSrc = pkg.src; };

rawAnnotated = testRun "Tip module annotation succeeded" null
                       { inherit (annotated) failed; } ''
                         O=$(cat "$failed")
                         [[ "x$O" = "xfalse" ]] || exit 1
                       '';

# Just to make sure, also check the encapsulated version we actually use
processed = tipBenchmarks.process {};

tipAnnotated = testRun "Tip benchmarks annotated" null
                       { inherit (processed.rawAnnotated) failed; } ''
                         O=$(cat "$failed")
                         [[ "x$O" = "xfalse" ]] || exit 1
                       '';

in {
  inherit haveSrc haveDump canRunTypes rawAnnotated tipAnnotated;
}
