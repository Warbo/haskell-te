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

ranTypes = drvFromScript (env // { outputs = [ "stdout" "stdout" "code" ];
                                   inherit asts; }) ''
             set -e
             "${runTypesScript {
                  inherit pkg;
                  pkgSrc = pkg.src;
              }}" < "$asts" > stdout 2> stderr
             CODE="$?"

             echo "$CODE" > "$code"

             cp stdout "$stdout"
             cp stderr "$stderr"
           '';

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

annotatedAsts = drvFromScript (env // { inherit (ranTypes) stdout) ''
                  set -e
                  "${annotateAstsScript}" < "$stdout" > out
                  "${storeResult}" out
                '';

canAnnotateAsts = testRun "Can run annotateAstsScript on tip module" null
                          { inherit annotatedAsts; } ''
                            O=$(cat "$annotatedAst")
                            [[ -n "$O" ]] || exit 1
                          '';

gotDeps = drvFromScript (env // { inherit annotatedAsts; }) ''
            "${getDepsScript}" < "$annotatedAsts" > out
            "${storeResult}" out
          '';

canGetDeps = testRun "Can run getDepsScript on tip module" null
                     { inherit gotDeps; } ''
                       O=$(cat "$gotDeps")
                       [[ -n "$O" ]] || exit 1
                     '';

# Try the 'annotate' function, which combines the above pieces
annotated = annotate { inherit quick asts pkg;
                       pkgSrc = pkg.src; };

rawAnnotated = testRun "Tip module annotation succeeded" null
                       { inherit (annotated) failed; } ''
                         O=$(cat "$failed")
                         [[ "x$O" = "xfalse" ]] || exit 1
                       '';

# Just to make sure, also check the encapsulated version we actually use
processed = tipBenchmarks.process { inherit quick; };

tipAnnotated = testRun "Tip benchmarks annotated" null
                       { inherit (processed.rawAnnotated) failed; } ''
                         O=$(cat "$failed")
                         [[ "x$O" = "xfalse" ]] || exit 1
                       '';

in {
  inherit haveSrc haveDump canRunTypes canAnnotateAsts canGetDeps rawAnnotated
          tipAnnotated;
}
