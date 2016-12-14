defs: with defs; with lib; with quickspecBench; with builtins;

let checkVar = var: ''
      [[ -n "${"$" + var}" ]] || {
        echo "No ${var}" 1>&2
        exit 1
      }
      [[ -e "${"$" + var}" ]] || {
        echo "${var} '${"$" + var}' doesn't exist" 1>&2
        exit 1
      }
    '';
    run = code: ''
      DIR="$PWD" source ${writeScript "to-run" code} < ${./example.smt2}
    '';
    go  = name: testRun name null { buildInputs = [ package ]; };
in mapAttrs go {

  failOnGarbage = ''
    if echo '!"£$%^&*()' | quickspecBench > >(tee stdout) 2> >(tee stderr >&2)
    then
      exit 1
    fi
    exit 0
  '';

  genSig = ''
    export   OUT_DIR="${./testPackage}"
    export ANNOTATED="${./annotated.json}"
    export       DIR="$PWD"

    ${run mkQuickSpecSig}

    for F in sig.hs env.nix
    do
      [[ -e "$F" ]] || {
        echo "Couldn't find '$F'" 1>&2
        exit 1
      }
    done
  '';

  runScript = ''
    quickspecBench < ${./example.smt2} > /dev/null || exit 1
  '';

  runRunSig = ''
    ${run runSig}
    ${checkVar "RESULT"}
  '';

  runMkQuickSpecSig = ''
    ${run mkQuickSpecSig}
    ${checkVar "SIG"}
  '';

  runGetAsts = ''
    ${run getAsts}
    ${checkVar "ANNOTATED"}
  '';

  runMkPkg = ''
    ${run mkPkg}
    ${checkVar "OUT_DIR"}
  '';

  runMkDir = ''
    ${mkDir}
    ${checkVar "DIR"}
  '';

  getJsonOutput = ''
    BENCH_OUT=$(quickspecBench < "${./example.smt2}") || exit 1

    TYPE=$(echo "$BENCH_OUT" | jq -r 'type') || {
      echo -e "START BENCH_OUT\n\n$BENCH_OUT\n\nEND BENCH_OUT" 1>&2
      exit 1
    }

    [[ "x$TYPE" = "xobject" ]] || {
      echo -e "START BENCH_OUT\n\n$BENCH_OUT\n\nEND BENCH_OUT" 1>&2
      echo "'$TYPE' is not object" 1>&2
      exit 1
    }
  '';

  filterSamples = let keepers = [
    { name = "append";          module = "A"; package = "tip-benchmark-sig"; }
    { name = "constructorNil";  module = "A"; package = "tip-benchmark-sig"; }
    { name = "constructorCons"; module = "A"; package = "tip-benchmark-sig"; }
  ];
  in ''
       set -e
       export BENCH_FILTER_KEEPERS='${toJSON keepers}'
       BENCH_OUT=$(quickspecBench < ${../benchmarks/list-full.smt2})
       for S in append constructorNil constructorCons
       do
         echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null || {
           echo "No equations for '$S'" 1>&2
           exit 1
         }
       done
       for S in map foldl foldr length reverse
       do
         if echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null
         then
           echo "Found equation with forbidden symbol '$S'" 1>&2
           exit 1
         fi
       done
     '';
}
