defs: with defs; with lib; with quickspecBench;

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
    run = script: ''DIR="$PWD" source ${script} < ${./example.smt2} '';
    go  = name: testRun name null { buildInputs = [ package ]; };
in mapAttrs go {

  failOnGarbage = ''
    if echo '!"£$%^&*()' | quickspecBench 1> stdout 2> stderr
    then
      cat stderr stdout 1>&2
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

  runMkSmt = ''
    ${run mkSmt}
    ${checkVar "SMT_FILE"}
  '';

  runMkDir = ''
    source ${mkDir}
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
}
