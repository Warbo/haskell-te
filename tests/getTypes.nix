defs: with defs; with builtins;

with rec {
  hsPkg = runCommand "hsPkg" {} ''
    mkdir hsPkg
    export OUT_DIR="$PWD/hsPkg"
    "${tipBenchmarks.tools}/bin/full_haskell_package.rkt" < ${../benchmarks/nat-simple.smt2}
    cp -r hsPkg "$out"
  '';
  nixed       = nixedHsPkg "${hsPkg}";
  annotations = annotated  "${nixed}";
};

testRun "Have types for ASTs" { inherit annotations nixed; }
  {
    inherit annotations;
    buildInputs = [ jq ];
  }
  ''
    jq -e 'map(has("type") and .type != null) | any' < "$annotations"
  ''
