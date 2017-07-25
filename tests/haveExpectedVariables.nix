defs: with defs;

with rec {
  env = runCommand "have-expected-vars"
    (withNix {
      inherit (quickspecBench.benchVars.standalone)
        genAnnotatedPkg genInput;
      data = ../benchmarks/list-full.smt2;
    })
    ''
      # Make a dir to hold our generated Haskell package; it must be accessible to
      # other Nix builders, since we'll be invoking Nix recursively.
      export OUT_DIR="$PWD/pkg"
      mkdir "$OUT_DIR"
      chmod 777 -R "$PWD"

      # Convert TIP format to Haskell, extract ASTs and annotate with type info
      ASTS=$("$genAnnotatedPkg" < "$data")

      # Generate a QuickSpec signature for the generated Haskell package, along
      # with the code to explore it.
      "$genInput" < "$ASTS" > "$out"
    '';

  code = runCommand "code.hs" { inherit env; buildInputs = [ jq ]; } ''
    jq -r '.code' < "$env" > "$out"
  '';
};
{
  askForVariables = runCommand "ask-for-vars"
    {
      inherit code;
    }
    ''
      echo "Ensuring Haskell code requests variables for appropriate types" 1>&2

      # Find where we're adding variables to the signature and get their types
      # This parsing is pretty fragile; if it breaks, it might be worth using
      # haskell-src-exts or similar.
      TYPES=$(grep -A 2 'MLSpec.Helper.addVars' < "$code" |
              grep 'getArbGen'                            |
              grep -o ':: .*\]'                           |
              grep -o ' .*[^]]'                           |
              grep -o '[^ ].*[^ ]'                        )

      for TYPE in Prelude.Integer '(A.List) Prelude.Integer'
      do
        echo "$TYPES" | grep -F "$TYPE" > /dev/null || {
          echo "Didn't ask for variables of type '$TYPE'" 1>&2
          exit 1
        }
      done

      echo "pass" > "$out"
    '';
}
