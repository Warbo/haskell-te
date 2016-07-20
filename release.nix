{
  check = with import ./nix-support {};
          let foo = stdenv.mkDerivation {
                name = "dummy";
                buildCommand = ''
                  source $stdenv/setup
                  echo "success" > "$out"
                '';
              };
           in foo;
  #tests = import ./nix-support/tests.nix {};

  #tip-eqs = import ./nix-support/exploreTip.nix;
}
