{
  check = with import ./nix-support {};
          let drv = writeScript "dummy.nix" ''
                with import <nixpkgs>;
                stdenv.mkDerivation {
                  name = "dummy-input";
                  buildCommand = "source $stdenv/setup\necho foo > \"$out\"";
                }
              '';
              foo = stdenv.mkDerivation {
                name = "dummy";
                buildCommand = ''
                  source $stdenv/setup
                  mkdir -p "$out"
                  echo "success" > "$out"
                '';
              };
           in foo;
  #tests = import ./nix-support/tests.nix {};

  #tip-eqs = import ./nix-support/exploreTip.nix;
}
