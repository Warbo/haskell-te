{
  check = with import ./nix-support {};
          let drv = writeScript "dummy.nix" ''
                with import <nixpkgs> {};
                buildEnv {
                  name  = "dummy-input";
                  paths = [ bash python ];
                }
              '';
              bool = writeScript "bool" "true";
              foo = stdenv.mkDerivation {
                name = "dummy";
                buildInputs = [ (import "${drv}") nix ];
                NIX_REMOTE  = builtins.trace (builtins.getEnv "NIX_REMOTE") runScript {} ''
                  if nix-instantiate --eval -E null 2> /dev/null
                  then
                    printf "$NIX_REMOTE" > "$out"
                  else
                    printf "daemon"      > "$out"
                  fi
                '';
                #"daemon"; #builtins.getEnv "NIX_REMOTE"; # e.g. "daemon"
                buildCommand = ''
                  source $stdenv/setup

                  echo "NIX_REMOTE: $NIX_REMOTE"
                  nix-instantiate --eval -E 'import "${bool}"'
                '';
              };
           in foo;

  tests = import ./nix-support/tests.nix {};

  #tip-eqs = import ./nix-support/exploreTip.nix;
}
