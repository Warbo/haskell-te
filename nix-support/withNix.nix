{ bash, callPackage, coreutils, fail, helpersSrc, jq, lib, nix, perl, procps,
  runCommand, utillinux }:

with builtins;
with rec {
  # Force nix-helpers version to use the same Nix package as us
  withNix' =
    with callPackage "${helpersSrc}/helpers/withNix.nix" {};
    def;

  # Allow given env to override us, but we must override buildInputs
  go = env: withNix' ({ inherit NIX_PATH; } // env) // {
    buildInputs = (env.buildInputs or []) ++ commonDeps;
  };

  # We include these for historical reasons
  commonDeps = [
    bash coreutils jq (nix.out or nix) perl procps utillinux
  ];

  # Override NIX_PATH to take into account recursion using <real>

  NIX_PATH = concatStringsSep ":" [
    "nixpkgs=${./..}"
    "real=${toString pathReal}"
    (getEnv "NIX_PATH")
  ];

  # If we don't have <real> yet, use <nixpkgs>
  pathReal = with tryEval <real>;
             if success then value else <nixpkgs>;

  # Tests

  checkPath = runCommand "try-nix-path.nix"
    (go { buildInputs = [ fail jq ]; })
    ''
      function go {
        echo "Checking: $*" 1>&2
        nix-instantiate --show-trace --eval --read-write-mode -E \
          "with builtins // { x = import <nixpkgs> { config = {}; overlays = []; }; }; $1" ||
          fail "Failed:\nNIX_PATH: $NIX_PATH\nNIX_REMOTE: $NIX_REMOTE"
        echo "Finished: $*" 1>&2
      }

      echo "Checking <nixpkgs> gets overridden" 1>&2
      RESULT=$(go '<nixpkgs>')
      F="$RESULT/nix-support/withNix.nix"
      [[ -e "$F" ]] || fail "No such file '$F' (<nixpkgs> = '$RESULT')"

      echo "Checking <nixpkgs> isn't polluted by ~/.nixpkgs/config.nix" 1>&2
      go 'assert !(x                 ? warbo-utilities); true'
      go 'assert !(x.haskellPackages ? haskell-example); true'

      echo "Checking <nixpkgs> has our custom definitions" 1>&2
      go 'assert x ? wrap; true'
      for P in mlspec mlspec-helper nix-eval runtime-arbitrary
      do
        go "assert x.haskellPackages ? $P; true"
      done

      echo "true" > "$out"
    '';
};

assert import checkPath;
go
