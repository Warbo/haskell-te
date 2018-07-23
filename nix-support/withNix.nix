{ bash, coreutils, fail, jq, lib, nix, nix-helpers, nixpkgs1803, perl, procps,
  runCommand, utillinux }:

with builtins;
with rec {
  # Allow given env to override us, but we must override buildInputs
  go = env: nix-helpers.withNix ({ inherit NIX_PATH; } // env) // {
    buildInputs = (env.buildInputs or []) ++ commonDeps;
  };

  # We include these for historical reasons
  commonDeps = [ bash coreutils jq nixPkg perl procps utillinux ];

  # Override NIX_PATH to take into account recursion using <real>

  NIX_PATH = concatStringsSep ":" [
    "nixpkgs=${./..}"
    "real=${toString pathReal}"
    (getEnv "NIX_PATH")
  ];

  # If we don't have <real> yet, use <nixpkgs>
  pathReal = with tryEval <real>;
             if success then value else <nixpkgs>;

  # Make sure we use a Nix package which corresponds to the system's

  nixV1 = compareVersions builtins.nixVersion "2" == -1;

  nixPkg = if nixV1 then nix else nixpkgs1803.nix;

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

assert nixV1 -> compareVersions nixPkg.version "2" == -1 || die {
  inherit (nixPkg) version;
  error = "Nix package doesn't have version 1.x";
};
assert nixV1 || compareVersions nix.version "2" == 1 || die {
  inherit (nixPkg) version;
  error = "Nix package should be higher than 2.0.0";
};
assert import checkPath;

go
