# Builds the environment in which to run a benchmark
args:

with import ../nix-support {};
with rec {
  inherit (nix-config) attrsToDirs wrap;
};
attrsToDirs {
  bin = {
    python = wrap {
      file = "${python}/bin/python";
    };
  };
}
