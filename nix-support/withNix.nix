{ bash, coreutils, jq, lib, nix, nixEnv, perl, procps, runCommand, utillinux }:
with builtins;
with nixEnv;
with rec {
  commonDeps = [ bash coreutils jq nix perl procps utillinux ];
};

# Allow env to override nixEnv, but we must override buildInputs
env: nixEnv // env // { buildInputs = (env.buildInputs or []) ++ commonDeps; }
