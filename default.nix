# Set 'bypassPublicApi' to get access to all of our implementation details, but
# keep in mind that we make no guarantees about their stability.
{ args ? {}, bypassPublicApi ? false }:

with rec {
  # Implementation details
  pkgs = import ./nix-support args;

  # Used for general performance testing, as well as formal evaluation
  benchmarkEnv = import ./benchmarks { inherit pkgs; };

  # Provides our exploration scripts
  inherit (pkgs) package;
};
if bypassPublicApi
   then { inherit benchmarkEnv package pkgs; }
   else package
