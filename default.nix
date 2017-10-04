# Set 'bypassPublicApi' to get access to all of our implementation details, but
# keep in mind that we make no guarantees about their stability.
{ args ? {}, bypassPublicApi ? false }:

with rec {
  # Implementation details
  pkgs = import ./nix-support args;

  # Used for general performance testing, as well as formal evaluation
  benchmarkEnv = import ./benchmarks { inherit pkgs; };

  # Integration tests (unit tests should ideally be baked into derivations)
  tests = import ./tests { inherit pkgs; };

  # Only builds successfully if all tests pass
  testSuite = with pkgs; withDeps (allDrvsIn tests) nothing;

  # Provides our exploration scripts. Encourage users to run the test suite, but
  # also provide an escape hatch for those who want it (e.g. for debugging).
  packageUntested = pkgs.package;
  package         = pkgs.withDeps [ testSuite ] packageUntested;
};
if bypassPublicApi
   then { inherit benchmarkEnv packageUntested package pkgs tests testSuite; }
   else package
