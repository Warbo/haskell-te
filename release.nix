# Pick out those values which are "externally-facing", e.g. to build with CI
{
  inherit (import ./.)
    benchmarkEnv benchmarkRunner package;
}
