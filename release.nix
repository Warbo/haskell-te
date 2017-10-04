# Entry point for evaluating/building
with rec {
  go = stable:
    with import ./. {
      args            = { inherit stable; };
      bypassPublicApi = true;
    };
    # Remove unbuildable 'override' and 'overrideDerivation' attributes
    pkgs.stripOverrides {
      inherit benchmarkEnv packageUntested package tests testSuite;
    };
};
{
  stable   = go true;
  unstable = go false;
}
