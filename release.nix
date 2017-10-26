# A useful entry point for continuous integration (e.g. Hydra)
with rec {
  go = stable:
    with import ./. {
      args            = { inherit stable; };
      bypassPublicApi = true;
    };
    # Remove unbuildable 'override' and 'overrideDerivation' attributes
    pkgs.stripOverrides {
      inherit benchmarkEnv package;
    };
};
{
  stable   = go true;
  unstable = go false;
}
