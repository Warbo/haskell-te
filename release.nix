# Entry point for evaluating/building
with rec {
  go = stable:
    with { pkgs = import ./nix-support { inherit stable; }; };
    pkgs.stripOverrides {
      inherit (pkgs) tests testSuite package;
      benchmarkEnv = import ./benchmarks {};
    };
};
{
  stable   = go true;
  unstable = go false;
}
