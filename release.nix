# Entry point for evaluating/building
with rec {
  go = stable:
    with {
      pkgs = import ./nix-support { inherit stable; };
    };
    pkgs.stripOverrides {
      inherit (pkgs) tests testSuite package;
      benchmarkEnv = import ./benchmarks {};
    };

  # Only include "unstable" if we have extra Nix paths
  unstable = with builtins.tryEval <mlspec>;
             if success then { unstable = go false; } else {};
};
{ stable = go true; } // unstable
