# All of the magic happens in ./nix-support, including a bunch of implementation
# details. Here we extract a set of "exports" to act as our external API.
with builtins;
with {
  allDefs = import ./nix-support {};
};
{
  # We still allow access to our internals, but warn those who rely on it
  allDefs = trace ''
    WARNING: Delving into implementation details of haskell-te. If possible,
    consider sticking to the stable API; if your use-case isn't supported, the
    API can be extended.
  '' allDefs;

  # Our stable API
  inherit (allDefs)
    buckets package testSuite tipBenchmarks;

  inherit (allDefs.sampling)
    drawSamples;
}
