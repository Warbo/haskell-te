{ benchmark, explore-theories, format, lib, ml4hs, parseJSON,
  runScript, withNix, writeScript }:
with builtins;
with lib;

{ quick, formatted }:

assert isAttrs formatted;
assert all (n: isString n)                    (attrNames formatted);
assert all (n: isInt (fromJSON n))            (attrNames formatted);
assert all (n: isList formatted."${n}")       (attrNames formatted);
assert all (n: all isString formatted."${n}") (attrNames formatted);

let explore = writeScript "format-and-explore" ''
      set -e
      function noDepth {
        grep -v "^Depth" || true # Don't abort if nothing found
      }
      explore-theories | noDepth
    '';
    doExplore = clusterCount: f:
      parseJSON (runScript { buildInputs = [ explore-theories ]; } ''
        set -e
        export CLUSTERS="${clusterCount}"
        "${benchmark quick "${explore}" []}" < "${f}" > "$out"
      '');
    go = clusterCount: clusters:
           map (doExplore clusterCount) clusters;
    result = mapAttrs go formatted;
in
assert isAttrs result;
assert all (n: isInt  (fromJSON n))  (attrNames result);
assert all (n: isList result."${n}") (attrNames result);
result
