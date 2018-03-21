{ jq, lib, lzip, runCommand }:

with builtins;
with lib;
with rec {
  sampleFiles = [
    "b1247807-nix-py-dirnull.json.lz"  # Even numbered sizes
    "bdea634a-nix-py-dirnull.json.lz"  # Odd  numbered sizes
    "a531ce8f-nix-py-dirnull.json.lz"  # Rep 30
  ];

  samplesFrom = file: runCommand "samples.json"
    {
      buildInputs = [ jq lzip ];
      file        = ./results/desktop + "/${file}";
    }
    ''
      echo "Pulling samples out of '$file'" 1>&2
      mkdir "$out"
      cd "$out"
      lzip -d < "$file" | jq '.results | .["quickspectip.track_data"] |
                              .result  | .[0]                         |
                              map_values(.reps |
                                         map_values(.sample))' > data.json
      echo 'with builtins; fromJSON (readFile ./data.json)' > default.nix
    '';

  pieces = map (f: import (samplesFrom f)) sampleFiles;

  distinct = xs: ys: all (x: !(elem x ys)) xs && all (y: !(elem y xs)) ys;

  mergeSizes = xs: ys: ys // mapAttrs (size: reps:
                                        if hasAttr size ys
                                           then mergeReps reps (getAttr size ys)
                                           else reps)
                                      xs;

  mergeReps = xs: ys: assert distinct (attrNames xs) (attrNames ys) ||
                       abort { inherit xs ys; msg = "Reps overlap"; };
                      xs // ys;

  err = msg: abort (toJSON { inherit msg result; });

  result = fold mergeSizes {} pieces;
};

assert all (s: with { size = toString s; };
               hasAttr size result || err "No size ${size}")
           (range 1 20) || err "Missing sizes";
assert all (s: all (r: with { rep = toString r; };
                       hasAttr rep (getAttr s result) ||
                       err "Size ${s} missing rep ${rep}")
                   (range 0 30))
           (attrNames result) || err "Missing reps";
assert all (s: with { x = getAttr s result; };
               all (r: length (getAttr r x) == fromJSON s ||
                       err "Size ${s} rep ${r} wrong size")
                   (attrNames x))
           (attrNames result) || err "Wrong size sample";
{
  removeOverrides = true;
  value           = result;
}
