with import ./. {};
stdenv.mkDerivation {
  name         = "haskell-te-benchmark-env";
  src          = ./benchmarkEnv.nix;
  unpackPhase  = "true";
  buildInputs  = [
    asv-nix
    (mkBin {
      name   = "unzipBenchmarks";
      paths  = [ fail nixpkgs.lzip ];
      script = ''
        #!/usr/bin/env bash
        set   -e
        shopt -s nullglob

        echo "Looking for data" 1>&2
        [[ -d benchmarks/results ]] || fail "Couldn't find benchmarks/results"
        [[ -d .asv/results       ]] || fail "Couldn't find .asv/results"
        for D in benchmarks/results/*
        do
          [[ -d "$D" ]] || continue
          DIR=$(basename "$D")
          [[ -d .asv/results/"$DIR" ]] || fail "Couldn't find .asv/results/$DIR"
          for F in "$D"/*.json.lz
          do
            NAME=$(basename "$F" .lz)
            echo "Extracting $F to .asv/results/$DIR/$NAME" 1>&2
            lzip -d < "$F" > .asv/results/"$DIR"/"$NAME"
          done
        done
      '';
    })
  ];
  installPhase = ''
    set -e
    echo 'WARNING: Building the "benchmarkEnv" derivation. This is not meant
    to be a "real" package: it only provides a build environment, for use with
    nix-shell (e.g. "nix-shell benchmarkEnv.nix")'
    echo "This is not a 'package', it's meant to be used via nix-shell" > "$out"
  '';
  shellHook = ''
    echo "Entered benchmarking shell: use 'asv' command to run benchmarks." 1>&2
    echo "Use 'unzipBenchmarks' to extract previous results into place."    1>&2
  '';
}
