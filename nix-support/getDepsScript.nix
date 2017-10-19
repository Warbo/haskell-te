{ bash, haskellPackages, jq, mkBin, runCommand, utillinux, writeScript }:

runCommand "GetDepsScript"
  {
    buildInputs = [ (haskellPackages.ghcWithPackages (h: [
      h.GetDeps h.lens-aeson h.validation
    ])) ];
    script = ./getDepsScript.hs;
  }
  ''
    set -e
    mkdir -p "$out/bin"

    # Copy here rather than trying to build directly in /nix/store
    cp "$script" getDepsScript.hs

    ghc --make -o "$out/bin/getDepsScript" getDepsScript.hs
  ''
