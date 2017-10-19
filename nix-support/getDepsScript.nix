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
    ghc --make -o "$out/bin/getDepsScript" "$script"
  ''
