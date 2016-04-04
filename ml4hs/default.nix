{ haskellPackages, jq, stdenv }:

stdenv.mkDerivation {
  name = "ml4hs";
  src  = ./.;

  # Used for testing script
  propagatedBuildInputs = [
    jq
    (haskellPackages.ghcWithPackages (p: [
      p.QuickCheck
    ]))
  ];
  installPhase = ''
    # Put scripts in place
    mkdir -p "$out/lib/ml4hs"
    for SCRIPT in *.sh
    do
      cp "$SCRIPT" "$out/lib/ml4hs/"
    done

    # Install a top-level entry point
    mkdir -p "$out/bin"
    printf "#!/bin/sh\ncd $out/lib/ml4hs\n./ml4hs.sh \"\$@\"\n" > "$out/bin/ml4hs"
    chmod +x "$out/bin/ml4hs"
  '';
}
