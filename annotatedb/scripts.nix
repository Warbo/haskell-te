{ stdenv, jq, GetDeps, utillinux }:

builtins.trace "FIXME: Get rid of annotatedb/scripts.nix" stdenv.mkDerivation {
  name = "annotatedb";
  propagatedBuildInputs = [ jq GetDeps utillinux ];
}
