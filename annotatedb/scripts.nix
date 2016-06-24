{ stdenv, jq, getDeps, utillinux }:

builtins.trace "FIXME: Get rid of annotatedb/scripts.nix" stdenv.mkDerivation {
  name = "annotatedb";
  propagatedBuildInputs = [ jq getDeps utillinux ];
}
