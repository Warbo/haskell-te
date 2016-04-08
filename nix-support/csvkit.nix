{ buildPythonPackage, gnutar, pythonPackages, runScript, storeResult, pip2nix }:

let expr = runScript { buildInputs = [ pip2nix.pip2nix.python27 ]; } ''
  set -e

  cp -r "${../packages/csvkit}" ./csvkit
  chmod -R +w ./csvkit
  cd ./csvkit

  pip2nix scaffold --package csvkit
  cat > pip2nix.ini <<EOF
  [pip2nix]
  requirements = ./requirements-py2.txt
  EOF
  pip2nix generate

  cd ..
  "${storeResult}" ./csvkit
'';

in import expr
