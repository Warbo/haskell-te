{ buildPythonPackage, gnutar, pythonPackages, runScript, storeResult }:

buildPythonPackage {
  name = "csvkit";
  #version = "2014-11-28";

  src = runScript { buildInputs = [ gnutar ]; } ''
    set -e
    # We don't want the tar to contain the whole hierarchy, only "./csvkit"
    OLD_DIR="$PWD"
    ARCHIVE="$/csvkit.tar.gz"
    cd "${../packages}"

    tar czf "$OLD_DIR/csvkit.tar.gz" ./csvkit

    cd "$OLD_DIR"
    "${storeResult}" csvkit.tar.gz
  '';

  propagatedBuildInputs = [
    pythonPackages.python
    pythonPackages.dateutil
  ];
}
