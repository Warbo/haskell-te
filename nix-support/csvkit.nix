{ fetchurl, buildPythonPackage, gnutar, pythonPackages, runScript, storeResult }:

let mkPy = name: url: md5: inputs: buildPythonPackage {
  inherit name;
  src = fetchurl { inherit url md5; };
  propagatedBuildInputs = [ pythonPackages.python ] ++ inputs;
};

dateutil = mkPy
  "dateutil"
  "https://pypi.python.org/packages/source/p/python-dateutil/python-dateutil-2.2.tar.gz"
  "c1f654d0ff7e33999380a8ba9783fd5c"
  [ pythonPackages.six ];

agate-excel = mkPy
  "agate-excel"
  "https://pypi.python.org/packages/source/a/agate-excel/agate-excel-0.1.0.tar.gz"
  "a054629ce7b1bcee3a1df26832330554"
  [ agate ];

agate = mkPy
  "agate"
  "https://pypi.python.org/packages/source/a/agate/agate-1.3.0.tar.gz"
  "7fa87088a6121e06a373706b7f43d0b7"
  [ pythonPackages.six parsedatetime ];

parsedatetime = mkPy
  "parsedatetime"
  "https://pypi.python.org/packages/source/p/parsedatetime/parsedatetime-2.1.tar.gz"
  "096fe294137914b3dbbe268ecb18b74b"
  [];

in mkPy
  "csvkit"
  "https://pypi.python.org/packages/source/c/csvkit/csvkit-0.4.1.tar.gz" # "https://pypi.python.org/packages/source/c/csvkit/csvkit-0.9.1.tar.gz"
  "35d1dbdfe66aac7eff9a7e9c317ef4b3"
  [ dateutil ]
  /*
in buildPythonPackage {
  name = "csvkit";

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
    dateutil
    agate-excel
  ];
}
*/
