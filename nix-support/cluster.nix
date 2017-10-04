{ bash, ML4HSFE, runWeka, wrap }:

{
  clusterScript = wrap {
    name   = "cluster";
    paths  = [ bash ML4HSFE runWeka ];
    script = ''
      #!/usr/bin/env bash
      set -e

      [[ -n "$WIDTH"  ]] ||  WIDTH=30
      [[ -n "$HEIGHT" ]] || HEIGHT=30
      export WIDTH
      export HEIGHT
      ml4hsfe-outer-loop
    '';
  };
}
