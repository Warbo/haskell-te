{ bash, ML4HSFE, wrap }:

{
  clusterScript = wrap {
    name   = "cluster";
    paths  = [ bash ML4HSFE ];
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
