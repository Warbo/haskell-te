{ bash, checkStderr, dumpToNix, explore, fail, getDepsScript, haskellPackages,
  jq, mkBin, nixedHsPkg, runCommand, runTypesScript, runTypesScriptData,
  utillinux, wrap }:

with builtins;

with rec {
  getArities = mkBin {
    name   = "getArities";
    paths  = [ bash jq ];
    vars   = {

      # Extract the name and module from the qname of each object
      EXTRACT =
        with rec {
          # Splits a qualified name into a module and a name ("bits")
          input = ''(.qname | split(".") | reverse) as $bits'';

          # The name is the last "bit"
          name = ''$bits[0]'';

          # The module is all except the last "bit", joined by dots
          mod = ''$bits[1:] | reverse | join(".")'';
        };
      "${input} | . + {name: ${name}, module: ${mod}}";

      # There may be duplicates: one which is hashed and one which isn't. We
      # prefer to be hashed if possible, so we update each objects' "hashable"
      # field to true if the array contains a hashable object with the same qname.
      SET_HASHABLE = ''
        . as $all | map(.qname as $qn | . + {
                          "hashable": ($all | map(select(.qname == $qn)) | any)
                        })
      '';

      # Any duplicates will be identical, including their "hashable" field, so we
      # can dedupe using "unique".
      UNIQUIFY = ". | unique | map(del(.qname))";
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      # Keep lines which look like JSON objects
      grep '^{' | jq -c -M "$EXTRACT"      |  # Set the right name
                  jq -s -M "$SET_HASHABLE" |  # Prefer hashable
                  jq       "$UNIQUIFY"        # Remove dupes
    '';
  };

  getTypes = mkBin {
    name   = "getTypes";
    paths  = [ bash jq utillinux ];
    script = ''
      #!/usr/bin/env bash
      set -e

      # Monomorphic types come in via stdin

      function trim {
        grep -o '[^ ].*[^ ]'
      }

      # Turn (foo)::bar::baz into foo\tbaz
      grep '::' |
        sed 's/(\(.*\)).*::*.*::\(.*\)/\1\t\2/g' |
        while read -r LINE
        do
          # Cut at the \t, trim whitespace and reverse the (qualified) name
          RNAME=$(echo "$LINE" | cut -f 1 | trim | rev)
          TYPE=$( echo "$LINE" | cut -f 2 | trim)

          # Chop the reversed name at the first dot, eg. 'eman.2doM.1doM' gives
          # 'eman' and '2doM.1doM', then reverse to get 'name' and 'Mod1.Mod2'
          NAME=$(echo "$RNAME" | cut -d '.' -f 1  | rev)
          MODS=$(echo "$RNAME" | cut -d '.' -f 2- | rev)

          echo "{\"module\": \"$MODS\", \"name\": \"$NAME\", \"type\": \"$TYPE\"}"
        done |
        jq -s '.'
    '';
  };

  tagAstsScript = default: wrap {
    name   = "tagAsts";
    paths  = [ bash jq ];
    vars   = {
      inherit default;
      FALLBACK_ID = ''
        {
             "name" : $this.name,
           "module" : $this.module,
          "package" : $this.package
        }
      '';

      # Select $tags matching $this
      QUERY = ''map(select((.module == $this.module) and
                           (.name   == $this.name))) | .[0]'';

      # Combine matching $tags with $this
      ACTION = ". + $this";
    };
    script = ''
      #!/usr/bin/env bash

      # Given JSON objects on stdin, and a file descriptor containing JSON objects
      # as $1, combines those elements of each with matching pkg/mod/name. If no
      # match is found in $1, 'default' is used as a fallback

      function msg {
        echo -e "$1" 1>&2
      }

      [[ -n "$1" ]] || {
        msg "tagAsts requires an argument for its tags"
        msg "For example, 'echo FOO | tagAsts <(echo BAR)'"
        exit 1
      }

      TYPE=$(echo "$default" | jq -r 'type') || {
        msg "Couldn't parse tagAsts default argument '$default' as JSON"
        exit 3
      }

      [[ "x$TYPE" = "xobject" ]] || {
        msg "tagAsts default argument '$default' has type '$TYPE'"
        msg "It should be an object"
        exit 4
      }

      export FALLBACK="($FALLBACK_ID + $default)"

      # Call the current AST $this, then loop over $tags
      INPUT=".[] | . as \$this | \$tags + [$FALLBACK]"

      jq --argfile tags "$1" "[$INPUT | $QUERY | $ACTION]"
    '';
  };

  annotateAsts = mkBin {
    name   = "annotateAsts";
    paths  = [ getArities getTypes jq ];
    vars   = {
      tagTypesScript   = tagAstsScript ''{"type":null}'';
      tagAritiesScript = tagAstsScript ''
        {
                  "arity" : null,
          "quickspecable" : false,
               "hashable" : false
        }
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      function msg {
        echo -e "$1" 1>&2
      }

      function tagTypes {
        "$tagTypesScript" <(echo "$RAWSCOPE" | getTypes)
      }

      function tagArities {
        "$tagAritiesScript" <(echo "$RAWTYPES" | getArities)
      }

         INPUT=$(cat                                 ); msg "Getting ASTs"
       RAWASTS=$(echo "$INPUT" | jq -c '.asts'       ); msg "Getting types"
      RAWTYPES=$(echo "$INPUT" | jq -r '.result'     ); msg "Getting scope"
      RAWSCOPE=$(echo "$INPUT" | jq -r '.scoperesult'); msg "Tagging"

      echo "$RAWASTS" | tagTypes | tagArities

      msg "Tagged"
    '';
  };

  annotateDbScript = wrap {
    name   = "annotateDb";
    paths  = [ annotateAsts bash getDepsScript ];
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      # Turns output from dump-package or dump-hackage into a form suitable for
      # clustering

      "$typesScript" | annotateAsts | getDepsScript
    '';
  };

  annotateScript = mkBin {
    name   = "annotate";
    paths  = [ bash checkStderr fail ];
    vars   = { annotateDb = annotateDbScript; };
    script = ''
      #!/usr/bin/env bash
      [[ -n "$typesScript" ]] || fail "No typesScript set"
      "$annotateDb" 2> >(checkStderr)

      # Give checkStderr some time to process (hacky and racy)
      CODE="$?"
      sleep 1
      exit "$CODE"
    '';
  };
};

rec {
  annotated = { pkgDir }:
    with rec {
      pkgSrc   = nixedHsPkg pkgDir;
      f        = dumpToNix { pkgDir = pkgSrc; };
      env      = explore.extractedEnv {
        inherit f;
        extraHs    = [];
        standalone = pkgSrc;
      };
    };
    runCommand "annotate"
      {
        inherit f;
        buildInputs = env ++ [ annotateScript ];
        typesScript = runTypesScript { inherit pkgSrc; };
      }
      ''
        set -e
        annotate < "$f" > "$out"
      '';

  annotateRawAstsFrom = mkBin {
    name   = "annotateRawAstsFrom";
    paths  = [ annotateScript bash ];
    vars   = { typesScript = runTypesScriptData.script; };
    script = ''
      #!/usr/bin/env bash
      pkgSrc=$(readlink -f "$1")
      export pkgSrc

      annotate
    '';
  };
}
