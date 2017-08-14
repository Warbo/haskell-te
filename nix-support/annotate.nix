{ bash, checkStderr, explore, getDepsScript, haskellPackages, jq, runCommand,
  runTypesScript, wrap }:

with builtins;

{ asts, pkg, pkgSrc ? null }:

with rec {

getAritiesScript = wrap {
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

getTypesScript = wrap {
  name   = "getTypes";
  paths  = [ bash jq ];
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

annotateAstsScript = wrap {
  name   = "annotateAsts";
  paths  = [ jq ];
  vars   = {
    inherit getTypesScript getAritiesScript;
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
      "$tagTypesScript" <(echo "$RAWSCOPE" | "$getTypesScript")
    }

    function tagArities {
      "$tagAritiesScript" <(echo "$RAWTYPES" | "$getAritiesScript")
    }

       INPUT=$(cat                                 ); msg "Getting ASTs"
     RAWASTS=$(echo "$INPUT" | jq -c '.asts'       ); msg "Getting types"
    RAWTYPES=$(echo "$INPUT" | jq -r '.result'     ); msg "Getting scope"
    RAWSCOPE=$(echo "$INPUT" | jq -r '.scoperesult'); msg "Tagging"

    echo "$RAWASTS" | tagTypes | tagArities

    msg "Tagged"
  '';
};

annotateDb = wrap {
  name   = "annotateDb";
  paths  = [ bash ];
  vars   = {
    inherit annotateAstsScript getDepsScript;
    typesScript = runTypesScript {
      pkgSrc = if pkg ? srcNixed
                  then pkg.srcNixed
                  else pkgSrc;
    };
  };
  script = ''
    #!/usr/bin/env bash

    # Turns output from dump-package or dump-hackage into a form suitable for
    # clustering

    "$typesScript" | "$annotateAstsScript" | "$getDepsScript"
  '';
};

env = if haskellPackages ? pkg.name
         then { extraHs    = [ pkg.name ];
                standalone = null; }
         else { extraHs    = [];
                standalone = if pkg ? srcNixed
                                then pkg.srcNixed
                                else pkgSrc; };

};

drvFromScript
   {
     buildInputs = explore.extractedEnv (env // { f = asts; });
     outputs     = stdParts;
     inherit asts;
   }
   ''
     set -e
     O=$("${runCmd {
              cmd = annotateDb;
          }}" < "$asts")

     ${storeParts}
   ''
