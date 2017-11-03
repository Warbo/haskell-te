{ bash, checkStderr, dumpToNix, extractedEnv, fail, getDepsScript,
  haskellPackages, jq, lib, mkBin, nixedHsPkg, pkgName, runCommand,
  runTypesScript, runTypesScriptData, testData, unpack, utillinux, withDeps,
  wrap }:

with builtins;
with lib;

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
      # field to true if the array contains a hashable object with the same
      # qname.
      SET_HASHABLE = ''
        . as $all | map(.qname as $qn | . + {
          "hashable": ($all | map(select(.qname == $qn) | .hashable) | any)
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

      INPUT=$(cat)
      if [[ -z "$IN_SELF_TEST" ]]
      then
        if [[ "$DEBUG" -eq 1 ]]
        then
          NAME=$(echo "$INPUT" | sha256sum | head -n1 | cut -d ' ' -f1)
          msg "DEBUG detected, writing to '$NAME.annotateInput'"
          echo "$INPUT" > "$NAME.annotateInput"
        else
          msg "This stage is tricky. Set DEBUG=1 to see the debug info."
        fi
      fi

      msg "Getting ASTs";   RAWASTS=$(echo "$INPUT" | jq -c '.asts'       )
      msg "Getting types"; RAWTYPES=$(echo "$INPUT" | jq -r '.result'     )
      msg "Getting scope"; RAWSCOPE=$(echo "$INPUT" | jq -r '.scoperesult')

      msg "Tagging"
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

      "$typesScript" | annotateAsts | getDepsScript
    '';
  };

  annotateScript = withDeps (concatLists (attrValues
                              (mapAttrs testsFor {
                                inherit (testData.haskellDrvs) test-theory;
                              })) ++ checkDlist)
                            annotateScript-untested;

  annotateScript-untested = mkBin {
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

  testsFor = attr: pkg:
    with rec {
      asts = annotatedWith annotateScript-untested {
        pkgDir = unpack pkg.src;
        extras = { IN_SELF_TEST = "1"; };
      };
      annotatedExists = runCommand "annotatedExists"
        {
          inherit asts;
          buildInputs = [ fail ];
        }
        ''
          set -e
          [[ -e "$asts" ]] || fail "annotated '$asts' doesn't exist"
          mkdir "$out"
        '';

      haveAsts = runCommand "test-have-asts"
        {
          inherit asts;
          buildInputs = [ fail jq ];
        }
        ''
          set -e
          jq -e 'length | . > 0' < "$asts" || fail "Empty ASTs"
          mkdir "$out"
        '';

      astsLabelled = runCommand "test-asts-are-labelled"
        {
          inherit asts;
          buildInputs = [ fail jq ];
          pkgName     = pkgName pkg.name;
        }
        ''
          set -e
          jq -cr '.[] | .package' < "$asts" | while read -r LINE
          do
            [[ "x$LINE" = "x$pkgName" ]] || fail "Unlabelled: '$pkgName' '$LINE'"
          done
          mkdir "$out"
        '';

      astsHaveField = map (f: runCommand "${attr}-asts-have-${f}"
        {
          inherit asts;
          buildInputs = [ fail jq ];
        }
        ''
          set -e
          jq -e 'map(has("${f}")) | all' < "$asts" || fail "No '$f' field found"
          mkdir "$out"
        '')
        [ "package" "module" "name" "ast" "type" "arity" "quickspecable"
          "hashable" ];

      noCoreNames = runCommand "no-core-names"
        {
          inherit asts;
          buildInputs = [ fail jq ];
        }
        ''
          set -e
          if jq -cr '.[] | .name' < "$asts" | grep -cF ".$"
          then
            fail "Found core names in '$asts'"
          fi
          mkdir "$out"
        '';

      getTypes = runCommand "have-types-for-asts"
        {
          annotations = annotatedWith annotateScript-untested {
            extras = { IN_SELF_TEST = "1"; };
            pkgDir = toString (nixedHsPkg (toString runCommand "hsPkg"
              {
                buildInputs = tipBenchmarks.tools;
                example     = ../benchmarks/nat-simple.smt2;
              }
              ''
                set -e
                mkdir hsPkg
                export OUT_DIR="$PWD/hsPkg"
                full_haskell_package < "$example"
                cp -r hsPkg "$out"
              ''));
          };
          buildInputs = [ jq ];
        }
        ''
          set -e
          jq -e 'map(has("type") and .type != null) | any' < "$annotations"
          mkdir "$out"
        '';

      dependencyNameVersions = runCommand "dependency-name-versions"
        {
          inherit asts;
          pName       = pkg.name;
          buildInputs = [ fail jq ]; }
        ''
          set -e
          DEPS=$(jq -cr '.[] | .dependencies | .[] | .package' < "$asts" |
                 sort -u) ||
            fail "Couldn't get packages of '$pName' dependencies" 1>&2

          if echo "$DEPS" | grep -- "-[0-9][0-9.]*$" > /dev/null
          then
            fail "Deps of '$pkgName' have versions in package IDs:\n$DEPS" 1>&2
          fi
          mkdir "$out"
        '';

      haveDependencies = runCommand "haveDeps-${pkg.name}"
        {
          inherit asts;
          buildInputs = [ jq ];
        }
        ''
          set -e
          jq -e 'map(has("dependencies")) | all' < "$asts" > "$out"
        '';

      namesUnversioned = runCommand "names-unversioned-${attr}"
        {
          F           = asts;
          buildInputs = [ fail jq ];
          pkgName     = pkg.name;
        }
        ''
          set -e

          function assertNoVersions {
            if grep -- "-[0-9][0-9.]*$" > /dev/null
            then
              fail "Versions found in package names of $1$pkgName"
            fi
          }

          [[ -e "$F" ]] || fail "Couldn't find file '$F'"

          jq -rc '.[] | .package'                       < "$F" |
            assertNoVersions ""

          jq -rc '.[] | .dependencies | .[] | .package' < "$F" |
            assertNoVersions "dependencies of "

          mkdir "$out"
        '';
    };
    astsHaveField ++ [
      annotatedExists astsHaveField astsLabelled dependencyNameVersions getTypes
      haveAsts haveDependencies namesUnversioned noCoreNames
    ];

  # Regression tests for ef5280028f66a9e7
  checkDlist =
    with rec {
      pkg  = haskellPackages.dlist;
      asts = annotatedWith annotateScript-untested {
        pkgDir = unpack pkg.src;
        extras = { IN_SELF_TEST = "1"; };
      };
      notHashable = runCommand "dlist-not-hashable"
        {
          inherit asts;
          buildInputs = [ fail jq ];
        }
        ''
          set -e
          jq -e 'map(select(.name == "replicate")) | length |
                                                     . == 1 ' < "$asts" ||
            fail "No 'replicate' found"
          jq -e '.[] | select(.name == "replicate") | .hashable |
                                                      not       ' < "$asts" ||
            fail "'replicate' shouldn't be hashable (DLists are functions)"

          jq -e 'map(select(.name == "toList")) | length |
                                                  . == 1 ' < "$asts" ||
            fail "No 'toList' found"
          jq -e '.[] | select(.name == "toList") | .hashable' < "$asts" ||
            fail "'toList' should be hashable ([Integer] can be serialised)"

          mkdir "$out"
        '';
    };
    [ notHashable ];

  annotatedWith = annotateScript: { pkgDir, extras ? {} }:
    with rec {
      pkgSrc   = nixedHsPkg pkgDir;
      f        = dumpToNix { pkgDir = pkgSrc; };
      env      = extractedEnv {
        inherit f;
        standalone = pkgSrc;
      };
    };
    runCommand "annotate"
      ({
        inherit f;
        buildInputs = env ++ [ annotateScript ];
        typesScript = runTypesScript { inherit pkgSrc; };
      } // extras)
      ''
        set -e
        annotate < "$f" > "$out"
      '';
};

rec {
  annotated = annotatedWith annotateScript;

  annotateRawAstsFrom = mkBin {
    name   = "annotateRawAstsFrom";
    paths  = [ annotateScript bash ];
    vars   = { typesScript = runTypesScriptData.script; };
    script = ''
      #!/usr/bin/env bash
      set -e
      pkgSrc=$(readlink -f "$1")
      export pkgSrc

      annotate
    '';
  };
}
