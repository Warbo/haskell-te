{ bash, benchmark, drvFromScript, explore, getDepsScript, haskellPackages,
  runTypesScript, stdParts, storeParts, writeScript }:

with builtins;

{ asts, pkg, pkgSrc ? null, quick }:

with {

getAritiesScript = withDeps "getArities" [ jq ] ''
  #!${bash}/bin/bash

  # Split a qualified name into a module and a name
  # shellcheck disable=SC2016
  INPUT='(.qname | split(".") | reverse) as $bits'

  # The name is the last bit
  # shellcheck disable=SC2016
  NAME='$bits[0]'

  # The module is all except the last bit, joined by dots
  # shellcheck disable=SC2016
  MOD='$bits[1:] | reverse | join(".")'

  grep '^{' |
    jq -c -M "$INPUT | . + {name: $NAME, module: $MOD} | del(.qname)" |
    jq -s -M '.'
'';

getTypesScript = withDeps "getTypes" [ jq ] ''
  #!${bash}/bin/bash

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

tagAstsScript = default: withDeps "tagAsts" [ jq ] ''
  #!${bash}/bin/bash

  # Given JSON objects on stdin, and a file descriptor containing JSON objects as
  # $1, combines those elements of each with matching pkg/mod/name. If no match is
  # found in $1, 'default' is used as a fallback

  function msg {
    echo -e "$1" 1>&2
  }

  [[ -n "$1" ]] || {
    msg "tagAsts requires an argument for its tags"
    msg "For example, 'echo FOO | tagAsts <(echo BAR)'"
    exit 1
  }

  TYPE=$(echo '${default}' | jq -r 'type') || {
    msg "Couldn't parse tagAsts default argument '${default}' as JSON"
    exit 3
  }

  [[ "x$TYPE" = "xobject" ]] || {
      msg "tagAsts default argument '${default}' has type '$TYPE'"
      msg "It should be an object"
      exit 4
  }

  FALLBACK='({"name":$this.name,"module":$this.module,"package":$this.package} + ${default})'

  # Call the current AST $this, then loop over $tags
  INPUT=".[] | . as \$this | \$tags + [$FALLBACK]"

  # Select $tags matching $this
  # shellcheck disable=SC2016
  QUERY='map(select((.module == $this.module) and (.name == $this.name))) | .[0]'

  # Combine matching $tags with $this
  # shellcheck disable=SC2016
  ACTION='. + $this'

  jq --argfile tags "$1" "[$INPUT | $QUERY | $ACTION]"
'';

annotateAstsScript = withDeps "annotateAsts" [ jq ] ''
  #!/usr/bin/env bash
  set -e

  function msg {
    echo -e "$1" 1>&2
  }

  function tagTypes {
    "${tagAstsScript ''{"type":null}''}" <(echo "$RAWSCOPE" | "${getTypesScript}")
  }

  function tagArities {
    "${tagAstsScript ''{"arity":null,"quickspecable":false}''}" <(echo "$RAWTYPES" | "${getAritiesScript}")
  }

     INPUT=$(cat)

  msg "Getting ASTs"

   RAWASTS=$(echo "$INPUT" | jq -c '.asts')

  msg "Getting types"

  RAWTYPES=$(echo "$INPUT" | jq -r '.result')

  msg "Getting scope"

  RAWSCOPE=$(echo "$INPUT" | jq -r '.scoperesult')

  msg "Tagging"

  echo "$RAWASTS" | tagTypes | tagArities

  msg "Tagged"
'';

annotateDb = writeScript "annotateDb" ''
  #!${bash}/bin/bash

  # Turns output from dump-package or dump-hackage into a form suitable for
  # clustering

  "${runTypesScript { inherit pkg;
                      pkgSrc = if pkg ? srcNixed
                                  then pkg.srcNixed
                                  else pkgSrc; }}" |
    "${annotateAstsScript}"                        |
    "${getDepsScript}"
'';

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
     O=$("${benchmark {
              inherit quick;
              cmd = annotateDb;
          }}" < "$asts")

     ${storeParts}
   ''
