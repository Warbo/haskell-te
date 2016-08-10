{ benchmark, checkHsEnv, haskellPackageNames, format, haskellPackages, jq, lib,
  ml4hs, mlspec, ourCheck, parseJSON, pkgName, runScript, self, strip,
  writeScript }:
with builtins;
with lib;

let

explore-theories = f: writeScript "explore-theories" ''
  set -e
  set -o pipefail

  INPUT=$(cat)

  function noDepth {
    grep -v "^Depth" || true # Don't abort if nothing found
  }

  echo "$INPUT" | MLSpec "$@" | noDepth | jq -s '.'
'';

extractEnv = f:
  trace "Extracting env from '${f}'" (runScript {} ''
    set -e
    set -o pipefail

    [[ -e "${f}" ]] || {
      echo "Path '${f}' doesn't exist" 1>&2
      exit 1
    }

    jq -r '.[] | (if type == "array" then .[] else . end) | .package' < "${f}" |
      sort -u > "$out"
  '');

findHsPkgReferences =
  let extractionScript = writeScript "find-references" ''
        # Allow package names to be given directly, one per line
        INPUT=$(cat)
        echo "$INPUT"

        # Take package names from JSON fields. These include:
        #
        #  - Objects with a 'package' field
        #  - Arrays of such objects
        #  - Arrays of arrays of such objects
        #
        # We should be able to ignore dependencies, as they'll be brought in
        # automatically.
        FLATTEN='if type == "array" then .[] else .'
        echo "$INPUT" | jq -r "$FLATTEN | $FLATTEN | .package" 2> /dev/null || true
      '';
   in writeScript "unique-references" ''
        INPUT=$(cat | grep '[a-zA-Z_]')
        while read -r NAME
        do
          if grep -xF "$NAME" < "${haskellPackageNames}" > /dev/null
          then
            echo "$NAME"
          fi
        done < <(echo "$INPUT" | "${extractionScript}" | sort -u | grep '^.')
      '';

hsPkgsInEnv = env: names:
  parseJSON (runScript env ''
    "${checkHsEnv names}" || exit 1
    echo "true" > "$out"
  '');

# Make a list of packages suitable for a 'buildInputs' field. We treat Haskell
# packages separately from everything else. The Haskell packages will include:
#
#  - The contents of 'extra-haskell-packages', required for our scripts
#  - The contents of the 'extraHs' argument; use '[]' for none
#  - The cabal package contained at path 'standalone' (requires a 'default.nix'
#    file, e.g. from 'nixFromCabal'); use 'null' for none
#  - Any 'package' fields read from the JSON file 'f'
#
# The non-Haskell packages will include:
#
#  - The contents of extra-packages, required by our scripts
#  - The contents of the 'extraPkgs' argument; use '[]' for none
#
extractedEnv = { extraPkgs ? [], extraHs ? [], standalone ? null, f ? null }:
      # Use a variety of extra settings when 'standalone' is given
  let attrs   = if standalone != null &&
                   pathExists (unsafeDiscardStringContext
                                 "${toString standalone}/default.nix")
                   then trace "Including '${toString standalone}'" rec {
                     pkg   = h: h.callPackage (import standalone) {};
                     pkgs  = h: if elem name hsNames
                                   then []
                                   else [ (pkg h) ];
                     name  = pkgName (pkg haskellPackages).name;
                     names = [ name ];
                   }
                   else {
                     pkgs  = h: [];
                     names = [];
                   };
      extracted = [];#if f == null then []
                     #           else map strip (splitString "\n" (extractEnv f));
      hsNames = unique (map pkgName (extracted ++ extra-haskell-packages ++ extraHs));
      hsPkgs  = h: (concatMap (n: if haskellPackages ? "${n}"
                                     then [ h."${n}" ]
                                     else [          ])
                              hsNames) ++ attrs.pkgs h;
      ps      = [ (haskellPackages.ghcWithPackages hsPkgs) ] ++
                extra-packages ++ extraPkgs;
   in assert hsPkgsInEnv { buildInputs = ps; } (hsNames ++ attrs.names);
      ps;

# Haskell packages required for MLSpec
extra-haskell-packages = [ "mlspec" "mlspec-helper" "runtime-arbitrary"
                           "quickspec" ];

prefixed-haskell-packages = concatStringsSep "\n"
                              (map (x: "h.${x}") extra-haskell-packages);

extra-packages = [ jq ];

exploreEnv = [ (haskellPackages.ghcWithPackages (h: map (n: h."${n}")
                                                    extra-haskell-packages)) ] ++
             extra-packages;

mkGhcPkg = writeScript "mkGhcPkg" ''
  set -e
  set -o pipefail

  echo "(haskellPackages.ghcWithPackages (h: ["

  GIVEN=($1)
  EXTRA=($2)
  for PKG in "''${GIVEN[@]}" "''${EXTRA[@]}"
  do
    UNQUAL=$(echo "$PKG" | sed -e 's/^h\.//g')
    FOUND=$(nix-instantiate --eval -E \
            "let pkgs = import <nixpkgs> {}; in pkgs.haskellPackages ? $UNQUAL")
    if [[ "x$FOUND" = "xtrue" ]]
    then
      echo "$PKG"
    else
      echo "Couldn't find '$PKG' in haskellPackages; ignoring, in the hope we have a nixFromCabal alternative" 1>&2
    fi
  done

  echo "]))"
'';

doExplore = standalone: quick: clusterCount: f:
  let cmd    = toString (explore-theories f);
      script = ''
        set -e
        export CLUSTERS="${clusterCount}"
        "${benchmark {
             inherit quick cmd;
             inputs = [f];
         }}" < "${f}" > "$out"
      '';
      env    = { buildInputs = extractedEnv { inherit standalone f; }; };
   in parseJSON (runScript env script);

go = { quick, standalone }: clusterCount: clusters:
       map (doExplore standalone quick clusterCount) clusters;

aCheck = formatted: result:
  assert isAttrs formatted;
  assert all (n: isString n)                  (attrNames formatted);
  assert all (n: isInt (fromJSON n))          (attrNames formatted);
  assert all (n: isList formatted."${n}")       (attrNames formatted);
  assert all (n: all isString formatted."${n}") (attrNames formatted);

  assert ourCheck "explored is set ${toJSON result}"
               (isAttrs result);

  assert ourCheck "explored keys are numeric ${toJSON result}"
               (all (n: isInt  (fromJSON n))  (attrNames result));

  assert ourCheck "explored values are lists ${toJSON result}"
               (all (n: isList result."${n}") (attrNames result));

  assert ourCheck "explored values contain sets ${toJSON result}"
               (all (n: all isAttrs result."${n}") (attrNames result));

  assert ourCheck "explored values have stdout ${toJSON result}"
               (all (n: all (x: x ? stdout) result."${n}")
                    (attrNames result));

  assert ourCheck "explored values have time ${toJSON result}"
               (all (n: all (x: x ? time) result."${n}")
                    (attrNames result));
  true;

checkAndExplore = { quick, formatted, standalone ? null }:
  let results = mapAttrs (go { inherit quick standalone; }) formatted;
      failed  = any (n: any (x: x.failed) results."${n}") (attrNames results);
      result  = { inherit results failed; };
   in if failed then result
                else assert aCheck formatted result.results; result;

in {
  inherit extra-haskell-packages explore-theories exploreEnv
          extractedEnv findHsPkgReferences;
  explore = checkAndExplore;
}
