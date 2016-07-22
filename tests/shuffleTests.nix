defs: with defs;
with builtins;
with lib;

let

# `unique` in Nix's standard library overflows the stack, since it's not
# tail-recursive; we use bash to avoid this

uniquePkgs =
  let elems  = writeScript "pkg-names" (concatStringsSep "\n" shuffledList);
      unique = parseJSON (runScript { buildInputs = [ jq ]; } ''
                 set -e
                 if sort < "${elems}" | uniq -d | grep '^.' > /dev/null
                 then
                   # `uniq -d` prints duplicate lines. Since `grep` found
                   # something, there must have been duplicates
                   echo "false"  > "$out"
                 else
                   # `grep` didn't find any (non-empty) lines, so `uniq` didn't
                   # find any dupes
                   echo "true" > "$out"
                 fi
               '');

   in testMsg unique "Shuffled package names look unique";

selection = random.randStrings shuffledList (length shuffledList);

in

testAll [
  (testMsg (isList shuffledList) "isList ${typeOf shuffledList}")

  uniquePkgs
]
