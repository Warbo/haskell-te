defs: with defs;
with builtins;
with lib;

let

# `unique` in Nix's standard library overflows the stack, since it's not
# tail-recursive: after recursing on the tail, duplicates of the head are
# removedeach call . after recursing on the tail of the list, it removes
# occurrences of the head and prepends one, then prepends the head.
# Our version takes the head of `list` This version doesn't,
# as it's tail-recursive.

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
