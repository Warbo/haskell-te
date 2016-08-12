defs: with defs;
with builtins;
with lib;

let

# `unique` in Nix's standard library overflows the stack, since it's not
# tail-recursive; we use bash to avoid this

uniquePkgs =
  let elems  = writeScript "pkg-names" (concatStringsSep "\n" shuffledList);
   in drvFromScript { inherit elems; } ''
        set -e
        if sort < "$elems" | uniq -d | grep '^.' > /dev/null
        then
          # `uniq -d` prints duplicate lines. Since `grep` found
          # something, there must have been duplicates
          exit 1
        else
          # `grep` didn't find any (non-empty) lines, so `uniq` didn't
          # find any dupes
          touch "$out"
        fi
      '';

in {
 inherit uniquePkgs;

 isShuffledList = testMsg (isList shuffledList) "isList";
}
