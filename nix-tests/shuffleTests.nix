defs: with defs;

let shuffleExists = pathExists "${shuffledList}";
    shuffleUnique = parseJSON (runScript {} ''
      set -e
      AMOUNT=$(( RANDOM % 100 + 10 ))
      OUTPUT=$(head -n$AMOUNT < "${shuffledList}")
      COUNT=$(echo "$OUTPUT" | wc -l)
      UNIQUE=$(echo "$OUTPUT" | "${coreutils}/bin/sort" -u | \
                                "${coreutils}/bin/wc" -l)
      [[ "$COUNT" -eq "$UNIQUE" ]] || {
        echo -e "'$COUNT/$AMOUNT' unique lines found in '${shuffledList}'" 1>&2
        exit 1
      }
      echo "true" > "$out"
    '');
in all (t: assertMsg t.val t.msg) [
     { val = shuffleExists;
       msg = "Shuffled package list is created"; }
     { val = shuffleUnique;
       msg = "Packages in shuffled list are unique"; }
   ]
