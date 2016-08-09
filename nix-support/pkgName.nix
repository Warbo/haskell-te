{ runScript }:
with builtins;

givenName:

assert isString givenName;

runScript { inherit givenName; } ''
  N=$(echo "$givenName" | sed -e 's/-[0-9][0-9.]*$//g')
  printf "%s" "$N" > "$out"
''
