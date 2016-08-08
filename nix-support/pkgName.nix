{ runScript }:
with builtins;

name:

assert isString name;

runScript { inherit name; } ''
  N=$(echo "$name" | sed -e 's/-[0-9][0-9.]*$//g')
  printf "%s" "$N" > "$out"
''
