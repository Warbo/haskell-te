{ bash, lib, makeWrapper, runCommand, writeScript }:
with lib;
with builtins;

name: deps: text:

assert isString name;
assert isList deps;
assert isString text;

with {
  prefices = fold (dep: rest: rest + '' --prefix PATH : "${dep}/bin"'') "" deps;
};

runCommand "${name}-with-deps" { buildInputs = [ makeWrapper ]; } ''
  #!${bash}/bin/bash
  makeWrapper "${writeScript "${name}-script" text}" "$out" ${prefices}
''
