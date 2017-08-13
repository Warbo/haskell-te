{ bash, lib, makeWrapper, runCommand, wrap, writeScript }:
with lib;
with builtins;

name: deps: text:

assert isString name;
assert isList   deps;
assert isString text;

wrap {
  name   = "${name}-with-deps";
  paths  = deps;
  script = text;
}
