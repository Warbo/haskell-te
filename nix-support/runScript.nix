{ lib, writeScript, runCommand }:
with builtins; with lib;

env: text:

let script = writeScript "script" text;
    runner = runCommand  "runner" env script;
 in readFile "${runner}"
