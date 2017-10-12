{ lib, runCommand, withNix }:
with builtins; with lib;

env: text:

let drv = runCommand "runScript" (withNix env) text;
 in unsafeDiscardStringContext (readFile "${drv}")
