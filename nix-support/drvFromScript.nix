{ bash, coreutils, jq, lib, nix, perl, procps, runCommand, utillinux, withNix,
  writeScript }:
with builtins;

env: text:
  let script = writeScript "script" text;
   in runCommand "runner" (withNix env) script
