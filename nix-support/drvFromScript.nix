{ bash, coreutils, jq, lib, nix, perl, procps, runCommand, utillinux, withNix,
  writeScript }:
with builtins;

env: text:
  let script = writeScript "script" text;
   in runCommand (env.name or "drv-from-script") (withNix env) script
