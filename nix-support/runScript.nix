{ dbug, lib, runCommand, withNix, writeScript }:
with builtins; with lib;

env: text:

let script = writeScript "script" text;
    runner = runCommand  "runner" (withNix env) script;
 in dbug "Running script:\n\n${text}\n\nEND SCRIPT"
         (unsafeDiscardStringContext (readFile "${runner}"))
