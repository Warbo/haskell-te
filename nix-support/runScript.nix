{ dbug, drvFromScript, lib }:
with builtins; with lib;

env: text:

let drv = drvFromScript env text;
 in dbug "Running script:\n\n${text}\n\nEND SCRIPT"
         (unsafeDiscardStringContext (readFile "${drv}"))
