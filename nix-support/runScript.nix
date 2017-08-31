{ drvFromScript, lib }:
with builtins; with lib;

env: text:

let drv = drvFromScript env text;
 in unsafeDiscardStringContext (readFile "${drv}")
