{ lib, writeScript, runCommand }:
with builtins; with lib;

env: text:

let hash   = unsafeDiscardStringContext (hashString "sha256" text);
    script = writeScript "script-${hash}" text;
    runner = runCommand  "runner-${hash}" env script;
 in unsafeDiscardStringContext (readFile "${runner}")
