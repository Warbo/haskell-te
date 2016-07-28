{ runCommand, withNix, writeScript }:

env: text:

let script = writeScript "script" text;
 in runCommand  "runner" (withNix env) script;
