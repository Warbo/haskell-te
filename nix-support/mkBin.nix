{ attrsToDirs, wrap }:

args: attrsToDirs {
  bin = builtins.listToAttrs [{
    inherit (args) name;
    value = wrap args;
  }];
}
