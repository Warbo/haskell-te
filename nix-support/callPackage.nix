# This works the same way as callPackage in nixpkgs, but we allow the 'override'
# cruft added by 'makeOverridable' to be removed. This is important in some
# cases, e.g. where the result contains its own 'override' attribute.
{ newScope, self }:

f: args:
  with builtins // {
    result = newScope self f args;
  };
  if isAttrs result && result.removeOverrides or false
     then result.value
     else result
