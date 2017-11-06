# Get the original nixpkgs path
{}:

with builtins.tryEval <real>;
if success then value else <nixpkgs>
