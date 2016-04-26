{ haskellPackages, lib }:

# Extract ASTs from GHC and its dependencies; these are a special case since
# Cabal will refuse to built them on their own.

haskellPackages.ghc
