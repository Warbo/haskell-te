# Theory Exploration tools for Haskell; packaged for Nix

# Take haskellPackages as a parameter. Also accept src overrides (see addPkg)
args@{ haskellPackages, lib, latestGit ? (import ./latestGit.nix), ... }:

# Attributes are package names, "call" is whether to use callPackage or just
# import. "url" is the default Git repo name which, annoyingly, doesn't always
# match the package name. Fixable, but would temporarily break everything ;)
let urls = {
      ArbitraryHaskell = { call = true;  url = "arbitrary-haskell"; };
      AstPlugin        = { call = true;  url = "ast-plugin";        };
      getDeps          = { call = true;  url = "get-deps";          };
      HS2AST           = { call = true;  url = "hs2ast";            };
      ml4hs            = { call = false; url = "ml4hs";             };
      mlspec           = { call = true;  url = "mlspec";            };
      mlspec-helper    = { call = true;  url = "mlspec-helper";     };
      ML4HSFE          = { call = true;  url = "ml4hsfe";           };
      nix-eval         = { call = true;  url = "nix-eval";          };
      order-deps       = { call = true;  url = "order-deps";        };
      treefeatures     = { call = true;  url = "tree-features";     };
    };

    # Default source for TE tools
    getGit = x: latestGit {
                  url = "http://chriswarbo.net/git/${urls.${x}.url}.git";
                };

    # Append package "x" to the set "p"
    addPkg = hs: x: p: let source  = args.${x} or (getGit x);
                           package = if urls.${x}.call
                                        then hs.callPackage source {}
                                        else import         source;
                    in p // { ${x} = package; };

# Return a modified set of haskellPackages, with added theory exploration tools
in haskellPackages.override {

  # Build up a set of overrides, by mapping over the attributes in urls
  overrides = self: super: lib.fold (addPkg self)
                                    {}
                                    (builtins.attrNames urls);
}
