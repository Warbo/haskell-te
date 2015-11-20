# Allow git repos to be used without pre-determined revisions or hashes, in the
# same way we can use `src = ./.`.
#
# For example:
#
# let latestGit = import /path/to/latestGit.nix
#  in stdenv.mkDerivation {
#       name = "My Project";
#       src  = latestGit { url = "http://example.com/project.git"; };
#     }

let source = builtins.fetchurl
      "http://chriswarbo.net/git/nix-config/branches/master/imports/latestGit.nix";
in import "${source}"
