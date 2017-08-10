# Adds a path to the Nix store, even if it's there already, and returns the
# result as a string. This causes the data to be cached based solely on its
# content, rather than the inputs which generated it. For example, if we use
# some scripts to generate data, then perform some expensive computation with
# that data, we only want to re-do that computation if the data changes; if we
# refactor the scripts so they have a different hash, but generate the same
# data, Nix will re-do the computation regardless. If we instead pass the data
# to cacheContent, and do our computation with the result, then such
# "unobservable" changes won't invalidate the cached computations.
#
# NOTE: This works by forcing a build; this will slow down evaluation if your
# data is expensive to *generate*.

{ drvFromScript, jq }:

name: dir: import (drvFromScript
                    {
                      inherit dir name;
                      buildInputs = [ jq ];
                    }
                    ''
                      nix-store --add "$dir" | jq -R '.' > "$out"
                    '')
