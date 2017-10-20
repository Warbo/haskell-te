# Scripts which use our commands to generate data, and the results of running
# these scripts on some selected examples. This can be used in a few ways:
#
#  - If we're writing a Nix expression which needs the output of one of our
#    commands (e.g. some ASTs, a generated Haskell package, etc.) then we can
#    use the relevant 'command' function from here to run it.
#  - If we're defining a command, we don't want to expose an untested version,
#    but we also want to make sure that the invocations we test are the same as
#    the ones which will be used (also DRY!). We can do this by passing our
#    untested version as the 'script' parameter of the relevant 'command'
#    function, test the result, and use 'withDeps' to make the 'public' version
#    of the command depend on these tests passing.
#
# Most tests should use the provided example data, since it's designed to be
# fast. The only exception is when we're sampling, which obviously needs
# TEBenchmark.
{ fail, haskellPackages, haskellPkgToAsts, haskellPkgToRawAsts, jq, lib,
  makeHaskellPkgNixable, nix-config, nixedHsPkg, nixEnv, quickspec,
  quickspecAsts, runCommand, tipBenchmarks, tipToHaskellPkg, unpack, withNix }:

with lib;
rec {
  commands = {
    asts = { dir, name, script ? null }: runCommand "asts-of-${name}"
      (withNix {
        src         = dir;
        SKIP_NIX    = "1";
        buildInputs = [
          (haskellPkgToAsts { script = if script == null
                                          then haskellPkgToRawAsts
                                          else script; })
        ];
      })
      ''
        set -e
        haskellPkgToAsts "$src" > "$out"
      '';

    eqs = { asts, name, nixed, script ? null }: runCommand "eqs-of-${name}"
      {
        inherit asts;
        buildInputs = [ (if script == null then quickspecAsts else script) ];
        OUT_DIR     = nixed;
        MAX_SECS    = "180";
        MAX_KB      = "1000000";
        SKIP_NIX    = "1";
      }
      ''
        set -e
        quickspecAsts "$OUT_DIR" < "$asts" > "$out"
      '';

    finalEqs = { name, pkg, script ? null }: runCommand "test-quickspec-${name}"
      (nixEnv // {
        inherit pkg;
        buildInputs = [ (if script == null then quickspec else script) ];
        MAX_SECS    = "180";
        MAX_KB      = "1000000";
        SKIP_NIX    = "1";
      })
      ''
        set -e
        quickspec "$pkg" > "$out"
      '';

    haskellDrv = { dir, name, script ? null }: haskellPackages.callPackage
      (commands.haskellNixed { inherit dir name script; }) {};

    haskellNix = { dir, name, script ? null }: runCommand "nixed-${name}"
      {
        inherit dir;
        inherit (nix-config) stableHackageDb;
        buildInputs = [ fail (if script == null
                                 then makeHaskellPkgNixable
                                 else script) ];
        SKIP_NIX    = "1";
        n           = name;
      }
      ''
        set -e
        export HOME="$PWD"
        ln -s "$stableHackageDb/.cabal" "$HOME/.cabal"

        X=$(makeHaskellPkgNixable "$dir") ||
          fail "Package $n failed to nixify"
        cp -r "$X" "$out"
      '';

    haskellPkg = { name, script ? null, tip }:
      runCommand "haskell-pkg-of-${name}"
        {
          inherit tip;
          SKIP_NIX    = "1";
          buildInputs = [ fail (if script == null
                                   then tipToHaskellPkg
                                   else script) ];
        }
        ''
          set -e
          D=$(tipToHaskellPkg < "$tip")
          [[ -e "$D" ]] || fail "'$D' doesn't exist"

          X=$(readlink -f "$D")
          [[ -d "$X" ]] || fail "'$X' isn't dir"

          cp -r "$X" "$out"
        '';
  };

  # Selected example data for tests to use. These should be reasonably quick to
  # run.

  tip = { test-theory = ../tests/test-theory.smt2; };

  haskellPkgs = { script ? null }:
    mapAttrs (name: tip: commands.haskellPkg { inherit name tip; }) tip;

  haskellDrvs = mapAttrs (name: dir: haskellPackages.callPackage dir {})
                         (haskellNixed {});

  haskellNixed = { script ? null }:
    mapAttrs (name: dir: commands.haskellNix { inherit dir name script; })
             (haskellPkgs {});

  asts = { script ? null }:
    mapAttrs (name: dir: commands.asts { inherit dir name script; })
             (haskellNixed {});

  eqs = { script ? null }:
    mapAttrs (name: asts: commands.eqs {
                            inherit asts name script;
                            nixed = getAttr name (haskellNixed {});
                          })
             (asts {});

  finalEqs = { script ? null }:
    mapAttrs (name: pkg: commands.finalEqs { inherit name pkg script; })
             (haskellPkgs {});

  # Resource-intensive data, which should be used sparingly

  tip-benchmark = rec {
    asts = commands.asts {
      name = "tip-benchmark";
      dir  = nixed;
    };
    nixed = commands.haskellNix {
      name = "tip-benchmark-haskell";
      dir  = tipBenchmarks.tip-benchmark-haskell;
    };
  };

  isabelle-theories = genAttrs [ "list-full" "nat-full" "nat-simple" ] (name:
    rec {
      asts  = commands.asts { inherit name; dir = nixed; };
      nixed = commands.haskellNix { inherit name; dir = pkg; };
      pkg = commands.haskellPkg {
        inherit name;
        tip = ../benchmarks + "/${name}.smt2";
      };
    });
}
