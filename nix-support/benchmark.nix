{ fetchFromGitHub, havePath, makeWrapper, nix, pkgs, pythonPackages, runCommand,
  time, withNix, writeScript }:

with builtins;
rec {
  src = if havePath "sample-bench"
           then <sample-bench>
           else toString (fetchFromGitHub {
                  owner  = "Warbo";
                  repo   = "sample-bench";
                  rev    = "d71e333";
                  sha256 = "1hgdnh4lqgl1gdniggriqql9l2vhr63fg33vs9dqfs2m3zhaj18a";
                });

  benchmark = import src { inherit pkgs; };

  timeout = pkgs.callPackage "${src}/timeout.nix" {};

  simpleBench = runCommand "simple" {
    buildInputs = [ makeWrapper pythonPackages.python time ];
    raw         = writeScript "benchmark" ''
      #!/usr/bin/env python
      import json
      import re
      import shutil
      import subprocess
      import sys
      import tempfile

      def msg(s):
        sys.stdout.write(s + "\n")

      def containsErrors(s):
        for snippet in ["jq: error", "MLSpec: Failed", "syntax error",
                        "Argument list too long", "out of memory",
                        "parse error:"]:
          if snippet in s:
            msg("Errors found in stderr")
            return True

        if re.search("^error:", s) == None:
          return False

        msg("stderr contains errors")
        return True

      # Run the given command, benchmarking with 'time' and enforcing
      # time/space limits with 'withTimeout'.

      stdin = sys.stdin.read()
      cmd   = sys.argv[1]
      args  = ['time', '-f', 'BEGINTIME%eENDTIME', 'withTimeout', cmd]
      proc  = subprocess.Popen(args,  stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE)

      (out, err) = proc.communicate(stdin)
      code       = proc.returncode

      msg(err)

      failure = []
      if code != 0:
        failure.append({"exitcode": code})
        msg(cmd + " failed with code " + str(code))

      if containsErrors(err):
        failure.append({"stderr": err})
        msg("Errors found in stderr of " + cmd)

      if failure == []:
        msg("Finished running " + cmd)

      time = re.search(
        'BEGINTIME.*ENDTIME',
        err).group(0).replace(
        'BEGINTIME', "").replace(
        'ENDTIME', "")

      # Write large strings to the Nix store, so we can use nice little paths

      tmpdir = tempfile.mkdtemp()

      def store(content, name):
        path = tmpdir + '/' + name
        with open(path, 'w') as f:
          f.write(content)
        return subprocess.check_output(['nix-store', '--add', path]).strip()

      try:
        inpath  = store(stdin, 'stdin')
        outpath = store(out,   'stdout')
        errpath = store(err,   'stderr')
        print json.dumps({"failure" : failure,
                          "time"    : time,
                          "cmd"     : cmd,
                          "stdin"   : inpath,
                          "stdout"  : outpath,
                          "stderr"  : errpath})
      finally:
        shutil.rmtree(tmpdir)
    '';
  }
  ''
    makeWrapper "$raw" "$out" --prefix PATH :  "${pythonPackages.python}/bin" \
                              --prefix PATH :  "${time}/bin"                  \
                              --prefix PATH :  "${timeout}/bin"               \
                              --prefix PATH :  "${nix}/bin"                   \
                              --set NIX_PATH   "${(withNix {}).NIX_PATH}"     \
                              --set NIX_REMOTE "${(withNix {}).NIX_REMOTE}"
  '';
}
