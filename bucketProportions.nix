# Choose a bunch of samples, bucket them in a variety of ways and measure the
# proportion of ground truth theorems which apply to the resulting buckets.
#
# Write output to JSON for archiving.
with builtins;
with import ./nix-support {};

{ exposeDefs ? false }:  # Set to true to access definitions, e.g. to debug

with { defs = rec {

  maxSize = 100;
  reps    = 100;

  dupeSamples = runCommand "samples-with-dupes.json"
    {
      script = wrap {
        name   = "script.rkt";
        paths  = [ tipBenchmarks.tebench.env ];
        vars   = tipBenchmarks.tebench.cache;
        script = ''
          #!/usr/bin/env racket
          #lang racket
          (require json)
          (require lib/sampling)

          (write-json
            (make-immutable-hash
              (map (lambda (size)
                     (cons (string->symbol (~a size))
                           (make-immutable-hash
                             (map (lambda (rep)
                                    (eprintf
                                      (format "Size ~a rep ~a\n" size rep))
                                    (cons (string->symbol (~a rep))
                                          (map ~a
                                            (set->list
                                              (sample-from-benchmarks size
                                                                      rep)))))
                                  (range 0 ${toString reps} )))))
                   (range 1 ${toString (maxSize + 1)} ))))
        '';
      };
    }
    ''
      "$script" > "$out"
    '';

  samples = runCommand "samples.json"
    {
      inherit dupeSamples;
      dedupe = wrap {
        name = "dedupe.py";
        paths = [ nixpkgs.python ];
        script = ''
          #!/usr/bin/env python
          import json
          import sys

          data = json.loads(sys.stdin.read())
          for size in data:
            seen = []
            for iRep in sorted([int(rep) for rep in data[size]]):
              rep = str(iRep)
              sample = frozenset(data[size][rep])
              if sample in seen:
                data[size][rep] = None
              seen += [sample]
          print(json.dumps(data))
        '';
      };
    }
    ''
      "$dedupe" < "$dupeSamples" > "$out"
    '';

  result = null;

}; };
if exposeDefs
   then defs
   else defs.result
