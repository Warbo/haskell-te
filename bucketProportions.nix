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

  # Gather samples: run 'choose_sample size rep' for each size up to maxSize and
  # rep from 0 to reps-1. Returns an object mapping sizes to objects, where the
  # inner objects map reps to lists of name strings. We use the name 'dupe'
  # because we will end up with duplicate samples for small sizes. We do the
  # looping in Racket so we can call the sampler without the overhead of
  # invoking a fresh Racket process each time.
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

  # Deduplicate the raw samples: duplicates are replaced with null, whilst
  # non-duplicates are set as the "sample" key of an object.
  samples = runCommand "samples.json"
    {
      inherit dupeSamples;
      dedupe = wrap {
        name = "dedupe.py";
        paths = [ nixpkgs.python3 ];
        script = ''
          #!/usr/bin/env python3
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
              else:
                data[size][rep] = {'sample': data[size][rep]}
              seen += [sample]
          print(json.dumps(data))
        '';
      };
    }
    ''
      "$dedupe" < "$dupeSamples" > "$out"
    '';

  # Runs each sample through the stdio of a given program, adding the result to
  # the samples JSON. Useful for running a bucketing script on each sample.
  processSamples = { key, prog, samples }: runCommand "processed-${key}.json"
    {
      inherit samples;
      script = wrap {
        name  = "process-samples.py";
        paths = [ nixpkgs.python3 ];
        vars  = {
          inherit key prog;
          inherit (testData.tip-benchmark) asts;
        };
        script = ''
          #!/usr/bin/env python3
          from io         import StringIO
          from json       import dumps, loads
          from os         import getenv
          from subprocess import check_output
          from sys        import stderr, stdin

          msg  = lambda x: stderr.write(repr(x) + '\n')

          sort = lambda collection: sorted([elem for elem in collection])

          asts = {x['name']: x for x in loads(open(getenv('asts'), 'r').read())}

          astsFor = lambda names: [asts[name] for name in sort(names)]

          prog = getenv('prog')

          process = lambda names: loads(check_output(
            [prog],
            input=dumps(astsFor(names)).encode('utf-8')).decode('utf-8'))

          def recurse(path, val):
            if val is None:
              return None
            if type(val) == type({}):
              if 'sample' in val:
                return dict(val, sample=recurse(path, val['sample']))
              return {k: recurse(path + [k], val[k]) for k in sort(val)}
            msg(path)
            return process(val)

          data = loads(stdin.read())

          print(dumps(recurse([], data)))
        '';
      };
    }
    ''
      "$script" < "$samples" > "$out"
    '';

  # Run the bucket script on each sample; we use a few bucket sizes, in
  # increments
  addHashBuckets = samples: processSamples {
    inherit samples;
    key  = "hashed";
    prog = wrap {
      name  = "hash";
      paths = [ buckets.hashes jq ];
      vars  = {
        sizes = concatStringsSep " " (map toString (lib.range 1 20));
      };
      script = ''
        #!/usr/bin/env bash
        set -e

        INPUT=$(cat)

        for CLUSTER_SIZE in $sizes
        do
          export CLUSTER_SIZE
          echo "$INPUT" | hashBucket |
            jq '{(env["CLUSTER_SIZE"]) : map(map(.name))}'
        done | jq -s 'add'
      '';
    };
  };

  groundTruthsOf = samples: runCommand "ground-truths.json"
    {
      inherit samples;
      script = wrap {
        name   = "ground-truths-of.rkt";
        paths  = [ tipBenchmarks.tebench.env ];
        vars   = tipBenchmarks.tebench.cache;
        script = ''
          #!/usr/bin/env racket
          #lang racket
          (require        json)
          (require        rackunit)
          (require        lib/conjectures)
          (require/expose lib/conjectures (theorem-files-admitted-by))
          (require        lib/normalise)
          (require        lib/util)

          (define (err x)
            (error (format "~S" x)))

          ;; Ground truth for a sample (list of encoded names)
          (define (theorems-of-sample sample)
            (eprintf "theorems-of-sample\n")
            (unless (list? sample)
              (err `((error  "Expected sample to be a list")
                     (sample ,sample))))
            (theorem-files-admitted-by (map (compose decode-name string->symbol)
                                            sample)))

          ;; Ground truth for a list of samples (e.g. buckets)
          (define (theorems-of-sample-list samples)
            (eprintf "theorems-of-sample-list\n")
            (remove-duplicates
              (foldl (lambda (sample theorems)
                       (eprintf "\n~S\n" `((theorems ,theorems) (sample ,sample)))
                       (append theorems (theorems-of-sample sample)))
                     '()
                    samples)))

          ;; Takes a sample or list of samples, returns it with ground truth
          (define (add-ground-truth sample-or-list)
            (eprintf "add-ground-truth\n")
            (make-immutable-hash
              `((names    . ,sample-or-list)
                (theorems . ,(cond
                               [(not (list? sample-or-list))
                                (err `((error "Should have got a list")
                                       (sample-or-list ,sample-or-list)))]

                               [(empty? sample-or-list) '()]

                               [(string? (first sample-or-list))
                                (theorems-of-sample      sample-or-list)]

                               [(list?   (first sample-or-list))
                                (theorems-of-sample-list sample-or-list)]

                               [#t (err
                                 `((error "Unexpected list type")
                                   (sample-or-list ,sample-or-list)))])))))

          ;; Adds ground truths to any lists in the given map, recursively
          (define (add-ground-truths data)
            (eprintf "add-ground-truths\n")
            (hash-foldl (lambda (key value result)
                          (hash-set result key
                            (cond
                              [(list?  value) (add-ground-truth  value)]
                              [(hash?  value) (add-ground-truths value)]
                              [(equal? value 'null) value]

                              [#t (err `((error  "Unexpected type")
                                         (key    ,key)
                                         (value  ,value)
                                         (result ,result)))])))
                        (make-immutable-hash '())
                        data))

          ;; Add ground truths to stdio
          (write-json (add-ground-truths (string->jsexpr (port->string))))
        '';
      };
    }
    ''
      "$script" < "$samples" > "$out"
    '';

  withBuckets = addHashBuckets samples;

  result = groundTruthsOf withBuckets;

}; };
if exposeDefs
   then defs
   else defs.result
