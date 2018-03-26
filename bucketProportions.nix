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

  result = groundTruthsOf samples;

}; };
if exposeDefs
   then defs
   else defs.result
