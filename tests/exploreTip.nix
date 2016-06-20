defs: with defs; with builtins;

let

output = tipBenchmarks.process { quick = true; };

failed = output.failed;

eqs = output.equations;

eqCounts = output.equationCounts;

haveEqs = all (n: let content  = readFile eqs."${n}";
                      stripped = replaceStrings ["\n" " " "\t"]
                                                [""   ""  ""]
                                                content;
                   in stripped != "")
              (attrNames eqs);

nonZeroEqs = all (n: eqCounts."${n}" > 0) (attrNames eqCounts);

withDbg = dbg: msg: x: addErrorContext dbg (testMsg x msg || trace dbg false);

in all (x: x) [
  (withDbg ""                             "TIP benchmark didn't fail" (!failed))
  (withDbg "eqs: ${toJSON eqs}"           "Got TIP equations"         haveEqs)
  (withDbg "eqCounts: ${toJSON eqCounts}" "Non-zero equation counts"  nonZeroEqs)
]
