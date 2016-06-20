defs: with defs; with builtins;

let

output = tipBenchmarks.process { quick = true; };

failed = output.failed;

eqs = output.equations;

haveEqs = all (n: (readFile eqs."${n}".stdout) != "") (attrNames eqs);

in testMsg (!failed) "TIP benchmark didn't fail" &&
   testMsg haveEqs "Got equations"
