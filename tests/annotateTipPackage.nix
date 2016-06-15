defs: with defs; with builtins;

let processed = tipBenchmarks.process { quick = true; };
 in trace (toJSON processed.rawAnnotated) false
