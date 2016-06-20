defs: with defs; with builtins;

let

strippedContent = f:
  let content  = readFile f;
   in replaceStrings ["\n" " " "\t"]
                     [""   ""  ""]
                     content;

output = tipBenchmarks.process { quick = true; };

failed = output.failed;

explored = all (n: all (x: strippedContent x != "")
                       output.explored."${n}")
               (attrNames output.explored);

haveEqs = all (n: strippedContent output.equations."${n}" != "")
              (attrNames output.equations);

nonZeroEqs = all (n: output.equationCounts."${n}" > 0)
                 (attrNames output.equationCounts);

withDbg = dbg: msg: x: addErrorContext dbg (testMsg x msg || trace dbg false);

in all (x: x) [

  (testDbg (!output.failed)  "TIP benchmark didn't fail" "")

  (testDbg explored          "TIP benchmark explored"
           (toJSON { inherit (output) formatted rawExplored; }))

  (testDbg haveEqs    "Got TIP equations"
           (toJSON { inherit (output) formatted annotated clustered explored
                     equations; }))
  (testDbg nonZeroEqs "Non-zero equation counts"
           (toJSON { inherit (output) equationCounts; }))
]
