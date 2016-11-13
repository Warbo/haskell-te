defs: with defs; with builtins; pkg:

rec {

join = x: addErrorContext "joining ${toJSON x}"
            (concatStringsSep " " (map (e: ''"${e}"'') x));

inScript = n: ''
  cat ${join pkg.explored.${n}} | jq -s '.' > out
  "${storeResult}" out
'';

outScript = input: ''
  reduce-equations < "${input}" > out
  "${storeResult}" out
'';

checkReduce = n:
  let iScript = inScript n;
      oScript = outScript input;
      input   = addErrorContext "inScript: ${iScript} "
                                (runScript {} iScript);
      output  = addErrorContext "oScript: ${oScript} "
                                (runScript {
                                    buildInputs = explore.extractedEnv {
                                      extraHs = [ "reduce-equations" ];
                                    };
                                  }
                                  oScript);
      dbg     = toJSON { inherit iScript oScript input output; };
      result  = output != "";
   in addErrorContext dbg result;

tryReduce = n: addErrorContext "reducing: ${toJSON pkg.explored.${n}} "
                               (checkReduce n);

result = testMsg (all tryReduce (attrNames pkg.explored)) "Can reduce";

}.result
