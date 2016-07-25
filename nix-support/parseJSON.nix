# Give more context to fromJSON, in case of errors, and avoid floating point
# issues by first converting them to strings

{ dbug, jq, runScript, writeScript }:

with builtins;

let allNumsToStrings = writeScript "nums-to-strings" ''
      #!${jq}/bin/jq -Mf

      # "walk" definition, since it's only built-in in jq > 1.5, taken from
      # https://github.com/stedolan/jq/blob/master/src/builtin.jq
      def do_walk(f):
        . as $in
        | if type == "object" then
            reduce keys[] as $key
              ( {}; . + { ($key):  ($in[$key] | do_walk(f)) } ) | f
        elif type == "array" then map( do_walk(f) ) | f
        else f
        end;

      do_walk(if type == "number" then tostring else . end)
    '';
    parseString = txt:
      let result = runScript { inherit txt; passAsFile = [ "txt" ]; } ''
                     "${allNumsToStrings}" < "$txtPath" > "$out"
                   '';
       in dbug "Given JSON is '${txt}'; stringifying numbers too"
               (fromJSON result);
in txt:
   dbug "Parsing JSON value"
     (if isString txt
         then parseString txt
         else abort "Asked to parse a ${typeOf txt} as JSON")
