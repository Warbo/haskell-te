defs: with defs;
with builtins;
with lib;

let

two  = writeScript "two" ''{ "mean":{"estPoint":"2"}}'';
two2 = timeCalc.sumTimeDrvs [ two ];
four = timeCalc.sumTimeDrvs [ two two ];

in {
  twoEqTwo = testRun "sum [2] should equal 2" null { inherit two2; } ''
               set -e

               N=$(jq -r '.mean.estPoint' < "$two2")
               [[ "$N" -eq "2" ]] && exit 0

               echo "From '$two2' got N: $N" 1>&2
               exit 1
             '';

  twoPlusTwo = testRun "sum [2 2] should equal 4" null
                       { inherit four; } ''
                         set -e

                         N=$(jq -r '.mean.estPoint' < "$four")
                         [[ "$N" -eq "4" ]] && exit 0

                         echo "From '$four' got N: $N" 1>&2
                         exit 1
                       '';
}
