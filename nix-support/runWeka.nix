{ callPackage, fetchFromGitHub, havePath }:

callPackage (if havePath "runWeka"
                then <runWeka>
                else fetchFromGitHub {
                       owner  = "Warbo";
                       repo   = "run-weka";
                       rev    = "520a2a8";
                       sha256 = "1325yglg2kdj1bhglhl0947a50apa9pl48wc4va6yca2dbcjf3sr";
                     })
            {}
