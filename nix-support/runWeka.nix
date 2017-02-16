{ callPackage, fetchFromGitHub, havePath }:

callPackage (if havePath "runWeka"
                then <runWeka>
                else fetchFromGitHub {
                       owner  = "Warbo";
                       repo   = "run-weka";
                       rev    = "6a6f627";
                       sha256 = "14c199nakf9khwbb02n675dhf8b73y2cxpvjwxijfinkankdad7g";
                     })
            {}
