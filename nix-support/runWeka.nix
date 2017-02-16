{ callPackage, fetchFromGitHub, havePath }:

callPackage (if havePath "runWeka"
                then <runWeka>
                else fetchFromGitHub {
                       owner  = "Warbo";
                       repo   = "run-weka";
                       rev    = "a22cd2c";
                       sha256 = "153k060k3wzqqir4amv0f5viwm8g419abk46hh61s4psb7cascka";
                     })
            {}
