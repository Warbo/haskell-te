{ callPackage, fetchFromGitHub, stable }:

callPackage (if stable
                then fetchFromGitHub {
                       owner  = "Warbo";
                       repo   = "run-weka";
                       rev    = "c4033ce";
                       sha256 = "1zdmzznlrdz6ydsd2bm18bjb1xpiq840dvb6x64m4vhxddl0gg33";
                     }
                else <runWeka>)
            {}
