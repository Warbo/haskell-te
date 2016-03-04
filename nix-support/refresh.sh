#!/usr/bin/env bash

# Download the latest version of Nix expressions which come from elsewhere

wget -O nixFromCabal.nix http://chriswarbo.net/git/nix-config/branches/master/custom/imports/nixFromCabal.nix
