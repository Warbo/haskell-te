#!/usr/bin/env bash

# Helper functions for scripts to source

function info {
    echo -e "INFO: $1" >> /dev/stderr
}

function warn {
    echo -e "WARNING: $1" >> /dev/stderr
    return 1
}

function abort {
    echo -e "ERROR: $1" >> /dev/stderr
    exit 1
}
