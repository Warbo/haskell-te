from os         import getenv
from parameters import max_size, repetitions
from util       import tip_benchmarks, tip_setup

# Benchmark parameters. Will appear in alphabetical order as arguments, after
# 'cache'
args = {
    'rep'  : range(0, repetitions),
    'size' : range(1, max_size),
}

setup_cache = tip_setup(
    'hs',
    args,
    lambda stdout: ([getenv('hsTipRunner')], stdout))

# Generate benchmark functions and add them to this module
locals().update(tip_benchmarks(args))
