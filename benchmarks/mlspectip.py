from os         import getenv
from parameters import reps, sizes
from util       import tip_benchmarks, tip_cache

# Benchmark parameters. Will appear in alphabetical order as arguments, after
# 'cache'
args = {
    'rep'  : reps,
    'size' : sizes,
}

#setup_cache = tip_cache(
#    'ml',
#    args,
#    lambda stdout: ([getenv('mlTipRunner')], stdout))

# Generate benchmark functions and add them to this module
#locals().update(tip_benchmarks(args))
