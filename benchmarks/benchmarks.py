# See "Writing benchmarks" in the asv docs for more information.

from json  import loads
from os    import getenv
from sys   import stderr
from util  import cached, pipe, sort, timed_run

# Benchmark parameters. Will appear in alphabetical order as arguments, after
# 'cache'
params = {
    'rep'     :  range(0, 2),
    'size'    : range(1, 3),
    'timeout' : [timeout_secs]
}

# Tells asv how to run the benchmarks
attrs = {
    'repeat'      : 1,
    'number'      : 1,
    'params'      : reduce(lambda x, y: x + (y,),
                           [params[name] for name in sort(params.keys())],
                           ()),
    'param_names' : sort(params.keys())
}

# Used by our own code
timeout_secs = 20

# Running a TE tool is expensive, so we only want to run each sample once. By
# returning all of the results from setup_cache, each benchmark can can pick out
# the values it cares about, without having to re-run anything.
#
# The returned value will appear as the first argument to each benchmark
def setup_cache():
    '''Calculate results once, up front, and reuse for each benchmark.'''
    cache = {}
    for size in params['size']:
        cache[size] = []
        for rep in params['rep']:
            stdout, _ = pipe([getenv('qsSetup'), str(size), str(rep)])
            data      = loads(stdout)
            cache[size].append(timed_run([getenv('qsRunner'), data['runner']],
                                         data['code'],
                                         timeout_secs))
    return cache
setup_cache.timeout = 3600

# Benchmark functions

def track_sample(cache, rep, size, timeout):
    return []

def track_stdout(cache, rep, size, timeout):
    '''Return the raw stdout, so we can store it in git.'''
    return cached(cache, size, rep)['stdout']

def track_time(cache, rep, size, timeout):
    return cached(cache, size, rep)['time']

def track_precision(cache, rep, size, timeout):
    '''Run QuickSpec and calculate precision of the result.'''
    #cache[size][rep]
    stderr.write(repr(cache))
    return 1

# Assign parameters to benchmarks

for f in (track_sample, track_stdout, track_time, track_precision):
    for attr in attrs:
        setattr(f, attr, attrs[attr])
