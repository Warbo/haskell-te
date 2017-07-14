# See "Writing benchmarks" in the asv docs for more information.

from json  import dumps, loads
from os    import getenv
from sys   import stderr
from util  import cached, eqs_in, pipe, sort, timed_run

# Used by our own code
timeout_secs = 200

# Benchmark parameters. Will appear in alphabetical order as arguments, after
# 'cache'
params = {
    'rep'     : range(0, 1),
    'size'    : range(1, 5),
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

def setup_cache():
    '''Running a TE tool is expensive, so we only want to run each sample once.
    By returning all of the results from setup_cache, each benchmark can pick
    out the values it cares about, without having to re-run anything.
    The returned value will appear as the first argument to each benchmark.'''
    cache = {}
    for size in params['size']:
        cache[size] = [{} for _ in params['rep']]
        for rep in params['rep']:
            data = {'timeout': timeout_secs}

            # Choose a sample, and generate QuickSpec code for exploring it
            sample, _      = pipe(['choose_sample', str(size), str(rep)])
            date['sample'] = sample

            stdout, _ = pipe([getenv('qsSetup')], sample)
            program   = loads(stdout)

            # Run QuickSpec on this sample
            data.update(timed_run([getenv('qsRunner'), program['runner']],
                                  program['code'],
                                  timeout_secs))

            # Analyse the result, if we have one
            results = None
            if data['success']:
                # conjectures_for_sample expects encoded sample but decoded eqs
                encoded    = eqs_in(cache[size][rep]['stdout'])
                decoded, _ = pipe(['decode'], dumps(encoded))
                results, _ = pipe(['conjectures_for_sample'], decoded,
                                  env={'SAMPLED_NAMES' : sample})

            data['conjectures'] = loads(results)
            cache[size][rep]    = data

    return cache
setup_cache.timeout = timeout_secs * len(params['rep']) * len(params['size'])

def track_data(cache):
    '''Store the generated data in our results, so we can inspect it and
    reproduce the executions/analysis.'''
    return cache

# Benchmark functions

def track_conjectures(cache, rep, size):
    '''All of the conjectures we wanted to find.'''
    return len(cached(cache, size, rep, 'conjectures', 'wanted'))

def track_conjectured_equations(cache, rep, size):
    '''All of the wanted conjectures which were equations.'''
    return sum(map(lambda c: len(c['equation']),
                   cached(cache, size, rep, 'conjectures', 'wanted')))

def track_equations(cache, rep, size):
    return len(eqs_in(cached(cache, size, rep, 'stdout')))

def track_precision(cache, rep, size):
    prec = cached(cache, rep, size, 'conjectures', 'precision')
    return prec if prec else 0

def track_recall(cache, rep, size):
    return cached(cache, rep, size, 'conjectures', 'recall')

def track_time(cache, rep, size):
    return cached(cache, size, rep, 'time')

# Assign parameters to benchmarks

for f in (track_conjectures, track_conjectured_equations, track_equations,
          track_precision, track_recall, track_time):
    for attr in attrs:
        setattr(f, attr, attrs[attr])
