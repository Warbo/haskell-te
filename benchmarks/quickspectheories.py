# Benchmark QuickSpec on the theories stored in benchmarks/

from json       import dumps as jdumps, loads as jloads
from os         import chmod, getenv
from parameters import repetitions, timeout_secs
from sexpdata   import loads as sloads, dumps as sdumps
from stat       import S_IRWXU, S_IRWXG, S_IRWXO
from util       import cached, generate_cache, pipe, reps, set_attributes, theories, timed_run

def setup_cache():
    '''Run all repetitions on all theories up-front, to avoid expensive
    re-running of tools.'''

    data = jloads(getenv('qsStandalone'))

    def gen(theory, rep):
        '''Performs a single repetition of a single theory.'''
        thy    = data[theory]
        result = {'theory' : theory}

        result.update(timed_run([thy['runner']], '', timeout_secs))

        result['analysis'] = None
        if result['success']:
            analysis           = pipe([thy['analyser']], result['stdout'])
            result['analysis'] = jloads(analysis['stdout'])

        return result

    # Run all repetitions of all theories
    result = generate_cache(data.keys(), gen)

    # Merge in the theory-specific data once, rather than copying for each run
    for theory in data:
        result[theory].update(data[theory])

    return result

setup_cache.timeout = max(3600, timeout_secs * len(reps()) * len(theories()))

def track_data(cache, _):
    '''A dummy benchmark which spits out the raw data, for archiving.'''
    return cache
track_data.repeat      = 1
track_data.number      = 1
track_data.params      = (["dummy"],)
track_data.param_names = ["dummy"]


# Benchmarks

def track_ground_truth(cache, theory):
    sexps = sloads('(\n{0}\n)'.format(cache[theory]['ground_truth']))
    return len(sexps)

def track_equations(cache, rep, theory):
    return len(jloads(cached(cache, theory, rep, 'stdout')))

def track_precision(cache, rep, theory):
    return cached(cache, theory, rep, 'analysis', 'precision')

def track_recall(cache, rep, theory):
    return cached(cache, theory, rep, 'analysis', 'recall')

def track_time(cache, rep, theory):
    return cached(cache, theory, rep, 'time')

# Assign parameters to benchmarks

set_attributes([track_ground_truth, track_equations, track_precision,
                track_recall, track_time],
               {
                   'repeat'      : 1,
                   'number'      : 1,
                   'params'      : (reps(), theories()),
                   'param_names' : ['rep', 'theory']
               })

# The ground truth doesn't change across reps, so only track it per theory
track_ground_truth.params      = (theories())
track_ground_truth.param_names = ['theory']
