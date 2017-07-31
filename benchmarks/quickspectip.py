from json       import dumps, loads
from os         import getenv
from parameters import repetitions, timeout_secs
from util       import cached, eqs_in, generate_cache, pipe, set_attributes, \
                       sort, timed_run

# Benchmark parameters. Will appear in alphabetical order as arguments, after
# 'cache'
args = {
    'rep'  : range(0, repetitions),
    'size' : range(1, 20),
}

def setup_cache():
    '''Running a TE tool is expensive, so we only want to run each sample once.
    By returning all of the results from setup_cache, each benchmark can pick
    out the values it cares about, without having to re-run anything.
    The returned value will appear as the first argument to each benchmark.'''
    def gen(size, rep):
        data = {}

        # Choose a sample, and generate QuickSpec code for exploring it
        sample, _      = pipe(['choose_sample', str(size), str(rep)])
        data['sample'] = sample

        stdout, _ = pipe([getenv('qsTipSetup')], sample)
        program   = loads(stdout)

        # Run QuickSpec on this sample
        data.update(timed_run([getenv('qsTipRunner'), program['runner']],
                              program['code'],
                              timeout_secs))

        # Analyse the result, if we have one
        results = 'null'
        if data['success']:
            # conjectures_for_sample expects encoded sample but decoded eqs
            encoded    = eqs_in(data['stdout'])
            decoded, _ = pipe(['decode'], dumps(encoded))
            results, _ = pipe(['conjectures_for_sample'], decoded,
                              env={'SAMPLED_NAMES' : sample})

        data['conjectures'] = loads(results)
        return data

    return generate_cache(args['size'], gen)
setup_cache.timeout = max(3600,
                          timeout_secs * len(args['rep']) * len(args['size']))

def track_data(cache, _):
    '''Store the generated data in our results, so we can inspect it and
    reproduce the executions/analysis.'''
    return cache

track_data.repeat      = 1
track_data.number      = 1
track_data.params      = (["dummy"],)
track_data.param_names = ["dummy"]

# Benchmark functions

def track_conjectures(cache, rep, size):
    '''All of the conjectures we wanted to find.'''
    return len(cached(cache, size, rep, 'conjectures', 'wanted'))

def track_conjectured_equations(cache, rep, size):
    '''All of the wanted conjectures which were equations. QuickSpec can only
    find equations, so this is our theoretical maximum.'''
    return sum(map(lambda c: len(c['equation']),
                   cached(cache, size, rep, 'conjectures', 'wanted')))

def track_equations(cache, rep, size):
    '''How many equations we found (in total).'''
    return len(eqs_in(cached(cache, size, rep, 'stdout')))

def track_precision(cache, rep, size):
    '''Proportion of found equations which were wanted.'''
    prec = cached(cache, size, rep, 'conjectures', 'precision')
    return prec if prec else 0

def track_recall(cache, rep, size):
    '''Proportion of wanted conjectures which were found.'''
    return cached(cache, size, rep, 'conjectures', 'recall')

def track_time(cache, rep, size):
    '''Time taken to explore (excludes setup and analysis).'''
    return cached(cache, size, rep, 'time')

# Tells asv how to run the benchmarks

set_attributes([track_conjectures, track_conjectured_equations, track_equations,
                track_precision, track_recall, track_time],
               {
                   'repeat'      : 1,
                   'number'      : 1,
                   'params'      : reduce(lambda x, y: x + (y,),
                                          [args[name] for name in sort(args.keys())],
                                          ()),
                   'param_names' : sort(args.keys())
               })
