from json         import loads, dumps
from os           import environ, getenv, getpgid, killpg, setsid
from parameters   import reps, sizes, timeout_secs
from signal       import SIGTERM
from subprocess32 import check_output, PIPE, Popen, TimeoutExpired
from sys          import exc_info
from tempfile     import mkdtemp
from threading    import Thread
from timeit       import default_timer

def time(f):
    '''Run function 'f' and return its result, and the time it took to run (in
    seconds).'''
    start  = default_timer()
    result = f()
    end    = default_timer()
    return (result, end - start)

def pipe(cmd, stdin=None, timeout=None, env=None):
    '''Runs 'stdin' through 'cmd' and returns stdout, stderr and whether we
    timed out.'''

    # Extend the current environment, if requested
    extra_env = None
    if env:
        extra_env = environ.copy()
        for var in env:
            extra_env[var] = env[var]

    # setsid puts the subprocess in its own process group, rather than the group
    # containing this Python process
    killed = None
    proc   = Popen(cmd, stdin=PIPE if stdin else None, stdout=PIPE, stderr=PIPE,
                   preexec_fn=setsid, env=extra_env)

    try:
        (stdout, stderr) = proc.communicate(input=stdin, timeout=timeout)
        result = {'stdout': stdout, 'stderr': stderr, 'killed': False}
    except TimeoutExpired:
        # Kill the process group, which will include all children
        killpg(getpgid(proc.pid), SIGTERM)
        result = {'stdout': None, 'stderr': None, 'killed': True}

    proc.wait()  # Reaps zombies

    return result

def timed_run(cmd, stdin, timeout=None, env=None):
    '''Run the given command+args, for at most timeout_secs. Returns stdout,
    wall-clock time taken and success/fail depending whether it timed out.'''
    result, secs = time(lambda *_: pipe(cmd, stdin, timeout, env=env))

    return {
        'stdout'  : result['stdout'],
        'stderr'  : result['stderr'],
        'time'    : secs,
        'success' : not result['killed']
    }

def cached(cache, theory, rep, *path):
    '''Look up the given data from the cache. If this run failed, an exception
    is thrown (so we avoid looking up data that wasn't generated).'''
    result = cache[theory]['reps'][rep]
    if result['success']:
        for key in path:
            result = result[key]
        return result
    raise Exception('Repetition {0} of theory {1} failed'.format(rep, theory))

def sort(l):
    '''Built-in sort is in-place; this will return the sorted list too.'''
    l.sort()
    return l

def generate_cache(theories, f):
    '''Call the function 'f' for each repetition of each given theory, return an
    accumulated dictionary of the results.'''
    cache = {}
    for theory in theories:
        cache[theory] = {'reps': {}}
        for rep in reps:
            data = {'rep': rep, 'timeout': timeout_secs}
            data.update(f(theory, rep))
            cache[theory]['reps'][rep] = data
    return cache

def set_attributes(funcs, attrs):
    for f in funcs:
        for attr in attrs:
            setattr(f, attr, attrs[attr])

def tip_benchmarks():
    benchmarks = {
        # Store the generated data in our results, so we can inspect it and
        # reproduce the executions/analysis.'''
        'track_data': lambda cache, _: cache,

        # Benchmark functions

        # All of the conjectures we wanted to find.
        'track_conjectures': lambda cache, rep, size:
            len(cached(cache, size, rep, 'wanted')),

        # All of the wanted conjectures which were equations. QuickSpec can only
        # find equations, so this is our theoretical maximum.
        'track_conjectured_equations': lambda cache, rep, size:
            sum(map(lambda c: len(c['equation']),
                    cached(cache, size, rep, 'wanted'))),

        # How many equations we found (in total).
        'track_equations': lambda cache, rep, size:
            len(loads(cached(cache, size, rep, 'stdout'))),

        # Proportion of found equations which were wanted.
        'track_precision': lambda cache, rep, size:
            cached(cache, size, rep, 'precision') or 0,

        # Proportion of wanted conjectures which were found.
        'track_recall': lambda cache, rep, size:
            cached(cache, size, rep, 'recall'),

        # Time taken to explore (excludes setup and analysis).
        'track_time': lambda cache, rep, size:
            cached(cache, size, rep, 'time')
    }

    # Tells asv how to run the benchmarks

    for name in benchmarks:
        benchmarks[name].func_name = name

    set_attributes(benchmarks.values(),
                   {
                       'repeat'      : 1,
                       'number'      : 1,
                       'params'      : reduce(lambda x, y: x + (y,),
                                              [reps, sizes],
                                              ()),
                       'param_names' : ['rep', 'size']
                   })

    # track_data isn't a "real" benchmark, so only do it once
    benchmarks['track_data'].repeat      = 1
    benchmarks['track_data'].number      = 1
    benchmarks['track_data'].params      = (["dummy"],)
    benchmarks['track_data'].param_names = ["dummy"]

    return benchmarks

def theories():
    '''The standalone theories we're benchmarking (nat-simple, etc.)'''
    return loads(getenv('qsStandalone')).keys()

tips = {
    'quickspecTip': loads(open(getenv('quickspecTip'), 'r').read())
}

def tip_cache(var_name):
    '''Running a TE tool is expensive, so we only want to run each sample once.
    By returning all of the results from setup_cache, each benchmark can pick
    out the values it cares about, without having to re-run anything.
    The returned value will appear as the first argument to each benchmark.'''
    def setup_cache():
        def gen(size, rep):
            cmds     = tips['quickspecTip'][str(size)][str(rep)]
            result   = timed_run([cmds['runner']], '', timeout=timeout_secs)
            analysis = {'analysed': False}
            with open(cmds['sampleFile'], 'r') as sampleFile:
                result['sample'] = filter(None, sampleFile.read().split('\n'))

            to_analyse = result['stdout'] if result['success'] else '[]'
            try:
                analysed = pipe([cmds['analyser']], to_analyse)['stdout']
                analysis = {'analysed': True}
            except:
                analysis = {'analysed':       False,
                            'analysis error': repr(exc_info())}

            if analysis['analysed']:
                try:
                    analysis = loads(analysed)
                    analysis['analysed'] = True
                except:
                    analysis = {'analysed':        False,
                                'analysis error':  repr(exc_info()),
                                'analysis stdout': analysed}
            return dict(result, **analysis)

        return generate_cache(sizes, gen)

    setup_cache.timeout = max(3600, timeout_secs * len(reps) * len(sizes))

    return setup_cache

def compose(f, g):
    return lambda x: f(g(x))
