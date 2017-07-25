# Benchmark QuickSpec on the theories stored in benchmarks/

from json       import dumps as jdumps, loads as jloads
from os         import chmod, getenv
from parameters import repetitions, timeout_secs
from sexpdata   import loads as sloads, dumps as sdumps
from stat       import S_IRWXU, S_IRWXG, S_IRWXO
from util       import cached, eqs_in, generate_cache, pipe, sort, TempDir, timed_run

files  = jloads(getenv('theoryFiles'))
truths = jloads(getenv('theoryTruths'))
args   = {
    'rep'    : range(0, repetitions),
    'theory' : list(set(jloads(getenv('theoryFiles' )).keys() + \
                        jloads(getenv('theoryTruths')).keys()))
}

# Tells asv how to run the benchmarks
attrs = {
    'repeat'      : 1,
    'number'      : 1,
    'params'      : reduce(lambda x, y: x + (y,),
                           [args[name] for name in sort(args.keys())],
                           ()),
    'param_names' : sort(args.keys())
}

def setup_cache():
    '''Run all repetitions on all theories up-front, to avoid expensive
    re-running of tools.'''

    def readFiles(files):
        '''Turns a dictionary of filenames into a dictionary of file content.'''
        result = {}
        for theory in files:
            with open(files[theory], 'r') as f:
                result[theory] = f.read()
        return result

    # This data is specific to a theory, but not any particular run. For example
    # it includes the ground truth for that theory, but not the time taken by a
    # run
    data = {}
    for theory in args['theory']:
        # TODO: We can speed this up if we use nix-build to make the package
        # (annotation should be fine as-is). That way, it will all be cached,
        # and re-used as long as the theory file and TIP tools remain unchanged.
        thy = {
            'theory'      : theory,
            'content'     : readFiles(files )[theory],
            'conjectures' : readFiles(truths)[theory]
        }

        # Translate this theory into Haskell and extract type, arity, etc. info
        with TempDir() as out_dir:
            chmod(out_dir, S_IRWXU | S_IRWXG | S_IRWXO)
            env        = {'OUT_DIR' : out_dir}
            ann_out, _ = pipe([getenv('qsStandaloneMkPkg')],
                              thy['content'],
                              env=env)

            annotated  = None
            with open(ann_out.strip(), 'r') as f:
                annotated = jloads(f.read())

                # Make a Haskell program to explore this theory with QuickSpec
                setup_out, _ = pipe([getenv('qsStandaloneSetup')],
                                    jdumps(annotated),
                                    env=env)
                setup        = jloads(setup_out)

                # Build the environment (GHC with all the right packages)
                env, _      = pipe(['nix-build', '-E', setup['env']], env=env)

                thy['env']  = {'PATH' : env.strip() + '/bin:' + getenv('PATH')}
                thy['cmd']  = [getenv('qsStandaloneRunner'), setup['runner']]
                thy['code'] = setup['code']

        data[theory] = thy

    def gen(theory, rep):
        '''Performs a single repetition of a single theory.'''
        thy    = data[theory]
        result = {'theory' : theory}

        result.update(timed_run(thy['cmd'], thy['code'], timeout_secs,
                                env=thy['env']))

        result['analysis'] = None
        if result['success']:
            # Discard "Depth" lines, since they're just progress info
            eqs       = map(jloads, filter(lambda l: not l.startswith('Depth') \
                                                     and l.strip(),
                                           result['stdout'].split('\n')))

            out, _ = pipe(['precision_recall_eqs'], jdumps(eqs),
                          env={'GROUND_TRUTH' : truths[theory],
                               'TRUTH_SOURCE' : truths[theory]})

            result['analysis'] = jloads(out)

        return result

    # Run all repetitions of all theories
    result = generate_cache(args['theory'], gen)

    # Merge in the theory-specific data once, rather than copying for each run
    for theory in data:
        result[theory].update(data[theory])

    return result

setup_cache.timeout = max(3600,
                          timeout_secs * len(args['rep']) * len(args['theory']))

def track_data(cache):
    '''A dummy benchmark which spits out the raw data, for archiving.'''
    return cache

# Benchmarks

def track_conjectures(cache, theory):
    sexps = sloads('(\n{0}\n)'.format(cache[theory]['conjectures']))
    return len(sexps)

def track_equations(cache, rep, theory):
    return len(eqs_in(cached(cache, theory, rep, 'stdout')))

def track_precision(cache, rep, theory):
    return cached(cache, theory, rep, 'analysis', 'precision')

def track_recall(cache, rep, theory):
    return cached(cache, theory, rep, 'analysis', 'recall')

def track_time(cache, rep, theory):
    return cached(cache, theory, rep, 'time')

# Assign parameters to benchmarks

for f in (track_conjectures, track_equations, track_precision, track_recall,
          track_time):
    for attr in attrs:
        setattr(f, attr, attrs[attr])

# The available conjectures (ground truth) doesn't change across reps, so only
# track it per theory
track_conjectures.params      = (args['theory'],)
track_conjectures.param_names = ['theory']
