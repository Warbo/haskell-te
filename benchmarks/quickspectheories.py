# Benchmark QuickSpec on the theories stored in benchmarks/

from json       import dumps, loads
from os         import chmod, getenv
from parameters import repetitions, timeout_secs
from stat       import S_IRWXU, S_IRWXG, S_IRWXO
from util       import eqs_in, generate_cache, pipe, TempDir, timed_run

theoryFiles = loads(getenv('theoryFiles'))

config = {
    'theory' : theoryFiles.keys()
}

def theory_params(theory):
    '''Generate environment for exploring the given theory.'''
    # Fetch this theory
    params = {'theory' : theory}

    # TODO: We can speed this up if we use nix-store to add theoryFiles[theory]
    # to the Nix store (which gives us a content-based hash), then use nix-build
    # to make the package (annotation should be fine as-is). This way, it will
    # all be cached, and re-used as long as the theory file and TIP tools remain
    # unchanged.
    content = ''
    with open(theoryFiles[theory], 'r') as f:
        content = f.read()
    params['content'] = content

    # Translate this theory into Haskell and extract type, arity, etc. info
    with TempDir() as out_dir:
        chmod(out_dir, S_IRWXU | S_IRWXG | S_IRWXO)
        env        = {'OUT_DIR' : out_dir}
        ann_out, _ = pipe([getenv('qsStandaloneMkPkg')], content, env=env)

        annotated  = None
        with open(ann_out.strip(), 'r') as f:
            annotated = loads(f.read())
        params['annotated'] = annotated

        # Make a Haskell program to explore this theory with QuickSpec
        setup_out, _ = pipe([getenv('qsStandaloneSetup')],
                            dumps(annotated),
                            env=env)
        setup        = loads(setup_out)

        # Build the environment (GHC with all the right packages)
        env, _ = pipe(['nix-build', '-E', setup['env']], env=env)

        params['env']  = {'PATH' : env.strip() + '/bin:' + getenv('PATH')}
        params['cmd']  = [getenv('qsStandaloneRunner'), setup['runner']]
        params['code'] = setup['code']

    return params

def setup_cache():
    '''Run all repetitions on all theories up-front, to avoid expensive
    re-running of tools.'''
    data = {}
    for theory in config['theory']:
        data[theory] = theory_params(theory)

    def gen(theory, rep):
        this = data[theory]
        this.update(timed_run(this['cmd'], this['code'], timeout_secs,
                              env=this['env']))
        return this

    return generate_cache(config['theory'], gen)

def track_data(cache):
    '''A dummy benchmark which spits out the raw data, for archiving.'''
    return cache

# Benchmarks

def track_equations(cache, rep, theory):
    return len(eqs_in(cached(cache, theory, rep, 'stdout')))
