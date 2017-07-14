# Benchmark QuickSpec on the theories stored in benchmarks/

from json       import dumps, loads
from os         import getenv
from parameters import repetitions, timeout_secs
from util       import TempDir

params = {
    'theory' : ['list-full', 'nat-full', 'nat-simple']
}

theoryFiles = loads(getenv('theoryFiles'))

def foosetup_cache():
    '''Run all repetitions on all theories up-front, to avoid expensive
    re-running of tools.'''
    def gen(theory, rep):
        # Fetch this theory
        theory_content = ''
        with open(theoryFiles[theory], 'r') as f:
            theory_content = f.read()

        # Convert the theory to a suitable QuickSpec program
        with TempDir() as out_dir:
            annotated, _ = pipe([getenv('qsStandaloneMkPkg')], theory_content,
                                env={'OUT_DIR' : out_dir})
            annotated_content = None
            with open(annotated.strip(), 'r') as f:
                annotated_content = loads(f.read())

            stdout,    _ = pipe([getenv('qsStandaloneSetup')],
                                dumps(annotated_content),
                                env={'OUT_DIR' : out_dir})
            program      = loads(stdout)

            import sys
            sys.stderr.write(repr(program))
            sys.exit(1)

        # Run QuickSpec on this theory
        data.update(timed_run([getenv('qsStandaloneRunner'), program['runner']],
                              program['code'],
                              timeout_secs))


    return generate_cache(params['theory'], gen)
