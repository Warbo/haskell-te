# See "Writing benchmarks" in the asv docs for more information.

from json       import loads
from os         import getenv
from subprocess import check_output, PIPE, Popen
from timeit     import default_timer

class QuickSpec:

    param_names = ['size',      'rep']
    params      = (range(1, 3), range(0, 2))
    #timeout     = 3600          # One hour
    timer       = default_timer # Use wall-clock time, to measure subprocesses

    def setup(self, size, rep):
        '''Choose a sample and generate Haskell code to explore it.'''
        data = loads(check_output([getenv('qsSetup'), str(size), str(rep)]))

        self.quickspec = lambda *_: Popen(
            [getenv('qsRunner'), data['runner']],
            stdin=PIPE, stdout=PIPE
        ).communicate(data['code'])

    def time_run(self, size, rep):
        '''Run QuickSpec and discard the result, so we can time it.'''
        self.quickspec()

    def track_precision(self, size, rep):
        '''Run QuickSpec and calculate precision of the result.'''
        import sys
        sys.stderr.write(repr(self.quickspec()))
