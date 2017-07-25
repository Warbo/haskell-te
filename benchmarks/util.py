from json       import loads
from os         import environ, getpgid, killpg, setsid
from parameters import repetitions, timeout_secs
from shutil     import rmtree
from signal     import SIGTERM
from subprocess import check_output, PIPE, Popen
from tempfile   import mkdtemp
from threading  import Thread
from timeit     import default_timer

def time(f):
    '''Run function 'f' and return its result, and the time it took to run (in
    seconds).'''
    start  = default_timer()
    result = f()
    end    = default_timer()
    return (result, end - start)

def pipe(cmd, stdin=None, timeout=None, env=None):
    '''Runs 'stdin' through 'cmd' and returns stdout. Like Popen.communicate()
    but allows a timeout.'''

    # Extend the current environment, if requested
    extra_env = None
    if env:
        extra_env = environ.copy()
        for var in env:
            extra_env[var] = env[var]

    # setsid puts the subprocess in its own process group, rather than the group
    # containing this Python process
    killed = None
    proc   = Popen(cmd, stdin=PIPE if stdin else None, stdout=PIPE,
                   preexec_fn=setsid, env=extra_env)
    try:
        stdout        = []
        stdout_thread = Thread(target=lambda *_: stdout.append(proc.stdout.read()),
                               args=())
        stdout_thread.setDaemon(True)
        stdout_thread.start()

        if stdin:
            try:
                proc.stdin.write(stdin)
            except IOError as e:
                if e.errno != errno.EPIPE:
                    raise
            proc.stdin.close()

        stdout_thread.join(timeout)
        killed = stdout_thread.isAlive()  # True iff we timed out
        if killed:
            # Kill the process group, which will include all children
            killpg(getpgid(proc.pid), SIGTERM)

        proc.wait()  # Reaps zombies

        return (stdout[0] if stdout else '', killed)
    finally:
        if killed is None:
            killpg(getpgid(proc.pid), SIGTERM)

def timed_run(cmd, stdin, timeout=None, env=None):
    '''Run the given command+args, for at most timeout_secs. Returns stdout,
    wall-clock time taken and success/fail depending whether it timed out.'''
    result, secs   = time(lambda *_: pipe(cmd, stdin, timeout, env=env))
    stdout, killed = result

    return {
        'stdout'  : stdout,
        'time'    : secs,
        'success' : not killed
    }

def cached(cache, size, rep, *path):
    '''Look up the given data from the cache. If this run failed, an exception
    is thrown (so we avoid looking up data that wasn't generated).'''
    result = cache[size]['reps'][rep]
    if result['success']:
        for key in path:
            result = result[key]
        return result
    raise Exception('Repetition {0} of size {1} failed'.format(rep, size))

def sort(l):
    '''Built-in sort is in-place; this will return the sorted list too.'''
    l.sort()
    return l

def eqs_in(stdout):
    '''Extracts any equations present in the given stdout.'''
    def keep_line(l):
        return l.strip() and not l.startswith('Depth')

    return map(loads, filter(keep_line, stdout.split('\n')))

def generate_cache(theories, f):
    '''Call the function 'f' for each repetition of each given theory, return an
    accumulated dictionary of the results.'''
    cache = {}
    for theory in theories:
        reps          = range(0, repetitions)
        cache[theory] = {'reps': [{} for _ in reps]}
        for rep in reps:
            data = {'rep': rep, 'timeout': timeout_secs}
            data.update(f(theory, rep))
            cache[theory]['reps'][rep] = data
    return cache

class TempDir(object):
    '''Context manager for using temp dirs in 'with' statements.'''
    def __enter__(self):
        self.name = mkdtemp()
        return self.name

    def __exit__(self, exc_type, exc_value, traceback):
        rmtree(self.name)
