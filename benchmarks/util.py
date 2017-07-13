from os         import getpgid, killpg, setsid
from signal     import SIGTERM
from subprocess import check_output, PIPE, Popen
from threading  import Thread
from timeit     import default_timer

def time(f):
    '''Run function 'f' and return its result, and the time it took to run (in
    seconds).'''
    start  = default_timer()
    result = f()
    end    = default_timer()
    return (result, end - start)

def pipe(cmd, stdin=None, timeout=None):
    '''Runs 'stdin' through 'cmd' and returns stdout. Like Popen.communicate()
    but allows a timeout.'''
    # setsid puts the subprocess in its own process group, rather than the group
    # containing this Python process
    proc          = Popen(cmd, stdin=PIPE if stdin else None, stdout=PIPE,
                          preexec_fn=setsid)
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

def timed_run(cmd, stdin, timeout=None):
    '''Run the given command+args, for at most timeout_secs. Returns stdout,
    wall-clock time taken and success/fail depending whether it timed out.'''
    result, secs   = time(lambda *_: pipe(cmd, stdin, timeout))
    stdout, killed = result

    return {
        'stdout'  : stdout,
        'time'    : secs,
        'success' : not killed
    }

def cached(cache, size, rep):
    result = cache[size][rep]
    if result['success']:
        return result
    raise Exception('Repetition {0} of size {1} failed'.format(rep, size))

def sort(l):
    l.sort()
    return l
