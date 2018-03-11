from json import loads
from os   import getenv

parameters    = loads(getenv('parameters'))
repetitions   = parameters['repetitions']
timeout_secs  = parameters['timeout_secs']
max_size      = parameters['max_size']
specific_reps = parameters['specific_reps']
reps          = range(0, repetitions) if specific_reps == [] else specific_reps
sizes         = range(1, max_size + 1)
