from json import loads
from os   import getenv

parameters   = loads(getenv('parameters'))
repetitions  = parameters['repetitions']
timeout_secs = parameters['timeout_secs']
max_size     = parameters['max_size']
reps         = range(0, repetitions)
sizes        = range(1, max_size + 1)
