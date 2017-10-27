from json import loads
from os   import getenv

parameters   = loads(getenv('parameters'))
repetitions  = parameters['repetitions']
timeout_secs = parameters['timeout_secs']
max_size     = parameters['max_size']
