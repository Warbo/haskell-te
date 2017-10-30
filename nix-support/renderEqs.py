#!/usr/bin/env python
from json import loads
from sys  import stdin

def wrap(expr):
    '''Wraps the given expression in parentheses if it's an application.'''
    return ('({0})' if expr['role'] == 'application' else '{0}').format(
        render(expr))

def render(expr):
    '''Render a single expression to a string.'''
    return {
        'constant'    : lambda: expr['symbol'],
        'variable'    : lambda: (filter(lambda c: c.isupper(), expr['type']) +
                                 str(expr['id'])).lower(),
        'application' : lambda: '{0} {1}'.format(wrap(expr['lhs']),
                                                 wrap(expr['rhs']))
    }[expr['role']]()

for eq in loads(stdin.read()):
    print('{0} ~= {1}'.format(render(eq['lhs']), render(eq['rhs'])))
