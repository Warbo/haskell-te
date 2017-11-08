#!/usr/bin/env python
from json import loads
from sys  import stdin

def dedupe(l):
    result = []
    for x in l:
        if x not in result:
            result += [x]
    return result

def names(expr):
    def go(x):
        return {
            'constant'    : lambda: [x['symbol']],
            'variable'    : lambda: [],
            'application' : lambda: go(x['lhs']) + go(x['rhs'])
        }[x['role']]()
    return go(expr)

def varsOf(lhs, rhs):
    def go(x):
        return {
            'constant'    : lambda: [],
            'variable'    : lambda: [x],
            'application' : lambda: go(x['lhs']) + go(x['rhs'])
        }[x['role']]()
    return dedupe(go(lhs) + go(rhs))

def wrap(vs, expr):
    '''Wraps the given expression in parentheses if it's an application.'''
    return ('({0})' if expr['role'] == 'application' else '{0}').format(
        render(vs, expr))

# Read in all equations
eqs = loads(stdin.read())

# Pick a symbol for variables which doesn't clash with any constant name
syms   = dedupe(reduce(lambda r, eq: r + names(eq['lhs']) + names(eq['rhs']),
                       eqs,
                       []))
varPre = 'v'
while any([s.startswith(varPre) for s in syms]):
    varPre += 'v'

def render(vs, expr):
    '''Render an expression to a string, numbering variables based on vs.'''
    return {
        'constant'    : lambda: expr['symbol'],
        'variable'    : lambda: varPre + str(vs.index(expr)),
        'application' : lambda: '{0} {1}'.format(wrap(vs, expr['lhs']),
                                                 wrap(vs, expr['rhs']))
    }[expr['role']]()

for eq in eqs:
    vs = varsOf(eq['lhs'], eq['rhs'])
    print('{0} ~= {1}'.format(render(vs, eq['lhs']), render(vs, eq['rhs'])))
