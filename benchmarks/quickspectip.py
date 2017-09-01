from util import tip_benchmarks, tip_cache

setup_cache = tip_cache('quickspecTip')

# Generate benchmark functions and add them to this module
locals().update(tip_benchmarks())
