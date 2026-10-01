"""Sortie C9, item 0: logdvbnd7 = logdvbnd with hollog's margin 1/8, so the
holomorphy hypothesis is SQ(C,7/4) C_ D (generated from c8_o.gen_logdvbnd
with three numerals changed)."""
import sys, os, inspect
sys.path.insert(0, os.path.dirname(__file__))
import c8_o
from c8_o import *

R74 = '( 7 / 4 )'


def build():
    src = inspect.getsource(c8_o.gen_logdvbnd)
    reps = [
        ("W('logdvbnd', 'The log-derivative bound: a function holomorphic on an open set containing the square of half-side 2 about",
         "W('logdvbnd7', 'The log-derivative bound: a function holomorphic on an open set containing the square of half-side ` 7 / 4 ` about"),
        ("R138, R38 = '( ; 1 3 / 8 )', '( 3 / 8 )'", "R138, R38 = '( ; 1 3 / 8 )', '( 1 / 8 )'"),
        ("SQ('C', '2')", "SQ('C', R74)"),
        ("SQA('C', '2')", "SQA('C', R74)"),
        ("SQB('C', '2')", "SQB('C', R74)"),
        ("lin.lineq(w, A0, X, '2',", "lin.lineq(w, A0, X, R74,"),
        ("'( %s -> ( _i x. %s ) = ( _i x. 2 ) )' % (A0, X)", "'( %s -> ( _i x. %s ) = ( _i x. %s ) )' % (A0, X, R74)"),
        ("'( %s -> ( %s + ( _i x. %s ) ) = ( 2 + ( _i x. 2 ) ) )' % (A0, X, X)", "'( %s -> ( %s + ( _i x. %s ) ) = ( %s + ( _i x. %s ) ) )' % (A0, X, X, R74, R74)"),
        ("assert '( %s -> %s )' % (A0, GOAL) == FS['logdvbnd']", "assert '( %s -> %s )' % (A0, GOAL) == FS['logdvbnd'].replace(SQ('C', '2'), SQ('C', R74))"),
        ("Lean ` norm_logDeriv_le_of_log_norm_bound ` , constant ` 1600 ` there; ~ hollog",
         "Lean ` norm_logDeriv_le_of_log_norm_bound ` , constant ` 1600 ` there; ~ logdvbnd with the margin ` 1 / 8 ` for ~ hollog ; ~ hollog"),
    ]
    for a, b in reps:
        assert src.count(a) >= 1, a
        src = src.replace(a, b)
    src = src.replace('def gen_logdvbnd(', 'def gen_logdvbnd7(')
    ns = dict(vars(c8_o))
    ns['R74'] = R74
    import c9lib
    ns['stmt'] = c9lib.stmt
    exec(src, ns)
    return ns['gen_logdvbnd7']


if __name__ == '__main__':
    build()()
