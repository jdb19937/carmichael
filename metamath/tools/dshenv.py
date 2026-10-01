"""Sortie DSH: Z6's macro environment at the half-line parameters.
Imports z6clib (z6blib, z6alib) and rewrites every string global and every STATEMENTS value of those
modules by dshlib.dsub, so that module lambdas (GR, MRr, ...) and constants (A5B, CL, ...) produce the
half-line text; STATEMENTS also gets the dshX keys (trstmt).  Generator copies tools/gen/dsh_b_*.py,
dsh_c_*.py do `from dshenv import *`."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z6clib, z6blib, z6alib
import dshlib


def _fix(mod):
    for k, v in list(vars(mod).items()):
        if isinstance(v, str) and not k.startswith('__'):
            setattr(mod, k, dshlib.dsub(v))
    st = getattr(mod, 'STATEMENTS', None)
    if isinstance(st, dict):
        for k in list(st):
            st[k] = dshlib.dsub(st[k])


for _m in (z6alib, z6blib, z6clib):
    _fix(_m)
for _x in dshlib.TR:
    z6alib.STATEMENTS['dsh' + _x] = dshlib.trstmt(_x)
for _k, _v in dshlib.STATEMENTS.items():
    z6alib.STATEMENTS[_k] = _v
from z6clib import *
from z6clib import STATEMENTS, HYPS
for _k, _v in list(globals().items()):
    if isinstance(_v, str) and not _k.startswith('__'):
        globals()[_k] = dshlib.dsub(_v)
