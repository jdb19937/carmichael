"""Sortie A5, batch 2: the Scales tuple (Lean: structure Scales).
MM_DB=sorties/a5.mm python3 tools/gen/a5_sc.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1lib
from tm import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

XPS = '( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )'
V1 = '( 1st ` V )'
V2 = '( 2nd ` V )'
V11 = '( 1st ` %s )' % V1
V12 = '( 2nd ` %s )' % V1
Z = '( 1st ` %s )' % V11
WW = '( 2nd ` %s )' % V11
Y = '( 1st ` %s )' % V12
T = '( 2nd ` %s )' % V12
IW = '<. <. %s , %s >. , <. %s , %s >. >.' % (Z, WW, Y, T)
TUP = '<. %s , %s >.' % (IW, V2)
P = 'V e. Scales'


def prologue(w):
    st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (P, f))
    bi = w.s([w.inst('df-scales')], 'eleq2i', '( V e. Scales <-> V e. %s )' % XPS)
    xp = st([st([], 'id', P), st([bi], 'a1i', '( V e. Scales <-> V e. %s )' % XPS)],
            'mpbid', 'V e. %s' % XPS)
    x1 = st([xp, w.inst('xp1st')], 'syl', '%s e. ( ( NN X. NN0 ) X. ( NN X. NN0 ) )' % V1)
    x11 = st([x1, w.inst('xp1st')], 'syl', '%s e. ( NN X. NN0 )' % V11)
    x12 = st([x1, w.inst('xp2nd')], 'syl', '%s e. ( NN X. NN0 )' % V12)
    return st, xp, x1, x11, x12


# --------------------------------------------------------------- scalesiw
w = W('scalesiw', 'The window argument of a tuple of scales (Lean: the first four fields of Scales).')
st, xp, x1, x11, x12 = prologue(w)
e11 = st([x11, w.inst('1st2nd2')], 'syl', '%s = <. %s , %s >.' % (V11, Z, WW))
e12 = st([x12, w.inst('1st2nd2')], 'syl', '%s = <. %s , %s >.' % (V12, Y, T))
e1 = st([x1, w.inst('1st2nd2')], 'syl', '%s = <. %s , %s >.' % (V1, V11, V12))
op = w.s([e11, e12], 'opeq12d', '( %s -> <. %s , %s >. = %s )' % (P, V11, V12, IW))
w.qed([e1, op], 'eqtrd', '( %s -> %s = %s )' % (P, V1, IW))
run(w)

# --------------------------------------------------------------- scalestup
w = W('scalestup', 'The five components of a tuple of scales, and the tuple itself (Lean: structure Scales).')
st, xp, x1, x11, x12 = prologue(w)
zz = st([x11, w.inst('xp1st')], 'syl', '%s e. NN' % Z)
ww = st([x11, w.inst('xp2nd')], 'syl', '%s e. NN0' % WW)
yy = st([x12, w.inst('xp1st')], 'syl', '%s e. NN' % Y)
tt = st([x12, w.inst('xp2nd')], 'syl', '%s e. NN0' % T)
hh = st([xp, w.inst('xp2nd')], 'syl', '%s e. NN0' % V2)
ev = st([xp, w.inst('1st2nd2')], 'syl', 'V = <. %s , %s >.' % (V1, V2))
iw = st([], 'scalesiw', '%s = %s' % (V1, IW))
op = w.s([iw], 'opeq1d', '( %s -> <. %s , %s >. = %s )' % (P, V1, V2, TUP))
tup = st([ev, op], 'eqtrd', 'V = %s' % TUP)
w.qed([st([zz, ww], 'jca', '( %s e. NN /\\ %s e. NN0 )' % (Z, WW)),
       st([yy, tt], 'jca', '( %s e. NN /\\ %s e. NN0 )' % (Y, T)),
       st([hh, tup], 'jca', '( %s e. NN0 /\\ V = %s )' % (V2, TUP))], '3jca',
      '( %s -> ( ( %s e. NN /\\ %s e. NN0 ) /\\ ( %s e. NN /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ V = %s ) ) )'
      % (P, Z, WW, Y, T, V2, TUP))
run(w)
