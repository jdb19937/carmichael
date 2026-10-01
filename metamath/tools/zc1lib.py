"""Sortie ZC1: helpers and the frozen statements (C11, the zero-count layer,
SmallDiskZeroCount, the zeroDiskFinset layer).  Built on tools/c10lib.py.

    python3 tools/zc1lib.py print     # the frozen table
    MM_DB=sorties/zc1.mm python3 tools/zc1lib.py check [LABEL...]   # grammar check (mmatch)
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from c10lib import *
import c10lib as _c10


def stmt(label):
    """the assertion of LABEL from sorties/zc1.mm or carmichael.mm, without |-"""
    for fn in ('sorties/zc1.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def patch(*mods):
    for m in mods:
        m.stmt = stmt


patch(_c10)

# ---- objects ---------------------------------------------------------------------
HOLF = lambda F, D: '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)
R2524 = '( ; 2 5 / ; 2 4 )'
L25 = '( log ` %s )' % R2524
NX = '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'
E = '( N DChrLF X )'
E1 = '( 1 DChrLF ( 0g ` ( DChr ` 1 ) ) )'
ETA = '( z e. %s |-> sum_ k e. NN ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) ) )' % HP0
GF = '( z e. %s |-> ( 1 - ( 2 ^c ( 1 - z ) ) ) )' % HP0


def CT(t):
    return '( 2 + ( _i x. %s ) )' % t


def RCT(t):
    return '( ( ( 1 / 4 ) + ( _i x. ( %s - 3 ) ) ) crect ( ( ; 1 5 / 4 ) + ( _i x. ( %s + 3 ) ) ) )' % (t, t)


def ZS(F, t, r=R138):
    return '{ r e. %s | ( %s ` r ) = 0 }' % (SQ(CT(t), r), F)


def HO(F, q='q'):
    return '( %s holord %s )' % (F, q)


def MASS(Z, F, q='q'):
    return 'sum_ %s e. %s %s' % (q, Z, HO(F, q))


def JW(B, M):
    """the four-strip mass bound"""
    return '( ( 4 x. ( log ` ( %s / %s ) ) ) / %s )' % (B, M, L25)


def BOX(s, t):
    return '( ( %s + ( _i x. -u %s ) ) crect ( 1 + ( _i x. %s ) ) )' % (s, t, t)


def ZF(F, s, t):
    """zeroFinset: the zeros off 1 in the box [ s , 1 ] x [ -t , t ]"""
    return '{ r e. %s | ( r =/= 1 /\\ ( %s ` r ) = 0 ) }' % (BOX(s, t), F)


def ZC(F, s, t):
    """zeroCountBox"""
    return MASS(ZF(F, s, t), F)


# ---- frozen statements -------------------------------------------------------------
S = {}
JH = '( ( %s /\\ T e. RR ) /\\ ( B e. RR /\\ A. x e. %s ( abs ` ( F ` x ) ) <_ B ) /\\ ( M e. RR+ /\\ M <_ ( abs ` ( F ` %s ) ) ) )' % (
    HOLF('F', HP0), SQ(CT('T'), R74), CT('T'))
ZQF = '{ r e. ( %s crect %s ) | ( F ` r ) = 0 }' % (QA('T'), QB('T'))
S['jenstrip'] = '( %s -> ( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN /\\ ( %s x. %s ) <_ ( log ` ( B / M ) ) ) )' % (
    JH, ZQF, ZQF, MASS(ZQF, 'F'), L25)
JQH = ('( ( %s /\\ T e. RR ) /\\ ( B e. RR /\\ A. x e. %s ( abs ` ( F ` x ) ) <_ B ) /\\ '
       '( M e. RR+ /\\ A. t e. ( ( T - 2 ) [,] ( T + 2 ) ) M <_ ( abs ` ( F ` %s ) ) ) )') % (HOLF('F', HP0), RCT('T'), CT('t'))
ZS13 = ZS('F', 'T')
S['jensq13'] = '( %s -> ( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN /\\ %s <_ %s ) )' % (JQH, ZS13, ZS13, MASS(ZS13, 'F'), JW('B', 'M'))

ORDER = list(S)


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'zc1gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'zc1gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=zc1gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::zc1gc%s.1 |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


GENS = ['zc1_a', 'zc1_b', 'zc1_c', 'zc1_d', 'zc1_e', 'zc1_f', 'zc1_g', 'zc1_h', 'zc1_i', 'zc1_j', 'zc1_k', 'zc1_l', 'zc1_m',
        'zc1_n', 'zc1_o', 'zc1_p', 'zc1_q', 'zc1_r', 'zc1_s', 'zc1_t', 'zc1_v', 'zc1_w', 'zc1_x', 'zc1_y', 'zc1_z', 'zc1_zz']


def load_all():
    """import every generator so that S holds all frozen statements (the generators add their own)"""
    import importlib
    saved = sys.argv[:]
    sys.argv = sys.argv[:1] + ['-none-']
    try:
        for g in GENS:
            importlib.import_module(g)
    finally:
        sys.argv = saved
    return importlib.import_module('zc1lib').S


if __name__ == '__main__':
    if 'print' in sys.argv or 'check' in sys.argv:
        S = load_all()
        ORDER = list(S)
    if 'print' in sys.argv:
        for lab in ORDER:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)


def fcc(w, ante, hol, F, D, x, xin):
    """( ante -> ( F ` x ) e. CC ) from hol : ( ante -> HOL(F, D) ) and xin : ( ante -> x e. D )"""
    cn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ante, F, D))
    ff = w.s([cn, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (ante, F, D))
    return w.s([ff, xin], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (ante, F, x))
