"""Sortie A4b, batch 2: the M algebra and the z facts of costPieces_bound.

M is the product ( ell2 ` n ) x. ( ell3 ` n ) , carried as its own variable
with the equation M = ( A x. B ) so that no certificate of tools/lin.py ever
needs degree three (A4b-blueprint.md section 1 item 1).

    MM_DB=sorties/a4b.mm python3 tools/gen/a4b_m.py [labels]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from a2lib import WH
from cl import Closure
from lin import linarith, nlinarith
import num

only = [a for a in sys.argv[1:] if not a.startswith('-')]
GENS = []
def gen(fn):
    GENS.append(fn); return fn
PH = 'ph'
def A(f): return '( ph -> %s )' % f


def mhyps(w):
    """A e. RR , 1 <_ A , B e. RR , 12 <_ B , M e. RR , M = ( A x. B )"""
    are = w.h('A e. RR'); a1 = w.h('1 <_ A')
    bre = w.h('B e. RR'); b12 = w.h('; 1 2 <_ B')
    mre = w.h('M e. RR'); meq = w.h('M = ( A x. B )')
    c = Closure(w, PH, {'A': ('RR', are), 'B': ('RR', bre), 'M': ('RR', mre)})
    return are, a1, bre, b12, mre, meq, c


@gen
def cbm12():
    w = WH('cbm12', 'The product of the iterated logarithms is at least twelve '
                    '(Lean AlgBudget.lean, ` hM ` of costPieces_bound).')
    are, a1, bre, b12, mre, meq, c = mhyps(w)
    nlinarith(w, PH, [a1, b12, meq], '; 1 2 <_ M', closure=c, name='qed')
    return w


@gen
def cbmb():
    w = WH('cbmb', 'The third iterated logarithm is at most the product '
                   '(Lean AlgBudget.lean, ` hstar ` of costPieces_bound).')
    are, a1, bre, b12, mre, meq, c = mhyps(w)
    nlinarith(w, PH, [a1, b12, meq], 'B <_ M', closure=c, name='qed')
    return w


@gen
def cbma():
    w = WH('cbma', 'Twelve times the second iterated logarithm is at most the product '
                   '(Lean AlgBudget.lean, ` h12l2 ` of costPieces_bound).')
    are, a1, bre, b12, mre, meq, c = mhyps(w)
    nlinarith(w, PH, [a1, b12, meq], '( ; 1 2 x. A ) <_ M', closure=c, name='qed')
    return w


def zhyps(w):
    cre = w.h('C e. RR'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    zre = w.h('Z e. RR'); zlo = w.h('( C x. M ) <_ Z')
    c = Closure(w, PH, {'C': ('RR', cre), 'M': ('RR', mre), 'Z': ('RR', zre)})
    return cre, c1000, mre, m12, zre, zlo, c


@gen
def cbz12():
    w = WH('cbz12', 'The first scale is at least twelve thousand at every windowed scale '
                    '(Lean AlgBudget.lean, ` htriple ` and ` hz12000 ` of costPieces_bound).')
    cre, c1000, mre, m12, zre, zlo, c = zhyps(w)
    nlinarith(w, PH, [c1000, m12, zlo], '; ; ; ; 1 2 0 0 0 <_ Z', closure=c, name='qed')
    return w


@gen
def cbmz():
    w = WH('cbmz', 'The product of the iterated logarithms is at most the first scale '
                   '(Lean AlgBudget.lean, ` hML ` of costPieces_bound).')
    cre, c1000, mre, m12, zre, zlo, c = zhyps(w)
    nlinarith(w, PH, [c1000, m12, zlo], 'M <_ Z', closure=c, name='qed')
    return w


@gen
def cblz():
    w = WH('cblz', 'The logarithm of the first scale is at most three times the third '
                   'iterated logarithm (Lean AlgBudget.lean, ` hlz ` of costPieces_bound).')
    cre = w.h('C e. RR'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
    are = w.h('A e. RR'); a1 = w.h('1 <_ A')
    bre = w.h('B e. RR'); b12 = w.h('; 1 2 <_ B'); beq = w.h('B = ( log ` A )')
    hlc = w.h('( log ` ( 4 x. C ) ) <_ B')
    mre = w.h('M e. RR'); meq = w.h('M = ( A x. B )')
    zre = w.h('Z e. RR'); z1 = w.h('1 <_ Z'); zhi = w.h('Z <_ ( ( 4 x. C ) x. M )')
    c = Closure(w, PH, {'C': ('RR', cre), 'A': ('RR', are), 'B': ('RR', bre),
                        'M': ('RR', mre), 'Z': ('RR', zre)})
    m12 = w.s([are, a1, bre, b12, mre, meq], 'cbm12', A('; 1 2 <_ M'))
    m0 = linarith(w, PH, [m12], '0 < M', closure=c)
    a0 = linarith(w, PH, [a1], '0 < A', closure=c)
    b0 = linarith(w, PH, [b12], '0 < B', closure=c)
    z0 = linarith(w, PH, [z1], '0 < Z', closure=c)
    c40 = linarith(w, PH, [c1000], '0 < ( 4 x. C )', closure=c)
    c0 = linarith(w, PH, [c1000], '0 < C', closure=c)
    for v, st in (('M', m0), ('A', a0), ('B', b0), ('Z', z0), ('C', c0)):
        c.have(v, 'gt0', st)
    mrp = w.s([mre, m0], 'elrpd', A('M e. RR+'))
    arp = w.s([are, a0], 'elrpd', A('A e. RR+'))
    brp = w.s([bre, b0], 'elrpd', A('B e. RR+'))
    zrp = w.s([zre, z0], 'elrpd', A('Z e. RR+'))
    c4re = w.s([w.s([num.fact(w, '4', 'RR')], 'a1i', A('4 e. RR')), cre], 'remulcld', A('( 4 x. C ) e. RR'))
    c4rp = w.s([c4re, c40], 'elrpd', A('( 4 x. C ) e. RR+'))
    bigrp = w.s([c4rp, mrp], 'rpmulcld', A('( ( 4 x. C ) x. M ) e. RR+'))
    # log Z <_ log ( ( 4 C ) M )
    bi = w.s([zrp, bigrp, w.inst('logleb')], 'syl2anc',
             A('( Z <_ ( ( 4 x. C ) x. M ) <-> ( log ` Z ) <_ ( log ` ( ( 4 x. C ) x. M ) ) )'))
    h1 = w.s([zhi, bi], 'mpbid', A('( log ` Z ) <_ ( log ` ( ( 4 x. C ) x. M ) )'))
    h2 = w.s([c4rp, mrp, w.inst('relogmul')], 'syl2anc',
             A('( log ` ( ( 4 x. C ) x. M ) ) = ( ( log ` ( 4 x. C ) ) + ( log ` M ) )'))
    h3a = w.s([w.s([meq], 'fveq2d', A('( log ` M ) = ( log ` ( A x. B ) )')),
               w.s([arp, brp, w.inst('relogmul')], 'syl2anc',
                   A('( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) )'))], 'eqtrd',
              A('( log ` M ) = ( ( log ` A ) + ( log ` B ) )'))
    h4 = w.s([beq], 'eqcomd', A('( log ` A ) = B'))
    b1 = linarith(w, PH, [b12], '1 <_ B', closure=c)
    h5 = w.s([bre, b1, w.inst('extrwlogle')], 'syl2anc', A('( log ` B ) <_ ( B - 1 )'))
    linarith(w, PH, [h1, h2, h3a, h4, hlc, h5], '( log ` Z ) <_ ( 3 x. B )', closure=c, name='qed')
    return w


@gen
def cbtlz():
    w = WH('cbtlz', 'The number of reservoir primes times the logarithm of the first scale '
                    'is at most fifteen times the product of the iterated logarithms '
                    '(Lean AlgBudget.lean, ` hTlz ` of costPieces_bound).')
    are = w.h('A e. RR'); a1 = w.h('1 <_ A')
    bre = w.h('B e. RR'); mre = w.h('M e. RR'); meq = w.h('M = ( A x. B )')
    tre = w.h('T e. RR'); thi = w.h('T <_ ( 5 x. A )')
    gre = w.h('G e. RR'); g0 = w.h('0 <_ G'); ghi = w.h('G <_ ( 3 x. B )')
    c = Closure(w, PH, {'A': ('RR', are), 'B': ('RR', bre), 'M': ('RR', mre),
                        'T': ('RR', tre), 'G': ('RR', gre)})
    nlinarith(w, PH, [a1, meq, thi, g0, ghi], '( T x. G ) <_ ( ; 1 5 x. M )', closure=c, name='qed')
    return w


def main():
    ok = True
    for fn in GENS:
        if only and fn.__name__ not in only:
            continue
        ok = fn().run() and ok
    return ok

if __name__ == '__main__':
    sys.exit(0 if main() else 1)
