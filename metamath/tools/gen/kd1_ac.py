"""Sortie KD1: zeros near 1 + i T lie in the 13/8 square zero set (kdmemzd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from lin import linarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_memzd():
    w = W('kdmemzd', 'Lean ` KDerivDetect.mem_zeroDiskFinset_of_near ` : a zero of ` L ( s , chi ) ` within ` W <_ 1 / 2 ` of ` 1 + i T ` belongs to the zero set of the ` 13 / 8 ` square about ` 2 + i T ` .')
    A0 = S['kdmemzd'].split(' -> Q e.')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ct = s([], 'simp1', '( %s /\\ T e. RR )' % CHI); tr = s([ct], 'simprd', 'T e. RR')
    ql = s([], 'simp2', '( Q e. CC /\\ ( %s ` Q ) = 0 )' % LFN); qc = s([ql], 'simpld', 'Q e. CC'); l0 = s([ql], 'simprd', '( %s ` Q ) = 0' % LFN)
    wg = s([], 'simp3', '( W e. RR /\\ W <_ ( 1 / 2 ) /\\ ( abs ` ( Q - %s ) ) <_ W )' % ONE('T'))
    wr = s([wg], 'simp1d', 'W e. RR'); w12 = s([wg], 'simp2d', 'W <_ ( 1 / 2 )'); dq = s([wg], 'simp3d', '( abs ` ( Q - %s ) ) <_ W' % ONE('T'))
    O1 = ONE('T'); DQ = '( Q - %s )' % O1
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
    o1c = s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % O1)
    dqc = s([qc, o1c], 'subcld', '%s e. CC' % DQ)
    ro = s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % O1)
    io = s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % O1)
    rd = s([qc, o1c], 'resubd', '( Re ` %s ) = ( ( Re ` Q ) - ( Re ` %s ) )' % (DQ, O1))
    idd = s([qc, o1c], 'imsubd', '( Im ` %s ) = ( ( Im ` Q ) - ( Im ` %s ) )' % (DQ, O1))
    adq = s([dqc], 'abscld', '( abs ` %s ) e. RR' % DQ)
    ar = s([dqc, w.inst('absrele')], 'syl', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (DQ, DQ))
    ai = s([dqc, w.inst('absimle')], 'syl', '( abs ` ( Im ` %s ) ) <_ ( abs ` %s )' % (DQ, DQ))
    rdr = s([dqc], 'recld', '( Re ` %s ) e. RR' % DQ); idr = s([dqc], 'imcld', '( Im ` %s ) e. RR' % DQ)
    arw = s([s([rdr], 'recnd', '( Re ` %s ) e. CC' % DQ)], 'abscld', '( abs ` ( Re ` %s ) ) e. RR' % DQ)
    aiw = s([s([idr], 'recnd', '( Im ` %s ) e. CC' % DQ)], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % DQ)
    arW = s([arw, adq, wr, ar, dq], 'letrd', '( abs ` ( Re ` %s ) ) <_ W' % DQ)
    aiW = s([aiw, adq, wr, ai, dq], 'letrd', '( abs ` ( Im ` %s ) ) <_ W' % DQ)
    rb = s([arW, s([rdr, wr], 'absled', '( ( abs ` ( Re ` %s ) ) <_ W <-> ( -u W <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ W ) )' % (DQ, DQ, DQ))], 'mpbid', '( -u W <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ W )' % (DQ, DQ))
    ib = s([aiW, s([idr, wr], 'absled', '( ( abs ` ( Im ` %s ) ) <_ W <-> ( -u W <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ W ) )' % (DQ, DQ, DQ))], 'mpbid', '( -u W <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ W )' % (DQ, DQ))
    SQ13 = SQ(CT('T'), R138)
    from kd1_q import corners
    cct = s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CT('T'))
    rc = s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 2' % CT('T'))
    icc = s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % CT('T'))
    c = Closure(w, A0, {'T': ('RR', tr), 'W': ('RR', wr)})
    K = corners(w, A0, CT('T'), R138, cct, rc, icc, c.mem(R138, 'RR'))
    for X_ in ('( Re ` %s )' % A13, '( Re ` %s )' % B13, '( Im ` %s )' % A13, '( Im ` %s )' % B13):
        st = K['lo'] if A13 in X_ else K['hi']
        c.leaf(X_, 'RR', s([st], 'recld' if X_.startswith('( Re') else 'imcld', '%s e. RR' % X_)); c.atom(X_)
    for X_, st in (('( Re ` Q )', s([qc], 'recld', '( Re ` Q ) e. RR')), ('( Im ` Q )', s([qc], 'imcld', '( Im ` Q ) e. RR')), ('( Re ` %s )' % DQ, rdr), ('( Im ` %s )' % DQ, idr),
                   ('( Re ` %s )' % O1, s([o1c], 'recld', '( Re ` %s ) e. RR' % O1)), ('( Im ` %s )' % O1, s([o1c], 'imcld', '( Im ` %s ) e. RR' % O1))):
        c.leaf(X_, 'RR', st); c.atom(X_)
    hy = [rd, idd, ro, io, K['ReA'], K['ReB'], K['ImA'], K['ImB'], w12, s([rb], 'simpld', '-u W <_ ( Re ` %s )' % DQ), s([rb], 'simprd', '( Re ` %s ) <_ W' % DQ),
          s([ib], 'simpld', '-u W <_ ( Im ` %s )' % DQ), s([ib], 'simprd', '( Im ` %s ) <_ W' % DQ)]
    g1 = linarith(w, A0, hy, '( Re ` %s ) <_ ( Re ` Q )' % A13, closure=c)
    g2 = linarith(w, A0, hy, '( Re ` Q ) <_ ( Re ` %s )' % B13, closure=c)
    g3 = linarith(w, A0, hy, '( Im ` %s ) <_ ( Im ` Q )' % A13, closure=c)
    g4 = linarith(w, A0, hy, '( Im ` Q ) <_ ( Im ` %s )' % B13, closure=c)
    ri = s([s([c.mem('( Re ` Q )', 'RR'), g1, g2], '3jca', '( ( Re ` Q ) e. RR /\\ ( Re ` %s ) <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ ( Re ` %s ) )' % (A13, B13)),
            s([c.mem('( Re ` %s )' % A13, 'RR'), c.mem('( Re ` %s )' % B13, 'RR'), w.inst('elicc2')], 'syl2anc',
              '( ( Re ` Q ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) <-> ( ( Re ` Q ) e. RR /\\ ( Re ` %s ) <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ ( Re ` %s ) ) )' % (A13, B13, A13, B13))],
           'mpbird', '( Re ` Q ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (A13, B13))
    ii = s([s([c.mem('( Im ` Q )', 'RR'), g3, g4], '3jca', '( ( Im ` Q ) e. RR /\\ ( Im ` %s ) <_ ( Im ` Q ) /\\ ( Im ` Q ) <_ ( Im ` %s ) )' % (A13, B13)),
            s([c.mem('( Im ` %s )' % A13, 'RR'), c.mem('( Im ` %s )' % B13, 'RR'), w.inst('elicc2')], 'syl2anc',
              '( ( Im ` Q ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) <-> ( ( Im ` Q ) e. RR /\\ ( Im ` %s ) <_ ( Im ` Q ) /\\ ( Im ` Q ) <_ ( Im ` %s ) ) )' % (A13, B13, A13, B13))],
           'mpbird', '( Im ` Q ) e. ( ( Im ` %s ) [,] ( Im ` %s ) )' % (A13, B13))
    qsq = s([s([qc, ri, ii], '3jca', '( Q e. CC /\\ ( Re ` Q ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` Q ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A13, B13, A13, B13)),
             s([K['lo'], K['hi'], w.inst('elcrect')], 'syl2anc', '( Q e. %s <-> ( Q e. CC /\\ ( Re ` Q ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` Q ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (SQ13, A13, B13, A13, B13))],
            'mpbird', 'Q e. %s' % SQ13)
    ely = w.s([w.s([], 'fveqeq2', '( r = Q -> ( ( %s ` r ) = 0 <-> ( %s ` Q ) = 0 ) )' % (LFN, LFN))], 'elrab', '( Q e. %s <-> ( Q e. %s /\\ ( %s ` Q ) = 0 ) )' % (ZD(), SQ13, LFN))
    fin = s([s([qsq, l0], 'jca', '( Q e. %s /\\ ( %s ` Q ) = 0 )' % (SQ13, LFN)), ely], 'sylibr', 'Q e. %s' % ZD())
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdmemzd']))
    return run(w)


if __name__ == '__main__':
    gen_memzd()
