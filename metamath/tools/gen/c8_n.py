"""Sortie C8, section 4: squares about a point (sqre, absreimle, sqint, sqmem,
sqsub, sqrbd, sqnest)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from cl import lift

A0S = '( C e. CC /\\ R e. RR )'


def SQRE(c='C', r='R'):
    a, b = SQA(c, r), SQB(c, r)
    return '( ( ( Re ` %s ) = ( ( Re ` %s ) - %s ) /\\ ( Re ` %s ) = ( ( Re ` %s ) + %s ) ) /\\ ( ( Im ` %s ) = ( ( Im ` %s ) - %s ) /\\ ( Im ` %s ) = ( ( Im ` %s ) + %s ) ) )' % (
        a, c, r, b, c, r, a, c, r, b, c, r)


def sqparts(w, ante, st, c='C', r='R'):
    """the four equalities of a step ( ante -> SQRE(c, r) ): [ReA, ReB, ImA, ImB]"""
    a, b = SQA(c, r), SQB(c, r)
    re_ = w.s([st, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` %s ) = ( ( Re ` %s ) - %s ) /\\ ( Re ` %s ) = ( ( Re ` %s ) + %s ) ) )' % (ante, a, c, r, b, c, r))
    im_ = w.s([st, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` %s ) = ( ( Im ` %s ) - %s ) /\\ ( Im ` %s ) = ( ( Im ` %s ) + %s ) ) )' % (ante, a, c, r, b, c, r))
    return [w.s([re_, w.inst('simpl')], 'syl', '( %s -> ( Re ` %s ) = ( ( Re ` %s ) - %s ) )' % (ante, a, c, r)),
            w.s([re_, w.inst('simpr')], 'syl', '( %s -> ( Re ` %s ) = ( ( Re ` %s ) + %s ) )' % (ante, b, c, r)),
            w.s([im_, w.inst('simpl')], 'syl', '( %s -> ( Im ` %s ) = ( ( Im ` %s ) - %s ) )' % (ante, a, c, r)),
            w.s([im_, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) = ( ( Im ` %s ) + %s ) )' % (ante, b, c, r))]


def sqre_at(w, ante, cst, rst, c='C', r='R'):
    """( ante -> SQRE(c, r) ) from cst : ( ante -> c e. CC ), rst : ( ante -> R e. RR )"""
    j = w.s([cst, rst], 'jca', '( %s -> ( %s e. CC /\\ %s e. RR ) )' % (ante, c, r))
    return w.s([j, w.inst('sqre')], 'syl', '( %s -> %s )' % (ante, SQRE(c, r)))


def gen_sqre():
    w = W('sqre', 'The real and imaginary parts of the corners of the square of half-side ` R ` about ` C ` .')
    A0 = A0S
    cc = w.s([], 'simpl', '( %s -> C e. CC )' % A0)
    rr = w.s([], 'simpr', '( %s -> R e. RR )' % A0)
    rc = w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)
    WW = '( R + ( _i x. R ) )'
    wc = w.s([rc, w.s([closed(w, A0, 'ax-icn', '_i e. CC'), rc], 'mulcld', '( %s -> ( _i x. R ) e. CC )' % A0)], 'addcld', '( %s -> %s e. CC )' % (A0, WW))
    rw = w.s([rr, rr], 'crred', '( %s -> ( Re ` %s ) = R )' % (A0, WW))
    iw = w.s([rr, rr], 'crimd', '( %s -> ( Im ` %s ) = R )' % (A0, WW))
    out = []
    for part, pw, op, lem in [('Re', rw, '-', 'resubd'), ('Re', rw, '+', 'readdd'), ('Im', iw, '-', 'imsubd'), ('Im', iw, '+', 'imaddd')]:
        X = '( C %s %s )' % (op, WW)
        e1 = w.s([cc, wc], lem, '( %s -> ( %s ` %s ) = ( ( %s ` C ) %s ( %s ` %s ) ) )' % (A0, part, X, part, op, part, WW))
        e2 = w.s([pw], 'oveq2d', '( %s -> ( ( %s ` C ) %s ( %s ` %s ) ) = ( ( %s ` C ) %s R ) )' % (A0, part, op, part, WW, part, op))
        out.append(w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` %s ) = ( ( %s ` C ) %s R ) )' % (A0, part, X, part, op)))
    a, b = SQA('C', 'R'), SQB('C', 'R')
    j1 = w.s([out[0], out[1]], 'jca', '( %s -> ( ( Re ` %s ) = ( ( Re ` C ) - R ) /\\ ( Re ` %s ) = ( ( Re ` C ) + R ) ) )' % (A0, a, b))
    j2 = w.s([out[2], out[3]], 'jca', '( %s -> ( ( Im ` %s ) = ( ( Im ` C ) - R ) /\\ ( Im ` %s ) = ( ( Im ` C ) + R ) ) )' % (A0, a, b))
    w.qed([j1, j2], 'jca', '( %s -> %s )' % (A0, SQRE()))
    return run8(w)


def gen_absreimle():
    w = W('absreimle', 'The absolute value of a complex number is at most the sum of the absolute values of its real and imaginary parts.')
    A0 = 'A e. CC'
    ac = w.s([], 'id', '( A e. CC -> A e. CC )')
    re_ = w.s([ac], 'recld', '( %s -> ( Re ` A ) e. RR )' % A0)
    im_ = w.s([ac], 'imcld', '( %s -> ( Im ` A ) e. RR )' % A0)
    rc = w.s([re_], 'recnd', '( %s -> ( Re ` A ) e. CC )' % A0)
    ic = w.s([im_], 'recnd', '( %s -> ( Im ` A ) e. CC )' % A0)
    iC = closed(w, A0, 'ax-icn', '_i e. CC')
    iim = w.s([iC, ic], 'mulcld', '( %s -> ( _i x. ( Im ` A ) ) e. CC )' % A0)
    rp = w.s([ac, w.inst('replim')], 'syl', '( %s -> A = ( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) )' % A0)
    t = w.s([rc, iim], 'abstrid', '( %s -> ( abs ` ( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) ) <_ ( ( abs ` ( Re ` A ) ) + ( abs ` ( _i x. ( Im ` A ) ) ) ) )' % A0)
    am = w.s([w.s([iC, ic], 'absmuld', '( %s -> ( abs ` ( _i x. ( Im ` A ) ) ) = ( ( abs ` _i ) x. ( abs ` ( Im ` A ) ) ) )' % A0),
              w.s([w.s([closed(w, A0, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( %s -> ( ( abs ` _i ) x. ( abs ` ( Im ` A ) ) ) = ( 1 x. ( abs ` ( Im ` A ) ) ) )' % A0),
                   w.s([w.s([ic], 'abscld', '( %s -> ( abs ` ( Im ` A ) ) e. RR )' % A0)], 'recnd', '( %s -> ( abs ` ( Im ` A ) ) e. CC )' % A0) and
                   w.s([w.s([w.s([ic], 'abscld', '( %s -> ( abs ` ( Im ` A ) ) e. RR )' % A0)], 'recnd', '( %s -> ( abs ` ( Im ` A ) ) e. CC )' % A0)], 'mullidd',
                       '( %s -> ( 1 x. ( abs ` ( Im ` A ) ) ) = ( abs ` ( Im ` A ) ) )' % A0)], 'eqtrd',
                  '( %s -> ( ( abs ` _i ) x. ( abs ` ( Im ` A ) ) ) = ( abs ` ( Im ` A ) ) )' % A0)], 'eqtrd', '( %s -> ( abs ` ( _i x. ( Im ` A ) ) ) = ( abs ` ( Im ` A ) ) )' % A0)
    t2 = w.s([t, w.s([am], 'oveq2d', '( %s -> ( ( abs ` ( Re ` A ) ) + ( abs ` ( _i x. ( Im ` A ) ) ) ) = ( ( abs ` ( Re ` A ) ) + ( abs ` ( Im ` A ) ) ) )' % A0)], 'breqtrd',
             '( %s -> ( abs ` ( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) ) <_ ( ( abs ` ( Re ` A ) ) + ( abs ` ( Im ` A ) ) ) )' % A0)
    w.qed([w.s([rp], 'fveq2d', '( %s -> ( abs ` A ) = ( abs ` ( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) ) )' % A0), t2], 'eqbrtrd',
          '( %s -> ( abs ` A ) <_ ( ( abs ` ( Re ` A ) ) + ( abs ` ( Im ` A ) ) ) )' % A0)
    return run8(w)


def coords(w, ante, ust, cst, U='U', c='C'):
    """for U, c complex: steps X = Re U - Re c, |X| <_ |U - c| and the same for Im;
    returns dict with leaves and facts"""
    d = {}
    uc = w.s([ust, cst], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (ante, U, c))
    d['auc'] = w.s([uc], 'abscld', '( %s -> ( abs ` ( %s - %s ) ) e. RR )' % (ante, U, c))
    for part, lem, lemle in [('Re', 'resubd', 'absrele'), ('Im', 'imsubd', 'absimle')]:
        X = '( ( %s ` %s ) - ( %s ` %s ) )' % (part, U, part, c)
        e = w.s([ust, cst], lem, '( %s -> ( %s ` ( %s - %s ) ) = %s )' % (ante, part, U, c, X))
        le = w.s([uc, w.inst(lemle)], 'syl', '( %s -> ( abs ` ( %s ` ( %s - %s ) ) ) <_ ( abs ` ( %s - %s ) ) )' % (ante, part, U, c, U, c))
        lex = w.s([w.s([e], 'fveq2d', '( %s -> ( abs ` ( %s ` ( %s - %s ) ) ) = ( abs ` %s ) )' % (ante, part, U, c, X)), le], 'eqbrtrrd',
                  '( %s -> ( abs ` %s ) <_ ( abs ` ( %s - %s ) ) )' % (ante, X, U, c))
        pu = w.s([ust], 'recld' if part == 'Re' else 'imcld', '( %s -> ( %s ` %s ) e. RR )' % (ante, part, U))
        pc = w.s([cst], 'recld' if part == 'Re' else 'imcld', '( %s -> ( %s ` %s ) e. RR )' % (ante, part, c))
        xr = w.s([pu, pc], 'resubcld', '( %s -> %s e. RR )' % (ante, X))
        lo, hi, ax = absbnds(w, ante, X, xr)
        d[part] = dict(X=X, lex=lex, lo=lo, hi=hi, ax=ax, pu=pu, pc=pc)
    return d


def sqcc(w, ante, cst, rst, c='C', r='R'):
    """steps ( ante -> SQA(c,r) e. CC ), ( ante -> SQB(c,r) e. CC )"""
    rc = w.s([rst], 'recnd', '( %s -> %s e. CC )' % (ante, r))
    WW = '( %s + ( _i x. %s ) )' % (r, r)
    wc = w.s([rc, w.s([closed(w, ante, 'ax-icn', '_i e. CC'), rc], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (ante, r))], 'addcld', '( %s -> %s e. CC )' % (ante, WW))
    return (w.s([cst, wc], 'subcld', '( %s -> %s e. CC )' % (ante, SQA(c, r))), w.s([cst, wc], 'addcld', '( %s -> %s e. CC )' % (ante, SQB(c, r))))


def reim_leaves(w, ante, xs):
    """leaves ( Re ` x ), ( Im ` x ) for steps xs = {x: ( ante -> x e. CC )}"""
    lv = {}
    for x, st in xs.items():
        lv['( Re ` %s )' % x] = w.s([st], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (ante, x))
        lv['( Im ` %s )' % x] = w.s([st], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (ante, x))
    return lv


def gen_sqint():
    w = W('sqint', 'A point closer to ` C ` than ` R ` is strictly inside the square of half-side ` R ` about ` C ` .')
    A0 = '( %s /\\ ( U e. CC /\\ ( abs ` ( U - C ) ) < R ) )' % A0S
    a, b = SQA('C', 'R'), SQB('C', 'R')
    cs = w.s([], 'simpll', '( %s -> C e. CC )' % A0)
    rs = w.s([], 'simplr', '( %s -> R e. RR )' % A0)
    us = w.s([], 'simprl', '( %s -> U e. CC )' % A0)
    lt = w.s([], 'simprr', '( %s -> ( abs ` ( U - C ) ) < R )' % A0)
    pa = sqparts(w, A0, sqre_at(w, A0, cs, rs))
    ac, bc = sqcc(w, A0, cs, rs)
    d = coords(w, A0, us, cs)
    lv = reim_leaves(w, A0, {a: ac, b: bc, 'U': us, 'C': cs})
    lv['R'] = rs; lv['( abs ` ( U - C ) )'] = d['auc']
    for part in ('Re', 'Im'):
        lv['( abs ` %s )' % d[part]['X']] = d[part]['ax']
    g = []
    for i, (part, lo) in enumerate([('Re', True), ('Re', False), ('Im', True), ('Im', False)]):
        D = d[part]
        if lo:
            g.append(lin8(w, A0, [pa[i], D['lo'], D['lex'], lt], '( %s ` %s ) < ( %s ` U )' % (part, a, part), lv))
        else:
            g.append(lin8(w, A0, [pa[i], D['hi'], D['lex'], lt], '( %s ` U ) < ( %s ` %s )' % (part, part, b), lv))
    j1 = w.s([g[0], g[1]], 'jca', '( %s -> ( ( Re ` %s ) < ( Re ` U ) /\\ ( Re ` U ) < ( Re ` %s ) ) )' % (A0, a, b))
    j2 = w.s([g[2], g[3]], 'jca', '( %s -> ( ( Im ` %s ) < ( Im ` U ) /\\ ( Im ` U ) < ( Im ` %s ) ) )' % (A0, a, b))
    w.qed([us, w.s([j1, j2], 'jca', '( %s -> ( ( ( Re ` %s ) < ( Re ` U ) /\\ ( Re ` U ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` U ) /\\ ( Im ` U ) < ( Im ` %s ) ) ) )' % (A0, a, b, a, b))],
          'jca', '( %s -> %s )' % (A0, INTG(a, b, 'U')))
    return run8(w)


def gen_sqmem():
    w = W('sqmem', 'A point of the square of half-side ` R ` about ` C ` is within ` 2 R ` of ` C ` .')
    a, b = SQA('C', 'R'), SQB('C', 'R')
    A0 = '( %s /\\ U e. %s )' % (A0S, SQ('C', 'R'))
    cs = w.s([], 'simpll', '( %s -> C e. CC )' % A0)
    rs = w.s([], 'simplr', '( %s -> R e. RR )' % A0)
    um = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, SQ('C', 'R')))
    pa = sqparts(w, A0, sqre_at(w, A0, cs, rs))
    ac, bc = sqcc(w, A0, cs, rs)
    EL = '( U e. CC /\\ ( Re ` U ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` U ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (a, b, a, b)
    el = w.s([um, w.s([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, a, b)), w.inst('elcrect')], 'syl', '( %s -> ( U e. %s <-> %s ) )' % (A0, SQ('C', 'R'), EL))],
             'mpbid', '( %s -> %s )' % (A0, EL))
    us = w.s([el, w.inst('simp1')], 'syl', '( %s -> U e. CC )' % A0)
    lv = reim_leaves(w, A0, {a: ac, b: bc, 'U': us, 'C': cs})
    lv['R'] = rs
    d = coords(w, A0, us, cs)
    bnd = {}
    for part, k in (('Re', 'simp2'), ('Im', 'simp3')):
        mem = w.s([el, w.inst(k)], 'syl', '( %s -> ( %s ` U ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) )' % (A0, part, part, a, part, b))
        E2 = '( ( %s ` U ) e. RR /\\ ( %s ` %s ) <_ ( %s ` U ) /\\ ( %s ` U ) <_ ( %s ` %s ) )' % (part, part, a, part, part, part, b)
        e2 = w.s([mem, w.s([lv['( %s ` %s )' % (part, a)], lv['( %s ` %s )' % (part, b)], w.inst('elicc2')], 'syl2anc',
                           '( %s -> ( ( %s ` U ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> %s ) )' % (A0, part, part, a, part, b, E2))], 'mpbid', '( %s -> %s )' % (A0, E2))
        l1 = w.s([e2, w.inst('simp2')], 'syl', '( %s -> ( %s ` %s ) <_ ( %s ` U ) )' % (A0, part, a, part))
        l2 = w.s([e2, w.inst('simp3')], 'syl', '( %s -> ( %s ` U ) <_ ( %s ` %s ) )' % (A0, part, part, b))
        X = d[part]['X']
        i0 = 0 if part == 'Re' else 2
        n1 = lin8(w, A0, [pa[i0], l1], '-u R <_ %s' % X, lv)
        n2 = lin8(w, A0, [pa[i0 + 1], l2], '%s <_ R' % X, lv)
        xr = w.s([d[part]['pu'], d[part]['pc']], 'resubcld', '( %s -> %s e. RR )' % (A0, X))
        bnd[part] = w.s([w.s([n1, n2], 'jca', '( %s -> ( -u R <_ %s /\\ %s <_ R ) )' % (A0, X, X)), w.s([xr, rs], 'absled', '( %s -> ( ( abs ` %s ) <_ R <-> ( -u R <_ %s /\\ %s <_ R ) ) )' % (A0, X, X, X))],
                        'mpbird', '( %s -> ( abs ` %s ) <_ R )' % (A0, X))
    uc = w.s([us, cs], 'subcld', '( %s -> ( U - C ) e. CC )' % A0)
    ari = w.s([uc, w.inst('absreimle')], 'syl', '( %s -> ( abs ` ( U - C ) ) <_ ( ( abs ` ( Re ` ( U - C ) ) ) + ( abs ` ( Im ` ( U - C ) ) ) ) )' % A0)
    XR, XI = d['Re']['X'], d['Im']['X']
    eqs = w.s([w.s([w.s([us, cs], 'resubd', '( %s -> ( Re ` ( U - C ) ) = %s )' % (A0, XR))], 'fveq2d', '( %s -> ( abs ` ( Re ` ( U - C ) ) ) = ( abs ` %s ) )' % (A0, XR)),
               w.s([w.s([us, cs], 'imsubd', '( %s -> ( Im ` ( U - C ) ) = %s )' % (A0, XI))], 'fveq2d', '( %s -> ( abs ` ( Im ` ( U - C ) ) ) = ( abs ` %s ) )' % (A0, XI))],
              'oveq12d', '( %s -> ( ( abs ` ( Re ` ( U - C ) ) ) + ( abs ` ( Im ` ( U - C ) ) ) ) = ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, XR, XI))
    ari2 = w.s([ari, eqs], 'breqtrd', '( %s -> ( abs ` ( U - C ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, XR, XI))
    lv['( abs ` ( U - C ) )'] = d['auc']; lv['( abs ` %s )' % XR] = d['Re']['ax']; lv['( abs ` %s )' % XI] = d['Im']['ax']
    lin8(w, A0, [ari2, bnd['Re'], bnd['Im']], '( abs ` ( U - C ) ) <_ ( 2 x. R )', lv)
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
    return run8(w)


def asqed(w):
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]


def gen_sqsub():
    w = W('sqsub', 'A square of half-side ` T ` about ` U ` lies in the open square of half-side ` R ` about ` C ` when ` abs ( U - C ) + T < R ` .')
    A0 = '( ( C e. CC /\\ ( R e. RR /\\ T e. RR ) ) /\\ ( U e. CC /\\ ( ( abs ` ( U - C ) ) + T ) < R ) )'
    a, b, p, q = SQA('C', 'R'), SQB('C', 'R'), SQA('U', 'T'), SQB('U', 'T')
    cs = w.s([], 'simpll', '( %s -> C e. CC )' % A0)
    rs = w.s([], 'simplrl', '( %s -> R e. RR )' % A0)
    ss = w.s([], 'simplrr', '( %s -> T e. RR )' % A0)
    us = w.s([], 'simprl', '( %s -> U e. CC )' % A0)
    lt = w.s([], 'simprr', '( %s -> ( ( abs ` ( U - C ) ) + T ) < R )' % A0)
    pa = sqparts(w, A0, sqre_at(w, A0, cs, rs))
    pp = sqparts(w, A0, sqre_at(w, A0, us, ss, 'U', 'T'), 'U', 'T')
    ac, bc = sqcc(w, A0, cs, rs)
    pc, qc = sqcc(w, A0, us, ss, 'U', 'T')
    d = coords(w, A0, us, cs)
    lv = reim_leaves(w, A0, {a: ac, b: bc, p: pc, q: qc, 'U': us, 'C': cs})
    lv['R'] = rs; lv['T'] = ss; lv['( abs ` ( U - C ) )'] = d['auc']
    for part in ('Re', 'Im'):
        lv['( abs ` %s )' % d[part]['X']] = d[part]['ax']
    g = []
    for i, (part, lo) in enumerate([('Re', True), ('Re', False), ('Im', True), ('Im', False)]):
        D = d[part]
        if lo:
            g.append(lin8(w, A0, [pa[i], pp[i], D['lo'], D['lex'], lt], '( %s ` %s ) < ( %s ` %s )' % (part, a, part, p), lv))
        else:
            g.append(lin8(w, A0, [pa[i], pp[i], D['hi'], D['lex'], lt], '( %s ` %s ) < ( %s ` %s )' % (part, q, part, b), lv))
    I3 = '( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )' % (a, p, q, b, a, p, q, b)
    j = w.s([w.s([g[0], g[1]], 'jca', '( %s -> ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) )' % (A0, a, p, q, b)),
             w.s([g[2], g[3]], 'jca', '( %s -> ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )' % (A0, a, p, q, b))], 'jca', '( %s -> %s )' % (A0, I3))
    w.qed([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, a, b)), w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, p, q)), j,
           w.inst('crectorect')], 'syl3anc', '( %s -> %s C_ %s )' % (A0, SQ('U', 'T'), ORECT(a, b)))
    return run8(w)


def gen_sqrbd():
    w = W('sqrbd', 'The half-side ` R ` is below the four coordinate gaps of the centre of the square.')
    A0 = A0S
    a, b = SQA('C', 'R'), SQB('C', 'R')
    cs = w.s([], 'simpl', '( %s -> C e. CC )' % A0)
    rs = w.s([], 'simpr', '( %s -> R e. RR )' % A0)
    pa = sqparts(w, A0, sqre_at(w, A0, cs, rs))
    ac, bc = sqcc(w, A0, cs, rs)
    lv = reim_leaves(w, A0, {a: ac, b: bc, 'C': cs})
    lv['R'] = rs
    g = [lin8(w, A0, [pa[0]], 'R <_ ( ( Re ` C ) - ( Re ` %s ) )' % a, lv), lin8(w, A0, [pa[1]], 'R <_ ( ( Re ` %s ) - ( Re ` C ) )' % b, lv),
         lin8(w, A0, [pa[2]], 'R <_ ( ( Im ` C ) - ( Im ` %s ) )' % a, lv), lin8(w, A0, [pa[3]], 'R <_ ( ( Im ` %s ) - ( Im ` C ) )' % b, lv)]
    R = RBDG(a, b, 'C', 'R')
    j = w.s([w.s([g[0], g[1]], 'jca', '( %s -> ( R <_ ( ( Re ` C ) - ( Re ` %s ) ) /\\ R <_ ( ( Re ` %s ) - ( Re ` C ) ) ) )' % (A0, a, b)),
             w.s([g[2], g[3]], 'jca', '( %s -> ( R <_ ( ( Im ` C ) - ( Im ` %s ) ) /\\ R <_ ( ( Im ` %s ) - ( Im ` C ) ) ) )' % (A0, a, b))], 'jca',
            '( %s -> %s )' % (A0, R[len('( R e. RR /\\ '):-2]))
    w.qed([rs, j], 'jca', '( %s -> %s )' % (A0, R))
    return run8(w)


def gen_sqnest():
    w = W('sqnest', 'The corners of the square of half-side ` R ` moved out by ` T + i T ` are the corners of the square of half-side ` R + T ` .')
    A0 = '( C e. CC /\\ ( R e. CC /\\ T e. CC ) )'
    cs = w.s([], 'simpl', '( %s -> C e. CC )' % A0)
    rc = w.s([], 'simprl', '( %s -> R e. CC )' % A0)
    sc = w.s([], 'simprr', '( %s -> T e. CC )' % A0)
    ic = closed(w, A0, 'ax-icn', '_i e. CC')
    ir = w.s([ic, rc], 'mulcld', '( %s -> ( _i x. R ) e. CC )' % A0)
    is_ = w.s([ic, sc], 'mulcld', '( %s -> ( _i x. T ) e. CC )' % A0)
    WR, WS = '( R + ( _i x. R ) )', '( T + ( _i x. T ) )'
    wr = w.s([rc, ir], 'addcld', '( %s -> %s e. CC )' % (A0, WR))
    ws_ = w.s([sc, is_], 'addcld', '( %s -> %s e. CC )' % (A0, WS))
    RS = '( R + T )'
    WRS = '( %s + ( _i x. %s ) )' % (RS, RS)
    a4 = w.s([rc, ir, sc, is_], 'add4d', '( %s -> ( %s + %s ) = ( %s + ( ( _i x. R ) + ( _i x. T ) ) ) )' % (A0, WR, WS, RS))
    ad = w.s([w.s([ic, rc, sc], 'adddid', '( %s -> ( _i x. %s ) = ( ( _i x. R ) + ( _i x. T ) ) )' % (A0, RS))], 'eqcomd', '( %s -> ( ( _i x. R ) + ( _i x. T ) ) = ( _i x. %s ) )' % (A0, RS))
    wsum = w.s([a4, w.s([ad], 'oveq2d', '( %s -> ( %s + ( ( _i x. R ) + ( _i x. T ) ) ) = %s )' % (A0, RS, WRS))], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, WR, WS, WRS))
    ea = w.s([w.s([cs, wr, ws_], 'subsub4d', '( %s -> ( %s - %s ) = ( C - ( %s + %s ) ) )' % (A0, SQA('C', 'R'), WS, WR, WS)), w.s([wsum], 'oveq2d', '( %s -> ( C - ( %s + %s ) ) = %s )' % (A0, WR, WS, SQA('C', RS)))],
             'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A0, SQA('C', 'R'), WS, SQA('C', RS)))
    eb = w.s([w.s([cs, wr, ws_], 'addassd', '( %s -> ( %s + %s ) = ( C + ( %s + %s ) ) )' % (A0, SQB('C', 'R'), WS, WR, WS)), w.s([wsum], 'oveq2d', '( %s -> ( C + ( %s + %s ) ) = %s )' % (A0, WR, WS, SQB('C', RS)))],
             'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, SQB('C', 'R'), WS, SQB('C', RS)))
    w.qed([ea, eb], 'jca', '( %s -> ( ( %s - %s ) = %s /\\ ( %s + %s ) = %s ) )' % (A0, SQA('C', 'R'), WS, SQA('C', RS), SQB('C', 'R'), WS, SQB('C', RS)))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_sqre, gen_absreimle, gen_sqint, gen_sqmem, gen_sqsub, gen_sqrbd, gen_sqnest]:
        g()
