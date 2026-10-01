"""ZL3b E1: generic lint lemmas for section E (translation, tails, splits, odd functions, scaling).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_e1.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of
from zl3b_d2 import cst

only = sys.argv[1:]
S = STATEMENTS


# ---------------------------------------------------------------- zl3ltr
if __name__ == '__main__' and (not only or 'zl3ltr' in only):
    w = W('zl3ltr', 'Translation of the integrand of a segment integral is translation of the segment.')
    ph, concl = ante_of(S['zl3ltr'])
    pc = w.s([], 'simpl1', '( %s -> P e. CC )' % ph); qc = w.s([], 'simpl2', '( %s -> Q e. CC )' % ph)
    sc = w.s([], 'simpl3', '( %s -> S e. CC )' % ph); gf = w.s([], 'simpr', '( %s -> G : CC --> CC )' % ph)
    F1 = TRN('G', 'S')
    gex = D(w, ph, 'syl2anc', [gf, cst(w, ph, 'cnex', 'CC e. _V'), w.inst('fex')], 'G e. _V')
    PS, QS = '( P + S )', '( Q + S )'
    psc = D(w, ph, 'addcld', [pc, sc], '%s e. CC' % PS); qsc = D(w, ph, 'addcld', [qc, sc], '%s e. CC' % QS)
    l1 = D(w, ph, 'syl3anc', [cst(w, ph, 'mptex', '%s e. _V' % F1), pc, qc, w.inst('lintval')], '%s = S. ( 0 (,) 1 ) ( ( %s ` ( P + ( t x. ( Q - P ) ) ) ) x. ( Q - P ) ) _d t' % (LI(F1, 'P', 'Q'), F1))
    l2 = D(w, ph, 'syl3anc', [gex, psc, qsc, w.inst('lintval')], '%s = S. ( 0 (,) 1 ) ( ( G ` ( %s + ( t x. ( %s - %s ) ) ) ) x. ( %s - %s ) ) _d t' % (LI('G', PS, QS), PS, QS, PS, QS, PS))
    A1 = '( %s /\\ t e. ( 0 (,) 1 ) )' % ph
    tc = w.s([w.s([w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % A1), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % A1)], 'recnd', '( %s -> t e. CC )' % A1)
    pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1); qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1); sc1 = w.s([sc], 'adantr', '( %s -> S e. CC )' % A1)
    QP = '( Q - P )'; TQP = '( t x. %s )' % QP; X = '( P + %s )' % TQP
    qpc = D(w, A1, 'subcld', [qc1, pc1], '%s e. CC' % QP); tqc = D(w, A1, 'mulcld', [tc, qpc], '%s e. CC' % TQP)
    xc = D(w, A1, 'addcld', [pc1, tqc], '%s e. CC' % X)
    XS = '( %s + S )' % X
    xsc = D(w, A1, 'addcld', [xc, sc1], '%s e. CC' % XS)
    # F1 ` X = G ` ( X + S )
    E = 'y = %s' % X
    ey = w.s([], 'id', '( %s -> %s )' % (E, E))
    sb = D(w, E, 'fveq2d', [D(w, E, 'oveq1d', [ey], '( y + S ) = %s' % XS)], '( G ` ( y + S ) ) = ( G ` %s )' % XS)
    fv = w.s([xc, w.s([sb, w.s([], 'eqid', '%s = %s' % (F1, F1)), w.s([], 'fvex', '( G ` %s ) e. _V' % XS)], 'fvmpt', '( %s e. CC -> ( %s ` %s ) = ( G ` %s ) )' % (X, F1, X, XS))],
             'syl', '( %s -> ( %s ` %s ) = ( G ` %s ) )' % (A1, F1, X, XS))
    # ( P + S ) + ( t x. ( ( Q + S ) - ( P + S ) ) ) = X + S
    dd = D(w, A1, 'pnpcan2d', [qc1, pc1, sc1], '( %s - %s ) = %s' % (QS, PS, QP))
    a1 = D(w, A1, 'oveq2d', [D(w, A1, 'oveq2d', [dd], '( t x. ( %s - %s ) ) = %s' % (QS, PS, TQP))], '( %s + ( t x. ( %s - %s ) ) ) = ( %s + %s )' % (PS, QS, PS, PS, TQP))
    a2 = D(w, A1, 'add32d', [pc1, sc1, tqc], '( %s + %s ) = %s' % (PS, TQP, XS))
    arg = D(w, A1, 'eqtrd', [a1, a2], '( %s + ( t x. ( %s - %s ) ) ) = %s' % (PS, QS, PS, XS))
    gv = D(w, A1, 'eqtr4d', [fv, D(w, A1, 'fveq2d', [arg], '( G ` ( %s + ( t x. ( %s - %s ) ) ) ) = ( G ` %s )' % (PS, QS, PS, XS))],
           '( %s ` %s ) = ( G ` ( %s + ( t x. ( %s - %s ) ) ) )' % (F1, X, PS, QS, PS))
    pt = D(w, A1, 'oveq12d', [gv, D(w, A1, 'eqcomd', [dd], '%s = ( %s - %s )' % (QP, QS, PS))],
           '( ( %s ` %s ) x. %s ) = ( ( G ` ( %s + ( t x. ( %s - %s ) ) ) ) x. ( %s - %s ) )' % (F1, X, QP, PS, QS, PS, QS, PS))
    ig = w.s([pt], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) ( ( %s ` %s ) x. %s ) _d t = S. ( 0 (,) 1 ) ( ( G ` ( %s + ( t x. ( %s - %s ) ) ) ) x. ( %s - %s ) ) _d t )'
             % (ph, F1, X, QP, PS, QS, PS, QS, PS))
    w.qed([l1, D(w, ph, 'eqtr4d', [ig, l2], 'S. ( 0 (,) 1 ) ( ( %s ` %s ) x. %s ) _d t = %s' % (F1, X, QP, LI('G', PS, QS)))], 'eqtrd', S['zl3ltr'])
    go(w, only)


# ---------------------------------------------------------------- zl3tl
def pow2t(t):
    return '( 2 ^c -u ( %s / 4 ) )' % t


def tail_b(t):
    return '( C x. ( %s ^c D ) )' % pow2t(t)


if __name__ == '__main__' and (not only or 'zl3tl' in only):
    w = W('zl3tl', 'An exponential tail bound gives the limit at infinity.')
    ph, concl = ante_of(S['zl3tl'])
    lc = w.s([], 'simp1l', '( %s -> L e. CC )' % ph); cr = w.s([], 'simp1r', '( %s -> C e. RR )' % ph)
    dp = w.s([], 'simp2l', '( %s -> D e. RR+ )' % ph); yr = w.s([], 'simp2r', '( %s -> Y e. RR )' % ph)
    ff = w.s([], 'simp3l', '( %s -> F : RR+ --> CC )' % ph)
    HB = 'A. s e. RR+ ( Y <_ s -> ( abs ` ( ( F ` s ) - L ) ) <_ %s )' % tail_b('s')
    hb = w.s([], 'simp3r', '( %s -> %s )' % (ph, HB))
    feq = D(w, ph, 'feqmptd', [ff], 'F = ( t e. RR+ |-> ( F ` t ) )')
    A1 = '( %s /\\ t e. RR+ )' % ph
    P2 = pow2t('t'); PD = '( %s ^c D )' % P2; B = tail_b('t')
    r1 = D(w, ph, 'rlimcxp', [cst(w, A1, 'ovex', '%s e. _V' % P2), cst(w, ph, 'z6e4lim', '( t e. RR+ |-> %s ) ~~>r 0' % P2), dp], '( t e. RR+ |-> %s ) ~~>r 0' % PD)
    cc = D(w, ph, 'recnd', [cr], 'C e. CC')
    r2 = D(w, ph, 'syl2anc', [cst(w, ph, 'rpssre', 'RR+ C_ RR'), cc, w.inst('rlimconst')], '( t e. RR+ |-> C ) ~~>r C')
    tp = w.s([], 'simpr', '( %s -> t e. RR+ )' % A1)
    tr = D(w, A1, 'rpred', [tp], 't e. RR')
    ntr = D(w, A1, 'renegcld', [D(w, A1, 'rehalfcld', [tr], '( t / 2 ) e. RR')], '-u ( t / 2 ) e. RR') if False else None
    t4 = D(w, A1, 'redivcld', [tr, cst(w, A1, '4re', '4 e. RR'), cst(w, A1, '4ne0', '4 =/= 0')], '( t / 4 ) e. RR')
    nt4 = D(w, A1, 'renegcld', [t4], '-u ( t / 4 ) e. RR')
    p2 = D(w, A1, 'rpcxpcld', [cst(w, A1, '2rp', '2 e. RR+'), nt4], '%s e. RR+' % P2)
    dr1 = w.s([D(w, ph, 'rpred', [dp], 'D e. RR')], 'adantr', '( %s -> D e. RR )' % A1)
    pd = D(w, A1, 'rpcxpcld', [p2, dr1], '%s e. RR+' % PD)
    rm = D(w, ph, 'rlimmul', [w.s([cc], 'adantr', '( %s -> C e. CC )' % A1), D(w, A1, 'rpcnd', [pd], '%s e. CC' % PD), r2, r1],
           '( t e. RR+ |-> %s ) ~~>r ( C x. 0 )' % B)
    r0 = D(w, ph, 'breqtrd', [rm, D(w, ph, 'mul01d', [cc], '( C x. 0 ) = 0')], '( t e. RR+ |-> %s ) ~~>r 0' % B)
    cr1 = w.s([cr], 'adantr', '( %s -> C e. RR )' % A1)
    br = D(w, A1, 'remulcld', [cr1, D(w, A1, 'rpred', [pd], '%s e. RR' % PD)], '%s e. RR' % B)
    bc = D(w, A1, 'recnd', [br], '%s e. CC' % B)
    fc = D(w, A1, 'ffvelcdmd', [w.s([ff], 'adantr', '( %s -> F : RR+ --> CC )' % A1), tp], '( F ` t ) e. CC')
    A2 = '( %s /\\ ( t e. RR+ /\\ Y <_ t ) )' % ph
    E = 's = t'
    es = w.s([], 'id', '( %s -> %s )' % (E, E))
    Bs = tail_b('s')
    eb = D(w, E, 'oveq2d', [D(w, E, 'oveq1d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'oveq1d', [es], '( s / 4 ) = ( t / 4 )')], '-u ( s / 4 ) = -u ( t / 4 )')],
                                                             '%s = %s' % (pow2t('s'), P2))], '( %s ^c D ) = %s' % (pow2t('s'), PD))], '%s = %s' % (Bs, B))
    ea = D(w, E, 'fveq2d', [D(w, E, 'oveq1d', [D(w, E, 'fveq2d', [es], '( F ` s ) = ( F ` t )')], '( ( F ` s ) - L ) = ( ( F ` t ) - L )')],
           '( abs ` ( ( F ` s ) - L ) ) = ( abs ` ( ( F ` t ) - L ) )')
    sub = D(w, E, 'imbi12d', [w.s([], 'breq2', '( %s -> ( Y <_ s <-> Y <_ t ) )' % E),
                              D(w, E, 'breq12d', [ea, eb], '( ( abs ` ( ( F ` s ) - L ) ) <_ %s <-> ( abs ` ( ( F ` t ) - L ) ) <_ %s )' % (Bs, B))],
            '( ( Y <_ s -> ( abs ` ( ( F ` s ) - L ) ) <_ %s ) <-> ( Y <_ t -> ( abs ` ( ( F ` t ) - L ) ) <_ %s ) )' % (Bs, B))
    tp2 = w.s([], 'simprl', '( %s -> t e. RR+ )' % A2)
    hb2 = w.s([hb], 'adantr', '( %s -> %s )' % (A2, HB))
    it = w.s([sub, hb2, tp2], 'rspcdva', '( %s -> ( Y <_ t -> ( abs ` ( ( F ` t ) - L ) ) <_ %s ) )' % (A2, B))
    le1 = D(w, A2, 'mpd', [w.s([], 'simprr', '( %s -> Y <_ t )' % A2), it], '( abs ` ( ( F ` t ) - L ) ) <_ %s' % B)
    lift = lambda st, f: w.s([w.s([st], 'adantrr', '( %s -> %s )' % (A2, f)) if False else st], 'idi', '( %s -> %s )' % (A2, f))
    A2t = '( ( %s /\\ t e. RR+ ) /\\ Y <_ t )' % ph
    br2 = w.s([br], 'adantrr', '( %s -> %s e. RR )' % (A2, B))
    bc2 = w.s([bc], 'adantrr', '( %s -> %s e. CC )' % (A2, B))
    fc2 = w.s([fc], 'adantrr', '( %s -> ( F ` t ) e. CC )' % A2)
    lc2 = w.s([lc], 'adantr', '( %s -> L e. CC )' % A2)
    fl = D(w, A2, 'subcld', [fc2, lc2], '( ( F ` t ) - L ) e. CC')
    le2 = D(w, A2, 'letrd', [D(w, A2, 'abscld', [fl], '( abs ` ( ( F ` t ) - L ) ) e. RR'), br2, D(w, A2, 'abscld', [bc2], '( abs ` %s ) e. RR' % B), le1, D(w, A2, 'leabsd', [br2], '%s <_ ( abs ` %s )' % (B, B))],
             '( abs ` ( ( F ` t ) - L ) ) <_ ( abs ` %s )' % B)
    le3 = D(w, A2, 'breqtrrd', [le2, D(w, A2, 'fveq2d', [D(w, A2, 'subid1d', [bc2], '( %s - 0 ) = %s' % (B, B))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (B, B))],
            '( abs ` ( ( F ` t ) - L ) ) <_ ( abs ` ( %s - 0 ) )' % B)
    sq = w.s([yr, lc, r0, bc, fc, le3], 'rlimsqzlem', '( %s -> ( t e. RR+ |-> ( F ` t ) ) ~~>r L )' % ph)
    w.qed([feq, sq], 'eqbrtrd', S['zl3tl'])
    go(w, only)


# ---------------------------------------------------------------- zl3lod
if __name__ == '__main__' and (not only or 'zl3lod' in only):
    w = W('zl3lod', 'The integral of an odd function over a segment symmetric about ` 0 ` vanishes.')
    ph, concl = ante_of(S['zl3lod'])
    ac = w.s([], 'simpll', '( %s -> A e. CC )' % ph)
    gc = w.s([], 'simplr', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    ODD = 'A. y e. CC ( G ` -u y ) = -u ( G ` y )'
    od = w.s([], 'simpr', '( %s -> %s )' % (ph, ODD))
    nac = D(w, ph, 'negcld', [ac], '-u A e. CC')
    NA = '-u A'
    css = D(w, ph, 'syl2anc', [nac, ac, w.inst('csegcl')], '( -u A cseg A ) C_ CC')
    X = LI('G', NA, 'A'); Y = LI('G', 'A', NA)
    l1 = D(w, ph, 'syl', [w.s([w.s([nac, ac], 'jca', '( %s -> ( -u A e. CC /\\ A e. CC ) )' % ph), w.s([gc, css], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ ( -u A cseg A ) C_ CC ) )' % ph)],
                                 'jca', '( %s -> ( ( -u A e. CC /\\ A e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( -u A cseg A ) C_ CC ) ) )' % ph), w.inst('lintrev')], '%s = -u %s' % (Y, X))
    gv = D(w, ph, 'elexd', [gc], 'G e. _V')
    V1 = 'S. ( 0 (,) 1 ) ( ( G ` ( A + ( t x. ( -u A - A ) ) ) ) x. ( -u A - A ) ) _d t'
    V2 = 'S. ( 0 (,) 1 ) ( ( G ` ( -u A + ( t x. ( A - -u A ) ) ) ) x. ( A - -u A ) ) _d t'
    y1 = D(w, ph, 'syl3anc', [gv, ac, nac, w.inst('lintval')], '%s = %s' % (Y, V1))
    x1 = D(w, ph, 'syl3anc', [gv, nac, ac, w.inst('lintval')], '%s = %s' % (X, V2))
    A1 = '( %s /\\ t e. ( 0 (,) 1 ) )' % ph
    tc = w.s([w.s([w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % A1), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % A1)], 'recnd', '( %s -> t e. CC )' % A1)
    a1 = w.s([ac], 'adantr', '( %s -> A e. CC )' % A1); na1 = w.s([nac], 'adantr', '( %s -> -u A e. CC )' % A1)
    AA = '( A - -u A )'; TA = '( t x. %s )' % AA; U = '( -u A + %s )' % TA
    aac = D(w, A1, 'subcld', [a1, na1], '%s e. CC' % AA); tac = D(w, A1, 'mulcld', [tc, aac], '%s e. CC' % TA)
    uc = D(w, A1, 'addcld', [na1, tac], '%s e. CC' % U)
    n1 = D(w, A1, 'negdid', [na1, tac], '-u %s = ( -u -u A + -u %s )' % (U, TA))
    n2 = D(w, A1, 'oveq1d', [D(w, A1, 'negnegd', [a1], '-u -u A = A')], '( -u -u A + -u %s ) = ( A + -u %s )' % (TA, TA))
    n3 = D(w, A1, 'oveq2d', [D(w, A1, 'eqcomd', [D(w, A1, 'mulneg2d', [tc, aac], '( t x. -u %s ) = -u %s' % (AA, TA))], '-u %s = ( t x. -u %s )' % (TA, AA))],
           '( A + -u %s ) = ( A + ( t x. -u %s ) )' % (TA, AA))
    nd = D(w, A1, 'negsubdi2d', [a1, na1], '-u %s = ( -u A - A )' % AA)
    n4 = D(w, A1, 'oveq2d', [D(w, A1, 'oveq2d', [nd], '( t x. -u %s ) = ( t x. ( -u A - A ) )' % AA)], '( A + ( t x. -u %s ) ) = ( A + ( t x. ( -u A - A ) ) )' % AA)
    nu = D(w, A1, 'eqtrd', [D(w, A1, 'eqtrd', [D(w, A1, 'eqtrd', [n1, n2], '-u %s = ( A + -u %s )' % (U, TA)), n3], '-u %s = ( A + ( t x. -u %s ) )' % (U, AA)), n4],
           '-u %s = ( A + ( t x. ( -u A - A ) ) )' % U)
    E = 'y = %s' % U
    ey = w.s([], 'id', '( %s -> %s )' % (E, E))
    sub = D(w, E, 'eqeq12d', [D(w, E, 'fveq2d', [D(w, E, 'negeqd', [ey], '-u y = -u %s' % U)], '( G ` -u y ) = ( G ` -u %s )' % U),
                              D(w, E, 'negeqd', [D(w, E, 'fveq2d', [ey], '( G ` y ) = ( G ` %s )' % U)], '-u ( G ` y ) = -u ( G ` %s )' % U)],
            '( ( G ` -u y ) = -u ( G ` y ) <-> ( G ` -u %s ) = -u ( G ` %s ) )' % (U, U))
    oddu = w.s([sub, w.s([od], 'adantr', '( %s -> %s )' % (A1, ODD)), uc], 'rspcdva', '( %s -> ( G ` -u %s ) = -u ( G ` %s ) )' % (A1, U, U))
    g1 = D(w, A1, 'eqtr3d', [D(w, A1, 'fveq2d', [nu], '( G ` -u %s ) = ( G ` ( A + ( t x. ( -u A - A ) ) ) )' % U), oddu],
           '( G ` ( A + ( t x. ( -u A - A ) ) ) ) = -u ( G ` %s )' % U)
    p1 = D(w, A1, 'oveq12d', [g1, D(w, A1, 'eqcomd', [nd], '( -u A - A ) = -u %s' % AA)], '( ( G ` ( A + ( t x. ( -u A - A ) ) ) ) x. ( -u A - A ) ) = ( -u ( G ` %s ) x. -u %s )' % (U, AA))
    guc = D(w, A1, 'ffvelcdmd', [w.s([w.s([gc], 'adantr', '( %s -> G e. ( CC -cn-> CC ) )' % A1), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % A1), uc], '( G ` %s ) e. CC' % U)
    p2 = D(w, A1, 'mul2negd', [guc, aac], '( -u ( G ` %s ) x. -u %s ) = ( ( G ` %s ) x. %s )' % (U, AA, U, AA))
    pt = D(w, A1, 'eqtrd', [p1, p2], '( ( G ` ( A + ( t x. ( -u A - A ) ) ) ) x. ( -u A - A ) ) = ( ( G ` %s ) x. %s )' % (U, AA))
    ig = w.s([pt], 'itgeq2dv', '( %s -> %s = %s )' % (ph, V1, V2))
    yx = D(w, ph, 'eqtr4d', [D(w, ph, 'eqtrd', [y1, ig], '%s = %s' % (Y, V2)), x1], '%s = %s' % (Y, X))
    xx = D(w, ph, 'eqtr3d', [yx, l1], '%s = -u %s' % (X, X))
    xc = D(w, ph, 'syl', [w.s([w.s([nac, ac], 'jca', '( %s -> ( -u A e. CC /\\ A e. CC ) )' % ph), w.s([gc, css], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ ( -u A cseg A ) C_ CC ) )' % ph)],
                               'jca', '( %s -> ( ( -u A e. CC /\\ A e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( -u A cseg A ) C_ CC ) ) )' % ph), w.inst('lintcl')], '%s e. CC' % X)
    w.qed([xx, D(w, ph, 'eqnegd', [xc], '( %s = -u %s <-> %s = 0 )' % (X, X, X))], 'mpbid', S['zl3lod'])
    go(w, only)


# ---------------------------------------------------------------- zl3lsc
if __name__ == '__main__' and (not only or 'zl3lsc' in only):
    w = W('zl3lsc', 'Scaling the variable of the integrand scales the segment.')
    ph, concl = ante_of(S['zl3lsc'])
    pc = w.s([], 'simp1l', '( %s -> P e. CC )' % ph); qc = w.s([], 'simp1r', '( %s -> Q e. CC )' % ph)
    lc = w.s([], 'simp2l', '( %s -> L e. CC )' % ph); ln = w.s([], 'simp2r', '( %s -> L =/= 0 )' % ph)
    gc = w.s([], 'simp3', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    F1 = '( y e. CC |-> ( G ` ( L x. y ) ) )'
    LP, LQ = '( L x. P )', '( L x. Q )'
    lpc = D(w, ph, 'mulcld', [lc, pc], '%s e. CC' % LP); lqc = D(w, ph, 'mulcld', [lc, qc], '%s e. CC' % LQ)
    QP = '( Q - P )'; QL = '( %s - %s )' % (LQ, LP)
    I1 = 'S. ( 0 (,) 1 ) ( ( %s ` ( P + ( t x. %s ) ) ) x. %s ) _d t' % (F1, QP, QP)
    BG = '( ( G ` ( %s + ( t x. %s ) ) ) x. %s )' % (LP, QL, QL)
    I2 = 'S. ( 0 (,) 1 ) %s _d t' % BG
    l1 = D(w, ph, 'syl3anc', [cst(w, ph, 'mptex', '%s e. _V' % F1), pc, qc, w.inst('lintval')], '%s = %s' % (LI(F1, 'P', 'Q'), I1))
    gv = D(w, ph, 'elexd', [gc], 'G e. _V')
    l2 = D(w, ph, 'syl3anc', [gv, lpc, lqc, w.inst('lintval')], '%s = %s' % (LI('G', LP, LQ), I2))
    css = D(w, ph, 'syl2anc', [lpc, lqc, w.inst('csegcl')], '( %s cseg %s ) C_ CC' % (LP, LQ))
    ib = D(w, ph, 'syl', [w.s([w.s([lpc, lqc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, LP, LQ)), w.s([gc, css], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (ph, LP, LQ))],
                              'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (ph, LP, LQ, LP, LQ)), w.inst('lintibl')],
           '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % BG)
    A1 = '( %s /\\ t e. ( 0 (,) 1 ) )' % ph
    tc = w.s([w.s([w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % A1), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % A1)], 'recnd', '( %s -> t e. CC )' % A1)
    p1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1); q1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
    l1c = w.s([lc], 'adantr', '( %s -> L e. CC )' % A1); ln1 = w.s([ln], 'adantr', '( %s -> L =/= 0 )' % A1)
    gf = w.s([w.s([gc], 'adantr', '( %s -> G e. ( CC -cn-> CC ) )' % A1), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % A1)
    qpc = D(w, A1, 'subcld', [q1, p1], '%s e. CC' % QP)
    TQ = '( t x. %s )' % QP; X = '( P + %s )' % TQ
    tqc = D(w, A1, 'mulcld', [tc, qpc], '%s e. CC' % TQ); xc = D(w, A1, 'addcld', [p1, tqc], '%s e. CC' % X)
    LX = '( L x. %s )' % X
    E = 'y = %s' % X
    ey = w.s([], 'id', '( %s -> %s )' % (E, E))
    sb = D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [ey], '( L x. y ) = %s' % LX)], '( G ` ( L x. y ) ) = ( G ` %s )' % LX)
    fv = w.s([xc, w.s([sb, w.s([], 'eqid', '%s = %s' % (F1, F1)), w.s([], 'fvex', '( G ` %s ) e. _V' % LX)], 'fvmpt', '( %s e. CC -> ( %s ` %s ) = ( G ` %s ) )' % (X, F1, X, LX))],
             'syl', '( %s -> ( %s ` %s ) = ( G ` %s ) )' % (A1, F1, X, LX))
    lp1 = w.s([lpc], 'adantr', '( %s -> %s e. CC )' % (A1, LP)); lq1 = w.s([lqc], 'adantr', '( %s -> %s e. CC )' % (A1, LQ))
    sd = D(w, A1, 'subdid', [l1c, q1, p1], '( L x. %s ) = %s' % (QP, QL))
    a1 = D(w, A1, 'adddid', [l1c, p1, tqc], '%s = ( %s + ( L x. %s ) )' % (LX, LP, TQ))
    a2 = D(w, A1, 'mul12d', [l1c, tc, qpc], '( L x. %s ) = ( t x. ( L x. %s ) )' % (TQ, QP))
    a3 = D(w, A1, 'oveq2d', [sd], '( t x. ( L x. %s ) ) = ( t x. %s )' % (QP, QL))
    arg = D(w, A1, 'eqtrd', [a1, D(w, A1, 'oveq2d', [D(w, A1, 'eqtrd', [a2, a3], '( L x. %s ) = ( t x. %s )' % (TQ, QL))], '( %s + ( L x. %s ) ) = ( %s + ( t x. %s ) )' % (LP, TQ, LP, QL))],
            '%s = ( %s + ( t x. %s ) )' % (LX, LP, QL))
    GV = '( G ` ( %s + ( t x. %s ) ) )' % (LP, QL)
    g1 = D(w, A1, 'eqtrd', [fv, D(w, A1, 'fveq2d', [arg], '( G ` %s ) = %s' % (LX, GV))], '( %s ` %s ) = %s' % (F1, X, GV))
    gvc = D(w, A1, 'ffvelcdmd', [gf, D(w, A1, 'addcld', [lp1, D(w, A1, 'mulcld', [tc, D(w, A1, 'subcld', [lq1, lp1], '%s e. CC' % QL)], '( t x. %s ) e. CC' % QL)], '( %s + ( t x. %s ) ) e. CC' % (LP, QL))],
              '%s e. CC' % GV)
    RL = '( 1 / L )'
    rlc = D(w, A1, 'reccld', [l1c, ln1], '%s e. CC' % RL)
    # ( 1 / L ) x. ( GV x. QL ) = GV x. QP
    r1 = D(w, A1, 'mul12d', [rlc, gvc, D(w, A1, 'subcld', [lq1, lp1], '%s e. CC' % QL)], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (RL, BG, GV, RL, QL))
    r2 = D(w, A1, 'oveq2d', [D(w, A1, 'eqcomd', [sd], '%s = ( L x. %s )' % (QL, QP))], '( %s x. %s ) = ( %s x. ( L x. %s ) )' % (RL, QL, RL, QP))
    r3 = D(w, A1, 'eqtr3d', [D(w, A1, 'mulassd', [rlc, l1c, qpc], '( ( %s x. L ) x. %s ) = ( %s x. ( L x. %s ) )' % (RL, QP, RL, QP)),
                             D(w, A1, 'eqtrd', [D(w, A1, 'oveq1d', [D(w, A1, 'recid2d', [l1c, ln1], '( %s x. L ) = 1' % RL)], '( ( %s x. L ) x. %s ) = ( 1 x. %s )' % (RL, QP, QP)),
                                                D(w, A1, 'mullidd', [qpc], '( 1 x. %s ) = %s' % (QP, QP))], '( ( %s x. L ) x. %s ) = %s' % (RL, QP, QP))],
            '( %s x. ( L x. %s ) ) = %s' % (RL, QP, QP))
    r4 = D(w, A1, 'eqtrd', [r2, r3], '( %s x. %s ) = %s' % (RL, QL, QP))
    rr = D(w, A1, 'eqtrd', [r1, D(w, A1, 'oveq2d', [r4], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (GV, RL, QL, GV, QP))], '( %s x. %s ) = ( %s x. %s )' % (RL, BG, GV, QP))
    pt = D(w, A1, 'eqtr4d', [D(w, A1, 'oveq1d', [g1], '( ( %s ` %s ) x. %s ) = ( %s x. %s )' % (F1, X, QP, GV, QP)), rr],
           '( ( %s ` %s ) x. %s ) = ( %s x. %s )' % (F1, X, QP, RL, BG))
    ig = w.s([pt], 'itgeq2dv', '( %s -> %s = S. ( 0 (,) 1 ) ( %s x. %s ) _d t )' % (ph, I1, RL, BG))
    bgc = D(w, A1, 'mulcld', [gvc, D(w, A1, 'subcld', [lq1, lp1], '%s e. CC' % QL)], '%s e. CC' % BG)
    rlc0 = D(w, ph, 'reccld', [lc, ln], '%s e. CC' % RL)
    im = w.s([rlc0, bgc, ib], 'itgmulc2', '( %s -> ( %s x. %s ) = S. ( 0 (,) 1 ) ( %s x. %s ) _d t )' % (ph, RL, I2, RL, BG))
    i2c = D(w, ph, 'syl', [w.s([w.s([lpc, lqc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, LP, LQ)), w.s([gc, css], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (ph, LP, LQ))],
                               'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (ph, LP, LQ, LP, LQ)), w.inst('lintcl')], '%s e. CC' % LI('G', LP, LQ))
    dv = D(w, ph, 'divrec2d', [i2c, lc, ln], '( %s / L ) = ( %s x. %s )' % (LI('G', LP, LQ), RL, LI('G', LP, LQ)))
    dv2 = D(w, ph, 'eqtrd', [dv, D(w, ph, 'oveq2d', [l2], '( %s x. %s ) = ( %s x. %s )' % (RL, LI('G', LP, LQ), RL, I2))], '( %s / L ) = ( %s x. %s )' % (LI('G', LP, LQ), RL, I2))
    w.qed([D(w, ph, 'eqtrd', [l1, ig], '%s = S. ( 0 (,) 1 ) ( %s x. %s ) _d t' % (LI(F1, 'P', 'Q'), RL, BG)), D(w, ph, 'eqtrd', [dv2, im], '( %s / L ) = S. ( 0 (,) 1 ) ( %s x. %s ) _d t' % (LI('G', LP, LQ), RL, BG))],
          'eqtr4d', S['zl3lsc'])
    go(w, only)


# ---------------------------------------------------------------- zl3v2
def seg_pre(w, A_, P, Q, pc, qc, gc):
    """( A_ -> ( ( P e. CC /\\ Q e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( P cseg Q ) C_ CC ) ) )"""
    css = D(w, A_, 'syl2anc', [pc, qc, w.inst('csegcl')], '( %s cseg %s ) C_ CC' % (P, Q))
    return w.s([w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A_, P, Q)), w.s([gc, css], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (A_, P, Q))],
               'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (A_, P, Q, P, Q))


if __name__ == '__main__' and (not only or 'zl3v2' in only):
    w = W('zl3v2', 'Splitting a vertical segment at an intermediate height.')
    ph, concl = ante_of(S['zl3v2'])
    cr = w.s([], 'simpll', '( %s -> C e. RR )' % ph); gc = w.s([], 'simplr', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    ur = w.s([], 'simprl1', '( %s -> U e. RR )' % ph); vr = w.s([], 'simprl2', '( %s -> V e. RR )' % ph); wr = w.s([], 'simprl3', '( %s -> W e. RR )' % ph)
    uv = w.s([], 'simprr1', '( %s -> U <_ V )' % ph); vw = w.s([], 'simprr2', '( %s -> V <_ W )' % ph); uw = w.s([], 'simprr3', '( %s -> U < W )' % ph)
    cc = D(w, ph, 'recnd', [cr], 'C e. CC'); uc = D(w, ph, 'recnd', [ur], 'U e. CC'); vc = D(w, ph, 'recnd', [vr], 'V e. CC'); wc = D(w, ph, 'recnd', [wr], 'W e. CC')
    ic = cst(w, ph, 'ax-icn', '_i e. CC')
    PU, PV, PW = CP('C', 'U'), CP('C', 'V'), CP('C', 'W')
    iu = D(w, ph, 'mulcld', [ic, uc], '( _i x. U ) e. CC'); iv = D(w, ph, 'mulcld', [ic, vc], '( _i x. V ) e. CC'); iw = D(w, ph, 'mulcld', [ic, wc], '( _i x. W ) e. CC')
    puc = D(w, ph, 'addcld', [cc, iu], '%s e. CC' % PU); pwc = D(w, ph, 'addcld', [cc, iw], '%s e. CC' % PW)
    WU = '( W - U )'; VU = '( V - U )'; SS = '( %s / %s )' % (VU, WU)
    wu0 = D(w, ph, 'mpbid', [uw, D(w, ph, 'posdifd', [ur, wr], '( U < W <-> 0 < %s )' % WU)], '0 < %s' % WU)
    wur = D(w, ph, 'resubcld', [wr, ur], '%s e. RR' % WU); vur = D(w, ph, 'resubcld', [vr, ur], '%s e. RR' % VU)
    wup = D(w, ph, 'elrpd', [wur, wu0], '%s e. RR+' % WU)
    sr = D(w, ph, 'redivcld', [vur, wur, D(w, ph, 'gt0ne0d', [wu0], '%s =/= 0' % WU)], '%s e. RR' % SS)
    vu0 = D(w, ph, 'subge0d', [vr, ur], '( 0 <_ %s <-> U <_ V )' % VU)
    s0 = D(w, ph, 'divge0d', [vur, wup, D(w, ph, 'mpbird', [uv, vu0], '0 <_ %s' % VU)], '0 <_ %s' % SS)
    vw2 = D(w, ph, 'lesub1d', [vr, wr, ur], '( V <_ W <-> %s <_ %s )' % (VU, WU))
    s1 = D(w, ph, 'mpbird', [D(w, ph, 'mpbid', [vw, vw2], '%s <_ %s' % (VU, WU)), D(w, ph, 'syl2anc', [vur, wup, w.inst('divle1le')], '( %s <_ 1 <-> %s <_ %s )' % (SS, VU, WU))], '%s <_ 1' % SS)
    sin = D(w, ph, 'mpbir', [w.s([sr, s0, s1], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (ph, SS, SS, SS))], '%s e. ( 0 [,] 1 )' % SS) if False else None
    sin = w.s([w.s([sr, s0, s1], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (ph, SS, SS, SS)), w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (SS, SS, SS, SS))],
              'sylibr', '( %s -> %s e. ( 0 [,] 1 ) )' % (ph, SS))
    # PV = PU + SS x. ( PW - PU )
    wuc = D(w, ph, 'recnd', [wur], '%s e. CC' % WU); vuc = D(w, ph, 'recnd', [vur], '%s e. CC' % VU)
    d1 = D(w, ph, 'pnpcand', [cc, iw, iu], '( %s - %s ) = ( ( _i x. W ) - ( _i x. U ) )' % (PW, PU))
    d2 = D(w, ph, 'eqtr4d', [d1, D(w, ph, 'subdid', [ic, wc, uc], '( _i x. %s ) = ( ( _i x. W ) - ( _i x. U ) )' % WU)], '( %s - %s ) = ( _i x. %s )' % (PW, PU, WU))
    m1 = D(w, ph, 'oveq2d', [d2], '( %s x. ( %s - %s ) ) = ( %s x. ( _i x. %s ) )' % (SS, PW, PU, SS, WU))
    ssc = D(w, ph, 'recnd', [sr], '%s e. CC' % SS)
    m2 = D(w, ph, 'mul12d', [ssc, ic, wuc], '( %s x. ( _i x. %s ) ) = ( _i x. ( %s x. %s ) )' % (SS, WU, SS, WU))
    m3 = D(w, ph, 'oveq2d', [D(w, ph, 'divcan1d', [vuc, wuc, D(w, ph, 'gt0ne0d', [wu0], '%s =/= 0' % WU)], '( %s x. %s ) = %s' % (SS, WU, VU))], '( _i x. ( %s x. %s ) ) = ( _i x. %s )' % (SS, WU, VU))
    mm = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [m1, m2], '( %s x. ( %s - %s ) ) = ( _i x. ( %s x. %s ) )' % (SS, PW, PU, SS, WU)), m3], '( %s x. ( %s - %s ) ) = ( _i x. %s )' % (SS, PW, PU, VU))
    e1 = D(w, ph, 'oveq2d', [mm], '( %s + ( %s x. ( %s - %s ) ) ) = ( %s + ( _i x. %s ) )' % (PU, SS, PW, PU, PU, VU))
    ivu = D(w, ph, 'mulcld', [ic, vuc], '( _i x. %s ) e. CC' % VU)
    e2 = D(w, ph, 'addassd', [cc, iu, ivu], '( %s + ( _i x. %s ) ) = ( C + ( ( _i x. U ) + ( _i x. %s ) ) )' % (PU, VU, VU))
    e3 = D(w, ph, 'eqtr4d', [D(w, ph, 'eqtr4d', [D(w, ph, 'oveq2d', [D(w, ph, 'pncan3d', [uc, vc], '( U + %s ) = V' % VU)], '( _i x. ( U + %s ) ) = ( _i x. V )' % VU),
                                                  D(w, ph, 'adddid', [ic, uc, vuc], '( _i x. ( U + %s ) ) = ( ( _i x. U ) + ( _i x. %s ) )' % (VU, VU))], '( ( _i x. U ) + ( _i x. %s ) ) = ( _i x. V )' % VU) if False else
                             D(w, ph, 'eqtr3d', [D(w, ph, 'adddid', [ic, uc, vuc], '( _i x. ( U + %s ) ) = ( ( _i x. U ) + ( _i x. %s ) )' % (VU, VU)),
                                                 D(w, ph, 'oveq2d', [D(w, ph, 'pncan3d', [uc, vc], '( U + %s ) = V' % VU)], '( _i x. ( U + %s ) ) = ( _i x. V )' % VU)],
                               '( ( _i x. U ) + ( _i x. %s ) ) = ( _i x. V )' % VU), w.s([], 'eqid', '( _i x. V ) = ( _i x. V )') if False else D(w, ph, 'eqid', [], '( _i x. V ) = ( _i x. V )')],
            '( ( _i x. U ) + ( _i x. %s ) ) = ( _i x. V )' % VU) if False else None
    e3 = D(w, ph, 'eqtr3d', [D(w, ph, 'adddid', [ic, uc, vuc], '( _i x. ( U + %s ) ) = ( ( _i x. U ) + ( _i x. %s ) )' % (VU, VU)),
                             D(w, ph, 'oveq2d', [D(w, ph, 'pncan3d', [uc, vc], '( U + %s ) = V' % VU)], '( _i x. ( U + %s ) ) = ( _i x. V )' % VU)],
            '( ( _i x. U ) + ( _i x. %s ) ) = ( _i x. V )' % VU)
    e4 = D(w, ph, 'oveq2d', [e3], '( C + ( ( _i x. U ) + ( _i x. %s ) ) ) = %s' % (VU, PV))
    ceq = D(w, ph, 'eqtr4d', [w.s([], 'eqid', '%s = %s' % (PV, PV)) if False else D(w, ph, 'eqidd', [], '%s = %s' % (PV, PV)),
                              D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [e1, e2], '( %s + ( %s x. ( %s - %s ) ) ) = ( C + ( ( _i x. U ) + ( _i x. %s ) ) )' % (PU, SS, PW, PU, VU)), e4],
                                '( %s + ( %s x. ( %s - %s ) ) ) = %s' % (PU, SS, PW, PU, PV))], '%s = ( %s + ( %s x. ( %s - %s ) ) )' % (PV, PU, SS, PW, PU))
    pre = seg_pre(w, ph, PU, PW, puc, pwc, gc)
    w.qed([w.s([pre, sin, ceq], '3jca', '( %s -> ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) /\\ %s e. ( 0 [,] 1 ) /\\ %s = ( %s + ( %s x. ( %s - %s ) ) ) ) )'
                  % (ph, PU, PW, PU, PW, SS, PV, PU, SS, PW, PU)), w.inst('lintsplit')], 'syl', S['zl3v2'])
    go(w, only)


# ---------------------------------------------------------------- zl3epc
def bl_at(w, A_, bl, C, bexpr, br, Mv='M', G='G'):
    """( A_ -> ( abs ` ( G ` ( C + ( _i x. b' ) ) ) ) <_ ( M x. ( 2 ^c -u ( abs ` b' ) ) ) ) from bl: ( A_ -> A. b e. RR ... )"""
    E = 'b = %s' % bexpr
    eb = w.s([], 'id', '( %s -> %s )' % (E, E))
    L = lambda b: '( abs ` ( %s ` %s ) )' % (G, CP(C, b)); R = lambda b: '( %s x. ( 2 ^c -u ( abs ` %s ) ) )' % (Mv, b)
    sub = D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [eb], '( _i x. b ) = ( _i x. %s )' % bexpr)], '%s = %s' % (CP(C, 'b'), CP(C, bexpr)))],
                                                             '( %s ` %s ) = ( %s ` %s )' % (G, CP(C, 'b'), G, CP(C, bexpr)))], '%s = %s' % (L('b'), L(bexpr))),
                               D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [eb], '( abs ` b ) = ( abs ` %s )' % bexpr)], '-u ( abs ` b ) = -u ( abs ` %s )' % bexpr)],
                                                                  '( 2 ^c -u ( abs ` b ) ) = ( 2 ^c -u ( abs ` %s ) )' % bexpr)], '%s = %s' % (R('b'), R(bexpr)))],
            '( %s <_ %s <-> %s <_ %s )' % (L('b'), R('b'), L(bexpr), R(bexpr)))
    return w.s([sub, bl, br], 'rspcdva', '( %s -> %s <_ %s )' % (A_, L(bexpr), R(bexpr)))


def m_nonneg(w, A_, bl, C, cc, gf, Mv='M', G='G'):
    """( A_ -> 0 <_ M ) from the line bound at b = 0"""
    z0 = cst(w, A_, '0re', '0 e. RR')
    b0 = bl_at(w, A_, bl, C, '0', z0, Mv, G)
    one = D(w, A_, 'eqtrd', [D(w, A_, 'oveq2d', [D(w, A_, 'eqtrd', [D(w, A_, 'negeqd', [cst(w, A_, 'abs0', '( abs ` 0 ) = 0')], '-u ( abs ` 0 ) = -u 0'), cst(w, A_, 'neg0', '-u 0 = 0')], '-u ( abs ` 0 ) = 0')],
                                            '( 2 ^c -u ( abs ` 0 ) ) = ( 2 ^c 0 )'), w.s([cst(w, A_, '2cn', '2 e. CC'), w.inst('cxp0')], 'syl', '( %s -> ( 2 ^c 0 ) = 1 )' % A_)], '( 2 ^c -u ( abs ` 0 ) ) = 1')
    mm = D(w, A_, 'eqtrd', [D(w, A_, 'oveq2d', [one], '( %s x. ( 2 ^c -u ( abs ` 0 ) ) ) = ( %s x. 1 )' % (Mv, Mv)), D(w, A_, 'mulridd', [D(w, A_, 'recnd', [w.s([], 'IDX', 'x')], '%s e. CC' % Mv) if False else None], 'x') if False else None], 'x') if False else None
    mr = None
    return b0, one


if __name__ == '__main__' and (not only or 'zl3epc' in only):
    w = W('zl3epc', 'A vertical segment on which ` | Im | >_ H ` contributes at most ` M 2 ^ -H ` times its length.')
    ph, concl = ante_of(S['zl3epc'])
    cr = w.s([], 'simplll', '( %s -> C e. RR )' % ph); gc = w.s([], 'simpllr', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    mr = w.s([], 'simplrl', '( %s -> M e. RR )' % ph); bl = w.s([], 'simplrr', '( %s -> %s )' % (ph, BLC('C')))
    hr = w.s([], 'simprl1', '( %s -> H e. RR )' % ph); vr = w.s([], 'simprl2', '( %s -> V e. RR )' % ph); wr = w.s([], 'simprl3', '( %s -> W e. RR )' % ph)
    DJ = '( ( H <_ V /\\ H <_ W ) \\/ ( V <_ -u H /\\ W <_ -u H ) )'
    dj = w.s([], 'simprr', '( %s -> %s )' % (ph, DJ))
    cc = D(w, ph, 'recnd', [cr], 'C e. CC'); vc = D(w, ph, 'recnd', [vr], 'V e. CC'); wc = D(w, ph, 'recnd', [wr], 'W e. CC')
    ic = cst(w, ph, 'ax-icn', '_i e. CC')
    gf = w.s([gc, w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % ph)
    # 0 <_ M
    b0, one = m_nonneg(w, ph, bl, 'C', cc, gf)
    G0 = '( G ` %s )' % CP('C', '0')
    g0c = D(w, ph, 'ffvelcdmd', [gf, D(w, ph, 'addcld', [cc, D(w, ph, 'mulcld', [ic, cst(w, ph, '0cn', '0 e. CC')], '( _i x. 0 ) e. CC')], '%s e. CC' % CP('C', '0'))], '%s e. CC' % G0)
    mc = D(w, ph, 'recnd', [mr], 'M e. CC')
    mm = D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [one], '( M x. ( 2 ^c -u ( abs ` 0 ) ) ) = ( M x. 1 )'), D(w, ph, 'mulridd', [mc], '( M x. 1 ) = M')], '( M x. ( 2 ^c -u ( abs ` 0 ) ) ) = M')
    m0 = D(w, ph, 'letrd', [cst(w, ph, '0re', '0 e. RR'), D(w, ph, 'abscld', [g0c], '( abs ` %s ) e. RR' % G0), mr, D(w, ph, 'absge0d', [g0c], '0 <_ ( abs ` %s )' % G0),
                            D(w, ph, 'breqtrd', [b0, mm], '( abs ` %s ) <_ M' % G0)], '0 <_ M')
    PV_, PW_ = CP('C', 'V'), CP('C', 'W')
    pvc = D(w, ph, 'addcld', [cc, D(w, ph, 'mulcld', [ic, vc], '( _i x. V ) e. CC')], '%s e. CC' % PV_)
    pwc = D(w, ph, 'addcld', [cc, D(w, ph, 'mulcld', [ic, wc], '( _i x. W ) e. CC')], '%s e. CC' % PW_)
    MB = '( M x. ( 2 ^c -u H ) )'
    p2h = D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [hr], '-u H e. RR')], '( 2 ^c -u H ) e. RR+')
    mbr = D(w, ph, 'remulcld', [mr, D(w, ph, 'rpred', [p2h], '( 2 ^c -u H ) e. RR')], '%s e. RR' % MB)
    # pointwise bound
    A1 = '( %s /\\ z e. ( %s cseg %s ) )' % (ph, PV_, PW_)
    Z = '( %s + ( s x. ( %s - %s ) ) )' % (PV_, PW_, PV_)
    ex = w.s([w.s([], 'simpr', '( %s -> z e. ( %s cseg %s ) )' % (A1, PV_, PW_)), w.s([w.s([pvc, pwc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, PV_, PW_)), w.inst('csegel')], 'syl',
                                                                                           '( %s -> ( z e. ( %s cseg %s ) <-> E. s e. ( 0 [,] 1 ) z = %s ) )' % (ph, PV_, PW_, Z)) if False else
              w.s([w.s([w.s([pvc, pwc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, PV_, PW_)), w.inst('csegel')], 'syl', '( %s -> ( z e. ( %s cseg %s ) <-> E. s e. ( 0 [,] 1 ) z = %s ) )' % (ph, PV_, PW_, Z))],
                  'adantr', '( %s -> ( z e. ( %s cseg %s ) <-> E. s e. ( 0 [,] 1 ) z = %s ) )' % (A1, PV_, PW_, Z))], 'mpbid', '( %s -> E. s e. ( 0 [,] 1 ) z = %s )' % (A1, Z))
    A2 = '( %s /\\ ( s e. ( 0 [,] 1 ) /\\ z = %s ) )' % (A1, Z)
    lift = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A2, f))
    sI = w.s([], 'simprl', '( %s -> s e. ( 0 [,] 1 ) )' % A2)
    s01 = w.s([sI, w.s([], 'elicc01', '( s e. ( 0 [,] 1 ) <-> ( s e. RR /\\ 0 <_ s /\\ s <_ 1 ) )')], 'sylib', '( %s -> ( s e. RR /\\ 0 <_ s /\\ s <_ 1 ) )' % A2)
    sr = w.s([s01], 'simp1d', '( %s -> s e. RR )' % A2); s0 = w.s([s01], 'simp2d', '( %s -> 0 <_ s )' % A2); s1 = w.s([s01], 'simp3d', '( %s -> s <_ 1 )' % A2)
    cr2, vr2, wr2, hr2, mr2 = [lift(x, f) for x, f in [(cr, 'C e. RR'), (vr, 'V e. RR'), (wr, 'W e. RR'), (hr, 'H e. RR'), (mr, 'M e. RR')]]
    pvc2 = lift(pvc, '%s e. CC' % PV_); pwc2 = lift(pwc, '%s e. CC' % PW_)
    Y = '( V + ( s x. ( W - V ) ) )'
    im1 = D(w, A2, 'syl3anc', [pvc2, pwc2, sr, w.inst('cseglinim')], '( Im ` %s ) = ( ( Im ` %s ) + ( s x. ( ( Im ` %s ) - ( Im ` %s ) ) ) )' % (Z, PV_, PW_, PV_))
    imv = D(w, A2, 'crimd', [cr2, vr2], '( Im ` %s ) = V' % PV_); imw = D(w, A2, 'crimd', [cr2, wr2], '( Im ` %s ) = W' % PW_)
    im2 = D(w, A2, 'oveq12d', [imv, D(w, A2, 'oveq2d', [D(w, A2, 'oveq12d', [imw, imv], '( ( Im ` %s ) - ( Im ` %s ) ) = ( W - V )' % (PW_, PV_))], '( s x. ( ( Im ` %s ) - ( Im ` %s ) ) ) = ( s x. ( W - V ) )' % (PW_, PV_))],
             '( ( Im ` %s ) + ( s x. ( ( Im ` %s ) - ( Im ` %s ) ) ) ) = %s' % (PV_, PW_, PV_, Y))
    imz = D(w, A2, 'eqtrd', [im1, im2], '( Im ` %s ) = %s' % (Z, Y))
    re1 = D(w, A2, 'syl3anc', [pvc2, pwc2, sr, w.inst('cseglinre')], '( Re ` %s ) = ( ( Re ` %s ) + ( s x. ( ( Re ` %s ) - ( Re ` %s ) ) ) )' % (Z, PV_, PW_, PV_))
    rev = D(w, A2, 'crred', [cr2, vr2], '( Re ` %s ) = C' % PV_); rew = D(w, A2, 'crred', [cr2, wr2], '( Re ` %s ) = C' % PW_)
    cc2 = D(w, A2, 'recnd', [cr2], 'C e. CC'); sc2 = D(w, A2, 'recnd', [sr], 's e. CC')
    re2 = D(w, A2, 'oveq12d', [rev, D(w, A2, 'oveq2d', [D(w, A2, 'oveq12d', [rew, rev], '( ( Re ` %s ) - ( Re ` %s ) ) = ( C - C )' % (PW_, PV_))], '( s x. ( ( Re ` %s ) - ( Re ` %s ) ) ) = ( s x. ( C - C ) )' % (PW_, PV_))],
             '( ( Re ` %s ) + ( s x. ( ( Re ` %s ) - ( Re ` %s ) ) ) ) = ( C + ( s x. ( C - C ) ) )' % (PV_, PW_, PV_))
    re3 = D(w, A2, 'eqtrd', [D(w, A2, 'oveq2d', [D(w, A2, 'eqtrd', [D(w, A2, 'oveq2d', [D(w, A2, 'subidd', [cc2], '( C - C ) = 0')], '( s x. ( C - C ) ) = ( s x. 0 )'), D(w, A2, 'mul01d', [sc2], '( s x. 0 ) = 0')],
                                                                   '( s x. ( C - C ) ) = 0')], '( C + ( s x. ( C - C ) ) ) = ( C + 0 )'), D(w, A2, 'addridd', [cc2], '( C + 0 ) = C')], '( C + ( s x. ( C - C ) ) ) = C')
    rez = D(w, A2, 'eqtrd', [D(w, A2, 'eqtrd', [re1, re2], '( Re ` %s ) = ( C + ( s x. ( C - C ) ) )' % Z), re3], '( Re ` %s ) = C' % Z)
    zeq = w.s([], 'simprr', '( %s -> z = %s )' % (A2, Z))
    zc = D(w, A2, 'addcld', [pvc2, D(w, A2, 'mulcld', [sc2, D(w, A2, 'subcld', [pwc2, pvc2], '( %s - %s ) e. CC' % (PW_, PV_))], '( s x. ( %s - %s ) ) e. CC' % (PW_, PV_))], '%s e. CC' % Z)
    zr = D(w, A2, 'eqtrd', [D(w, A2, 'replimd', [zc], '%s = ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (Z, Z, Z)), D(w, A2, 'oveq12d', [rez, D(w, A2, 'oveq2d', [imz], '( _i x. ( Im ` %s ) ) = ( _i x. %s )' % (Z, Y))],
                                                                                                                              '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) = %s' % (Z, Z, CP('C', Y)))], '%s = %s' % (Z, CP('C', Y)))
    zz = D(w, A2, 'eqtrd', [zeq, zr], 'z = %s' % CP('C', Y))
    yr = D(w, A2, 'readdcld', [vr2, D(w, A2, 'remulcld', [sr, D(w, A2, 'resubcld', [wr2, vr2], '( W - V ) e. RR')], '( s x. ( W - V ) ) e. RR')], '%s e. RR' % Y)
    by = bl_at(w, A2, lift(bl, BLC('C')), 'C', Y, yr)
    # H <_ | Y |
    import lin
    one_s = D(w, A2, 'resubcld', [cst(w, A2, '1re', '1 e. RR'), sr], '( 1 - s ) e. RR')
    ms0 = D(w, A2, 'subge0d', [cst(w, A2, '1re', '1 e. RR'), sr], '( 0 <_ ( 1 - s ) <-> s <_ 1 )')
    os0 = D(w, A2, 'mpbird', [s1, ms0], '0 <_ ( 1 - s )')
    A3 = '( %s /\\ ( H <_ V /\\ H <_ W ) )' % A2
    A4 = '( %s /\\ ( V <_ -u H /\\ W <_ -u H ) )' % A2
    L3 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A3, f)); L4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A4, f))
    hv = w.s([], 'simprl', '( %s -> H <_ V )' % A3); hw = w.s([], 'simprr', '( %s -> H <_ W )' % A3)
    sr3, os3, s03, vr3, wr3, hr3, yr3 = L3(sr, 's e. RR'), L3(os0, '0 <_ ( 1 - s )'), L3(s0, '0 <_ s'), L3(vr2, 'V e. RR'), L3(wr2, 'W e. RR'), L3(hr2, 'H e. RR'), L3(yr, '%s e. RR' % Y)
    f1 = D(w, A3, 'mulge0d', [sr3, D(w, A3, 'resubcld', [wr3, hr3], '( W - H ) e. RR'), s03, D(w, A3, 'mpbird', [hw, D(w, A3, 'subge0d', [wr3, hr3], '( 0 <_ ( W - H ) <-> H <_ W )')], '0 <_ ( W - H )')], '0 <_ ( s x. ( W - H ) )')
    f2 = D(w, A3, 'mulge0d', [L3(one_s, '( 1 - s ) e. RR'), D(w, A3, 'resubcld', [vr3, hr3], '( V - H ) e. RR'), os3, D(w, A3, 'mpbird', [hv, D(w, A3, 'subge0d', [vr3, hr3], '( 0 <_ ( V - H ) <-> H <_ V )')], '0 <_ ( V - H )')],
           '0 <_ ( ( 1 - s ) x. ( V - H ) )')
    hy = lin.linarith(w, A3, [f1, f2], 'H <_ %s' % Y, leaves={'s': sr3, 'V': vr3, 'W': wr3, 'H': hr3}, products=True)
    ay3 = D(w, A3, 'letrd', [hr3, yr3, D(w, A3, 'abscld', [D(w, A3, 'recnd', [yr3], '%s e. CC' % Y)], '( abs ` %s ) e. RR' % Y), hy, D(w, A3, 'leabsd', [yr3], '%s <_ ( abs ` %s )' % (Y, Y))], 'H <_ ( abs ` %s )' % Y)
    vh = w.s([], 'simprl', '( %s -> V <_ -u H )' % A4); wh = w.s([], 'simprr', '( %s -> W <_ -u H )' % A4)
    sr4, os4, s04, vr4, wr4, hr4, yr4 = L4(sr, 's e. RR'), L4(os0, '0 <_ ( 1 - s )'), L4(s0, '0 <_ s'), L4(vr2, 'V e. RR'), L4(wr2, 'W e. RR'), L4(hr2, 'H e. RR'), L4(yr, '%s e. RR' % Y)
    nh4 = D(w, A4, 'renegcld', [hr4], '-u H e. RR')
    g1 = D(w, A4, 'mulge0d', [sr4, D(w, A4, 'resubcld', [nh4, wr4], '( -u H - W ) e. RR'), s04, D(w, A4, 'mpbird', [wh, D(w, A4, 'subge0d', [nh4, wr4], '( 0 <_ ( -u H - W ) <-> W <_ -u H )')], '0 <_ ( -u H - W )')],
           '0 <_ ( s x. ( -u H - W ) )')
    g2 = D(w, A4, 'mulge0d', [L4(one_s, '( 1 - s ) e. RR'), D(w, A4, 'resubcld', [nh4, vr4], '( -u H - V ) e. RR'), os4, D(w, A4, 'mpbird', [vh, D(w, A4, 'subge0d', [nh4, vr4], '( 0 <_ ( -u H - V ) <-> V <_ -u H )')], '0 <_ ( -u H - V )')],
           '0 <_ ( ( 1 - s ) x. ( -u H - V ) )')
    hy4 = lin.linarith(w, A4, [g1, g2], 'H <_ -u %s' % Y, leaves={'s': sr4, 'V': vr4, 'W': wr4, 'H': hr4}, products=True)
    yc4 = D(w, A4, 'recnd', [yr4], '%s e. CC' % Y)
    ay4 = D(w, A4, 'letrd', [hr4, D(w, A4, 'renegcld', [yr4], '-u %s e. RR' % Y), D(w, A4, 'abscld', [yc4], '( abs ` %s ) e. RR' % Y), hy4,
                             D(w, A4, 'breqtrd', [D(w, A4, 'leabsd', [D(w, A4, 'renegcld', [yr4], '-u %s e. RR' % Y)], '-u %s <_ ( abs ` -u %s )' % (Y, Y)), D(w, A4, 'absnegd', [yc4], '( abs ` -u %s ) = ( abs ` %s )' % (Y, Y))],
                               '-u %s <_ ( abs ` %s )' % (Y, Y))], 'H <_ ( abs ` %s )' % Y)
    ay = w.s([ay3, ay4, lift(dj, DJ)], 'mpjaodan', '( %s -> H <_ ( abs ` %s ) )' % (A2, Y))
    ayr = D(w, A2, 'abscld', [D(w, A2, 'recnd', [yr], '%s e. CC' % Y)], '( abs ` %s ) e. RR' % Y)
    pl = D(w, A2, 'cxplead', [cst(w, A2, '2re', '2 e. RR'), cst(w, A2, '1le2', '1 <_ 2'), D(w, A2, 'renegcld', [ayr], '-u ( abs ` %s ) e. RR' % Y), D(w, A2, 'renegcld', [hr2], '-u H e. RR'),
                               D(w, A2, 'mpbid', [ay, D(w, A2, 'lenegd', [hr2, ayr], '( H <_ ( abs ` %s ) <-> -u ( abs ` %s ) <_ -u H )' % (Y, Y))], '-u ( abs ` %s ) <_ -u H' % Y)],
            '( 2 ^c -u ( abs ` %s ) ) <_ ( 2 ^c -u H )' % Y)
    p2y = D(w, A2, 'rpcxpcld', [cst(w, A2, '2rp', '2 e. RR+'), D(w, A2, 'renegcld', [ayr], '-u ( abs ` %s ) e. RR' % Y)], '( 2 ^c -u ( abs ` %s ) ) e. RR+' % Y)
    ml = D(w, A2, 'lemul2ad', [D(w, A2, 'rpred', [p2y], '( 2 ^c -u ( abs ` %s ) ) e. RR' % Y), lift(D(w, ph, 'rpred', [p2h], '( 2 ^c -u H ) e. RR'), '( 2 ^c -u H ) e. RR'), mr2, lift(m0, '0 <_ M'), pl],
           '( M x. ( 2 ^c -u ( abs ` %s ) ) ) <_ %s' % (Y, MB))
    gz = D(w, A2, 'fveq2d', [D(w, A2, 'fveq2d', [zz], '( G ` z ) = ( G ` %s )' % CP('C', Y))], '( abs ` ( G ` z ) ) = ( abs ` ( G ` %s ) )' % CP('C', Y))
    gy = D(w, A2, 'eqbrtrd', [gz, D(w, A2, 'letrd', [D(w, A2, 'abscld', [D(w, A2, 'ffvelcdmd', [lift(gf, 'G : CC --> CC'), D(w, A2, 'eqeltrrd', [zz, D(w, A2, 'eleqtrd', [zc, D(w, A2, 'eqcomd', [zeq], '%s = z' % Z)], 'z e. CC')], '%s e. CC' % CP('C', Y)) if False else
                                                                                              D(w, A2, 'eqeltrrd', [zz, D(w, A2, 'eqeltrd', [zeq, zc], 'z e. CC')], '%s e. CC' % CP('C', Y))], '( G ` %s ) e. CC' % CP('C', Y))],
                                                                  '( abs ` ( G ` %s ) ) e. RR' % CP('C', Y)),
                                                      D(w, A2, 'remulcld', [mr2, D(w, A2, 'rpred', [p2y], '( 2 ^c -u ( abs ` %s ) ) e. RR' % Y)], '( M x. ( 2 ^c -u ( abs ` %s ) ) ) e. RR' % Y),
                                                      lift(mbr, '%s e. RR' % MB), by, ml], '( abs ` ( G ` %s ) ) <_ %s' % (CP('C', Y), MB))], '( abs ` ( G ` z ) ) <_ %s' % MB)
    pw = w.s([ex, gy], 'rexlimddv', '( %s -> ( abs ` ( G ` z ) ) <_ %s )' % (A1, MB))
    ra = w.s([pw], 'ralrimiva', '( %s -> A. z e. ( %s cseg %s ) ( abs ` ( G ` z ) ) <_ %s )' % (ph, PV_, PW_, MB))
    pre = seg_pre(w, ph, PV_, PW_, pvc, pwc, gc)
    lab = w.s([w.s([pre, mbr, ra], '3jca', '( %s -> ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) /\\ %s e. RR /\\ A. z e. ( %s cseg %s ) ( abs ` ( G ` z ) ) <_ %s ) )'
                  % (ph, PV_, PW_, PV_, PW_, MB, PV_, PW_, MB)), w.inst('lintabs')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. ( abs ` ( %s - %s ) ) ) )' % (ph, LI('G', PV_, PW_), MB, PW_, PV_))
    d1 = D(w, ph, 'pnpcand', [cc, D(w, ph, 'mulcld', [ic, wc], '( _i x. W ) e. CC'), D(w, ph, 'mulcld', [ic, vc], '( _i x. V ) e. CC')], '( %s - %s ) = ( ( _i x. W ) - ( _i x. V ) )' % (PW_, PV_))
    d2 = D(w, ph, 'eqtr4d', [d1, D(w, ph, 'subdid', [ic, wc, vc], '( _i x. ( W - V ) ) = ( ( _i x. W ) - ( _i x. V ) )')], '( %s - %s ) = ( _i x. ( W - V ) )' % (PW_, PV_))
    wvc = D(w, ph, 'subcld', [wc, vc], '( W - V ) e. CC')
    a1 = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [d2], '( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( W - V ) ) )' % (PW_, PV_)), D(w, ph, 'absmuld', [ic, wvc], '( abs ` ( _i x. ( W - V ) ) ) = ( ( abs ` _i ) x. ( abs ` ( W - V ) ) )')],
           '( abs ` ( %s - %s ) ) = ( ( abs ` _i ) x. ( abs ` ( W - V ) ) )' % (PW_, PV_))
    a2 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq1d', [cst(w, ph, 'absi', '( abs ` _i ) = 1')], '( ( abs ` _i ) x. ( abs ` ( W - V ) ) ) = ( 1 x. ( abs ` ( W - V ) ) )'),
                            D(w, ph, 'mullidd', [D(w, ph, 'abscld', [wvc], '( abs ` ( W - V ) ) e. RR') if False else D(w, ph, 'recnd', [D(w, ph, 'abscld', [wvc], '( abs ` ( W - V ) ) e. RR')], '( abs ` ( W - V ) ) e. CC')],
                              '( 1 x. ( abs ` ( W - V ) ) ) = ( abs ` ( W - V ) )')], '( ( abs ` _i ) x. ( abs ` ( W - V ) ) ) = ( abs ` ( W - V ) )')
    w.qed([lab, D(w, ph, 'oveq2d', [D(w, ph, 'eqtrd', [a1, a2], '( abs ` ( %s - %s ) ) = ( abs ` ( W - V ) )' % (PW_, PV_))], '( %s x. ( abs ` ( %s - %s ) ) ) = ( %s x. ( abs ` ( W - V ) ) )' % (MB, PW_, PV_, MB))],
          'breqtrd', S['zl3epc'])
    go(w, only)
