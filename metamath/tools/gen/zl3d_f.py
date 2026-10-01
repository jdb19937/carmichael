"""ZL3d section F: the theta transformation of a primitive character (zl3thfe).
`MM_DB=sorties/zl3d.mm python3 tools/gen/zl3d_f.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl3d_a import *
from c0b_lib import CxSum, rn

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL3D_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if L.HYPS.get(w.label) else w.run()


def want(label):
    return __name__ == '__main__' and (not only or label in only)


# ---------------------------------------------------------------- zl3fzz (zl3fzs of ZL3b with F on ZZ in place of H ( i n ))
def SUMF(lo, hi):
    return 'sum_ n e. ( %s ... %s ) ( F ` n )' % (lo, hi)


PAIR = '( ( F ` n ) + ( F ` -u n ) )'


def SUMP(hi):
    return 'sum_ n e. ( 1 ... %s ) %s' % (hi, PAIR)


if want('zl3fzz'):
    w = W('zl3fzz', 'A symmetric finite sum over ` -u J ... J ` is the central term plus the sum of the pairs ` n ` , ` -u n ` .')
    HF = 'F : ZZ --> CC'
    EQ = lambda T: '%s = ( ( F ` 0 ) + %s )' % (SUMF('-u %s' % T, T), SUMP(T))
    PK = lambda T: '( %s -> %s )' % (HF, EQ(T))
    def subst(T):
        E = 'k = %s' % T
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        fz = D(w, E, 'oveq12d', [D(w, E, 'negeqd', [e], '-u k = -u %s' % T), e], '( -u k ... k ) = ( -u %s ... %s )' % (T, T))
        l = D(w, E, 'sumeq1d', [fz], '%s = %s' % (SUMF('-u k', 'k'), SUMF('-u %s' % T, T)))
        r = D(w, E, 'oveq2d', [D(w, E, 'sumeq1d', [D(w, E, 'oveq2d', [e], '( 1 ... k ) = ( 1 ... %s )' % T)], '%s = %s' % (SUMP('k'), SUMP(T)))],
              '( ( F ` 0 ) + %s ) = ( ( F ` 0 ) + %s )' % (SUMP('k'), SUMP(T)))
        return D(w, E, 'imbi2d', [D(w, E, 'eqeq12d', [l, r], '( %s <-> %s )' % (EQ('k'), EQ(T)))], '( %s <-> %s )' % (PK('k'), PK(T)))
    h1 = subst('0'); h2 = subst('m'); h3 = subst('( m + 1 )'); h4 = subst('J')
    B0 = HF
    h0c = D(w, B0, 'ffvelcdmd', [w.s([], 'id', '( %s -> %s )' % (B0, B0)), cst(w, B0, '0z', '0 e. ZZ')], '( F ` 0 ) e. CC')
    fz0 = D(w, B0, 'eqtrd', [D(w, B0, 'oveq1d', [cst(w, B0, 'neg0', '-u 0 = 0')], '( -u 0 ... 0 ) = ( 0 ... 0 )'), w.s([cst(w, B0, '0z', '0 e. ZZ'), w.inst('fzsn')], 'syl', '( %s -> ( 0 ... 0 ) = { 0 } )' % B0)],
            '( -u 0 ... 0 ) = { 0 }')
    ssn = w.s([cst(w, B0, 'c0ex', '0 e. _V'), h0c, w.s([w.s([], 'fveq2', '( n = 0 -> ( F ` n ) = ( F ` 0 ) )')], 'sumsn',
                                                       '( ( 0 e. _V /\\ ( F ` 0 ) e. CC ) -> sum_ n e. { 0 } ( F ` n ) = ( F ` 0 ) )')], 'syl2anc',
              '( %s -> sum_ n e. { 0 } ( F ` n ) = ( F ` 0 ) )' % B0)
    l0 = D(w, B0, 'eqtrd', [D(w, B0, 'sumeq1d', [fz0], '%s = sum_ n e. { 0 } ( F ` n )' % SUMF('-u 0', '0')), ssn], '%s = ( F ` 0 )' % SUMF('-u 0', '0'))
    r0 = D(w, B0, 'eqtrd', [D(w, B0, 'oveq2d', [D(w, B0, 'eqtrd', [D(w, B0, 'sumeq1d', [cst(w, B0, 'fz10', '( 1 ... 0 ) = (/)')], '%s = sum_ n e. (/) %s' % (SUMP('0'), PAIR)), cst(w, B0, 'sum0', 'sum_ n e. (/) %s = 0' % PAIR)],
                                                  '%s = 0' % SUMP('0'))], '( ( F ` 0 ) + %s ) = ( ( F ` 0 ) + 0 )' % SUMP('0')), D(w, B0, 'addridd', [h0c], '( ( F ` 0 ) + 0 ) = ( F ` 0 )')],
            '( ( F ` 0 ) + %s ) = ( F ` 0 )' % SUMP('0'))
    base = D(w, B0, 'eqtr4d', [l0, r0], EQ('0'))
    A = '( m e. NN0 /\\ %s )' % HF
    m0 = w.s([], 'simpl', '( %s -> m e. NN0 )' % A); hf = w.s([], 'simpr', '( %s -> %s )' % (A, HF))
    mz = D(w, A, 'nn0zd', [m0], 'm e. ZZ'); mr = D(w, A, 'nn0red', [m0], 'm e. RR'); mc = D(w, A, 'nn0cnd', [m0], 'm e. CC')
    one = cst(w, A, 'ax-1cn', '1 e. CC')
    m1 = '( m + 1 )'
    m1z = D(w, A, 'peano2zd', [mz], '%s e. ZZ' % m1); m1r = D(w, A, 'zred', [m1z], '%s e. RR' % m1)
    X_ = '-u %s' % m1; nm = '-u m'
    x_z = D(w, A, 'znegcld', [m1z], '%s e. ZZ' % X_); x_r = D(w, A, 'zred', [x_z], '%s e. RR' % X_)
    nmz = D(w, A, 'znegcld', [mz], '%s e. ZZ' % nm); nmr = D(w, A, 'zred', [nmz], '%s e. RR' % nm)
    def hval(lo, hi, neg=False):
        Bq = '( %s /\\ n e. ( %s ... %s ) )' % (A, lo, hi)
        nz_ = w.s([w.s([], 'simpr', '( %s -> n e. ( %s ... %s ) )' % (Bq, lo, hi)), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % Bq)
        hb = w.s([hf], 'adantr', '( %s -> %s )' % (Bq, HF))
        a = D(w, Bq, 'ffvelcdmd', [hb, nz_], '( F ` n ) e. CC')
        if not neg:
            return a
        b = D(w, Bq, 'ffvelcdmd', [hb, D(w, Bq, 'znegcld', [nz_], '-u n e. ZZ')], '( F ` -u n ) e. CC')
        return D(w, Bq, 'addcld', [a, b], '%s e. CC' % PAIR)
    def hsub(T):
        return w.s([], 'fveq2', '( n = %s -> ( F ` n ) = ( F ` %s ) )' % (T, T))
    def uz(lo, hi, loz, hiz, le):
        return w.s([w.s([loz, hiz, le], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (A, lo, hi, lo, hi)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (hi, lo, lo, hi, lo, hi))],
                   'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (A, hi, lo))
    p0 = D(w, A, 'nngt0d', [w.s([m0, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A, m1))], '0 < %s' % m1)
    lex = D(w, A, 'ltled', [x_r, m1r, D(w, A, 'lttrd', [x_r, cst(w, A, '0re', '0 e. RR'), m1r, D(w, A, 'mpbid', [p0, D(w, A, 'lt0neg2d', [m1r], '( 0 < %s <-> %s < 0 )' % (m1, X_))], '%s < 0' % X_), p0], '%s < %s' % (X_, m1))],
            '%s <_ %s' % (X_, m1))
    f1 = w.s([uz(X_, m1, x_z, m1z, lex), hval(X_, m1), hsub(X_)], 'fsum1p', '( %s -> %s = ( ( F ` %s ) + %s ) )' % (A, SUMF(X_, m1), X_, SUMF('( %s + 1 )' % X_, m1)))
    xp1 = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [w.s([mc, one, w.inst('negdi2')], 'syl2anc', '( %s -> %s = ( %s - 1 ) )' % (A, X_, nm))], '( %s + 1 ) = ( ( %s - 1 ) + 1 )' % (X_, nm)),
                            w.s([D(w, A, 'negcld', [mc], '%s e. CC' % nm), one, w.inst('npcan')], 'syl2anc', '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (A, nm, nm))], '( %s + 1 ) = %s' % (X_, nm))
    f2 = D(w, A, 'sumeq1d', [D(w, A, 'oveq1d', [xp1], '( ( %s + 1 ) ... %s ) = ( %s ... %s )' % (X_, m1, nm, m1))], '%s = %s' % (SUMF('( %s + 1 )' % X_, m1), SUMF(nm, m1)))
    lem = D(w, A, 'letrd', [nmr, cst(w, A, '0re', '0 e. RR'), mr, D(w, A, 'mpbid', [D(w, A, 'nn0ge0d', [m0], '0 <_ m'), D(w, A, 'le0neg2d', [mr], '( 0 <_ m <-> %s <_ 0 )' % nm)], '%s <_ 0' % nm), D(w, A, 'nn0ge0d', [m0], '0 <_ m')],
            '%s <_ m' % nm)
    f3 = w.s([uz(nm, 'm', nmz, mz, lem), hval(nm, m1), hsub(m1)], 'fsump1', '( %s -> %s = ( %s + ( F ` %s ) ) )' % (A, SUMF(nm, m1), SUMF(nm, 'm'), m1))
    HB = '( F ` %s )' % X_; HT_ = '( F ` %s )' % m1; SM = SUMF(nm, 'm')
    lstep = D(w, A, 'eqtrd', [f1, D(w, A, 'oveq2d', [D(w, A, 'eqtrd', [f2, f3], '%s = ( %s + %s )' % (SUMF('( %s + 1 )' % X_, m1), SM, HT_))],
                                                     '( %s + %s ) = ( %s + ( %s + %s ) )' % (HB, SUMF('( %s + 1 )' % X_, m1), HB, SM, HT_))], '%s = ( %s + ( %s + %s ) )' % (SUMF(X_, m1), HB, SM, HT_))
    uz0 = D(w, A, 'eleqtrrd', [D(w, A, 'eleqtrd', [m0, cst(w, A, 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'm e. ( ZZ>= ` 0 )'),
                               D(w, A, 'fveq2d', [cst(w, A, '1m1e0', '( 1 - 1 ) = 0')], '( ZZ>= ` ( 1 - 1 ) ) = ( ZZ>= ` 0 )')], 'm e. ( ZZ>= ` ( 1 - 1 ) )')
    fs2 = w.s([cst(w, A, '1z', '1 e. ZZ'), uz0, w.inst('fzsuc2')], 'syl2anc', '( %s -> ( 1 ... %s ) = ( ( 1 ... m ) u. { %s } ) )' % (A, m1, m1))
    PD = '( ( F ` %s ) + ( F ` -u %s ) )' % (m1, m1)
    pdc = D(w, A, 'addcld', [D(w, A, 'ffvelcdmd', [hf, m1z], '( F ` %s ) e. CC' % m1), D(w, A, 'ffvelcdmd', [hf, x_z], '( F ` -u %s ) e. CC' % m1)], '%s e. CC' % PD)
    psub = w.s([hsub(m1), w.s([w.s([], 'negeq', '( n = %s -> -u n = -u %s )' % (m1, m1))], 'fveq2d', '( n = %s -> ( F ` -u n ) = ( F ` -u %s ) )' % (m1, m1))],
               'oveq12d', '( n = %s -> %s = %s )' % (m1, PAIR, PD))
    fsn = w.s([w.s([], 'nfv', 'F/ n %s' % A), w.s([], 'nfcv', 'F/_ n %s' % PD), w.s([], 'fzfid', '( %s -> ( 1 ... m ) e. Fin )' % A),
               w.s([m1z, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A, m1)), cst(w, A, 'fzp1nel', '-. %s e. ( 1 ... m )' % m1), hval('1', 'm', True), psub, pdc], 'fsumsplitsn',
              '( %s -> sum_ n e. ( ( 1 ... m ) u. { %s } ) %s = ( %s + %s ) )' % (A, m1, PAIR, SUMP('m'), PD))
    rstep = D(w, A, 'eqtrd', [D(w, A, 'sumeq1d', [fs2], '%s = sum_ n e. ( ( 1 ... m ) u. { %s } ) %s' % (SUMP(m1), m1, PAIR)), fsn], '%s = ( %s + %s )' % (SUMP(m1), SUMP('m'), PD))
    A2 = '( %s /\\ %s )' % (A, EQ('m'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (A2, EQ('m')))
    lA = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    H0 = '( F ` 0 )'
    h0c2 = lA(D(w, A, 'ffvelcdmd', [hf, cst(w, A, '0z', '0 e. ZZ')], '%s e. CC' % H0), '%s e. CC' % H0)
    spc = lA(w.s([w.s([], 'fzfid', '( %s -> ( 1 ... m ) e. Fin )' % A), hval('1', 'm', True)], 'fsumcl', '( %s -> %s e. CC )' % (A, SUMP('m'))), '%s e. CC' % SUMP('m'))
    hbc = lA(D(w, A, 'ffvelcdmd', [hf, x_z], '%s e. CC' % HB), '%s e. CC' % HB)
    htc = lA(D(w, A, 'ffvelcdmd', [hf, m1z], '%s e. CC' % HT_), '%s e. CC' % HT_)
    L1 = D(w, A2, 'eqtrd', [lA(lstep, '%s = ( %s + ( %s + %s ) )' % (SUMF(X_, m1), HB, SM, HT_)), D(w, A2, 'oveq2d', [D(w, A2, 'oveq1d', [ih], '( %s + %s ) = ( ( %s + %s ) + %s )' % (SM, HT_, H0, SUMP('m'), HT_))],
                                                                                                      '( %s + ( %s + %s ) ) = ( %s + ( ( %s + %s ) + %s ) )' % (HB, SM, HT_, HB, H0, SUMP('m'), HT_))],
            '%s = ( %s + ( ( %s + %s ) + %s ) )' % (SUMF(X_, m1), HB, H0, SUMP('m'), HT_))
    SP = SUMP('m')
    cs = CxSum(w, A2, {HB: hbc, H0: h0c2, SP: spc, HT_: htc}, {H0: 0, SP: 1, HT_: 2, HB: 3})
    nL, aL = cs.nf(('+', HB, ('+', ('+', H0, SP), HT_)))
    nR, aR = cs.nf(('+', H0, ('+', SP, ('+', HT_, HB))))
    assert aL == aR
    R1 = D(w, A2, 'oveq2d', [lA(rstep, '%s = ( %s + %s )' % (SUMP(m1), SP, PD))], '( %s + %s ) = ( %s + ( %s + %s ) )' % (H0, SUMP(m1), H0, SP, PD))
    fin = D(w, A2, 'eqtr4d', [D(w, A2, 'eqtrd', [L1, nL], '%s = %s' % (SUMF(X_, m1), rn(aL))), D(w, A2, 'eqtrd', [R1, nR], '( %s + %s ) = %s' % (H0, SUMP(m1), rn(aR)))], EQ(m1))
    st1 = w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (A, EQ('m'), EQ(m1)))
    st2 = w.s([st1], 'ex', '( m e. NN0 -> ( %s -> ( %s -> %s ) ) )' % (HF, EQ('m'), EQ(m1)))
    st3 = w.s([st2], 'a2d', '( m e. NN0 -> ( %s -> %s ) )' % (PK('m'), PK(m1)))
    ind = w.s([h1, h2, h3, h4, base, st3], 'nn0ind', '( J e. NN0 -> %s )' % PK('J'))
    w.qed([ind], 'impcom', S['zl3fzz'])
    go(w)


H2 = '( 1 / 2 )'


def hb_facts(w, A, hb):
    """from hb: ( A -> HBF ) : F map, C real, the bound"""
    ff = D(w, A, 'simpld', [hb], 'F : ZZ --> CC')
    r = D(w, A, 'simprd', [hb], '( C e. RR /\\ A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) ) )' % H2)
    return ff, D(w, A, 'simpld', [r], 'C e. RR'), D(w, A, 'simprd', [r], 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2)


def fbound(w, A, bnd, X, xz, F='F', C='C'):
    """( A -> ( abs ` ( F ` X ) ) <_ ( C x. ( ( 1 / 2 ) ^ ( abs ` X ) ) ) )"""
    sub = w.s([w.s([w.s([], 'fveq2', '( i = %s -> ( %s ` i ) = ( %s ` %s ) )' % (X, F, F, X))], 'fveq2d', '( i = %s -> ( abs ` ( %s ` i ) ) = ( abs ` ( %s ` %s ) ) )' % (X, F, F, X)),
               w.s([w.s([w.s([], 'fveq2', '( i = %s -> ( abs ` i ) = ( abs ` %s ) )' % (X, X))], 'oveq2d', '( i = %s -> ( %s ^ ( abs ` i ) ) = ( %s ^ ( abs ` %s ) ) )' % (X, H2, H2, X))], 'oveq2d',
                   '( i = %s -> ( %s x. ( %s ^ ( abs ` i ) ) ) = ( %s x. ( %s ^ ( abs ` %s ) ) ) )' % (X, C, H2, C, H2, X))],
              'breq12d', '( i = %s -> ( ( abs ` ( %s ` i ) ) <_ ( %s x. ( %s ^ ( abs ` i ) ) ) <-> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) ) ) )' % (X, F, C, H2, F, X, C, H2, X))
    return D(w, A, 'rspcdva', [sub, bnd, xz], '( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) )' % (F, X, C, H2, X))


def pair_bound(w, A, ff, cr, bnd, X, xn):
    """X e. NN: ( A -> ( abs ` P(X) ) <_ ( ( 2 x. C ) x. ( ( 1 / 2 ) ^ X ) ) ), and P(X) e. CC"""
    xz = D(w, A, 'nnzd', [xn], '%s e. ZZ' % X)
    nx = D(w, A, 'znegcld', [xz], '-u %s e. ZZ' % X)
    a = D(w, A, 'ffvelcdmd', [ff, xz], '( F ` %s ) e. CC' % X); b = D(w, A, 'ffvelcdmd', [ff, nx], '( F ` -u %s ) e. CC' % X)
    P = '( ( F ` %s ) + ( F ` -u %s ) )' % (X, X)
    pc = D(w, A, 'addcld', [a, b], '%s e. CC' % P)
    xr = D(w, A, 'nnred', [xn], '%s e. RR' % X); x0 = D(w, A, 'nnge1d' if False else 'nnnn0d', [xn], '%s e. NN0' % X)
    ax = D(w, A, 'absidd', [xr, D(w, A, 'nn0ge0d', [x0], '0 <_ %s' % X)], '( abs ` %s ) = %s' % (X, X))
    anx = D(w, A, 'eqtrd', [D(w, A, 'absnegd', [D(w, A, 'recnd', [xr], '%s e. CC' % X)], '( abs ` -u %s ) = ( abs ` %s )' % (X, X)), ax], '( abs ` -u %s ) = %s' % (X, X))
    PW = '( %s ^ %s )' % (H2, X)
    b1 = D(w, A, 'breqtrd', [fbound(w, A, bnd, X, xz), D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [ax], '( %s ^ ( abs ` %s ) ) = %s' % (H2, X, PW))], '( C x. ( %s ^ ( abs ` %s ) ) ) = ( C x. %s )' % (H2, X, PW))],
           '( abs ` ( F ` %s ) ) <_ ( C x. %s )' % (X, PW))
    b2 = D(w, A, 'breqtrd', [fbound(w, A, bnd, '-u %s' % X, nx), D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [anx], '( %s ^ ( abs ` -u %s ) ) = %s' % (H2, X, PW))], '( C x. ( %s ^ ( abs ` -u %s ) ) ) = ( C x. %s )' % (H2, X, PW))],
           '( abs ` ( F ` -u %s ) ) <_ ( C x. %s )' % (X, PW))
    tri = D(w, A, 'abstrid', [a, b], '( abs ` %s ) <_ ( ( abs ` ( F ` %s ) ) + ( abs ` ( F ` -u %s ) ) )' % (P, X, X))
    pwr = D(w, A, 'reexpcld', [cst(w, A, 'halfre', '%s e. RR' % H2), x0], '%s e. RR' % PW)
    fin = nlinarith(w, A, [tri, b1, b2], '( abs ` %s ) <_ ( ( 2 x. C ) x. %s )' % (P, PW),
                    leaves={'( abs ` %s )' % P: D(w, A, 'abscld', [pc], '( abs ` %s ) e. RR' % P), '( abs ` ( F ` %s ) )' % X: D(w, A, 'abscld', [a], '( abs ` ( F ` %s ) ) e. RR' % X),
                            '( abs ` ( F ` -u %s ) )' % X: D(w, A, 'abscld', [b], '( abs ` ( F ` -u %s ) ) e. RR' % X), 'C': cr, PW: pwr},
                    atoms=['( abs ` %s )' % P, '( abs ` ( F ` %s ) )' % X, '( abs ` ( F ` -u %s ) )' % X, PW])
    return fin, pc


# ---------------------------------------------------------------- zl3pzt
if want('zl3pzt'):
    w = W('zl3pzt', 'Under a majorant ` C ( 1 / 2 ) ^ abs ( n ) ` the sum over ` ZZ ` converges and its symmetric partial sums are within ` 2 C ( 1 / 2 ) ^ j ` .')
    A, Cc = ante_of('zl3pzt')
    ff, cr, bnd = hb_facts(w, A, w.s([], 'idi', '( %s -> %s )' % (A, A)) if False else D(w, A, 'id', [], A))
    PAIRk = lambda X: '( ( F ` %s ) + ( F ` -u %s ) )' % (X, X)
    PMn = '( n e. NN |-> %s )' % PAIRk('n')
    PMm = '( m e. NN |-> %s )' % PAIRk('m')
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    pbk, pck = pair_bound(w, Ak, ad(w, Ak, ff, 'F : ZZ --> CC'), ad(w, Ak, cr, 'C e. RR'), ad(w, Ak, bnd, 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2), 'k', kn)
    def pairsub(v, X):
        return w.s([w.s([], 'fveq2', '( %s = %s -> ( F ` %s ) = ( F ` %s ) )' % (v, X, v, X)), w.s([w.s([], 'negeq', '( %s = %s -> -u %s = -u %s )' % (v, X, v, X))], 'fveq2d', '( %s = %s -> ( F ` -u %s ) = ( F ` -u %s ) )' % (v, X, v, X))],
                   'oveq12d', '( %s = %s -> %s = %s )' % (v, X, PAIRk(v), PAIRk(X)))
    pmk = D(w, Ak, 'syl', [kn, w.s([pairsub('n', 'k'), w.s([], 'eqid', '%s = %s' % (PMn, PMn)), w.s([], 'ovex', '%s e. _V' % PAIRk('k'))], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (PMn, PAIRk('k')))],
            '( %s ` k ) = %s' % (PMn, PAIRk('k')))
    C2 = '( 2 x. C )'
    ms = D(w, A, 'zl3mser', [D(w, A, 'remulcld', [cst(w, A, '2re', '2 e. RR'), cr], '%s e. RR' % C2), cst(w, A, 'halfre', '%s e. RR' % H2), D(w, A, 'rpge0d', [w.s([w.s([w.s([], '1rp', '1 e. RR+'), w.inst('rphalfcl')], 'ax-mp', '%s e. RR+' % H2)], 'a1i', '( %s -> %s e. RR+ )' % (A, H2))], '0 <_ %s' % H2),
                             cst(w, A, 'halflt1', '%s < 1' % H2), D(w, Ak, 'eqeltrd', [pmk, pck], '( %s ` k ) e. CC' % PMn),
                             D(w, Ak, 'eqbrtrd', [D(w, Ak, 'fveq2d', [pmk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (PMn, PAIRk('k'))), pbk], '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ^ k ) )' % (PMn, C2, H2))],
           '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) ) )' % (PMn, PMn, C2, H2, H2))
    cvg = D(w, A, 'simpld', [ms], 'seq 1 ( + , %s ) e. dom ~~>' % PMn)
    # tail at j
    Aj = '( %s /\\ j e. NN0 )' % A
    j0 = w.s([], 'simpr', '( %s -> j e. NN0 )' % Aj)
    ffj, crj, bndj = ad(w, Aj, ff, 'F : ZZ --> CC'), ad(w, Aj, cr, 'C e. RR'), ad(w, Aj, bnd, 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2)
    fz = D(w, Aj, 'syl2anc' if False else 'sylancl' if False else 'syl2anc', [ffj, j0, w.inst('zl3fzz')], '%s = ( ( F ` 0 ) + sum_ n e. ( 1 ... j ) %s )' % (L.SYM('F', 'j'), PAIRk('n')))
    J1 = '( 1 + j )'
    j1n = D(w, Aj, 'syl2anc', [cst(w, Aj, '1nn', '1 e. NN'), j0, w.inst('nnnn0addcl')], '%s e. NN' % J1)
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    WJ = '( ZZ>= ` %s )' % J1
    Ajn = '( %s /\\ n e. NN )' % Aj
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % Ajn)
    pmn = D(w, Ajn, 'syl', [nn_, w.s([pairsub('m', 'n'), w.s([], 'eqid', '%s = %s' % (PMm, PMm)), w.s([], 'ovex', '%s e. _V' % PAIRk('n'))], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (PMm, PAIRk('n')))],
            '( %s ` n ) = %s' % (PMm, PAIRk('n')))
    _, pcn = pair_bound(w, Ajn, ad(w, Ajn, ffj, 'F : ZZ --> CC'), ad(w, Ajn, crj, 'C e. RR'), ad(w, Ajn, bndj, 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2), 'n', nn_)
    pmeq = w.s([pairsub('m', 'n')], 'cbvmptv', '%s = %s' % (PMm, PMn))
    cvgm = D(w, Aj, 'eleqtrrd' if False else 'mpbird', [ad(w, Aj, cvg, 'seq 1 ( + , %s ) e. dom ~~>' % PMn),
                                                        w.s([w.s([w.s([pmeq, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (PMm, PMn))], 'eleq1i', '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (PMm, PMn))],
                                                            'a1i', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (Aj, PMm, PMn))],
             'seq 1 ( + , %s ) e. dom ~~>' % PMm)
    spl = D(w, Aj, 'isumsplit', [nnu, w.s([], 'eqid', '%s = %s' % (WJ, WJ)), j1n, pmn, pcn, cvgm],
            'sum_ n e. NN %s = ( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + sum_ n e. %s %s )' % (PAIRk('n'), J1, PAIRk('n'), WJ, PAIRk('n')))
    jj = D(w, Aj, 'pncan2d', [D(w, Aj, '1cnd', [], '1 e. CC'), D(w, Aj, 'nn0cnd', [j0], 'j e. CC')], '( %s - 1 ) = j' % J1)
    spl2 = D(w, Aj, 'eqtrd', [spl, D(w, Aj, 'oveq1d', [D(w, Aj, 'sumeq1d', [D(w, Aj, 'oveq2d', [jj], '( 1 ... ( %s - 1 ) ) = ( 1 ... j )' % J1)],
                                                        'sum_ n e. ( 1 ... ( %s - 1 ) ) %s = sum_ n e. ( 1 ... j ) %s' % (J1, PAIRk('n'), PAIRk('n')))],
                                       '( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + sum_ n e. %s %s ) = ( sum_ n e. ( 1 ... j ) %s + sum_ n e. %s %s )' % (J1, PAIRk('n'), WJ, PAIRk('n'), PAIRk('n'), WJ, PAIRk('n')))],
             'sum_ n e. NN %s = ( sum_ n e. ( 1 ... j ) %s + sum_ n e. %s %s )' % (PAIRk('n'), PAIRk('n'), WJ, PAIRk('n')))
    F0 = '( F ` 0 )'
    SA, SW, SN = 'sum_ n e. ( 1 ... j ) %s' % PAIRk('n'), 'sum_ n e. %s %s' % (WJ, PAIRk('n')), 'sum_ n e. NN %s' % PAIRk('n')
    Ajf = '( %s /\\ n e. ( 1 ... j ) )' % Aj
    nf = D(w, Ajf, 'elfznn', [w.s([], 'simpr', '( %s -> n e. ( 1 ... j ) )' % Ajf)], 'n e. NN') if False else w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... j ) )' % Ajf), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % Ajf)
    _, pcf = pair_bound(w, Ajf, ad(w, Ajf, ffj, 'F : ZZ --> CC'), ad(w, Ajf, crj, 'C e. RR'), ad(w, Ajf, bndj, 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2), 'n', nf)
    sac = D(w, Aj, 'fsumcl', [D(w, Aj, 'fzfid', [], '( 1 ... j ) e. Fin'), pcf], '%s e. CC' % SA)
    # the tail as a shifted series
    Ajw = '( %s /\\ n e. %s )' % (Aj, WJ)
    nw = D(w, Ajw, 'syl2anc', [ad(w, Ajw, j1n, '%s e. NN' % J1), w.s([], 'simpr', '( %s -> n e. %s )' % (Ajw, WJ)), w.inst('eluznn')], 'n e. NN')
    _, pcw = pair_bound(w, Ajw, ad(w, Ajw, ffj, 'F : ZZ --> CC'), ad(w, Ajw, crj, 'C e. RR'), ad(w, Ajw, bndj, 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2), 'n', nw)
    JK = '( j + k )'
    sh = D(w, Aj, 'isumshft', [nnu, w.s([], 'eqid', '%s = %s' % (WJ, WJ)), pairsub('n', JK), D(w, Aj, 'nn0zd', [j0], 'j e. ZZ'), cst(w, Aj, '1z', '1 e. ZZ'), pcw],
           '%s = sum_ k e. NN %s' % (SW, PAIRk(JK)))
    swc = D(w, Aj, 'eqeltrd' if False else 'isumcl' if False else 'mpbird', [], '') if False else None
    TQ = '( q e. NN |-> %s )' % PAIRk('( j + q )')
    Ajk = '( %s /\\ k e. NN )' % Aj
    kn2 = w.s([], 'simpr', '( %s -> k e. NN )' % Ajk)
    jkn = D(w, Ajk, 'syl2anc', [ad(w, Ajk, j0, 'j e. NN0'), kn2, w.inst('nn0nnaddcl')], '%s e. NN' % JK)
    pbjk, pcjk = pair_bound(w, Ajk, ad(w, Ajk, ffj, 'F : ZZ --> CC'), ad(w, Ajk, crj, 'C e. RR'), ad(w, Ajk, bndj, 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2), JK, jkn)
    tqk = D(w, Ajk, 'syl', [kn2, w.s([pairsub('q', 'k') if False else w.s([w.s([], 'oveq2', '( q = k -> ( j + q ) = %s )' % JK), w.s([], 'dummy', '')], 'x', 'x') if False else
                                      w.s([w.s([w.s([], 'oveq2', '( q = k -> ( j + q ) = %s )' % JK)], 'fveq2d', '( q = k -> ( F ` ( j + q ) ) = ( F ` %s ) )' % JK),
                                           w.s([w.s([w.s([], 'oveq2', '( q = k -> ( j + q ) = %s )' % JK)], 'negeqd', '( q = k -> -u ( j + q ) = -u %s )' % JK)], 'fveq2d', '( q = k -> ( F ` -u ( j + q ) ) = ( F ` -u %s ) )' % JK)],
                                          'oveq12d', '( q = k -> %s = %s )' % (PAIRk('( j + q )'), PAIRk(JK))),
                                      w.s([], 'eqid', '%s = %s' % (TQ, TQ)), w.s([], 'ovex', '%s e. _V' % PAIRk(JK))], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (TQ, PAIRk(JK)))],
            '( %s ` k ) = %s' % (TQ, PAIRk(JK)))
    BJ = '( %s x. ( %s ^ j ) )' % (C2, H2)
    hc = cst(w, Ajk, 'halfcn', '%s e. CC' % H2)
    ea = D(w, Ajk, 'expaddd', [hc, D(w, Ajk, 'nnnn0d', [kn2], 'k e. NN0'), ad(w, Ajk, j0, 'j e. NN0')], '( %s ^ %s ) = ( ( %s ^ j ) x. ( %s ^ k ) )' % (H2, JK, H2, H2))
    c2c = D(w, Ajk, 'recnd', [D(w, Ajk, 'remulcld', [cst(w, Ajk, '2re', '2 e. RR'), ad(w, Ajk, crj, 'C e. RR')], '%s e. RR' % C2)], '%s e. CC' % C2)
    hj = D(w, Ajk, 'expcld', [hc, ad(w, Ajk, j0, 'j e. NN0')], '( %s ^ j ) e. CC' % H2); hk = D(w, Ajk, 'expcld', [hc, D(w, Ajk, 'nnnn0d', [kn2], 'k e. NN0')], '( %s ^ k ) e. CC' % H2)
    re_ = chain(w, Ajk, ['( %s x. ( %s ^ %s ) )' % (C2, H2, JK), '( %s x. ( ( %s ^ j ) x. ( %s ^ k ) ) )' % (C2, H2, H2), '( %s x. ( %s ^ k ) )' % (BJ, H2)],
                [D(w, Ajk, 'oveq2d', [ea], '( %s x. ( %s ^ %s ) ) = ( %s x. ( ( %s ^ j ) x. ( %s ^ k ) ) )' % (C2, H2, JK, C2, H2, H2)),
                 ('r', D(w, Ajk, 'mulassd', [c2c, hj, hk], '( %s x. ( %s ^ k ) ) = ( %s x. ( ( %s ^ j ) x. ( %s ^ k ) ) )' % (BJ, H2, C2, H2, H2)))])
    tb = D(w, Ajk, 'breqtrd', [D(w, Ajk, 'eqbrtrd', [D(w, Ajk, 'fveq2d', [tqk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (TQ, PAIRk(JK))), pbjk], '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ^ %s ) )' % (TQ, C2, H2, JK)), re_],
           '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ^ k ) )' % (TQ, BJ, H2))
    bjr = D(w, Aj, 'remulcld', [D(w, Aj, 'remulcld', [cst(w, Aj, '2re', '2 e. RR'), crj], '%s e. RR' % C2), D(w, Aj, 'reexpcld', [cst(w, Aj, 'halfre', '%s e. RR' % H2), j0], '( %s ^ j ) e. RR' % H2)], '%s e. RR' % BJ)
    ms2 = D(w, Aj, 'zl3mser', [bjr, cst(w, Aj, 'halfre', '%s e. RR' % H2), D(w, Aj, 'rpge0d', [w.s([w.s([w.s([], '1rp', '1 e. RR+'), w.inst('rphalfcl')], 'ax-mp', '%s e. RR+' % H2)], 'a1i', '( %s -> %s e. RR+ )' % (Aj, H2))], '0 <_ %s' % H2), cst(w, Aj, 'halflt1', '%s < 1' % H2),
                               D(w, Ajk, 'eqeltrd', [tqk, pcjk], '( %s ` k ) e. CC' % TQ), tb],
            '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) ) )' % (TQ, TQ, BJ, H2, H2))
    sb = D(w, Aj, 'simprd', [ms2], '( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) )' % (TQ, BJ, H2, H2))
    se = D(w, Aj, 'sumeq2dv', [tqk], 'sum_ k e. NN ( %s ` k ) = sum_ k e. NN %s' % (TQ, PAIRk(JK)))
    val = D(w, Aj, 'eqtrd', [D(w, Aj, 'oveq2d', [cst(w, Aj, '1mhlfehlf', '( 1 - %s ) = %s' % (H2, H2))], '( ( %s x. %s ) / ( 1 - %s ) ) = ( ( %s x. %s ) / %s )' % (BJ, H2, H2, BJ, H2, H2)),
                             D(w, Aj, 'divcan4d', [D(w, Aj, 'recnd', [bjr], '%s e. CC' % BJ), cst(w, Aj, 'halfcn', '%s e. CC' % H2), D(w, Aj, 'rpne0d', [w.s([w.s([w.s([], '1rp', '1 e. RR+'), w.inst('rphalfcl')], 'ax-mp', '%s e. RR+' % H2)], 'a1i', '( %s -> %s e. RR+ )' % (Aj, H2))], '%s =/= 0' % H2)],
                               '( ( %s x. %s ) / %s ) = %s' % (BJ, H2, H2, BJ))], '( ( %s x. %s ) / ( 1 - %s ) ) = %s' % (BJ, H2, H2, BJ))
    # PZ - sym = SW
    PZ = L.PZF('F'); SYMJ = L.SYM('F', 'j')
    f0c = D(w, Aj, 'ffvelcdmd', [ffj, cst(w, Aj, '0z', '0 e. ZZ')], '%s e. CC' % F0)
    swc = D(w, Aj, 'eqeltrd', [sh, D(w, Aj, 'eqeltrrd', [se, D(w, Aj, 'isumcl' if False else 'eqeltrd', [], '') if False else None], '') if False else None], '') if False else None
    sncl = D(w, Aj, 'eqeltrd' if False else 'isumcl', [nnu, cst(w, Aj, '1z', '1 e. ZZ'), pmn, pcn, cvgm], '%s e. CC' % SN)
    d1 = D(w, Aj, 'oveq2d', [fz], '( %s - %s ) = ( %s - ( %s + %s ) )' % (PZ, SYMJ, PZ, F0, SA))
    d2 = D(w, Aj, 'pnpcand', [f0c, sncl, sac], '( ( %s + %s ) - ( %s + %s ) ) = ( %s - %s )' % (F0, SN, F0, SA, SN, SA))
    d3 = D(w, Aj, 'oveq1d', [spl2], '( %s - %s ) = ( ( %s + %s ) - %s )' % (SN, SA, SA, SW, SA))
    swc = D(w, Aj, 'eqeltrd', [D(w, Aj, 'eqtrd', [sh, D(w, Aj, 'eqcomd', [se], 'sum_ k e. NN %s = sum_ k e. NN ( %s ` k )' % (PAIRk(JK), TQ))], '%s = sum_ k e. NN ( %s ` k )' % (SW, TQ)),
                               D(w, Aj, 'isumcl', [nnu, cst(w, Aj, '1z', '1 e. ZZ'), D(w, Ajk, 'eqidd', [], '( %s ` k ) = ( %s ` k )' % (TQ, TQ)), D(w, Ajk, 'eqeltrd', [tqk, pcjk], '( %s ` k ) e. CC' % TQ),
                                                   D(w, Aj, 'simpld', [ms2], 'seq 1 ( + , %s ) e. dom ~~>' % TQ)], 'sum_ k e. NN ( %s ` k ) e. CC' % TQ)], '%s e. CC' % SW)
    d4 = D(w, Aj, 'pncan2d', [sac, swc], '( ( %s + %s ) - %s ) = %s' % (SA, SW, SA, SW))
    dd = chain(w, Aj, ['( %s - %s )' % (PZ, SYMJ), '( %s - ( %s + %s ) )' % (PZ, F0, SA), '( %s - %s )' % (SN, SA), '( ( %s + %s ) - %s )' % (SA, SW, SA), SW, 'sum_ k e. NN ( %s ` k )' % TQ],
               [d1, d2, d3, d4, D(w, Aj, 'eqtrd', [sh, D(w, Aj, 'eqcomd', [se], 'sum_ k e. NN %s = sum_ k e. NN ( %s ` k )' % (PAIRk(JK), TQ))], '%s = sum_ k e. NN ( %s ` k )' % (SW, TQ))])
    tail = D(w, Aj, 'breqtrd', [D(w, Aj, 'eqbrtrd', [D(w, Aj, 'fveq2d', [dd], '( abs ` ( %s - %s ) ) = ( abs ` sum_ k e. NN ( %s ` k ) )' % (PZ, SYMJ, TQ)), sb],
                                  '( abs ` ( %s - %s ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) )' % (PZ, SYMJ, BJ, H2, H2)), val], '( abs ` ( %s - %s ) ) <_ %s' % (PZ, SYMJ, BJ))
    ral = D(w, A, 'ralrimiva', [tail], 'A. j e. NN0 ( abs ` ( %s - %s ) ) <_ %s' % (PZ, SYMJ, BJ))
    w.qed([cvg, ral], 'jca', S['zl3pzt'])
    go(w)


# ---------------------------------------------------------------- zl3frg
WIN = lambda J: '( ( Q x. M ) ... ( ( Q x. M ) + ( ( %s x. M ) - 1 ) ) )' % J
LHSg = lambda J: 'sum_ n e. %s ( F ` n )' % WIN(J)
RNG = lambda J: '( Q ... ( Q + ( %s - 1 ) ) )' % J
INN = lambda J: 'sum_ m e. %s ( F ` ( b + ( m x. M ) ) )' % RNG(J)
RHSg = lambda J: 'sum_ b e. ( 0 ..^ M ) %s' % INN(J)
PSg = lambda J: '%s = %s' % (LHSg(J), RHSg(J))

if want('zl3frg'):
    w = W('zl3frg', 'A window of ` J ` blocks of ` M ` consecutive integers, summed by residues ` b ` and quotients ` m ` ( induction on ` J ` ).')
    A, Cc = ante_of('zl3frg')
    c = '( ( M e. NN /\\ Q e. ZZ ) /\\ F : ZZ --> CC )'
    def sub(T):
        E = 't = %s' % T
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        tm = D(w, E, 'oveq1d', [e], '( t x. M ) = ( %s x. M )' % T)
        win = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'oveq1d', [tm], '( ( t x. M ) - 1 ) = ( ( %s x. M ) - 1 )' % T)], '( ( Q x. M ) + ( ( t x. M ) - 1 ) ) = ( ( Q x. M ) + ( ( %s x. M ) - 1 ) )' % T)],
                 '%s = %s' % (WIN('t'), WIN(T)))
        l = D(w, E, 'sumeq1d', [win], '%s = %s' % (LHSg('t'), LHSg(T)))
        rng = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'oveq1d', [e], '( t - 1 ) = ( %s - 1 )' % T)], '( Q + ( t - 1 ) ) = ( Q + ( %s - 1 ) )' % T)], '%s = %s' % (RNG('t'), RNG(T)))
        inn = D(w, E, 'sumeq1d', [rng], '%s = %s' % (INN('t'), INN(T)))
        r = D(w, E, 'sumeq2dv', [w.s([inn], 'adantr', '( ( %s /\\ b e. ( 0 ..^ M ) ) -> %s = %s )' % (E, INN('t'), INN(T)))], '%s = %s' % (RHSg('t'), RHSg(T)))
        return D(w, E, 'eqeq12d', [l, r], '( %s <-> %s )' % (PSg('t'), PSg(T)))
    h1, h2, h3, h4 = sub('0'), sub('r'), sub('( r + 1 )'), sub('J')
    mn = D(w, c, 'simpll', [], 'M e. NN'); qz = D(w, c, 'simplr', [], 'Q e. ZZ'); ff = D(w, c, 'simpr', [], 'F : ZZ --> CC')
    mz = D(w, c, 'nnzd', [mn], 'M e. ZZ'); mr = D(w, c, 'nnred', [mn], 'M e. RR'); qr = D(w, c, 'zred', [qz], 'Q e. RR')
    QM = '( Q x. M )'
    qmz = D(w, c, 'zmulcld', [qz, mz], '%s e. ZZ' % QM); qmr = D(w, c, 'zred', [qmz], '%s e. RR' % QM)
    # base: both sides are empty sums
    E0 = '( %s + ( ( 0 x. M ) - 1 ) )' % QM
    z0 = D(w, c, 'mul02d', [D(w, c, 'nncnd', [mn], 'M e. CC')], '( 0 x. M ) = 0')
    e0z = D(w, c, 'zaddcld', [qmz, D(w, c, 'zsubcld', [D(w, c, 'zmulcld', [cst(w, c, '0z', '0 e. ZZ'), mz], '( 0 x. M ) e. ZZ'), cst(w, c, '1z', '1 e. ZZ')], '( ( 0 x. M ) - 1 ) e. ZZ')], '%s e. ZZ' % E0)
    e0lt = linarith(w, c, [z0], '%s < %s' % (E0, QM), leaves={QM: qmr, '( 0 x. M )': D(w, c, 'zred', [D(w, c, 'zmulcld', [cst(w, c, '0z', '0 e. ZZ'), mz], '( 0 x. M ) e. ZZ')], '( 0 x. M ) e. RR')},
                    atoms=[QM, '( 0 x. M )'])
    wn = D(w, c, 'mpbid', [e0lt, D(w, c, 'syl2anc', [qmz, e0z, w.inst('fzn')], '( %s < %s <-> %s = (/) )' % (E0, QM, WIN('0')))], '%s = (/)' % WIN('0'))
    l0 = D(w, c, 'eqtrd', [D(w, c, 'sumeq1d', [wn], '%s = sum_ n e. (/) ( F ` n )' % LHSg('0')), cst(w, c, 'sum0', 'sum_ n e. (/) ( F ` n ) = 0')], '%s = 0' % LHSg('0'))
    R0 = '( Q + ( 0 - 1 ) )'
    r0z = D(w, c, 'zaddcld', [qz, cst(w, c, 'zcn' if False else 'idi', '') if False else D(w, c, 'zsubcld', [cst(w, c, '0z', '0 e. ZZ'), cst(w, c, '1z', '1 e. ZZ')], '( 0 - 1 ) e. ZZ')], '%s e. ZZ' % R0)
    r0lt = linarith(w, c, [], '%s < Q' % R0, leaves={'Q': qr})
    rn_ = D(w, c, 'mpbid', [r0lt, D(w, c, 'syl2anc', [qz, r0z, w.inst('fzn')], '( %s < Q <-> %s = (/) )' % (R0, RNG('0')))], '%s = (/)' % RNG('0'))
    cb = '( %s /\\ b e. ( 0 ..^ M ) )' % c
    i0 = D(w, cb, 'eqtrd', [D(w, cb, 'sumeq1d', [ad(w, cb, rn_, '%s = (/)' % RNG('0'))], '%s = sum_ m e. (/) ( F ` ( b + ( m x. M ) ) )' % INN('0')),
                            cst(w, cb, 'sum0', 'sum_ m e. (/) ( F ` ( b + ( m x. M ) ) ) = 0')], '%s = 0' % INN('0'))
    r0 = D(w, c, 'eqtrd', [D(w, c, 'sumeq2dv', [i0], '%s = sum_ b e. ( 0 ..^ M ) 0' % RHSg('0')),
                           w.s([w.s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin'), w.inst('olci')], 'ax-mp', '( ( 0 ..^ M ) C_ ( ZZ>= ` 0 ) \\/ ( 0 ..^ M ) e. Fin )'), w.inst('sumz')], 'ax-mp',
                               'sum_ b e. ( 0 ..^ M ) 0 = 0') if False else
                           w.s([w.s([w.s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'olci', '( ( 0 ..^ M ) C_ ( ZZ>= ` 0 ) \\/ ( 0 ..^ M ) e. Fin )'), w.inst('sumz')], 'ax-mp',
                                    'sum_ b e. ( 0 ..^ M ) 0 = 0')], 'a1i', '( %s -> sum_ b e. ( 0 ..^ M ) 0 = 0 )' % c)], '%s = 0' % RHSg('0'))
    base = D(w, c, 'eqtr4d', [l0, r0], PSg('0'))
    # step, computed without the induction hypothesis
    C0 = '( %s /\\ r e. NN0 )' % c
    r0 = w.s([], 'simpr', '( %s -> r e. NN0 )' % C0)
    up = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C0, f))
    mnr, qzr, ffr, mzr, mrr, qrr, qmzr, qmrr = [up(s_, f_) for s_, f_ in [(mn, 'M e. NN'), (qz, 'Q e. ZZ'), (ff, 'F : ZZ --> CC'), (mz, 'M e. ZZ'), (mr, 'M e. RR'), (qr, 'Q e. RR'), (qmz, '%s e. ZZ' % QM), (qmr, '%s e. RR' % QM)]]
    rz = D(w, C0, 'nn0zd', [r0], 'r e. ZZ'); rr = D(w, C0, 'nn0red', [r0], 'r e. RR')
    X = '( ( Q + r ) x. M )'
    xz = D(w, C0, 'zmulcld', [D(w, C0, 'zaddcld', [qzr, rz], '( Q + r ) e. ZZ'), mzr], '%s e. ZZ' % X)
    rmz = D(w, C0, 'zmulcld', [rz, mzr], '( r x. M ) e. ZZ')
    K = '( %s + ( ( r x. M ) - 1 ) )' % QM; K1 = '( %s + 1 )' % K
    N = '( %s + ( ( ( r + 1 ) x. M ) - 1 ) )' % QM
    kz = D(w, C0, 'zaddcld', [qmzr, D(w, C0, 'peano2zm' if False else 'zsubcld', [rmz, cst(w, C0, '1z', '1 e. ZZ')], '( ( r x. M ) - 1 ) e. ZZ')], '%s e. ZZ' % K)
    k1z = D(w, C0, 'peano2zd', [kz], '%s e. ZZ' % K1)
    r1mz = D(w, C0, 'zmulcld', [D(w, C0, 'peano2zd', [rz], '( r + 1 ) e. ZZ'), mzr], '( ( r + 1 ) x. M ) e. ZZ')
    nz = D(w, C0, 'zaddcld', [qmzr, D(w, C0, 'zsubcld', [r1mz, cst(w, C0, '1z', '1 e. ZZ')], '( ( ( r + 1 ) x. M ) - 1 ) e. ZZ')], '%s e. ZZ' % N)
    cl = Closure(w, C0, {'Q': qrr, 'M': mrr, 'r': rr})
    kx = lineq(w, C0, K1, X, closure=cl, products=True)
    r0g = D(w, C0, 'nn0ge0d', [r0], '0 <_ r'); m1 = D(w, C0, 'nnge1d', [mnr], '1 <_ M')
    le1 = nlinarith(w, C0, [r0g, m1], '%s <_ %s' % (QM, K1), closure=cl)
    le2 = nlinarith(w, C0, [m1], '%s <_ %s' % (K, N), closure=cl)
    k1u = D(w, C0, 'mpbir3and', [qmzr, k1z, le1, cst(w, C0, 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (K1, QM, QM, K1, QM, K1))], '%s e. ( ZZ>= ` %s )' % (K1, QM))
    nu = D(w, C0, 'mpbir3and', [kz, nz, le2, cst(w, C0, 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (N, K, K, N, K, N))], '%s e. ( ZZ>= ` %s )' % (N, K))
    W1 = '( ( %s ... %s ) u. ( %s ... %s ) )' % (QM, K, K1, N)
    wsp = D(w, C0, 'syl2anc', [k1u, nu, w.inst('fzsplit2')], '%s = %s' % (WIN('( r + 1 )'), W1))
    dis = D(w, C0, 'syl', [D(w, C0, 'zred' if False else 'ltp1d', [D(w, C0, 'zred', [kz], '%s e. RR' % K)], '%s < %s' % (K, K1)), w.inst('fzdisj')], '( ( %s ... %s ) i^i ( %s ... %s ) ) = (/)' % (QM, K, K1, N))
    Cn = '( %s /\\ n e. %s )' % (C0, WIN('( r + 1 )'))
    fnc = D(w, Cn, 'ffvelcdmd', [ad(w, Cn, ffr, 'F : ZZ --> CC'), w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, WIN('( r + 1 )'))), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % Cn)], '( F ` n ) e. CC')
    spl = D(w, C0, 'fsumsplit', [dis, wsp, D(w, C0, 'fzfid', [], '%s e. Fin' % WIN('( r + 1 )')), fnc],
            '%s = ( sum_ n e. ( %s ... %s ) ( F ` n ) + sum_ n e. ( %s ... %s ) ( F ` n ) )' % (LHSg('( r + 1 )'), QM, K, K1, N))
    # the new block, shifted
    M1 = '( M - 1 )'
    m1z_ = D(w, C0, 'zsubcld', [mzr, cst(w, C0, '1z', '1 e. ZZ')], '%s e. ZZ' % M1)
    Cb = '( %s /\\ b e. ( 0 ... %s ) )' % (C0, M1)
    bz = w.s([w.s([], 'simpr', '( %s -> b e. ( 0 ... %s ) )' % (Cb, M1)), w.inst('elfzelz')], 'syl', '( %s -> b e. ZZ )' % Cb)
    fbx = D(w, Cb, 'ffvelcdmd', [ad(w, Cb, ffr, 'F : ZZ --> CC'), D(w, Cb, 'zaddcld', [bz, ad(w, Cb, xz, '%s e. ZZ' % X)], '( b + %s ) e. ZZ' % X)], '( F ` ( b + %s ) ) e. CC' % X)
    shs = w.s([w.s([], 'oveq1', '( b = ( n - %s ) -> ( b + %s ) = ( ( n - %s ) + %s ) )' % (X, X, X, X))], 'fveq2d', '( b = ( n - %s ) -> ( F ` ( b + %s ) ) = ( F ` ( ( n - %s ) + %s ) ) )' % (X, X, X, X))
    sh = D(w, C0, 'fsumshft', [xz, cst(w, C0, '0z', '0 e. ZZ'), m1z_, fbx, shs],
           'sum_ b e. ( 0 ... %s ) ( F ` ( b + %s ) ) = sum_ n e. ( ( 0 + %s ) ... ( %s + %s ) ) ( F ` ( ( n - %s ) + %s ) )' % (M1, X, X, M1, X, X, X))
    xc = D(w, C0, 'zcnd', [xz], '%s e. CC' % X)
    lo = D(w, C0, 'eqtrd', [D(w, C0, 'addlidd', [xc], '( 0 + %s ) = %s' % (X, X)), D(w, C0, 'eqcomd', [kx], '%s = %s' % (X, K1))], '( 0 + %s ) = %s' % (X, K1))
    hi = lineq(w, C0, '( %s + %s )' % (M1, X), N, closure=cl, products=True)
    Cn2 = '( %s /\\ n e. ( ( 0 + %s ) ... ( %s + %s ) ) )' % (C0, X, M1, X)
    nzz = w.s([w.s([], 'simpr', '( %s -> n e. ( ( 0 + %s ) ... ( %s + %s ) ) )' % (Cn2, X, M1, X)), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % Cn2)
    np_ = D(w, Cn2, 'fveq2d', [D(w, Cn2, 'npcand', [D(w, Cn2, 'zcnd', [nzz], 'n e. CC'), ad(w, Cn2, xc, '%s e. CC' % X)], '( ( n - %s ) + %s ) = n' % (X, X))], '( F ` ( ( n - %s ) + %s ) ) = ( F ` n )' % (X, X))
    sh2 = D(w, C0, 'eqtrd', [sh, D(w, C0, 'eqtrd', [D(w, C0, 'sumeq2dv', [np_], 'sum_ n e. ( ( 0 + %s ) ... ( %s + %s ) ) ( F ` ( ( n - %s ) + %s ) ) = sum_ n e. ( ( 0 + %s ) ... ( %s + %s ) ) ( F ` n )' % (X, M1, X, X, X, X, M1, X)),
                                                     D(w, C0, 'sumeq1d', [D(w, C0, 'oveq12d', [lo, hi], '( ( 0 + %s ) ... ( %s + %s ) ) = ( %s ... %s )' % (X, M1, X, K1, N))],
                                                       'sum_ n e. ( ( 0 + %s ) ... ( %s + %s ) ) ( F ` n ) = sum_ n e. ( %s ... %s ) ( F ` n )' % (X, M1, X, K1, N))],
                                     'sum_ n e. ( ( 0 + %s ) ... ( %s + %s ) ) ( F ` ( ( n - %s ) + %s ) ) = sum_ n e. ( %s ... %s ) ( F ` n )' % (X, M1, X, X, X, K1, N))],
              'sum_ b e. ( 0 ... %s ) ( F ` ( b + %s ) ) = sum_ n e. ( %s ... %s ) ( F ` n )' % (M1, X, K1, N))
    fzo = D(w, C0, 'syl', [mzr, w.inst('fzoval')], '( 0 ..^ M ) = ( 0 ... %s )' % M1)
    BLKb = 'sum_ b e. ( 0 ..^ M ) ( F ` ( b + %s ) )' % X
    blk = D(w, C0, 'eqtrd', [D(w, C0, 'sumeq1d', [fzo], '%s = sum_ b e. ( 0 ... %s ) ( F ` ( b + %s ) )' % (BLKb, M1, X)), sh2], '%s = sum_ n e. ( %s ... %s ) ( F ` n )' % (BLKb, K1, N))
    # inner sums
    Cb2 = '( %s /\\ b e. ( 0 ..^ M ) )' % C0
    bz2 = w.s([w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Cb2), w.inst('elfzoelz')], 'syl', '( %s -> b e. ZZ )' % Cb2)
    QR = '( Q + ( r - 1 ) )'
    qrz = D(w, C0, 'zaddcld', [qzr, D(w, C0, 'peano2zm' if False else 'zsubcld', [rz, cst(w, C0, '1z', '1 e. ZZ')], '( r - 1 ) e. ZZ')], '%s e. ZZ' % QR)
    ge_ = linarith(w, C0, [r0g], '( Q - 1 ) <_ %s' % QR, closure=cl)
    qru = D(w, C0, 'mpbir3and', [D(w, C0, 'zsubcld', [qzr, cst(w, C0, '1z', '1 e. ZZ')], '( Q - 1 ) e. ZZ'), qrz, ge_, cst(w, C0, 'eluz2', '( %s e. ( ZZ>= ` ( Q - 1 ) ) <-> ( ( Q - 1 ) e. ZZ /\\ %s e. ZZ /\\ ( Q - 1 ) <_ %s ) )' % (QR, QR, QR))],
            '%s e. ( ZZ>= ` ( Q - 1 ) )' % QR)
    rg1 = D(w, C0, 'syl2anc', [qzr, qru, w.inst('fzsuc2')], '( Q ... ( %s + 1 ) ) = ( ( Q ... %s ) u. { ( %s + 1 ) } )' % (QR, QR, QR))
    re1 = lineq(w, C0, '( Q + ( ( r + 1 ) - 1 ) )', '( %s + 1 )' % QR, closure=cl)
    rq = lineq(w, C0, '( %s + 1 )' % QR, '( Q + r )', closure=cl)
    rng2 = D(w, C0, 'eqtrd', [D(w, C0, 'oveq2d', [re1], '%s = ( Q ... ( %s + 1 ) )' % (RNG('( r + 1 )'), QR)), rg1], '%s = ( ( Q ... %s ) u. { ( %s + 1 ) } )' % (RNG('( r + 1 )'), QR, QR))
    FB = lambda mm: '( F ` ( b + ( %s x. M ) ) )' % mm
    Cbm = '( %s /\\ m e. ( Q ... %s ) )' % (Cb2, QR)
    mzz = w.s([w.s([], 'simpr', '( %s -> m e. ( Q ... %s ) )' % (Cbm, QR)), w.inst('elfzelz')], 'syl', '( %s -> m e. ZZ )' % Cbm)
    fbm = D(w, Cbm, 'ffvelcdmd', [ad(w, Cbm, ad(w, Cb2, ffr, 'F : ZZ --> CC'), 'F : ZZ --> CC'), D(w, Cbm, 'zaddcld', [ad(w, Cbm, bz2, 'b e. ZZ'), D(w, Cbm, 'zmulcld', [mzz, ad(w, Cbm, ad(w, Cb2, mzr, 'M e. ZZ'), 'M e. ZZ')], '( m x. M ) e. ZZ')],
                                                                                               '( b + ( m x. M ) ) e. ZZ')], '%s e. CC' % FB('m'))
    QR1 = '( %s + 1 )' % QR
    msub = w.s([w.s([w.s([], 'oveq1', '( m = %s -> ( m x. M ) = ( %s x. M ) )' % (QR1, QR1))], 'oveq2d', '( m = %s -> ( b + ( m x. M ) ) = ( b + ( %s x. M ) ) )' % (QR1, QR1))], 'fveq2d',
               '( m = %s -> %s = %s )' % (QR1, FB('m'), FB(QR1)))
    fq1 = D(w, Cb2, 'ffvelcdmd', [ad(w, Cb2, ffr, 'F : ZZ --> CC'), D(w, Cb2, 'zaddcld', [bz2, D(w, Cb2, 'zmulcld', [ad(w, Cb2, D(w, C0, 'peano2zd', [qrz], '%s e. ZZ' % QR1), '%s e. ZZ' % QR1), ad(w, Cb2, mzr, 'M e. ZZ')], '( %s x. M ) e. ZZ' % QR1)],
                                                                                          '( b + ( %s x. M ) ) e. ZZ' % QR1)], '%s e. CC' % FB(QR1))
    ssn = w.s([w.s([], 'nfv', 'F/ m %s' % Cb2), w.s([], 'nfcv', 'F/_ m %s' % FB(QR1)), D(w, Cb2, 'fzfid', [], '( Q ... %s ) e. Fin' % QR), D(w, Cb2, 'elexd' if False else 'syl', [ad(w, Cb2, D(w, C0, 'peano2zd', [qrz], '%s e. ZZ' % QR1), '%s e. ZZ' % QR1), w.inst('elex')], '%s e. _V' % QR1),
               cst(w, Cb2, 'fzp1nel', '-. %s e. ( Q ... %s )' % (QR1, QR)), fbm, msub, fq1], 'fsumsplitsn',
              '( %s -> sum_ m e. ( ( Q ... %s ) u. { %s } ) %s = ( sum_ m e. ( Q ... %s ) %s + %s ) )' % (Cb2, QR, QR1, FB('m'), QR, FB('m'), FB(QR1)))
    inn1 = D(w, Cb2, 'eqtrd', [D(w, Cb2, 'sumeq1d', [ad(w, Cb2, rng2, '%s = ( ( Q ... %s ) u. { %s } )' % (RNG('( r + 1 )'), QR, QR1))], '%s = sum_ m e. ( ( Q ... %s ) u. { %s } ) %s' % (INN('( r + 1 )'), QR, QR1, FB('m'))), ssn],
               '%s = ( sum_ m e. ( Q ... %s ) %s + %s )' % (INN('( r + 1 )'), QR, FB('m'), FB(QR1)))
    t1 = D(w, Cb2, 'fveq2d', [D(w, Cb2, 'oveq2d', [D(w, Cb2, 'oveq1d', [ad(w, Cb2, rq, '%s = ( Q + r )' % QR1)], '( %s x. M ) = %s' % (QR1, X))], '( b + ( %s x. M ) ) = ( b + %s )' % (QR1, X))],
            '%s = ( F ` ( b + %s ) )' % (FB(QR1), X))
    rr_ = D(w, Cb2, 'sumeq1d', [ad(w, Cb2, D(w, C0, 'oveq2d', [D(w, C0, 'eqcomd', [lineq(w, C0, '( Q + ( r - 1 ) )', '( Q + ( r - 1 ) )', closure=cl)], '') if False else D(w, C0, 'eqidd', [], '%s = %s' % (RNG('r'), RNG('r')))], '') if False else D(w, C0, 'eqidd', [], '%s = ( Q ... %s )' % (RNG('r'), QR)), '%s = ( Q ... %s )' % (RNG('r'), QR))],
              '%s = sum_ m e. ( Q ... %s ) %s' % (INN('r'), QR, FB('m')))
    inn2 = D(w, Cb2, 'eqtr4d', [inn1, D(w, Cb2, 'oveq12d', [rr_, t1], '( %s + %s ) = ( sum_ m e. ( Q ... %s ) %s + ( F ` ( b + %s ) ) )' % (INN('r'), FB(QR1), QR, FB('m'), X))],
               '%s = ( %s + %s )' % (INN('( r + 1 )'), INN('r'), FB(QR1))) if False else None
    inn2 = D(w, Cb2, 'eqtrd', [inn1, D(w, Cb2, 'oveq12d', [D(w, Cb2, 'eqcomd', [rr_], 'sum_ m e. ( Q ... %s ) %s = %s' % (QR, FB('m'), INN('r'))), t1],
                                                         '( sum_ m e. ( Q ... %s ) %s + %s ) = ( %s + ( F ` ( b + %s ) ) )' % (QR, FB('m'), FB(QR1), INN('r'), X))],
               '%s = ( %s + ( F ` ( b + %s ) ) )' % (INN('( r + 1 )'), INN('r'), X))
    innc = D(w, Cb2, 'fsumcl', [D(w, Cb2, 'fzfid', [], '%s e. Fin' % RNG('r')), D(w, '( %s /\\ m e. %s )' % (Cb2, RNG('r')), 'idi', [fbm], '%s e. CC' % FB('m')) if False else fbm], '%s e. CC' % INN('r'))
    fbx2 = D(w, Cb2, 'ffvelcdmd', [ad(w, Cb2, ffr, 'F : ZZ --> CC'), D(w, Cb2, 'zaddcld', [bz2, ad(w, Cb2, xz, '%s e. ZZ' % X)], '( b + %s ) e. ZZ' % X)], '( F ` ( b + %s ) ) e. CC' % X)
    rhs1 = D(w, C0, 'eqtrd', [D(w, C0, 'sumeq2dv', [inn2], '%s = sum_ b e. ( 0 ..^ M ) ( %s + ( F ` ( b + %s ) ) )' % (RHSg('( r + 1 )'), INN('r'), X)),
                              D(w, C0, 'fsumadd', [cst(w, C0, 'fzofi', '( 0 ..^ M ) e. Fin'), innc, fbx2], 'sum_ b e. ( 0 ..^ M ) ( %s + ( F ` ( b + %s ) ) ) = ( %s + %s )' % (INN('r'), X, RHSg('r'), BLKb))],
               '%s = ( %s + %s )' % (RHSg('( r + 1 )'), RHSg('r'), BLKb))
    # combine with the induction hypothesis
    Cr = '( %s /\\ %s )' % (C0, PSg('r'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (Cr, PSg('r')))
    lr = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Cr, f))
    fin = chain(w, Cr, [LHSg('( r + 1 )'), '( %s + sum_ n e. ( %s ... %s ) ( F ` n ) )' % (LHSg('r'), K1, N), '( %s + %s )' % (RHSg('r'), BLKb), RHSg('( r + 1 )')],
                [lr(spl, '%s = ( %s + sum_ n e. ( %s ... %s ) ( F ` n ) )' % (LHSg('( r + 1 )'), LHSg('r'), K1, N)),
                 D(w, Cr, 'oveq12d', [ih, D(w, Cr, 'eqcomd', [lr(blk, '%s = sum_ n e. ( %s ... %s ) ( F ` n )' % (BLKb, K1, N))], 'sum_ n e. ( %s ... %s ) ( F ` n ) = %s' % (K1, N, BLKb))],
                   '( %s + sum_ n e. ( %s ... %s ) ( F ` n ) ) = ( %s + %s )' % (LHSg('r'), K1, N, RHSg('r'), BLKb)),
                 ('r', lr(rhs1, '%s = ( %s + %s )' % (RHSg('( r + 1 )'), RHSg('r'), BLKb)))])
    ind = w.s([h1, h2, h3, h4, base, fin], 'nn0indd', '( ( %s /\\ J e. NN0 ) -> %s )' % (c, PSg('J')))
    re_ = w.s([w.s([D(w, A, 'jca', [D(w, A, 'jca', [D(w, A, 'simpl1', [], 'M e. NN'), D(w, A, 'simpl2', [], 'Q e. ZZ')], '( M e. NN /\\ Q e. ZZ )'), D(w, A, 'simpr', [], 'F : ZZ --> CC')], c),
                    D(w, A, 'simpl3', [], 'J e. NN0')], 'jca', '( %s -> ( %s /\\ J e. NN0 ) )' % (A, c)), ind], 'syl', S['zl3frg'].replace('qed', 'qed'))
    w.lines[-1] = w.lines[-1].replace(w.lines[-1].split(':')[0] + ':', 'qed:', 1)
    go(w)


def fboundv(w, A, bnd, X, xz, v, F='F', C='C'):
    """as fbound with the bound letter v"""
    sub = w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (v, X, F, v, F, X))], 'fveq2d', '( %s = %s -> ( abs ` ( %s ` %s ) ) = ( abs ` ( %s ` %s ) ) )' % (v, X, F, v, F, X)),
               w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( abs ` %s ) = ( abs ` %s ) )' % (v, X, v, X))], 'oveq2d', '( %s = %s -> ( %s ^ ( abs ` %s ) ) = ( %s ^ ( abs ` %s ) ) )' % (v, X, H2, v, H2, X))], 'oveq2d',
                   '( %s = %s -> ( %s x. ( %s ^ ( abs ` %s ) ) ) = ( %s x. ( %s ^ ( abs ` %s ) ) ) )' % (v, X, C, H2, v, C, H2, X))],
              'breq12d', '( %s = %s -> ( ( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) ) <-> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) ) ) )' % (v, X, F, v, C, H2, v, F, X, C, H2, X))
    return D(w, A, 'rspcdva', [sub, bnd, xz], '( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) )' % (F, X, C, H2, X))


def hb_cbv(w, v1, v2, F='F', C='C'):
    """closed: ( A. v1 ... <-> A. v2 ... )"""
    B = lambda v: 'A. %s e. ZZ ( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) )' % (v, F, v, C, H2, v)
    sub = w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (v1, v2, F, v1, F, v2))], 'fveq2d', '( %s = %s -> ( abs ` ( %s ` %s ) ) = ( abs ` ( %s ` %s ) ) )' % (v1, v2, F, v1, F, v2)),
               w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( abs ` %s ) = ( abs ` %s ) )' % (v1, v2, v1, v2))], 'oveq2d', '( %s = %s -> ( %s ^ ( abs ` %s ) ) = ( %s ^ ( abs ` %s ) ) )' % (v1, v2, H2, v1, H2, v2))], 'oveq2d',
                   '( %s = %s -> ( %s x. ( %s ^ ( abs ` %s ) ) ) = ( %s x. ( %s ^ ( abs ` %s ) ) ) )' % (v1, v2, C, H2, v1, C, H2, v2))],
              'breq12d', '( %s = %s -> ( ( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) ) <-> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s ^ ( abs ` %s ) ) ) ) )' % (v1, v2, F, v1, C, H2, v1, F, v2, C, H2, v2))
    return w.s([sub], 'cbvralvw', '( %s <-> %s )' % (B(v1), B(v2))), B


# ---------------------------------------------------------------- zl3rgb
if want('zl3rgb'):
    w = W('zl3rgb', 'The residue class ` m |-> F ( b + m M ) ` inherits the majorant, with the constant ` C 2 ^ M ` .')
    A, Cc = ante_of('zl3rgb')
    cb, BB = hb_cbv(w, 'i', 'j')
    A0 = '( ( ( M e. NN /\\ b e. ( 0 ..^ M ) ) /\\ ( F : ZZ --> CC /\\ C e. RR ) ) /\\ %s )' % BB('j')
    mn = D(w, A0, 'simplll', [], 'M e. NN'); bo = D(w, A0, 'simpllr', [], 'b e. ( 0 ..^ M )')
    ff = D(w, A0, 'simplrl', [], 'F : ZZ --> CC'); cr = D(w, A0, 'simplrr', [], 'C e. RR'); bj = D(w, A0, 'simpr', [], BB('j'))
    mz = D(w, A0, 'nnzd', [mn], 'M e. ZZ'); mr = D(w, A0, 'nnred', [mn], 'M e. RR'); m0 = D(w, A0, 'nnnn0d', [mn], 'M e. NN0')
    bz = D(w, A0, 'syl', [bo, w.inst('elfzoelz')], 'b e. ZZ'); br = D(w, A0, 'zred', [bz], 'b e. RR')
    b0 = D(w, A0, 'syl', [bo, w.inst('elfzole1')], '0 <_ b'); bm = D(w, A0, 'syl', [bo, w.inst('elfzolt2')], 'b < M')
    # C >_ 0
    f0 = fboundv(w, A0, bj, '0', cst(w, A0, '0z', '0 e. ZZ'), 'j')
    one = D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [cst(w, A0, 'abs0', '( abs ` 0 ) = 0')], '( %s ^ ( abs ` 0 ) ) = ( %s ^ 0 )' % (H2, H2)), cst(w, A0, 'idi' if False else 'halfcn', '') if False else
                             w.s([w.s([w.s([], 'halfcn', '%s e. CC' % H2), w.inst('exp0')], 'ax-mp', '( %s ^ 0 ) = 1' % H2)], 'a1i', '( %s -> ( %s ^ 0 ) = 1 )' % (A0, H2))], '( %s ^ ( abs ` 0 ) ) = 1' % H2)
    f0c = D(w, A0, 'ffvelcdmd', [ff, cst(w, A0, '0z', '0 e. ZZ')], '( F ` 0 ) e. CC')
    c0 = D(w, A0, 'letrd', [cst(w, A0, '0re', '0 e. RR'), D(w, A0, 'abscld', [f0c], '( abs ` ( F ` 0 ) ) e. RR'), cr, D(w, A0, 'absge0d', [f0c], '0 <_ ( abs ` ( F ` 0 ) )'),
                            D(w, A0, 'breqtrd', [f0, D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [one], '( C x. ( %s ^ ( abs ` 0 ) ) ) = ( C x. 1 )' % H2), D(w, A0, 'mulridd', [D(w, A0, 'recnd', [cr], 'C e. CC')], '( C x. 1 ) = C')],
                                                                        '( C x. ( %s ^ ( abs ` 0 ) ) ) = C' % H2)], '( abs ` ( F ` 0 ) ) <_ C')], '0 <_ C')
    GBm = L.GB()
    Ai = '( %s /\\ i e. ZZ )' % A0
    iz = w.s([], 'simpr', '( %s -> i e. ZZ )' % Ai)
    up = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Ai, f))
    ib = '( b + ( i x. M ) )'
    ibz = D(w, Ai, 'zaddcld', [up(bz, 'b e. ZZ'), D(w, Ai, 'zmulcld', [iz, up(mz, 'M e. ZZ')], '( i x. M ) e. ZZ')], '%s e. ZZ' % ib)
    gsub = w.s([w.s([w.s([], 'oveq1', '( m = i -> ( m x. M ) = ( i x. M ) )')], 'oveq2d', '( m = i -> ( b + ( m x. M ) ) = %s )' % ib)], 'fveq2d', '( m = i -> ( F ` ( b + ( m x. M ) ) ) = ( F ` %s ) )' % ib)
    gv = D(w, Ai, 'syl', [iz, w.s([gsub, w.s([], 'eqid', '%s = %s' % (GBm, GBm)), w.s([], 'fvex', '( F ` %s ) e. _V' % ib)], 'fvmpt', '( i e. ZZ -> ( %s ` i ) = ( F ` %s ) )' % (GBm, ib))],
           '( %s ` i ) = ( F ` %s )' % (GBm, ib))
    fb = fboundv(w, Ai, up(bj, BB('j')), ib, ibz, 'j')
    AI, AB = '( abs ` i )', '( abs ` %s )' % ib
    ai0 = D(w, Ai, 'syl', [iz, w.inst('nn0abscl')], '%s e. NN0' % AI); ab0 = D(w, Ai, 'syl', [ibz, w.inst('nn0abscl')], '%s e. NN0' % AB)
    air = D(w, Ai, 'nn0red', [ai0], '%s e. RR' % AI); abr = D(w, Ai, 'nn0red', [ab0], '%s e. RR' % AB)
    ic = D(w, Ai, 'zcnd', [iz], 'i e. CC'); mc = D(w, Ai, 'recnd', [up(mr, 'M e. RR')], 'M e. CC'); bc = D(w, Ai, 'zcnd', [up(bz, 'b e. ZZ')], 'b e. CC')
    imc = D(w, Ai, 'mulcld', [ic, mc], '( i x. M ) e. CC')
    am = D(w, Ai, 'eqtrd', [D(w, Ai, 'absmuld', [ic, mc], '( abs ` ( i x. M ) ) = ( %s x. ( abs ` M ) )' % AI),
                            D(w, Ai, 'oveq2d', [D(w, Ai, 'absidd', [up(mr, 'M e. RR'), D(w, Ai, 'nnge1d' if False else 'nn0ge0d', [up(m0, 'M e. NN0')], '0 <_ M')], '( abs ` M ) = M')], '( %s x. ( abs ` M ) ) = ( %s x. M )' % (AI, AI))],
           '( abs ` ( i x. M ) ) = ( %s x. M )' % AI)
    dd = D(w, Ai, 'breqtrrd' if False else 'eqbrtrrd', [D(w, Ai, 'fveq2d', [D(w, Ai, 'pncan2d', [bc, imc], '( %s - b ) = ( i x. M )' % ib)], '( abs ` ( %s - b ) ) = ( abs ` ( i x. M ) )' % ib),
                                                       D(w, Ai, 'abs2dif2d', [D(w, Ai, 'addcld', [bc, imc], '%s e. CC' % ib), bc], '( abs ` ( %s - b ) ) <_ ( %s + ( abs ` b ) )' % (ib, AB))],
            '( abs ` ( i x. M ) ) <_ ( %s + ( abs ` b ) )' % AB)
    dd2 = D(w, Ai, 'breqtrrd' if False else 'eqbrtrrd', [am, dd], '( %s x. M ) <_ ( %s + ( abs ` b ) )' % (AI, AB))
    abb = D(w, Ai, 'absidd', [up(br, 'b e. RR'), up(b0, '0 <_ b')], '( abs ` b ) = b')
    dd3 = D(w, Ai, 'breqtrd', [dd2, D(w, Ai, 'oveq2d', [abb], '( %s + ( abs ` b ) ) = ( %s + b )' % (AB, AB))], '( %s x. M ) <_ ( %s + b )' % (AI, AB))
    ile = nlinarith(w, Ai, [dd3, up(bm, 'b < M'), D(w, Ai, 'nnge1d', [up(mn, 'M e. NN')], '1 <_ M'), D(w, Ai, 'nn0ge0d', [ai0], '0 <_ %s' % AI)], '%s <_ ( %s + M )' % (AI, AB),
                    leaves={AI: air, AB: abr, 'M': up(mr, 'M e. RR'), 'b': up(br, 'b e. RR')}, atoms=[AI, AB])
    ABM = '( %s + M )' % AB
    abmz = D(w, Ai, 'nn0zd', [D(w, Ai, 'nn0addcld', [ab0, up(m0, 'M e. NN0')], '%s e. NN0' % ABM)], '%s e. ZZ' % ABM)
    uz = D(w, Ai, 'mpbir3and', [D(w, Ai, 'nn0zd', [ai0], '%s e. ZZ' % AI), abmz, ile, cst(w, Ai, 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (ABM, AI, AI, ABM, AI, ABM))],
           '%s e. ( ZZ>= ` %s )' % (ABM, AI))
    le = D(w, Ai, 'syl2anc', [D(w, Ai, '3jca', [cst(w, Ai, 'halfre', '%s e. RR' % H2), ai0, uz], '( %s e. RR /\\ %s e. NN0 /\\ %s e. ( ZZ>= ` %s ) )' % (H2, AI, ABM, AI)),
                              D(w, Ai, 'jca', [cst(w, Ai, 'halfge0', '0 <_ %s' % H2), cst(w, Ai, 'halflt1' if False else 'halfle1' if False else 'idi', '') if False else
                                               D(w, Ai, 'ltled', [cst(w, Ai, 'halfre', '%s e. RR' % H2), cst(w, Ai, '1re', '1 e. RR'), cst(w, Ai, 'halflt1', '%s < 1' % H2)], '%s <_ 1' % H2)],
                                '( 0 <_ %s /\\ %s <_ 1 )' % (H2, H2)), w.inst('leexp2r')], '( %s ^ %s ) <_ ( %s ^ %s )' % (H2, ABM, H2, AI))
    X_, Y_, Z_, P_ = '( %s ^ %s )' % (H2, AB), '( %s ^ %s )' % (H2, ABM), '( %s ^ %s )' % (H2, AI), '( 2 ^ M )'
    hc = cst(w, Ai, 'halfcn', '%s e. CC' % H2); tc = cst(w, Ai, '2cn', '2 e. CC')
    ea = D(w, Ai, 'expaddd', [hc, up(m0, 'M e. NN0'), ab0], '%s = ( %s x. ( %s ^ M ) )' % (Y_, X_, H2))
    xc = D(w, Ai, 'expcld', [hc, ab0], '%s e. CC' % X_); hm = D(w, Ai, 'expcld', [hc, up(m0, 'M e. NN0')], '( %s ^ M ) e. CC' % H2); pc = D(w, Ai, 'expcld', [tc, up(m0, 'M e. NN0')], '%s e. CC' % P_)
    two1 = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0'), w.inst('recid')], 'mp2an', '( 2 x. %s ) = 1' % H2)], 'a1i', '( %s -> ( 2 x. %s ) = 1 )' % (Ai, H2))
    pm = chain(w, Ai, ['( %s x. ( %s ^ M ) )' % (P_, H2), '( ( 2 x. %s ) ^ M )' % H2, '( 1 ^ M )', '1'],
               [('r', D(w, Ai, 'mulexpd', [tc, hc, up(m0, 'M e. NN0')], '( ( 2 x. %s ) ^ M ) = ( %s x. ( %s ^ M ) )' % (H2, P_, H2))),
                D(w, Ai, 'oveq1d', [two1], '( ( 2 x. %s ) ^ M ) = ( 1 ^ M )' % H2), D(w, Ai, 'syl', [up(mz, 'M e. ZZ'), w.inst('1exp')], '( 1 ^ M ) = 1')])
    # P x. Y = X
    py = chain(w, Ai, ['( %s x. %s )' % (P_, Y_), '( %s x. ( %s x. ( %s ^ M ) ) )' % (P_, X_, H2), '( %s x. ( %s x. ( %s ^ M ) ) )' % (X_, P_, H2), '( %s x. 1 )' % X_, X_],
               [D(w, Ai, 'oveq2d', [ea], '( %s x. %s ) = ( %s x. ( %s x. ( %s ^ M ) ) )' % (P_, Y_, P_, X_, H2)), D(w, Ai, 'mul12d', [pc, xc, hm], '( %s x. ( %s x. ( %s ^ M ) ) ) = ( %s x. ( %s x. ( %s ^ M ) ) )' % (P_, X_, H2, X_, P_, H2)),
                D(w, Ai, 'oveq2d', [pm], '( %s x. ( %s x. ( %s ^ M ) ) ) = ( %s x. 1 )' % (X_, P_, H2, X_)), D(w, Ai, 'mulridd', [xc], '( %s x. 1 ) = %s' % (X_, X_))])
    crr = up(cr, 'C e. RR')
    cx = D(w, Ai, 'eqtr3d', [D(w, Ai, 'oveq2d', [py], '( C x. ( %s x. %s ) ) = ( C x. %s )' % (P_, Y_, X_)),
                             D(w, Ai, 'mulassd', [D(w, Ai, 'recnd', [crr], 'C e. CC'), pc, D(w, Ai, 'expcld', [hc, D(w, Ai, 'nn0addcld', [ab0, up(m0, 'M e. NN0')], '%s e. NN0' % ABM)], '%s e. CC' % Y_)],
                               '( ( C x. %s ) x. %s ) = ( C x. ( %s x. %s ) )' % (P_, Y_, P_, Y_))], '( C x. %s ) = ( ( C x. %s ) x. %s )' % (X_, P_, Y_)) if False else None
    cx = D(w, Ai, 'eqtrd', [D(w, Ai, 'mulassd', [D(w, Ai, 'recnd', [crr], 'C e. CC'), pc, D(w, Ai, 'expcld', [hc, D(w, Ai, 'nn0addcld', [ab0, up(m0, 'M e. NN0')], '%s e. NN0' % ABM)], '%s e. CC' % Y_)],
                                   '( ( C x. %s ) x. %s ) = ( C x. ( %s x. %s ) )' % (P_, Y_, P_, Y_)), D(w, Ai, 'oveq2d', [py], '( C x. ( %s x. %s ) ) = ( C x. %s )' % (P_, Y_, X_))],
            '( ( C x. %s ) x. %s ) = ( C x. %s )' % (P_, Y_, X_))
    CP = '( C x. %s )' % P_
    cpr = D(w, Ai, 'remulcld', [crr, D(w, Ai, 'reexpcld', [cst(w, Ai, '2re', '2 e. RR'), up(m0, 'M e. NN0')], '%s e. RR' % P_)], '%s e. RR' % CP)
    cp0 = D(w, Ai, 'mulge0d', [crr, D(w, Ai, 'reexpcld', [cst(w, Ai, '2re', '2 e. RR'), up(m0, 'M e. NN0')], '%s e. RR' % P_), up(c0, '0 <_ C'),
                               D(w, Ai, 'expge0d', [cst(w, Ai, '2re', '2 e. RR'), up(m0, 'M e. NN0'), cst(w, Ai, '0le2', '0 <_ 2')], '0 <_ %s' % P_)], '0 <_ %s' % CP)
    GA = '( abs ` ( F ` %s ) )' % ib
    yr = D(w, Ai, 'reexpcld', [cst(w, Ai, 'halfre', '%s e. RR' % H2), D(w, Ai, 'nn0addcld', [ab0, up(m0, 'M e. NN0')], '%s e. NN0' % ABM)], '%s e. RR' % Y_)
    zr = D(w, Ai, 'reexpcld', [cst(w, Ai, 'halfre', '%s e. RR' % H2), ai0], '%s e. RR' % Z_)
    xr = D(w, Ai, 'reexpcld', [cst(w, Ai, 'halfre', '%s e. RR' % H2), ab0], '%s e. RR' % X_)
    fin0 = nlinarith(w, Ai, [fb, cx, le, cp0], '%s <_ ( %s x. %s )' % (GA, CP, Z_),
                     leaves={GA: D(w, Ai, 'abscld', [D(w, Ai, 'ffvelcdmd', [up(ff, 'F : ZZ --> CC'), ibz], '( F ` %s ) e. CC' % ib)], '%s e. RR' % GA), CP: cpr, Y_: yr, Z_: zr, X_: xr, 'C': crr},
                     atoms=[GA, CP, Y_, Z_, X_])
    fin1 = D(w, Ai, 'eqbrtrd', [D(w, Ai, 'fveq2d', [gv], '( abs ` ( %s ` i ) ) = %s' % (GBm, GA)), fin0], '( abs ` ( %s ` i ) ) <_ ( %s x. %s )' % (GBm, CP, Z_))
    ral = D(w, A0, 'ralrimiva', [fin1], 'A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. %s )' % (GBm, CP, Z_))
    gf = D(w, A0, 'fmptd', [D(w, '( %s /\\ m e. ZZ )' % A0, 'ffvelcdmd', [ad(w, '( %s /\\ m e. ZZ )' % A0, ff, 'F : ZZ --> CC'),
                                                                        D(w, '( %s /\\ m e. ZZ )' % A0, 'zaddcld', [ad(w, '( %s /\\ m e. ZZ )' % A0, bz, 'b e. ZZ'),
                                                                                                                  D(w, '( %s /\\ m e. ZZ )' % A0, 'zmulcld', [w.s([], 'simpr', '( ( %s /\\ m e. ZZ ) -> m e. ZZ )' % A0), ad(w, '( %s /\\ m e. ZZ )' % A0, mz, 'M e. ZZ')], '( m x. M ) e. ZZ')],
                                                                          '( b + ( m x. M ) ) e. ZZ')], '( F ` ( b + ( m x. M ) ) ) e. CC'), w.s([], 'eqid', '%s = %s' % (GBm, GBm))], '%s : ZZ --> CC' % GBm)
    res = D(w, A0, 'jca', [gf, D(w, A0, 'jca', [cpr if False else D(w, A0, 'remulcld', [cr, D(w, A0, 'reexpcld', [cst(w, A0, '2re', '2 e. RR'), m0], '%s e. RR' % P_)], '%s e. RR' % CP), ral],
                                            '( %s e. RR /\\ A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. %s ) )' % (CP, GBm, CP, Z_))], Cc)
    # A -> A0
    a1 = D(w, A, 'jca', [D(w, A, 'jca', [D(w, A, 'simpll', [], 'M e. NN'), D(w, A, 'simpr', [], 'b e. ( 0 ..^ M )')], '( M e. NN /\\ b e. ( 0 ..^ M ) )'),
                         D(w, A, 'jca', [D(w, A, 'simplrl', [], 'F : ZZ --> CC'), D(w, A, 'simplrd' if False else 'simplrr', [], '( C e. RR /\\ %s )' % BB('i'))], '') if False else
                         D(w, A, 'jca', [D(w, A, 'simplrl', [], 'F : ZZ --> CC'), D(w, A, 'simpld', [D(w, A, 'simplrr', [], '( C e. RR /\\ %s )' % BB('i'))], 'C e. RR')], '( F : ZZ --> CC /\\ C e. RR )')],
           '( ( M e. NN /\\ b e. ( 0 ..^ M ) ) /\\ ( F : ZZ --> CC /\\ C e. RR ) )')
    a2 = D(w, A, 'sylib', [D(w, A, 'simprd', [D(w, A, 'simplrr', [], '( C e. RR /\\ %s )' % BB('i'))], BB('i')), cb], BB('j')) if False else \
        w.s([D(w, A, 'simprd', [D(w, A, 'simplrr', [], '( C e. RR /\\ %s )' % BB('i'))], BB('i')), cb], 'sylib', '( %s -> %s )' % (A, BB('j')))
    w.qed([D(w, A, 'jca', [a1, a2], A0), res], 'syl', S['zl3rgb'])
    go(w)


def c_ge0(w, A, ff, cr, bnd, v='i'):
    """( A -> 0 <_ C ) from the majorant at 0"""
    f0 = fboundv(w, A, bnd, '0', cst(w, A, '0z', '0 e. ZZ'), v)
    one = D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [cst(w, A, 'abs0', '( abs ` 0 ) = 0')], '( %s ^ ( abs ` 0 ) ) = ( %s ^ 0 )' % (H2, H2)),
                           w.s([w.s([w.s([], 'halfcn', '%s e. CC' % H2), w.inst('exp0')], 'ax-mp', '( %s ^ 0 ) = 1' % H2)], 'a1i', '( %s -> ( %s ^ 0 ) = 1 )' % (A, H2))], '( %s ^ ( abs ` 0 ) ) = 1' % H2)
    f0c = D(w, A, 'ffvelcdmd', [ff, cst(w, A, '0z', '0 e. ZZ')], '( F ` 0 ) e. CC')
    return D(w, A, 'letrd', [cst(w, A, '0re', '0 e. RR'), D(w, A, 'abscld', [f0c], '( abs ` ( F ` 0 ) ) e. RR'), cr, D(w, A, 'absge0d', [f0c], '0 <_ ( abs ` ( F ` 0 ) )'),
                             D(w, A, 'breqtrd', [f0, D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [one], '( C x. ( %s ^ ( abs ` 0 ) ) ) = ( C x. 1 )' % H2), D(w, A, 'mulridd', [D(w, A, 'recnd', [cr], 'C e. CC')], '( C x. 1 ) = C')],
                                                                         '( C x. ( %s ^ ( abs ` 0 ) ) ) = C' % H2)], '( abs ` ( F ` 0 ) ) <_ C')], '0 <_ C')


def pz_cl(w, A, G, gf, cvg):
    """( A -> PZ(G) e. CC ) from gf: G : ZZ --> CC, cvg: seq 1 ( + , ( n e. NN |-> pair ) ) e. dom ~~>"""
    PR = lambda v: '( ( %s ` %s ) + ( %s ` -u %s ) )' % (G, v, G, v)
    PMn, PMm = '( n e. NN |-> %s )' % PR('n'), '( q e. NN |-> %s )' % PR('q')
    sub = lambda a, b: w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (a, b, G, a, G, b)),
                            w.s([w.s([], 'negeq', '( %s = %s -> -u %s = -u %s )' % (a, b, a, b))], 'fveq2d', '( %s = %s -> ( %s ` -u %s ) = ( %s ` -u %s ) )' % (a, b, G, a, G, b))],
                           'oveq12d', '( %s = %s -> %s = %s )' % (a, b, PR(a), PR(b)))
    pmeq = w.s([sub('q', 'n')], 'cbvmptv', '%s = %s' % (PMm, PMn))
    cvm = D(w, A, 'mpbird', [cvg, w.s([w.s([w.s([pmeq, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (PMm, PMn))], 'eleq1i',
                                          '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (PMm, PMn))], 'a1i', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A, PMm, PMn))],
            'seq 1 ( + , %s ) e. dom ~~>' % PMm)
    An = '( %s /\\ n e. NN )' % A
    nz = D(w, An, 'nnzd', [w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'n e. ZZ')
    pv = D(w, An, 'syl', [w.s([], 'simpr', '( %s -> n e. NN )' % An), w.s([sub('q', 'n'), w.s([], 'eqid', '%s = %s' % (PMm, PMm)), w.s([], 'ovex', '%s e. _V' % PR('n'))], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (PMm, PR('n')))],
           '( %s ` n ) = %s' % (PMm, PR('n')))
    pc = D(w, An, 'addcld', [D(w, An, 'ffvelcdmd', [ad(w, An, gf, '%s : ZZ --> CC' % G), nz], '( %s ` n ) e. CC' % G), D(w, An, 'ffvelcdmd', [ad(w, An, gf, '%s : ZZ --> CC' % G), D(w, An, 'znegcld', [nz], '-u n e. ZZ')], '( %s ` -u n ) e. CC' % G)],
           '%s e. CC' % PR('n'))
    sc = D(w, A, 'isumcl', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), pv, pc, cvm], 'sum_ n e. NN %s e. CC' % PR('n'))
    return D(w, A, 'addcld', [D(w, A, 'ffvelcdmd', [gf, cst(w, A, '0z', '0 e. ZZ')], '( %s ` 0 ) e. CC' % G), sc], '%s e. CC' % L.PZF(G))


# ---------------------------------------------------------------- zl3rg
if want('zl3rg'):
    w = W('zl3rg', 'Regrouping a sum over ` ZZ ` with a geometric majorant by the residues modulo ` M ` .')
    A, Cc = ante_of('zl3rg')
    HBv = L.HBF()
    mn = D(w, A, 'simpl', [], 'M e. NN'); hb = D(w, A, 'simpr', [], HBv)
    ff, cr, bnd = hb_facts(w, A, hb)
    BI = 'A. i e. ZZ ( abs ` ( F ` i ) ) <_ ( C x. ( %s ^ ( abs ` i ) ) )' % H2
    c0 = c_ge0(w, A, ff, cr, bnd)
    mz = D(w, A, 'nnzd', [mn], 'M e. ZZ'); mr = D(w, A, 'nnred', [mn], 'M e. RR'); m0 = D(w, A, 'nnnn0d', [mn], 'M e. NN0')
    pzt = D(w, A, 'syl', [hb, w.inst('zl3pzt')], '( seq 1 ( + , ( n e. NN |-> ( ( F ` n ) + ( F ` -u n ) ) ) ) e. dom ~~> /\\ A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. C ) x. ( %s ^ j ) ) )'
            % (L.PZF('F'), L.SYM('F', 'j'), H2))
    PZF_ = L.PZF('F')
    pzfc = pz_cl(w, A, 'F', ff, D(w, A, 'simpld', [pzt], 'seq 1 ( + , ( n e. NN |-> ( ( F ` n ) + ( F ` -u n ) ) ) ) e. dom ~~>'))
    GBb = L.GB(); PZg = L.PZF(GBb)
    CB = '( C x. ( 2 ^ M ) )'
    Ab = '( %s /\\ b e. ( 0 ..^ M ) )' % A
    hbb = D(w, Ab, 'syl', [w.s([], 'idi', '( %s -> %s )' % (Ab, Ab)) if False else D(w, Ab, 'id', [], Ab), w.inst('zl3rgb')], L.HBF(GBb, CB))
    pztb = D(w, Ab, 'syl', [hbb, w.inst('zl3pzt')], '( seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) + ( %s ` -u n ) ) ) ) e. dom ~~> /\\ A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) x. ( %s ^ j ) ) )'
             % (GBb, GBb, PZg, L.SYM(GBb, 'j'), CB, H2))
    gbf = D(w, Ab, 'simpld', [hbb], '%s : ZZ --> CC' % GBb)
    pzgc = pz_cl(w, Ab, GBb, gbf, D(w, Ab, 'simpld', [pztb], 'seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) + ( %s ` -u n ) ) ) ) e. dom ~~>' % (GBb, GBb)))
    LL = 'sum_ b e. ( 0 ..^ M ) %s' % PZg
    llc = D(w, A, 'fsumcl', [cst(w, A, 'fzofi', '( 0 ..^ M ) e. Fin'), pzgc], '%s e. CC' % LL)
    # at K
    AK = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % AK)
    u = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (AK, f))
    mnK, mzK, mrK, m0K, ffK, crK, c0K, bndK = u(mn, 'M e. NN'), u(mz, 'M e. ZZ'), u(mr, 'M e. RR'), u(m0, 'M e. NN0'), u(ff, 'F : ZZ --> CC'), u(cr, 'C e. RR'), u(c0, '0 <_ C'), u(bnd, BI)
    kz = D(w, AK, 'nnzd', [kn], 'k e. ZZ'); kr = D(w, AK, 'nnred', [kn], 'k e. RR'); k0 = D(w, AK, 'nnnn0d', [kn], 'k e. NN0')
    KM = '( k x. M )'
    kmz = D(w, AK, 'zmulcld', [kz, mzK], '%s e. ZZ' % KM); kmr = D(w, AK, 'zred', [kmz], '%s e. RR' % KM)
    cl = Closure(w, AK, {'k': kr, 'M': mrK, 'C': crK})
    J2 = '( ( 2 x. k ) + 1 )'
    j2 = D(w, AK, 'nn0addcld' if False else 'syl', [D(w, AK, 'nn0mulcld' if False else 'jca', [], '') if False else None], '') if False else None
    j20 = D(w, AK, 'nn0addcld', [D(w, AK, 'nn0mulcld', [cst(w, AK, '2nn0', '2 e. NN0'), k0], '( 2 x. k ) e. NN0'), cst(w, AK, '1nn0', '1 e. NN0')], '%s e. NN0' % J2)
    nkz = D(w, AK, 'znegcld', [kz], '-u k e. ZZ')
    WIN0 = '( ( -u k x. M ) ... ( ( -u k x. M ) + ( ( %s x. M ) - 1 ) ) )' % J2
    RNG0 = '( -u k ... ( -u k + ( %s - 1 ) ) )' % J2
    frg = D(w, AK, 'syl2anc', [D(w, AK, '3jca', [mnK, nkz, j20], '( M e. NN /\\ -u k e. ZZ /\\ %s e. NN0 )' % J2), ffK, w.inst('zl3frg')],
            'sum_ n e. %s ( F ` n ) = sum_ b e. ( 0 ..^ M ) sum_ m e. %s ( F ` ( b + ( m x. M ) ) )' % (WIN0, RNG0))
    TOP = '( %s + ( M - 1 ) )' % KM
    e1 = D(w, AK, 'mulneg1d', [D(w, AK, 'recnd', [kr], 'k e. CC'), D(w, AK, 'recnd', [mrK], 'M e. CC')], '( -u k x. M ) = -u %s' % KM)
    e2 = lineq(w, AK, '( ( -u k x. M ) + ( ( %s x. M ) - 1 ) )' % J2, TOP, closure=cl, products=True)
    e3 = lineq(w, AK, '( -u k + ( %s - 1 ) )' % J2, 'k', closure=cl)
    WIN = '( -u %s ... %s )' % (KM, TOP)
    V = 'sum_ n e. %s ( F ` n )' % WIN
    INm = 'sum_ m e. ( -u k ... k ) ( F ` ( b + ( m x. M ) ) )'
    wv = D(w, AK, 'sumeq1d', [D(w, AK, 'oveq12d', [e1, e2], '%s = %s' % (WIN0, WIN))], 'sum_ n e. %s ( F ` n ) = %s' % (WIN0, V))
    rv = D(w, AK, 'sumeq2dv', [w.s([D(w, AK, 'sumeq1d', [D(w, AK, 'oveq2d', [e3], '%s = ( -u k ... k )' % RNG0)], 'sum_ m e. %s ( F ` ( b + ( m x. M ) ) ) = %s' % (RNG0, INm))],
                                   'adantr', '( ( %s /\\ b e. ( 0 ..^ M ) ) -> sum_ m e. %s ( F ` ( b + ( m x. M ) ) ) = %s )' % (AK, RNG0, INm))],
            'sum_ b e. ( 0 ..^ M ) sum_ m e. %s ( F ` ( b + ( m x. M ) ) ) = sum_ b e. ( 0 ..^ M ) %s' % (RNG0, INm))
    AKb = '( %s /\\ b e. ( 0 ..^ M ) )' % AK
    bo = w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % AKb)
    SYMb = L.SYM(GBb, 'k')
    AKbn = '( %s /\\ n e. ( -u k ... k ) )' % AKb
    nzz = w.s([w.s([], 'simpr', '( %s -> n e. ( -u k ... k ) )' % AKbn), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % AKbn)
    gsub = w.s([w.s([w.s([], 'oveq1', '( m = n -> ( m x. M ) = ( n x. M ) )')], 'oveq2d', '( m = n -> ( b + ( m x. M ) ) = ( b + ( n x. M ) ) )')], 'fveq2d',
               '( m = n -> ( F ` ( b + ( m x. M ) ) ) = ( F ` ( b + ( n x. M ) ) ) )')
    gvn = D(w, AKbn, 'syl', [nzz, w.s([gsub, w.s([], 'eqid', '%s = %s' % (GBb, GBb)), w.s([], 'fvex', '( F ` ( b + ( n x. M ) ) ) e. _V')], 'fvmpt', '( n e. ZZ -> ( %s ` n ) = ( F ` ( b + ( n x. M ) ) ) )' % GBb)],
            '( %s ` n ) = ( F ` ( b + ( n x. M ) ) )' % GBb)
    s1 = D(w, AKb, 'sumeq2dv', [gvn], '%s = sum_ n e. ( -u k ... k ) ( F ` ( b + ( n x. M ) ) )' % SYMb)
    s2 = w.s([w.s([gsub], 'cbvsumv', '%s = sum_ n e. ( -u k ... k ) ( F ` ( b + ( n x. M ) ) )' % INm)], 'a1i', '( %s -> %s = sum_ n e. ( -u k ... k ) ( F ` ( b + ( n x. M ) ) ) )' % (AKb, INm))
    inb = D(w, AKb, 'eqtr4d', [s2, s1], '%s = %s' % (INm, SYMb))
    vs = chain(w, AK, [V, 'sum_ n e. %s ( F ` n )' % WIN0, 'sum_ b e. ( 0 ..^ M ) sum_ m e. %s ( F ` ( b + ( m x. M ) ) )' % RNG0, 'sum_ b e. ( 0 ..^ M ) %s' % INm, 'sum_ b e. ( 0 ..^ M ) %s' % SYMb],
               [('r', wv), frg, rv, D(w, AK, 'sumeq2dv', [inb], 'sum_ b e. ( 0 ..^ M ) %s = sum_ b e. ( 0 ..^ M ) %s' % (INm, SYMb))])
    # split V at k M
    KM1 = '( %s + 1 )' % KM
    m1z = D(w, AK, 'zsubcld', [mzK, cst(w, AK, '1z', '1 e. ZZ')], '( M - 1 ) e. ZZ')
    topz = D(w, AK, 'zaddcld', [kmz, m1z], '%s e. ZZ' % TOP)
    nkm = D(w, AK, 'znegcld', [kmz], '-u %s e. ZZ' % KM)
    km0 = D(w, AK, 'nn0mulcld', [k0, m0K], '%s e. NN0' % KM)
    km0r = D(w, AK, 'nn0ge0d', [km0], '0 <_ %s' % KM)
    mge = D(w, AK, 'nnge1d', [mnK], '1 <_ M')
    ua = D(w, AK, 'mpbir3and', [nkm, D(w, AK, 'peano2zd', [kmz], '%s e. ZZ' % KM1), linarith(w, AK, [km0r], '-u %s <_ %s' % (KM, KM1), leaves={KM: kmr}, atoms=[KM]),
                                cst(w, AK, 'eluz2', '( %s e. ( ZZ>= ` -u %s ) <-> ( -u %s e. ZZ /\\ %s e. ZZ /\\ -u %s <_ %s ) )' % (KM1, KM, KM, KM1, KM, KM1))], '%s e. ( ZZ>= ` -u %s )' % (KM1, KM))
    ub = D(w, AK, 'mpbir3and', [kmz, topz, linarith(w, AK, [mge], '%s <_ %s' % (KM, TOP), leaves={KM: kmr, 'M': mrK}, atoms=[KM]),
                                cst(w, AK, 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (TOP, KM, KM, TOP, KM, TOP))], '%s e. ( ZZ>= ` %s )' % (TOP, KM))
    SF = '( -u %s ... %s )' % (KM, KM); SE = '( %s ... %s )' % (KM1, TOP)
    wsp = D(w, AK, 'syl2anc', [ua, ub, w.inst('fzsplit2')], '%s = ( %s u. %s )' % (WIN, SF, SE))
    dis = D(w, AK, 'syl', [D(w, AK, 'ltp1d', [kmr], '%s < %s' % (KM, KM1)), w.inst('fzdisj')], '( %s i^i %s ) = (/)' % (SF, SE))
    AKn = '( %s /\\ n e. %s )' % (AK, WIN)
    fnc = D(w, AKn, 'ffvelcdmd', [ad(w, AKn, ffK, 'F : ZZ --> CC'), w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (AKn, WIN)), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % AKn)], '( F ` n ) e. CC')
    SYMF = L.SYM('F', KM); EE = 'sum_ n e. %s ( F ` n )' % SE
    vsp = D(w, AK, 'fsumsplit', [dis, wsp, D(w, AK, 'fzfid', [], '%s e. Fin' % WIN), fnc], '%s = ( %s + %s )' % (V, SYMF, EE))
    # the bound on E
    HK = '( %s ^ k )' % H2
    hkr = D(w, AK, 'reexpcld', [cst(w, AK, 'halfre', '%s e. RR' % H2), k0], '%s e. RR' % HK)
    hk0 = D(w, AK, 'expge0d', [cst(w, AK, 'halfre', '%s e. RR' % H2), k0, cst(w, AK, 'halfge0', '0 <_ %s' % H2)], '0 <_ %s' % HK)
    h01 = D(w, AK, 'jca', [cst(w, AK, 'halfge0', '0 <_ %s' % H2), D(w, AK, 'ltled', [cst(w, AK, 'halfre', '%s e. RR' % H2), cst(w, AK, '1re', '1 e. RR'), cst(w, AK, 'halflt1', '%s < 1' % H2)], '%s <_ 1' % H2)],
            '( 0 <_ %s /\\ %s <_ 1 )' % (H2, H2))
    AKe = '( %s /\\ n e. %s )' % (AK, SE)
    ne_ = w.s([], 'simpr', '( %s -> n e. %s )' % (AKe, SE))
    nz2 = w.s([ne_, w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % AKe)
    nr2 = D(w, AKe, 'zred', [nz2], 'n e. RR')
    nlo = w.s([ne_, w.inst('elfzle1')], 'syl', '( %s -> %s <_ n )' % (AKe, KM1))
    kKM = nlinarith(w, AK, [mge, D(w, AK, 'nngt0d', [kn], '0 < k')], 'k <_ %s' % KM, closure=cl)
    kn_ = linarith(w, AKe, [nlo, ad(w, AKe, kKM, 'k <_ %s' % KM)], 'k <_ n', leaves={'k': ad(w, AKe, kr, 'k e. RR'), 'n': nr2, KM: ad(w, AKe, kmr, '%s e. RR' % KM)}, atoms=[KM])
    n0 = linarith(w, AKe, [kn_, D(w, AKe, 'nngt0d', [ad(w, AKe, kn, 'k e. NN')], '0 < k')], '0 <_ n', leaves={'k': ad(w, AKe, kr, 'k e. RR'), 'n': nr2})
    an = D(w, AKe, 'absidd', [nr2, n0], '( abs ` n ) = n')
    fbn = D(w, AKe, 'breqtrd', [fboundv(w, AKe, ad(w, AKe, bndK, BI), 'n', nz2, 'i'), D(w, AKe, 'oveq2d', [D(w, AKe, 'oveq2d', [an], '( %s ^ ( abs ` n ) ) = ( %s ^ n )' % (H2, H2))], '( C x. ( %s ^ ( abs ` n ) ) ) = ( C x. ( %s ^ n ) )' % (H2, H2))],
            '( abs ` ( F ` n ) ) <_ ( C x. ( %s ^ n ) )' % H2)
    nuk = D(w, AKe, 'mpbir3and', [ad(w, AKe, kz, 'k e. ZZ'), nz2, kn_, cst(w, AKe, 'eluz2', '( n e. ( ZZ>= ` k ) <-> ( k e. ZZ /\\ n e. ZZ /\\ k <_ n ) )')], 'n e. ( ZZ>= ` k )')
    hn = D(w, AKe, 'syl2anc', [D(w, AKe, '3jca', [cst(w, AKe, 'halfre', '%s e. RR' % H2), ad(w, AKe, k0, 'k e. NN0'), nuk], '( %s e. RR /\\ k e. NN0 /\\ n e. ( ZZ>= ` k ) )' % H2), ad(w, AKe, h01, '( 0 <_ %s /\\ %s <_ 1 )' % (H2, H2)), w.inst('leexp2r')],
           '( %s ^ n ) <_ %s' % (H2, HK))
    CH = '( C x. %s )' % HK
    fbk = D(w, AKe, 'letrd', [D(w, AKe, 'abscld', [D(w, AKe, 'ffvelcdmd', [ad(w, AKe, ffK, 'F : ZZ --> CC'), nz2], '( F ` n ) e. CC')], '( abs ` ( F ` n ) ) e. RR'),
                              D(w, AKe, 'remulcld', [ad(w, AKe, crK, 'C e. RR'), D(w, AKe, 'reexpcld', [cst(w, AKe, 'halfre', '%s e. RR' % H2), D(w, AKe, 'nn0red' if False else 'zred', [], '') if False else
                                                                                                        D(w, AKe, 'nn0ge0' if False else 'elnn0z' if False else 'mpbir2and', [nz2, n0, cst(w, AKe, 'elnn0z', '( n e. NN0 <-> ( n e. ZZ /\\ 0 <_ n ) )')], 'n e. NN0')],
                                                                                        '( %s ^ n ) e. RR' % H2)], '( C x. ( %s ^ n ) ) e. RR' % H2),
                              D(w, AKe, 'remulcld', [ad(w, AKe, crK, 'C e. RR'), ad(w, AKe, hkr, '%s e. RR' % HK)], '%s e. RR' % CH), fbn,
                              D(w, AKe, 'lemul2ad', [D(w, AKe, 'reexpcld', [cst(w, AKe, 'halfre', '%s e. RR' % H2), D(w, AKe, 'mpbir2and', [nz2, n0, cst(w, AKe, 'elnn0z', '( n e. NN0 <-> ( n e. ZZ /\\ 0 <_ n ) )')], 'n e. NN0')], '( %s ^ n ) e. RR' % H2),
                                                     ad(w, AKe, hkr, '%s e. RR' % HK), ad(w, AKe, crK, 'C e. RR'), ad(w, AKe, c0K, '0 <_ C'), hn], '( C x. ( %s ^ n ) ) <_ %s' % (H2, CH))],
              '( abs ` ( F ` n ) ) <_ %s' % CH)
    efin = D(w, AK, 'fzfid', [], '%s e. Fin' % SE)
    fnce = D(w, AKe, 'ffvelcdmd', [ad(w, AKe, ffK, 'F : ZZ --> CC'), nz2], '( F ` n ) e. CC')
    chr_ = D(w, AK, 'remulcld', [crK, hkr], '%s e. RR' % CH)
    eb1 = D(w, AK, 'fsumabs', [efin, fnce], '( abs ` %s ) <_ sum_ n e. %s ( abs ` ( F ` n ) )' % (EE, SE))
    eb2 = D(w, AK, 'fsumle', [efin, D(w, AKe, 'abscld', [fnce], '( abs ` ( F ` n ) ) e. RR'), ad(w, AKe, chr_, '%s e. RR' % CH), fbk], 'sum_ n e. %s ( abs ` ( F ` n ) ) <_ sum_ n e. %s %s' % (SE, SE, CH))
    hz = D(w, AK, 'syl', [ub, w.inst('hashfzp1')], '( # ` %s ) = ( %s - %s )' % (SE, TOP, KM))
    eb3 = D(w, AK, 'eqtrd', [D(w, AK, 'syl2anc' if False else 'sylancl' if False else 'syl2anc', [efin, D(w, AK, 'recnd', [chr_], '%s e. CC' % CH), w.inst('fsumconst')], 'sum_ n e. %s %s = ( ( # ` %s ) x. %s )' % (SE, CH, SE, CH)),
                             D(w, AK, 'oveq1d', [hz], '( ( # ` %s ) x. %s ) = ( ( %s - %s ) x. %s )' % (SE, CH, TOP, KM, CH))], 'sum_ n e. %s %s = ( ( %s - %s ) x. %s )' % (SE, CH, TOP, KM, CH))
    # the tail of F at k M
    pztK = u(D(w, A, 'simprd', [pzt], 'A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. C ) x. ( %s ^ j ) )' % (PZF_, L.SYM('F', 'j'), H2)), 'A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. C ) x. ( %s ^ j ) )' % (PZF_, L.SYM('F', 'j'), H2))
    def jsub(G, X, C2):
        return w.s([w.s([w.s([w.s([w.s([w.s([], 'negeq', '( j = %s -> -u j = -u %s )' % (X, X)), w.s([], 'id', '( j = %s -> j = %s )' % (X, X))], 'oveq12d', '( j = %s -> ( -u j ... j ) = ( -u %s ... %s ) )' % (X, X, X))],
                                    'sumeq1d', '( j = %s -> %s = %s )' % (X, L.SYM(G, 'j'), L.SYM(G, X)))], 'oveq2d', '( j = %s -> ( %s - %s ) = ( %s - %s ) )' % (X, L.PZF(G), L.SYM(G, 'j'), L.PZF(G), L.SYM(G, X)))],
                         'fveq2d', '( j = %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (X, L.PZF(G), L.SYM(G, 'j'), L.PZF(G), L.SYM(G, X))),
                     w.s([w.s([], 'oveq2', '( j = %s -> ( %s ^ j ) = ( %s ^ %s ) )' % (X, H2, H2, X))], 'oveq2d', '( j = %s -> ( ( 2 x. %s ) x. ( %s ^ j ) ) = ( ( 2 x. %s ) x. ( %s ^ %s ) ) )' % (X, C2, H2, C2, H2, X))],
                    'breq12d', '( j = %s -> ( ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) x. ( %s ^ j ) ) <-> ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) x. ( %s ^ %s ) ) ) )'
                    % (X, L.PZF(G), L.SYM(G, 'j'), C2, H2, L.PZF(G), L.SYM(G, X), C2, H2, X))
    tF = D(w, AK, 'rspcdva', [jsub('F', KM, 'C'), pztK, km0], '( abs ` ( %s - %s ) ) <_ ( ( 2 x. C ) x. ( %s ^ %s ) )' % (PZF_, SYMF, H2, KM))
    kmu = D(w, AK, 'mpbir3and', [kz, kmz, kKM, cst(w, AK, 'eluz2', '( %s e. ( ZZ>= ` k ) <-> ( k e. ZZ /\\ %s e. ZZ /\\ k <_ %s ) )' % (KM, KM, KM))], '%s e. ( ZZ>= ` k )' % KM)
    hkm = D(w, AK, 'syl2anc', [D(w, AK, '3jca', [cst(w, AK, 'halfre', '%s e. RR' % H2), k0, kmu], '( %s e. RR /\\ k e. NN0 /\\ %s e. ( ZZ>= ` k ) )' % (H2, KM)), h01, w.inst('leexp2r')], '( %s ^ %s ) <_ %s' % (H2, KM, HK))
    C2 = '( 2 x. C )'
    c2r = D(w, AK, 'remulcld', [cst(w, AK, '2re', '2 e. RR'), crK], '%s e. RR' % C2)
    tF2 = D(w, AK, 'letrd', [D(w, AK, 'abscld', [D(w, AK, 'subcld', [u(pzfc, '%s e. CC' % PZF_), D(w, AK, 'fsumcl', [D(w, AK, 'fzfid', [], '%s e. Fin' % SF), D(w, '( %s /\\ n e. %s )' % (AK, SF), 'ffvelcdmd', [ad(w, '( %s /\\ n e. %s )' % (AK, SF), ffK, 'F : ZZ --> CC'), w.s([w.s([], 'simpr', '( ( %s /\\ n e. %s ) -> n e. %s )' % (AK, SF, SF)), w.inst('elfzelz')], 'syl', '( ( %s /\\ n e. %s ) -> n e. ZZ )' % (AK, SF))], '( F ` n ) e. CC')], '%s e. CC' % SYMF)],
                                                            '( %s - %s ) e. CC' % (PZF_, SYMF))], '( abs ` ( %s - %s ) ) e. RR' % (PZF_, SYMF)),
                             D(w, AK, 'remulcld', [c2r, D(w, AK, 'reexpcld', [cst(w, AK, 'halfre', '%s e. RR' % H2), km0], '( %s ^ %s ) e. RR' % (H2, KM))], '( %s x. ( %s ^ %s ) ) e. RR' % (C2, H2, KM)),
                             D(w, AK, 'remulcld', [c2r, hkr], '( %s x. %s ) e. RR' % (C2, HK)), tF,
                             D(w, AK, 'lemul2ad', [D(w, AK, 'reexpcld', [cst(w, AK, 'halfre', '%s e. RR' % H2), km0], '( %s ^ %s ) e. RR' % (H2, KM)), hkr, c2r,
                                                   D(w, AK, 'mulge0d', [cst(w, AK, '2re', '2 e. RR'), crK, cst(w, AK, '0le2', '0 <_ 2'), c0K], '0 <_ %s' % C2), hkm], '( %s x. ( %s ^ %s ) ) <_ ( %s x. %s )' % (C2, H2, KM, C2, HK))],
              '( abs ` ( %s - %s ) ) <_ ( %s x. %s )' % (PZF_, SYMF, C2, HK))
    # the residue tails at K
    pztbK = D(w, AKb, 'simprd', [D(w, AKb, 'syl', [D(w, AKb, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (AKb, A)), bo], Ab), w.s([pztb], 'idi' if False else 'ex' if False else 'idi', '') if False else None], '') if False else
                                 w.s([D(w, AKb, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (AKb, A)), bo], Ab), pztb], 'syl', '( %s -> ( seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) + ( %s ` -u n ) ) ) ) e. dom ~~> /\\ A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) x. ( %s ^ j ) ) ) )'
                                     % (AKb, GBb, GBb, PZg, L.SYM(GBb, 'j'), CB, H2))],
                  'A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) x. ( %s ^ j ) )' % (PZg, L.SYM(GBb, 'j'), CB, H2))
    tb = D(w, AKb, 'rspcdva', [jsub(GBb, 'k', CB), pztbK, ad(w, AKb, k0, 'k e. NN0')], '( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) x. %s )' % (PZg, SYMb, CB, HK))
    toAb = lambda st, f: w.s([D(w, AKb, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (AKb, A)), bo], Ab), st], 'syl', '( %s -> %s )' % (AKb, f))
    pzgK = toAb(pzgc, '%s e. CC' % PZg)
    gbfK = toAb(gbf, '%s : ZZ --> CC' % GBb)
    AKbn2 = '( %s /\\ n e. ( -u k ... k ) )' % AKb
    symc = D(w, AKb, 'fsumcl', [D(w, AKb, 'fzfid', [], '( -u k ... k ) e. Fin'), D(w, AKbn2, 'ffvelcdmd', [ad(w, AKbn2, gbfK, '%s : ZZ --> CC' % GBb), w.s([w.s([], 'simpr', '( %s -> n e. ( -u k ... k ) )' % AKbn2), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % AKbn2)],
                                                                                        '( %s ` n ) e. CC' % GBb)], '%s e. CC' % SYMb)
    DF = '( %s - %s )' % (PZg, SYMb)
    dfc = D(w, AKb, 'subcld', [pzgK, symc], '%s e. CC' % DF)
    CBH = '( ( 2 x. %s ) x. %s )' % (CB, HK)
    cbr = D(w, AK, 'remulcld', [crK, D(w, AK, 'reexpcld', [cst(w, AK, '2re', '2 e. RR'), m0K], '( 2 ^ M ) e. RR')], '%s e. RR' % CB)
    cbhr = D(w, AK, 'remulcld', [D(w, AK, 'remulcld', [cst(w, AK, '2re', '2 e. RR'), cbr], '( 2 x. %s ) e. RR' % CB), hkr], '%s e. RR' % CBH)
    ofi = cst(w, AK, 'fzofi', '( 0 ..^ M ) e. Fin')
    ssub = D(w, AK, 'fsumsub', [ofi, u(pzgc, '%s e. CC' % PZg) if False else pzgK, symc], 'sum_ b e. ( 0 ..^ M ) %s = ( %s - sum_ b e. ( 0 ..^ M ) %s )' % (DF, LL, SYMb))
    sb1 = D(w, AK, 'fsumabs', [ofi, dfc], '( abs ` sum_ b e. ( 0 ..^ M ) %s ) <_ sum_ b e. ( 0 ..^ M ) ( abs ` %s )' % (DF, DF))
    sb2 = D(w, AK, 'fsumle', [ofi, D(w, AKb, 'abscld', [dfc], '( abs ` %s ) e. RR' % DF), ad(w, AKb, cbhr, '%s e. RR' % CBH), tb], 'sum_ b e. ( 0 ..^ M ) ( abs ` %s ) <_ sum_ b e. ( 0 ..^ M ) %s' % (DF, CBH))
    sb3 = D(w, AK, 'eqtrd', [D(w, AK, 'syl2anc', [ofi, D(w, AK, 'recnd', [cbhr], '%s e. CC' % CBH), w.inst('fsumconst')], 'sum_ b e. ( 0 ..^ M ) %s = ( ( # ` ( 0 ..^ M ) ) x. %s )' % (CBH, CBH)),
                             D(w, AK, 'oveq1d', [D(w, AK, 'syl', [m0K, w.inst('hashfzo0')], '( # ` ( 0 ..^ M ) ) = M')], '( ( # ` ( 0 ..^ M ) ) x. %s ) = ( M x. %s )' % (CBH, CBH))],
              'sum_ b e. ( 0 ..^ M ) %s = ( M x. %s )' % (CBH, CBH))
    SUMS = 'sum_ b e. ( 0 ..^ M ) %s' % SYMb
    # combine
    LV = '( abs ` ( %s - %s ) )' % (LL, V)
    lve = D(w, AK, 'fveq2d', [D(w, AK, 'eqtr4d', [D(w, AK, 'oveq2d', [vs], '( %s - %s ) = ( %s - %s )' % (LL, V, LL, SUMS)), ssub], '( %s - %s ) = sum_ b e. ( 0 ..^ M ) %s' % (LL, V, DF))],
            '%s = ( abs ` sum_ b e. ( 0 ..^ M ) %s )' % (LV, DF))
    lvb = D(w, AK, 'eqbrtrd', [lve, D(w, AK, 'letrd', [D(w, AK, 'abscld', [D(w, AK, 'fsumcl', [ofi, dfc], 'sum_ b e. ( 0 ..^ M ) %s e. CC' % DF)], '( abs ` sum_ b e. ( 0 ..^ M ) %s ) e. RR' % DF),
                                                      D(w, AK, 'fsumrecl' if False else 'fsumrecl', [ofi, D(w, AKb, 'abscld', [dfc], '( abs ` %s ) e. RR' % DF)], 'sum_ b e. ( 0 ..^ M ) ( abs ` %s ) e. RR' % DF),
                                                      D(w, AK, 'fsumrecl', [ofi, ad(w, AKb, cbhr, '%s e. RR' % CBH)], 'sum_ b e. ( 0 ..^ M ) %s e. RR' % CBH), sb1, sb2],
                                        '( abs ` sum_ b e. ( 0 ..^ M ) %s ) <_ sum_ b e. ( 0 ..^ M ) %s' % (DF, CBH))], '%s <_ sum_ b e. ( 0 ..^ M ) %s' % (LV, CBH))
    lvb2 = D(w, AK, 'breqtrd', [lvb, sb3], '%s <_ ( M x. %s )' % (LV, CBH))
    vc = D(w, AK, 'fsumcl', [D(w, AK, 'fzfid', [], '%s e. Fin' % WIN), fnc], '%s e. CC' % V)
    symfc = D(w, AK, 'fsumcl', [D(w, AK, 'fzfid', [], '%s e. Fin' % SF), D(w, '( %s /\\ n e. %s )' % (AK, SF), 'ffvelcdmd', [ad(w, '( %s /\\ n e. %s )' % (AK, SF), ffK, 'F : ZZ --> CC'), w.s([w.s([], 'simpr', '( ( %s /\\ n e. %s ) -> n e. %s )' % (AK, SF, SF)), w.inst('elfzelz')], 'syl', '( ( %s /\\ n e. %s ) -> n e. ZZ )' % (AK, SF))], '( F ` n ) e. CC')], '%s e. CC' % SYMF)
    eec = D(w, AK, 'fsumcl', [efin, fnce], '%s e. CC' % EE)
    pzfK = u(pzfc, '%s e. CC' % PZF_); llK = u(llc, '%s e. CC' % LL)
    t1 = D(w, AK, 'abs3difd', [pzfK, llK, vc], '( abs ` ( %s - %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - %s ) ) )' % (PZF_, LL, PZF_, V, V, LL))
    pv = D(w, AK, 'eqtr4d', [D(w, AK, 'oveq2d', [vsp], '( %s - %s ) = ( %s - ( %s + %s ) )' % (PZF_, V, PZF_, SYMF, EE)), D(w, AK, 'subsub4d', [pzfK, symfc, eec], '( ( %s - %s ) - %s ) = ( %s - ( %s + %s ) )' % (PZF_, SYMF, EE, PZF_, SYMF, EE))],
            '( %s - %s ) = ( ( %s - %s ) - %s )' % (PZF_, V, PZF_, SYMF, EE))
    t2 = D(w, AK, 'eqbrtrd', [D(w, AK, 'fveq2d', [pv], '( abs ` ( %s - %s ) ) = ( abs ` ( ( %s - %s ) - %s ) )' % (PZF_, V, PZF_, SYMF, EE)),
                              D(w, AK, 'abs2dif2d', [D(w, AK, 'subcld', [pzfK, symfc], '( %s - %s ) e. CC' % (PZF_, SYMF)), eec], '( abs ` ( ( %s - %s ) - %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` %s ) )' % (PZF_, SYMF, EE, PZF_, SYMF, EE))],
              '( abs ` ( %s - %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` %s ) )' % (PZF_, V, PZF_, SYMF, EE))
    t3 = D(w, AK, 'abssubd', [vc, llK], '( abs ` ( %s - %s ) ) = %s' % (V, LL, LV))
    eb = D(w, AK, 'letrd', [D(w, AK, 'abscld', [eec], '( abs ` %s ) e. RR' % EE), D(w, AK, 'fsumrecl', [efin, D(w, AKe, 'abscld', [fnce], '( abs ` ( F ` n ) ) e. RR')], 'sum_ n e. %s ( abs ` ( F ` n ) ) e. RR' % SE),
                            D(w, AK, 'fsumrecl', [efin, ad(w, AKe, chr_, '%s e. RR' % CH)], 'sum_ n e. %s %s e. RR' % (SE, CH)), eb1, eb2], '( abs ` %s ) <_ sum_ n e. %s %s' % (EE, SE, CH))
    eb4 = D(w, AK, 'breqtrd', [eb, eb3], '( abs ` %s ) <_ ( ( %s - %s ) x. %s )' % (EE, TOP, KM, CH))
    tk = lineq(w, AK, '( %s - %s )' % (TOP, KM), '( M - 1 )', closure=cl, products=True)
    eb5 = D(w, AK, 'breqtrd', [eb4, D(w, AK, 'oveq1d', [tk], '( ( %s - %s ) x. %s ) = ( ( M - 1 ) x. %s )' % (TOP, KM, CH, CH))], '( abs ` %s ) <_ ( ( M - 1 ) x. %s )' % (EE, CH))
    DD = '( ( ( 2 x. C ) + ( M x. C ) ) + ( M x. ( 2 x. %s ) ) )' % CB
    AT = lambda x: '( abs ` %s )' % x
    atoms = [AT('( %s - %s )' % (PZF_, LL)), AT('( %s - %s )' % (PZF_, V)), AT('( %s - %s )' % (V, LL)), LV, AT('( %s - %s )' % (PZF_, SYMF)), AT(EE), HK, '( 2 ^ M )']
    lv_ = {}
    for x, s_ in [(AT('( %s - %s )' % (PZF_, LL)), D(w, AK, 'abscld', [D(w, AK, 'subcld', [pzfK, llK], '( %s - %s ) e. CC' % (PZF_, LL))], '%s e. RR' % AT('( %s - %s )' % (PZF_, LL)))),
                  (AT('( %s - %s )' % (PZF_, V)), D(w, AK, 'abscld', [D(w, AK, 'subcld', [pzfK, vc], '( %s - %s ) e. CC' % (PZF_, V))], '%s e. RR' % AT('( %s - %s )' % (PZF_, V)))),
                  (AT('( %s - %s )' % (V, LL)), D(w, AK, 'abscld', [D(w, AK, 'subcld', [vc, llK], '( %s - %s ) e. CC' % (V, LL))], '%s e. RR' % AT('( %s - %s )' % (V, LL)))),
                  (LV, D(w, AK, 'abscld', [D(w, AK, 'subcld', [llK, vc], '( %s - %s ) e. CC' % (LL, V))], '%s e. RR' % LV)),
                  (AT('( %s - %s )' % (PZF_, SYMF)), D(w, AK, 'abscld', [D(w, AK, 'subcld', [pzfK, symfc], '( %s - %s ) e. CC' % (PZF_, SYMF))], '%s e. RR' % AT('( %s - %s )' % (PZF_, SYMF)))),
                  (AT(EE), D(w, AK, 'abscld', [eec], '%s e. RR' % AT(EE))), (HK, hkr), ('( 2 ^ M )', D(w, AK, 'reexpcld', [cst(w, AK, '2re', '2 e. RR'), m0K], '( 2 ^ M ) e. RR'))]:
        cl.leaf(x, 'RR', s_)
    ch0 = D(w, AK, 'mulge0d', [crK, hkr, c0K, hk0], '0 <_ %s' % CH)
    fin = nlinarith(w, AK, [t1, t2, t3, tF2, eb5, lvb2, ch0], '%s <_ ( %s x. %s )' % (AT('( %s - %s )' % (PZF_, LL)), DD, HK), closure=cl)
    SS = '( NN X. { %s } )' % PZF_
    fv = D(w, AK, 'syl2anc', [pzfK, kn, w.inst('fvconst2g')], '( %s ` k ) = %s' % (SS, PZF_))
    b1 = D(w, AK, 'eqbrtrd', [D(w, AK, 'fveq2d', [D(w, AK, 'oveq1d', [fv], '( ( %s ` k ) - %s ) = ( %s - %s )' % (SS, LL, PZF_, LL))], '( abs ` ( ( %s ` k ) - %s ) ) = %s' % (SS, LL, AT('( %s - %s )' % (PZF_, LL)))), fin],
             '( abs ` ( ( %s ` k ) - %s ) ) <_ ( %s x. %s )' % (SS, LL, DD, HK))
    pk = D(w, AK, 'jca', [D(w, AK, 'eqeltrd', [fv, pzfK], '( %s ` k ) e. CC' % SS), b1], '( ( %s ` k ) e. CC /\\ ( abs ` ( ( %s ` k ) - %s ) ) <_ ( %s x. %s ) )' % (SS, SS, LL, DD, HK))
    ALLK = 'A. k e. NN ( ( %s ` k ) e. CC /\\ ( abs ` ( ( %s ` k ) - %s ) ) <_ ( %s x. ( %s ^ k ) ) )' % (SS, SS, LL, DD, H2)
    ral = D(w, A, 'ralrimiva', [pk], ALLK)
    ddr = D(w, A, 'readdcld', [D(w, A, 'readdcld', [D(w, A, 'remulcld', [cst(w, A, '2re', '2 e. RR'), cr], '( 2 x. C ) e. RR'), D(w, A, 'remulcld', [mr, cr], '( M x. C ) e. RR')], '( ( 2 x. C ) + ( M x. C ) ) e. RR'),
                               D(w, A, 'remulcld', [mr, D(w, A, 'remulcld', [cst(w, A, '2re', '2 e. RR'), D(w, A, 'remulcld', [cr, D(w, A, 'reexpcld', [cst(w, A, '2re', '2 e. RR'), m0], '( 2 ^ M ) e. RR')], '%s e. RR' % CB)], '( 2 x. %s ) e. RR' % CB)],
                                 '( M x. ( 2 x. %s ) ) e. RR' % CB)], '%s e. RR' % DD)
    sex = w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.s([], 'snex', '{ %s } e. _V' % PZF_)], 'xpex', '%s e. _V' % SS)], 'a1i', '( %s -> %s e. _V )' % (A, SS))
    sq = D(w, A, 'syl3anc', [D(w, A, 'jca', [llc, ddr], '( %s e. CC /\\ %s e. RR )' % (LL, DD)),
                             D(w, A, 'jca', [cst(w, A, 'halfre', '%s e. RR' % H2), D(w, A, 'jca', [cst(w, A, 'halfge0', '0 <_ %s' % H2), cst(w, A, 'halflt1', '%s < 1' % H2)], '( 0 <_ %s /\\ %s < 1 )' % (H2, H2))],
                               '( %s e. RR /\\ ( 0 <_ %s /\\ %s < 1 ) )' % (H2, H2, H2)),
                             D(w, A, 'jca', [sex, ral], '( %s e. _V /\\ %s )' % (SS, ALLK)), w.inst('zl3sqz')], '%s ~~> %s' % (SS, LL))
    cc_ = D(w, A, 'syl2anc', [pzfc, cst(w, A, '1z', '1 e. ZZ'), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqimss2i', '( ZZ>= ` 1 ) C_ NN'), w.s([], 'nnex', 'NN e. _V')], 'climconst2',
                                                                      '( ( %s e. CC /\\ 1 e. ZZ ) -> %s ~~> %s )' % (PZF_, SS, PZF_))], '%s ~~> %s' % (SS, PZF_))
    w.qed([cc_, sq, w.inst('climuni')], 'syl2anc', S['zl3rg'])
    go(w)


def sumP_cl(w, A, G, gf, cvg):
    """( A -> sum_ n e. NN pair e. CC ), as pz_cl"""
    PR = lambda v: '( ( %s ` %s ) + ( %s ` -u %s ) )' % (G, v, G, v)
    PMn, PMm = '( n e. NN |-> %s )' % PR('n'), '( q e. NN |-> %s )' % PR('q')
    sub = lambda a, b: w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (a, b, G, a, G, b)),
                            w.s([w.s([], 'negeq', '( %s = %s -> -u %s = -u %s )' % (a, b, a, b))], 'fveq2d', '( %s = %s -> ( %s ` -u %s ) = ( %s ` -u %s ) )' % (a, b, G, a, G, b))],
                           'oveq12d', '( %s = %s -> %s = %s )' % (a, b, PR(a), PR(b)))
    pmeq = w.s([sub('q', 'n')], 'cbvmptv', '%s = %s' % (PMm, PMn))
    cvm = D(w, A, 'mpbird', [cvg, w.s([w.s([w.s([pmeq, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (PMm, PMn))], 'eleq1i',
                                          '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (PMm, PMn))], 'a1i', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A, PMm, PMn))],
            'seq 1 ( + , %s ) e. dom ~~>' % PMm)
    An = '( %s /\\ n e. NN )' % A
    nz = D(w, An, 'nnzd', [w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'n e. ZZ')
    pv = D(w, An, 'syl', [w.s([], 'simpr', '( %s -> n e. NN )' % An), w.s([sub('q', 'n'), w.s([], 'eqid', '%s = %s' % (PMm, PMm)), w.s([], 'ovex', '%s e. _V' % PR('n'))], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (PMm, PR('n')))],
           '( %s ` n ) = %s' % (PMm, PR('n')))
    pc = D(w, An, 'addcld', [D(w, An, 'ffvelcdmd', [ad(w, An, gf, '%s : ZZ --> CC' % G), nz], '( %s ` n ) e. CC' % G), D(w, An, 'ffvelcdmd', [ad(w, An, gf, '%s : ZZ --> CC' % G), D(w, An, 'znegcld', [nz], '-u n e. ZZ')], '( %s ` -u n ) e. CC' % G)],
           '%s e. CC' % PR('n'))
    return D(w, A, 'isumcl', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), pv, pc, cvm], 'sum_ n e. NN %s e. CC' % PR('n'))


# ---------------------------------------------------------------- zl3pzf
def pairmap(G, v):
    return '( %s e. NN |-> ( ( %s ` %s ) + ( %s ` -u %s ) ) )' % (v, G, v, G, v)


def pairsub_(w, G, a, b):
    PR = lambda v: '( ( %s ` %s ) + ( %s ` -u %s ) )' % (G, v, G, v)
    return w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (a, b, G, a, G, b)),
                w.s([w.s([], 'negeq', '( %s = %s -> -u %s = -u %s )' % (a, b, a, b))], 'fveq2d', '( %s = %s -> ( %s ` -u %s ) = ( %s ` -u %s ) )' % (a, b, G, a, G, b))],
               'oveq12d', '( %s = %s -> %s = %s )' % (a, b, PR(a), PR(b)))


def seqcv_rename(w, A, G, cvg, v1, v2):
    """( A -> seq 1 ( + , pairmap(G,v2) ) e. dom ~~> ) from the v1 form"""
    eq = w.s([pairsub_(w, G, v1, v2)], 'cbvmptv', '%s = %s' % (pairmap(G, v1), pairmap(G, v2)))
    bi = w.s([w.s([eq, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (pairmap(G, v1), pairmap(G, v2)))], 'eleq1i',
             '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (pairmap(G, v1), pairmap(G, v2)))
    return D(w, A, 'mpbid', [cvg, w.s([bi], 'a1i', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A, pairmap(G, v1), pairmap(G, v2)))],
             'seq 1 ( + , %s ) e. dom ~~>' % pairmap(G, v2))


if want('zl3pzf'):
    w = W('zl3pzf', 'A finite sum of convergent sums over ` ZZ ` is the sum over ` ZZ ` of the finite sums ( ~ bvswap ).')
    A, Cc = ante_of('zl3pzf')
    HB_ = lambda b, v: '( ( H ` %s ) : ZZ --> CC /\\ seq 1 ( + , %s ) e. dom ~~> )' % (b, pairmap('( H ` %s )' % b, v))
    # ( b = c -> ( HB_(b,n) <-> HB_(c,q) ) )
    fb = w.s([], 'fveq2', '( b = c -> ( H ` b ) = ( H ` c ) )')
    mp1 = w.s([w.s([w.s([fb], 'fveq1d', '( b = c -> ( ( H ` b ) ` n ) = ( ( H ` c ) ` n ) )'), w.s([fb], 'fveq1d', '( b = c -> ( ( H ` b ) ` -u n ) = ( ( H ` c ) ` -u n ) )')], 'oveq12d',
                    '( b = c -> ( ( ( H ` b ) ` n ) + ( ( H ` b ) ` -u n ) ) = ( ( ( H ` c ) ` n ) + ( ( H ` c ) ` -u n ) ) )')], 'mpteq2dv',
              '( b = c -> %s = %s )' % (pairmap('( H ` b )', 'n'), pairmap('( H ` c )', 'n')))
    mp2 = w.s([mp1, w.s([pairsub_(w, '( H ` c )', 'n', 'q')], 'cbvmptv', '%s = %s' % (pairmap('( H ` c )', 'n'), pairmap('( H ` c )', 'q')))], 'eqtrdi',
              '( b = c -> %s = %s )' % (pairmap('( H ` b )', 'n'), pairmap('( H ` c )', 'q')))
    csub = w.s([w.s([fb], 'feq1d', '( b = c -> ( ( H ` b ) : ZZ --> CC <-> ( H ` c ) : ZZ --> CC ) )'),
                w.s([w.s([mp2], 'seqeq3d', '( b = c -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (pairmap('( H ` b )', 'n'), pairmap('( H ` c )', 'q')))], 'eleq1d',
                    '( b = c -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (pairmap('( H ` b )', 'n'), pairmap('( H ` c )', 'q')))],
               'anbi12d', '( b = c -> ( %s <-> %s ) )' % (HB_('b', 'n'), HB_('c', 'q')))
    cb = w.s([csub], 'cbvralvw', '( A. b e. A %s <-> A. c e. A %s )' % (HB_('b', 'n'), HB_('c', 'q')))
    A0 = '( A e. Fin /\\ A. c e. A %s )' % HB_('c', 'q')
    fin = D(w, A0, 'simpl', [], 'A e. Fin'); al = D(w, A0, 'simpr', [], 'A. c e. A %s' % HB_('c', 'q'))
    Ab = '( %s /\\ b e. A )' % A0
    fc = w.s([], 'fveq2', '( c = b -> ( H ` c ) = ( H ` b ) )')
    mq = w.s([w.s([w.s([fc], 'fveq1d', '( c = b -> ( ( H ` c ) ` q ) = ( ( H ` b ) ` q ) )'), w.s([fc], 'fveq1d', '( c = b -> ( ( H ` c ) ` -u q ) = ( ( H ` b ) ` -u q ) )')], 'oveq12d',
                   '( c = b -> ( ( ( H ` c ) ` q ) + ( ( H ` c ) ` -u q ) ) = ( ( ( H ` b ) ` q ) + ( ( H ` b ) ` -u q ) ) )')], 'mpteq2dv',
             '( c = b -> %s = %s )' % (pairmap('( H ` c )', 'q'), pairmap('( H ` b )', 'q')))
    bsub = w.s([w.s([fc], 'feq1d', '( c = b -> ( ( H ` c ) : ZZ --> CC <-> ( H ` b ) : ZZ --> CC ) )'),
                w.s([w.s([mq], 'seqeq3d', '( c = b -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (pairmap('( H ` c )', 'q'), pairmap('( H ` b )', 'q')))], 'eleq1d',
                    '( c = b -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (pairmap('( H ` c )', 'q'), pairmap('( H ` b )', 'q')))],
               'anbi12d', '( c = b -> ( %s <-> %s ) )' % (HB_('c', 'q'), HB_('b', 'q')))
    hb = D(w, Ab, 'rspcdva', [bsub, ad(w, Ab, al, 'A. c e. A %s' % HB_('c', 'q')), w.s([], 'simpr', '( %s -> b e. A )' % Ab)], HB_('b', 'q'))
    HBb = '( H ` b )'
    hf = D(w, Ab, 'simpld', [hb], '%s : ZZ --> CC' % HBb)
    hcq = D(w, Ab, 'simprd', [hb], 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(HBb, 'q'))
    hcv = seqcv_rename(w, Ab, HBb, hcq, 'q', 'n')
    P = lambda v: '( ( %s ` %s ) + ( %s ` -u %s ) )' % (HBb, v, HBb, v)
    SK = '( k e. ZZ |-> sum_ b e. A ( ( H ` b ) ` k ) )'
    def skv(X, xz, A2):
        sub = w.s([w.s([w.s([], 'fveq2', '( k = %s -> ( ( H ` b ) ` k ) = ( ( H ` b ) ` %s ) )' % (X, X))], 'adantr', '( ( k = %s /\\ b e. A ) -> ( ( H ` b ) ` k ) = ( ( H ` b ) ` %s ) )' % (X, X))], 'sumeq2dv',
                  '( k = %s -> sum_ b e. A ( ( H ` b ) ` k ) = sum_ b e. A ( ( H ` b ) ` %s ) )' % (X, X))
        return D(w, A2, 'syl', [xz, w.s([sub, w.s([], 'eqid', '%s = %s' % (SK, SK)), w.s([], 'sumex', 'sum_ b e. A ( ( H ` b ) ` %s ) e. _V' % X)], 'fvmpt',
                                        '( %s e. ZZ -> ( %s ` %s ) = sum_ b e. A ( ( H ` b ) ` %s ) )' % (X, SK, X, X))], '( %s ` %s ) = sum_ b e. A ( ( H ` b ) ` %s )' % (SK, X, X))
    v0 = skv('0', cst(w, A0, '0z', '0 e. ZZ'), A0)
    An = '( %s /\\ n e. NN )' % A0
    nz = D(w, An, 'nnzd', [w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'n e. ZZ')
    vn = skv('n', nz, An); vmn = skv('-u n', D(w, An, 'znegcld', [nz], '-u n e. ZZ'), An)
    Abn = '( %s /\\ b e. A )' % An
    abn_ab = D(w, Abn, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (Abn, A0)), w.s([], 'simpr', '( %s -> b e. A )' % Abn)], Ab)
    hfn = D(w, Abn, 'syl', [abn_ab, w.s([hf], 'idi', '( %s -> %s : ZZ --> CC )' % (Ab, HBb))], '%s : ZZ --> CC' % HBb)
    nzb = ad(w, Abn, nz, 'n e. ZZ')
    h1 = D(w, Abn, 'ffvelcdmd', [hfn, nzb], '( %s ` n ) e. CC' % HBb); h2 = D(w, Abn, 'ffvelcdmd', [hfn, D(w, Abn, 'znegcld', [nzb], '-u n e. ZZ')], '( %s ` -u n ) e. CC' % HBb)
    pn = D(w, An, 'eqtr4d', [D(w, An, 'oveq12d', [vn, vmn], '( ( %s ` n ) + ( %s ` -u n ) ) = ( sum_ b e. A ( ( H ` b ) ` n ) + sum_ b e. A ( ( H ` b ) ` -u n ) )' % (SK, SK)),
                             D(w, An, 'fsumadd', [ad(w, An, fin, 'A e. Fin'), h1, h2], 'sum_ b e. A %s = ( sum_ b e. A ( ( H ` b ) ` n ) + sum_ b e. A ( ( H ` b ) ` -u n ) )' % P('n'))],
            '( ( %s ` n ) + ( %s ` -u n ) ) = sum_ b e. A %s' % (SK, SK, P('n')))
    s1 = D(w, A0, 'sumeq2dv', [pn], 'sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = sum_ n e. NN sum_ b e. A %s' % (SK, SK, P('n')))
    Abj = '( %s /\\ ( b e. A /\\ n e. NN ) )' % A0
    abj = D(w, Abj, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Abj, A0)), w.s([], 'simprl', '( %s -> b e. A )' % Abj)], Ab)
    hfj = D(w, Abj, 'syl', [abj, w.s([hf], 'idi', '( %s -> %s : ZZ --> CC )' % (Ab, HBb))], '%s : ZZ --> CC' % HBb)
    nzj = D(w, Abj, 'nnzd', [w.s([], 'simprr', '( %s -> n e. NN )' % Abj)], 'n e. ZZ')
    pcj = D(w, Abj, 'addcld', [D(w, Abj, 'ffvelcdmd', [hfj, nzj], '( %s ` n ) e. CC' % HBb), D(w, Abj, 'ffvelcdmd', [hfj, D(w, Abj, 'znegcld', [nzj], '-u n e. ZZ')], '( %s ` -u n ) e. CC' % HBb)], '%s e. CC' % P('n'))
    PT = P('t')
    cvt = seqcv_rename(w, Ab, HBb, hcq, 'q', 't')
    bv = D(w, A0, 'bvswap', [fin, pcj, cvt, pairsub_(w, HBb, 'n', 't')], 'seq 1 ( + , ( t e. NN |-> sum_ b e. A %s ) ) ~~> sum_ b e. A sum_ n e. NN %s' % (PT, P('n')))
    TS = '( t e. NN |-> sum_ b e. A %s )' % PT
    tsub = w.s([w.s([pairsub_(w, HBb, 't', 'n')], 'adantr', '( ( t = n /\\ b e. A ) -> %s = %s )' % (PT, P('n')))], 'sumeq2dv', '( t = n -> sum_ b e. A %s = sum_ b e. A %s )' % (PT, P('n')))
    tsv = D(w, An, 'syl', [w.s([], 'simpr', '( %s -> n e. NN )' % An), w.s([tsub, w.s([], 'eqid', '%s = %s' % (TS, TS)), w.s([], 'sumex', 'sum_ b e. A %s e. _V' % P('n'))], 'fvmpt',
                                                                        '( n e. NN -> ( %s ` n ) = sum_ b e. A %s )' % (TS, P('n')))], '( %s ` n ) = sum_ b e. A %s' % (TS, P('n')))
    tsc = D(w, An, 'fsumcl', [ad(w, An, fin, 'A e. Fin'), D(w, Abn, 'addcld', [h1, h2], '%s e. CC' % P('n'))], 'sum_ b e. A %s e. CC' % P('n'))
    ic = D(w, A0, 'isumclim', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A0, '1z', '1 e. ZZ'), tsv, tsc, bv], 'sum_ n e. NN sum_ b e. A %s = sum_ b e. A sum_ n e. NN %s' % (P('n'), P('n')))
    SPb = 'sum_ n e. NN %s' % P('n')
    spc = sumP_cl(w, Ab, HBb, hf, hcv)
    h0 = D(w, Ab, 'ffvelcdmd', [hf, cst(w, Ab, '0z', '0 e. ZZ')], '( %s ` 0 ) e. CC' % HBb)
    fa = D(w, A0, 'fsumadd', [fin, h0, spc], 'sum_ b e. A ( ( %s ` 0 ) + %s ) = ( sum_ b e. A ( %s ` 0 ) + sum_ b e. A %s )' % (HBb, SPb, HBb, SPb))
    PZS = L.PZF(SK)
    fin_ = chain(w, A0, [PZS, '( sum_ b e. A ( ( H ` b ) ` 0 ) + sum_ n e. NN sum_ b e. A %s )' % P('n'), '( sum_ b e. A ( ( H ` b ) ` 0 ) + sum_ b e. A %s )' % SPb, 'sum_ b e. A %s' % L.PZF(HBb)],
                 [D(w, A0, 'oveq12d', [v0, s1], '%s = ( sum_ b e. A ( ( H ` b ) ` 0 ) + sum_ n e. NN sum_ b e. A %s )' % (PZS, P('n'))),
                  D(w, A0, 'oveq2d', [ic], '( sum_ b e. A ( ( H ` b ) ` 0 ) + sum_ n e. NN sum_ b e. A %s ) = ( sum_ b e. A ( ( H ` b ) ` 0 ) + sum_ b e. A %s )' % (P('n'), SPb)), ('r', fa)])
    w.qed([w.s([w.s([cb], 'anbi2i', '( %s <-> %s )' % (A, A0))], 'biimpi', '( %s -> %s )' % (A, A0)), fin_], 'syl', S['zl3pzf'])
    go(w)


# ---------------------------------------------------------------- the character facts
GD, ZN, DB, LMr, BZ, UZ, IG = '( DChr ` M )', '( Z/nZ ` M )', '( Base ` ( DChr ` M ) )', L.LM, '( Base ` ( Z/nZ ` M ) )', '( Unit ` ( Z/nZ ` M ) )', '( invg ` ( DChr ` M ) )'


def eq_(w, X):
    return w.s([], 'eqid', '%s = %s' % (X, X))


def chval(w, A, Z, zd, X, xz):
    """( A -> ( Z ` ( L ` X ) ) e. CC )"""
    return D(w, A, 'dchrzrhcl', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, LMr), zd, xz], '( %s ` ( %s ` %s ) ) e. CC' % (Z, LMr, X))


def chmul(w, A, Z, zd, X, Y, xz, yz):
    return D(w, A, 'dchrzrhmul', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, LMr), zd, xz, yz],
             '( %s ` ( %s ` ( %s x. %s ) ) ) = ( ( %s ` ( %s ` %s ) ) x. ( %s ` ( %s ` %s ) ) )' % (Z, LMr, X, Y, Z, LMr, X, Z, LMr, Y))


def lm_base(w, A, mn, X, xz):
    """( A -> ( L ` X ) e. B )"""
    ring = D(w, A, 'syl', [D(w, A, 'syl', [D(w, A, 'nnnn0d', [mn], 'M e. NN0'), w.s([eq_(w, ZN)], 'zncrng', '( M e. NN0 -> %s e. CRing )' % ZN)], '%s e. CRing' % ZN), w.inst('crngring')], '%s e. Ring' % ZN)
    rhm = D(w, A, 'syl', [ring, w.s([eq_(w, LMr)], 'zrhrhm', '( %s e. Ring -> %s e. ( ZZring RingHom %s ) )' % (ZN, LMr, ZN))], '%s e. ( ZZring RingHom %s )' % (LMr, ZN))
    lf = D(w, A, 'syl', [rhm, w.s([w.s([], 'zringbas', 'ZZ = ( Base ` ZZring )'), eq_(w, BZ)], 'rhmf', '( %s e. ( ZZring RingHom %s ) -> %s : ZZ --> %s )' % (LMr, ZN, LMr, BZ))], '%s : ZZ --> %s' % (LMr, BZ))
    return D(w, A, 'ffvelcdmd', [lf, xz], '( %s ` %s ) e. %s' % (LMr, X, BZ))


if want('zl3par'):
    w = W('zl3par', 'The parity ` a ` of a Dirichlet character: ` a e. { 0 , 1 } ` , ` Y ( -1 ) = ( -1 ) ^ a ` , and the inverse character has the same parity.')
    A, Cc = ante_of('zl3par')
    mn = D(w, A, 'simpl', [], 'M e. NN'); yd = D(w, A, 'simpr', [], 'Y e. %s' % DB)
    m1 = cst(w, A, 'neg1z', '-u 1 e. ZZ')
    V = '( Y ` ( %s ` -u 1 ) )' % LMr
    vc = chval(w, A, 'Y', yd, '-u 1', m1)
    sq = D(w, A, 'eqtr3d', [chmul(w, A, 'Y', yd, '-u 1', '-u 1', m1, m1),
                            D(w, A, 'eqtrd', [D(w, A, 'fveq2d', [D(w, A, 'fveq2d', [cst(w, A, 'neg1mulneg1e1', '( -u 1 x. -u 1 ) = 1')], '( %s ` ( -u 1 x. -u 1 ) ) = ( %s ` 1 )' % (LMr, LMr))],
                                                '( Y ` ( %s ` ( -u 1 x. -u 1 ) ) ) = ( Y ` ( %s ` 1 ) )' % (LMr, LMr)),
                                              D(w, A, 'dchrzrh1', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, LMr), yd], '( Y ` ( %s ` 1 ) ) = 1' % LMr)], '( Y ` ( %s ` ( -u 1 x. -u 1 ) ) ) = 1' % LMr)],
            '( %s x. %s ) = 1' % (V, V))
    sq2 = D(w, A, 'eqtrd', [D(w, A, 'sqvald', [vc], '( %s ^ 2 ) = ( %s x. %s )' % (V, V, V)), sq], '( %s ^ 2 ) = 1' % V)
    sq3 = D(w, A, 'eqtr4d', [sq2, cst(w, A, 'sq1', '( 1 ^ 2 ) = 1')], '( %s ^ 2 ) = ( 1 ^ 2 )' % V)
    orr = D(w, A, 'mpbid', [sq3, D(w, A, 'syl2anc', [vc, cst(w, A, 'ax-1cn', '1 e. CC'), w.inst('sqeqor')], '( ( %s ^ 2 ) = ( 1 ^ 2 ) <-> ( %s = 1 \\/ %s = -u 1 ) )' % (V, V, V))], '( %s = 1 \\/ %s = -u 1 )' % (V, V))
    PAR = L.ZL3.PAR
    # the inverse character
    ga = D(w, A, 'syl', [D(w, A, 'syl', [mn, w.s([eq_(w, GD)], 'dchrabl', '( M e. NN -> %s e. Abel )' % GD)], '%s e. Abel' % GD), w.inst('ablgrp')], '%s e. Grp' % GD)
    ybd = D(w, A, 'syl2anc', [ga, yd, w.s([eq_(w, DB), eq_(w, IG)], 'grpinvcl', '( ( %s e. Grp /\\ Y e. %s ) -> %s e. %s )' % (GD, DB, L.ZL3.YB, DB))], '%s e. %s' % (L.ZL3.YB, DB))
    inv = D(w, A, 'dchrinv', [eq_(w, GD), eq_(w, DB), yd, eq_(w, IG)], '%s = ( * o. Y )' % L.ZL3.YB)
    yf = D(w, A, 'dchrf', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, BZ), yd], 'Y : %s --> CC' % BZ)
    lb = lm_base(w, A, mn, '-u 1', m1)
    VB = '( %s ` ( %s ` -u 1 ) )' % (L.ZL3.YB, LMr)
    vb = D(w, A, 'eqtrd', [D(w, A, 'fveq1d', [inv], '%s = ( ( * o. Y ) ` ( %s ` -u 1 ) )' % (VB, LMr)), D(w, A, 'syl2anc', [yf, lb, w.inst('fvco3')], '( ( * o. Y ) ` ( %s ` -u 1 ) ) = ( * ` %s )' % (LMr, V))],
           '%s = ( * ` %s )' % (VB, V))
    # case V = 1
    A1 = '( %s /\\ %s = 1 )' % (A, V)
    e1 = w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, V))
    p0 = D(w, A1, 'iftrued', [e1], '%s = 0' % PAR)
    pw0 = D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [p0], '( -u 1 ^ %s ) = ( -u 1 ^ 0 )' % PAR), cst(w, A1, 'neg1cn', '-u 1 e. CC') if False else
                             w.s([w.s([w.s([], 'neg1cn', '-u 1 e. CC'), w.inst('exp0')], 'ax-mp', '( -u 1 ^ 0 ) = 1')], 'a1i', '( %s -> ( -u 1 ^ 0 ) = 1 )' % A1)], '( -u 1 ^ %s ) = 1' % PAR)
    c1a = D(w, A1, 'eqtr4d', [e1, pw0], '%s = ( -u 1 ^ %s )' % (V, PAR))
    cjv1 = D(w, A1, 'eqtrd', [D(w, A1, 'fveq2d', [e1], '( * ` %s ) = ( * ` 1 )' % V), w.s([w.s([w.s([], '1re', '1 e. RR'), w.inst('cjre')], 'ax-mp', '( * ` 1 ) = 1')], 'a1i', '( %s -> ( * ` 1 ) = 1 )' % A1)],
             '( * ` %s ) = 1' % V)
    c1b = D(w, A1, 'eqtr4d', [D(w, A1, 'eqtrd', [ad(w, A1, vb, '%s = ( * ` %s )' % (VB, V)), cjv1], '%s = 1' % VB), pw0], '%s = ( -u 1 ^ %s )' % (VB, PAR))
    p01 = D(w, A1, 'eqeltrd', [p0, cst(w, A1, 'c0ex' if False else 'prid1', '0 e. { 0 , 1 }') if False else w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }') and D(w, A1, 'idi', [w.s([], 'a1i', '')], '') if False else
                               w.s([w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }')], 'a1i', '( %s -> 0 e. { 0 , 1 } )' % A1)], '%s e. { 0 , 1 }' % PAR)
    case1 = D(w, A1, 'jca', [D(w, A1, 'jca', [p01, ad(w, A1, ybd, '%s e. %s' % (L.ZL3.YB, DB))], '( %s e. { 0 , 1 } /\\ %s e. %s )' % (PAR, L.ZL3.YB, DB)),
                             D(w, A1, 'jca', [c1a, c1b], '( %s = ( -u 1 ^ %s ) /\\ %s = ( -u 1 ^ %s ) )' % (V, PAR, VB, PAR))], Cc)
    # case V = -1
    A2 = '( %s /\\ %s = -u 1 )' % (A, V)
    e2 = w.s([], 'simpr', '( %s -> %s = -u 1 )' % (A2, V))
    ne = D(w, A2, 'eqnetrd' if False else 'eqnetrd', [e2, cst(w, A2, 'neg1ne1' if False else 'idi', '') if False else
                                                  w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], 'ax-1ne0', '1 =/= 0')], 'negne' if False else 'idi', '') if False else None], '', '') if False else
                                                  w.s([], 'neg1ne1' if False else 'idi', '') if False else None], '') if False else None
    lt = w.s([w.s([w.s([], 'neg1rr', '-u 1 e. RR'), w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR')], 'lttri', '( ( -u 1 < 0 /\\ 0 < 1 ) -> -u 1 < 1 )'),
              w.s([], 'neg1lt0', '-u 1 < 0'), w.s([], '0lt1', '0 < 1')], 'mp2an', '-u 1 < 1') if False else None
    lt = w.s([w.s([], 'neg1lt0', '-u 1 < 0'), w.s([], '0lt1', '0 < 1'), w.s([w.s([], 'neg1rr', '-u 1 e. RR'), w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR')], 'lttri', '( ( -u 1 < 0 /\\ 0 < 1 ) -> -u 1 < 1 )')],
             'mp2an', '-u 1 < 1')
    n1 = w.s([w.s([w.s([], 'neg1rr', '-u 1 e. RR'), lt], 'ltneii', '-u 1 =/= 1')], 'a1i', '( %s -> -u 1 =/= 1 )' % A2)
    vne = D(w, A2, 'eqnetrd', [e2, n1], '%s =/= 1' % V)
    p1 = D(w, A2, 'iffalsed', [D(w, A2, 'neneqd', [vne], '-. %s = 1' % V)], '%s = 1' % PAR)
    pw1 = D(w, A2, 'eqtrd', [D(w, A2, 'oveq2d', [p1], '( -u 1 ^ %s ) = ( -u 1 ^ 1 )' % PAR), w.s([w.s([w.s([], 'neg1cn', '-u 1 e. CC'), w.inst('exp1')], 'ax-mp', '( -u 1 ^ 1 ) = -u 1')], 'a1i', '( %s -> ( -u 1 ^ 1 ) = -u 1 )' % A2)],
            '( -u 1 ^ %s ) = -u 1' % PAR)
    c2a = D(w, A2, 'eqtr4d', [e2, pw1], '%s = ( -u 1 ^ %s )' % (V, PAR))
    cjv2 = D(w, A2, 'eqtrd', [D(w, A2, 'fveq2d', [e2], '( * ` %s ) = ( * ` -u 1 )' % V), w.s([w.s([w.s([], 'neg1rr', '-u 1 e. RR'), w.inst('cjre')], 'ax-mp', '( * ` -u 1 ) = -u 1')], 'a1i', '( %s -> ( * ` -u 1 ) = -u 1 )' % A2)],
             '( * ` %s ) = -u 1' % V)
    c2b = D(w, A2, 'eqtr4d', [D(w, A2, 'eqtrd', [ad(w, A2, vb, '%s = ( * ` %s )' % (VB, V)), cjv2], '%s = -u 1' % VB), pw1], '%s = ( -u 1 ^ %s )' % (VB, PAR))
    p11 = D(w, A2, 'eqeltrd', [p1, w.s([w.s([w.s([], '1ex', '1 e. _V')], 'prid2', '1 e. { 0 , 1 }')], 'a1i', '( %s -> 1 e. { 0 , 1 } )' % A2)], '%s e. { 0 , 1 }' % PAR)
    case2 = D(w, A2, 'jca', [D(w, A2, 'jca', [p11, ad(w, A2, ybd, '%s e. %s' % (L.ZL3.YB, DB))], '( %s e. { 0 , 1 } /\\ %s e. %s )' % (PAR, L.ZL3.YB, DB)),
                             D(w, A2, 'jca', [c2a, c2b], '( %s = ( -u 1 ^ %s ) /\\ %s = ( -u 1 ^ %s ) )' % (V, PAR, VB, PAR))], Cc)
    w.qed([case1, case2, orr], 'mpjaodan', S['zl3par'])
    go(w)


from zl3b_e4 import p_nn0


def pcases(w, A, pp, f, step0, step1):
    """( A -> f ) from step0( A0 ) and step1( A1 ) under P = 0 / P = 1"""
    A0 = '( %s /\\ P = 0 )' % A; A1 = '( %s /\\ P = 1 )' % A
    return w.s([step0(A0, w.s([], 'simpr', '( %s -> P = 0 )' % A0)), step1(A1, w.s([], 'simpr', '( %s -> P = 1 )' % A1)),
                w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % A)], 'mpjaodan', '( %s -> %s )' % (A, f))


def two_neg(w, A, K, kn0):
    """( A -> ( 2 ^c -u K ) = ( ( 1 / 2 ) ^ K ) ) for K e. NN0"""
    kc = D(w, A, 'nn0cnd', [kn0], '%s e. CC' % K)
    a = D(w, A, 'syl3anc', [cst(w, A, '2cn', '2 e. CC'), cst(w, A, '2ne0', '2 =/= 0'), kc, w.inst('cxpneg')], '( 2 ^c -u %s ) = ( 1 / ( 2 ^c %s ) )' % (K, K))
    b = D(w, A, 'oveq2d', [D(w, A, 'syl2anc', [cst(w, A, '2cn', '2 e. CC'), kn0, w.inst('cxpexp')], '( 2 ^c %s ) = ( 2 ^ %s )' % (K, K))], '( 1 / ( 2 ^c %s ) ) = ( 1 / ( 2 ^ %s ) )' % (K, K))
    c = D(w, A, 'syl3anc', [cst(w, A, '2cn', '2 e. CC'), cst(w, A, '2ne0', '2 =/= 0'), D(w, A, 'nn0zd', [kn0], '%s e. ZZ' % K), w.inst('exprec')], '( ( 1 / 2 ) ^ %s ) = ( 1 / ( 2 ^ %s ) )' % (K, K))
    return chain(w, A, ['( 2 ^c -u %s )' % K, '( 1 / ( 2 ^c %s ) )' % K, '( 1 / ( 2 ^ %s ) )' % K, '( ( 1 / 2 ) ^ %s )' % K], [a, b, ('r', c)])


ZTZ = L.ZT('Z', 'X', 'P')
EXn = lambda n: '( exp ` -u ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) )' % n
ZTv = lambda n: '( ( Z ` ( %s ` %s ) ) x. ( ( %s ^ P ) x. %s ) )' % (LMr, n, n, EXn(n))



def _ztsub(w, v, N):
    """closed: ( v = N -> ZTv(v) = ZTv(N) )"""
    return w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (v, N, LMr, v, LMr, N))], 'fveq2d', '( %s = %s -> ( Z ` ( %s ` %s ) ) = ( Z ` ( %s ` %s ) ) )' % (v, N, LMr, v, LMr, N)),
                w.s([w.s([], 'oveq1', '( %s = %s -> ( %s ^ P ) = ( %s ^ P ) )' % (v, N, v, N)),
                     w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( %s = %s -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (v, N, v, N))], 'oveq2d', '( %s = %s -> ( _pi x. ( %s ^ 2 ) ) = ( _pi x. ( %s ^ 2 ) ) )' % (v, N, v, N))], 'oveq1d',
                                   '( %s = %s -> ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) = ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) )' % (v, N, v, N))], 'negeqd',
                              '( %s = %s -> -u ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) = -u ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) )' % (v, N, v, N))], 'fveq2d', '( %s = %s -> %s = %s )' % (v, N, EXn(v), EXn(N)))],
                    'oveq12d', '( %s = %s -> ( ( %s ^ P ) x. %s ) = ( ( %s ^ P ) x. %s ) )' % (v, N, v, EXn(v), N, EXn(N)))],
               'oveq12d', '( %s = %s -> %s = %s )' % (v, N, ZTv(v), ZTv(N)))

def ztval(w, A, N, nz):
    """( A -> ( ZTZ ` N ) = ZTv(N) )"""
    if 'n' in N.split():
        ZQ = L.ZT('Z', 'X', 'P').replace('( n e. ZZ |-> ', '( q e. ZZ |-> ', 1)
        body = ZTv('n')
        ZQv = ZTv('q')
        ZQ = '( q e. ZZ |-> %s )' % ZQv
        cb = w.s([w.s([], 'idi' if False else 'nfv', '') if False else None], '', '') if False else None
        sub_nq = _ztsub(w, 'n', 'q')
        cbv = w.s([sub_nq], 'cbvmptv', '%s = %s' % (ZTZ, ZQ))
        sub = _ztsub(w, 'q', N)
        v = D(w, A, 'syl', [nz, w.s([sub, eq_(w, ZQ), w.s([], 'ovex', '%s e. _V' % ZTv(N))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (N, ZQ, N, ZTv(N)))], '( %s ` %s ) = %s' % (ZQ, N, ZTv(N)))
        return D(w, A, 'eqtrd', [w.s([w.s([cbv], 'fveq1i', '( %s ` %s ) = ( %s ` %s )' % (ZTZ, N, ZQ, N))], 'a1i', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A, ZTZ, N, ZQ, N)), v], '( %s ` %s ) = %s' % (ZTZ, N, ZTv(N)))
    sub = w.s([w.s([w.s([], 'fveq2', '( n = %s -> ( %s ` n ) = ( %s ` %s ) )' % (N, LMr, LMr, N))], 'fveq2d', '( n = %s -> ( Z ` ( %s ` n ) ) = ( Z ` ( %s ` %s ) ) )' % (N, LMr, LMr, N)),
               w.s([w.s([], 'oveq1', '( n = %s -> ( n ^ P ) = ( %s ^ P ) )' % (N, N)),
                    w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( n = %s -> ( n ^ 2 ) = ( %s ^ 2 ) )' % (N, N))], 'oveq2d', '( n = %s -> ( _pi x. ( n ^ 2 ) ) = ( _pi x. ( %s ^ 2 ) ) )' % (N, N))], 'oveq1d',
                                  '( n = %s -> ( ( _pi x. ( n ^ 2 ) ) x. ( X / M ) ) = ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) )' % (N, N))], 'negeqd',
                             '( n = %s -> -u ( ( _pi x. ( n ^ 2 ) ) x. ( X / M ) ) = -u ( ( _pi x. ( %s ^ 2 ) ) x. ( X / M ) ) )' % (N, N))], 'fveq2d', '( n = %s -> %s = %s )' % (N, EXn('n'), EXn(N)))],
                   'oveq12d', '( n = %s -> ( ( n ^ P ) x. %s ) = ( ( %s ^ P ) x. %s ) )' % (N, EXn('n'), N, EXn(N)))],
              'oveq12d', '( n = %s -> %s = %s )' % (N, ZTv('n'), ZTv(N)))
    return D(w, A, 'syl', [nz, w.s([sub, eq_(w, ZTZ), w.s([], 'ovex', '%s e. _V' % ZTv(N))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (N, ZTZ, N, ZTv(N)))], '( %s ` %s ) = %s' % (ZTZ, N, ZTv(N)))


# ---------------------------------------------------------------- zl3zt
if want('zl3zt'):
    w = W('zl3zt', 'The full theta series of a character ` Z ` of parity ` P ` : a geometric majorant, and ` PZ = RM + 2 TH ` .')
    A, Cc = ante_of('zl3zt')
    h1 = D(w, A, 'simp1', [], L.CH('Z')); h2 = D(w, A, 'simp2', [], '( P e. { 0 , 1 } /\\ ( Z ` ( %s ` -u 1 ) ) = ( -u 1 ^ P ) )' % LMr); xrp = D(w, A, 'simp3', [], 'X e. RR+')
    mn = D(w, A, 'simpld', [h1], 'M e. NN'); zd = D(w, A, 'simprd', [h1], 'Z e. %s' % DB)
    pp = D(w, A, 'simpld', [h2], 'P e. { 0 , 1 }'); zm1 = D(w, A, 'simprd', [h2], '( Z ` ( %s ` -u 1 ) ) = ( -u 1 ^ P )' % LMr)
    pn = p_nn0(w, A, pp)
    mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+'); XM = '( X / M )'
    xmp = D(w, A, 'rpdivcld', [xrp, mrp], '%s e. RR+' % XM); xmr = D(w, A, 'rpred', [xmp], '%s e. RR' % XM)
    C0 = '( exp ` ( 1 / ( _pi x. %s ) ) )' % XM
    c0r = D(w, A, 'reefcld', [D(w, A, 'rpred', [D(w, A, 'rpreccld', [D(w, A, 'rpmulcld', [cst(w, A, 'pirp', '_pi e. RR+'), xmp], '( _pi x. %s ) e. RR+' % XM)], '( 1 / ( _pi x. %s ) ) e. RR+' % XM)],
                                                      '( 1 / ( _pi x. %s ) ) e. RR' % XM)], '%s e. RR' % C0)
    def zval_cl(A2, N, nz, zd2, pn2, xm2):
        """( A2 -> ZTv(N) e. CC ), E real"""
        zc = chval(w, A2, 'Z', zd2, N, nz)
        er = D(w, A2, 'reefcld', [D(w, A2, 'renegcld', [D(w, A2, 'remulcld', [D(w, A2, 'remulcld', [cst(w, A2, 'pire', '_pi e. RR'), D(w, A2, 'resqcld', [D(w, A2, 'zred', [nz], '%s e. RR' % N)], '( %s ^ 2 ) e. RR' % N)],
                                                                                          '( _pi x. ( %s ^ 2 ) ) e. RR' % N), xm2], '( ( _pi x. ( %s ^ 2 ) ) x. %s ) e. RR' % (N, XM))], '-u ( ( _pi x. ( %s ^ 2 ) ) x. %s ) e. RR' % (N, XM))],
                 '%s e. RR' % EXn(N))
        pc = D(w, A2, 'expcld', [D(w, A2, 'zcnd', [nz], '%s e. CC' % N), pn2], '( %s ^ P ) e. CC' % N)
        return D(w, A2, 'mulcld', [zc, D(w, A2, 'mulcld', [pc, D(w, A2, 'recnd', [er], '%s e. CC' % EXn(N))], '( ( %s ^ P ) x. %s ) e. CC' % (N, EXn(N)))], '%s e. CC' % ZTv(N)), er, zc, pc
    # the majorant at i
    Ai = '( %s /\\ i e. ZZ )' % A
    iz = w.s([], 'simpr', '( %s -> i e. ZZ )' % Ai)
    ua = lambda st, f: ad(w, Ai, st, f)
    zvc, er, zc, pc = zval_cl(Ai, 'i', iz, ua(zd, 'Z e. %s' % DB), ua(pn, 'P e. NN0'), ua(xmr, '%s e. RR' % XM))
    zv = ztval(w, Ai, 'i', iz)
    ir = D(w, Ai, 'zred', [iz], 'i e. RR'); ic = D(w, Ai, 'zcnd', [iz], 'i e. CC')
    AI = '( abs ` i )'; air = D(w, Ai, 'abscld', [ic], '%s e. RR' % AI); ai0 = D(w, Ai, 'syl', [iz, w.inst('nn0abscl')], '%s e. NN0' % AI)
    za = D(w, Ai, 'dchrabs2', [eq_(w, GD), eq_(w, DB), eq_(w, ZN), eq_(w, BZ), ua(zd, 'Z e. %s' % DB), lm_base(w, Ai, ua(mn, 'M e. NN'), 'i', iz)], '( abs ` ( Z ` ( %s ` i ) ) ) <_ 1' % LMr)
    def s0(A0, e):
        a = D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [e], '( i ^ P ) = ( i ^ 0 )'), D(w, A0, 'syl', [ad(w, A0, ic, 'i e. CC'), w.inst('exp0')], '( i ^ 0 ) = 1')], '( i ^ P ) = 1')
        b = D(w, A0, 'eqtrd', [D(w, A0, 'fveq2d', [a], '( abs ` ( i ^ P ) ) = ( abs ` 1 )'), cst(w, A0, 'abs1', '( abs ` 1 ) = 1')], '( abs ` ( i ^ P ) ) = 1')
        return D(w, A0, 'eqbrtrd', [b, linarith(w, A0, [D(w, A0, 'absge0d', [ad(w, A0, ic, 'i e. CC')], '0 <_ %s' % AI)], '1 <_ ( 1 + %s )' % AI, leaves={AI: ad(w, A0, air, '%s e. RR' % AI)}, atoms=[AI])],
                 '( abs ` ( i ^ P ) ) <_ ( 1 + %s )' % AI)
    def s1(A1, e):
        a = D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [e], '( i ^ P ) = ( i ^ 1 )'), D(w, A1, 'syl', [ad(w, A1, ic, 'i e. CC'), w.inst('exp1')], '( i ^ 1 ) = i')], '( i ^ P ) = i')
        return D(w, A1, 'eqbrtrd', [D(w, A1, 'fveq2d', [a], '( abs ` ( i ^ P ) ) = %s' % AI), linarith(w, A1, [], '%s <_ ( 1 + %s )' % (AI, AI), leaves={AI: ad(w, A1, air, '%s e. RR' % AI)}, atoms=[AI])],
                 '( abs ` ( i ^ P ) ) <_ ( 1 + %s )' % AI)
    ipb = pcases(w, Ai, ua(pp, 'P e. { 0 , 1 }'), '( abs ` ( i ^ P ) ) <_ ( 1 + %s )' % AI, s0, s1)
    E_ = EXn('i')
    e0 = D(w, Ai, 'rpge0d', [D(w, Ai, 'rpefcld', [D(w, Ai, 'renegcld', [D(w, Ai, 'remulcld', [D(w, Ai, 'remulcld', [cst(w, Ai, 'pire', '_pi e. RR'), D(w, Ai, 'resqcld', [ir], '( i ^ 2 ) e. RR')], '( _pi x. ( i ^ 2 ) ) e. RR'), ua(xmr, '%s e. RR' % XM)],
                                                                                 '( ( _pi x. ( i ^ 2 ) ) x. %s ) e. RR' % XM)], '-u ( ( _pi x. ( i ^ 2 ) ) x. %s ) e. RR' % XM)], '%s e. RR+' % E_)], '0 <_ %s' % E_)
    ab = chain(w, Ai, ['( abs ` %s )' % ZTv('i'), '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( abs ` ( ( i ^ P ) x. %s ) ) )' % (LMr, E_), '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. ( abs ` %s ) ) )' % (LMr, E_),
                       '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) )' % (LMr, E_)],
               [D(w, Ai, 'absmuld', [zc, D(w, Ai, 'mulcld', [pc, D(w, Ai, 'recnd', [er], '%s e. CC' % E_)], '( ( i ^ P ) x. %s ) e. CC' % E_)],
                  '( abs ` %s ) = ( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( abs ` ( ( i ^ P ) x. %s ) ) )' % (ZTv('i'), LMr, E_)),
                D(w, Ai, 'oveq2d', [D(w, Ai, 'absmuld', [pc, D(w, Ai, 'recnd', [er], '%s e. CC' % E_)], '( abs ` ( ( i ^ P ) x. %s ) ) = ( ( abs ` ( i ^ P ) ) x. ( abs ` %s ) )' % (E_, E_))],
                  '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( abs ` ( ( i ^ P ) x. %s ) ) ) = ( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. ( abs ` %s ) ) )' % (LMr, E_, LMr, E_)),
                D(w, Ai, 'oveq2d', [D(w, Ai, 'oveq2d', [D(w, Ai, 'absidd', [er, e0], '( abs ` %s ) = %s' % (E_, E_))], '( ( abs ` ( i ^ P ) ) x. ( abs ` %s ) ) = ( ( abs ` ( i ^ P ) ) x. %s )' % (E_, E_))],
                  '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. ( abs ` %s ) ) ) = ( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) )' % (LMr, E_, LMr, E_))])
    gre = D(w, Ai, 'syl2anc', [ua(xmp, '%s e. RR+' % XM), ir, w.inst('zl3gre')], '( ( 1 + %s ) x. ( exp ` -u ( ( _pi x. %s ) x. ( i ^ 2 ) ) ) ) <_ ( %s x. ( 2 ^c -u %s ) )' % (AI, XM, C0, AI))
    exq = D(w, Ai, 'fveq2d', [D(w, Ai, 'negeqd', [D(w, Ai, 'mul32d', [cst(w, Ai, 'picn', '_pi e. CC'), D(w, Ai, 'recnd', [D(w, Ai, 'resqcld', [ir], '( i ^ 2 ) e. RR')], '( i ^ 2 ) e. CC'), D(w, Ai, 'recnd', [ua(xmr, '%s e. RR' % XM)], '%s e. CC' % XM)],
                                                            '( ( _pi x. ( i ^ 2 ) ) x. %s ) = ( ( _pi x. %s ) x. ( i ^ 2 ) )' % (XM, XM))], '-u ( ( _pi x. ( i ^ 2 ) ) x. %s ) = -u ( ( _pi x. %s ) x. ( i ^ 2 ) )' % (XM, XM))],
              '%s = ( exp ` -u ( ( _pi x. %s ) x. ( i ^ 2 ) ) )' % (E_, XM))
    gre2 = D(w, Ai, 'breqtrd', [D(w, Ai, 'eqbrtrd', [D(w, Ai, 'oveq2d', [exq], '( ( 1 + %s ) x. %s ) = ( ( 1 + %s ) x. ( exp ` -u ( ( _pi x. %s ) x. ( i ^ 2 ) ) ) )' % (AI, E_, AI, XM)), gre],
                                    '( ( 1 + %s ) x. %s ) <_ ( %s x. ( 2 ^c -u %s ) )' % (AI, E_, C0, AI)),
                                  D(w, Ai, 'oveq2d', [two_neg(w, Ai, AI, ai0)], '( %s x. ( 2 ^c -u %s ) ) = ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (C0, AI, C0, AI))],
               '( ( 1 + %s ) x. %s ) <_ ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (AI, E_, C0, AI))
    zar = D(w, Ai, 'abscld', [zc], '( abs ` ( Z ` ( %s ` i ) ) ) e. RR' % LMr); par = D(w, Ai, 'abscld', [pc], '( abs ` ( i ^ P ) ) e. RR')
    one_ = cst(w, Ai, '1re', '1 e. RR')
    iar = D(w, Ai, 'readdcld', [one_, air], '( 1 + %s ) e. RR' % AI)
    p1 = D(w, Ai, 'lemul1ad', [par, iar, er, e0, ipb], '( ( abs ` ( i ^ P ) ) x. %s ) <_ ( ( 1 + %s ) x. %s )' % (E_, AI, E_))
    p2 = D(w, Ai, 'lemul12ad', [zar, one_, D(w, Ai, 'remulcld', [par, er], '( ( abs ` ( i ^ P ) ) x. %s ) e. RR' % E_), D(w, Ai, 'remulcld', [iar, er], '( ( 1 + %s ) x. %s ) e. RR' % (AI, E_)),
                                 D(w, Ai, 'absge0d', [zc], '0 <_ ( abs ` ( Z ` ( %s ` i ) ) )' % LMr), D(w, Ai, 'mulge0d', [par, er, D(w, Ai, 'absge0d', [pc], '0 <_ ( abs ` ( i ^ P ) )'), e0], '0 <_ ( ( abs ` ( i ^ P ) ) x. %s )' % E_),
                                 za, p1], '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) ) <_ ( 1 x. ( ( 1 + %s ) x. %s ) )' % (LMr, E_, AI, E_))
    p3 = D(w, Ai, 'breqtrd', [p2, D(w, Ai, 'mullidd', [D(w, Ai, 'recnd', [D(w, Ai, 'remulcld', [iar, er], '( ( 1 + %s ) x. %s ) e. RR' % (AI, E_))], '( ( 1 + %s ) x. %s ) e. CC' % (AI, E_))],
                                  '( 1 x. ( ( 1 + %s ) x. %s ) ) = ( ( 1 + %s ) x. %s )' % (AI, E_, AI, E_))], '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) ) <_ ( ( 1 + %s ) x. %s )' % (LMr, E_, AI, E_))
    bd = D(w, Ai, 'eqbrtrd', [D(w, Ai, 'eqtrd', [D(w, Ai, 'fveq2d', [zv], '( abs ` ( %s ` i ) ) = ( abs ` %s )' % (ZTZ, ZTv('i'))), ab], '( abs ` ( %s ` i ) ) = ( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) )' % (ZTZ, LMr, E_)),
                              D(w, Ai, 'letrd', [D(w, Ai, 'remulcld', [zar, D(w, Ai, 'remulcld', [par, er], '( ( abs ` ( i ^ P ) ) x. %s ) e. RR' % E_)], '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) ) e. RR' % (LMr, E_)),
                                                 D(w, Ai, 'remulcld', [iar, er], '( ( 1 + %s ) x. %s ) e. RR' % (AI, E_)),
                                                 D(w, Ai, 'remulcld', [ua(c0r, '%s e. RR' % C0), D(w, Ai, 'reexpcld', [cst(w, Ai, 'halfre', '( 1 / 2 ) e. RR'), ai0], '( ( 1 / 2 ) ^ %s ) e. RR' % AI)], '( %s x. ( ( 1 / 2 ) ^ %s ) ) e. RR' % (C0, AI)),
                                                 p3, gre2], '( ( abs ` ( Z ` ( %s ` i ) ) ) x. ( ( abs ` ( i ^ P ) ) x. %s ) ) <_ ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (LMr, E_, C0, AI))],
             '( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (ZTZ, C0, AI))
    An = '( %s /\\ n e. ZZ )' % A
    zfn = zval_cl(An, 'n', w.s([], 'simpr', '( %s -> n e. ZZ )' % An), ad(w, An, zd, 'Z e. %s' % DB), ad(w, An, pn, 'P e. NN0'), ad(w, An, xmr, '%s e. RR' % XM))[0]
    ztf = D(w, A, 'fmptd', [zfn, eq_(w, ZTZ)], '%s : ZZ --> CC' % ZTZ)
    HBZ = D(w, A, 'jca', [ztf, D(w, A, 'jca', [c0r, D(w, A, 'ralrimiva', [bd], 'A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) )' % (ZTZ, C0))],
                                               '( %s e. RR /\\ A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) )' % (C0, ZTZ, C0))], L.HBF(ZTZ, C0))
    # the term at 0
    RM = L.ZL3.RM
    z0v = ztval(w, A, '0', cst(w, A, '0z', '0 e. ZZ'))
    E0 = EXn('0')
    e0eq = D(w, A, 'eqtrd', [D(w, A, 'fveq2d', [D(w, A, 'eqtrd', [D(w, A, 'negeqd', [D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [cst(w, A, 'sq0', '( 0 ^ 2 ) = 0')], '( _pi x. ( 0 ^ 2 ) ) = ( _pi x. 0 )'),
                                                                                                                                 D(w, A, 'mul01d', [cst(w, A, 'picn', '_pi e. CC')], '( _pi x. 0 ) = 0')], '( _pi x. ( 0 ^ 2 ) ) = 0')],
                                                                                                  '( ( _pi x. ( 0 ^ 2 ) ) x. %s ) = ( 0 x. %s )' % (XM, XM)), D(w, A, 'mul02d', [D(w, A, 'recnd', [xmr], '%s e. CC' % XM)], '( 0 x. %s ) = 0' % XM)],
                                                                                   '( ( _pi x. ( 0 ^ 2 ) ) x. %s ) = 0' % XM)], '-u ( ( _pi x. ( 0 ^ 2 ) ) x. %s ) = -u 0' % XM), cst(w, A, 'neg0', '-u 0 = 0')],
                                                      '-u ( ( _pi x. ( 0 ^ 2 ) ) x. %s ) = 0' % XM)], '%s = ( exp ` 0 )' % E0), cst(w, A, 'ef0', '( exp ` 0 ) = 1')], '%s = 1' % E0)
    AM1 = '( %s /\\ M = 1 )' % A; AMn = '( %s /\\ -. M = 1 )' % A
    m1e = w.s([], 'simpr', '( %s -> M = 1 )' % AM1)
    m0_1 = D(w, AM1, 'nnnn0d', [ad(w, AM1, mn, 'M e. NN')], 'M e. NN0')
    def l_eq(A2, a, b, az, bz):
        """( A2 -> ( L ` a ) = ( L ` b ) ) when M = 1"""
        bi = D(w, A2, 'syl3anc', [m0_1 if A2 == AM1 else None, az, bz, w.s([eq_(w, ZN), eq_(w, LMr)], 'zndvds', '( ( M e. NN0 /\\ %s e. ZZ /\\ %s e. ZZ ) -> ( ( %s ` %s ) = ( %s ` %s ) <-> M || ( %s - %s ) ) )' % (a, b, LMr, a, LMr, b, a, b))],
               '( ( %s ` %s ) = ( %s ` %s ) <-> M || ( %s - %s ) )' % (LMr, a, LMr, b, a, b))
        dv = D(w, A2, 'mpbird', [D(w, A2, 'syl', [D(w, A2, 'zsubcld', [az, bz], '( %s - %s ) e. ZZ' % (a, b)), w.inst('1dvds')], '1 || ( %s - %s )' % (a, b)),
                                 D(w, A2, 'breq1d', [m1e], '( M || ( %s - %s ) <-> 1 || ( %s - %s ) )' % (a, b, a, b))], 'M || ( %s - %s )' % (a, b))
        return D(w, A2, 'mpbird', [dv, bi], '( %s ` %s ) = ( %s ` %s )' % (LMr, a, LMr, b))
    zd1 = ad(w, AM1, zd, 'Z e. %s' % DB)
    z1 = D(w, AM1, 'dchrzrh1', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, LMr), zd1], '( Z ` ( %s ` 1 ) ) = 1' % LMr)
    zz0 = D(w, AM1, 'eqtrd', [D(w, AM1, 'fveq2d', [l_eq(AM1, '0', '1', cst(w, AM1, '0z', '0 e. ZZ'), cst(w, AM1, '1z', '1 e. ZZ'))], '( Z ` ( %s ` 0 ) ) = ( Z ` ( %s ` 1 ) )' % (LMr, LMr)), z1],
              '( Z ` ( %s ` 0 ) ) = 1' % LMr)
    zmm = D(w, AM1, 'eqtrd', [D(w, AM1, 'fveq2d', [l_eq(AM1, '-u 1', '1', cst(w, AM1, 'neg1z', '-u 1 e. ZZ'), cst(w, AM1, '1z', '1 e. ZZ'))], '( Z ` ( %s ` -u 1 ) ) = ( Z ` ( %s ` 1 ) )' % (LMr, LMr)), z1],
              '( Z ` ( %s ` -u 1 ) ) = 1' % LMr)
    pw1 = D(w, AM1, 'eqtr3d', [ad(w, AM1, zm1, '( Z ` ( %s ` -u 1 ) ) = ( -u 1 ^ P )' % LMr), zmm], '( -u 1 ^ P ) = 1')
    def q0(A0, e):
        return e
    def q1(A1, e):
        c = D(w, A1, 'eqtr3d', [D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [e], '( -u 1 ^ P ) = ( -u 1 ^ 1 )'), w.s([w.s([w.s([], 'neg1cn', '-u 1 e. CC'), w.inst('exp1')], 'ax-mp', '( -u 1 ^ 1 ) = -u 1')], 'a1i', '( %s -> ( -u 1 ^ 1 ) = -u 1 )' % A1)],
                                             '( -u 1 ^ P ) = -u 1'), ad(w, A1, pw1, '( -u 1 ^ P ) = 1')], '-u 1 = 1')
        lt = w.s([w.s([], 'neg1lt0', '-u 1 < 0'), w.s([], '0lt1', '0 < 1'), w.s([w.s([], 'neg1rr', '-u 1 e. RR'), w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR')], 'lttri', '( ( -u 1 < 0 /\\ 0 < 1 ) -> -u 1 < 1 )')],
                 'mp2an', '-u 1 < 1')
        ne = w.s([w.s([w.s([w.s([], 'neg1rr', '-u 1 e. RR'), lt], 'ltneii', '-u 1 =/= 1')], 'neii', '-. -u 1 = 1')], 'a1i', '( %s -> -. -u 1 = 1 )' % A1)
        return D(w, A1, 'pm2.21dd', [c, ne], 'P = 0')
    p0 = pcases(w, AM1, ad(w, AM1, pp, 'P e. { 0 , 1 }'), 'P = 0', q0, q1)
    zp = D(w, AM1, 'eqtrd', [D(w, AM1, 'oveq2d', [p0], '( 0 ^ P ) = ( 0 ^ 0 )'), w.s([w.s([w.s([], '0cn', '0 e. CC'), w.inst('exp0')], 'ax-mp', '( 0 ^ 0 ) = 1')], 'a1i', '( %s -> ( 0 ^ 0 ) = 1 )' % AM1)], '( 0 ^ P ) = 1')
    T0 = ZTv('0')
    t0a = D(w, AM1, 'eqtrd', [D(w, AM1, 'oveq12d', [zz0, D(w, AM1, 'oveq12d', [zp, ad(w, AM1, e0eq, '%s = 1' % E0)], '( ( 0 ^ P ) x. %s ) = ( 1 x. 1 )' % E0)], '%s = ( 1 x. ( 1 x. 1 ) )' % T0),
                              w.s([w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'oveq2i', '( 1 x. ( 1 x. 1 ) ) = ( 1 x. 1 )'), w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'eqtri', '( 1 x. ( 1 x. 1 ) ) = 1') and
                              w.s([w.s([w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'oveq2i', '( 1 x. ( 1 x. 1 ) ) = ( 1 x. 1 )'), w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'eqtri', '( 1 x. ( 1 x. 1 ) ) = 1')], 'a1i',
                                  '( %s -> ( 1 x. ( 1 x. 1 ) ) = 1 )' % AM1)], '%s = 1' % T0)
    rm1 = D(w, AM1, 'iftrued', [m1e], '%s = 1' % RM)
    c1 = D(w, AM1, 'eqtr4d', [D(w, AM1, 'eqtrd', [ad(w, AM1, z0v, '( %s ` 0 ) = %s' % (ZTZ, T0)), t0a], '( %s ` 0 ) = 1' % ZTZ), rm1], '( %s ` 0 ) = %s' % (ZTZ, RM))
    # M =/= 1
    mn1 = w.s([], 'simpr', '( %s -> -. M = 1 )' % AMn)
    mnn = ad(w, AMn, mn, 'M e. NN')
    un = D(w, AMn, 'syl2anc', [D(w, AMn, 'nnnn0d', [mnn], 'M e. NN0'), cst(w, AMn, '0z', '0 e. ZZ'), w.s([eq_(w, ZN), eq_(w, UZ), eq_(w, LMr)], 'znunit', '( ( M e. NN0 /\\ 0 e. ZZ ) -> ( ( %s ` 0 ) e. %s <-> ( 0 gcd M ) = 1 ) )' % (LMr, UZ))],
           '( ( %s ` 0 ) e. %s <-> ( 0 gcd M ) = 1 )' % (LMr, UZ))
    g0 = D(w, AMn, 'eqtrd', [D(w, AMn, 'syl', [D(w, AMn, 'nnzd', [mnn], 'M e. ZZ'), w.inst('gcd0id')], '( 0 gcd M ) = ( abs ` M )'), D(w, AMn, 'absidd', [D(w, AMn, 'nnred', [mnn], 'M e. RR'), D(w, AMn, 'nnnn0d' if False else 'nn0ge0d', [D(w, AMn, 'nnnn0d', [mnn], 'M e. NN0')], '0 <_ M')], '( abs ` M ) = M')],
            '( 0 gcd M ) = M')
    gn = D(w, AMn, 'mtbird' if False else 'mtbird', [], '') if False else None
    ng = D(w, AMn, 'mtbird', [D(w, AMn, 'eqeq1d', [g0], '( ( 0 gcd M ) = 1 <-> M = 1 )') if False else mn1, D(w, AMn, 'eqeq1d', [g0], '( ( 0 gcd M ) = 1 <-> M = 1 )')], '-. ( 0 gcd M ) = 1')
    nu = D(w, AMn, 'mtbird', [ng, un], '-. ( %s ` 0 ) e. %s' % (LMr, UZ))
    zn0 = D(w, AMn, 'dchrn0', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, BZ), eq_(w, UZ), ad(w, AMn, zd, 'Z e. %s' % DB), lm_base(w, AMn, mnn, '0', cst(w, AMn, '0z', '0 e. ZZ'))],
            '( ( Z ` ( %s ` 0 ) ) =/= 0 <-> ( %s ` 0 ) e. %s )' % (LMr, LMr, UZ))
    zz = D(w, AMn, 'mpbid', [D(w, AMn, 'mtbird', [nu, zn0], '-. ( Z ` ( %s ` 0 ) ) =/= 0' % LMr), cst(w, AMn, 'nne', '( -. ( Z ` ( %s ` 0 ) ) =/= 0 <-> ( Z ` ( %s ` 0 ) ) = 0 )' % (LMr, LMr))],
            '( Z ` ( %s ` 0 ) ) = 0' % LMr)
    zvn = zval_cl(AMn, '0', cst(w, AMn, '0z', '0 e. ZZ'), ad(w, AMn, zd, 'Z e. %s' % DB), ad(w, AMn, pn, 'P e. NN0'), ad(w, AMn, xmr, '%s e. RR' % XM))
    rest = D(w, AMn, 'mulcld', [zvn[3], D(w, AMn, 'recnd', [zvn[1]], '%s e. CC' % E0)], '( ( 0 ^ P ) x. %s ) e. CC' % E0)
    t0n = D(w, AMn, 'eqtrd', [D(w, AMn, 'oveq1d', [zz], '%s = ( 0 x. ( ( 0 ^ P ) x. %s ) )' % (T0, E0)), D(w, AMn, 'mul02d', [rest], '( 0 x. ( ( 0 ^ P ) x. %s ) ) = 0' % E0)], '%s = 0' % T0)
    c2 = D(w, AMn, 'eqtr4d', [D(w, AMn, 'eqtrd', [ad(w, AMn, z0v, '( %s ` 0 ) = %s' % (ZTZ, T0)), t0n], '( %s ` 0 ) = 0' % ZTZ), D(w, AMn, 'iffalsed', [mn1], '%s = 0' % RM)], '( %s ` 0 ) = %s' % (ZTZ, RM))
    zt0 = w.s([c1, c2], 'pm2.61dan', '( %s -> ( %s ` 0 ) = %s )' % (A, ZTZ, RM))
    # symmetry at n e. NN
    An = '( %s /\\ n e. NN )' % A
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    nz = D(w, An, 'nnzd', [nn_], 'n e. ZZ'); nc = D(w, An, 'zcnd', [nz], 'n e. CC')
    mnz = D(w, An, 'znegcld', [nz], '-u n e. ZZ')
    zdn, pnn, xmn = ad(w, An, zd, 'Z e. %s' % DB), ad(w, An, pn, 'P e. NN0'), ad(w, An, xmr, '%s e. RR' % XM)
    zvn_, ern, zcn, pcn = zval_cl(An, 'n', nz, zdn, pnn, xmn)
    vn = ztval(w, An, 'n', nz); vmn = ztval(w, An, '-u n', mnz)
    a_ = '( -u 1 ^ P )'
    ac = D(w, An, 'expcld', [cst(w, An, 'neg1cn', '-u 1 e. CC'), pnn], '%s e. CC' % a_)
    zmn = D(w, An, 'eqtrd', [D(w, An, 'fveq2d', [D(w, An, 'fveq2d', [D(w, An, 'eqcomd', [D(w, An, 'mulm1d', [nc], '( -u 1 x. n ) = -u n')], '-u n = ( -u 1 x. n )')], '( %s ` -u n ) = ( %s ` ( -u 1 x. n ) )' % (LMr, LMr))],
                                           '( Z ` ( %s ` -u n ) ) = ( Z ` ( %s ` ( -u 1 x. n ) ) )' % (LMr, LMr)),
                             D(w, An, 'eqtrd', [chmul(w, An, 'Z', zdn, '-u 1', 'n', cst(w, An, 'neg1z', '-u 1 e. ZZ'), nz),
                                                D(w, An, 'oveq1d', [ad(w, An, zm1, '( Z ` ( %s ` -u 1 ) ) = %s' % (LMr, a_))], '( ( Z ` ( %s ` -u 1 ) ) x. ( Z ` ( %s ` n ) ) ) = ( %s x. ( Z ` ( %s ` n ) ) )' % (LMr, LMr, a_, LMr))],
                               '( Z ` ( %s ` ( -u 1 x. n ) ) ) = ( %s x. ( Z ` ( %s ` n ) ) )' % (LMr, a_, LMr))], '( Z ` ( %s ` -u n ) ) = ( %s x. ( Z ` ( %s ` n ) ) )' % (LMr, a_, LMr))
    pmn = D(w, An, 'eqtrd', [D(w, An, 'oveq1d', [D(w, An, 'eqcomd', [D(w, An, 'mulm1d', [nc], '( -u 1 x. n ) = -u n')], '-u n = ( -u 1 x. n )')], '( -u n ^ P ) = ( ( -u 1 x. n ) ^ P )'),
                             D(w, An, 'mulexpd', [cst(w, An, 'neg1cn', '-u 1 e. CC'), nc, pnn], '( ( -u 1 x. n ) ^ P ) = ( %s x. ( n ^ P ) )' % a_)], '( -u n ^ P ) = ( %s x. ( n ^ P ) )' % a_)
    emn = D(w, An, 'fveq2d', [D(w, An, 'negeqd', [D(w, An, 'oveq1d', [D(w, An, 'oveq2d', [D(w, An, 'sqnegd', [nc], '( -u n ^ 2 ) = ( n ^ 2 )')], '( _pi x. ( -u n ^ 2 ) ) = ( _pi x. ( n ^ 2 ) )')],
                                                                     '( ( _pi x. ( -u n ^ 2 ) ) x. %s ) = ( ( _pi x. ( n ^ 2 ) ) x. %s )' % (XM, XM))], '-u ( ( _pi x. ( -u n ^ 2 ) ) x. %s ) = -u ( ( _pi x. ( n ^ 2 ) ) x. %s )' % (XM, XM))],
            '%s = %s' % (EXn('-u n'), EXn('n')))
    Zn, Np, En = '( Z ` ( %s ` n ) )' % LMr, '( n ^ P )', EXn('n')
    enc = D(w, An, 'recnd', [ern], '%s e. CC' % En)
    aa = chain(w, An, ['( %s x. %s )' % (a_, a_), '( ( -u 1 x. -u 1 ) ^ P )', '( 1 ^ P )', '1'],
               [('r', D(w, An, 'mulexpd', [cst(w, An, 'neg1cn', '-u 1 e. CC'), cst(w, An, 'neg1cn', '-u 1 e. CC'), pnn], '( ( -u 1 x. -u 1 ) ^ P ) = ( %s x. %s )' % (a_, a_))),
                D(w, An, 'oveq1d', [cst(w, An, 'neg1mulneg1e1', '( -u 1 x. -u 1 ) = 1')], '( ( -u 1 x. -u 1 ) ^ P ) = ( 1 ^ P )'), D(w, An, 'syl', [D(w, An, 'nn0zd', [pnn], 'P e. ZZ'), w.inst('1exp')], '( 1 ^ P ) = 1')])
    sy = chain(w, An, [ZTv('-u n'), '( ( %s x. %s ) x. ( ( %s x. %s ) x. %s ) )' % (a_, Zn, a_, Np, En), '( ( %s x. %s ) x. ( %s x. ( %s x. %s ) ) )' % (a_, Zn, a_, Np, En),
                       '( ( %s x. %s ) x. ( %s x. ( %s x. %s ) ) )' % (a_, a_, Zn, Np, En), '( 1 x. ( %s x. ( %s x. %s ) ) )' % (Zn, Np, En), ZTv('n')],
               [D(w, An, 'oveq12d', [zmn, D(w, An, 'oveq12d', [pmn, emn], '( ( -u n ^ P ) x. %s ) = ( ( %s x. %s ) x. %s )' % (EXn('-u n'), a_, Np, En))],
                  '%s = ( ( %s x. %s ) x. ( ( %s x. %s ) x. %s ) )' % (ZTv('-u n'), a_, Zn, a_, Np, En)),
                D(w, An, 'oveq2d', [D(w, An, 'mulassd', [ac, pcn, enc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (a_, Np, En, a_, Np, En))],
                  '( ( %s x. %s ) x. ( ( %s x. %s ) x. %s ) ) = ( ( %s x. %s ) x. ( %s x. ( %s x. %s ) ) )' % (a_, Zn, a_, Np, En, a_, Zn, a_, Np, En)),
                D(w, An, 'mul4d', [ac, zcn, ac, D(w, An, 'mulcld', [pcn, enc], '( %s x. %s ) e. CC' % (Np, En))], '( ( %s x. %s ) x. ( %s x. ( %s x. %s ) ) ) = ( ( %s x. %s ) x. ( %s x. ( %s x. %s ) ) )' % (a_, Zn, a_, Np, En, a_, a_, Zn, Np, En)),
                D(w, An, 'oveq1d', [aa], '( ( %s x. %s ) x. ( %s x. ( %s x. %s ) ) ) = ( 1 x. ( %s x. ( %s x. %s ) ) )' % (a_, a_, Zn, Np, En, Zn, Np, En)),
                D(w, An, 'mullidd', [zvn_], '( 1 x. %s ) = %s' % (ZTv('n'), ZTv('n')))])
    ztn = '( %s ` n )' % ZTZ
    pr_ = D(w, An, 'eqtr4d', [D(w, An, 'oveq2d', [D(w, An, 'eqtr4d', [vmn, D(w, An, 'eqtrd', [vn, D(w, An, 'eqcomd', [sy], '%s = %s' % (ZTv('n'), ZTv('-u n')))], '%s = %s' % (ztn, ZTv('-u n')))],
                                                    '( %s ` -u n ) = %s' % (ZTZ, ztn))], '( %s + ( %s ` -u n ) ) = ( %s + %s )' % (ztn, ZTZ, ztn, ztn)),
                              D(w, An, '2timesd', [D(w, An, 'eqeltrd', [vn, zvn_], '%s e. CC' % ztn)], '( 2 x. %s ) = ( %s + %s )' % (ztn, ztn, ztn))],
            '( %s + ( %s ` -u n ) ) = ( 2 x. %s )' % (ztn, ZTZ, ztn))
    s1 = D(w, A, 'sumeq2dv', [pr_], 'sum_ n e. NN ( %s + ( %s ` -u n ) ) = sum_ n e. NN ( 2 x. %s )' % (ztn, ZTZ, ztn))
    ZQ = '( q e. ZZ |-> %s )' % ZTv('q')
    cbq = w.s([_ztsub(w, 'n', 'q')], 'cbvmptv', '%s = %s' % (ZTZ, ZQ))
    fq = lambda A2, v: w.s([w.s([cbq], 'fveq1i', '( %s ` %s ) = ( %s ` %s )' % (ZTZ, v, ZQ, v))], 'a1i', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A2, ZTZ, v, ZQ, v))
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    kz = D(w, Ak, 'nnzd', [kn], 'k e. ZZ')
    zkc = D(w, Ak, 'ffvelcdmd', [ad(w, Ak, ztf, '%s : ZZ --> CC' % ZTZ), kz], '( %s ` k ) e. CC' % ZTZ)
    bdk = D(w, Ak, 'rspcdva', [w.s([w.s([w.s([], 'fveq2', '( i = k -> ( %s ` i ) = ( %s ` k ) )' % (ZTZ, ZTZ))], 'fveq2d', '( i = k -> ( abs ` ( %s ` i ) ) = ( abs ` ( %s ` k ) ) )' % (ZTZ, ZTZ)),
                                    w.s([w.s([w.s([], 'fveq2', '( i = k -> ( abs ` i ) = ( abs ` k ) )')], 'oveq2d', '( i = k -> ( ( 1 / 2 ) ^ ( abs ` i ) ) = ( ( 1 / 2 ) ^ ( abs ` k ) ) )')], 'oveq2d',
                                        '( i = k -> ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) = ( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) ) )' % (C0, C0))], 'breq12d',
                                   '( i = k -> ( ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) <-> ( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) ) ) )' % (ZTZ, C0, ZTZ, C0)),
                               ad(w, Ak, D(w, A, 'ralrimiva', [bd], 'A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) )' % (ZTZ, C0)), 'A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) )' % (ZTZ, C0)),
                               kz], '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) )' % (ZTZ, C0))
    kab = D(w, Ak, 'absidd', [D(w, Ak, 'nnred', [kn], 'k e. RR'), D(w, Ak, 'nn0ge0d', [D(w, Ak, 'nnnn0d', [kn], 'k e. NN0')], '0 <_ k')], '( abs ` k ) = k')
    bdk2 = D(w, Ak, 'breqtrd', [bdk, D(w, Ak, 'oveq2d', [D(w, Ak, 'oveq2d', [kab], '( ( 1 / 2 ) ^ ( abs ` k ) ) = ( ( 1 / 2 ) ^ k )')], '( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) ) = ( %s x. ( ( 1 / 2 ) ^ k ) )' % (C0, C0))],
             '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (ZTZ, C0))
    zqk = D(w, Ak, 'eqeltrrd', [fq(Ak, 'k'), zkc], '( %s ` k ) e. CC' % ZQ)
    bq = D(w, Ak, 'eqbrtrrd', [D(w, Ak, 'fveq2d', [fq(Ak, 'k')], '( abs ` ( %s ` k ) ) = ( abs ` ( %s ` k ) )' % (ZTZ, ZQ)), bdk2], '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (ZQ, C0))
    ms = D(w, A, 'zl3mser', [c0r, cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), cst(w, A, 'halfge0', '0 <_ ( 1 / 2 )'), cst(w, A, 'halflt1', '( 1 / 2 ) < 1'), zqk, bq],
           '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) )' % (ZQ, ZQ, C0))
    An2 = '( %s /\\ n e. NN )' % A
    zqn = D(w, An2, 'eqeltrrd', [fq(An2, 'n'), D(w, An2, 'ffvelcdmd', [ad(w, An2, ztf, '%s : ZZ --> CC' % ZTZ), D(w, An2, 'nnzd', [w.s([], 'simpr', '( %s -> n e. NN )' % An2)], 'n e. ZZ')], '( %s ` n ) e. CC' % ZTZ)],
            '( %s ` n ) e. CC' % ZQ)
    im = D(w, A, 'isummulc2', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), D(w, An2, 'eqidd', [], '( %s ` n ) = ( %s ` n )' % (ZQ, ZQ)), zqn, D(w, A, 'simpld', [ms], 'seq 1 ( + , %s ) e. dom ~~>' % ZQ),
                                cst(w, A, '2cn', '2 e. CC')], '( 2 x. sum_ n e. NN ( %s ` n ) ) = sum_ n e. NN ( 2 x. ( %s ` n ) )' % (ZQ, ZQ))
    CZZ = L.CZ('Z')
    THv = lambda v: '( ( %s ` %s ) x. ( ( %s ^ P ) x. %s ) )' % (CZZ, v, v, EXn(v))
    nn2 = w.s([], 'simpr', '( %s -> n e. NN )' % An2)
    czn = D(w, An2, 'syl', [nn2, w.s([w.s([w.s([], 'fveq2', '( a = n -> ( %s ` a ) = ( %s ` n ) )' % (LMr, LMr))], 'fveq2d', '( a = n -> ( Z ` ( %s ` a ) ) = ( Z ` ( %s ` n ) ) )' % (LMr, LMr)),
                                      eq_(w, CZZ), w.s([], 'fvex', '( Z ` ( %s ` n ) ) e. _V' % LMr)], 'fvmpt', '( n e. NN -> ( %s ` n ) = ( Z ` ( %s ` n ) ) )' % (CZZ, LMr))],
            '( %s ` n ) = ( Z ` ( %s ` n ) )' % (CZZ, LMr))
    qth = D(w, An2, 'eqtr4d', [D(w, An2, 'eqtr3d', [fq(An2, 'n'), ztval(w, An2, 'n', D(w, An2, 'nnzd', [nn2], 'n e. ZZ'))], '( %s ` n ) = %s' % (ZQ, ZTv('n'))),
                               D(w, An2, 'oveq1d', [czn], '%s = ( ( Z ` ( %s ` n ) ) x. ( ( n ^ P ) x. %s ) )' % (THv('n'), LMr, EXn('n')))], '( %s ` n ) = %s' % (ZQ, THv('n')))
    THP_ = L.THP(CZZ, 'X', 'P')
    SUMP_ = 'sum_ n e. NN ( %s + ( %s ` -u n ) )' % (ztn, ZTZ)
    sp = chain(w, A, [SUMP_, 'sum_ n e. NN ( 2 x. %s )' % ztn, 'sum_ n e. NN ( 2 x. ( %s ` n ) )' % ZQ, '( 2 x. sum_ n e. NN ( %s ` n ) )' % ZQ, '( 2 x. %s )' % THP_],
               [s1, D(w, A, 'sumeq2dv', [D(w, An2, 'oveq2d', [fq(An2, 'n')], '( 2 x. %s ) = ( 2 x. ( %s ` n ) )' % (ztn, ZQ))], 'sum_ n e. NN ( 2 x. %s ) = sum_ n e. NN ( 2 x. ( %s ` n ) )' % (ztn, ZQ)),
                ('r', im), D(w, A, 'oveq2d', [D(w, A, 'sumeq2dv', [qth], 'sum_ n e. NN ( %s ` n ) = %s' % (ZQ, THP_))], '( 2 x. sum_ n e. NN ( %s ` n ) ) = ( 2 x. %s )' % (ZQ, THP_))])
    pz = D(w, A, 'oveq12d', [zt0, sp], '%s = ( %s + ( 2 x. %s ) )' % (L.PZF(ZTZ), RM, L.THP(CZZ, 'X', 'P')))
    w.qed([HBZ, pz], 'jca', S['zl3zt'])
    go(w)


# ---------------------------------------------------------------- generic theta-term values
def EXg(n, X):
    return '( exp ` -u ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) )' % (n, X)


def ZTg(Z, n, X, P):
    return '( ( %s ` ( %s ` %s ) ) x. ( ( %s ^ %s ) x. %s ) )' % (Z, LMr, n, n, P, EXg(n, X))


def ztsub_g(w, Z, X, P, v, N):
    """closed: ( v = N -> ZTg(v) = ZTg(N) )"""
    return w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (v, N, LMr, v, LMr, N))], 'fveq2d', '( %s = %s -> ( %s ` ( %s ` %s ) ) = ( %s ` ( %s ` %s ) ) )' % (v, N, Z, LMr, v, Z, LMr, N)),
                w.s([w.s([], 'oveq1', '( %s = %s -> ( %s ^ %s ) = ( %s ^ %s ) )' % (v, N, v, P, N, P)),
                     w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( %s = %s -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (v, N, v, N))], 'oveq2d', '( %s = %s -> ( _pi x. ( %s ^ 2 ) ) = ( _pi x. ( %s ^ 2 ) ) )' % (v, N, v, N))], 'oveq1d',
                                   '( %s = %s -> ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) = ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) )' % (v, N, v, X, N, X))], 'negeqd',
                              '( %s = %s -> -u ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) = -u ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) )' % (v, N, v, X, N, X))], 'fveq2d', '( %s = %s -> %s = %s )' % (v, N, EXg(v, X), EXg(N, X)))],
                    'oveq12d', '( %s = %s -> ( ( %s ^ %s ) x. %s ) = ( ( %s ^ %s ) x. %s ) )' % (v, N, v, P, EXg(v, X), N, P, EXg(N, X)))],
               'oveq12d', '( %s = %s -> %s = %s )' % (v, N, ZTg(Z, v, X, P), ZTg(Z, N, X, P)))


def zt_val(w, A, Z, X, P, N, nz):
    """( A -> ( ZT(Z,X,P) ` N ) = ZTg(Z,N,X,P) ) for N free of n"""
    ZTm = L.ZT(Z, X, P)
    return D(w, A, 'syl', [nz, w.s([ztsub_g(w, Z, X, P, 'n', N), eq_(w, ZTm), w.s([], 'ovex', '%s e. _V' % ZTg(Z, N, X, P))], 'fvmpt',
                                   '( %s e. ZZ -> ( %s ` %s ) = %s )' % (N, ZTm, N, ZTg(Z, N, X, P)))], '( %s ` %s ) = %s' % (ZTm, N, ZTg(Z, N, X, P)))


def par_nn0(w, A, pp, P):
    A0 = '( %s /\\ %s = 0 )' % (A, P); A1 = '( %s /\\ %s = 1 )' % (A, P)
    return w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (A0, P)), cst(w, A0, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (A0, P)),
                w.s([w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, P)), cst(w, A1, '1nn0', '1 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (A1, P)),
                w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( %s = 0 \\/ %s = 1 ) )' % (A, P, P))], 'mpjaodan', '( %s -> %s e. NN0 )' % (A, P))


# ---------------------------------------------------------------- zl3gb
if want('zl3gb'):
    w = W('zl3gb', 'One residue class of the character theta at ` 1 / y ` is a shifted Gaussian theta at ` T = M / y ` , transformed by ~ zl3thg .')
    A, Cc = ante_of('zl3gb')
    PAR = L.ZL3.PAR
    ch = D(w, A, 'simpll', [], L.CH()); yrp = D(w, A, 'simplr', [], 'y e. RR+'); bo = D(w, A, 'simpr', [], 'b e. ( 0 ..^ M )')
    mn = D(w, A, 'simpld', [ch], 'M e. NN'); yd = D(w, A, 'simprd', [ch], 'Y e. %s' % DB)
    par = D(w, A, 'syl', [ch, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pp = D(w, A, 'simplld', [par], '%s e. { 0 , 1 }' % PAR)
    ym1 = D(w, A, 'simprld', [par], '( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (LMr, PAR))
    pn = par_nn0(w, A, pp, PAR)
    X1 = '( 1 / y )'
    x1p = D(w, A, 'rpreccld', [yrp], '%s e. RR+' % X1)
    ZTY1 = L.ZT('Y', X1, PAR)
    C0 = '( exp ` ( 1 / ( _pi x. ( %s / M ) ) ) )' % X1
    zt = D(w, A, 'syl3anc', [ch, D(w, A, 'jca', [pp, ym1], '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, LMr, PAR)), x1p, w.inst('zl3zt')],
            '( %s /\\ %s = ( %s + ( 2 x. %s ) ) )' % (L.HBF(ZTY1, C0), L.PZF(ZTY1), L.ZL3.RM, L.THP(L.CZ('Y'), X1, PAR)))
    hbF = D(w, A, 'simpld', [zt], L.HBF(ZTY1, C0))
    GBY = L.GB(ZTY1); CB = '( %s x. ( 2 ^ M ) )' % C0
    rgb = D(w, A, 'syl', [D(w, A, 'jca', [D(w, A, 'jca', [mn, hbF], '( M e. NN /\\ %s )' % L.HBF(ZTY1, C0)), bo], '( ( M e. NN /\\ %s ) /\\ b e. ( 0 ..^ M ) )' % L.HBF(ZTY1, C0)), w.inst('zl3rgb')],
             L.HBF(GBY, CB))
    gbf = D(w, A, 'simpld', [rgb], '%s : ZZ --> CC' % GBY)
    # facts
    mr = D(w, A, 'nnred', [mn], 'M e. RR'); mc = D(w, A, 'nncnd', [mn], 'M e. CC'); mne = D(w, A, 'nnne0d', [mn], 'M =/= 0'); mz = D(w, A, 'nnzd', [mn], 'M e. ZZ')
    yc = D(w, A, 'rpcnd', [yrp], 'y e. CC'); yne = D(w, A, 'rpne0d', [yrp], 'y =/= 0')
    bz = D(w, A, 'syl', [bo, w.inst('elfzoelz')], 'b e. ZZ'); bc = D(w, A, 'zcnd', [bz], 'b e. CC')
    YB_ = '( Y ` ( %s ` b ) )' % LMr
    ybc = chval(w, A, 'Y', yd, 'b', bz)
    c_ = '( %s x. ( M ^ %s ) )' % (YB_, PAR)
    mpc = D(w, A, 'expcld', [mc, pn], '( M ^ %s ) e. CC' % PAR)
    cc_ = D(w, A, 'mulcld', [ybc, mpc], '%s e. CC' % c_)
    # pointwise at m
    Am = '( %s /\\ m e. ZZ )' % A
    mz_ = w.s([], 'simpr', '( %s -> m e. ZZ )' % Am)
    cl = Closure(w, Am, {'M': [ad(w, Am, mc, 'M e. CC'), ad(w, Am, mne, 'M =/= 0')], 'y': [ad(w, Am, yc, 'y e. CC'), ad(w, Am, yne, 'y =/= 0')], 'b': ad(w, Am, bc, 'b e. CC'),
                         'm': D(w, Am, 'zcnd', [mz_], 'm e. CC'), PAR: ad(w, Am, pn, '%s e. NN0' % PAR), YB_: ad(w, Am, ybc, '%s e. CC' % YB_), '_pi': cst(w, Am, 'picn', '_pi e. CC')})
    cl.atom(PAR); cl.atom(YB_)
    c = lambda e: cl.mem(e, 'CC')
    N = '( b + ( m x. M ) )'; Wv = '( m + ( b / M ) )'
    nz = D(w, Am, 'zaddcld', [ad(w, Am, bz, 'b e. ZZ'), D(w, Am, 'zmulcld', [mz_, ad(w, Am, mz, 'M e. ZZ')], '( m x. M ) e. ZZ')], '%s e. ZZ' % N)
    gv = D(w, Am, 'syl2anc', [mz_, w.s([], 'fvex', '( %s ` %s ) e. _V' % (ZTY1, N)) and cst(w, Am, 'fvex', '( %s ` %s ) e. _V' % (ZTY1, N)), w.s([eq_(w, GBY)], 'fvmpt2', '( ( m e. ZZ /\\ ( %s ` %s ) e. _V ) -> ( %s ` m ) = ( %s ` %s ) )' % (ZTY1, N, GBY, ZTY1, N))],
           '( %s ` m ) = ( %s ` %s )' % (GBY, ZTY1, N))
    zv = zt_val(w, Am, 'Y', X1, PAR, N, nz)
    # Y ( L N ) = Y ( L b )
    dv = D(w, Am, 'breqtrrd', [D(w, Am, 'syl2anc', [mz_, ad(w, Am, mz, 'M e. ZZ'), w.inst('dvdsmul2')], 'M || ( m x. M )'), D(w, Am, 'pncan2d', [c('b'), c('( m x. M )')], '( %s - b ) = ( m x. M )' % N)],
           'M || ( %s - b )' % N)
    lnb = D(w, Am, 'mpbird', [dv, D(w, Am, 'syl3anc', [D(w, Am, 'nnnn0d', [ad(w, Am, mn, 'M e. NN')], 'M e. NN0'), nz, ad(w, Am, bz, 'b e. ZZ'),
                                                     w.s([eq_(w, ZN), eq_(w, LMr)], 'zndvds', '( ( M e. NN0 /\\ %s e. ZZ /\\ b e. ZZ ) -> ( ( %s ` %s ) = ( %s ` b ) <-> M || ( %s - b ) ) )' % (N, LMr, N, LMr, N))],
                                      '( ( %s ` %s ) = ( %s ` b ) <-> M || ( %s - b ) )' % (LMr, N, LMr, N))], '( %s ` %s ) = ( %s ` b )' % (LMr, N, LMr))
    yn = D(w, Am, 'fveq2d', [lnb], '( Y ` ( %s ` %s ) ) = %s' % (LMr, N, YB_))
    # N = M W
    nw = chain(w, Am, ['( M x. %s )' % Wv, '( ( M x. m ) + ( M x. ( b / M ) ) )', '( ( M x. m ) + b )', '( ( m x. M ) + b )', N],
               [D(w, Am, 'adddid', [c('M'), c('m'), c('( b / M )')], '( M x. %s ) = ( ( M x. m ) + ( M x. ( b / M ) ) )' % Wv),
                D(w, Am, 'oveq2d', [D(w, Am, 'divcan2d', [c('b'), c('M'), ad(w, Am, mne, 'M =/= 0')], '( M x. ( b / M ) ) = b')], '( ( M x. m ) + ( M x. ( b / M ) ) ) = ( ( M x. m ) + b )'),
                D(w, Am, 'oveq1d', [D(w, Am, 'mulcomd', [c('M'), c('m')], '( M x. m ) = ( m x. M )')], '( ( M x. m ) + b ) = ( ( m x. M ) + b )'),
                D(w, Am, 'addcomd', [c('( m x. M )'), c('b')], '( ( m x. M ) + b ) = %s' % N)])
    nw_ = D(w, Am, 'eqcomd', [nw], '%s = ( M x. %s )' % (N, Wv))
    pw = D(w, Am, 'eqtrd', [D(w, Am, 'oveq1d', [nw_], '( %s ^ %s ) = ( ( M x. %s ) ^ %s )' % (N, PAR, Wv, PAR)), D(w, Am, 'mulexpd', [c('M'), c(Wv), ad(w, Am, pn, '%s e. NN0' % PAR)], '( ( M x. %s ) ^ %s ) = ( ( M ^ %s ) x. ( %s ^ %s ) )' % (Wv, PAR, PAR, Wv, PAR))],
            '( %s ^ %s ) = ( ( M ^ %s ) x. ( %s ^ %s ) )' % (N, PAR, PAR, Wv, PAR))
    Q = '( %s / M )' % X1; M2 = '( M ^ 2 )'; W2 = '( %s ^ 2 )' % Wv
    n2 = D(w, Am, 'eqtrd', [D(w, Am, 'oveq1d', [nw_], '( %s ^ 2 ) = ( ( M x. %s ) ^ 2 )' % (N, Wv)), D(w, Am, 'sqmuld', [c('M'), c(Wv)], '( ( M x. %s ) ^ 2 ) = ( %s x. %s )' % (Wv, M2, W2))], '( %s ^ 2 ) = ( %s x. %s )' % (N, M2, W2))
    mq = chain(w, Am, ['( %s x. %s )' % (M2, Q), '( ( M x. M ) x. %s )' % Q, '( M x. ( M x. %s ) )' % Q, '( M x. %s )' % X1, '( M / y )'],
               [D(w, Am, 'oveq1d', [D(w, Am, 'sqvald', [c('M')], '%s = ( M x. M )' % M2)], '( %s x. %s ) = ( ( M x. M ) x. %s )' % (M2, Q, Q)),
                D(w, Am, 'mulassd', [c('M'), c('M'), c(Q)], '( ( M x. M ) x. %s ) = ( M x. ( M x. %s ) )' % (Q, Q)),
                D(w, Am, 'oveq2d', [D(w, Am, 'divcan2d', [c(X1), c('M'), ad(w, Am, mne, 'M =/= 0')], '( M x. %s ) = %s' % (Q, X1))], '( M x. ( M x. %s ) ) = ( M x. %s )' % (Q, X1)),
                ('r', D(w, Am, 'divrecd', [c('M'), c('y'), ad(w, Am, yne, 'y =/= 0')], '( M / y ) = ( M x. %s )' % X1))])
    ex = chain(w, Am, ['( ( _pi x. ( %s ^ 2 ) ) x. %s )' % (N, Q), '( ( _pi x. ( %s x. %s ) ) x. %s )' % (M2, W2, Q), '( ( ( _pi x. %s ) x. %s ) x. %s )' % (M2, W2, Q),
                       '( ( ( _pi x. %s ) x. %s ) x. %s )' % (M2, Q, W2), '( ( _pi x. ( %s x. %s ) ) x. %s )' % (M2, Q, W2), '( ( _pi x. ( M / y ) ) x. %s )' % W2],
               [D(w, Am, 'oveq1d', [D(w, Am, 'oveq2d', [n2], '( _pi x. ( %s ^ 2 ) ) = ( _pi x. ( %s x. %s ) )' % (N, M2, W2))], '( ( _pi x. ( %s ^ 2 ) ) x. %s ) = ( ( _pi x. ( %s x. %s ) ) x. %s )' % (N, Q, M2, W2, Q)),
                ('r', D(w, Am, 'oveq1d', [D(w, Am, 'mulassd', [c('_pi'), c(M2), c(W2)], '( ( _pi x. %s ) x. %s ) = ( _pi x. ( %s x. %s ) )' % (M2, W2, M2, W2))],
                         '( ( ( _pi x. %s ) x. %s ) x. %s ) = ( ( _pi x. ( %s x. %s ) ) x. %s )' % (M2, W2, Q, M2, W2, Q))),
                D(w, Am, 'mul32d', [c('( _pi x. %s )' % M2), c(W2), c(Q)], '( ( ( _pi x. %s ) x. %s ) x. %s ) = ( ( ( _pi x. %s ) x. %s ) x. %s )' % (M2, W2, Q, M2, Q, W2)),
                D(w, Am, 'oveq1d', [D(w, Am, 'mulassd', [c('_pi'), c(M2), c(Q)], '( ( _pi x. %s ) x. %s ) = ( _pi x. ( %s x. %s ) )' % (M2, Q, M2, Q))],
                  '( ( ( _pi x. %s ) x. %s ) x. %s ) = ( ( _pi x. ( %s x. %s ) ) x. %s )' % (M2, Q, W2, M2, Q, W2)),
                D(w, Am, 'oveq1d', [D(w, Am, 'oveq2d', [mq], '( _pi x. ( %s x. %s ) ) = ( _pi x. ( M / y ) )' % (M2, Q))], '( ( _pi x. ( %s x. %s ) ) x. %s ) = ( ( _pi x. ( M / y ) ) x. %s )' % (M2, Q, W2, W2))])
    EG = '( exp ` -u ( ( _pi x. ( M / y ) ) x. %s ) )' % W2
    eg = D(w, Am, 'fveq2d', [D(w, Am, 'negeqd', [ex], '-u ( ( _pi x. ( %s ^ 2 ) ) x. %s ) = -u ( ( _pi x. ( M / y ) ) x. %s )' % (N, Q, W2))], '%s = %s' % (EXg(N, X1), EG))
    WA = '( %s ^ %s )' % (Wv, PAR); MA = '( M ^ %s )' % PAR
    tv = chain(w, Am, [ZTg('Y', N, X1, PAR), '( %s x. ( ( %s x. %s ) x. %s ) )' % (YB_, MA, WA, EG), '( %s x. ( %s x. ( %s x. %s ) ) )' % (YB_, MA, WA, EG), '( %s x. ( %s x. %s ) )' % (c_, WA, EG)],
               [D(w, Am, 'oveq12d', [yn, D(w, Am, 'oveq12d', [pw, eg], '( ( %s ^ %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (N, PAR, EXg(N, X1), MA, WA, EG))],
                  '%s = ( %s x. ( ( %s x. %s ) x. %s ) )' % (ZTg('Y', N, X1, PAR), YB_, MA, WA, EG)),
                D(w, Am, 'oveq2d', [D(w, Am, 'mulassd', [c(MA), c(WA), c(EG)], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (MA, WA, EG, MA, WA, EG))],
                  '( %s x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (YB_, MA, WA, EG, YB_, MA, WA, EG)),
                ('r', D(w, Am, 'mulassd', [c(YB_), c(MA), c('( %s x. %s )' % (WA, EG))], '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (c_, WA, EG, YB_, MA, WA, EG)))])
    GLv = '( %s x. %s )' % (WA, EG)
    glsub = w.s([w.s([w.s([], 'oveq1', '( x = m -> ( x + ( b / M ) ) = %s )' % Wv)], 'oveq1d', '( x = m -> ( ( x + ( b / M ) ) ^ %s ) = %s )' % (PAR, WA)),
                      w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( x = m -> ( x + ( b / M ) ) = %s )' % Wv)], 'oveq1d', '( x = m -> ( ( x + ( b / M ) ) ^ 2 ) = %s )' % W2)], 'oveq2d',
                                    '( x = m -> ( ( _pi x. ( M / y ) ) x. ( ( x + ( b / M ) ) ^ 2 ) ) = ( ( _pi x. ( M / y ) ) x. %s ) )' % W2)], 'negeqd',
                               '( x = m -> -u ( ( _pi x. ( M / y ) ) x. ( ( x + ( b / M ) ) ^ 2 ) ) = -u ( ( _pi x. ( M / y ) ) x. %s ) )' % W2)], 'fveq2d',
                          '( x = m -> ( exp ` -u ( ( _pi x. ( M / y ) ) x. ( ( x + ( b / M ) ) ^ 2 ) ) ) = %s )' % EG)], 'oveq12d',
                     '( x = m -> ( ( ( x + ( b / M ) ) ^ %s ) x. ( exp ` -u ( ( _pi x. ( M / y ) ) x. ( ( x + ( b / M ) ) ^ 2 ) ) ) ) = %s )' % (PAR, GLv))
    glv = D(w, Am, 'syl', [mz_, w.s([glsub, eq_(w, L.GLB), w.s([], 'ovex', '%s e. _V' % GLv)], 'fvmpt', '( m e. ZZ -> ( %s ` m ) = %s )' % (L.GLB, GLv))], '( %s ` m ) = %s' % (L.GLB, GLv))
    gcl = D(w, Am, 'eqeltrd', [glv, c(GLv)], '( %s ` m ) e. CC' % L.GLB)
    gm = chain(w, Am, ['( %s ` m )' % GBY, '( %s ` %s )' % (ZTY1, N), ZTg('Y', N, X1, PAR), '( %s x. %s )' % (c_, GLv), '( %s x. ( %s ` m ) )' % (c_, L.GLB)],
               [gv, zv, tv, ('r', D(w, Am, 'oveq2d', [glv], '( %s x. ( %s ` m ) ) = ( %s x. %s )' % (c_, L.GLB, c_, GLv)))])
    ZTYq = '( r e. ZZ |-> %s )' % ZTg('Y', 'r', X1, PAR)
    ztq = w.s([ztsub_g(w, 'Y', X1, PAR, 'n', 'r')], 'cbvmptv', '%s = %s' % (ZTY1, ZTYq))
    GQ = '( p e. ZZ |-> ( %s ` ( b + ( p x. M ) ) ) )' % ZTYq
    s_a = w.s([w.s([w.s([], 'oveq1', '( m = p -> ( m x. M ) = ( p x. M ) )')], 'oveq2d', '( m = p -> ( b + ( m x. M ) ) = ( b + ( p x. M ) ) )')], 'fveq2d',
              '( m = p -> ( %s ` ( b + ( m x. M ) ) ) = ( %s ` ( b + ( p x. M ) ) ) )' % (ZTY1, ZTY1))
    s_b = w.s([ztq], 'fveq1i', '( %s ` ( b + ( p x. M ) ) ) = ( %s ` ( b + ( p x. M ) ) )' % (ZTY1, ZTYq))
    cbq = w.s([w.s([s_a, s_b], 'eqtrdi', '( m = p -> ( %s ` ( b + ( m x. M ) ) ) = ( %s ` ( b + ( p x. M ) ) ) )' % (ZTY1, ZTYq))], 'cbvmptv', '%s = %s' % (GBY, GQ))
    cbqA = w.s([cbq], 'a1i', '( %s -> %s = %s )' % (A, GBY, GQ))
    hbc, hbq_ = w.wcongr(L.HBF(GBY, CB), {}, A, {}, rules={GBY: (GQ, cbqA)})
    hbq = D(w, A, 'mpbid', [rgb, hbc], L.HBF(GQ, CB))
    pzt = D(w, A, 'syl', [hbq, w.inst('zl3pzt')], L.split_imp(S['zl3pzt'])[1].replace('( F `', '( %s `' % GQ).replace('( 2 x. C )', '( 2 x. %s )' % CB))
    cvq = D(w, A, 'simpld', [pzt], 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(GQ, 'n'))
    pzq, _ = w.rewrite(L.PZF(GBY), {GBY: (GQ, cbqA)}, A)
    cvqm = seqcv_rename(w, A, GQ, cvq, 'n', 'm')
    gqf = D(w, A, 'simpld', [hbq], '%s : ZZ --> CC' % GQ)
    pzqc = pz_cl(w, A, GQ, gqf, cvq)
    # the Gaussian transformation
    MY = '( M / y )'; BM = '( b / M )'
    thg = D(w, A, 'syl3anc', [D(w, A, 'rpdivcld', [D(w, A, 'nnrpd', [mn], 'M e. RR+'), yrp], '%s e. RR+' % MY), D(w, A, 'redivcld', [D(w, A, 'zred', [bz], 'b e. RR'), mr, mne], '%s e. RR' % BM), pp, w.inst('zl3thg')],
            '%s = %s' % (L.PZF(L.GLB), L.THGR))
    THGR = L.THGR
    # T ^c and ( -u _i ) ^ a in CC, PZ ( GRB ) in CC
    grc = D(w, A, 'syl3anc', [D(w, A, 'rpdivcld', [D(w, A, 'nnrpd', [mn], 'M e. RR+'), yrp], '%s e. RR+' % MY), D(w, A, 'redivcld', [D(w, A, 'zred', [bz], 'b e. RR'), mr, mne], '%s e. RR' % BM), pp, w.inst('zl3grc')],
            'seq 1 ( + , %s ) e. dom ~~>' % pairmap(L.GRB, 'm'))
    Ak_ = '( %s /\\ k e. ZZ )' % A
    kz_ = w.s([], 'simpr', '( %s -> k e. ZZ )' % Ak_)
    clk = Closure(w, Ak_, {'M': [ad(w, Ak_, mc, 'M e. CC'), ad(w, Ak_, mne, 'M =/= 0')], 'y': [ad(w, Ak_, yc, 'y e. CC'), ad(w, Ak_, yne, 'y =/= 0')], 'b': ad(w, Ak_, bc, 'b e. CC'),
                           'k': D(w, Ak_, 'zcnd', [kz_], 'k e. CC'), PAR: ad(w, Ak_, pn, '%s e. NN0' % PAR), '_pi': cst(w, Ak_, 'picn', '_pi e. CC'), '_i': cst(w, Ak_, 'ax-icn', '_i e. CC'),
                           MY: [D(w, Ak_, 'divcld', [ad(w, Ak_, mc, 'M e. CC'), ad(w, Ak_, yc, 'y e. CC'), ad(w, Ak_, yne, 'y =/= 0')], '%s e. CC' % MY),
                                D(w, Ak_, 'divne0d', [ad(w, Ak_, mc, 'M e. CC'), ad(w, Ak_, yc, 'y e. CC'), ad(w, Ak_, mne, 'M =/= 0'), ad(w, Ak_, yne, 'y =/= 0')], '%s =/= 0' % MY)]})
    clk.atom(MY)
    clk.atom(PAR)
    GRv = '( ( k ^ %s ) x. ( ( exp ` -u ( _pi x. ( ( k ^ 2 ) / %s ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( k x. %s ) ) ) ) )' % (PAR, MY, BM)
    grf = D(w, A, 'fmptd', [clk.mem(GRv, 'CC'), eq_(w, L.GRB)], '%s : ZZ --> CC' % L.GRB)
    pzrc = pz_cl(w, A, L.GRB, grf, seqcv_rename(w, A, L.GRB, grc, 'm', 'n'))
    clA = Closure(w, A, {'M': [mc, mne], 'y': [yc, yne], PAR: pn, '_i': cst(w, A, 'ax-icn', '_i e. CC'), L.PZF(L.GRB): pzrc})
    clA.atom(PAR); clA.atom(L.PZF(L.GRB))
    tgc = D(w, A, 'mulcld', [D(w, A, 'expcld', [D(w, A, 'negcld', [cst(w, A, 'ax-icn', '_i e. CC')], '-u _i e. CC'), pn], '( -u _i ^ %s ) e. CC' % PAR),
                             D(w, A, 'mulcld', [D(w, A, 'cxpcld', [D(w, A, 'divcld', [mc, yc, yne], '%s e. CC' % MY), D(w, A, 'negcld', [D(w, A, 'addcld', [cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), D(w, A, 'nn0cnd', [pn], '%s e. CC' % PAR)],
                                                                                                                                       '( ( 1 / 2 ) + %s ) e. CC' % PAR)], '-u ( ( 1 / 2 ) + %s ) e. CC' % PAR)],
                                                                 '( %s ^c -u ( ( 1 / 2 ) + %s ) ) e. CC' % (MY, PAR)), pzrc], '( ( %s ^c -u ( ( 1 / 2 ) + %s ) ) x. %s ) e. CC' % (MY, PAR, L.PZF(L.GRB)))],
              '%s e. CC' % THGR)
    GOAL = '%s = ( %s x. %s )' % (L.PZF(GBY), c_, THGR)
    # case Y ( L b ) =/= 0
    Ane = '( %s /\\ %s =/= 0 )' % (A, YB_)
    ne_ = w.s([], 'simpr', '( %s -> %s =/= 0 )' % (Ane, YB_))
    cne = D(w, Ane, 'mulne0d', [ad(w, Ane, ybc, '%s e. CC' % YB_), ne_, ad(w, Ane, mpc, '( M ^ %s ) e. CC' % PAR), D(w, Ane, 'expne0d', [ad(w, Ane, mc, 'M e. CC'), ad(w, Ane, mne, 'M =/= 0'), D(w, Ane, 'nn0zd', [ad(w, Ane, pn, '%s e. NN0' % PAR)], '%s e. ZZ' % PAR)], '( M ^ %s ) =/= 0' % PAR)],
            '%s =/= 0' % c_)
    ccn = ad(w, Ane, cc_, '%s e. CC' % c_)
    IC = '( 1 / %s )' % c_
    icc = D(w, Ane, 'reccld', [ccn, cne], '%s e. CC' % IC)
    Anm = '( %s /\\ m e. ZZ )' % Ane
    toAm = D(w, Anm, 'jca', [D(w, Anm, 'simpll', [], A), w.s([], 'simpr', '( %s -> m e. ZZ )' % Anm)], Am)
    lift = lambda st, f: D(w, Anm, 'syl', [toAm, st], f)
    gm_ = lift(gm, '( %s ` m ) = ( %s x. ( %s ` m ) )' % (GBY, c_, L.GLB))
    gcl_ = lift(gcl, '( %s ` m ) e. CC' % L.GLB)
    fqm = w.s([w.s([cbq], 'fveq1i', '( %s ` m ) = ( %s ` m )' % (GBY, GQ))], 'a1i', '( %s -> ( %s ` m ) = ( %s ` m ) )' % (Anm, GBY, GQ))
    gqm = D(w, Anm, 'eqtr3d', [fqm, gm_], '( %s ` m ) = ( %s x. ( %s ` m ) )' % (GQ, c_, L.GLB))
    icA = ad(w, Anm, icc, '%s e. CC' % IC); ccA = ad(w, Anm, ccn, '%s e. CC' % c_); cneA = ad(w, Anm, cne, '%s =/= 0' % c_)
    gl1 = chain(w, Anm, ['( %s x. ( %s ` m ) )' % (IC, GQ), '( %s x. ( %s x. ( %s ` m ) ) )' % (IC, c_, L.GLB), '( ( %s x. %s ) x. ( %s ` m ) )' % (IC, c_, L.GLB), '( 1 x. ( %s ` m ) )' % L.GLB, '( %s ` m )' % L.GLB],
                [D(w, Anm, 'oveq2d', [gqm], '( %s x. ( %s ` m ) ) = ( %s x. ( %s x. ( %s ` m ) ) )' % (IC, GQ, IC, c_, L.GLB)),
                 ('r', D(w, Anm, 'mulassd', [icA, ccA, gcl_], '( ( %s x. %s ) x. ( %s ` m ) ) = ( %s x. ( %s x. ( %s ` m ) ) )' % (IC, c_, L.GLB, IC, c_, L.GLB))),
                 D(w, Anm, 'oveq1d', [D(w, Anm, 'recid2d', [ccA, cneA], '( %s x. %s ) = 1' % (IC, c_))], '( ( %s x. %s ) x. ( %s ` m ) ) = ( 1 x. ( %s ` m ) )' % (IC, c_, L.GLB, L.GLB)),
                 D(w, Anm, 'mullidd', [gcl_], '( 1 x. ( %s ` m ) ) = ( %s ` m )' % (L.GLB, L.GLB))])
    gqc = D(w, Anm, 'eqeltrd', [gqm, D(w, Anm, 'mulcld', [ccA, gcl_], '( %s x. ( %s ` m ) ) e. CC' % (c_, L.GLB))], '( %s ` m ) e. CC' % GQ)
    ALLM = 'A. m e. ZZ ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) )' % (GQ, L.GLB, IC, GQ)
    alm = D(w, Ane, 'ralrimiva', [D(w, Anm, 'jca', [gqc, D(w, Anm, 'eqcomd', [gl1], '( %s ` m ) = ( %s x. ( %s ` m ) )' % (L.GLB, IC, GQ))], '( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) )' % (GQ, L.GLB, IC, GQ))], ALLM)
    zex = w.s([w.s([], 'zex', 'ZZ e. _V')], 'mptex', '%s e. _V' % L.GLB); zexq = w.s([w.s([], 'zex', 'ZZ e. _V')], 'mptex', '%s e. _V' % GQ)
    pzm = D(w, Ane, 'syl2anc', [D(w, Ane, '3jca', [icc, cst(w, Ane, 'idi', '') if False else w.s([zex], 'a1i', '( %s -> %s e. _V )' % (Ane, L.GLB)), w.s([zexq], 'a1i', '( %s -> %s e. _V )' % (Ane, GQ))],
                                                   '( %s e. CC /\\ %s e. _V /\\ %s e. _V )' % (IC, L.GLB, GQ)),
                                 D(w, Ane, 'jca', [alm, ad(w, Ane, cvqm, 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(GQ, 'm'))], '( %s /\\ seq 1 ( + , %s ) e. dom ~~> )' % (ALLM, pairmap(GQ, 'm'))),
                                 w.inst('zl3pzm')], '%s = ( %s x. %s )' % (L.PZF(L.GLB), IC, L.PZF(GQ)))
    PQ = L.PZF(GQ)
    pqc = ad(w, Ane, pzqc, '%s e. CC' % PQ)
    back = chain(w, Ane, ['( %s x. %s )' % (c_, L.PZF(L.GLB)), '( %s x. ( %s x. %s ) )' % (c_, IC, PQ), '( ( %s x. %s ) x. %s )' % (c_, IC, PQ), '( 1 x. %s )' % PQ, PQ],
                 [D(w, Ane, 'oveq2d', [pzm], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (c_, L.PZF(L.GLB), c_, IC, PQ)),
                  ('r', D(w, Ane, 'mulassd', [ccn, icc, pqc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (c_, IC, PQ, c_, IC, PQ))),
                  D(w, Ane, 'oveq1d', [D(w, Ane, 'recidd', [ccn, cne], '( %s x. %s ) = 1' % (c_, IC))], '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (c_, IC, PQ, PQ)),
                  D(w, Ane, 'mullidd', [pqc], '( 1 x. %s ) = %s' % (PQ, PQ))])
    caseN = chain(w, Ane, [L.PZF(GBY), PQ, '( %s x. %s )' % (c_, L.PZF(L.GLB)), '( %s x. %s )' % (c_, THGR)],
                  [ad(w, Ane, pzq, '%s = %s' % (L.PZF(GBY), PQ)), ('r', back), D(w, Ane, 'oveq2d', [ad(w, Ane, thg, '%s = %s' % (L.PZF(L.GLB), THGR))], '( %s x. %s ) = ( %s x. %s )' % (c_, L.PZF(L.GLB), c_, THGR))])
    # case Y ( L b ) = 0
    Aeq = '( %s /\\ %s = 0 )' % (A, YB_)
    e0_ = w.s([], 'simpr', '( %s -> %s = 0 )' % (Aeq, YB_))
    c0_ = D(w, Aeq, 'eqtrd', [D(w, Aeq, 'oveq1d', [e0_], '%s = ( 0 x. ( M ^ %s ) )' % (c_, PAR)), D(w, Aeq, 'mul02d', [ad(w, Aeq, mpc, '( M ^ %s ) e. CC' % PAR)], '( 0 x. ( M ^ %s ) ) = 0' % PAR)], '%s = 0' % c_)
    Aem = '( %s /\\ m e. ZZ )' % Aeq
    toAm2 = D(w, Aem, 'jca', [D(w, Aem, 'simpll', [], A), w.s([], 'simpr', '( %s -> m e. ZZ )' % Aem)], Am)
    gz = D(w, Aem, 'eqtrd', [D(w, Aem, 'syl', [toAm2, gm], '( %s ` m ) = ( %s x. ( %s ` m ) )' % (GBY, c_, L.GLB)),
                             D(w, Aem, 'eqtrd', [D(w, Aem, 'oveq1d', [ad(w, Aem, c0_, '%s = 0' % c_)], '( %s x. ( %s ` m ) ) = ( 0 x. ( %s ` m ) )' % (c_, L.GLB, L.GLB)),
                                                 D(w, Aem, 'mul02d', [D(w, Aem, 'syl', [toAm2, gcl], '( %s ` m ) e. CC' % L.GLB)], '( 0 x. ( %s ` m ) ) = 0' % L.GLB)], '( %s x. ( %s ` m ) ) = 0' % (c_, L.GLB))],
            '( %s ` m ) = 0' % GBY)
    gzq = D(w, Aem, 'eqtr3d', [w.s([w.s([cbq], 'fveq1i', '( %s ` m ) = ( %s ` m )' % (GBY, GQ))], 'a1i', '( %s -> ( %s ` m ) = ( %s ` m ) )' % (Aem, GBY, GQ)), gz], '( %s ` m ) = 0' % GQ)
    gzall = D(w, Aeq, 'ralrimiva', [gzq], 'A. m e. ZZ ( %s ` m ) = 0' % GQ)
    def gat(A2, X, xz):
        return D(w, A2, 'rspcdva', [w.s([w.s([], 'fveq2', '( m = %s -> ( %s ` m ) = ( %s ` %s ) )' % (X, GQ, GQ, X))], 'eqeq1d', '( m = %s -> ( ( %s ` m ) = 0 <-> ( %s ` %s ) = 0 ) )' % (X, GQ, GQ, X)),
                                     ad(w, A2, gzall, 'A. m e. ZZ ( %s ` m ) = 0' % GQ) if A2 != Aeq else gzall, xz], '( %s ` %s ) = 0' % (GQ, X))
    Aen = '( %s /\\ n e. NN )' % Aeq
    nzz = D(w, Aen, 'nnzd', [w.s([], 'simpr', '( %s -> n e. NN )' % Aen)], 'n e. ZZ')
    pr0 = D(w, Aen, 'eqtrd', [D(w, Aen, 'oveq12d', [gat(Aen, 'n', nzz), gat(Aen, '-u n', D(w, Aen, 'znegcld', [nzz], '-u n e. ZZ'))], '( ( %s ` n ) + ( %s ` -u n ) ) = ( 0 + 0 )' % (GQ, GQ)),
                              cst(w, Aen, '00id', '( 0 + 0 ) = 0')], '( ( %s ` n ) + ( %s ` -u n ) ) = 0' % (GQ, GQ))
    snn = D(w, Aeq, 'eqtrd', [D(w, Aeq, 'sumeq2dv', [pr0], 'sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = sum_ n e. NN 0' % (GQ, GQ)),
                              w.s([w.s([w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqimssi', 'NN C_ ( ZZ>= ` 1 )')], 'orci', '( NN C_ ( ZZ>= ` 1 ) \\/ NN e. Fin )'), w.inst('sumz')], 'ax-mp', 'sum_ n e. NN 0 = 0')],
                                  'a1i', '( %s -> sum_ n e. NN 0 = 0 )' % Aeq)], 'sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = 0' % (GQ, GQ))
    pz0q = D(w, Aeq, 'eqtrd', [D(w, Aeq, 'oveq12d', [gat(Aeq, '0', cst(w, Aeq, '0z', '0 e. ZZ')), snn], '%s = ( 0 + 0 )' % L.PZF(GQ)), cst(w, Aeq, '00id', '( 0 + 0 ) = 0')], '%s = 0' % L.PZF(GQ))
    pz0 = D(w, Aeq, 'eqtrd', [ad(w, Aeq, pzq, '%s = %s' % (L.PZF(GBY), L.PZF(GQ))), pz0q], '%s = 0' % L.PZF(GBY))
    rz = D(w, Aeq, 'eqtrd', [D(w, Aeq, 'oveq1d', [c0_], '( %s x. %s ) = ( 0 x. %s )' % (c_, THGR, THGR)), D(w, Aeq, 'mul02d', [ad(w, Aeq, tgc, '%s e. CC' % THGR)], '( 0 x. %s ) = 0' % THGR)], '( %s x. %s ) = 0' % (c_, THGR))
    caseE = D(w, Aeq, 'eqtr4d', [pz0, rz], GOAL)
    w.qed([D(w, A, 'ex', [caseE], '( %s = 0 -> %s )' % (YB_, GOAL)), D(w, A, 'ex', [caseN], '( %s =/= 0 -> %s )' % (YB_, GOAL))], 'pm2.61dne', S['zl3gb'])
    go(w)


# ---------------------------------------------------------------- zl3gs
if want('zl3gs'):
    w = W('zl3gs', 'The Gauss-sum step: summing the dual Gaussian terms against the character over the residues gives ` tau ( Y ) ` times the theta term of the inverse character ( ~ dchrgsshiftp ).')
    A, Cc = ante_of('zl3gs')
    PAR = L.ZL3.PAR; YB = L.ZL3.YB
    pr = D(w, A, 'simp1', [], L.PR); yrp = D(w, A, 'simp2', [], 'y e. RR+'); kz = D(w, A, 'simp3', [], 'k e. ZZ')
    ch = D(w, A, 'simpld', [pr], L.CH()); mn = D(w, A, 'simpld', [ch], 'M e. NN'); yd = D(w, A, 'simprd', [ch], 'Y e. %s' % DB)
    cond = D(w, A, 'simprd', [pr], '( M DChrCond Y ) = M')
    par = D(w, A, 'syl', [ch, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pn = par_nn0(w, A, D(w, A, 'simplld', [par], '%s e. { 0 , 1 }' % PAR), PAR)
    mc = D(w, A, 'nncnd', [mn], 'M e. CC'); mne = D(w, A, 'nnne0d', [mn], 'M =/= 0'); yc = D(w, A, 'rpcnd', [yrp], 'y e. CC'); yne = D(w, A, 'rpne0d', [yrp], 'y =/= 0')
    kc = D(w, A, 'zcnd', [kz], 'k e. CC')
    MY = '( M / y )'
    cl = Closure(w, A, {'M': [mc, mne], 'y': [yc, yne], 'k': kc, PAR: pn, '_pi': cst(w, A, 'picn', '_pi e. CC'), '_i': cst(w, A, 'ax-icn', '_i e. CC'),
                        MY: [D(w, A, 'divcld', [mc, yc, yne], '%s e. CC' % MY), D(w, A, 'divne0d', [mc, yc, mne, yne], '%s =/= 0' % MY)]})
    cl.atom(PAR); cl.atom(MY)
    c = lambda e: cl.mem(e, 'CC')
    KP = '( k ^ %s )' % PAR
    E1 = '( exp ` -u ( _pi x. ( ( k ^ 2 ) / %s ) ) )' % MY
    E2 = lambda b: '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( k x. ( %s / M ) ) ) )' % b
    GRk = '( %s x. ( %s x. %s ) )' % (KP, E1, E2('b'))
    Ab = '( %s /\\ b e. ( 0 ..^ M ) )' % A
    bz = w.s([w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Ab), w.inst('elfzoelz')], 'syl', '( %s -> b e. ZZ )' % Ab)
    clb = Closure(w, Ab, {'b': D(w, Ab, 'zcnd', [bz], 'b e. CC')}, parent=None)
    def cb(e):
        try:
            return cl.mem(e, 'CC') and ad(w, Ab, cl.mem(e, 'CC'), '%s e. CC' % e)
        except Exception:
            raise
    Xb = '( Y ` ( %s ` b ) )' % LMr
    xbc = chval(w, Ab, 'Y', ad(w, Ab, yd, 'Y e. %s' % DB), 'b', bz)
    kpc = ad(w, Ab, c(KP), '%s e. CC' % KP); e1c = ad(w, Ab, c(E1), '%s e. CC' % E1)
    bmc = D(w, Ab, 'divcld', [D(w, Ab, 'zcnd', [bz], 'b e. CC'), ad(w, Ab, mc, 'M e. CC'), ad(w, Ab, mne, 'M =/= 0')], '( b / M ) e. CC')
    e2c = D(w, Ab, 'efcld', [D(w, Ab, 'mulcld', [ad(w, Ab, c('( 2 x. ( _i x. _pi ) )'), '( 2 x. ( _i x. _pi ) ) e. CC'), D(w, Ab, 'mulcld', [ad(w, Ab, kc, 'k e. CC'), bmc], '( k x. ( b / M ) ) e. CC')],
                                                  '( ( 2 x. ( _i x. _pi ) ) x. ( k x. ( b / M ) ) ) e. CC')], '%s e. CC' % E2('b'))
    grsub = w.s([w.s([], 'id', '( k = k -> k = k )')], 'idi', '') if False else None
    grv = D(w, Ab, 'syl2anc', [ad(w, Ab, kz, 'k e. ZZ'), D(w, Ab, 'elexd', [D(w, Ab, 'mulcld', [kpc, D(w, Ab, 'mulcld', [e1c, e2c], '( %s x. %s ) e. CC' % (E1, E2('b')))], '%s e. CC' % GRk)], '%s e. _V' % GRk),
                               w.s([eq_(w, L.GRB)], 'fvmpt2', '( ( k e. ZZ /\\ %s e. _V ) -> ( %s ` k ) = %s )' % (GRk, L.GRB, GRk))], '( %s ` k ) = %s' % (L.GRB, GRk))
    PE = '( %s x. %s )' % (KP, E1)
    re_ = chain(w, Ab, ['( %s x. ( %s ` k ) )' % (Xb, L.GRB), '( %s x. %s )' % (Xb, GRk), '( %s x. ( %s x. %s ) )' % (Xb, PE, E2('b')), '( %s x. ( %s x. %s ) )' % (PE, Xb, E2('b'))],
                [D(w, Ab, 'oveq2d', [grv], '( %s x. ( %s ` k ) ) = ( %s x. %s )' % (Xb, L.GRB, Xb, GRk)),
                 D(w, Ab, 'oveq2d', [D(w, Ab, 'eqcomd', [D(w, Ab, 'mulassd', [kpc, e1c, e2c], '( %s x. %s ) = %s' % (PE, E2('b'), GRk))], '%s = ( %s x. %s )' % (GRk, PE, E2('b')))],
                   '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (Xb, GRk, Xb, PE, E2('b'))),
                 D(w, Ab, 'mul12d', [xbc, D(w, Ab, 'mulcld', [kpc, e1c], '%s e. CC' % PE), e2c], '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (Xb, PE, E2('b'), PE, Xb, E2('b')))])
    ofi = cst(w, A, 'fzofi', '( 0 ..^ M ) e. Fin')
    s1 = D(w, A, 'sumeq2dv', [re_], 'sum_ b e. ( 0 ..^ M ) ( %s x. ( %s ` k ) ) = sum_ b e. ( 0 ..^ M ) ( %s x. ( %s x. %s ) )' % (Xb, L.GRB, PE, Xb, E2('b')))
    xe = D(w, Ab, 'mulcld', [xbc, e2c], '( %s x. %s ) e. CC' % (Xb, E2('b')))
    s2 = D(w, A, 'fsummulc2', [ofi, c(PE), xe], '( %s x. sum_ b e. ( 0 ..^ M ) ( %s x. %s ) ) = sum_ b e. ( 0 ..^ M ) ( %s x. ( %s x. %s ) )' % (PE, Xb, E2('b'), PE, Xb, E2('b')))
    # the Gauss sum
    E3 = lambda b: '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( ( k x. %s ) / M ) ) )' % b
    e23 = D(w, Ab, 'oveq2d', [D(w, Ab, 'fveq2d', [D(w, Ab, 'oveq2d', [D(w, Ab, 'eqcomd', [D(w, Ab, 'divassd', [ad(w, Ab, kc, 'k e. CC'), D(w, Ab, 'zcnd', [bz], 'b e. CC'), ad(w, Ab, mc, 'M e. CC'), ad(w, Ab, mne, 'M =/= 0')],
                                                                                                   '( ( k x. b ) / M ) = ( k x. ( b / M ) )')], '( k x. ( b / M ) ) = ( ( k x. b ) / M )')],
                                                                          '( ( 2 x. ( _i x. _pi ) ) x. ( k x. ( b / M ) ) ) = ( ( 2 x. ( _i x. _pi ) ) x. ( ( k x. b ) / M ) )')], '%s = %s' % (E2('b'), E3('b')))],
              '( %s x. %s ) = ( %s x. %s )' % (Xb, E2('b'), Xb, E3('b')))
    s3 = D(w, A, 'sumeq2dv', [e23], 'sum_ b e. ( 0 ..^ M ) ( %s x. %s ) = sum_ b e. ( 0 ..^ M ) ( %s x. %s )' % (Xb, E2('b'), Xb, E3('b')))
    Xa = '( Y ` ( %s ` a ) )' % LMr
    ca1 = w.s([w.s([], 'fveq2', '( b = a -> ( %s ` b ) = ( %s ` a ) )' % (LMr, LMr))], 'fveq2d', '( b = a -> %s = %s )' % (Xb, Xa))
    ca2 = w.s([w.s([w.s([w.s([], 'oveq2', '( b = a -> ( k x. b ) = ( k x. a ) )')], 'oveq1d', '( b = a -> ( ( k x. b ) / M ) = ( ( k x. a ) / M ) )')], 'oveq2d',
                   '( b = a -> ( ( 2 x. ( _i x. _pi ) ) x. ( ( k x. b ) / M ) ) = ( ( 2 x. ( _i x. _pi ) ) x. ( ( k x. a ) / M ) ) )')], 'fveq2d', '( b = a -> %s = %s )' % (E3('b'), E3('a')))
    ca3 = w.s([ca1, ca2], 'oveq12d', '( b = a -> ( %s x. %s ) = ( %s x. %s ) )' % (Xb, E3('b'), Xa, E3('a')))
    cba = w.s([ca3], 'cbvsumv', 'sum_ b e. ( 0 ..^ M ) ( %s x. %s ) = sum_ a e. ( 0 ..^ M ) ( %s x. %s )' % (Xb, E3('b'), Xa, E3('a')))
    TAU = '( M DChrGS Y )'
    YBk = '( %s ` ( %s ` k ) )' % (YB, LMr)
    gs = D(w, A, 'syl3anc', [ch, cond, kz, w.inst('dchrgsshiftp')], 'sum_ a e. ( 0 ..^ M ) ( %s x. %s ) = ( %s x. %s )' % (Xa, E3('a'), YBk, TAU))
    gsum = chain(w, A, ['sum_ b e. ( 0 ..^ M ) ( %s x. %s )' % (Xb, E2('b')), 'sum_ b e. ( 0 ..^ M ) ( %s x. %s )' % (Xb, E3('b')), 'sum_ a e. ( 0 ..^ M ) ( %s x. %s )' % (Xa, E3('a')), '( %s x. %s )' % (YBk, TAU)],
                 [s3, w.s([cba], 'a1i', '( %s -> sum_ b e. ( 0 ..^ M ) ( %s x. %s ) = sum_ a e. ( 0 ..^ M ) ( %s x. %s ) )' % (A, Xb, E3('b'), Xa, E3('a'))), gs])
    # exponent: pi ( k^2 / ( M / y ) ) = ( pi k^2 ) ( y / M )
    ex = chain(w, A, ['( _pi x. ( ( k ^ 2 ) / %s ) )' % MY, '( _pi x. ( ( ( k ^ 2 ) x. y ) / M ) )', '( _pi x. ( ( k ^ 2 ) x. ( y / M ) ) )', '( ( _pi x. ( k ^ 2 ) ) x. ( y / M ) )'],
               [D(w, A, 'oveq2d', [D(w, A, 'divdiv2d', [c('( k ^ 2 )'), mc, yc, yne], '( ( k ^ 2 ) / %s ) = ( ( ( k ^ 2 ) x. y ) / M )' % MY)], '( _pi x. ( ( k ^ 2 ) / %s ) ) = ( _pi x. ( ( ( k ^ 2 ) x. y ) / M ) )' % MY),
                D(w, A, 'oveq2d', [D(w, A, 'divassd', [c('( k ^ 2 )'), yc, mc, mne], '( ( ( k ^ 2 ) x. y ) / M ) = ( ( k ^ 2 ) x. ( y / M ) )')], '( _pi x. ( ( ( k ^ 2 ) x. y ) / M ) ) = ( _pi x. ( ( k ^ 2 ) x. ( y / M ) ) )'),
                ('r', D(w, A, 'mulassd', [c('_pi'), c('( k ^ 2 )'), c('( y / M )')], '( ( _pi x. ( k ^ 2 ) ) x. ( y / M ) ) = ( _pi x. ( ( k ^ 2 ) x. ( y / M ) ) )'))])
    E1p = '( exp ` -u ( ( _pi x. ( k ^ 2 ) ) x. ( y / M ) ) )'
    ee = D(w, A, 'fveq2d', [D(w, A, 'negeqd', [ex], '-u ( _pi x. ( ( k ^ 2 ) / %s ) ) = -u ( ( _pi x. ( k ^ 2 ) ) x. ( y / M ) )' % MY)], '%s = %s' % (E1, E1p))
    PE2 = '( %s x. %s )' % (KP, E1p)
    tauc = D(w, A, 'dchrgscl' if False else 'syl', [ch, w.inst('dchrgscl')], '%s e. CC' % TAU)
    ybkc = chval(w, A, YB, D(w, A, 'simplrd', [par], '%s e. %s' % (YB, DB)), 'k', kz)
    fin = chain(w, A, ['sum_ b e. ( 0 ..^ M ) ( %s x. ( %s ` k ) )' % (Xb, L.GRB), 'sum_ b e. ( 0 ..^ M ) ( %s x. ( %s x. %s ) )' % (PE, Xb, E2('b')), '( %s x. sum_ b e. ( 0 ..^ M ) ( %s x. %s ) )' % (PE, Xb, E2('b')),
                    '( %s x. ( %s x. %s ) )' % (PE, YBk, TAU), '( %s x. ( %s x. %s ) )' % (PE2, YBk, TAU), '( ( %s x. %s ) x. %s )' % (YBk, TAU, PE2), '( ( %s x. %s ) x. %s )' % (TAU, YBk, PE2),
                    '( %s x. ( %s x. %s ) )' % (TAU, YBk, PE2)],
                [s1, ('r', s2), D(w, A, 'oveq2d', [gsum], '( %s x. sum_ b e. ( 0 ..^ M ) ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (PE, Xb, E2('b'), PE, YBk, TAU)),
                 D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [ee], '%s = %s' % (PE, PE2))], '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (PE, YBk, TAU, PE2, YBk, TAU)),
                 D(w, A, 'mulcomd', [c(PE2), D(w, A, 'mulcld', [ybkc, tauc], '( %s x. %s ) e. CC' % (YBk, TAU))], '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (PE2, YBk, TAU, YBk, TAU, PE2)),
                 D(w, A, 'oveq1d', [D(w, A, 'mulcomd', [ybkc, tauc], '( %s x. %s ) = ( %s x. %s )' % (YBk, TAU, TAU, YBk))], '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (YBk, TAU, PE2, TAU, YBk, PE2)),
                 D(w, A, 'mulassd', [tauc, ybkc, c(PE2)], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (TAU, YBk, PE2, TAU, YBk, PE2))])
    w.qed([fin], 'idi', S['zl3gs'])
    go(w)


# ---------------------------------------------------------------- zl3cst
if want('zl3cst'):
    w = W('zl3cst', 'The constant of the character theta transformation: ` M ^ P ( -i ) ^ P ( M / y ) ^ -( 1/2 + P ) T = ( T / ( i ^ P M ^ 1/2 ) ) y ^ ( P + 1/2 ) ` .')
    A, Cc = ante_of('zl3cst')
    h = D(w, A, 'simpl', [], '( M e. NN /\\ P e. { 0 , 1 } /\\ y e. RR+ )')
    mn = D(w, A, 'simp1d', [h], 'M e. NN'); pp = D(w, A, 'simp2d', [h], 'P e. { 0 , 1 }'); yrp = D(w, A, 'simp3d', [h], 'y e. RR+'); tc = D(w, A, 'simpr', [], 'T e. CC')
    pn = par_nn0(w, A, pp, 'P')
    mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+'); mc = D(w, A, 'rpcnd', [mrp], 'M e. CC'); mne = D(w, A, 'rpne0d', [mrp], 'M =/= 0')
    yc = D(w, A, 'rpcnd', [yrp], 'y e. CC'); yne = D(w, A, 'rpne0d', [yrp], 'y =/= 0')
    pc = D(w, A, 'nn0cnd', [pn], 'P e. CC')
    H = '( 1 / 2 )'
    hc = cst(w, A, 'halfcn', '%s e. CC' % H)
    E = '( %s + P )' % H
    ec = D(w, A, 'addcld', [hc, pc], '%s e. CC' % E)
    U, HM, V, Qi = '( M ^ P )', '( M ^c %s )' % H, '( y ^c %s )' % E, '( _i ^ P )'
    uc = D(w, A, 'expcld', [mc, pn], '%s e. CC' % U); une = D(w, A, 'expne0d', [mc, mne, D(w, A, 'nn0zd', [pn], 'P e. ZZ')], '%s =/= 0' % U)
    hmc = D(w, A, 'cxpcld', [mc, hc], '%s e. CC' % HM); hmne = D(w, A, 'cxpne0d', [mc, mne, hc], '%s =/= 0' % HM)
    vc = D(w, A, 'cxpcld', [yc, ec], '%s e. CC' % V)
    ic = cst(w, A, 'ax-icn', '_i e. CC'); ine = cst(w, A, 'ine0', '_i =/= 0')
    qc = D(w, A, 'expcld', [ic, pn], '%s e. CC' % Qi); qne = D(w, A, 'expne0d', [ic, ine, D(w, A, 'nn0zd', [pn], 'P e. ZZ')], '%s =/= 0' % Qi)
    MY = '( M / y )'
    # ( M / y ) ^c -E = V / ( HM x. U )
    me = D(w, A, 'eqtrd', [D(w, A, 'cxpaddd', [mc, mne, hc, pc], '( M ^c %s ) = ( %s x. ( M ^c P ) )' % (E, HM)),
                           D(w, A, 'oveq2d', [D(w, A, 'syl2anc', [mc, pn, w.inst('cxpexp')], '( M ^c P ) = %s' % U)], '( %s x. ( M ^c P ) ) = ( %s x. %s )' % (HM, HM, U))], '( M ^c %s ) = ( %s x. %s )' % (E, HM, U))
    mye = chain(w, A, ['( %s ^c -u %s )' % (MY, E), '( 1 / ( %s ^c %s ) )' % (MY, E), '( 1 / ( ( M ^c %s ) / ( y ^c %s ) ) )' % (E, E), '( %s / ( M ^c %s ) )' % (V, E), '( %s / ( %s x. %s ) )' % (V, HM, U)],
                [D(w, A, 'cxpnegd', [D(w, A, 'divcld', [mc, yc, yne], '%s e. CC' % MY), D(w, A, 'divne0d', [mc, yc, mne, yne], '%s =/= 0' % MY), ec], '( %s ^c -u %s ) = ( 1 / ( %s ^c %s ) )' % (MY, E, MY, E)),
                 D(w, A, 'oveq2d', [D(w, A, 'divcxpd', [D(w, A, 'rpred', [mrp], 'M e. RR'), D(w, A, 'rpge0d', [mrp], '0 <_ M'), yrp, ec], '( %s ^c %s ) = ( ( M ^c %s ) / ( y ^c %s ) )' % (MY, E, E, E))],
                   '( 1 / ( %s ^c %s ) ) = ( 1 / ( ( M ^c %s ) / ( y ^c %s ) ) )' % (MY, E, E, E)),
                 D(w, A, 'recdivd', [D(w, A, 'cxpcld', [mc, ec], '( M ^c %s ) e. CC' % E), vc, D(w, A, 'cxpne0d', [mc, mne, ec], '( M ^c %s ) =/= 0' % E), D(w, A, 'cxpne0d', [yc, yne, ec], '%s =/= 0' % V)],
                   '( 1 / ( ( M ^c %s ) / ( y ^c %s ) ) ) = ( %s / ( M ^c %s ) )' % (E, E, V, E)),
                 D(w, A, 'oveq2d', [me], '( %s / ( M ^c %s ) ) = ( %s / ( %s x. %s ) )' % (V, E, V, HM, U))])
    # ( -u _i ) ^ P = 1 / ( _i ^ P )
    def c0_(A0, e):
        return D(w, A0, 'eqtr4d', [D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [e], '( -u _i ^ P ) = ( -u _i ^ 0 )'), w.s([w.s([w.s([w.s([], 'ax-icn', '_i e. CC'), w.inst('negcl')], 'ax-mp', '-u _i e. CC'), w.inst('exp0')], 'ax-mp', '( -u _i ^ 0 ) = 1')], 'a1i', '( %s -> ( -u _i ^ 0 ) = 1 )' % A0)], '( -u _i ^ P ) = 1'),
                                   D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [e], '%s = ( _i ^ 0 )' % Qi), w.s([w.s([w.s([], 'ax-icn', '_i e. CC'), w.inst('exp0')], 'ax-mp', '( _i ^ 0 ) = 1')], 'a1i', '( %s -> ( _i ^ 0 ) = 1 )' % A0)], '%s = 1' % Qi)],
                                                                      '( 1 / %s ) = ( 1 / 1 )' % Qi), w.s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( %s -> ( 1 / 1 ) = 1 )' % A0)], '( 1 / %s ) = 1' % Qi)], '( -u _i ^ P ) = ( 1 / %s )' % Qi)
    def c1_(A1, e):
        return D(w, A1, 'eqtr4d', [D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [e], '( -u _i ^ P ) = ( -u _i ^ 1 )'), w.s([w.s([w.s([w.s([], 'ax-icn', '_i e. CC'), w.inst('negcl')], 'ax-mp', '-u _i e. CC'), w.inst('exp1')], 'ax-mp', '( -u _i ^ 1 ) = -u _i')], 'a1i', '( %s -> ( -u _i ^ 1 ) = -u _i )' % A1)], '( -u _i ^ P ) = -u _i'),
                                   D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [e], '%s = ( _i ^ 1 )' % Qi), w.s([w.s([w.s([], 'ax-icn', '_i e. CC'), w.inst('exp1')], 'ax-mp', '( _i ^ 1 ) = _i')], 'a1i', '( %s -> ( _i ^ 1 ) = _i )' % A1)], '%s = _i' % Qi)],
                                                                      '( 1 / %s ) = ( 1 / _i )' % Qi), w.s([w.s([], 'irec', '( 1 / _i ) = -u _i')], 'a1i', '( %s -> ( 1 / _i ) = -u _i )' % A1)], '( 1 / %s ) = -u _i' % Qi)], '( -u _i ^ P ) = ( 1 / %s )' % Qi)
    ni = pcases(w, A, pp, '( -u _i ^ P ) = ( 1 / %s )' % Qi, c0_, c1_)
    IQ = '( 1 / %s )' % Qi; HU = '( %s x. %s )' % (HM, U); huc = D(w, A, 'mulcld', [hmc, uc], '%s e. CC' % HU); hune = D(w, A, 'mulne0d', [hmc, hmne, uc, une], '%s =/= 0' % HU)
    QH = '( %s x. %s )' % (Qi, HM)
    qhc = D(w, A, 'mulcld', [qc, hmc], '%s e. CC' % QH); qhne = D(w, A, 'mulne0d', [qc, qne, hmc, hmne], '%s =/= 0' % QH)
    LHS = '( ( %s x. ( ( -u _i ^ P ) x. ( %s ^c -u %s ) ) ) x. T )' % (U, MY, E)
    ch = chain(w, A, [LHS, '( ( %s x. ( %s x. ( %s / %s ) ) ) x. T )' % (U, IQ, V, HU), '( ( %s x. ( ( 1 x. %s ) / ( %s x. %s ) ) ) x. T )' % (U, V, Qi, HU),
                      '( ( %s x. ( %s / ( %s x. %s ) ) ) x. T )' % (U, V, Qi, HU), '( ( ( %s x. %s ) / ( %s x. %s ) ) x. T )' % (U, V, Qi, HU),
                      '( ( ( %s x. %s ) / ( %s x. %s ) ) x. T )' % (V, U, Qi, HU), '( ( ( %s x. %s ) / ( %s x. %s ) ) x. T )' % (V, U, QH, U), '( ( %s / %s ) x. T )' % (V, QH),
                      '( T x. ( %s / %s ) )' % (V, QH), '( ( T x. %s ) / %s )' % (V, QH), '( ( T / %s ) x. %s )' % (QH, V)],
               [D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'oveq12d', [ni, mye], '( ( -u _i ^ P ) x. ( %s ^c -u %s ) ) = ( %s x. ( %s / %s ) )' % (MY, E, IQ, V, HU))],
                                    '( %s x. ( ( -u _i ^ P ) x. ( %s ^c -u %s ) ) ) = ( %s x. ( %s x. ( %s / %s ) ) )' % (U, MY, E, U, IQ, V, HU))], '%s = ( ( %s x. ( %s x. ( %s / %s ) ) ) x. T )' % (LHS, U, IQ, V, HU)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'divmuldivd', [cst(w, A, 'ax-1cn', '1 e. CC'), qc, vc, huc, qne, hune], '( %s x. ( %s / %s ) ) = ( ( 1 x. %s ) / ( %s x. %s ) )' % (IQ, V, HU, V, Qi, HU))],
                                                   '( %s x. ( %s x. ( %s / %s ) ) ) = ( %s x. ( ( 1 x. %s ) / ( %s x. %s ) ) )' % (U, IQ, V, HU, U, V, Qi, HU))],
                  '( ( %s x. ( %s x. ( %s / %s ) ) ) x. T ) = ( ( %s x. ( ( 1 x. %s ) / ( %s x. %s ) ) ) x. T )' % (U, IQ, V, HU, U, V, Qi, HU)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [D(w, A, 'mullidd', [vc], '( 1 x. %s ) = %s' % (V, V))], '( ( 1 x. %s ) / ( %s x. %s ) ) = ( %s / ( %s x. %s ) )' % (V, Qi, HU, V, Qi, HU))],
                                                   '( %s x. ( ( 1 x. %s ) / ( %s x. %s ) ) ) = ( %s x. ( %s / ( %s x. %s ) ) )' % (U, V, Qi, HU, U, V, Qi, HU))],
                  '( ( %s x. ( ( 1 x. %s ) / ( %s x. %s ) ) ) x. T ) = ( ( %s x. ( %s / ( %s x. %s ) ) ) x. T )' % (U, V, Qi, HU, U, V, Qi, HU)),
                D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'divassd', [uc, vc, D(w, A, 'mulcld', [qc, huc], '( %s x. %s ) e. CC' % (Qi, HU)), D(w, A, 'mulne0d', [qc, qne, huc, hune], '( %s x. %s ) =/= 0' % (Qi, HU))],
                                                                  '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s x. ( %s / ( %s x. %s ) ) )' % (U, V, Qi, HU, U, V, Qi, HU))],
                                                   '( %s x. ( %s / ( %s x. %s ) ) ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (U, V, Qi, HU, U, V, Qi, HU))],
                  '( ( %s x. ( %s / ( %s x. %s ) ) ) x. T ) = ( ( ( %s x. %s ) / ( %s x. %s ) ) x. T )' % (U, V, Qi, HU, U, V, Qi, HU)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq1d', [D(w, A, 'mulcomd', [uc, vc], '( %s x. %s ) = ( %s x. %s )' % (U, V, V, U))], '( ( %s x. %s ) / ( %s x. %s ) ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (U, V, Qi, HU, V, U, Qi, HU))],
                  '( ( ( %s x. %s ) / ( %s x. %s ) ) x. T ) = ( ( ( %s x. %s ) / ( %s x. %s ) ) x. T )' % (U, V, Qi, HU, V, U, Qi, HU)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, 'mulassd', [qc, hmc, uc], '( %s x. %s ) = ( %s x. %s )' % (QH, U, Qi, HU))], '( %s x. %s ) = ( %s x. %s )' % (Qi, HU, QH, U))],
                                                   '( ( %s x. %s ) / ( %s x. %s ) ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (V, U, Qi, HU, V, U, QH, U))],
                  '( ( ( %s x. %s ) / ( %s x. %s ) ) x. T ) = ( ( ( %s x. %s ) / ( %s x. %s ) ) x. T )' % (V, U, Qi, HU, V, U, QH, U)),
                D(w, A, 'oveq1d', [D(w, A, 'divcan5rd', [vc, qhc, uc, qhne, une], '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (V, U, QH, U, V, QH))],
                  '( ( ( %s x. %s ) / ( %s x. %s ) ) x. T ) = ( ( %s / %s ) x. T )' % (V, U, QH, U, V, QH)),
                D(w, A, 'mulcomd', [D(w, A, 'divcld', [vc, qhc, qhne], '( %s / %s ) e. CC' % (V, QH)), tc], '( ( %s / %s ) x. T ) = ( T x. ( %s / %s ) )' % (V, QH, V, QH)),
                D(w, A, 'eqcomd', [D(w, A, 'divassd', [tc, vc, qhc, qhne], '( ( T x. %s ) / %s ) = ( T x. ( %s / %s ) )' % (V, QH, V, QH))], '( T x. ( %s / %s ) ) = ( ( T x. %s ) / %s )' % (V, QH, V, QH)),
                D(w, A, 'div23d', [tc, vc, qhc, qhne], '( ( T x. %s ) / %s ) = ( ( T / %s ) x. %s )' % (V, QH, QH, V))])
    ep = D(w, A, 'oveq2d', [D(w, A, 'addcomd', [hc, pc], '%s = ( P + %s )' % (E, H))], '%s = ( y ^c ( P + %s ) )' % (V, H))
    w.qed([ch, D(w, A, 'oveq2d', [ep], '( ( T / %s ) x. %s ) = ( ( T / %s ) x. ( y ^c ( P + %s ) ) )' % (QH, V, QH, H))], 'eqtrd', S['zl3cst'])
    go(w)
