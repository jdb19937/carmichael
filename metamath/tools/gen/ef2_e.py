"""Sortie EF2: the local power series of a holomorphic function (ef2psa: coefficients; ef2pse: the expansion
F ( P + X ) = sum a_n X ^ n on the closed disc of radius E / 2 about P, from C1's rectintana)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
from c8_n import sqparts, sqre_at, sqcc
import lin
lin.FASTPATH = True

SQE = SQ('P', 'E'); QA = SQA('P', 'E'); QB = SQB('P', 'E')
P10 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (QB, QA)
P01 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (QA, QB)
FRM = '( ( ( %s cseg %s ) u. ( %s cseg %s ) ) u. ( ( %s cseg %s ) u. ( %s cseg %s ) ) )' % (QA, P10, P10, QB, QB, P01, P01, QA)


def CKv(v, m):
    return '( ( %s e. ( %s \\ { P } ) |-> ( ( F ` %s ) / ( ( %s - P ) ^ ( %s + 1 ) ) ) ) rectint <. %s , %s >. )' % (v, SQE, v, v, m, QA, QB)


AC = '( m e. NN0 |-> ( %s / %s ) )' % (CKv('z', 'm'), TPI)


def PSG(v='x'):
    return '( %s e. CC |-> ( n e. NN0 |-> ( ( %s ` n ) x. ( %s ^ n ) ) ) )' % (v, AC, v)


HYP0 = '( %s /\\ ( P e. CC /\\ E e. RR+ /\\ %s C_ D ) )' % (HOLF('F', 'D'), SQE)
S['ef2psa'] = '( %s -> %s : NN0 --> CC )' % (HYP0, AC)
S['ef2pse'] = '( ( %s /\\ ( X e. CC /\\ ( abs ` X ) <_ ( E / 2 ) ) ) -> seq 0 ( + , ( %s ` X ) ) ~~> ( F ` ( P + X ) ) )' % (HYP0, PSG())


def base(w, C, h0):
    """from h0 : ( C -> HYP0 ): dict of the square facts in context C"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    H1, H2 = top_and(HYP0)
    hol = s([h0, w.inst('simpl')], 'syl', H1); h2 = s([h0, w.inst('simpr')], 'syl', H2)
    K1, K2, K3 = top_and(H2)
    pc = s([h2, w.inst('simp1')], 'syl', K1); erp = s([h2, w.inst('simp2')], 'syl', K2); ssd = s([h2, w.inst('simp3')], 'syl', K3)
    er = s([erp], 'rpred', 'E e. RR')
    ps = sqparts(w, C, sqre_at(w, C, pc, er, c='P', r='E'), c='P', r='E')
    a, b = sqcc(w, C, pc, er, c='P', r='E')
    lv = {'E': er}
    for x, st in ((QA, a), (QB, b), ('P', pc)):
        lv['( Re ` %s )' % x] = s([st], 'recld', '( Re ` %s ) e. RR' % x)
        lv['( Im ` %s )' % x] = s([st], 'imcld', '( Im ` %s ) e. RR' % x)
    e0 = s([erp], 'rpgt0d', '0 < E')
    hy = ps + [e0]
    have = {'%s e. CC' % QA: a, '%s e. CC' % QB: b, 'P e. CC': pc}
    for goal in ('( Re ` %s ) < ( Re ` P )' % QA, '( Re ` P ) < ( Re ` %s )' % QB, '( Im ` %s ) < ( Im ` P )' % QA, '( Im ` P ) < ( Im ` %s )' % QB):
        have[goal] = lin8(w, C, hy, goal, lv)
    ins = conj(w, C, INS('P', QA, QB), have)
    hc = s([s([hol, ssd], 'jca', '( %s /\\ %s C_ D )' % (HOLF('F', 'D'), SQE)), w.inst('holcrect')], 'syl', '( F e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D F ) )' % SQE)
    have[INS('P', QA, QB)] = ins
    have['( F e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D F ) )' % SQE] = hc
    have['E e. RR'] = er; have['0 < E'] = e0
    return {'hol': hol, 'pc': pc, 'erp': erp, 'er': er, 'ssd': ssd, 'a': a, 'b': b, 'ps': ps, 'lv': lv, 'hy': hy, 'ins': ins, 'hc': hc, 'have': have}


def ck_cc(w, C, d, K, kn0):
    """( C -> CKv('z', K) e. CC ) from kn0 : ( C -> K e. NN0 )"""
    f = tsub(stmt('rectintccl'), {'A': QA, 'B': QB, 'M': '( %s + 1 )' % K, 'y': 'z'})
    fa, fc = ante_of(f)
    have = dict(d['have'])
    have['( %s + 1 ) e. NN0' % K] = w.s([kn0, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (C, K))
    return w.s([conj(w, C, fa, have), w.inst('rectintccl')], 'syl', '( %s -> %s )' % (C, fc))


def gen_psa():
    w = W('ef2psa', 'The Taylor coefficients ` ( 1 / 2 pi i ) ` times the rectangle integrals of ` F ( z ) / ( z - P ) ^ ( m + 1 ) ` of a function holomorphic near the square of half-side ` E ` about ` P ` are complex numbers.')
    C = HYP0
    d = base(w, C, w.s([], 'id', '( %s -> %s )' % (C, C)))
    Cm = '( %s /\\ m e. NN0 )' % C
    dm = {k: v for k, v in d.items()}
    dm['have'] = {k: up(w, v, Cm) for k, v in d['have'].items()}
    ck = ck_cc(w, Cm, dm, 'm', w.s([], 'simpr', '( %s -> m e. NN0 )' % Cm))
    tp = tpi_facts(w, Cm)
    val = w.s([ck, tp[0], tp[1]], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (Cm, CKv('z', 'm'), TPI))
    w.qed([val], 'fmpttd', S['ef2psa'])
    return run8(w)


def tpi_facts(w, C):
    """( C -> TPI e. CC ), ( C -> TPI =/= 0 )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    two = s([], '2cnd', '2 e. CC'); ic = s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'); pc = s([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')
    ipc = s([ic, pc], 'mulcld', '( _i x. _pi ) e. CC')
    tc = s([two, ipc], 'mulcld', '%s e. CC' % TPI)
    ipn = s([ic, s([w.s([], 'ine0', '_i =/= 0')], 'a1i', '_i =/= 0'), pc, s([w.s([], 'pine0', '_pi =/= 0')], 'a1i', '_pi =/= 0')], 'mulne0d', '( _i x. _pi ) =/= 0')
    tn = s([two, s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0'), ipc, ipn], 'mulne0d', '%s =/= 0' % TPI)
    return tc, tn


Z_ = '( P + X )'


def HMAP():
    return ('( j e. NN0 |-> ( ( ( %s - P ) ^ j ) x. ( ( y e. ( %s \\ { P } ) |-> ( ( F ` y ) / ( ( y - P ) ^ ( j + 1 ) ) ) ) rectint <. %s , %s >. ) ) )'
            % (Z_, SQE, QA, QB))


def CKy(k):
    return '( ( y e. ( %s \\ { P } ) |-> ( ( F ` y ) / ( ( y - P ) ^ ( %s + 1 ) ) ) ) rectint <. %s , %s >. )' % (SQE, k, QA, QB)


SX = '( n e. NN0 |-> sum_ k e. ( 0 ..^ n ) ( %s ` k ) )' % HMAP()


def gen_pse():
    w = W('ef2pse', 'Local power series (C1 ~ rectintana in ~ seq form): a function holomorphic near the square of half-side ` E ` about ` P ` is the sum of the series ` sum a_n X ^ n ` at ` P + X ` for ` abs X <_ E / 2 ` , with ` a_n ` the Cauchy coefficients of ~ ef2psa .')
    A0, GC = ante_of(S['ef2pse'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    h0 = s([], 'simpl', HYP0)
    X2 = '( X e. CC /\\ ( abs ` X ) <_ ( E / 2 ) )'
    xc = s([s([], 'simpr', X2), w.inst('simpl')], 'syl', 'X e. CC'); xle = s([s([], 'simpr', X2), w.inst('simpr')], 'syl', '( abs ` X ) <_ ( E / 2 )')
    # ---- case X =/= 0 ----
    A1 = '( %s /\\ X =/= 0 )' % A0
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    d = base(w, A1, up(w, h0, A1))
    x1 = up(w, xc, A1); xl1 = up(w, xle, A1); xn = s1([], 'simpr', 'X =/= 0')
    zc = s1([d['pc'], x1], 'addcld', '%s e. CC' % Z_)
    zp = s1([d['pc'], x1], 'pncan2d', '( %s - P ) = X' % Z_)
    lv = dict(d['lv'])
    for part, lem in (('Re', 'readdd'), ('Im', 'imaddd')):
        lv['( %s ` X )' % part] = s1([x1], 'recld' if part == 'Re' else 'imcld', '( %s ` X ) e. RR' % part)
    lv['( abs ` X )'] = s1([x1], 'abscld', '( abs ` X ) e. RR')
    hz = [s1([d['pc'], x1], 'readdd', '( Re ` %s ) = ( ( Re ` P ) + ( Re ` X ) )' % Z_), s1([d['pc'], x1], 'imaddd', '( Im ` %s ) = ( ( Im ` P ) + ( Im ` X ) )' % Z_)]
    for part, lem in (('Re', 'absrele'), ('Im', 'absimle')):
        pr = lv['( %s ` X )' % part]
        ab = s1([x1, w.inst(lem)], 'syl', '( abs ` ( %s ` X ) ) <_ ( abs ` X )' % part)
        abr = s1([s1([pr], 'recnd', '( %s ` X ) e. CC' % part)], 'abscld', '( abs ` ( %s ` X ) ) e. RR' % part)
        half = s1([d['er'], numst(w, A1, '2', 'RR'), s1([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')], 'redivcld', '( E / 2 ) e. RR')
        le = s1([abr, lv['( abs ` X )'], half, ab, xl1], 'letrd', '( abs ` ( %s ` X ) ) <_ ( E / 2 )' % part)
        bb = s1([le, s1([pr, half], 'absled', '( ( abs ` ( %s ` X ) ) <_ ( E / 2 ) <-> ( -u ( E / 2 ) <_ ( %s ` X ) /\\ ( %s ` X ) <_ ( E / 2 ) ) )' % (part, part, part))], 'mpbid',
                '( -u ( E / 2 ) <_ ( %s ` X ) /\\ ( %s ` X ) <_ ( E / 2 ) )' % (part, part))
        hz.append(s1([bb, w.inst('simpl')], 'syl', '-u ( E / 2 ) <_ ( %s ` X )' % part))
        hz.append(s1([bb, w.inst('simpr')], 'syl', '( %s ` X ) <_ ( E / 2 )' % part))
    for x, st in ((Z_, zc),):
        lv['( Re ` %s )' % x] = s1([st], 'recld', '( Re ` %s ) e. RR' % x)
        lv['( Im ` %s )' % x] = s1([st], 'imcld', '( Im ` %s ) e. RR' % x)
    have = dict(d['have'])
    have['%s e. CC' % Z_] = zc
    for goal in ('( Re ` %s ) < ( Re ` %s )' % (QA, Z_), '( Re ` %s ) < ( Re ` %s )' % (Z_, QB), '( Im ` %s ) < ( Im ` %s )' % (QA, Z_), '( Im ` %s ) < ( Im ` %s )' % (Z_, QB)):
        have[goal] = lin8(w, A1, d['hy'] + hz, goal, lv)
    zpne = s1([zc, d['pc'], s1([zp, xn], 'eqnetrd', '( %s - P ) =/= 0' % Z_)], 'subne0ad', '%s =/= P' % Z_)
    have['P =/= %s' % Z_] = s1([zpne], 'necomd', 'P =/= %s' % Z_)
    for goal in ('E <_ ( ( Re ` P ) - ( Re ` %s ) )' % QA, 'E <_ ( ( Re ` %s ) - ( Re ` P ) )' % QB, 'E <_ ( ( Im ` P ) - ( Im ` %s ) )' % QA, 'E <_ ( ( Im ` %s ) - ( Im ` P ) )' % QB):
        have[goal] = lin8(w, A1, d['hy'], goal, lv)
    have['( abs ` ( %s - P ) ) <_ ( E / 2 )' % Z_] = s1([s1([zp], 'fveq2d', '( abs ` ( %s - P ) ) = ( abs ` X )' % Z_), xl1], 'eqbrtrd', '( abs ` ( %s - P ) ) <_ ( E / 2 )' % Z_)
    # the frame bound, inside the existential of crectbnd
    CB = tsub(stmt('crectbnd'), {'A': QA, 'B': QB, 'G': 'F', 'm': 'l'})
    cba, cbc = ante_of(CB)
    hcn = s1([d['hol'], w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )')
    have['F e. ( D -cn-> CC )'] = hcn; have['%s C_ D' % SQE] = d['ssd']
    cb = s1([conj(w, A1, cba, have), w.inst('crectbnd')], 'syl', cbc)
    BODY = cbc[len('E. l e. RR '):]
    Al = '( ( %s /\\ l e. RR ) /\\ %s )' % (A1, BODY)
    sl = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Al, f))
    hl = {k: up(w, v, Al) for k, v in have.items()}
    fes = []
    for k in range(1, 5):
        fa, fc = ante_of(tsub(stmt('crectfe%d' % k), {'A': QA, 'B': QB}))
        fes.append(sl([conj(w, Al, fa, hl), w.inst('crectfe%d' % k)], 'syl', fc))
    SQP = '( %s \\ { P } )' % SQE
    E12 = '( ( %s cseg %s ) u. ( %s cseg %s ) )' % (QA, P10, P10, QB)
    E34 = '( ( %s cseg %s ) u. ( %s cseg %s ) )' % (QB, P01, P01, QA)
    fr = sl([sl([fes[0], fes[1]], 'unssd', '%s C_ %s' % (E12, SQP)), sl([fes[2], fes[3]], 'unssd', '%s C_ %s' % (E34, SQP))], 'unssd', '%s C_ %s' % (FRM, SQP))
    fr2 = sl([fr, sl([w.s([], 'difss', '%s C_ %s' % (SQP, SQE))], 'a1i', '%s C_ %s' % (SQP, SQE))], 'sstrd', '%s C_ %s' % (FRM, SQE))
    bnd = sl([fr2, sl([], 'simpr', BODY), w.inst('ssralv')], 'sylc', 'A. u e. %s ( abs ` ( F ` u ) ) <_ l' % FRM)
    hl['l e. RR'] = sl([], 'simplr', 'l e. RR')
    hl['A. u e. %s ( abs ` ( F ` u ) ) <_ l' % FRM] = bnd
    RA = tsub(stmt('rectintana'), {'A': QA, 'B': QB, 'Z': Z_, 'R': 'E', 'M': 'l', 'H': HMAP(), 'G': GMAP('b')})
    raa, rac = ante_of(RA)
    idb = w.s([], 'id', '( b = n -> b = n )')
    csb, _ = w.congr(GMAP('b')[len('( b e. NN0 |-> '):-2], {'b': 'n'}, 'b = n', {'b': idb})
    g_ = w.s([csb], 'cbvmptv', '%s = %s' % (GMAP('b'), GMAP())); h_ = w.s([], 'eqid', '%s = %s' % (HMAP(), HMAP()))
    ana = w.s([conj(w, Al, raa, hl), w.s([g_, h_], 'rectintana', RA)], 'syl', '( %s -> %s )' % (Al, rac))
    lim = s1([cb, w.s([w.s([ana], 'ex', '( ( %s /\\ l e. RR ) -> ( %s -> %s ) )' % (A1, BODY, rac))], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (A1, cbc, rac))], 'mpd', rac)
    FZ = '( F ` %s )' % Z_
    TL = '( %s x. %s )' % (TPI, FZ)
    tc, tn = tpi_facts(w, A1)
    HK = lambda K: '( %s ` %s )' % (HMAP(), K)
    SQP = '( %s \\ { P } )' % SQE
    # ---- climshft2: seq 0 ( + , H ) ~~> TL ----
    Ai = '( %s /\\ i e. NN )' % A1
    si = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    inn = si([], 'simpr', 'i e. NN')
    ic = si([inn], 'nncnd', 'i e. CC')
    e1 = si([ic, si([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'negsubd', '( i + -u 1 ) = ( i - 1 )')
    SEQH = 'seq 0 ( + , %s )' % HMAP()
    e2 = si([e1], 'fveq2d', '( %s ` ( i + -u 1 ) ) = ( %s ` ( i - 1 ) )' % (SEQH, SEQH))
    Aik = '( %s /\\ k e. ( 0 ... ( i - 1 ) ) )' % Ai
    kn0 = w.s([w.s([], 'simpr', '( %s -> k e. ( 0 ... ( i - 1 ) ) )' % Aik), w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % Aik)
    hv, hc = hval(w, Aik, d, zp, kn0, 'k', x1)
    im1 = si([si([inn, w.inst('nnm1nn0')], 'syl', '( i - 1 ) e. NN0'), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '( i - 1 ) e. ( ZZ>= ` 0 )')
    e3 = si([w.s([], 'eqidd', '( %s -> %s = %s )' % (Aik, HK('k'), HK('k'))), im1, hc], 'fsumser', 'sum_ k e. ( 0 ... ( i - 1 ) ) %s = ( %s ` ( i - 1 ) )' % (HK('k'), SEQH))
    from z4blib import fvmd
    e4 = fvmd(w, Ai, 'n', 'NN0', 'sum_ k e. ( 0 ..^ n ) %s' % HK('k'), 'i', si([inn], 'nnnn0d', 'i e. NN0'),
              w.s([w.s([], 'sumex', 'sum_ k e. ( 0 ..^ i ) %s e. _V' % HK('k'))], 'a1i', '( %s -> sum_ k e. ( 0 ..^ i ) %s e. _V )' % (Ai, HK('k'))))
    e5 = si([si([inn], 'nnzd', 'i e. ZZ'), w.inst('fzoval')], 'syl', '( 0 ..^ i ) = ( 0 ... ( i - 1 ) )')
    e6 = si([e5], 'sumeq1d', 'sum_ k e. ( 0 ..^ i ) %s = sum_ k e. ( 0 ... ( i - 1 ) ) %s' % (HK('k'), HK('k')))
    pt = si([si([e2, si([e3], 'eqcomd', '( %s ` ( i - 1 ) ) = sum_ k e. ( 0 ... ( i - 1 ) ) %s' % (SEQH, HK('k')))], 'eqtrd',
                 '( %s ` ( i + -u 1 ) ) = sum_ k e. ( 0 ... ( i - 1 ) ) %s' % (SEQH, HK('k'))),
             si([e4, e6], 'eqtrd', '( %s ` i ) = sum_ k e. ( 0 ... ( i - 1 ) ) %s' % (SX, HK('k')))], 'eqtr4d', '( %s ` ( i + -u 1 ) ) = ( %s ` i )' % (SEQH, SX))
    sh = s1([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s1([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), s1([w.s([], 'neg1z', '-u 1 e. ZZ')], 'a1i', '-u 1 e. ZZ'),
             s1([w.s([], 'mptex', '%s e. _V' % SX)], 'a1i', '%s e. _V' % SX), s1([w.s([], 'seqex', '%s e. _V' % SEQH)], 'a1i', '%s e. _V' % SEQH), pt],
            'climshft2', '( %s ~~> %s <-> %s ~~> %s )' % (SX, TL, SEQH, TL))
    lh = s1([lim, sh], 'mpbid', '%s ~~> %s' % (SEQH, TL))
    # ---- isermulc2 ----
    Ak = '( %s /\\ k e. NN0 )' % A1
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    kk = sk([], 'simpr', 'k e. NN0')
    hv2, hc2 = hval(w, Ak, d, zp, kk, 'k', x1)
    pv = psval(w, Ak, up(w, x1, Ak), kk, 'X', 'k', d)
    R_ = '( 1 / %s )' % TPI
    tck = up(w, tc, Ak); tnk = up(w, tn, Ak)
    ckz = ck_cc(w, Ak, dict(d, have={kx: up(w, vx, Ak) for kx, vx in d['have'].items()}), 'k', kk)
    CK = CKv('z', 'k')
    XK = '( X ^ k )'
    xk = sk([up(w, x1, Ak), kk], 'expcld', '%s e. CC' % XK)
    rc = sk([tck, tnk], 'reccld', '%s e. CC' % R_)
    q1 = sk([sk([ckz, tck, tnk], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (CK, TPI, CK, R_))], 'oveq1d', '( ( %s / %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (CK, TPI, XK, CK, R_, XK))
    q2 = sk([ckz, rc, xk], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (CK, R_, XK, CK, R_, XK))
    q3 = sk([ckz, rc, xk], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (CK, R_, XK, R_, CK, XK))
    q4 = sk([sk([ckz, xk], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (CK, XK, XK, CK))], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (R_, CK, XK, R_, XK, CK))
    q5 = sk([hv2], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (R_, HK('k'), R_, XK, CK))
    PK = '( ( %s ` X ) ` k )' % PSG()
    chain = sk([sk([sk([sk([pv, q1], 'eqtrd', '%s = ( ( %s x. %s ) x. %s )' % (PK, CK, R_, XK)), q2], 'eqtrd', '%s = ( %s x. ( %s x. %s ) )' % (PK, CK, R_, XK)), q3], 'eqtrd',
                   '%s = ( %s x. ( %s x. %s ) )' % (PK, R_, CK, XK)), q4], 'eqtrd', '%s = ( %s x. ( %s x. %s ) )' % (PK, R_, XK, CK))
    ptw = sk([chain, q5], 'eqtr4d', '%s = ( %s x. %s )' % (PK, R_, HK('k')))
    im = s1([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )'), s1([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ'), s1([tc, tn], 'reccld', '%s e. CC' % R_), lh, hc2, ptw],
            'isermulc2', 'seq 0 ( + , ( %s ` X ) ) ~~> ( %s x. %s )' % (PSG(), R_, TL))
    # ( 1 / T ) ( T F Z ) = F Z
    zin = s1([s1([d['a'], d['b']], 'jca', '( %s e. CC /\\ %s e. CC )' % (QA, QB)), conj(w, A1, '( %s e. CC /\\ %s )' % (Z_, INS(Z_, QA, QB)), have), w.inst('crectinp')], 'syl2anc',
             '%s e. %s' % (Z_, SQE))
    fz = fcc(w, A1, d['hol'], 'F', 'D', Z_, s1([d['ssd'], zin], 'sseldd', '%s e. D' % Z_))
    r1 = s1([s1([s1([tc, tn], 'reccld', '%s e. CC' % R_), tc, fz], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (R_, TPI, FZ, R_, TL))], 'eqcomd',
            '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (R_, TL, R_, TPI, FZ))
    r2 = s1([s1([tc, tn], 'recid2d', '( %s x. %s ) = 1' % (R_, TPI))], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (R_, TPI, FZ, FZ))
    r3 = s1([s1([r1, r2], 'eqtrd', '( %s x. %s ) = ( 1 x. %s )' % (R_, TL, FZ)), s1([fz], 'mullidd', '( 1 x. %s ) = %s' % (FZ, FZ))], 'eqtrd', '( %s x. %s ) = %s' % (R_, TL, FZ))
    case1 = w.s([s1([im, r3], 'breqtrd', GC)], 'ex', '( %s -> ( X =/= 0 -> %s ) )' % (A0, GC))
    case0 = zero_case(w, A0, h0, xc, GC)
    w.qed([case0, case1], 'pm2.61dne', S['ef2pse'])
    return run8(w)


def hval(w, C, d, zp, kst, K, x1st):
    """( C -> ( HMAP ` K ) = ( ( X ^ K ) x. CKv('z', K) ) ) and ( C -> ( HMAP ` K ) e. CC ); kst : ( C -> K e. NN0 )"""
    from z4blib import fvmd
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    BODY = lambda j: '( ( ( %s - P ) ^ %s ) x. %s )' % (Z_, j, CKy(j))
    v1 = fvmd(w, C, 'j', 'NN0', BODY('j'), K, kst, w.s([], 'ovexd', '( %s -> %s e. _V )' % (C, BODY(K))))
    zpc = up(w, zp, C)
    v2 = s([s([zpc], 'oveq1d', '( ( %s - P ) ^ %s ) = ( X ^ %s )' % (Z_, K, K))], 'oveq1d', '%s = ( ( X ^ %s ) x. %s )' % (BODY(K), K, CKy(K)))
    MY = '( y e. ( %s \\ { P } ) |-> ( ( F ` y ) / ( ( y - P ) ^ ( %s + 1 ) ) ) )' % (SQE, K)
    MZ = '( z e. ( %s \\ { P } ) |-> ( ( F ` z ) / ( ( z - P ) ^ ( %s + 1 ) ) ) )' % (SQE, K)
    idst = w.s([], 'id', '( y = z -> y = z )')
    cs, new = w.congr('( ( F ` y ) / ( ( y - P ) ^ ( %s + 1 ) ) )' % K, {'y': 'z'}, 'y = z', {'y': idst})
    cb = w.s([cs], 'cbvmptv', '%s = %s' % (MY, MZ))
    v3 = s([w.s([cb], 'oveq1i', '( %s rectint <. %s , %s >. ) = ( %s rectint <. %s , %s >. )' % (MY, QA, QB, MZ, QA, QB))], 'a1i', '%s = %s' % (CKy(K), CKv('z', K)))
    v4 = s([v3], 'oveq2d', '( ( X ^ %s ) x. %s ) = ( ( X ^ %s ) x. %s )' % (K, CKy(K), K, CKv('z', K)))
    val = s([s([v1, v2], 'eqtrd', '( %s ` %s ) = ( ( X ^ %s ) x. %s )' % (HMAP(), K, K, CKy(K))), v4], 'eqtrd', '( %s ` %s ) = ( ( X ^ %s ) x. %s )' % (HMAP(), K, K, CKv('z', K)))
    dC = dict(d, have={kx: up(w, vx, C) for kx, vx in d['have'].items()})
    ck = ck_cc(w, C, dC, K, kst)
    pc = s([s([up(w, x1st, C), kst], 'expcld', '( X ^ %s ) e. CC' % K), ck], 'mulcld', '( ( X ^ %s ) x. %s ) e. CC' % (K, CKv('z', K)))
    return val, s([val, pc], 'eqeltrd', '( %s ` %s ) e. CC' % (HMAP(), K))


def psval(w, C, xst, kst, Xv, K, d):
    """( C -> ( ( PSG ` Xv ) ` K ) = ( ( CKv('z', K) / TPI ) x. ( Xv ^ K ) ) )"""
    from z4blib import fvmd
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    ge = w.s([], 'eqid', '%s = %s' % (PSG(), PSG()))
    p1 = s([xst, kst, w.s([ge], 'pserval2', '( ( %s e. CC /\\ %s e. NN0 ) -> ( ( %s ` %s ) ` %s ) = ( ( %s ` %s ) x. ( %s ^ %s ) ) )' % (Xv, K, PSG(), Xv, K, AC, K, Xv, K))],
           'syl2anc', '( ( %s ` %s ) ` %s ) = ( ( %s ` %s ) x. ( %s ^ %s ) )' % (PSG(), Xv, K, AC, K, Xv, K))
    ACB = lambda m: '( %s / %s )' % (CKv('z', m), TPI)
    a1 = fvmd(w, C, 'm', 'NN0', ACB('m'), K, kst, w.s([], 'ovexd', '( %s -> %s e. _V )' % (C, ACB(K))))
    return s([p1, s([a1], 'oveq1d', '( ( %s ` %s ) x. ( %s ^ %s ) ) = ( %s x. ( %s ^ %s ) )' % (AC, K, Xv, K, ACB(K), Xv, K))], 'eqtrd',
             '( ( %s ` %s ) ` %s ) = ( %s x. ( %s ^ %s ) )' % (PSG(), Xv, K, ACB(K), Xv, K))


def zero_case(w, A0, h0, xc, GC):
    """( A0 -> ( X = 0 -> GC ) )"""
    from z4blib import fvmd
    A2 = '( %s /\\ X = 0 )' % A0
    s2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A2, f))
    d = base(w, A2, up(w, h0, A2))
    x2 = up(w, xc, A2); x0 = s2([], 'simpr', 'X = 0')
    tc, tn = tpi_facts(w, A2)
    PX = '( %s ` X )' % PSG()
    PXK = lambda K: '( %s ` %s )' % (PX, K)
    IFB = lambda v: 'if ( %s e. { 0 } , %s , 0 )' % (v, PXK(v))
    FP = '( i e. ZZ |-> %s )' % IFB('i')
    FPk = '( k e. ZZ |-> %s )' % IFB('k')
    def pxcc(C, kst, K):
        dC = dict(d, have={kx: up(w, vx, C) for kx, vx in d['have'].items()})
        pv = psval(w, C, up(w, x2, C), kst, 'X', K, dC)
        ck = ck_cc(w, C, dC, K, kst)
        pr = w.s([w.s([ck, up(w, tc, C), up(w, tn, C)], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (C, CKv('z', K), TPI)),
                  w.s([up(w, x2, C), kst], 'expcld', '( %s -> ( X ^ %s ) e. CC )' % (C, K))], 'mulcld', '( %s -> ( ( %s / %s ) x. ( X ^ %s ) ) e. CC )' % (C, CKv('z', K), TPI, K))
        return pv, w.s([pv, pr], 'eqeltrd', '( %s -> %s e. CC )' % (C, PXK(K)))
    # seqfeq
    Ak = '( %s /\\ k e. ( ZZ>= ` 0 ) )' % A2
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    kn0 = sk([sk([], 'simpr', 'k e. ( ZZ>= ` 0 )'), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrrdi', 'k e. NN0')
    pv, pc = pxcc(Ak, kn0, 'k')
    fvk = fvmd(w, Ak, 'i', 'ZZ', IFB('i'), 'k', sk([kn0], 'nn0zd', 'k e. ZZ'), sk([pc, sk([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFB('k')))
    Ak1 = '( %s /\\ k e. { 0 } )' % Ak
    t1 = w.s([w.s([w.s([], 'simpr', '( %s -> k e. { 0 } )' % Ak1)], 'iftrued', '( %s -> %s = %s )' % (Ak1, IFB('k'), PXK('k')))], 'eqcomd', '( %s -> %s = %s )' % (Ak1, PXK('k'), IFB('k')))
    Ak2 = '( %s /\\ -. k e. { 0 } )' % Ak
    s3 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak2, f))
    nk = s3([], 'simpr', '-. k e. { 0 }')
    nk2 = s3([nk, s3([w.s([], 'velsn', '( k e. { 0 } <-> k = 0 )')], 'a1i', '( k e. { 0 } <-> k = 0 )')], 'mtbid', '-. k = 0')
    kn = s3([s3([up(w, kn0, Ak2), s3([nk2], 'neqned', 'k =/= 0')], 'jca', '( k e. NN0 /\\ k =/= 0 )'), w.s([], 'elnnne0', '( k e. NN <-> ( k e. NN0 /\\ k =/= 0 ) )')], 'sylibr', 'k e. NN')
    xk0 = s3([s3([up(w, x0, Ak2)], 'oveq1d', '( X ^ k ) = ( 0 ^ k )'), s3([kn], '0expd', '( 0 ^ k ) = 0')], 'eqtrd', '( X ^ k ) = 0')
    CK = CKv('z', 'k')
    dC = dict(d, have={kx: up(w, vx, Ak2) for kx, vx in d['have'].items()})
    ckq = s3([ck_cc(w, Ak2, dC, 'k', up(w, kn0, Ak2)), up(w, tc, Ak2), up(w, tn, Ak2)], 'divcld', '( %s / %s ) e. CC' % (CK, TPI))
    z1 = s3([s3([up(w, pv, Ak2), s3([xk0], 'oveq2d', '( ( %s / %s ) x. ( X ^ k ) ) = ( ( %s / %s ) x. 0 )' % (CK, TPI, CK, TPI))], 'eqtrd',
                '%s = ( ( %s / %s ) x. 0 )' % (PXK('k'), CK, TPI)), s3([ckq], 'mul01d', '( ( %s / %s ) x. 0 ) = 0' % (CK, TPI))], 'eqtrd', '%s = 0' % PXK('k'))
    t2 = s3([z1, s3([nk], 'iffalsed', '%s = 0' % IFB('k'))], 'eqtr4d', '%s = %s' % (PXK('k'), IFB('k')))
    ptw = sk([sk([t1, t2], 'pm2.61dan', '%s = %s' % (PXK('k'), IFB('k'))), fvk], 'eqtr4d', '%s = ( %s ` k )' % (PXK('k'), FP))
    SP, SF = 'seq 0 ( + , %s )' % PX, 'seq 0 ( + , %s )' % FP
    sq = s2([s2([], '0zd', '0 e. ZZ'), ptw], 'seqfeq', '%s = %s' % (SP, SF))
    # fsumcvg
    idik = w.s([], 'id', '( i = k -> i = k )')
    cs, new = w.congr(IFB('i'), {'i': 'k'}, 'i = k', {'i': idik})
    fpk = w.s([cs], 'cbvmptv', '%s = %s' % (FP, FPk))
    A0k = '( %s /\\ k e. { 0 } )' % A2
    k0 = w.s([w.s([w.s([], 'simpr', '( %s -> k e. { 0 } )' % A0k), w.inst('elsni')], 'syl', '( %s -> k = 0 )' % A0k), w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % A0k)], 'eqeltrd', '( %s -> k e. NN0 )' % A0k)
    _, pc0 = pxcc(A0k, k0, 'k')
    ssfz = s2([w.s([w.s([], 'fz0sn', '( 0 ... 0 ) = { 0 }')], 'eqimss2i', '{ 0 } C_ ( 0 ... 0 )')], 'a1i', '{ 0 } C_ ( 0 ... 0 )')
    u0 = s2([s2([], '0zd', '0 e. ZZ'), w.inst('uzid')], 'syl', '0 e. ( ZZ>= ` 0 )')
    fc = s2([fpk, pc0, u0, ssfz], 'fsumcvg', '%s ~~> ( %s ` 0 )' % (SF, SF))
    s1v = s2([s2([], '0zd', '0 e. ZZ'), w.inst('seq1')], 'syl', '( %s ` 0 ) = ( %s ` 0 )' % (SF, FP))
    z0 = s2([], '0zd', '0 e. ZZ')
    zin0 = s2([w.s([w.s([], '0cn', '0 e. CC'), w.inst('snidg')], 'ax-mp', '0 e. { 0 }')], 'a1i', '0 e. { 0 }')
    n0 = s2([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0')
    pv0, pc00 = pxcc(A2, n0, '0')
    fv0 = fvmd(w, A2, 'i', 'ZZ', IFB('i'), '0', z0, s2([pc00, s2([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFB('0')))
    it0 = s2([zin0], 'iftrued', '%s = %s' % (IFB('0'), PXK('0')))
    CK0 = CKv('z', '0')
    e0 = s2([s2([x2], 'exp0d', '( X ^ 0 ) = 1')], 'oveq2d', '( ( %s / %s ) x. ( X ^ 0 ) ) = ( ( %s / %s ) x. 1 )' % (CK0, TPI, CK0, TPI))
    dC0 = d
    ckq0 = s2([ck_cc(w, A2, d, '0', n0), tc, tn], 'divcld', '( %s / %s ) e. CC' % (CK0, TPI))
    e1 = s2([ckq0], 'mulridd', '( ( %s / %s ) x. 1 ) = ( %s / %s )' % (CK0, TPI, CK0, TPI))
    # the coefficient at 0 by Cauchy's formula
    SQP = '( %s \\ { P } )' % SQE
    Az = '( %s /\\ z e. %s )' % (A2, SQP)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zcc = sz([sz([sz([w.s([], 'difss', '%s C_ %s' % (SQP, SQE))], 'a1i', '%s C_ %s' % (SQP, SQE)), sz([up(w, d['a'], Az), up(w, d['b'], Az), w.inst('crectss')], 'syl2anc', '%s C_ CC' % SQE)], 'sstrd',
                  '%s C_ CC' % SQP), sz([], 'simpr', 'z e. %s' % SQP)], 'sseldd', 'z e. CC')
    zp = sz([zcc, up(w, d['pc'], Az)], 'subcld', '( z - P ) e. CC')
    ex1 = sz([sz([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'oveq2i', '( ( z - P ) ^ ( 0 + 1 ) ) = ( ( z - P ) ^ 1 )')], 'a1i', '( ( z - P ) ^ ( 0 + 1 ) ) = ( ( z - P ) ^ 1 )'),
              sz([zp], 'exp1d', '( ( z - P ) ^ 1 ) = ( z - P )')], 'eqtrd', '( ( z - P ) ^ ( 0 + 1 ) ) = ( z - P )')
    ex2 = sz([ex1], 'oveq2d', '( ( F ` z ) / ( ( z - P ) ^ ( 0 + 1 ) ) ) = ( ( F ` z ) / ( z - P ) )')
    M0 = '( z e. %s |-> ( ( F ` z ) / ( ( z - P ) ^ ( 0 + 1 ) ) ) )' % SQP
    M1 = '( z e. %s |-> ( ( F ` z ) / ( z - P ) ) )' % SQP
    meq = s2([ex2], 'mpteq2dva', '%s = %s' % (M0, M1))
    ci = s2([meq], 'oveq1d', '%s = ( %s rectint <. %s , %s >. )' % (CK0, M1, QA, QB))
    RC = tsub(stmt('rectintcau'), {'A': QA, 'B': QB})
    rca, rcc = ante_of(RC)
    cau = s2([conj(w, A2, rca, d['have']), w.inst('rectintcau')], 'syl', rcc)
    FP_ = '( F ` P )'
    ck0 = s2([ci, cau], 'eqtrd', '%s = ( %s x. %s )' % (CK0, TPI, FP_))
    pin = s2([s2([d['a'], d['b']], 'jca', '( %s e. CC /\\ %s e. CC )' % (QA, QB)), conj(w, A2, '( P e. CC /\\ %s )' % INS('P', QA, QB), d['have']), w.inst('crectinp')], 'syl2anc', 'P e. %s' % SQE)
    fpc = fcc(w, A2, d['hol'], 'F', 'D', 'P', s2([d['ssd'], pin], 'sseldd', 'P e. D'))
    dv = s2([s2([ck0], 'oveq1d', '( %s / %s ) = ( ( %s x. %s ) / %s )' % (CK0, TPI, TPI, FP_, TPI)), s2([fpc, tc, tn], 'divcan3d', '( ( %s x. %s ) / %s ) = %s' % (TPI, FP_, TPI, FP_))], 'eqtrd',
            '( %s / %s ) = %s' % (CK0, TPI, FP_))
    fpx = s2([s2([s2([x0], 'oveq2d', '( P + X ) = ( P + 0 )'), s2([d['pc']], 'addridd', '( P + 0 ) = P')], 'eqtrd', '( P + X ) = P')], 'fveq2d', '( F ` ( P + X ) ) = %s' % FP_)
    # value chain: seq FP at 0 = F ( P + X )
    ch = s2([s1v, fv0], 'eqtrd', '( %s ` 0 ) = %s' % (SF, IFB('0')))
    ch = s2([ch, it0], 'eqtrd', '( %s ` 0 ) = %s' % (SF, PXK('0')))
    ch = s2([ch, pv0], 'eqtrd', '( %s ` 0 ) = ( ( %s / %s ) x. ( X ^ 0 ) )' % (SF, CK0, TPI))
    ch = s2([ch, e0], 'eqtrd', '( %s ` 0 ) = ( ( %s / %s ) x. 1 )' % (SF, CK0, TPI))
    ch = s2([ch, e1], 'eqtrd', '( %s ` 0 ) = ( %s / %s )' % (SF, CK0, TPI))
    ch = s2([ch, dv], 'eqtrd', '( %s ` 0 ) = %s' % (SF, FP_))
    ch = s2([ch, fpx], 'eqtr4d', '( %s ` 0 ) = ( F ` ( P + X ) )' % SF)
    lim = s2([sq, s2([fc, ch], 'breqtrd', '%s ~~> ( F ` ( P + X ) )' % SF)], 'eqbrtrd', GC)
    return w.s([lim], 'ex', '( %s -> ( X = 0 -> %s ) )' % (A0, GC))


def GMAP(v='n'):
    return ('( %s e. NN0 |-> ( ( y e. ( %s \\ { P , %s } ) |-> ( ( ( F ` y ) x. ( ( ( %s - P ) / ( y - P ) ) ^ %s ) ) / ( y - %s ) ) ) rectint <. %s , %s >. ) )'
            % (v, SQE, Z_, Z_, v, Z_, QA, QB))


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2psa', 'ef2pse']:
        {'ef2psa': gen_psa, 'ef2pse': gen_pse}[g]()
