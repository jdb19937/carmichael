"""Sortie KD1: Cauchy's estimate for the K-th derivative of the Landau remainder at s0 (kdrepb)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_repb():
    w = W('kdrepb', 'Lean ` KDerivDetect.norm_iteratedDeriv_le_of_bounded_on_disk ` at ` s0 = ( 1 + E ) + i T ` : ` abs g ^ ( K ) ( s0 ) <_ K ! 2 3 ^ K 17500000 log ( N ( abs T + 2 ) ) ` , from ` kdcest ` on a square ` SQ ( s0 , t ) ` , ` 1 / 3 <_ t <_ 2 / 5 ` , whose frame misses the zeros ( ` kdfrm ` ; C10 ` lndlchrk ` on the frame).')
    A0 = S['kdrepb'].split(' -> ( abs ` ( ( ( CC Dn g )')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    kd = s([], 'simpl', KDH); hgp = s([], 'simpr', HGP())
    chi = s([kd], 'simpld', CHI)
    tek = s([kd], 'simprd', '( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ K e. NN0 )' % R120)
    tr = s([tek], 'simp1d', 'T e. RR'); ee = s([tek], 'simp2d', '( E e. RR+ /\\ E <_ %s )' % R120); kk = s([tek], 'simp3d', 'K e. NN0')
    ep = s([ee], 'simpld', 'E e. RR+'); er = s([ep], 'rpred', 'E e. RR')
    GID = 'A. z e. %s ( ( %s ` z ) =/= 0 -> ( g ` z ) = ( ( ( ( CC _D %s ) ` z ) / ( %s ` z ) ) - sum_ q e. %s ( %s / ( z - q ) ) ) )' % (O13, LFN, LFN, LFN, ZD(), MU())
    hg = s([hgp], 'simpld', HOLF('g', O13)); gid = s([hgp], 'simprd', GID)
    nx = s([chi], 'simpld', NXH)
    SS = S0(); SQ13 = SQ(CT('T'), R138)
    c = Closure(w, A0, {'T': ('RR', tr), 'E': ('RR', er)})
    s0c = s([s([s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), er], 'readdcld', '( 1 + E ) e. RR')], 'recnd', '( 1 + E ) e. CC'),
             s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SS)
    # the zero set with binder y, finite, in CC
    ZDy = '{ y e. %s | ( %s ` y ) = 0 }' % (SQ13, LFN)
    cby = w.s([w.s([], 'fveqeq2', '( r = y -> ( ( %s ` r ) = 0 <-> ( %s ` y ) = 0 ) )' % (LFN, LFN))], 'cbvrabv', '%s = %s' % (ZD(), ZDy))
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0])
    zyf = s([zfin, w.s([cby], 'a1i', '( %s -> %s = %s )' % (A0, ZD(), ZDy))], 'eqeltrrd', '%s e. Fin' % ZDy)
    cct = s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CT('T'))
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    ric = s([s([c.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([c.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
            'addcld', '%s e. CC' % RI_)
    a13 = s([cct, ric], 'subcld', '%s e. CC' % A13); b13 = s([cct, ric], 'addcld', '%s e. CC' % B13)
    sqcc = s([s([a13, b13], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    zycc = s([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZDy, SQ13))], 'a1i', '( %s -> %s C_ %s )' % (A0, ZDy, SQ13)), sqcc], 'sstrd', '%s C_ CC' % ZDy)
    osq = s([a13, b13, w.inst('orectss')], 'syl2anc', '%s C_ %s' % (O13, SQ13))
    FRr = tsub(S['kdfrm'], {'Z': ZDy, 'P': SS})
    fa, fc = split_imp(FRr)
    frm = s([zyf, zycc, s0c, w.inst('kdfrm')], 'syl3anc', fc)
    # rename r -> t
    Ir = '( ( 1 / 3 ) [,] ( 2 / 5 ) )'
    BR = 'A. u e. %s -. u e. %s' % (FSQ(SS, 'r'), ZDy)
    BT = 'A. u e. %s -. u e. %s' % (FSQ(SS, 't'), ZDy)
    idrt = w.s([], 'id', '( r = t -> r = t )')
    crt, nrt = w.wcongr(BR, {'r': 't'}, 'r = t', {'r': idrt})
    assert nrt == BT
    frt = s([frm, w.s([crt], 'cbvrexvw', '( E. r e. %s %s <-> E. t e. %s %s )' % (Ir, BR, Ir, BT))], 'sylib', 'E. t e. %s %s' % (Ir, BT))
    Ar = '( %s /\\ ( t e. %s /\\ %s ) )' % (A0, Ir, BT)
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ar, f))
    L = lambda st: lift(w, st, Ar)
    ti = a([], 'simprl', 't e. %s' % Ir)
    ca = Closure(w, Ar, {})
    te = a([ti, a([ca.mem('( 1 / 3 )', 'RR'), ca.mem('( 2 / 5 )', 'RR'), w.inst('elicc2')], 'syl2anc', '( t e. %s <-> ( t e. RR /\\ ( 1 / 3 ) <_ t /\\ t <_ ( 2 / 5 ) ) )' % Ir)],
           'mpbid', '( t e. RR /\\ ( 1 / 3 ) <_ t /\\ t <_ ( 2 / 5 ) )')
    ttr = a([te], 'simp1d', 't e. RR'); t13 = a([te], 'simp2d', '( 1 / 3 ) <_ t')
    ca.leaf('t', 'RR', ttr)
    t0 = linarith(w, Ar, [t13], '0 < t', closure=ca)
    tp = a([ttr, t0], 'elrpd', 't e. RR+')
    GEO = tsub(S['kdgeo'], {'R': 't'})
    ga, gc = split_imp(GEO)
    geo = a([L(tr), L(ee), ti, w.inst('kdgeo')], 'syl3anc', gc)
    g12 = a([geo], 'simpld', top_and(gc)[0])
    SQT = SQ(SS, 't')
    g1 = a([g12], 'simpld', '%s C_ %s' % (SQT, O13)); g2 = a([g12], 'simprd', 'A. u e. %s ( abs ` ( u - %s ) ) <_ ( 3 / 2 )' % (SQT, CT('T')))
    q2 = sqctx2(w, Ar, SS, 't', L(s0c), tp)
    FR = FSQ(SS, 't')
    bt = a([], 'simprr', BT)
    # frame bound
    Av = '( %s /\\ v e. %s )' % (Ar, FR)
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    M = lambda st: lift(w, st, Av)
    vf = b([], 'simpr', 'v e. %s' % FR)
    vs = b([M(q2['fru']), vf], 'sseldd', 'v e. %s' % SQT)
    vo = b([M(g1), vs], 'sseldd', 'v e. %s' % O13)
    vsq = b([M(osq), vo], 'sseldd', 'v e. %s' % SQ13)
    cuv = w.s([w.s([], 'eleq1', '( u = v -> ( u e. %s <-> v e. %s ) )' % (ZDy, ZDy))], 'notbid', '( u = v -> ( -. u e. %s <-> -. v e. %s ) )' % (ZDy, ZDy))
    nvz = b([vf, M(bt), w.s([cuv], 'rspcv', '( v e. %s -> ( %s -> -. v e. %s ) )' % (FR, BT, ZDy))], 'sylc', '-. v e. %s' % ZDy)
    ely = w.s([w.s([], 'fveqeq2', '( y = v -> ( ( %s ` y ) = 0 <-> ( %s ` v ) = 0 ) )' % (LFN, LFN))], 'elrab', '( v e. %s <-> ( v e. %s /\\ ( %s ` v ) = 0 ) )' % (ZDy, SQ13, LFN))
    imp = b([vsq, w.s([ely], 'biimpri', '( ( v e. %s /\\ ( %s ` v ) = 0 ) -> v e. %s )' % (SQ13, LFN, ZDy))], 'T.', 'T.') if False else \
        w.s([w.s([vsq, w.s([ely], 'biimpri', '( ( v e. %s /\\ ( %s ` v ) = 0 ) -> v e. %s )' % (SQ13, LFN, ZDy))], 'sylan', '( ( %s /\\ ( %s ` v ) = 0 ) -> v e. %s )' % (Av, LFN, ZDy))],
            'ex', '( %s -> ( ( %s ` v ) = 0 -> v e. %s ) )' % (Av, LFN, ZDy))
    nl = b([imp, nvz], 'mtod', '-. ( %s ` v ) = 0' % LFN)
    lnz = b([nl], 'neqned', '( %s ` v ) =/= 0' % LFN)
    cdu = w.s([w.s([w.s([], 'oveq1', '( u = v -> ( u - %s ) = ( v - %s ) )' % (CT('T'), CT('T')))], 'fveq2d', '( u = v -> ( abs ` ( u - %s ) ) = ( abs ` ( v - %s ) ) )' % (CT('T'), CT('T')))],
              'breq1d', '( u = v -> ( ( abs ` ( u - %s ) ) <_ ( 3 / 2 ) <-> ( abs ` ( v - %s ) ) <_ ( 3 / 2 ) ) )' % (CT('T'), CT('T')))
    dv = b([vs, M(g2), w.s([cdu], 'rspcv', '( v e. %s -> ( A. u e. %s ( abs ` ( u - %s ) ) <_ ( 3 / 2 ) -> ( abs ` ( v - %s ) ) <_ ( 3 / 2 ) ) )' % (SQT, SQT, CT('T'), CT('T')))],
           'sylc', '( abs ` ( v - %s ) ) <_ ( 3 / 2 )' % CT('T'))
    RZ = GID[len('A. z e. %s ' % O13):]
    idzv = w.s([], 'id', '( z = v -> z = v )')
    czv, rv = w.wcongr(RZ, {'z': 'v'}, 'z = v', {'z': idzv})
    gv = b([lnz, b([vo, M(gid), w.s([czv], 'rspcv', '( v e. %s -> ( %s -> %s ) )' % (O13, GID, rv))], 'sylc', rv)], 'mpd', split_imp(rv)[1])
    vc = b([vs, b([M(q2['ab']), w.inst('crectss')], 'syl', '%s C_ CC' % SQT) and b([b([M(q2['ab']), w.inst('crectss')], 'syl', '%s C_ CC' % SQT), vs], 'sseldd', 'v e. CC')], 'T.', 'T.') if False else \
        b([b([M(q2['ab']), w.inst('crectss')], 'syl', '%s C_ CC' % SQT), vs], 'sseldd', 'v e. CC')
    LN = tsub(stmt('lndlchrk'), {'S': 'v'})
    lna, lnc = split_imp(LN)
    ln = b([b([M(chi), M(tr)], 'jca', top_and(lna)[0]), b([vc, dv, lnz], '3jca', top_and(lna)[1]), w.inst('lndlchrk')], 'syl2anc', lnc)
    gvb = b([b([gv], 'fveq2d', '( abs ` ( g ` v ) ) = %s' % lnc.split(' <_ ', 1)[0]), ln], 'eqbrtrd', '( abs ` ( g ` v ) ) <_ %s' % KL)
    ballv = a([gvb], 'ralrimiva', 'A. v e. %s ( abs ` ( g ` v ) ) <_ %s' % (FR, KL))
    cgu = w.s([w.s([w.s([], 'fveq2', '( u = v -> ( g ` u ) = ( g ` v ) )')], 'fveq2d', '( u = v -> ( abs ` ( g ` u ) ) = ( abs ` ( g ` v ) ) )')], 'breq1d',
              '( u = v -> ( ( abs ` ( g ` u ) ) <_ %s <-> ( abs ` ( g ` v ) ) <_ %s ) )' % (KL, KL))
    ballu = a([ballv, w.s([cgu], 'cbvralvw', '( A. u e. %s ( abs ` ( g ` u ) ) <_ %s <-> A. v e. %s ( abs ` ( g ` v ) ) <_ %s )' % (FR, KL, FR, KL))], 'sylibr', 'A. u e. %s ( abs ` ( g ` u ) ) <_ %s' % (FR, KL))
    # KL real and nonnegative
    nn_ = a([L(nx)], 'simpld', 'N e. NN')
    at2 = a([a([a([L(tr)], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR'), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Ar)], 'readdcld', '( ( abs ` T ) + 2 ) e. RR')
    XT = '( N x. ( ( abs ` T ) + 2 ) )'
    xr = a([a([nn_], 'nnred', 'N e. RR'), at2], 'remulcld', '%s e. RR' % XT)
    ck = Closure(w, Ar, {'N': ('RR', a([nn_], 'nnred', 'N e. RR')), '( abs ` T )': ('RR', a([a([L(tr)], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR'))})
    ck.atom('( abs ` T )')
    ck.have('N', 'ge1', a([nn_], 'nnge1d', '1 <_ N'))
    ck.have('( abs ` T )', 'ge0', a([a([L(tr)], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )'))
    n1 = a([nn_], 'nnge1d', '1 <_ N'); t2 = linarith(w, Ar, [a([a([L(tr)], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')], '1 <_ ( ( abs ` T ) + 2 )', closure=ck)
    x1 = a([w.s([], '1red', '( %s -> 1 e. RR )' % Ar), w.s([], '1red', '( %s -> 1 e. RR )' % Ar), a([nn_], 'nnred', 'N e. RR'), at2, w.s([], '0le1', '0 <_ 1') and w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % Ar),
            w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % Ar), n1, t2], 'lemul12ad', '( 1 x. 1 ) <_ %s' % XT)
    x1b = a([w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % Ar), x1], 'eqbrtrrd', '1 <_ %s' % XT)
    lg0 = a([xr, x1b, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` %s )' % XT)
    xrp = a([xr, a([w.s([], '0red', '( %s -> 0 e. RR )' % Ar), w.s([], '1red', '( %s -> 1 e. RR )' % Ar), xr, w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % Ar), x1b], 'ltletrd', '0 < %s' % XT)], 'elrpd', '%s e. RR+' % XT)
    lgr = a([xrp], 'relogcld', '( log ` %s ) e. RR' % XT)
    kc = Closure(w, Ar, {'( log ` %s )' % XT: ('RR', lgr)}); kc.atom('( log ` %s )' % XT)
    klr = kc.mem(KL, 'RR')
    kl0 = linarith(w, Ar, [lg0], '0 <_ %s' % KL, closure=kc)
    # Cauchy estimate and Cauchy's formula
    sqh = a([L(s0c), tp, g1], '3jca', '( %s e. CC /\\ t e. RR+ /\\ %s C_ %s )' % (SS, SQT, O13))
    CE = tsub(S['kdcest'], {'F': 'g', 'D': O13, 'P': SS, 'R': 't', 'M': KL})
    cea, cec = split_imp(CE)
    ce = a([a([a([L(hg), w.inst('simpl')], 'syl', 'g e. ( %s -cn-> CC )' % O13), sqh], 'jca', top_and(cea)[0]), a([L(kk), klr, ballu], '3jca', top_and(cea)[1]), w.inst('kdcest')], 'syl2anc', cec)
    CD = tsub(S['kdcdn'], {'F': 'g', 'D': O13, 'P': SS, 'R': 't'})
    cda, cdc = split_imp(CD)
    cd = a([L(hg), sqh, L(kk), w.inst('kdcdn')], 'syl3anc', cdc)
    TCg = TC('g', SS, 't', 'K')
    DN = '( ( ( CC Dn g ) ` K ) ` %s )' % SS
    fk = a([L(kk), w.inst('faccl')], 'syl', '( ! ` K ) e. NN')
    fkc = a([fk], 'nncnd', '( ! ` K ) e. CC'); fkr = a([fk], 'nnred', '( ! ` K ) e. RR'); fk0 = a([a([fk], 'nnrpd', '( ! ` K ) e. RR+')], 'rpge0d', '0 <_ ( ! ` K )')
    tcr_ = cec.split(' <_ ', 1)[0]
    # TC e. CC from Cauchy's formula: TC = DN / K!  -- instead use abscl on TC via its bound: need TC e. CC; get from rectintccl-free route: DN = K! TC and DN e. CC
    hk = a([L(hg), L(kk), w.inst('kdholdn')], 'syl2anc', HOLF('( ( CC Dn g ) ` K )', O13))
    s0o = a([g1, a([q2['inp'], w.inst('crectinp')], 'syl', '%s e. %s' % (SS, SQT))], 'sseldd', '%s e. %s' % (SS, O13))
    dnc = a([a([a([hk, w.inst('simpl')], 'syl', '( ( CC Dn g ) ` K ) e. ( %s -cn-> CC )' % O13), w.inst('cncff')], 'syl', '( ( CC Dn g ) ` K ) : %s --> CC' % O13), s0o], 'ffvelcdmd', '%s e. CC' % DN)
    fkn = a([fk], 'nnne0d', '( ! ` K ) =/= 0')
    PSA = tsub(stmt('ef2psa'), {'F': 'g', 'D': O13, 'P': SS, 'E': 't'})
    psa_a, psa_c = split_imp(PSA)
    psa = a([L(hg), sqh, w.inst('ef2psa')], 'syl2anc', psa_c)
    MAPT = psa_c.split(' : NN0 --> CC')[0]
    idm = w.s([], 'id', '( m = K -> m = K )')
    body_m = MAPT[len('( m e. NN0 |-> '):-2]
    cm, vK = w.congr(body_m, {'m': 'K'}, 'm = K', {'m': idm})
    assert vK == TCg, (vK[:200], TCg[:200])
    tck = a([psa, L(kk)], 'ffvelcdmd', '( %s ` K ) e. CC' % MAPT)
    fvk = a([w.s([cm, w.s([], 'eqid', '%s = %s' % (MAPT, MAPT))], 'fvmptg', '( ( K e. NN0 /\\ %s e. _V ) -> ( %s ` K ) = %s )' % (vK, MAPT, vK)) and L(kk),
             w.s([w.s([], 'ovex', '%s e. _V' % vK)], 'a1i', '( %s -> %s e. _V )' % (Ar, vK)),
             w.s([cm, w.s([], 'eqid', '%s = %s' % (MAPT, MAPT))], 'fvmptg', '( ( K e. NN0 /\\ %s e. _V ) -> ( %s ` K ) = %s )' % (vK, MAPT, vK))], 'syl2anc', '( %s ` K ) = %s' % (MAPT, vK))
    tcc = a([fvk, tck], 'eqeltrrd', '%s e. CC' % TCg)
    # abs DN = K! abs TC <_ K! ( 2 KL / t ^ K ) <_ K! ( 2 3^K KL )
    ab1 = a([a([cd], 'fveq2d', '( abs ` %s ) = ( abs ` ( ( ! ` K ) x. %s ) )' % (DN, TCg)), a([fkc, tcc], 'absmuld', '( abs ` ( ( ! ` K ) x. %s ) ) = ( ( abs ` ( ! ` K ) ) x. ( abs ` %s ) )' % (TCg, TCg)),
             a([a([fkr, fk0], 'absidd', '( abs ` ( ! ` K ) ) = ( ! ` K )')], 'oveq1d', '( ( abs ` ( ! ` K ) ) x. ( abs ` %s ) ) = ( ( ! ` K ) x. ( abs ` %s ) )' % (TCg, TCg))],
            '3eqtrd', '( abs ` %s ) = ( ( ! ` K ) x. ( abs ` %s ) )' % (DN, TCg))
    B1 = '( ( 2 x. %s ) / ( t ^ K ) )' % KL
    B2 = '( ( 2 x. ( 3 ^ K ) ) x. %s )' % KL
    tk = a([tp, a([L(kk)], 'nn0zd', 'K e. ZZ')], 'rpexpcld', '( t ^ K ) e. RR+')
    it = '( 1 / t )'
    itr = a([tp], 'rprecred', '%s e. RR' % it)
    it0 = a([a([tp], 'rpreccld', '%s e. RR+' % it)], 'rpge0d', '0 <_ %s' % it)
    i3a = a([w.s([], '1red', '( %s -> 1 e. RR )' % Ar), w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % Ar), tp], 'ledivmuld', '( ( 1 / t ) <_ 3 <-> 1 <_ ( t x. 3 ) )')
    i3b = linarith(w, Ar, [t13], '1 <_ ( t x. 3 )', closure=ca)
    i3 = a([i3b, i3a], 'mpbird', '( 1 / t ) <_ 3')
    ik = a([itr, w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % Ar), L(kk), it0, i3], 'leexp1ad', '( %s ^ K ) <_ ( 3 ^ K )' % it)
    er_ = a([a([ttr], 'recnd', 't e. CC'), a([tp], 'rpne0d', 't =/= 0'), a([L(kk)], 'nn0zd', 'K e. ZZ')], 'exprecd', '( %s ^ K ) = ( 1 / ( t ^ K ) )' % it)
    two = a([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Ar), klr], 'remulcld', '( 2 x. %s ) e. RR' % KL)
    two0 = a([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Ar), klr, w.s([w.s([], '0le2', '0 <_ 2')], 'a1i', '( %s -> 0 <_ 2 )' % Ar), kl0], 'mulge0d', '0 <_ ( 2 x. %s )' % KL)
    d1 = a([a([two], 'recnd', '( 2 x. %s ) e. CC' % KL), a([tk], 'rpcnd', '( t ^ K ) e. CC'), a([tk], 'rpne0d', '( t ^ K ) =/= 0')], 'divrecd', '%s = ( ( 2 x. %s ) x. ( 1 / ( t ^ K ) ) )' % (B1, KL))
    d2 = a([d1, a([er_], 'eqcomd', '( 1 / ( t ^ K ) ) = ( %s ^ K )' % it)], 'T.', 'T.') if False else a([d1, a([a([er_], 'eqcomd', '( 1 / ( t ^ K ) ) = ( %s ^ K )' % it)], 'oveq2d', '( ( 2 x. %s ) x. ( 1 / ( t ^ K ) ) ) = ( ( 2 x. %s ) x. ( %s ^ K ) )' % (KL, KL, it))], 'eqtrd', '%s = ( ( 2 x. %s ) x. ( %s ^ K ) )' % (B1, KL, it))
    l1 = a([a([itr, L(kk)], 'reexpcld', '( %s ^ K ) e. RR' % it), a([w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % Ar), L(kk)], 'reexpcld', '( 3 ^ K ) e. RR'), two, two0, ik], 'lemul2ad',
           '( ( 2 x. %s ) x. ( %s ^ K ) ) <_ ( ( 2 x. %s ) x. ( 3 ^ K ) )' % (KL, it, KL))
    cr = Closure(w, Ar, {KL: ('RR', klr), '( 3 ^ K )': ('RR', a([w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % Ar), L(kk)], 'reexpcld', '( 3 ^ K ) e. RR'))})
    cr.atom(KL); cr.atom('( 3 ^ K )')
    r2 = ringeq(w, Ar, '( ( 2 x. %s ) x. ( 3 ^ K ) )' % KL, B2, cr)
    bb = a([a([d2, l1], 'eqbrtrd', '%s <_ ( ( 2 x. %s ) x. ( 3 ^ K ) )' % (B1, KL)), r2], 'breqtrd', '%s <_ %s' % (B1, B2))
    tb = a([a([tcc], 'abscld', '( abs ` %s ) e. RR' % TCg), a([two, tk], 'rerpdivcld', '%s e. RR' % B1), cr.mem(B2, 'RR'), ce, bb], 'letrd', '( abs ` %s ) <_ %s' % (TCg, B2))
    fb = a([a([tcc], 'abscld', '( abs ` %s ) e. RR' % TCg), cr.mem(B2, 'RR'), fkr, fk0, tb], 'lemul2ad', '( ( ! ` K ) x. ( abs ` %s ) ) <_ ( ( ! ` K ) x. %s )' % (TCg, B2))
    goal = a([ab1, fb], 'eqbrtrd', '( abs ` %s ) <_ ( ( ! ` K ) x. %s )' % (DN, B2))
    w.qed([frt, goal], 'rexlimddv', S['kdrepb'])
    return run(w)





if __name__ == '__main__':
    gen_repb()
