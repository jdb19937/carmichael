"""Sortie CEN2: the small regime (cen2lg1, cen2small; Lean Census censusCount_le_of_small 1466-1604)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def c_(w, ctx):
    return lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (ctx, f))


def gen_L1():
    w = W('cen2lg1', 'For ` 1 <_ V ` and ` 2 <_ Z ` : ` 1 <_ log ( Z ( V + 2 ) ) ` (Lean Census ` h L 1 ` , from ` e < 3 < 6 ` ).')
    A0, C0 = split_imp(S['cen2lg1'])
    s = c_(w, A0)
    vr = s([], 'simpll', 'V e. RR'); v1 = s([], 'simplr', '1 <_ V'); zr = s([], 'simprl', 'Z e. RR'); z2 = s([], 'simprr', '2 <_ Z')
    c0 = Closure(w, A0, {'V': ('RR', vr), 'Z': ('RR', zr)})
    zp = linarith(w, A0, [z2], '0 < Z', closure=c0); c0.have('Z', 'gt0', zp)
    vp = linarith(w, A0, [v1], '0 < ( V + 2 )', closure=c0); c0.have('( V + 2 )', 'gt0', vp)
    WZ = '( Z x. ( V + 2 ) )'
    LL_ = LOGZ('Z', 'V')
    six = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), zr, s([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), c0.mem('( V + 2 )', 'RR'),
             s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), c0.ge0('3'), z2, linarith(w, A0, [v1], '3 <_ ( V + 2 )', closure=c0)], 'lemul12ad',
            '( 2 x. 3 ) <_ %s' % WZ)
    e3 = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    c0.have('_e', 'RR', s([w.s([], 'ere', '_e e. RR')], 'a1i', '_e e. RR'))
    c0.atom(WZ)
    c0.have(WZ, 'RR', c0.mem(WZ, 'RR'))
    ele = linarith(w, A0, [six, s([e3], 'a1i', '_e < 3')], '_e <_ %s' % WZ, closure=c0)
    lg = s([ele, s([s([w.s([], 'epr', '_e e. RR+')], 'a1i', '_e e. RR+'), c0.mem(WZ, 'RR+')], 'logled', '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (WZ, LL_))], 'mpbid', '( log ` _e ) <_ %s' % LL_)
    w.qed([s([w.s([], 'loge', '( log ` _e ) = 1')], 'a1i', '( log ` _e ) = 1'), lg], 'eqbrtrrd', S['cen2lg1'])
    return run(w)


def gen_small():
    w = W('cen2small', 'The small regime: if ` ( 1 - S ) log ( Z ( V + 2 ) ) <_ 10 ^ -10 ` then at most 13 primitive characters of modulus at most ` Z ` have a zero in ` [ S , 1 ] x [ -V , V ] ` (Lean Census ` censusCount_le_of_small ` , threshold ` 10 ^ -10 ` ; the width is ` D = 10 ^ -10 / L ` , which is at most ` 1 / 40 ` since ` L >_ 1 ` ).')
    A0, C0 = split_imp(S['cen2small'])
    s = c_(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    sr = g('S e. RR'); vr = g('V e. RR'); zr = g('Z e. RR'); s1 = g('S <_ 1'); v1 = g('1 <_ V'); z2 = g('2 <_ Z'); s39 = g('%s <_ S' % F3940)
    LL_ = LOGZ('Z', 'V')
    hs = g('( ( 1 - S ) x. %s ) <_ %s' % (LL_, THR))
    K = '( |_ ` Z )'
    kz = s([zr], 'flcld', '%s e. ZZ' % K)
    k2 = s([s([zr, s([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), w.inst('flge')], 'syl2anc', '( 2 <_ Z <-> 2 <_ %s )' % K), z2], 'mpbird', '2 <_ %s' % K) if False else \
        s([z2, s([zr, s([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), w.inst('flge')], 'syl2anc', '( 2 <_ Z <-> 2 <_ %s )' % K)], 'mpbid', '2 <_ %s' % K)
    kle = s([zr, w.inst('flle')], 'syl', '%s <_ Z' % K)
    l1 = s([s([vr, v1], 'jca', '( V e. RR /\\ 1 <_ V )'), s([zr, z2], 'jca', '( Z e. RR /\\ 2 <_ Z )'), w.inst('cen2lg1')], 'syl2anc', '1 <_ %s' % LL_)
    c0 = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'Z': ('RR', zr), K: ('ZZ', kz)})
    zp = linarith(w, A0, [z2], '0 < Z', closure=c0); c0.have('Z', 'gt0', zp)
    vp = linarith(w, A0, [v1], '0 < ( V + 2 )', closure=c0); c0.have('( V + 2 )', 'gt0', vp)
    lrp = s([c0.mem(LL_, 'RR'), linarith(w, A0, [l1], '0 < %s' % LL_, closure=c0)], 'elrpd', '%s e. RR+' % LL_)
    c0.have(LL_, 'RR+', lrp); c0.atom(LL_)
    D = '( %s / %s )' % (THR, LL_)
    drp = c0.mem(D, 'RR+')
    dl = s([c0.mem(THR, 'CC'), c0.mem(LL_, 'CC'), s([lrp], 'rpne0d', '%s =/= 0' % LL_)], 'divcan1d', '( %s x. %s ) = %s' % (D, LL_, THR))
    c0.atom(D); c0.have(D, 'RR+', drp)
    dle = nlinarith(w, A0, [dl, l1, s([drp], 'rpge0d', '0 <_ %s' % D)], '%s <_ %s' % (D, F140), closure=c0)
    sd0 = s([hs, s([dl], 'eqcomd', '%s = ( %s x. %s )' % (THR, D, LL_))], 'breqtrd', '( ( 1 - S ) x. %s ) <_ ( %s x. %s )' % (LL_, D, LL_))
    sd = s([sd0, s([c0.mem('( 1 - S )', 'RR'), c0.mem(D, 'RR'), lrp], 'lemul1d', '( ( 1 - S ) <_ %s <-> ( ( 1 - S ) x. %s ) <_ ( %s x. %s ) )' % (D, LL_, D, LL_))], 'mpbird', '( 1 - S ) <_ %s' % D)
    PARSD = tokrep(PARS, {'D': D})
    pars = s([s([drp, dle], 'jca', '( %s e. RR+ /\\ %s <_ %s )' % (D, D, F140)), s([s([vr, v1], 'jca', '( V e. RR /\\ 1 <_ V )'), s([zr, z2], 'jca', '( Z e. RR /\\ 2 <_ Z )')], 'jca',
               '( ( V e. RR /\\ 1 <_ V ) /\\ ( Z e. RR /\\ 2 <_ Z ) )'), s([dl], 'eqled', '( %s x. %s ) <_ %s' % (D, LL_, THR))], '3jca', PARSD)
    # the union of the tail
    Bm = BC('S', 'V', 'm')
    UNK = 'U_ m e. ( 2 ... %s ) %s' % (K, Bm)
    TL = tokrep(S['cen2tail'], {'K': K})
    tl = s([kz, w.inst('cen2tail')], 'syl', split_imp(TL)[1])
    ufi = s([tl], 'simpld', '%s e. Fin' % UNK)
    ueq = s([tl], 'simprd', '( # ` %s ) = sum_ m e. ( 2 ... %s ) ( # ` %s )' % (UNK, K, Bm))
    # contradiction from 13 elements
    HU = '( # ` %s )' % UNK
    A13 = '( %s /\\ %s <_ %s )' % (A0, N13, HU)
    SS = '( s C_ %s /\\ ( # ` s ) = %s )' % (UNK, N13)
    C3 = '( %s /\\ %s )' % (A0, SS)
    c3 = c_(w, C3)
    sfin = c3([lift(w, ufi, C3), c3([], 'simprl', 's C_ %s' % UNK), w.inst('ssfi')], 'syl2anc', 's e. Fin')
    A3a = '( %s /\\ b e. s )' % C3
    a3 = c_(w, A3a)
    au = a3([a3([], 'simpr', 'b e. s'), a3([a3([], 'simplrl', 's C_ %s' % UNK), w.inst('ssel')], 'syl', '( b e. s -> b e. %s )' % UNK)], 'mpd', 'b e. %s' % UNK)
    EM = 'E. m e. ( 2 ... %s ) b e. %s' % (K, Bm)
    em = a3([au, w.s([], 'eliun', '( b e. %s <-> %s )' % (UNK, EM))], 'sylib', EM)
    ral1 = c3([em], 'ralrimiva', 'A. b e. s %s' % EM)
    Bfb = BC('S', 'V', '( f ` b )'); Bfc = BC('S', 'V', '( f ` c )'); Bfa = BC('S', 'V', '( f ` a )')
    eqm = 'm = ( f ` b )'
    idm = w.s([], 'id', '( %s -> %s )' % (eqm, eqm))
    stm, bf_ = w.wcongr('b e. %s' % Bm, {'m': '( f ` b )'}, eqm, {'m': idm})
    assert bf_ == 'b e. %s' % Bfb, bf_
    FS = '( f : s --> ( 2 ... %s ) /\\ A. b e. s b e. %s )' % (K, Bfb)
    ac1 = w.s([stm], 'ac6sfi', '( ( s e. Fin /\\ A. b e. s %s ) -> E. f %s )' % (EM, FS))
    ef = c3([sfin, ral1, ac1], 'syl2anc', 'E. f %s' % FS)
    C4 = '( %s /\\ %s )' % (C3, FS)
    c4 = c_(w, C4)
    fr4 = c4([], 'simprl', 'f : s --> ( 2 ... %s )' % K)
    al4 = c4([], 'simprr', 'A. b e. s b e. %s' % Bfb)

    def at(ctx, x, xm):
        """( ctx -> x e. BC(f x) ) from x e. s"""
        eq = 'b = %s' % x
        idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
        st, bx = w.wcongr('b e. %s' % Bfb, {'b': x}, eq, {'b': idx})
        rs = w.s([st], 'rspcv', '( %s e. s -> ( A. b e. s b e. %s -> %s ) )' % (x, Bfb, bx))
        return w.s([xm, lift(w, al4, ctx), rs], 'sylc', '( %s -> %s )' % (ctx, bx)), bx
    A4a = '( %s /\\ c e. s )' % C4
    a4 = c_(w, A4a)
    an = a4([], 'simpr', 'c e. s')
    abf, _ = at(A4a, 'c', an)
    Zc = ZFB('S', 'V', '( f ` c )', 'c')
    DNf = '( Base ` ( DChr ` ( f ` c ) ) )'
    PHY = lambda y: '( ( ( f ` c ) DChrCond %s ) = ( f ` c ) /\\ %s =/= (/) )' % (y, ZFB('S', 'V', '( f ` c )', y))
    eqy = 'y = c'
    idy = w.s([], 'id', '( %s -> %s )' % (eqy, eqy))
    sty, py = w.wcongr(PHY('y'), {'y': 'c'}, eqy, {'y': idy})
    er = w.s([sty], 'elrab', '( c e. %s <-> ( c e. %s /\\ %s ) )' % (Bfc, DNf, PHY('c')))
    am = a4([abf, er], 'sylib', '( c e. %s /\\ %s )' % (DNf, PHY('c')))
    zn = a4([a4([am], 'simprd', PHY('c'))], 'simprd', '%s =/= (/)' % Zc)
    eq_ = a4([zn, w.s([], 'n0', '( %s =/= (/) <-> E. q q e. %s )' % (Zc, Zc))], 'sylib', 'E. q q e. %s' % Zc)
    A4q = '( %s /\\ q e. %s )' % (A4a, Zc)
    q4 = c_(w, A4q)
    qm = q4([], 'simpr', 'q e. %s' % Zc)
    qb = q4([qm, w.inst('elrabi')], 'syl', 'q e. %s' % BOX('S', 'V'))
    ZBQ = tokrep(S['cen2zb'], {'O': 'q'})
    qzb = q4([q4([lift(w, sr, A4q), lift(w, vr, A4q)], 'jca', '( S e. RR /\\ V e. RR )'), qb, w.inst('cen2zb')], 'syl2anc', split_imp(ZBQ)[1])
    qc = q4([qzb], 'simp1d', 'q e. CC')
    ZP = 'p e. %s' % Zc
    ep = w.s([w.s([], 'eleq1', '( p = q -> ( p e. %s <-> q e. %s ) )' % (Zc, Zc))], 'rspcev', '( ( q e. CC /\\ q e. %s ) -> E. p e. CC %s )' % (Zc, ZP))
    epq = q4([qc, qm, ep], 'syl2anc', 'E. p e. CC %s' % ZP)
    ep2 = w.s([w.s([epq], 'ex', '( %s -> ( q e. %s -> E. p e. CC %s ) )' % (A4a, Zc, ZP))], 'exlimdv', '( %s -> ( E. q q e. %s -> E. p e. CC %s ) )' % (A4a, Zc, ZP))
    epa = a4([eq_, ep2], 'mpd', 'E. p e. CC %s' % ZP)
    ral2 = c4([epa], 'ralrimiva', 'A. c e. s E. p e. CC %s' % ZP)
    eqp = 'p = ( g ` c )'
    GS = '( g : s --> CC /\\ A. c e. s ( g ` c ) e. %s )' % Zc
    ac2 = w.s([w.s([], 'eleq1', '( %s -> ( %s <-> ( g ` c ) e. %s ) )' % (eqp, ZP, Zc))], 'ac6sfi', '( ( s e. Fin /\\ A. c e. s E. p e. CC %s ) -> E. g %s )' % (ZP, GS))
    eg = c4([lift(w, sfin, C4), ral2, ac2], 'syl2anc', 'E. g %s' % GS)
    C5 = '( %s /\\ %s )' % (C4, GS)
    c5 = c_(w, C5)
    A5a = '( %s /\\ a e. s )' % C5
    a5 = c_(w, A5a)
    an5 = a5([], 'simpr', 'a e. s')
    Za = ZFB('S', 'V', '( f ` a )', 'a')
    gs5 = c5([], 'simprr', 'A. c e. s ( g ` c ) e. %s' % Zc)
    eqc = 'c = a'
    idc = w.s([], 'id', '( %s -> %s )' % (eqc, eqc))
    stc, gx = w.wcongr('( g ` c ) e. %s' % Zc, {'c': 'a'}, eqc, {'c': idc})
    assert gx == '( g ` a ) e. %s' % Za, gx
    rsc = w.s([stc], 'rspcv', '( a e. s -> ( A. c e. s ( g ` c ) e. %s -> %s ) )' % (Zc, gx))
    ga = a5([an5, lift(w, gs5, A5a), rsc], 'sylc', gx)
    fa5 = a5([lift(w, fr4, A5a), an5], 'ffvelcdmd', '( f ` a ) e. ( 2 ... %s )' % K)
    abf5, _ = at(A5a, 'a', an5)
    FAMT = tokrep(S['cen2fam'], {'N': '( f ` a )', 'X': 'a', 'R': '( g ` a )', 'K': K, 'D': D})
    fa_, fc_ = split_imp(FAMT)
    q1, q2, q3 = top_and(fa_)
    fm = a5([a5([a5([fa5, lift(w, kle, A5a)], 'jca', q1), a5([abf5, ga], 'jca', q2),
                  a5([a5([lift(w, sr, A5a), lift(w, vr, A5a), lift(w, zr, A5a)], '3jca', '( S e. RR /\\ V e. RR /\\ Z e. RR )'),
                      a5([lift(w, c0.mem(D, 'RR'), A5a), lift(w, sd, A5a)], 'jca', '( %s e. RR /\\ ( 1 - S ) <_ %s )' % (D, D))], 'jca', q3)], '3jca', fa_), w.inst('cen2fam')], 'syl', fc_)
    famr = c5([fm], 'ralrimiva', 'A. a e. s %s' % fc_)
    N13T = tokrep(S['cen2n13'], {'J': 's', 'M': 'f', 'P': 'g', 'D': D})
    X = N13T[3:]
    assert ('A. a e. s %s' % fc_) in X
    hx = c5([c5([c5([lift(w, sfin, C5), c5([], 'simplrr', '( # ` s ) = %s' % N13) if False else lift(w, c3([], 'simprr', '( # ` s ) = %s' % N13), C5)], 'jca', '( s e. Fin /\\ ( # ` s ) = %s )' % N13),
                     famr], 'jca', top_and(X)[0]), lift(w, pars, C5)], 'jca', X)
    nx = w.s([], 'cen2n13', N13T)
    f5 = c5([hx, w.s([nx], 'pm2.21i', '( %s -> F. )' % X)], 'syl', 'F.')
    f4 = w.s([w.s([f5], 'ex', '( %s -> ( %s -> F. ) )' % (C4, GS))], 'exlimdv', '( %s -> ( E. g %s -> F. ) )' % (C4, GS))
    f4b = c4([eg, f4], 'mpd', 'F.')
    f3 = w.s([w.s([f4b], 'ex', '( %s -> ( %s -> F. ) )' % (C3, FS))], 'exlimdv', '( %s -> ( E. f %s -> F. ) )' % (C3, FS))
    f3b = c3([ef, f3], 'mpd', 'F.')
    f2 = w.s([w.s([f3b], 'ex', '( %s -> ( %s -> F. ) )' % (A0, SS))], 'exlimdv', '( %s -> ( E. s %s -> F. ) )' % (A0, SS))
    a13 = c_(w, A13)
    SUB = tokrep(S['cen2sub'], {'A': UNK, 'N': N13})
    sub = a13([a13([lift(w, ufi, A13), a13([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0') if False else c_(w, A13)([], 'id', '%s e. NN0' % N13) if False else
                    w.s([], 'nn0cn', 'x') if False else a13([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '3nn0', '3 e. NN0')], 'decnncl', '; 1 3 e. NN') if False else
                                                          w.s([], '13nn0', '%s e. NN0' % N13) if False else None], 'id', 'x') if False else None,
                    a13([], 'simpr', '%s <_ %s' % (N13, HU))], 'id', 'x') if False else None], 'id', 'x') if False else None
    n13 = w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '3nn0', '3 e. NN0')], 'deccl', '%s e. NN0' % N13)
    sub = a13([lift(w, ufi, A13), a13([n13], 'a1i', '%s e. NN0' % N13), a13([], 'simpr', '%s <_ %s' % (N13, HU)), w.inst('cen2sub')], 'syl3anc', split_imp(SUB)[1])
    fin_ = a13([sub, lift(w, f2, A13)], 'mpd', 'F.')
    no13 = w.s([fin_, w.s([w.s([], 'fal', '-. F.')], 'a1i', '( %s -> -. F. )' % A13)], 'pm2.65da', '( %s -> -. %s <_ %s )' % (A0, N13, HU))
    hur = s([s([ufi, w.inst('hashcl')], 'syl', '%s e. NN0' % HU)], 'nn0zd', '%s e. ZZ' % HU)
    lt = s([no13, s([s([hur], 'zred', '%s e. RR' % HU), c0.mem(N13, 'RR')], 'ltnled', '( %s < %s <-> -. %s <_ %s )' % (HU, N13, N13, HU))], 'mpbird', '%s < %s' % (HU, N13))
    le12 = s([lt, s([hur, c0.mem(N13, 'ZZ'), w.inst('zltlem1')], 'syl2anc', '( %s < %s <-> %s <_ ( %s - 1 ) )' % (HU, N13, HU, N13))], 'mpbid', '%s <_ ( %s - 1 )' % (HU, N13))
    # the census = the modulus-1 term + the tail
    CN = CNT('S', 'V', K)
    B1 = BC('S', 'V', '1')
    kuz = s([s([], '1zzd', '1 e. ZZ'), kz, linarith(w, A0, [k2], '1 <_ %s' % K, closure=c0)], 'eluz2d', '%s e. ( ZZ>= ` 1 )' % K) if False else None
    kuz = s([s([s([], '1zzd', '1 e. ZZ'), kz, linarith(w, A0, [k2], '1 <_ %s' % K, closure=c0)], '3jca', '( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s )' % (K, K)),
             w.s([], 'eluz2', '( %s e. ( ZZ>= ` 1 ) <-> ( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s ) )' % (K, K, K))], 'sylibr', '%s e. ( ZZ>= ` 1 )' % K)
    A1 = '( %s /\\ m e. ( 1 ... %s ) )' % (A0, K)
    a1 = c_(w, A1)
    mn = a1([a1([], 'simpr', 'm e. ( 1 ... %s )' % K), w.inst('elfznn')], 'syl', 'm e. NN')
    hbm = a1([a1([a1([a1([mn, w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ m )' % (Bm, Bm))], 'simpld', '%s e. Fin' % Bm), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % Bm)],
             'nn0cnd', '( # ` %s ) e. CC' % Bm)
    eq1 = 'm = 1'
    id1 = w.s([], 'id', '( %s -> %s )' % (eq1, eq1))
    st1, b1_ = w.congr('( # ` %s )' % Bm, {'m': '1'}, eq1, {'m': id1})
    assert b1_ == '( # ` %s )' % B1
    f1p = s([kuz, hbm, st1], 'fsum1p', '%s = ( ( # ` %s ) + sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) )' % (CN, B1, K, Bm))
    s12 = s([s([s([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2')], 'oveq1d', '( ( 1 + 1 ) ... %s ) = ( 2 ... %s )' % (K, K))], 'sumeq1d',
            'sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) = sum_ m e. ( 2 ... %s ) ( # ` %s )' % (K, Bm, K, Bm))
    TLS = 'sum_ m e. ( 2 ... %s ) ( # ` %s )' % (K, Bm)
    dec_ = s([f1p, s([s12], 'oveq2d', '( ( # ` %s ) + sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) ) = ( ( # ` %s ) + %s )' % (B1, K, Bm, B1, TLS))], 'eqtrd', '%s = ( ( # ` %s ) + %s )' % (CN, B1, TLS))
    b1 = s([s([], '1nn', '1 e. NN') if False else s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ 1 )' % (B1, B1))
    for at, st in ((CN, None), ('( # ` %s )' % B1, None), (TLS, None), (HU, None)):
        c0.atom(at)
    c0.have('( # ` %s )' % B1, 'RR', s([s([s([b1], 'simpld', '%s e. Fin' % B1), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % B1)], 'nn0red', '( # ` %s ) e. RR' % B1))
    c0.have(HU, 'RR', s([hur], 'zred', '%s e. RR' % HU))
    hurr = s([hur], 'zred', '%s e. RR' % HU)
    tlr = s([ueq, hurr], 'eqeltrrd', '%s e. RR' % TLS)
    c0.have(TLS, 'RR', tlr)
    b1r = s([s([s([b1], 'simpld', '%s e. Fin' % B1), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % B1)], 'nn0red', '( # ` %s ) e. RR' % B1)
    c0.have(CN, 'RR', s([dec_, s([b1r, tlr], 'readdcld', '( ( # ` %s ) + %s ) e. RR' % (B1, TLS))], 'eqeltrd', '%s e. RR' % CN))
    fin2 = linarith(w, A0, [dec_, ueq, s([b1], 'simprd', '( # ` %s ) <_ 1' % B1), le12], '%s <_ %s' % (CN, N13), closure=c0)
    w.lines[-1:] = w.lines[-1:]
    w.qed([fin2], 'id', S['cen2small']) if False else None
    last = w.lines.pop()
    name, rest = last.split(':', 1)
    w.lines.append('qed:' + rest)
    return run(w)


if __name__ == '__main__':
    gen_L1()
    gen_small()
