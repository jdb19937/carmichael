"""Sortie ZC1: the box count for nonprincipal characters (zc1cnt, Lean zeroCountBox_le_of_ne_one) and the E instances of zffin/zcmono."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c0lib import hyp
from c8_o import numst
from c9_b import decode
from c10_f import crfacts, clo
import c9_h
patch(c9_h)
from c9_h import lf_hol
import zc1_c, zc1_d, zc1_e, zc1_i, zc1_j, zc1_k, zc1_l
from zc1_j import two_nz
import lin
lin.FASTPATH = True

H = '( 1 / 2 )'
ZFE = ZF(E, H, 'T')
C64 = '; ; ; 6 4 0 0'
S['zc1cnt'] = '( ( %s /\\ ( T e. RR /\\ 1 <_ T ) ) -> %s <_ ( %s x. ( T x. ( log ` ( N x. ( T + 2 ) ) ) ) ) )' % (CHI, ZC(E, H, 'T'), C64)
S['ezf'] = '( ( %s /\\ ( ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ T e. RR ) ) -> ( %s e. Fin /\\ A. q e. %s ( %s holord q ) e. NN ) )' % (NX, ZF(E, 'A', 'T'), ZF(E, 'A', 'T'), E)


def e_h2(w, A0, nx, Nv='N', Xv='X'):
    """( A0 -> ( HOL(E, HP0) /\\ ( E ` 2 ) =/= 0 ) ) for E = ( Nv DChrLF Xv ); nx : ( A0 -> NX[Nv, Xv] )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    E_ = '( %s DChrLF %s )' % (Nv, Xv)
    NX_ = tsub(NX, {'N': Nv, 'X': Xv})
    hol = s([nx, w.inst('zl1ehol')], 'syl', HOLF(E_, HP0))
    def ctr():
        return s([s([nx, s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR')], 'jca', '( %s /\\ 0 e. RR )' % NX_), w.inst('ectr')], 'syl',
                 '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % E_), '( 1 / 2 )'
    lb = two_nz(w, A0, E_, ctr)
    E2 = '( %s ` 2 )' % E_
    ch2 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( 2 e. %s <-> ( 2 e. CC /\\ 0 < ( Re ` 2 ) ) )' % HP0)
    re2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    h2 = s([s([s([], '2cnd', '2 e. CC'), s([lin8(w, A0, [], '0 < 2', {}), re2], 'breqtrrd', '0 < ( Re ` 2 )')], 'jca', '( 2 e. CC /\\ 0 < ( Re ` 2 ) )'), ch2], 'mpbird', '2 e. %s' % HP0)
    e2c = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (E_, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (E_, HP0)), h2], 'ffvelcdmd', '%s e. CC' % E2)
    ae = s([e2c], 'abscld', '( abs ` %s ) e. RR' % E2)
    e2n = s([lin8(w, A0, [lb], '0 < ( abs ` %s )' % E2, {'( abs ` %s )' % E2: ae}), s([e2c, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (E2, E2))], 'mpbird', '%s =/= 0' % E2)
    return s([hol, e2n], 'jca', '( %s /\\ %s =/= 0 )' % (HOLF(E_, HP0), E2))


def gen_ezf():
    w = W('ezf', 'The box zero set of ` E = ( s - 1 ) L ( s , X ) ` off ` 1 ` is finite with orders in ` NN ` , every character (Lean ` finite_LZerosBox ` , ` one_le_analyticOrderNatAt_of_mem_zeroFinset ` ; ~ zffin , ~ ectr ).')
    A0 = ante_of(S['ezf'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', NX)
    hh = e_h2(w, A0, nx)
    Z = tsub(S['zffin'], {'F': E})
    za, zc = ante_of(Z)
    w.qed([s([hh, s([], 'simpr', top_and(za)[1])], 'jca', za), w.inst('zffin')], 'syl', S['ezf'])
    return run8(w)


def gen_zc1cnt():
    w = W('zc1cnt', 'Box zero count for nonprincipal characters (Lean ` zeroCountBox_le_of_ne_one ` , constant ` 1120 ` there): the zeros off ` 1 ` of ` E ` in ` [ 1 / 2 , 1 ] x. [ - T , T ] ` , ` T >_ 1 ` , have mass at most ` 6400 T log ( N ( T + 2 ) ) ` ( ~ boxcnt , ~ lchrzc8 , ~ zc1eord ).')
    A0 = ante_of(S['zc1cnt'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tt = s([], 'simpr', '( T e. RR /\\ 1 <_ T )')
    tr = s([tt, w.inst('simpl')], 'syl', 'T e. RR'); t1 = s([tt, w.inst('simpr')], 'syl', '1 <_ T')
    nx = s([chi, w.inst('simpl')], 'syl', NX)
    nn_ = s([nx, w.inst('simpl')], 'syl', 'N e. NN'); nr = s([nn_], 'nnred', 'N e. RR'); n1 = s([nn_], 'nnge1d', '1 <_ N')
    EZ = tsub(S['ezf'], {'A': H})
    eza, ezc = ante_of(EZ)
    hr = numst(w, A0, H, 'RR')
    ez = s([s([nx, s([s([hr, numst(w, A0, H, 'gt0'), lin8(w, A0, [], '%s <_ 1' % H, {})], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (H, H, H)), tr], 'jca', top_and(eza)[1])], 'jca', eza),
            w.inst('ezf')], 'syl', ezc)
    gfin = s([ez, w.inst('simpl')], 'syl', '%s e. Fin' % ZFE)
    alnn = s([ez, w.inst('simpr')], 'syl', 'A. q e. %s ( %s holord q ) e. NN' % (ZFE, E))
    Aq = '( %s /\\ q e. %s )' % (A0, ZFE)
    sq = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    Lq = lambda st: lift(w, st, Aq)
    BOXH = BOX(H, 'T')
    subr = w.s([w.s([], 'neeq1', '( r = q -> ( r =/= 1 <-> q =/= 1 ) )'), w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (E, E))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (E, E))],
               'anbi12d', '( r = q -> ( ( r =/= 1 /\\ ( %s ` r ) = 0 ) <-> ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (E, E))
    elq = w.s([subr], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (ZFE, BOXH, E))
    qq = sq([sq([], 'simpr', 'q e. %s' % ZFE), elq], 'sylib', '( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (BOXH, E))
    qb = sq([qq, w.inst('simpl')], 'syl', 'q e. %s' % BOXH); qn1 = sq([qq, w.inst('simprl')], 'syl', 'q =/= 1'); eq0 = sq([qq, w.inst('simprr')], 'syl', '( %s ` q ) = 0' % E)
    BA, BB = '( %s + ( _i x. -u T ) )' % H, '( 1 + ( _i x. T ) )'
    bac, rbA, ibA = crfacts(w, Aq, H, '-u T', numst(w, Aq, H, 'RR'), sq([Lq(tr)], 'renegcld', '-u T e. RR'))
    bbc, rbB, ibB = crfacts(w, Aq, '1', 'T', numst(w, Aq, '1', 'RR'), Lq(tr))
    dq = decode(w, Aq, qb, bac, bbc, BA, BB, BOXH, U='q')
    qc = dq[0]
    lvq = {'( Re ` q )': sq([qc], 'recld', '( Re ` q ) e. RR'), '( Im ` q )': sq([qc], 'imcld', '( Im ` q ) e. RR'), 'T': Lq(tr)}
    for e, st in (('( Re ` %s )' % BA, bac), ('( Im ` %s )' % BA, bac), ('( Re ` %s )' % BB, bbc), ('( Im ` %s )' % BB, bbc)):
        lvq[e] = sq([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hyq = [rbA, ibA, rbB, ibB] + dq[1:]
    rlo = lin8(w, Aq, hyq, '( 1 / 2 ) <_ ( Re ` q )', lvq); rhi = lin8(w, Aq, hyq, '( Re ` q ) <_ 1', lvq)
    iq = sq([sq([lin8(w, Aq, hyq, '-u T <_ ( Im ` q )', lvq), lin8(w, Aq, hyq, '( Im ` q ) <_ T', lvq)], 'jca', '( -u T <_ ( Im ` q ) /\\ ( Im ` q ) <_ T )'),
             sq([lvq['( Im ` q )'], Lq(tr)], 'absled', '( ( abs ` ( Im ` q ) ) <_ T <-> ( -u T <_ ( Im ` q ) /\\ ( Im ` q ) <_ T ) )')], 'mpbird', '( abs ` ( Im ` q ) ) <_ T')
    qhp = sq([sq([qc, lin8(w, Aq, [rlo], '0 < ( Re ` q )', lvq)], 'jca', '( q e. CC /\\ 0 < ( Re ` q ) )'),
              sq([sq([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbird', 'q e. %s' % HP0)
    EO = tsub(S['zc1eord'], {'P': 'q'})
    eoa, eoc = ante_of(EO)
    eo = sq([sq([Lq(chi), sq([qhp, qn1], 'jca', '( q e. %s /\\ q =/= 1 )' % HP0)], 'jca', eoa), w.inst('zc1eord')], 'syl', eoc)
    oeq = sq([eo, w.inst('simpl')], 'syl', top_and(eoc)[0])
    lq0 = sq([eq0, sq([eo, w.inst('simpr')], 'syl', top_and(eoc)[1])], 'mpbid', '( %s ` q ) = 0' % LFN)
    ennq = sq([alnn], 'r19.21bi' if False else 'r19.21bi', '( %s holord q ) e. NN' % E) if False else w.s([alnn], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Aq, E))
    lnn = sq([oeq, ennq], 'eqeltrrd', '( %s holord q ) e. NN' % LFN)
    # sum over ZFE of E holord = sum of LFN holord
    se = s([oeq], 'sumeq2dv', '%s = %s' % (MASS(ZFE, E), MASS(ZFE, LFN)))
    # boxcnt at ph := A0
    PH = A0
    BH = [tsub(x, {'ph': PH, 'G': ZFE, 'W': HO(LFN), 'A': 'N', 'K': '; ; 8 0 0'}) for x in zc1_l.BXH]
    b1 = gfin
    b2 = sq([sq([lnn], 'nnred', '( %s holord q ) e. RR' % LFN), sq([sq([lnn], 'nnnn0d', '( %s holord q ) e. NN0' % LFN)], 'nn0ge0d', '0 <_ ( %s holord q )' % LFN)], 'jca', ante_of(BH[1])[1])
    b3 = sq([qc, sq([rlo, rhi], 'jca', '( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )'), iq], '3jca', ante_of(BH[2])[1])
    b4 = s([s([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )'), s([nr, n1], 'jca', '( N e. RR /\\ 1 <_ N )'), s([numst(w, A0, '; ; 8 0 0', 'RR'), numst(w, A0, '; ; 8 0 0', 'ge0')], 'jca', '( ; ; 8 0 0 e. RR /\\ 0 <_ ; ; 8 0 0 )')],
           '3jca', ante_of(BH[3])[1])
    # b5: for t e. RR the square part of ZFE is inside ZSL ( t )
    At = '( %s /\\ t e. RR )' % A0
    st_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (At, f))
    ZL_t = ZS(LFN, 't')
    SUB = tsub(zc1_l.SUBT('t'), {'G': ZFE})
    Atq = '( %s /\\ q e. %s )' % (At, SUB)
    stq = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Atq, f))
    SQt = SQ(CT('t'), R138)
    qs = stq([], 'simpr', 'q e. %s' % SUB)
    esb = w.s([w.s([], 'eleq1', '( p = q -> ( p e. %s <-> q e. %s ) )' % (SQt, SQt))], 'elrab', '( q e. %s <-> ( q e. %s /\\ q e. %s ) )' % (SUB, ZFE, SQt))
    qs2 = stq([qs, esb], 'sylib', '( q e. %s /\\ q e. %s )' % (ZFE, SQt))
    qz = stq([qs2, w.inst('simpl')], 'syl', 'q e. %s' % ZFE); qsq = stq([qs2, w.inst('simpr')], 'syl', 'q e. %s' % SQt)
    Aq2 = Aq
    toAq = stq([stq([], 'simpll', A0), qz], 'jca', Aq)
    lq0t = stq([toAq, w.s([lq0], 'x', 'x') if False else lq0], 'syl', '( %s ` q ) = 0' % LFN)
    subl = w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (LFN, LFN))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (LFN, LFN))
    qzl = stq([subl, qsq, lq0t], 'elrabd', 'q e. %s' % ZL_t)
    ssb = st_([w.s([qzl], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (At, SUB, ZL_t))], 'ssrdv', '%s C_ %s' % (SUB, ZL_t))
    LZ = tsub(S['lchrzc8'], {'T': 't'})
    lza, lzc = ante_of(LZ)
    lz = st_([st_([lift(w, chi, At), st_([], 'simpr', 't e. RR')], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zlf = st_([lz, w.inst('simp1')], 'syl', top_and(lzc)[0]); zln = st_([lz, w.inst('simp2')], 'syl', top_and(lzc)[1]); zlm = st_([lz, w.inst('simp3')], 'syl', top_and(lzc)[2])
    Atz = '( %s /\\ q e. %s )' % (At, ZL_t)
    zqn = w.s([zln], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Atz, LFN))
    le = st_([zlf, w.s([zqn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Atz, LFN)), w.s([w.s([zqn], 'nnnn0d', '( %s -> ( %s holord q ) e. NN0 )' % (Atz, LFN))], 'nn0ge0d', '( %s -> 0 <_ ( %s holord q ) )' % (Atz, LFN)), ssb],
             'fsumless', '%s <_ %s' % (MASS(SUB, LFN), MASS(ZL_t, LFN)))
    Rt = ante_of(BH[4])[1].split(' <_ ', 1)[1]
    b5 = st_([st_([st_([lift(w, gfin, At), w.s([w.s([], 'ssrab2', '%s C_ %s' % (SUB, ZFE))], 'a1i', '( %s -> %s C_ %s )' % (At, SUB, ZFE))], 'ssfid', '%s e. Fin' % SUB),
                   w.s([w.s([w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (Atq, A0)), qz], 'jca', '( %s -> %s )' % (Atq, Aq)), b2], 'syl', '( %s -> ( ( %s holord q ) e. RR /\\ 0 <_ ( %s holord q ) ) )' % (Atq, LFN, LFN)),
                              w.inst('simpl')], 'syl', '( %s -> ( %s holord q ) e. RR )' % (Atq, LFN))], 'x', 'x') if False else
                   w.s([w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (Atq, A0)), qz], 'jca', '( %s -> %s )' % (Atq, Aq)), b2], 'syl', '( %s -> ( ( %s holord q ) e. RR /\\ 0 <_ ( %s holord q ) ) )' % (Atq, LFN, LFN)), w.inst('simpl')],
                       'syl', '( %s -> ( %s holord q ) e. RR )' % (Atq, LFN))], 'fsumrecl', '%s e. RR' % MASS(SUB, LFN)),
              st_([zlf, w.s([zqn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Atz, LFN))], 'fsumrecl', '%s e. RR' % MASS(ZL_t, LFN)),
              lin8(w, At, [], '0 <_ 0', {}) and None, le, zlm], 'x', 'x') if False else None
    msr = st_([st_([lift(w, gfin, At), w.s([w.s([], 'ssrab2', '%s C_ %s' % (SUB, ZFE))], 'a1i', '( %s -> %s C_ %s )' % (At, SUB, ZFE))], 'ssfid', '%s e. Fin' % SUB),
               w.s([w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (Atq, A0)), qz], 'jca', '( %s -> %s )' % (Atq, Aq)), b2], 'syl', '( %s -> ( ( %s holord q ) e. RR /\\ 0 <_ ( %s holord q ) ) )' % (Atq, LFN, LFN)), w.inst('simpl')],
                   'syl', '( %s -> ( %s holord q ) e. RR )' % (Atq, LFN))], 'fsumrecl', '%s e. RR' % MASS(SUB, LFN))
    mlr = st_([zlf, w.s([zqn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Atz, LFN))], 'fsumrecl', '%s e. RR' % MASS(ZL_t, LFN))
    import cl as _cl
    atr = st_([st_([], 'simpr', 't e. RR')], 'recnd', 't e. CC')
    XTt = '( N x. ( ( abs ` t ) + 2 ) )'
    lvx = {'N': lift(w, nr, At), '( abs ` t )': st_([atr], 'abscld', '( abs ` t ) e. RR')}
    cx = _cl.Closure(w, At, lvx)
    for k_ in lvx:
        cx.atom(k_)
    xtp = st_([cx.mem(XTt, 'RR'), lin.linarith(w, At, [lift(w, n1, At), st_([atr], 'absge0d', '0 <_ ( abs ` t )'),
                                                     st_([lift(w, nr, At), st_([atr], 'abscld', '( abs ` t ) e. RR'), lin8(w, At, [lift(w, n1, At)], '0 <_ N', lvx), st_([atr], 'absge0d', '0 <_ ( abs ` t )')],
                                                         'mulge0d', '0 <_ ( N x. ( abs ` t ) )')], '0 < %s' % XTt, closure=cx, products=True)], 'elrpd', '%s e. RR+' % XTt)
    RR_ = st_([numst(w, At, '; ; 8 0 0', 'RR'), st_([xtp], 'relogcld', '( log ` %s ) e. RR' % XTt)], 'remulcld', '( ; ; 8 0 0 x. ( log ` %s ) ) e. RR' % XTt)
    b5 = st_([msr, mlr, RR_, le, zlm], 'letrd', '%s <_ %s' % (MASS(SUB, LFN), Rt))
    bh = [b1, None, None, b4, b5]
    # boxcnt as a closed-up instance: its hypotheses are the steps b1..b5
    BC = tsub(S['boxcnt'], {'ph': PH, 'G': ZFE, 'W': HO(LFN), 'A': 'N', 'K': '; ; 8 0 0'})
    bc = w.s([b1, b2, b3, b4, b5], 'boxcnt', BC)
    RHS = BC.split(' <_ ', 1)[1][:-2]
    L_ = '( log ` ( N x. ( T + 2 ) ) )'
    lv = {'T': tr, L_: None}
    ltp = s([s([nr, s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')], 'remulcld', '( N x. ( T + 2 ) ) e. RR'),
             lin.linarith(w, A0, [n1, t1, s([nr, tr, lin8(w, A0, [n1], '0 <_ N', {'N': nr}), lin8(w, A0, [t1], '0 <_ T', {'T': tr})], 'mulge0d', '0 <_ ( N x. T )')], '0 < ( N x. ( T + 2 ) )',
                          closure=clo(w, A0, {'N': nr, 'T': tr}), products=True)], 'elrpd', '( N x. ( T + 2 ) ) e. RR+')
    msz = s([gfin, sq([lnn], 'nnred', '( %s holord q ) e. RR' % LFN)], 'fsumrecl', '%s e. RR' % MASS(ZFE, LFN))
    lv = {'T': tr, L_: s([ltp], 'relogcld', '%s e. RR' % L_), MASS(ZFE, LFN): msz}
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    fin = lin.linarith(w, A0, [bc], '%s <_ ( %s x. ( T x. %s ) )' % (MASS(ZFE, LFN), C64, L_), closure=c, products=True)
    w.qed([se, fin], 'eqbrtrd', S['zc1cnt'])
    return run8(w)


if __name__ == '__main__':
    gen_ezf()
    gen_zc1cnt()
