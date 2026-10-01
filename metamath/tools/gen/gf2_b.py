"""Sortie GF2, section B: the frozen headline gf2bt (Lean Bgram_eq_main_add_rem_frozen + norm_Brem_le').
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_b.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
import gf1lib as G1L
from gf1lib import tsub, proj, build, HOL
from mvlib import ringeq, ringeqp
import gf2_a as GA_
import gf2_g as GG
import gf2_s as GS
import gf2_d as GD
import gf2_l as GL

S_ = L.S
CH = '( a e. NN |-> ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) ) )'
EF = '( N DChrLF X )'
FRS = {'A': L.LM0, 'B': L.LXP, 'L': L.ELLD, 'R': L.RP, 'C': CH, 'E': EF}
DB = L.DB_('N')
HZ2 = L.HZ2
TNF_ = lambda n: tsub(GG.TNQ(n), FRS)
PFn = lambda n: '( ( N PFun %s ) ` %s )' % (L.RP, n)
ZRn = lambda n: '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % n
PRN = '( n e. NN |-> if ( ( n gcd N ) = 1 , 1 , 0 ) )'
import gf2_s as _GS
CHR = '( %s : NN --> CC /\\ ( %s ` 1 ) = 1 /\\ %s )' % (CH, CH, tsub(GD.MULT, {'C': CH}))
CBf = tsub(_GS.CBj, {'C': CH})
EHf = tsub(_GS.EHOL, {'E': EF})
E1f = '( %s ` 1 ) = if ( %s = %s , ( ( phi ` N ) / N ) , 0 )' % (EF, CH, PRN)
DSf = tsub(_GS.DSER, {'C': CH, 'E': EF})
ZL1 = '( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ %s ) )' % (CHR, CBf, EHf, E1f, DSf)
S_['gf2bgs'] = '( ( ( %s /\\ N e. NN ) /\\ ( X e. %s /\\ S e. CC ) ) -> sum_ n e. NN %s = %s )' % (HZ2, DB, TNF_('n'), L.BGX('X', 'S'))


def frozen_facts(w, a, P_):
    """A = log M0, B = log XP e. RR, >_ 0, A <_ B ; L = ELLD e. RR+ ; R = RP e. RR , 1 <_ R ; D e. RR+"""
    st = mkst(w, a)
    dr = P_('D e. RR'); d1 = P_('1 < D'); l2 = P_('2 <_ ( log ` D )')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    LD = '( log ` D )'
    ldr = st([drp], 'relogcld', '%s e. RR' % LD)
    out = {'D e. RR+': drp, '%s e. RR' % LD: ldr}
    for q, X in (('( 3 / 5 )', L.LM0), ('( 6 / 5 )', L.LXP)):
        e = st([drp, litr(w, a, q)], 'logcxpd', '%s = ( %s x. %s )' % (X, q, LD))
        xr = st([e, st([litr(w, a, q), ldr], 'remulcld', '( %s x. %s ) e. RR' % (q, LD))], 'eqeltrd', '%s e. RR' % X)
        out['%s e. RR' % X] = xr; out['eq' + X] = e
        out['0 <_ %s' % X] = st([e, lin.linarith(w, a, [l2], '0 <_ ( %s x. %s )' % (q, LD), leaves={LD: ldr})], 'breqtrrd', '0 <_ %s' % X)
    out['%s <_ %s' % (L.LM0, L.LXP)] = lin.linarith(w, a, [out['eq' + L.LM0], out['eq' + L.LXP], l2], '%s <_ %s' % (L.LM0, L.LXP),
                                                     leaves={LD: ldr, L.LM0: out['%s e. RR' % L.LM0], L.LXP: out['%s e. RR' % L.LXP]})
    lpos = lin.linarith(w, a, [l2], '0 < %s' % L.ELLD, leaves={LD: ldr})
    out['%s e. RR+' % L.ELLD] = st([st([litr(w, a, '( 1 / ; ; 1 0 0 )'), ldr], 'remulcld', '%s e. RR' % L.ELLD), lpos], 'elrpd', '%s e. RR+' % L.ELLD)
    rpp = st([drp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % L.RP)
    out['%s e. RR' % L.RP] = st([rpp], 'rpred', '%s e. RR' % L.RP)
    d1le = lin.linarith(w, a, [d1], '1 <_ D', leaves={'D': dr})
    r1 = st([st([dr, d1le], 'jca', '( D e. RR /\\ 1 <_ D )'), st([st([], '0red', '0 e. RR'), litr(w, a, '( 1 / ; ; 1 0 0 )')], 'jca', '( 0 e. RR /\\ ( 1 / ; ; 1 0 0 ) e. RR )'),
             lin.linarith(w, a, [], '0 <_ ( 1 / ; ; 1 0 0 )'), w.inst('cxplea')], 'syl3anc', '( D ^c 0 ) <_ %s' % L.RP)
    out['1 <_ %s' % L.RP] = st([st([st([st([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1')], 'eqcomd', '1 = ( D ^c 0 )'), r1], 'eqbrtrd', '1 <_ %s' % L.RP)
    return out


def gf2bgs():
    w = W('gf2bgs', 'The anchor series at the frozen parameters is the Gram function ` BGX ` : termwise, ` ( 1 / n ) P ( n ) ^ 2 chi ( n ) n ^ -u S W ( n ) ` '
          '(~ z5bmajval , ~ z5wwinval ).')
    a = split_imp(S_['gf2bgs'])[0]; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    ff = frozen_facts(w, a, P_)
    an = '( %s /\\ n e. NN )' % a; tn = mkst(w, an)
    nn = tn([], 'simpr', 'n e. NN')
    lift_ = lambda x: lift(w, x, an)
    qv, _ = mpv(w, an, 'b', 'NN', '( ( %s ^ 2 ) x. ( %s ` b ) )' % (PFn('b'), CH), 'n', nn)
    cv, _ = mpv(w, an, 'a', 'NN', ZRn('a'), 'n', nn)
    QN = '( ( %s ^ 2 ) x. %s )' % (PFn('n'), ZRn('n'))
    qv2 = tn([qv, tn([cv], 'oveq2d', '( ( %s ^ 2 ) x. ( %s ` n ) ) = %s' % (PFn('n'), CH, QN))], 'eqtrd', '( %s ` n ) = %s' % (tsub(GG.QF, FRS), QN))
    WNf = tsub(GA_.WN('n'), FRS)
    WF = '( WWin ` <. %s , %s , %s >. )' % (L.M0, L.XP, L.ELLD)
    M0v = tn([], 'ovexd', '%s e. _V' % L.M0); XPv = tn([], 'ovexd', '%s e. _V' % L.XP); ELv = tn([], 'ovexd', '%s e. _V' % L.ELLD)
    wv = tn([tn([M0v, XPv, ELv], '3jca', '( %s e. _V /\\ %s e. _V /\\ %s e. _V )' % (L.M0, L.XP, L.ELLD)), nn, w.inst('z5wwinval')], 'syl2anc', '( %s ` n ) = %s' % (WF, WNf))
    PF = '( N PFun %s )' % L.RP
    bv = tn([tn([tn([], 'ovexd', '%s e. _V' % PF), tn([], 'fvexd', '%s e. _V' % WF)], 'jca', '( %s e. _V /\\ %s e. _V )' % (PF, WF)), nn, w.inst('z5bmajval')], 'syl2anc',
            '( %s ` n ) = ( ( ( 1 / n ) x. ( %s ^ 2 ) ) x. ( %s ` n ) )' % (L.BM, PFn('n'), WF))
    # the atoms
    wnr = tn([tn([tn([lift_(ff['%s e. RR' % L.LM0]), lift_(ff['%s e. RR' % L.LXP])], 'jca', '( %s e. RR /\\ %s e. RR )' % (L.LM0, L.LXP)),
                  lift_(ff['%s e. RR+' % L.ELLD])], 'jca', '( ( %s e. RR /\\ %s e. RR ) /\\ %s e. RR+ )' % (L.LM0, L.LXP, L.ELLD)), nn], 'jca',
             tsub(split_imp(S_['gf2wnre'])[0], {'A': L.LM0, 'B': L.LXP, 'L': L.ELLD, 'K': 'n'}))
    wnre = tn([wnr, w.inst('gf2wnre')], 'syl', '%s e. RR' % WNf)
    wfc = tn([wv, tn([wnre], 'recnd', '%s e. CC' % WNf)], 'eqeltrd', '( %s ` n ) e. CC' % WF)
    rpr = lift_(ff['%s e. RR' % L.RP])
    rp0 = lin.linarith(w, an, [lift_(ff['1 <_ %s' % L.RP])], '0 <_ %s' % L.RP, leaves={L.RP: rpr})
    pfh = tn([lift_(P_('N e. NN')), tn([rpr, rp0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (L.RP, L.RP))], 'jca', '( N e. NN /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (L.RP, L.RP))
    pfb = tn([pfh, nn, w.inst('z5pfunabs')], 'syl2anc', '( abs ` %s ) <_ ( |_ ` %s )' % (PFn('n'), L.RP))
    pfc = tn([pfb, w.inst('z6absle')], 'syl', '%s e. CC' % PFn('n'))
    zl = tn([tn([lift_(P_('N e. NN')), lift_(P_('X e. %s' % DB))], 'jca', '( N e. NN /\\ X e. %s )' % DB), w.inst('zl1lif')], 'syl', ZL1)
    chf = tn([tn([tn([zl], 'simpld', '( %s /\\ %s )' % (CHR, CBf))], 'simpld', CHR)], 'simp1d', '%s : NN --> CC' % CH)
    zrc = tn([cv, tn([chf, nn], 'ffvelcdmd', '( %s ` n ) e. CC' % CH)], 'eqeltrrd', '%s e. CC' % ZRn('n'))
    nsc = tn([tn([nn], 'nncnd', 'n e. CC'), tn([lift_(P_('S e. CC'))], 'negcld', '-u S e. CC')], 'cxpcld', '( n ^c -u S ) e. CC')
    inc = tn([tn([nn], 'nnrecred', '( 1 / n ) e. RR')], 'recnd', '( 1 / n ) e. CC')
    CNf = tsub(GA_.CN('n'), dict(FRS, Q=tsub(GG.QF, FRS)))
    rc, vc_ = w.rewrite(CNf, {'( %s ` n )' % tsub(GG.QF, FRS): (QN, qv2)}, an)
    v1 = '( %s x. ( %s ` n ) )' % (vc_, WF)
    assert TNF_('n') == '( %s x. %s )' % (CNf, WNf), (TNF_('n')[:200], CNf[:200])
    r1 = tn([rc, tn([wv], 'eqcomd', '%s = ( %s ` n )' % (WNf, WF))], 'oveq12d', '%s = %s' % (TNF_('n'), v1))
    BT = '( ( ( %s ` n ) x. %s ) x. ( n ^c -u S ) )' % (L.BM, ZRn('n'))
    r2, v2 = w.rewrite(BT, {'( %s ` n )' % L.BM: ('( ( ( 1 / n ) x. ( %s ^ 2 ) ) x. ( %s ` n ) )' % (PFn('n'), WF), bv)}, an)
    cl = Closure(w, an, {'( 1 / n )': inc, PFn('n'): pfc, ZRn('n'): zrc, '( n ^c -u S )': nsc, '( %s ` n )' % WF: wfc})
    rq = ringeqp(w, an, v1, v2, cl)
    te = tn([tn([r1, rq], 'eqtrd', '%s = %s' % (TNF_('n'), v2)), tn([r2], 'eqcomd', '%s = %s' % (v2, BT))], 'eqtrd', '%s = %s' % (TNF_('n'), BT))
    fin = st([te], 'sumeq2dv', split_imp(S_['gf2bgs'])[1])
    w.qed([fin], 'idi', S_['gf2bgs'])
    return w


HFBf = lambda v: tsub(GS.HFB(v), FRS)
X0 = '( 0g ` ( DChr ` N ) )'
BTA = split_imp(S_['gf2bt'])[0]
RSA = '( ( %s /\\ ( N e. NN /\\ X e. %s ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 1 / ; 5 0 ) ) ) )' % (HZ2, DB)
S_['gf2res'] = '( %s -> %s = if ( X = %s , %s , 0 ) )' % (RSA, HFBf('-u S'), X0, L.MAIN('S'))


def gf2res():
    w = W('gf2res', 'The residue at the pole ` -u S ` (Lean ` Hfull_at_pole ` , ` Mh_one_principal ` ): ` HF ( -u S ) = G1 ( -u S ) M_h ( 1 ) E ( 1 ) ` is the principal '
          'term ` ( phi ( N ) / N ) PHI G1 ( -u S ) ` for the principal character and 0 otherwise (~ zl1lif , ~ zl1prn , ~ gf2mh1 ).')
    a = RSA; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    ff = frozen_facts(w, a, P_)
    sc = P_('S e. CC')
    one = ringeq(w, a, '( ( 1 + S ) + -u S )', '1', Closure(w, a, {'S': sc}))
    rw, v0 = w.rewrite(HFBf('-u S'), {'( ( 1 + S ) + -u S )': ('1', one)}, a)
    G1S = tsub(GS.G1w('-u S'), FRS)
    MH1 = tsub(GS.MHs('1'), FRS)
    E1 = '( %s ` 1 )' % EF
    assert v0 == '( %s x. ( %s x. %s ) )' % (G1S, MH1, E1), v0
    zl = st([st([P_('N e. NN'), P_('X e. %s' % DB)], 'jca', '( N e. NN /\\ X e. %s )' % DB), w.inst('zl1lif')], 'syl', ZL1)
    e1 = st([st([st([zl], 'simprd', '( ( %s /\\ %s ) /\\ %s )' % (EHf, E1f, DSf))], 'simpld', '( %s /\\ %s )' % (EHf, E1f))], 'simprd', E1f)
    prn = st([P_('N e. NN'), P_('X e. %s' % DB), w.inst('zl1prn')], 'syl2anc', '( %s = %s <-> X = %s )' % (CH, PRN, X0))
    # G1 ( -u S ) e. CC
    HPM1 = G1L.HPM1
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    nrs = lin.linarith(w, a, [P_('( Re ` S ) <_ ( 1 / ; 5 0 )')], '-u 1 < -u ( Re ` S )', leaves={'( Re ` S )': rsr})
    ph_ = st([st([st([sc], 'negcld', '-u S e. CC'), st([nrs, st([sc], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')], 'breqtrrd', '-u 1 < ( Re ` -u S )')], 'jca',
                 '( -u S e. CC /\\ -u 1 < ( Re ` -u S ) )'), st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl',
                                                              '( -u S e. %s <-> ( -u S e. CC /\\ -u 1 < ( Re ` -u S ) ) )' % HPM1)], 'mpbird', '-u S e. %s' % HPM1)
    g1h = st([st([st([ff['%s e. RR' % L.LM0], ff['%s e. RR' % L.LXP]], 'jca', '( %s e. RR /\\ %s e. RR )' % (L.LM0, L.LXP)), ff['%s e. RR+' % L.ELLD]], 'jca',
                 '( ( %s e. RR /\\ %s e. RR ) /\\ %s e. RR+ )' % (L.LM0, L.LXP, L.ELLD)), w.inst('gf1g1h')], 'syl',
             tsub(split_imp(G1L.S['gf1g1h'])[1], {'A': L.LM0, 'B': L.LXP, 'L': L.ELLD}))
    G1M = '( w e. %s |-> %s )' % (HPM1, tsub(GS.G1w('w'), FRS))
    g1v, _ = mpv(w, a, 'w', HPM1, tsub(GS.G1w('w'), FRS), '-u S', ph_)
    g1c = st([g1v, st([st([st([g1h], 'simpld', '%s e. ( %s -cn-> CC )' % (G1M, HPM1)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (G1M, HPM1)), ph_], 'ffvelcdmd',
                      '( %s ` -u S ) e. CC' % G1M)], 'eqeltrrd', '%s e. CC' % G1S)
    chf = st([st([st([zl], 'simpld', '( %s /\\ %s )' % (CHR, CBf))], 'simpld', CHR)], 'simp1d', '%s : NN --> CC' % CH)
    cbj = st([st([zl], 'simpld', '( %s /\\ %s )' % (CHR, CBf))], 'simprd', CBf)
    CBk = 'A. k e. NN ( abs ` ( %s ` k ) ) <_ 1' % CH
    idjk = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( %s ` j ) = ( %s ` k ) )' % (CH, CH))], 'fveq2d', '( j = k -> ( abs ` ( %s ` j ) ) = ( abs ` ( %s ` k ) ) )' % (CH, CH))], 'breq1d',
               '( j = k -> ( ( abs ` ( %s ` j ) ) <_ 1 <-> ( abs ` ( %s ` k ) ) <_ 1 ) )' % (CH, CH))
    cbk = st([cbj, w.s([idjk], 'cbvralvw', '( %s <-> %s )' % (CBf, CBk))], 'sylib', CBk)
    re10 = a1(w, a, w.s([w.s([w.s([], '1re', '1 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 1 ) = 1'), w.s([], '0le1', '0 <_ 1')], 'breqtrri', '0 <_ ( Re ` 1 )'), '0 <_ ( Re ` 1 )')
    mhb = st([st([P_('N e. NN'), ff['%s e. RR' % L.RP]], 'jca', '( N e. NN /\\ %s e. RR )' % L.RP), st([chf, cbk], 'jca', '( %s : NN --> CC /\\ %s )' % (CH, CBk)),
              st([st([], '1cnd', '1 e. CC'), re10], 'jca', '( 1 e. CC /\\ 0 <_ ( Re ` 1 ) )'), w.inst('gf1mhb')], 'syl3anc',
             '( %s e. CC /\\ ( abs ` %s ) <_ %s )' % (MH1, MH1, tsub(G1L.HM('N', 'R'), FRS)))
    mhc = st([mhb], 'simpld', '%s e. CC' % MH1)
    # case X = 0g
    c1 = '( %s /\\ X = %s )' % (a, X0); t1 = mkst(w, c1)
    chp = t1([t1([], 'simpr', 'X = %s' % X0), lift(w, prn, c1)], 'mpbird', '%s = %s' % (CH, PRN))
    PN = '( ( phi ` N ) / N )'
    e1t = t1([lift(w, e1, c1), t1([chp, w.s([], 'iftrue', '( %s = %s -> if ( %s = %s , %s , 0 ) = %s )' % (CH, PRN, CH, PRN, PN, PN))], 'syl',
                                  'if ( %s = %s , %s , 0 ) = %s' % (CH, PRN, PN, PN))], 'eqtrd', '%s = %s' % (E1, PN))
    mr1, mv1 = w.rewrite(MH1, {CH: (PRN, chp)}, c1)
    PHI = L.PHI('N', L.RP)
    mh1 = t1([t1([lift(w, P_('N e. NN'), c1), lift(w, ff['%s e. RR' % L.RP], c1)], 'jca', '( N e. NN /\\ %s e. RR )' % L.RP), w.inst('gf2mh1')], 'syl', '%s = %s' % (mv1, PHI))
    mhe = t1([mr1, mh1], 'eqtrd', '%s = %s' % (MH1, PHI))
    pnc = t1([t1([t1([t1([lift(w, P_('N e. NN'), c1), w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nncnd', '( phi ` N ) e. CC'),
                  t1([lift(w, P_('N e. NN'), c1)], 'nncnd', 'N e. CC'), t1([lift(w, P_('N e. NN'), c1)], 'nnne0d', 'N =/= 0')], 'divcld', '%s e. CC' % PN)], 'idi', '%s e. CC' % PN)
    phic = t1([mhe, lift(w, mhc, c1)], 'eqeltrrd', '%s e. CC' % PHI)
    inner = t1([mhe, e1t], 'oveq12d', '( %s x. %s ) = ( %s x. %s )' % (MH1, E1, PHI, PN))
    hv1 = t1([lift(w, rw, c1), t1([inner], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (G1S, MH1, E1, G1S, PHI, PN))], 'eqtrd',
             '%s = ( %s x. ( %s x. %s ) )' % (HFBf('-u S'), G1S, PHI, PN))
    MAINS = L.MAIN('S')
    rq = ringeq(w, c1, '( %s x. ( %s x. %s ) )' % (G1S, PHI, PN), MAINS, Closure(w, c1, {G1S: lift(w, g1c, c1), PHI: phic, PN: pnc}))
    IFM = 'if ( X = %s , %s , 0 )' % (X0, MAINS)
    ift = t1([t1([], 'simpr', 'X = %s' % X0), w.s([], 'iftrue', '( X = %s -> %s = %s )' % (X0, IFM, MAINS))], 'syl', '%s = %s' % (IFM, MAINS))
    ca = t1([t1([hv1, rq], 'eqtrd', '%s = %s' % (HFBf('-u S'), MAINS)), ift], 'eqtr4d', '%s = %s' % (HFBf('-u S'), IFM))
    # case X =/= 0g
    c2 = '( %s /\\ -. X = %s )' % (a, X0); t2 = mkst(w, c2)
    nch = t2([t2([], 'simpr', '-. X = %s' % X0), lift(w, prn, c2)], 'mtbird', '-. %s = %s' % (CH, PRN))
    e1f = t2([lift(w, e1, c2), t2([nch, w.s([], 'iffalse', '( -. %s = %s -> if ( %s = %s , %s , 0 ) = 0 )' % (CH, PRN, CH, PRN, PN))], 'syl',
                                   'if ( %s = %s , %s , 0 ) = 0' % (CH, PRN, PN))], 'eqtrd', '%s = 0' % E1)
    z1_ = t2([t2([e1f], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (MH1, E1, MH1)), t2([lift(w, mhc, c2)], 'mul01d', '( %s x. 0 ) = 0' % MH1)], 'eqtrd', '( %s x. %s ) = 0' % (MH1, E1))
    z2_ = t2([t2([z1_], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. 0 )' % (G1S, MH1, E1, G1S)), t2([lift(w, g1c, c2)], 'mul01d', '( %s x. 0 ) = 0' % G1S)], 'eqtrd',
             '( %s x. ( %s x. %s ) ) = 0' % (G1S, MH1, E1))
    iff_ = t2([t2([], 'simpr', '-. X = %s' % X0), w.s([], 'iffalse', '( -. X = %s -> %s = 0 )' % (X0, IFM))], 'syl', '%s = 0' % IFM)
    cb_ = t2([t2([lift(w, rw, c2), z2_], 'eqtrd', '%s = 0' % HFBf('-u S')), iff_], 'eqtr4d', '%s = %s' % (HFBf('-u S'), IFM))
    w.qed([ca, cb_], 'pm2.61dan', S_['gf2res'])
    return w


BGT = lambda n: '( ( ( %s ` %s ) x. %s ) x. ( %s ^c -u S ) )' % (L.BM, n, ZRn(n), n)
BGF = '( n e. NN |-> %s )' % BGT('n')
S_['gf2bgc'] = '( ( ( %s /\\ N e. NN ) /\\ ( X e. %s /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) ) -> %s e. CC )' % (HZ2, DB, L.BGX('X', 'S'))


def gf2bgc():
    w = W('gf2bgc', 'The Gram function converges absolutely: ` | b_n chi ( n ) n ^ -u S | <_ b_n ` and ` sum b_n ` converges (~ gf2bmc , ~ z5bmaj0 , ~ cvgcmpce ).')
    a = split_imp(S_['gf2bgc'])[0]; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    ff = frozen_facts(w, a, P_)
    zl = st([st([P_('N e. NN'), P_('X e. %s' % DB)], 'jca', '( N e. NN /\\ X e. %s )' % DB), w.inst('zl1lif')], 'syl', ZL1)
    chf = st([st([st([zl], 'simpld', '( %s /\\ %s )' % (CHR, CBf))], 'simpld', CHR)], 'simp1d', '%s : NN --> CC' % CH)
    cbj = st([st([zl], 'simpld', '( %s /\\ %s )' % (CHR, CBf))], 'simprd', CBf)
    hz = st([P_('D e. RR'), P_('1 < D'), P_('2 <_ ( log ` D )')], '3jca', HZ2)
    bmcv = st([hz, P_('N e. NN'), w.inst('gf2bmc')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % L.BM)
    ak = '( %s /\\ k e. NN )' % a; tk = mkst(w, ak)
    kn = tk([], 'simpr', 'k e. NN')
    WF = '( WWin ` <. %s , %s , %s >. )' % (L.M0, L.XP, L.ELLD)
    PF = '( N PFun %s )' % L.RP
    bv = tk([tk([tk([], 'ovexd', '%s e. _V' % PF), tk([], 'fvexd', '%s e. _V' % WF)], 'jca', '( %s e. _V /\\ %s e. _V )' % (PF, WF)), kn, w.inst('z5bmajval')], 'syl2anc',
            '( %s ` k ) = ( ( ( 1 / k ) x. ( %s ^ 2 ) ) x. ( %s ` k ) )' % (L.BM, PFn('k'), WF))
    WNk = tsub(GA_.WN('k'), FRS)
    wv = tk([tk([tk([], 'ovexd', '%s e. _V' % L.M0), tk([], 'ovexd', '%s e. _V' % L.XP), tk([], 'ovexd', '%s e. _V' % L.ELLD)], '3jca',
                '( %s e. _V /\\ %s e. _V /\\ %s e. _V )' % (L.M0, L.XP, L.ELLD)), kn, w.inst('z5wwinval')], 'syl2anc', '( %s ` k ) = %s' % (WF, WNk))
    lk = lambda x: lift(w, x, ak)
    wnr = tk([tk([tk([tk([lk(ff['%s e. RR' % L.LM0]), lk(ff['%s e. RR' % L.LXP])], 'jca', '( %s e. RR /\\ %s e. RR )' % (L.LM0, L.LXP)), lk(ff['%s e. RR+' % L.ELLD])], 'jca',
                      '( ( %s e. RR /\\ %s e. RR ) /\\ %s e. RR+ )' % (L.LM0, L.LXP, L.ELLD)), kn], 'jca',
                  tsub(split_imp(S_['gf2wnre'])[0], {'A': L.LM0, 'B': L.LXP, 'L': L.ELLD, 'K': 'k'})), w.inst('gf2wnre')], 'syl', '%s e. RR' % WNk)
    wfr = tk([wv, wnr], 'eqeltrd', '( %s ` k ) e. RR' % WF)
    pfr = tk([tk([tk([lk(P_('N e. NN')), lk(ff['%s e. RR' % L.RP])], 'jca', '( N e. NN /\\ %s e. RR )' % L.RP), kn], 'jca', '( ( N e. NN /\\ %s e. RR ) /\\ k e. NN )' % L.RP),
              w.inst('z5pfunre')], 'syl', '%s e. RR' % PFn('k'))
    bmr = tk([bv, tk([tk([tk([kn], 'nnrecred', '( 1 / k ) e. RR'), tk([pfr], 'resqcld', '( %s ^ 2 ) e. RR' % PFn('k'))], 'remulcld', '( ( 1 / k ) x. ( %s ^ 2 ) ) e. RR' % PFn('k')),
                      wfr], 'remulcld', '( ( ( 1 / k ) x. ( %s ^ 2 ) ) x. ( %s ` k ) ) e. RR' % (PFn('k'), WF))], 'eqeltrd', '( %s ` k ) e. RR' % L.BM)
    bm0 = tk([tk([lk(hz), lk(P_('N e. NN'))], 'jca', '( %s /\\ N e. NN )' % HZ2), kn, w.inst('z5bmaj0')], 'syl2anc', '0 <_ ( %s ` k )' % L.BM)
    cv, _ = mpv(w, ak, 'a', 'NN', ZRn('a'), 'k', kn)
    zrc = tk([cv, tk([lk(chf), kn], 'ffvelcdmd', '( %s ` k ) e. CC' % CH)], 'eqeltrrd', '%s e. CC' % ZRn('k'))
    rspk = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( %s ` j ) = ( %s ` k ) )' % (CH, CH))], 'fveq2d', '( j = k -> ( abs ` ( %s ` j ) ) = ( abs ` ( %s ` k ) ) )' % (CH, CH))],
               'breq1d', '( j = k -> ( ( abs ` ( %s ` j ) ) <_ 1 <-> ( abs ` ( %s ` k ) ) <_ 1 ) )' % (CH, CH))
    chb = tk([rspk, lk(cbj), kn], 'rspcdva', '( abs ` ( %s ` k ) ) <_ 1' % CH)
    zrb = tk([tk([tk([cv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (CH, ZRn('k')))], 'eqcomd', '( abs ` %s ) = ( abs ` ( %s ` k ) )' % (ZRn('k'), CH)), chb], 'eqbrtrd',
             '( abs ` %s ) <_ 1' % ZRn('k'))
    sc = lk(P_('S e. CC')); s0 = lk(P_('0 <_ ( Re ` S )'))
    krp = tk([kn], 'nnrpd', 'k e. RR+'); kc = tk([kn], 'nncnd', 'k e. CC')
    nsc = tk([sc], 'negcld', '-u S e. CC')
    ksc = tk([kc, nsc], 'cxpcld', '( k ^c -u S ) e. CC')
    ab = tk([krp, nsc, w.inst('abscxp')], 'syl2anc', '( abs ` ( k ^c -u S ) ) = ( k ^c ( Re ` -u S ) )')
    rn = tk([sc], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')
    rsr = tk([sc], 'recld', '( Re ` S ) e. RR')
    le0 = lin.linarith(w, ak, [s0], '-u ( Re ` S ) <_ 0', leaves={'( Re ` S )': rsr})
    cl_ = tk([tk([tk([kn], 'nnred', 'k e. RR'), tk([kn], 'nnge1d', '1 <_ k')], 'jca', '( k e. RR /\\ 1 <_ k )'),
              tk([tk([rsr], 'renegcld', '-u ( Re ` S ) e. RR'), tk([], '0red', '0 e. RR')], 'jca', '( -u ( Re ` S ) e. RR /\\ 0 e. RR )'), le0, w.inst('cxplea')], 'syl3anc',
             '( k ^c -u ( Re ` S ) ) <_ ( k ^c 0 )')
    kb = tk([tk([ab, tk([rn], 'oveq2d', '( k ^c ( Re ` -u S ) ) = ( k ^c -u ( Re ` S ) )')], 'eqtrd', '( abs ` ( k ^c -u S ) ) = ( k ^c -u ( Re ` S ) )'),
             tk([cl_, tk([kc, w.inst('cxp0')], 'syl', '( k ^c 0 ) = 1')], 'breqtrd', '( k ^c -u ( Re ` S ) ) <_ 1')], 'eqbrtrd', '( abs ` ( k ^c -u S ) ) <_ 1')
    bmc = tk([bmr], 'recnd', '( %s ` k ) e. CC' % L.BM)
    BZ = '( ( %s ` k ) x. %s )' % (L.BM, ZRn('k'))
    bzc = tk([bmc, zrc], 'mulcld', '%s e. CC' % BZ)
    tc = tk([bzc, ksc], 'mulcld', '%s e. CC' % BGT('k'))
    ab1 = tk([bmc, zrc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( %s ` k ) ) x. ( abs ` %s ) )' % (BZ, L.BM, ZRn('k')))
    abm = tk([bmr, bm0], 'absidd', '( abs ` ( %s ` k ) ) = ( %s ` k )' % (L.BM, L.BM))
    ab1b = tk([ab1, tk([abm], 'oveq1d', '( ( abs ` ( %s ` k ) ) x. ( abs ` %s ) ) = ( ( %s ` k ) x. ( abs ` %s ) )' % (L.BM, ZRn('k'), L.BM, ZRn('k')))], 'eqtrd',
              '( abs ` %s ) = ( ( %s ` k ) x. ( abs ` %s ) )' % (BZ, L.BM, ZRn('k')))
    azr = tk([zrc], 'abscld', '( abs ` %s ) e. RR' % ZRn('k'))
    b1 = tk([azr, tk([], '1red', '1 e. RR'), bmr, bm0, zrb], 'lemul2ad', '( ( %s ` k ) x. ( abs ` %s ) ) <_ ( ( %s ` k ) x. 1 )' % (L.BM, ZRn('k'), L.BM))
    b1b = tk([tk([ab1b, b1], 'eqbrtrd', '( abs ` %s ) <_ ( ( %s ` k ) x. 1 )' % (BZ, L.BM)), tk([bmc], 'mulridd', '( ( %s ` k ) x. 1 ) = ( %s ` k )' % (L.BM, L.BM))], 'breqtrd',
              '( abs ` %s ) <_ ( %s ` k )' % (BZ, L.BM))
    b2 = tk([tk([bzc, ksc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( k ^c -u S ) ) )' % (BGT('k'), BZ)),
             tk([tk([bzc], 'abscld', '( abs ` %s ) e. RR' % BZ), bmr, tk([ksc], 'abscld', '( abs ` ( k ^c -u S ) ) e. RR'), tk([], '1red', '1 e. RR'),
                 tk([bzc], 'absge0d', '0 <_ ( abs ` %s )' % BZ), tk([ksc], 'absge0d', '0 <_ ( abs ` ( k ^c -u S ) )'), b1b, kb], 'lemul12ad',
                '( ( abs ` %s ) x. ( abs ` ( k ^c -u S ) ) ) <_ ( ( %s ` k ) x. 1 )' % (BZ, L.BM))], 'eqbrtrd', '( abs ` %s ) <_ ( ( %s ` k ) x. 1 )' % (BGT('k'), L.BM))
    b3 = tk([b2, tk([bmc], 'mulridd', '( ( %s ` k ) x. 1 ) = ( %s ` k )' % (L.BM, L.BM))], 'breqtrd', '( abs ` %s ) <_ ( %s ` k )' % (BGT('k'), L.BM))
    gv, _ = mpv(w, ak, 'n', 'NN', BGT('n'), 'k', kn)
    b4 = tk([tk([tk([gv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (BGF, BGT('k'))), b3], 'eqbrtrd', '( abs ` ( %s ` k ) ) <_ ( %s ` k )' % (BGF, L.BM)),
             tk([tk([bmc], 'mullidd', '( 1 x. ( %s ` k ) ) = ( %s ` k )' % (L.BM, L.BM))], 'eqcomd', '( %s ` k ) = ( 1 x. ( %s ` k ) )' % (L.BM, L.BM))], 'breqtrd',
            '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (BGF, L.BM))
    ak1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    kn1 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % ak1), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                   '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'syl', '( %s -> k e. NN )' % ak1)
    b41 = w.s([w.s([w.s([b4], 'ex', '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) ) )' % (a, BGF, L.BM))], 'adantr',
                   '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) ) )' % (ak1, BGF, L.BM)), kn1], 'mpd', '( %s -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) )' % (ak1, BGF, L.BM))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    gcv = st([nnuz, a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'), bmr, tk([gv, tc], 'eqeltrd', '( %s ` k ) e. CC' % BGF), bmcv, st([], '1red', '1 e. RR'), b41], 'cvgcmpce',
             'seq 1 ( + , %s ) e. dom ~~>' % BGF)
    isc = w.s([nnuz, a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), gv, tc, gcv], 'isumcl', '( %s -> sum_ k e. NN %s e. CC )' % (a, BGT('k')))
    idkn = w.s([], 'id', '( k = n -> k = n )')
    cst, _ = w.congr(BGT('k'), {'k': 'n'}, 'k = n', {'k': idkn})
    cbs = a1(w, a, w.s([cst], 'cbvsumv', 'sum_ k e. NN %s = %s' % (BGT('k'), L.BGX('X', 'S'))), 'sum_ k e. NN %s = %s' % (BGT('k'), L.BGX('X', 'S')))
    fin = st([cbs, isc], 'eqeltrrd', '%s e. CC' % L.BGX('X', 'S'))
    w.qed([fin], 'idi', S_['gf2bgc'])
    return w



def gf2bt():
    w = W('gf2bt', 'The Gram function minus its principal residue (Lean ` Bgram_eq_main_add_rem_frozen ` and ` norm_Brem_le' + "'" + ' ` ): at the frozen '
          'parameters, ` | BGX ( X , S ) - [ X = chi_0 ] MAIN ( S ) | <_ C11 ( log D ) ^ 3 D ^ -u ( 7/100 ) ` for every character ` X ` mod ` N ` and '
          '` 0 <_ Re S <_ 1/50 ` , ` N ( | Im S | + 2 ) <_ 2 D ` (~ gf2gram , ~ gf2bgs , ~ gf2res , ~ gf2left , ~ gf2num ).')
    a = BTA; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    ff = frozen_facts(w, a, P_)
    zl = st([st([P_('N e. NN'), P_('X e. %s' % DB)], 'jca', '( N e. NN /\\ X e. %s )' % DB), w.inst('zl1lif')], 'syl', ZL1)
    c1 = st([zl], 'simpld', '( %s /\\ %s )' % (CHR, CBf))
    chr_ = st([c1], 'simpld', CHR); cbj = st([c1], 'simprd', CBf)
    chf = st([chr_], 'simp1d', '%s : NN --> CC' % CH); mult = st([chr_], 'simp3d', tsub(GD.MULT, {'C': CH}))
    c2 = st([zl], 'simprd', '( ( %s /\\ %s ) /\\ %s )' % (EHf, E1f, DSf))
    ehf = st([st([c2], 'simpld', '( %s /\\ %s )' % (EHf, E1f))], 'simpld', EHf); dsf = st([c2], 'simprd', DSf)
    CVXf = tsub(GS.CVXH, {'E': EF})
    cvx = st([P_('N e. NN'), P_('X e. %s' % DB), w.inst('zl3cvxh')], 'syl2anc', CVXf)
    hz = st([P_('D e. RR'), P_('1 < D'), P_('2 <_ ( log ` D )')], '3jca', HZ2)
    facts = {'%s e. RR' % L.LM0: ff['%s e. RR' % L.LM0], '%s e. RR' % L.LXP: ff['%s e. RR' % L.LXP], '0 <_ %s' % L.LM0: ff['0 <_ %s' % L.LM0],
             '0 <_ %s' % L.LXP: ff['0 <_ %s' % L.LXP], '%s e. RR+' % L.ELLD: ff['%s e. RR+' % L.ELLD], 'N e. NN': P_('N e. NN'), '%s e. RR' % L.RP: ff['%s e. RR' % L.RP],
             '1 <_ %s' % L.RP: ff['1 <_ %s' % L.RP], '%s : NN --> CC' % CH: chf, CBf: cbj, EHf: ehf, DSf: dsf, CVXf: cvx, 'S e. CC': P_('S e. CC'),
             '0 <_ ( Re ` S )': P_('0 <_ ( Re ` S )'), '( Re ` S ) <_ ( 1 / ; 5 0 )': P_('( Re ` S ) <_ ( 1 / ; 5 0 )'), tsub(GD.MULT, {'C': CH}): mult,
             HZ2: hz, 'D e. RR': P_('D e. RR'), '1 < D': P_('1 < D'), '2 <_ ( log ` D )': P_('2 <_ ( log ` D )'),
             '( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ ( 2 x. D )': P_('( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ ( 2 x. D )'),
             '%s <_ %s' % (L.LM0, L.LXP): ff['%s <_ %s' % (L.LM0, L.LXP)]}
    gram = st([build(w, a, tsub(GG.GH, FRS), facts), w.inst('gf2gram')], 'syl', tsub(split_imp(S_['gf2gram'])[1], FRS))
    left = st([build(w, a, tsub(GL.LEH, FRS), facts), w.inst('gf2left')], 'syl', tsub(split_imp(S_['gf2left'])[1], FRS))
    num_ = st([hz, w.inst('gf2num')], 'syl', split_imp(S_['gf2num'])[1])
    bgs = st([st([st([hz, P_('N e. NN')], 'jca', '( %s /\\ N e. NN )' % HZ2), st([P_('X e. %s' % DB), P_('S e. CC')], 'jca', '( X e. %s /\\ S e. CC )' % DB)], 'jca',
                 split_imp(S_['gf2bgs'])[0]), w.inst('gf2bgs')], 'syl', split_imp(S_['gf2bgs'])[1])
    res = st([build(w, a, RSA, facts | {'X e. %s' % DB: P_('X e. %s' % DB)}), w.inst('gf2res')], 'syl', split_imp(S_['gf2res'])[1])
    bgc = st([build(w, a, split_imp(S_['gf2bgc'])[0], facts | {'X e. %s' % DB: P_('X e. %s' % DB)}), w.inst('gf2bgc')], 'syl', '%s e. CC' % L.BGX('X', 'S'))
    TPI = GS.TPI
    V = tsub(GS.VLh(GS.GI, GS.CLL), FRS)
    SS = 'sum_ n e. NN %s' % TNF_('n')
    BG = L.BGX('X', 'S')
    HF = HFBf('-u S')
    IFM = 'if ( X = %s , %s , 0 )' % (X0, L.MAIN('S'))
    g2 = st([gram], 'simprd', '( ( %s x. %s ) - %s ) = ( %s x. %s )' % (TPI, SS, V, TPI, HF))
    e1 = st([st([st([bgs], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (TPI, SS, TPI, BG))], 'oveq1d', '( ( %s x. %s ) - %s ) = ( ( %s x. %s ) - %s )' % (TPI, SS, V, TPI, BG, V)),
             st([g2, st([res], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (TPI, HF, TPI, IFM))], 'eqtrd', '( ( %s x. %s ) - %s ) = ( %s x. %s )' % (TPI, SS, V, TPI, IFM))], 'eqtr3d',
            '( ( %s x. %s ) - %s ) = ( %s x. %s )' % (TPI, BG, V, TPI, IFM))
    vc = st([left, w.inst('z6absle')], 'syl', '%s e. CC' % V)
    tpc, tge = GA_.tpifacts(w, a)
    tbc = st([tpc, bgc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, BG))
    tic = st([e1, st([tbc, vc], 'subcld', '( ( %s x. %s ) - %s ) e. CC' % (TPI, BG, V))], 'eqeltrrd', '( %s x. %s ) e. CC' % (TPI, IFM))
    # IFM e. CC : HF ( -u S ) e. CC by gf2hf
    HFx = tsub(GS.HFH, FRS)
    hff = {'%s e. RR' % L.LM0: ff['%s e. RR' % L.LM0], '%s e. RR' % L.LXP: ff['%s e. RR' % L.LXP], '%s e. RR+' % L.ELLD: ff['%s e. RR+' % L.ELLD],
           'N e. NN': P_('N e. NN'), '%s e. RR' % L.RP: ff['%s e. RR' % L.RP], '%s : NN --> CC' % CH: chf, 'S e. CC': P_('S e. CC'), '0 <_ ( Re ` S )': P_('0 <_ ( Re ` S )'), EHf: ehf}
    HFx2 = tsub(HFx, {'V': 'NN', 'W': 'RR'})
    hf = st([build(w, a, HFx2, hff), w.inst('gf2hf')], 'syl', tsub(HOL(GS.HFF, GS.HPM1), FRS))
    HFFf = tsub(GS.HFF, FRS)
    HPM1 = GS.HPM1
    sc = P_('S e. CC')
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    nrs = lin.linarith(w, a, [P_('( Re ` S ) <_ ( 1 / ; 5 0 )')], '-u 1 < -u ( Re ` S )', leaves={'( Re ` S )': rsr})
    ph_ = st([st([st([sc], 'negcld', '-u S e. CC'), st([nrs, st([sc], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')], 'breqtrrd', '-u 1 < ( Re ` -u S )')], 'jca',
                 '( -u S e. CC /\\ -u 1 < ( Re ` -u S ) )'), st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl',
                                                              '( -u S e. %s <-> ( -u S e. CC /\\ -u 1 < ( Re ` -u S ) ) )' % HPM1)], 'mpbird', '-u S e. %s' % HPM1)
    hv, _ = mpv(w, a, 'w', HPM1, tsub(GS.HFB('w'), FRS), '-u S', ph_, exs=st([], 'ovexd', '%s e. _V' % HF))
    hfc = st([hv, st([st([st([hf], 'simpld', '%s e. ( %s -cn-> CC )' % (HFFf, HPM1)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (HFFf, HPM1)), ph_], 'ffvelcdmd',
                     '( %s ` -u S ) e. CC' % HFFf)], 'eqeltrrd', '%s e. CC' % HF)
    ifc = st([res, hfc], 'eqeltrrd', '%s e. CC' % IFM)
    # V = TPI ( BG - IFM )
    s23 = st([tbc, vc, tic, w.inst('subsub23')], 'syl3anc', '( ( ( %s x. %s ) - %s ) = ( %s x. %s ) <-> ( ( %s x. %s ) - ( %s x. %s ) ) = %s )' % (TPI, BG, V, TPI, IFM, TPI, BG, TPI, IFM, V))
    e2 = st([e1, s23], 'mpbid', '( ( %s x. %s ) - ( %s x. %s ) ) = %s' % (TPI, BG, TPI, IFM, V))
    DM = '( %s - %s )' % (BG, IFM)
    sd = st([tpc, bgc, ifc], 'subdid', '( %s x. %s ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (TPI, DM, TPI, BG, TPI, IFM))
    ve = st([sd, e2], 'eqtrd', '( %s x. %s ) = %s' % (TPI, DM, V))
    dmc = st([bgc, ifc], 'subcld', '%s e. CC' % DM)
    av = st([st([ve], 'fveq2d', '( abs ` ( %s x. %s ) ) = ( abs ` %s )' % (TPI, DM, V)), st([tpc, dmc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TPI, DM, TPI, DM))],
            'eqtr3d', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (V, TPI, DM))
    # | TPI | = 2 pi
    ic = a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'); pic = a1(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')
    pir = a1(w, a, w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
    p3 = a1(w, a, w.s([], 'pigt3', '3 < _pi'), '3 < _pi')
    a1_ = st([st([], '2cnd', '2 e. CC'), st([ic, pic], 'mulcld', '( _i x. _pi ) e. CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
    a2 = st([ic, pic], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )')
    ap = st([pir, lin.linarith(w, a, [p3], '0 <_ _pi', leaves={'_pi': pir})], 'absidd', '( abs ` _pi ) = _pi')
    a2v = st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), a1(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2')], 'absidd', '( abs ` 2 ) = 2')
    ai = a1(w, a, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')
    TP = '( 2 x. _pi )'
    atv = st([a1_, st([a2v, st([a2, st([ai, ap], 'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')],
                      'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. ( 1 x. _pi ) )')], 'eqtrd', '( abs ` %s ) = ( 2 x. ( 1 x. _pi ) )' % TPI)
    atv2 = st([atv, st([st([pic], 'mullidd', '( 1 x. _pi ) = _pi')], 'oveq2d', '( 2 x. ( 1 x. _pi ) ) = %s' % TP)], 'eqtrd', '( abs ` %s ) = %s' % (TPI, TP))
    tpp = st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), a1(w, a, w.s([], 'pirp', '_pi e. RR+'), '_pi e. RR+')], 'rpmulcld', '%s e. RR+' % TP)
    adr = st([dmc], 'abscld', '( abs ` %s ) e. RR' % DM)
    av2 = st([av, st([atv2], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, DM, TP, DM))], 'eqtrd', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (V, TP, DM))
    av3 = st([av2, st([st([tpp], 'rpcnd', '%s e. CC' % TP), st([adr], 'recnd', '( abs ` %s ) e. CC' % DM)], 'mulcomd', '( %s x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (TP, DM, DM, TP))],
             'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (V, DM, TP))
    # K e. RR
    ct = GL.ctre(w, a)
    drp = ff['D e. RR+']; ldr = ff['( log ` D ) e. RR']
    EACf = tsub(GL.EAC, {'A': L.LM0})
    ear = st([st([ff['%s e. RR' % L.LM0], litr(w, a, GS.CLL)], 'remulcld', '( %s x. %s ) e. RR' % (L.LM0, GS.CLL))], 'reefcld', '%s e. RR' % EACf)
    HMBf = tsub(GL.HMB, {'R': L.RP})
    rpp = st([drp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % L.RP)
    hbr = st([st([ct], 'resqcld', '( CTau ^ 2 ) e. RR'), st([st([rpp, litr(w, a, '( ; ; 8 0 1 / ; ; 4 0 0 )')], 'rpcxpcld', '( %s ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR+' % L.RP)], 'rpred',
                                                            '( %s ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR' % L.RP)], 'remulcld', '%s e. RR' % HMBf)
    C12C = '( %s x. CTau )' % GL.C12
    d3r = st([st([drp, litr(w, a, '( ; ; 3 9 7 / ; ; 8 0 0 )')], 'rpcxpcld', '%s e. RR+' % GL.D397)], 'rpred', '%s e. RR' % GL.D397)
    k2 = st([st([st([a1(w, a, num.real(w, GL.C12), '%s e. RR' % GL.C12), ct], 'remulcld', '%s e. RR' % C12C), d3r], 'remulcld', '( %s x. %s ) e. RR' % (C12C, GL.D397)), ldr],
            'remulcld', '( ( %s x. %s ) x. ( log ` D ) ) e. RR' % (C12C, GL.D397))
    k1 = st([st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), ear], 'remulcld', '( 2 x. %s ) e. RR' % EACf), hbr], 'remulcld', '( ( 2 x. %s ) x. %s ) e. RR' % (EACf, HMBf))
    klr = st([k1, k2], 'remulcld', '%s e. RR' % GL.KLPf)
    l2p = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'),
                        w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')],
                       'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    kglr = st([a1(w, a, num.real(w, '( ; 5 0 / ; 4 9 )'), '( ; 5 0 / ; 4 9 ) e. RR'),
               st([a1(w, a, w.s([num.real(w, '; ; ; 1 0 2 4'), num.real(w, '; ; ; 1 6 3 2')], 'remulcli', '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. RR'), '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. RR'),
                   l2p], 'rerpdivcld', '( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) / ( log ` 2 ) ) e. RR')], 'remulcld', '%s e. RR' % GL.KGL)
    K = '( %s x. %s )' % (GL.KLPf, GL.KGL)
    kr = st([klr, kglr], 'remulcld', '%s e. RR' % K)
    assert tsub(split_imp(S_['gf2left'])[1], FRS) == '( abs ` %s ) <_ %s' % (V, K), tsub(split_imp(S_['gf2left'])[1], FRS)[:300]
    b1 = st([av3, left], 'eqbrtrrd', '( ( abs ` %s ) x. %s ) <_ %s' % (DM, TP, K))
    b2 = st([b1, st([adr, kr, tpp], 'lemuldivd', '( ( ( abs ` %s ) x. %s ) <_ %s <-> ( abs ` %s ) <_ ( %s / %s ) )' % (DM, TP, K, DM, K, TP))], 'mpbid',
            '( abs ` %s ) <_ ( %s / %s )' % (DM, K, TP))
    C11N = '; ; ; ; ; ; ; ; ; ; ; ; 2 0 0 0 0 0 0 0 0 0 0 0 0'
    c11r = st([a1(w, a, num.real(w, C11N), '%s e. RR' % C11N), st([ct, a1(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '( CTau ^ 3 ) e. RR')], 'remulcld',
              '%s e. RR' % L.C11)
    L3 = '( ( log ` D ) ^ 3 )'
    D7 = GL.D7
    tr_ = st([st([c11r, st([ldr, a1(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '%s e. RR' % L3)], 'remulcld', '( %s x. %s ) e. RR' % (L.C11, L3)),
              st([st([drp, litr(w, a, '-u ( 7 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % D7)], 'rpred', '%s e. RR' % D7)], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (L.C11, L3, D7))
    fin = st([adr, st([kr, tpp], 'rerpdivcld', '( %s / %s ) e. RR' % (K, TP)), tr_, b2, num_], 'letrd', split_imp(S_['gf2bt'])[1])
    w.qed([fin], 'idi', S_['gf2bt'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
