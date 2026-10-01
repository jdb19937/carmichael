"""Sortie C9: the L-function instance (sqhp0, lchrsqb, lndlchr)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from cl import lift
import congr as _cg
from c8_o import numst
from c8_n import sqparts, sqre_at, sqcc
from c9_b import decode
from c9_freeze import S as FS
import lin
lin.FASTPATH = True


def gen_sqhp0():
    w = W('sqhp0', 'A square about ` C ` of half-side ` R < Re C ` lies in the right half-plane.')
    A0 = '( ( C e. CC /\\ R e. RR ) /\\ R < ( Re ` C ) )'
    cs = w.s([], 'simpll', '( %s -> C e. CC )' % A0)
    rs = w.s([], 'simplr', '( %s -> R e. RR )' % A0)
    lt = w.s([], 'simpr', '( %s -> R < ( Re ` C ) )' % A0)
    a, b = SQA('C', 'R'), SQB('C', 'R')
    Au = '( %s /\\ u e. %s )' % (A0, SQ('C', 'R'))
    L = lambda st: lift(w, st, Au)
    ac, bc = sqcc(w, Au, L(cs), L(rs))
    pa = sqparts(w, Au, sqre_at(w, Au, L(cs), L(rs)))
    d = decode(w, Au, w.s([], 'simpr', '( %s -> u e. %s )' % (Au, SQ('C', 'R'))), ac, bc, a, b, SQ('C', 'R'), U='u')
    lv = {'( Re ` %s )' % a: w.s([ac], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Au, a)), '( Re ` u )': w.s([d[0]], 'recld', '( %s -> ( Re ` u ) e. RR )' % Au),
          '( Re ` C )': w.s([L(cs)], 'recld', '( %s -> ( Re ` C ) e. RR )' % Au), 'R': L(rs)}
    pos = lin8(w, Au, [pa[0], d[1], L(lt)], '0 < ( Re ` u )', lv)
    el = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Au), w.inst('elhp2')], 'syl', '( %s -> ( u e. %s <-> ( u e. CC /\\ 0 < ( Re ` u ) ) ) )' % (Au, HP0))
    uh = w.s([w.s([d[0], pos], 'jca', '( %s -> ( u e. CC /\\ 0 < ( Re ` u ) ) )' % Au), el], 'mpbird', '( %s -> u e. %s )' % (Au, HP0))
    goal = '( %s -> %s C_ %s )' % (A0, SQ('C', 'R'), HP0)
    assert goal == FS['sqhp0']
    w.qed([w.s([uh], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (A0, SQ('C', 'R'), HP0))], 'ssrdv', goal)
    return run8(w)


def c0_facts(w, A0, tr):
    """C0 e. CC, Re C0 = 2, Im C0 = T"""
    two = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
    c0 = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), w.s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'mulcld',
                                                                  '( %s -> ( _i x. T ) e. CC )' % A0)], 'addcld', '( %s -> %s e. CC )' % (A0, C0))
    re0 = w.s([two, tr], 'crred', '( %s -> ( Re ` %s ) = 2 )' % (A0, C0))
    im0 = w.s([two, tr], 'crimd', '( %s -> ( Im ` %s ) = T )' % (A0, C0))
    return c0, re0, im0


def in_hp(w, A0, c0, re0, U, ust, r):
    """( A0 -> U e. HP0 ) from ust : ( A0 -> U e. SQ(C0, r) ), r < 2"""
    rr = numst(w, A0, r, 'RR')
    lt = w.s([lin8(w, A0, [], '%s < 2' % r, {}), re0], 'breqtrrd', '( %s -> %s < ( Re ` %s ) )' % (A0, r, C0))
    f = tsub(stmt('sqhp0'), {'C': C0, 'R': r})
    a, c = ante_of(f)
    ss = w.s([w.s([w.s([c0, rr], 'jca', '( %s -> ( %s e. CC /\\ %s e. RR ) )' % (A0, C0, r)), lt], 'jca', '( %s -> %s )' % (A0, a)), w.inst('sqhp0')], 'syl', '( %s -> %s )' % (A0, c))
    return w.s([ss, ust], 'sseldd', '( %s -> %s e. %s )' % (A0, U, HP0))


def lf_hol(w, A0, chi):
    """( A0 -> HOL(LFN, HP0) ) from chi : ( A0 -> CHI ) (lchrhol0 at T = 0, binder z renamed s)"""
    f = tsub(stmt('lchrhol0'), {'T': '0'})
    a, c = ante_of(f)
    z0 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), lin8(w, A0, [], '0 <_ 0', {})], 'jca', '( %s -> ( 0 e. RR /\\ 0 <_ 0 ) )' % A0)
    hz = w.s([w.s([chi, z0], 'jca', '( %s -> %s )' % (A0, a)), w.inst('lchrhol0')], 'syl', '( %s -> %s )' % (A0, c))
    LFZ = '( z e. %s |-> %s )' % (HP0, LSs('z'))
    assert c == HOLG(LFZ, HP0), c
    sub = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = s -> -u z = -u s )')], 'oveq2d', '( z = s -> ( k ^c -u z ) = ( k ^c -u s ) )'),
                          w.s([w.s([], 'negeq', '( z = s -> -u z = -u s )')], 'oveq2d', '( z = s -> ( ( k + 1 ) ^c -u z ) = ( ( k + 1 ) ^c -u s ) )')], 'oveq12d',
                         '( z = s -> ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) = ( ( k ^c -u s ) - ( ( k + 1 ) ^c -u s ) ) )')], 'oveq2d',
                    '( z = s -> ( sum_ i e. ( 1 ... k ) ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` i ) ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) ) = ( sum_ i e. ( 1 ... k ) ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` i ) ) x. ( ( k ^c -u s ) - ( ( k + 1 ) ^c -u s ) ) ) )')],
               'sumeq2sdv', '( z = s -> %s = %s )' % (LSs('z'), LSs('s')))
    ce = w.s([w.s([sub], 'cbvmptv', '%s = %s' % (LFZ, LFN))], 'a1i', '( %s -> %s = %s )' % (A0, LFZ, LFN))
    cn = w.s([w.s([ce], 'eqcomd', '( %s -> %s = %s )' % (A0, LFN, LFZ)), w.s([hz, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, LFZ, HP0))], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, LFN, HP0))
    dm = w.s([w.s([hz, w.inst('simpr')], 'syl', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, HP0, LFZ)), w.s([w.s([ce], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, LFZ, LFN))], 'dmeqd',
              '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, LFZ, LFN))], 'sseqtrd', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, HP0, LFN))
    return w.s([cn, dm], 'jca', '( %s -> %s )' % (A0, HOLG(LFN, HP0)))


def gen_lchrsqb():
    w = W('lchrsqb', 'The continued ` L ( s , chi ) ` is bounded by ` 20 N ( abs T + 2 ) ` on the square of half-side ` 7 / 4 ` about ` 2 + i T ` ( ~ lchrab4 ; Lean has ` 15 N ( abs T + 2 ) ` on the disc of radius ` 7 / 4 ` ).')
    SQC = SQ(C0, R74)
    A0 = '( ( %s /\\ T e. RR ) /\\ U e. %s )' % (CHI, SQC)
    chi = w.s([], 'simpll', '( %s -> %s )' % (A0, CHI))
    tr = w.s([], 'simplr', '( %s -> T e. RR )' % A0)
    us = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, SQC))
    c0, re0, im0 = c0_facts(w, A0, tr)
    uh = in_hp(w, A0, c0, re0, 'U', us, R74)
    vx = w.s([w.s([], 'sumex', '%s e. _V' % LSs('U'))], 'a1i', '( %s -> %s e. _V )' % (A0, LSs('U')))
    fv, val = _cg.mptval(w, A0, 's', HP0, LSs('s'), 'U', uh, exs=vx, gen=w.g)
    assert val == LSs('U'), val
    r74 = numst(w, A0, R74, 'RR')
    a, b = SQA(C0, R74), SQB(C0, R74)
    ac, bc = sqcc(w, A0, c0, r74, c=C0, r=R74)
    pa = sqparts(w, A0, sqre_at(w, A0, c0, r74, c=C0, r=R74), c=C0, r=R74)
    d = decode(w, A0, us, ac, bc, a, b, SQC)
    ucc = d[0]
    lv = {'( Re ` %s )' % a: w.s([ac], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, a)), '( Re ` U )': w.s([ucc], 'recld', '( %s -> ( Re ` U ) e. RR )' % A0),
          '( Re ` %s )' % C0: w.s([c0], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, C0))}
    q4 = lin8(w, A0, [pa[0], d[1], re0], '( 1 / 4 ) <_ ( Re ` U )', lv)
    ab4 = w.s([w.s([chi, w.s([ucc, q4], 'jca', '( %s -> ( U e. CC /\\ ( 1 / 4 ) <_ ( Re ` U ) ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( U e. CC /\\ ( 1 / 4 ) <_ ( Re ` U ) ) ) )' % (A0, CHI)),
               w.inst('lchrab4')], 'syl', '( %s -> ( abs ` %s ) <_ ( ( 5 x. N ) x. ( 2 + ( abs ` U ) ) ) )' % (A0, LSs('U')))
    # abs U <_ abs T + 11/2
    sm = w.s([w.s([w.s([c0, r74], 'jca', '( %s -> ( %s e. CC /\\ %s e. RR ) )' % (A0, C0, R74)), us], 'jca', '( %s -> ( ( %s e. CC /\\ %s e. RR ) /\\ U e. %s ) )' % (A0, C0, R74, SQC)), w.inst('sqmem')],
             'syl', '( %s -> ( abs ` ( U - %s ) ) <_ ( 2 x. %s ) )' % (A0, C0, R74))
    uc0 = w.s([ucc, c0], 'subcld', '( %s -> ( U - %s ) e. CC )' % (A0, C0))
    tri = w.s([w.s([w.s([ucc, c0], 'npcand', '( %s -> ( ( U - %s ) + %s ) = U )' % (A0, C0, C0))], 'fveq2d', '( %s -> ( abs ` ( ( U - %s ) + %s ) ) = ( abs ` U ) )' % (A0, C0, C0)),
               w.s([uc0, c0], 'abstrid', '( %s -> ( abs ` ( ( U - %s ) + %s ) ) <_ ( ( abs ` ( U - %s ) ) + ( abs ` %s ) ) )' % (A0, C0, C0, C0, C0))], 'eqbrtrrd',
              '( %s -> ( abs ` U ) <_ ( ( abs ` ( U - %s ) ) + ( abs ` %s ) ) )' % (A0, C0, C0))
    ari = w.s([c0, w.inst('absreimle')], 'syl', '( %s -> ( abs ` %s ) <_ ( ( abs ` ( Re ` %s ) ) + ( abs ` ( Im ` %s ) ) ) )' % (A0, C0, C0, C0))
    a2 = w.s([w.s([re0], 'fveq2d', '( %s -> ( abs ` ( Re ` %s ) ) = ( abs ` 2 ) )' % (A0, C0)),
              w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), lin8(w, A0, [], '0 <_ 2', {})], 'absidd', '( %s -> ( abs ` 2 ) = 2 )' % A0)], 'eqtrd', '( %s -> ( abs ` ( Re ` %s ) ) = 2 )' % (A0, C0))
    at = w.s([im0], 'fveq2d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` T ) )' % (A0, C0))
    atr = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
    atr = w.s([atr], 'abscld', '( %s -> ( abs ` T ) e. RR )' % A0)
    lv2 = {'( abs ` U )': w.s([ucc], 'abscld', '( %s -> ( abs ` U ) e. RR )' % A0), '( abs ` ( U - %s ) )' % C0: w.s([uc0], 'abscld', '( %s -> ( abs ` ( U - %s ) ) e. RR )' % (A0, C0)),
           '( abs ` %s )' % C0: w.s([c0], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, C0)),
           '( abs ` ( Re ` %s ) )' % C0: w.s([w.s([w.s([c0], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, C0))], 'recnd', '( %s -> ( Re ` %s ) e. CC )' % (A0, C0))], 'abscld', '( %s -> ( abs ` ( Re ` %s ) ) e. RR )' % (A0, C0)),
           '( abs ` ( Im ` %s ) )' % C0: w.s([w.s([w.s([c0], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (A0, C0))], 'recnd', '( %s -> ( Im ` %s ) e. CC )' % (A0, C0))], 'abscld', '( %s -> ( abs ` ( Im ` %s ) ) e. RR )' % (A0, C0)),
           '( abs ` T )': atr}
    GU = '( 2 + ( abs ` U ) ) <_ ( ( abs ` T ) + ( ; 1 5 / 2 ) )'
    gu = lin8(w, A0, [sm, tri, ari, a2, at], GU, lv2)
    nn = w.s([w.s([chi, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) )' % A0), w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    nr = w.s([nn], 'nnred', '( %s -> N e. RR )' % A0)
    n0 = w.s([w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)], 'nn0ge0d', '( %s -> 0 <_ N )' % A0)
    fn = w.s([w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % A0), nr], 'remulcld', '( %s -> ( 5 x. N ) e. RR )' % A0)
    fn0 = w.s([w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % A0), nr, lin8(w, A0, [], '0 <_ 5', {}), n0], 'mulge0d', '( %s -> 0 <_ ( 5 x. N ) )' % A0)
    t2u = w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), lv2['( abs ` U )']], 'readdcld', '( %s -> ( 2 + ( abs ` U ) ) e. RR )' % A0)
    t152 = w.s([atr, numst(w, A0, '( ; 1 5 / 2 )', 'RR')], 'readdcld', '( %s -> ( ( abs ` T ) + ( ; 1 5 / 2 ) ) e. RR )' % A0)
    m1 = w.s([t2u, t152, fn, gu, fn0], 'lemul2ad', '( %s -> ( ( 5 x. N ) x. ( 2 + ( abs ` U ) ) ) <_ ( ( 5 x. N ) x. ( ( abs ` T ) + ( ; 1 5 / 2 ) ) ) )' % A0)
    NT = '( N x. ( abs ` T ) )'
    ntr = w.s([nr, atr], 'remulcld', '( %s -> %s e. RR )' % (A0, NT))
    nt0 = w.s([nr, atr, n0, w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'absge0d', '( %s -> 0 <_ ( abs ` T ) )' % A0)], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, NT))
    ntc = w.s([ntr], 'recnd', '( %s -> %s e. CC )' % (A0, NT))
    nc = w.s([nr], 'recnd', '( %s -> N e. CC )' % A0)
    atc = w.s([atr], 'recnd', '( %s -> ( abs ` T ) e. CC )' % A0)
    # expand both products
    L5 = '( ( 5 x. N ) x. ( ( abs ` T ) + ( ; 1 5 / 2 ) ) )'
    fnc = w.s([fn], 'recnd', '( %s -> ( 5 x. N ) e. CC )' % A0)
    tn = w.s([w.s([numst(w, A0, '; 2 0', 'RR'), nr], 'remulcld', '( %s -> ( ; 2 0 x. N ) e. RR )' % A0)], 'recnd', '( %s -> ( ; 2 0 x. N ) e. CC )' % A0)
    c152 = numst(w, A0, '( ; 1 5 / 2 )', 'CC')
    P5, P20 = '( ( 5 x. N ) x. ( abs ` T ) )', '( ( ; 2 0 x. N ) x. ( abs ` T ) )'
    e5 = w.s([fnc, atc, c152], 'adddid', '( %s -> %s = ( %s + ( ( 5 x. N ) x. ( ; 1 5 / 2 ) ) ) )' % (A0, L5, P5))
    e5b = w.s([numst(w, A0, '5', 'CC'), nc, atc], 'mulassd', '( %s -> %s = ( 5 x. %s ) )' % (A0, P5, NT))
    e20 = w.s([tn, atc, w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)], 'adddid', '( %s -> %s = ( %s + ( ( ; 2 0 x. N ) x. 2 ) ) )' % (A0, B20, P20))
    e20b = w.s([numst(w, A0, '; 2 0', 'CC'), nc, atc], 'mulassd', '( %s -> %s = ( ; 2 0 x. %s ) )' % (A0, P20, NT))
    m2 = lin8(w, A0, [e5, e5b, e20, e20b, nt0, n0], '%s <_ %s' % (L5, B20), {NT: ntr, 'N': nr, P5: w.s([fn, atr], 'remulcld', '( %s -> %s e. RR )' % (A0, P5)), P20: w.s([w.s([numst(w, A0, '; 2 0', 'RR'), nr], 'remulcld', '( %s -> ( ; 2 0 x. N ) e. RR )' % A0), atr], 'remulcld', '( %s -> %s e. RR )' % (A0, P20)), L5: w.s([fn, t152], 'remulcld', '( %s -> %s e. RR )' % (A0, L5)),
                                                                   B20: w.s([w.s([numst(w, A0, '; 2 0', 'RR'), nr], 'remulcld', '( %s -> ( ; 2 0 x. N ) e. RR )' % A0), w.s([atr, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)], 'readdcld', '( %s -> ( ( abs ` T ) + 2 ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, B20))})
    hol = lf_hol(w, A0, chi)
    lff = w.s([w.s([hol, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, LFN, HP0)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (A0, LFN, HP0))
    lsc = w.s([fv, w.s([lff, uh], 'ffvelcdmd', '( %s -> ( %s ` U ) e. CC )' % (A0, LFN))], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, LSs('U')))
    als = w.s([lsc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, LSs('U')))
    X5 = '( ( 5 x. N ) x. ( 2 + ( abs ` U ) ) )'
    x5 = w.s([fn, t2u], 'remulcld', '( %s -> %s e. RR )' % (A0, X5))
    l5r = w.s([fn, t152], 'remulcld', '( %s -> %s e. RR )' % (A0, L5))
    b20r = w.s([w.s([numst(w, A0, '; 2 0', 'RR'), nr], 'remulcld', '( %s -> ( ; 2 0 x. N ) e. RR )' % A0), w.s([atr, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)], 'readdcld', '( %s -> ( ( abs ` T ) + 2 ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, B20))
    bnd = w.s([als, l5r, b20r, w.s([als, x5, l5r, ab4, m1], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, LSs('U'), L5)), m2], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, LSs('U'), B20))
    goal = '( %s -> ( abs ` ( %s ` U ) ) <_ %s )' % (A0, LFN, B20)
    assert goal == FS['lchrsqb']
    w.qed([w.s([fv], 'fveq2d', '( %s -> ( abs ` ( %s ` U ) ) = ( abs ` %s ) )' % (A0, LFN, LSs('U'))), bnd], 'eqbrtrd', goal)
    return run8(w)


def gen_lndlchr():
    w = W('lndlchr', 'The Landau expansion for ` L ( s , chi ) ` , ` chi ` nonprincipal (Lean ` norm_logDeriv_sub_sum_zeroDiskFinset_le ` , PartialFractions.lean): on the disc of radius ` 3 / 2 ` about ` 2 + i T ` , ` L\' / L ` minus the sum of ` ( L holord q ) / ( s - q ) ` over the zeros ` q ` in the square of half-side ` 13 / 8 ` is at most ` 6272 ( log ( 20 N ( abs T + 2 ) / abs L ( 2 + i T ) ) + W log 26 ) ` , ` W ` a bound for the multiplicity mass ( ~ lndgen , ~ lchrsqb ).')
    A0, GOALC = ante_of(FS['lndlchr'])
    X1, X2 = top_and(A0)
    chi = w.s([], 'simpll', '( %s -> %s )' % (A0, CHI))
    y2 = w.s([], 'simplr', '( %s -> %s )' % (A0, top_and(X1)[1]))
    tr = w.s([y2, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
    wsum = w.s([y2, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, top_and(top_and(X1)[1])[1]))
    x3 = w.s([], 'simpr', '( %s -> %s )' % (A0, X2))
    c0, re0, im0 = c0_facts(w, A0, tr)
    hol = lf_hol(w, A0, chi)
    r74 = numst(w, A0, R74, 'RR')
    lt = w.s([lin8(w, A0, [], '%s < 2' % R74, {}), re0], 'breqtrrd', '( %s -> %s < ( Re ` %s ) )' % (A0, R74, C0))
    f = tsub(stmt('sqhp0'), {'C': C0, 'R': R74})
    fa, fc = ante_of(f)
    shp = w.s([w.s([w.s([c0, r74], 'jca', '( %s -> ( %s e. CC /\\ %s e. RR ) )' % (A0, C0, R74)), lt], 'jca', '( %s -> %s )' % (A0, fa)), w.inst('sqhp0')], 'syl', '( %s -> %s )' % (A0, fc))
    SQC = SQ(C0, R74)
    Ax = '( %s /\\ x e. %s )' % (A0, SQC)
    SB = tsub(stmt('lchrsqb'), {'U': 'x'})
    sba, sbc = ante_of(SB)
    sbx = w.s([w.s([w.s([lift(w, chi, Ax), lift(w, tr, Ax)], 'jca', '( %s -> ( %s /\\ T e. RR ) )' % (Ax, CHI)), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, SQC))], 'jca', '( %s -> %s )' % (Ax, sba)),
               w.inst('lchrsqb')], 'syl', '( %s -> %s )' % (Ax, sbc))
    FBDL = 'A. x e. %s %s' % (SQC, sbc)
    fbx = w.s([sbx], 'ralrimiva', '( %s -> %s )' % (A0, FBDL))
    nn = w.s([w.s([chi, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) )' % A0), w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    nr = w.s([nn], 'nnred', '( %s -> N e. RR )' % A0)
    atr = w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'abscld', '( %s -> ( abs ` T ) e. RR )' % A0)
    b20r = w.s([w.s([numst(w, A0, '; 2 0', 'RR'), nr], 'remulcld', '( %s -> ( ; 2 0 x. N ) e. RR )' % A0), w.s([atr, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)], 'readdcld', '( %s -> ( ( abs ` T ) + 2 ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, B20))
    # L ( C0 ) =/= 0
    ch = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (A0, C0, HP0, C0, C0))
    c0h = w.s([w.s([c0, w.s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, C0))], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (A0, C0, C0)), ch], 'mpbird', '( %s -> %s e. %s )' % (A0, C0, HP0))
    vx = w.s([w.s([], 'sumex', '%s e. _V' % LSs(C0))], 'a1i', '( %s -> %s e. _V )' % (A0, LSs(C0)))
    fv, val = _cg.mptval(w, A0, 's', HP0, LSs('s'), C0, c0h, exs=vx, gen=w.g)
    assert val == LSs(C0), val
    g1 = w.s([lin8(w, A0, [], '1 < 2', {}), re0], 'breqtrrd', '( %s -> 1 < ( Re ` %s ) )' % (A0, C0))
    z1 = w.s([c0, g1], 'jca', '( %s -> ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (A0, C0, C0))
    AG = tsub(stmt('lchragr'), {'Z': C0})
    aga, agc = ante_of(AG)
    agr = w.s([w.s([chi, z1], 'jca', '( %s -> %s )' % (A0, aga)), w.inst('lchragr')], 'syl', '( %s -> %s )' % (A0, agc))
    NE = tsub(stmt('lchrne0'), {'Z': C0})
    nea, nec = ante_of(NE)
    ne = w.s([w.s([w.s([chi, w.inst('simpl')], 'syl', '( %s -> ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) )' % A0), z1], 'jca', '( %s -> %s )' % (A0, nea)), w.inst('lchrne0')], 'syl', '( %s -> %s )' % (A0, nec))
    DS = agc.split(' = ', 1)[1]
    lc0 = w.s([w.s([fv, agr], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (A0, LFN, C0, DS)), ne], 'eqnetrd', '( %s -> ( %s ` %s ) =/= 0 )' % (A0, LFN, C0))
    LG_ = tsub(stmt('lndgen'), {'F': LFN, 'D': HP0, 'C': C0, 'B': B20})
    la, lcc = ante_of(LG_)
    P1, P2, P3 = top_and(la)
    p1 = w.s([hol, w.s([c0, shp], 'jca', '( %s -> ( %s e. CC /\\ %s C_ %s ) )' % (A0, C0, SQC, HP0))], 'jca', '( %s -> %s )' % (A0, P1))
    Q1, Q2 = top_and(P2)
    p2 = w.s([w.s([b20r, fbx], 'jca', '( %s -> %s )' % (A0, Q1)), w.s([lc0, wsum], 'jca', '( %s -> %s )' % (A0, Q2))], 'jca', '( %s -> %s )' % (A0, P2))
    assert P3 == X2, (P3, X2)
    goal = FS['lndlchr']
    assert goal == '( %s -> %s )' % (A0, lcc), (goal, lcc)
    w.qed([w.s([p1, p2, x3], '3jca', '( %s -> %s )' % (A0, la)), w.inst('lndgen')], 'syl', goal)
    return run8(w)


def _clo(w, A0, lv):
    import cl as _cl
    c = _cl.Closure(w, A0, lv)
    for k in lv:
        c.atom(k)
    return c


if __name__ == '__main__':
    gen_sqhp0()
    gen_lchrsqb()
    gen_lndlchr()
