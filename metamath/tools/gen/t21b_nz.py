"""Sortie T21b: t21nzb (no_zero_in_box)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *
import congr as _cg

EY = '( N DChrLF y )'
MY = '( N DChrCond y )'
PY = '( N DChrPrim y )'
EPY = '( %s DChrLF %s )' % (MY, PY)
NY = '( N e. NN /\\ y e. ( Base ` ( DChr ` N ) ) )'
DBN = '( Base ` ( DChr ` N ) )'
U0 = '( 0g ` ( DChr ` N ) )'


def ysub(t):
    return t.replace('( N DChrCond X )', MY).replace('( N DChrPrim X )', PY).replace('( N DChrLF X )', EY)


def gen_nzb():
    w = W('t21nzb', 'Zero transfer (zone IV(a)): when ` E1 ` ( zeta ) has no zero in ` [ U , 1 ] x. [ - V , V ] ` , ` U <_ T ` , and no conductor ` 2 <_ m <_ Z ` carrying a primitive character with a zero in ` [ T , 1 ] x. [ - V , V ] ` divides ` N <_ Z ` , no character mod ` N ` has a zero in ` [ T , 1 ] x. [ - V , V ] ` (Lean ` no_zero_in_box ` ; ~ t21lfp , ~ t21pfne , ~ zc1tord , ~ dchrconddvdn ).')
    A0, concl = split_imp(SB['t21nzb'])
    ZO = ZFo(HALF, 'W')
    ZR = ZF(EY, HALF, 'W')
    C = '( %s /\\ ( y e. %s /\\ p e. %s ) )' % (A0, DBN, ZO)
    A1 = '( %s /\\ T <_ ( Re ` p ) )' % C
    s = S_(w, A1)
    u = unpackA(w, A0)
    L1 = lambda st: lift(w, st, A1)
    nn = L1(u['N e. NN']); tr = L1(u['T e. RR']); ur = L1(u['U e. RR']); ut = L1(u['U <_ T'])
    vr = L1(u['V e. RR']); wr = L1(u['W e. RR']); zr = L1(u['Z e. RR']); nz = L1(u['N <_ Z'])
    zeta = L1(u[ZETA('U', 'V')]); hb = L1(u[HBAD('Z', 'T', 'V', 'N', y='j')])
    yin = s([], 'simplrl', 'y e. %s' % DBN)
    pino = s([], 'simplrr', 'p e. %s' % ZO)
    tre = s([], 'simpr', 'T <_ ( Re ` p )')
    ny = s([nn, yin], 'jca', NY)
    # p e. ZF_r
    phr = lambda b: '( %s =/= 1 /\\ ( %s ` %s ) = 0 )' % (b, EY, b)
    cro, _ = w.wcongr(phr('r'), {'r': 'o'}, 'r = o', {'r': w.s([], 'id', '( r = o -> r = o )')})
    zeq = w.s([cro], 'cbvrabv', '%s = %s' % (ZR, ZO))
    pin = s([pino, s([s([zeq], 'eqcomi', '%s = %s' % (ZO, ZR)) if False else s([w.s([zeq], 'eqcomi', '%s = %s' % (ZO, ZR))], 'a1i', '%s = %s' % (ZO, ZR))], 'x', 'x') if False else None], 'x', 'x') if False else None
    zeqc = w.s([zeq], 'eqcomi', '%s = %s' % (ZO, ZR))
    pin = s([pino, s([zeqc], 'a1i', '%s = %s' % (ZO, ZR))], 'eleqtrd', 'p e. %s' % ZR)
    half = s([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF)
    CND = '( p e. CC /\\ ( ( %s <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 ) /\\ ( abs ` ( Im ` p ) ) <_ W ) /\\ ( p =/= 1 /\\ ( %s ` p ) = 0 ) )' % (HALF, EY)
    el = ap(w, A1, [half, wr], 't21zfel', '( p e. %s <-> %s )' % (ZR, CND))
    cnd = s([pin, el], 'mpbid', CND)
    pc = s([cnd], 'simp1d', 'p e. CC')
    mid = s([cnd], 'simp2d', '( ( %s <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 ) /\\ ( abs ` ( Im ` p ) ) <_ W )' % HALF)
    rlo = s([s([mid], 'simpld', '( %s <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 )' % HALF)], 'simpld', '%s <_ ( Re ` p )' % HALF)
    rhi = s([s([mid], 'simpld', '( %s <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 )' % HALF)], 'simprd', '( Re ` p ) <_ 1')
    lst = s([cnd], 'simp3d', '( p =/= 1 /\\ ( %s ` p ) = 0 )' % EY)
    pn1 = s([lst], 'simpld', 'p =/= 1')
    ez = s([lst], 'simprd', '( %s ` p ) = 0' % EY)
    rer = s([pc], 'recld', '( Re ` p ) e. RR')
    re0 = lin.linarith(w, A1, [rlo], '0 < ( Re ` p )', leaves={'( Re ` p )': rer})
    php = s([s([pc, re0], 'jca', '( p e. CC /\\ 0 < ( Re ` p ) )'), s([s([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( p e. %s <-> ( p e. CC /\\ 0 < ( Re ` p ) ) )' % HP0)], 'mpbird', 'p e. %s' % HP0)
    IM = '( abs ` ( Im ` p ) )'
    imr = s([s([s([pc], 'imcld', '( Im ` p ) e. RR')], 'recnd', '( Im ` p ) e. CC')], 'abscld', '%s e. RR' % IM)
    # ---- principal case: E1 ( p ) = 0 against the zeta clearance
    Ap = '( %s /\\ y = %s )' % (A1, U0)
    sp = S_(w, Ap)
    Lp = lambda st: lift(w, st, Ap)
    tord = ap(w, Ap, [Lp(nn), Lp(yin), sp([], 'simpr', 'y = %s' % U0), Lp(php)], 'zc1tord',
              '( ( %s holord p ) = ( %s holord p ) /\\ ( ( %s ` p ) = 0 <-> ( %s ` p ) = 0 ) )' % (EY, E1, EY, E1))
    e1z = sp([Lp(ez), sp([tord], 'simprd', '( ( %s ` p ) = 0 <-> ( %s ` p ) = 0 )' % (EY, E1))], 'mpbid', '( %s ` p ) = 0' % E1)
    Ap2 = '( %s /\\ %s <_ V )' % (Ap, IM)
    s2 = S_(w, Ap2)
    L2 = lambda st: lift(w, st, Ap2)
    ZB = '( ( ( U <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 ) /\\ %s <_ V ) -> ( %s ` p ) =/= 0 )' % (IM, E1)
    zb_s = lambda sv: '( ( ( U <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 ) /\\ ( abs ` ( Im ` %s ) ) <_ V ) -> ( %s ` %s ) =/= 0 )' % (sv, sv, sv, E1, sv)
    cz, _ = w.wcongr(zb_s('s'), {'s': 'p'}, 's = p', {'s': w.s([], 'id', '( s = p -> s = p )')})
    zp = s2([L2(zeta), L2(pc), w.s([cz], 'rspcv', '( p e. CC -> ( %s -> %s ) )' % (ZETA('U', 'V'), ZB))], 'x', 'x') if False else None
    zp = s2([L2(pc), L2(zeta), w.s([cz], 'rspcv', '( p e. CC -> ( %s -> %s ) )' % (ZETA('U', 'V'), ZB))], 'sylc', ZB)
    ure = lin.linarith(w, Ap2, [L2(ut), L2(tre)], 'U <_ ( Re ` p )', leaves={'U': L2(ur), 'T': L2(tr), '( Re ` p )': L2(rer)})
    pre = s2([s2([ure, L2(rhi)], 'jca', '( U <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 )'), s2([], 'simpr', '%s <_ V' % IM)], 'jca', '( ( U <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 ) /\\ %s <_ V )' % IM)
    ne1 = s2([s2([pre, zp], 'mpd', '( %s ` p ) =/= 0' % E1)], 'neneqd', '-. ( %s ` p ) = 0' % E1)
    case1 = sp([lift(w, e1z, Ap2), ne1], 'pm2.65da', '-. %s <_ V' % IM)
    # ---- nonprincipal case: the conductor M is a bad conductor dividing N
    An = '( %s /\\ y =/= %s )' % (A1, U0)
    sn = S_(w, An)
    Ln = lambda st: lift(w, st, An)
    nyn = Ln(ny)
    lf = ap(w, An, [Ln(nn), Ln(yin), Ln(php)], 't21lfp', '( %s ` p ) = ( %s x. ( %s ` p ) )' % (EY, ysub(PFX('p')), EPY))
    PFp = ysub(PFX('p'))
    pfn = ap(w, An, [Ln(nn), Ln(yin), Ln(pc), Ln(re0)], 't21pfne', '%s =/= 0' % PFp)
    PFW = ysub('( w e. CC |-> %s )' % PFX('w'))
    dph = sn([nyn, w.inst('zl2dph')], 'syl', '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (PFW, PFW))
    pfwf = sn([sn([dph], 'simpld', '%s e. ( CC -cn-> CC )' % PFW), w.inst('cncff')], 'syl', '%s : CC --> CC' % PFW)
    pfv = sn([Ln(pc), w.inst('zl2dpv')], 'syl', '( %s ` p ) = %s' % (PFW, PFp))
    pfc = sn([pfv, sn([pfwf, Ln(pc)], 'ffvelcdmd', '( %s ` p ) e. CC' % PFW)], 'eqeltrrd', '%s e. CC' % PFp)
    mx = sn([sn([nyn, w.inst('dchrcondnn')], 'syl', '%s e. NN' % MY), sn([nyn, w.inst('dchrprimcl')], 'syl', '%s e. ( Base ` ( DChr ` %s ) )' % (PY, MY))], 'jca',
            '( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) )' % (MY, PY, MY))
    mnn = sn([mx], 'simpld', '%s e. NN' % MY)
    ephol = sn([mx, w.inst('zl1ehol')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (EPY, HP0, HP0, EPY))
    epf = sn([sn([ephol], 'simpld', '%s e. ( %s -cn-> CC )' % (EPY, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (EPY, HP0))
    epc = sn([epf, Ln(php)], 'ffvelcdmd', '( %s ` p ) e. CC' % EPY)
    prod0 = sn([sn([lf], 'eqcomd', '( %s x. ( %s ` p ) ) = ( %s ` p )' % (PFp, EPY, EY)), Ln(ez)], 'eqtrd', '( %s x. ( %s ` p ) ) = 0' % (PFp, EPY))
    m0 = sn([pfc, epc], 'mul0ord', '( ( %s x. ( %s ` p ) ) = 0 <-> ( %s = 0 \\/ ( %s ` p ) = 0 ) )' % (PFp, EPY, PFp, EPY))
    orr = sn([prod0, m0], 'mpbid', '( %s = 0 \\/ ( %s ` p ) = 0 )' % (PFp, EPY))
    epz = sn([sn([pfn], 'neneqd', '-. %s = 0' % PFp), sn([orr], 'ord', '( -. %s = 0 -> ( %s ` p ) = 0 )' % (PFp, EPY))], 'mpd', '( %s ` p ) = 0' % EPY)
    # M >= 2
    ceq = sn([nyn, w.inst('dchrcondeq1')], 'syl', '( y = %s <-> %s = 1 )' % (U0, MY))
    mn1 = sn([sn([], 'simpr', 'y =/= %s' % U0), sn([ceq], 'necon3bid', '( y =/= %s <-> %s =/= 1 )' % (U0, MY))], 'mpbid', '%s =/= 1' % MY)
    m1 = sn([mn1, sn([mnn, w.inst('nngt1ne1')], 'syl', '( 1 < %s <-> %s =/= 1 )' % (MY, MY))], 'mpbird', '1 < %s' % MY)
    mz = sn([mnn], 'nnzd', '%s e. ZZ' % MY)
    m2a = sn([m1, ap(w, An, [sn([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), mz], 'zltp1le', '( 1 < %s <-> ( 1 + 1 ) <_ %s )' % (MY, MY))], 'mpbid', '( 1 + 1 ) <_ %s' % MY)
    m2 = sn([w.s([], '1p1e2', '( 1 + 1 ) = 2') and sn([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2'), m2a], 'eqbrtrrd', '2 <_ %s' % MY)
    # M || N, M <_ floor Z
    mdv = sn([nyn, w.inst('dchrconddvdn')], 'syl', '%s || N' % MY)
    mle = sn([mdv, sn([mz, Ln(nn)], 'x', 'x') if False else sn([sn([mz, Ln(nn)], 'jca', '( %s e. ZZ /\\ N e. NN )' % MY), w.inst('dvdsle')], 'syl', '( %s || N -> %s <_ N )' % (MY, MY))], 'mpd', '%s <_ N' % MY)
    mzr = lin.linarith(w, An, [mle, Ln(nz)], '%s <_ Z' % MY, leaves={MY: sn([mnn], 'nnred', '%s e. RR' % MY), 'N': sn([Ln(nn)], 'nnred', 'N e. RR'), 'Z': Ln(zr)})
    mfl = sn([mzr, sn([sn([Ln(zr), mz], 'jca', '( Z e. RR /\\ %s e. ZZ )' % MY), w.inst('flge')], 'syl', '( %s <_ Z <-> %s <_ ( |_ ` Z ) )' % (MY, MY))], 'mpbid', '%s <_ ( |_ ` Z )' % MY)
    flz = sn([Ln(zr)], 'flcld', '( |_ ` Z ) e. ZZ')
    melfz = sn([sn([mz, sn([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), flz], '3jca', '( %s e. ZZ /\\ 2 e. ZZ /\\ ( |_ ` Z ) e. ZZ )' % MY), w.inst('elfz')], 'syl',
               '( %s e. ( 2 ... ( |_ ` Z ) ) <-> ( 2 <_ %s /\\ %s <_ ( |_ ` Z ) ) )' % (MY, MY, MY))
    mfz = sn([sn([m2, mfl], 'jca', '( 2 <_ %s /\\ %s <_ ( |_ ` Z ) )' % (MY, MY)), melfz], 'mpbird', '%s e. ( 2 ... ( |_ ` Z ) )' % MY)
    # p in the box of the primitive character
    ZE = ZF(EPY, 'T', 'V')
    CND2 = '( p e. CC /\\ ( ( T <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 ) /\\ %s <_ V ) /\\ ( p =/= 1 /\\ ( %s ` p ) = 0 ) )' % (IM, EPY)
    An2 = '( %s /\\ %s <_ V )' % (An, IM)
    s3 = S_(w, An2)
    L3 = lambda st: lift(w, st, An2)
    el2 = ap(w, An2, [L3(tr), L3(vr)], 't21zfel', '( p e. %s <-> %s )' % (ZE, CND2))
    c2 = s3([L3(pc), s3([s3([L3(tre), L3(rhi)], 'jca', '( T <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 )'), s3([], 'simpr', '%s <_ V' % IM)], 'jca', '( ( T <_ ( Re ` p ) /\\ ( Re ` p ) <_ 1 ) /\\ %s <_ V )' % IM),
             s3([L3(pn1), L3(epz)], 'jca', '( p =/= 1 /\\ ( %s ` p ) = 0 )' % EPY)], '3jca', CND2)
    pinE = s3([c2, el2], 'mpbird', 'p e. %s' % ZE)
    ZEo = '{ o e. %s | ( o =/= 1 /\\ ( ( %s DChrLF %s ) ` o ) = 0 ) }' % (BOX('T', 'V'), MY, PY)
    phe = lambda b: '( %s =/= 1 /\\ ( %s ` %s ) = 0 )' % (b, EPY, b)
    cro2, _ = w.wcongr(phe('r'), {'r': 'o'}, 'r = o', {'r': w.s([], 'id', '( r = o -> r = o )')})
    zeq2 = w.s([cro2], 'cbvrabv', '%s = %s' % (ZE, ZEo))
    pinEo = s3([pinE, s3([zeq2], 'a1i', '%s = %s' % (ZE, ZEo))], 'eleqtrd', 'p e. %s' % ZEo)
    ne0 = s3([pinEo, w.inst('ne0i')], 'syl', '%s =/= (/)' % ZEo)
    pp = sn([nyn, w.inst('dchrprimprim')], 'syl', '( %s DChrCond %s ) = %s' % (MY, PY, MY))
    phj = lambda j: '( ( %s DChrCond %s ) = %s /\\ { o e. %s | ( o =/= 1 /\\ ( ( %s DChrLF %s ) ` o ) = 0 ) } =/= (/) )' % (MY, j, MY, BOX('T', 'V'), MY, j)
    cj, _ = w.wcongr(phj('j'), {'j': PY}, 'j = %s' % PY, {'j': w.s([], 'id', '( j = %s -> j = %s )' % (PY, PY))})
    BCM = BC('T', 'V', MY, y='j')
    elj = w.s([cj], 'elrab', '( %s e. %s <-> ( %s e. ( Base ` ( DChr ` %s ) ) /\\ %s ) )' % (PY, BCM, PY, MY, phj(PY)))
    pbc = s3([s3([L3(sn([mx], 'simprd', '%s e. ( Base ` ( DChr ` %s ) )' % (PY, MY))), s3([L3(pp), ne0], 'jca', phj(PY))], 'jca', '( %s e. ( Base ` ( DChr ` %s ) ) /\\ %s )' % (PY, MY, phj(PY))), elj], 'mpbir2and', 'x') if False else None
    pbc = s3([s3([L3(sn([mx], 'simprd', '%s e. ( Base ` ( DChr ` %s ) )' % (PY, MY))), s3([L3(pp), ne0], 'jca', phj(PY))], 'jca', '( %s e. ( Base ` ( DChr ` %s ) ) /\\ %s )' % (PY, MY, phj(PY))),
              s3([elj], 'a1i', '( %s e. %s <-> ( %s e. ( Base ` ( DChr ` %s ) ) /\\ %s ) )' % (PY, BCM, PY, MY, phj(PY)))], 'mpbird', '%s e. %s' % (PY, BCM))
    bcne = s3([pbc, w.inst('ne0i')], 'syl', '%s =/= (/)' % BCM)
    # M in the bad set
    BADJ = BAD('Z', 'T', 'V', y='j')
    bce = lambda e: '%s =/= (/)' % BC('T', 'V', e, y='j')
    ce, _ = w.wcongr(bce('e'), {'e': MY}, 'e = %s' % MY, {'e': w.s([], 'id', '( e = %s -> e = %s )' % (MY, MY))})
    ele = w.s([ce], 'elrab', '( %s e. %s <-> ( %s e. ( 2 ... ( |_ ` Z ) ) /\\ %s ) )' % (MY, BADJ, MY, bce(MY)))
    mbad = s3([s3([L3(mfz), bcne], 'jca', '( %s e. ( 2 ... ( |_ ` Z ) ) /\\ %s )' % (MY, bce(MY))), s3([ele], 'a1i', '( %s e. %s <-> ( %s e. ( 2 ... ( |_ ` Z ) ) /\\ %s ) )' % (MY, BADJ, MY, bce(MY)))], 'mpbird', '%s e. %s' % (MY, BADJ))
    ci, _ = w.wcongr('-. i || N', {'i': MY}, 'i = %s' % MY, {'i': w.s([], 'id', '( i = %s -> i = %s )' % (MY, MY))})
    nd = s3([mbad, L3(hb), w.s([ci], 'rspcv', '( %s e. %s -> ( %s -> -. %s || N ) )' % (MY, BADJ, HBAD('Z', 'T', 'V', 'N', y='j'), MY))], 'sylc', '-. %s || N' % MY)
    case2 = sn([L3(mdv), nd], 'pm2.65da', '-. %s <_ V' % IM)
    both = s([case1, case2], 'pm2.61dane', '-. %s <_ V' % IM)
    lt = s([both, s([vr, imr], 'ltnled', '( V < %s <-> -. %s <_ V )' % (IM, IM))], 'mpbird', 'V < %s' % IM)
    imp = w.s([lt], 'ex', '( %s -> ( T <_ ( Re ` p ) -> V < %s ) )' % (C, IM))
    w.qed([imp], 'ralrimivva', SB['t21nzb'])
    return go(w)


if __name__ == '__main__':
    gen_nzb()
