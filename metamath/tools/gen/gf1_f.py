"""Sortie GF1, section F: characters times n^-s (gf1cxb, gf1chb, gf1chc).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_f.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *
from mvlib import ringeq

only = sys.argv[1:]
S['gf1cxb'] = '( ( K e. NN /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) -> ( ( K ^c -u S ) e. CC /\\ ( abs ` ( K ^c -u S ) ) <_ 1 ) )'


def gen_cxb():
    w = W('gf1cxb', '` abs ( K ^c -u S ) <_ 1 ` for ` K e. NN ` and ` 0 <_ Re S ` (Lean ` norm_natCast_cpow_neg_le_one ` ).')
    X0, CONC = split_imp(S['gf1cxb'])
    d = mk(w, X0)
    kn = proj(w, X0, 'K e. NN'); sc = proj(w, X0, 'S e. CC'); s0 = proj(w, X0, '0 <_ ( Re ` S )')
    kc = d('nncnd', [kn], 'K e. CC'); kne = d('nnne0d', [kn], 'K =/= 0')
    cc = d('cxpcld', [kc, d('negcld', [sc], '-u S e. CC')], '( K ^c -u S ) e. CC')
    ab = d('syl2anc', [kn, sc, w.inst('cxpnnabs')], '( abs ` ( K ^c -u S ) ) = ( K ^c -u ( Re ` S ) )')
    kr = d('nnred', [kn], 'K e. RR'); k1 = d('nnge1d', [kn], '1 <_ K')
    rs = d('recld', [sc], '( Re ` S ) e. RR')
    nr = d('renegcld', [rs], '-u ( Re ` S ) e. RR')
    le = lin.linarith(w, X0, [s0], '-u ( Re ` S ) <_ 0', closure=Closure(w, X0, {'( Re ` S )': rs}))
    cl = d('syl3anc', [d('jca', [kr, k1], '( K e. RR /\\ 1 <_ K )'), d('jca', [nr, a1(w, X0, '0re', '0 e. RR')], '( -u ( Re ` S ) e. RR /\\ 0 e. RR )'), le, w.inst('cxplea')],
           '( K ^c -u ( Re ` S ) ) <_ ( K ^c 0 )')
    c0 = d('syl', [kc, w.inst('cxp0')], '( K ^c 0 ) = 1')
    b = chain(w, X0, ['( abs ` ( K ^c -u S ) )', '( K ^c -u ( Re ` S ) )', '( K ^c 0 )', '1'], [ab, cl, c0], ['=', '<_', '='])
    fin = d('jca', [cc, b], CONC)
    w.qed([fin], 'idi', S['gf1cxb'])
    return run(w, only)


ZRK = ZR('N', 'K')
XK = '( X ` %s )' % ZRK
YK = '( Y ` %s )' % ZRK


def gen_chb():
    w = W('gf1chb', '` chi ( K ) K ^c -u S ` is a complex number of absolute value at most ` 1 ` on ` 0 <_ Re S ` ( ~ cen2chv , ~ gf1cxb ).')
    X0, CONC = split_imp(S['gf1chb'])
    d = mk(w, X0)
    nn = proj(w, X0, 'N e. NN'); xb = proj(w, X0, 'X e. %s' % DB_('N')); kn = proj(w, X0, 'K e. NN')
    ch = d('syl', [d('jca', [d('jca', [nn, xb], '( N e. NN /\\ X e. %s )' % DB_('N')), d('nnzd', [kn], 'K e. ZZ')], '( ( N e. NN /\\ X e. %s ) /\\ K e. ZZ )' % DB_('N')), w.inst('cen2chv')],
           '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (XK, XK))
    cx = d('syl', [d('jca', [kn, d('jca', [proj(w, X0, 'S e. CC'), proj(w, X0, '0 <_ ( Re ` S )')], '( S e. CC /\\ 0 <_ ( Re ` S ) )')], '( K e. NN /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) )'), w.inst('gf1cxb')],
           split_imp(S['gf1cxb'])[1])
    xc = d('simpld', [ch], '%s e. CC' % XK); x1 = d('simprd', [ch], '( abs ` %s ) <_ 1' % XK)
    kc = d('simpld', [cx], '( K ^c -u S ) e. CC'); k1 = d('simprd', [cx], '( abs ` ( K ^c -u S ) ) <_ 1')
    pc = d('mulcld', [xc, kc], '( %s x. ( K ^c -u S ) ) e. CC' % XK)
    ab = d('absmuld', [xc, kc], '( abs ` ( %s x. ( K ^c -u S ) ) ) = ( ( abs ` %s ) x. ( abs ` ( K ^c -u S ) ) )' % (XK, XK))
    m = d('lemul12ad', [d('abscld', [xc], '( abs ` %s ) e. RR' % XK), a1(w, X0, '1re', '1 e. RR'), d('abscld', [kc], '( abs ` ( K ^c -u S ) ) e. RR'), a1(w, X0, '1re', '1 e. RR'),
                        d('absge0d', [xc], '0 <_ ( abs ` %s )' % XK), x1, d('absge0d', [kc], '0 <_ ( abs ` ( K ^c -u S ) )'), k1],
           '( ( abs ` %s ) x. ( abs ` ( K ^c -u S ) ) ) <_ ( 1 x. 1 )' % XK)
    b = chain(w, X0, ['( abs ` ( %s x. ( K ^c -u S ) ) )' % XK, '( ( abs ` %s ) x. ( abs ` ( K ^c -u S ) ) )' % XK, '( 1 x. 1 )', '1'],
              [ab, m, a1(w, X0, '1t1e1', '( 1 x. 1 ) = 1')], ['=', '<_', '='])
    fin = d('jca', [pc, b], CONC)
    w.qed([fin], 'idi', S['gf1chb'])
    return run(w, only)


def gen_chc():
    w = W('gf1chc', '` chi_j ( K ) K ^c -u S . * ( chi_k ( K ) K ^c -u T ) = ( chi_j chi_k ^ -1 ) ( K ) K ^c -u ( S + * T ) ` (Lean ` char_cpow_mul_conj ` ; ` conj_char_apply ` is ~ dchrinv ).')
    X0, CONC = split_imp(S['gf1chc'])
    d = mk(w, X0)
    nn = proj(w, X0, 'N e. NN'); xb = proj(w, X0, 'X e. %s' % DB_('N')); yb = proj(w, X0, 'Y e. %s' % DB_('N'))
    sc = proj(w, X0, 'S e. CC'); tc = proj(w, X0, 'T e. CC'); kn = proj(w, X0, 'K e. NN')
    G = '( DChr ` N )'; Zn = '( Z/nZ ` N )'; Bz = '( Base ` %s )' % Zn
    eg = w.s([], 'eqid', '%s = %s' % (G, G)); ez = w.s([], 'eqid', '%s = %s' % (Zn, Zn)); eb = w.s([], 'eqid', '%s = %s' % (DB_('N'), DB_('N')))
    ebz = w.s([], 'eqid', '%s = %s' % (Bz, Bz))
    et = w.s([], 'eqid', '( +g ` %s ) = ( +g ` %s )' % (G, G)); ei = w.s([], 'eqid', '( invg ` %s ) = ( invg ` %s )' % (G, G))
    IY = '( ( invg ` %s ) ` Y )' % G
    iy = d('dchrinv', [eg, eb, yb, ei], '%s = ( * o. Y )' % IY) if False else w.s([eg, eb, yb, ei], 'dchrinv', '( %s -> %s = ( * o. Y ) )' % (X0, IY))
    # the inverse is a character
    grp = d('syl', [nn, w.inst('dchrabl')], '%s e. Abel' % G) if False else None
    iyb = d('eqeltrd', [iy, d('idi', [], '') if False else None], '') if False else None
    # value at ZRHom K
    zf = d('syl', [d('syl', [d('nnnn0d', [nn], 'N e. NN0'), w.s([ez, ebz, w.s([], 'eqid', '( ZRHom ` %s ) = ( ZRHom ` %s )' % (Zn, Zn))], 'znzrhfo', '( N e. NN0 -> ( ZRHom ` %s ) : ZZ -onto-> %s )' % (Zn, Bz))], '( ZRHom ` %s ) : ZZ -onto-> %s' % (Zn, Bz)), w.inst('fof')], '( ZRHom ` %s ) : ZZ --> %s' % (Zn, Bz))
    ak = d('ffvelcdmd', [zf, d('nnzd', [kn], 'K e. ZZ')], '%s e. %s' % (ZRK, Bz))
    xf = w.s([eg, ez, eb, ebz, xb], 'dchrf', '( %s -> X : %s --> CC )' % (X0, Bz))
    yf = w.s([eg, ez, eb, ebz, yb], 'dchrf', '( %s -> Y : %s --> CC )' % (X0, Bz))
    xc = d('ffvelcdmd', [xf, ak], '%s e. CC' % XK); yc = d('ffvelcdmd', [yf, ak], '%s e. CC' % YK)
    cy = d('syl2anc', [yf, ak, w.inst('fvco3')], '( ( * o. Y ) ` %s ) = ( * ` %s )' % (ZRK, YK))
    iyv = d('eqtrd', [d('fveq1d', [iy], '( %s ` %s ) = ( ( * o. Y ) ` %s )' % (IY, ZRK, ZRK)), cy], '( %s ` %s ) = ( * ` %s )' % (IY, ZRK, YK))
    # IY is a character: it equals * o. Y, a function on Bz
    cjf = a1(w, X0, 'ax-mp' if False else 'cjf', '* : CC --> CC')
    cyf = d('syl2anc', [cjf, yf, w.inst('fco')], '( * o. Y ) : %s --> CC' % Bz)
    iyf = d('feq1d' if False else 'mpbird', [cyf, d('feq1d', [iy], '( %s : %s --> CC <-> ( * o. Y ) : %s --> CC )' % (IY, Bz, Bz))], '%s : %s --> CC' % (IY, Bz))
    mulv = d('syl2anc', [d('jca', [d('ffnd', [xf], 'X Fn %s' % Bz), d('ffnd', [iyf], '%s Fn %s' % (IY, Bz))], '( X Fn %s /\\ %s Fn %s )' % (Bz, IY, Bz)),
                         d('jca', [a1(w, X0, 'fvex', '%s e. _V' % Bz), ak], '( %s e. _V /\\ %s e. %s )' % (Bz, ZRK, Bz)), w.inst('fnfvof')],
             '( ( X oF x. %s ) ` %s ) = ( %s x. ( %s ` %s ) )' % (IY, ZRK, XK, IY, ZRK)) if False else \
        d('syl', [d('jca', [d('jca', [d('ffnd', [xf], 'X Fn %s' % Bz), d('ffnd', [iyf], '%s Fn %s' % (IY, Bz))], '( X Fn %s /\\ %s Fn %s )' % (Bz, IY, Bz)),
                            d('jca', [a1(w, X0, 'fvex', '%s e. _V' % Bz), ak], '( %s e. _V /\\ %s e. %s )' % (Bz, ZRK, Bz))],
                     '( ( X Fn %s /\\ %s Fn %s ) /\\ ( %s e. _V /\\ %s e. %s ) )' % (Bz, IY, Bz, Bz, ZRK, Bz)), w.inst('fnfvof')],
          '( ( X oF x. %s ) ` %s ) = ( %s x. ( %s ` %s ) )' % (IY, ZRK, XK, IY, ZRK))
    # the inverse character lies in the group
    ab_ = w.s([eg, nn, w.inst('dchrabl')], 'syl', '( %s -> %s e. Abel )' % (X0, G)) if False else d('syl', [nn, w.s([eg], 'dchrabl', '( N e. NN -> %s e. Abel )' % G)], '%s e. Abel' % G)
    gp = d('syl', [ab_, w.inst('ablgrp')], '%s e. Grp' % G)
    iyb = d('syl2anc', [gp, yb, w.s([eb, ei], 'grpinvcl', '( ( %s e. Grp /\\ Y e. %s ) -> %s e. %s )' % (G, DB_('N'), IY, DB_('N')))], '%s e. %s' % (IY, DB_('N')))
    dm = w.s([eg, ez, eb, et, xb, iyb], 'dchrmul', '( %s -> ( X ( +g ` %s ) %s ) = ( X oF x. %s ) )' % (X0, G, IY, IY))
    PX = '( X ( +g ` %s ) %s )' % (G, IY)
    CY = '( * ` %s )' % YK
    pv = chain(w, X0, ['( %s ` %s )' % (PX, ZRK), '( ( X oF x. %s ) ` %s )' % (IY, ZRK), '( %s x. ( %s ` %s ) )' % (XK, IY, ZRK), '( %s x. %s )' % (XK, CY)],
               [d('fveq1d', [dm], '( %s ` %s ) = ( ( X oF x. %s ) ` %s )' % (PX, ZRK, IY, ZRK)), mulv, d('oveq2d', [iyv], '( %s x. ( %s ` %s ) ) = ( %s x. %s )' % (XK, IY, ZRK, XK, CY))])
    # powers
    kc = d('nncnd', [kn], 'K e. CC'); kne = d('nnne0d', [kn], 'K =/= 0')
    KS = '( K ^c -u S )'; KT = '( K ^c -u T )'; CT = '( * ` T )'; KC = '( K ^c -u %s )' % CT
    nsc = d('negcld', [sc], '-u S e. CC'); ntc = d('negcld', [tc], '-u T e. CC')
    ksc = d('cxpcld', [kc, nsc], '%s e. CC' % KS); ktc = d('cxpcld', [kc, ntc], '%s e. CC' % KT)
    ctc = d('cjcld', [tc], '%s e. CC' % CT)
    kcc = d('cxpcld', [kc, d('negcld', [ctc], '-u %s e. CC' % CT)], '%s e. CC' % KC)
    cjk = d('eqtrd', [d('syl2anc', [kn, ntc, w.inst('cencjcx')], '( * ` %s ) = ( K ^c ( * ` -u T ) )' % KT),
                      d('oveq2d', [d('cjnegd', [tc], '( * ` -u T ) = -u %s' % CT)], '( K ^c ( * ` -u T ) ) = %s' % KC)], '( * ` %s ) = %s' % (KT, KC))
    cjp = d('eqtrd', [d('cjmuld', [yc, ktc], '( * ` ( %s x. %s ) ) = ( %s x. ( * ` %s ) )' % (YK, KT, CY, KT)), d('oveq2d', [cjk], '( %s x. ( * ` %s ) ) = ( %s x. %s )' % (CY, KT, CY, KC))],
              '( * ` ( %s x. %s ) ) = ( %s x. %s )' % (YK, KT, CY, KC))
    SCT = '( S + %s )' % CT
    ng = d('syl2anc', [sc, ctc, w.inst('negdi')], '-u %s = ( -u S + -u %s )' % (SCT, CT))
    cad = d('syl3anc', [d('jca', [kc, kne], '( K e. CC /\\ K =/= 0 )'), nsc, d('negcld', [ctc], '-u %s e. CC' % CT), w.inst('cxpadd')],
            '( K ^c ( -u S + -u %s ) ) = ( %s x. %s )' % (CT, KS, KC))
    kk = d('eqtrd', [d('oveq2d', [ng], '( K ^c -u %s ) = ( K ^c ( -u S + -u %s ) )' % (SCT, CT)), cad], '( K ^c -u %s ) = ( %s x. %s )' % (SCT, KS, KC))
    cyc = d('cjcld', [yc], '%s e. CC' % CY)
    cl = Closure(w, X0, {XK: ('CC', xc), CY: ('CC', cyc), KS: ('CC', ksc), KC: ('CC', kcc)})
    for a_ in [XK, CY, KS, KC]:
        cl.atom(a_)
    L0 = '( ( %s x. %s ) x. ( * ` ( %s x. %s ) ) )' % (XK, KS, YK, KT)
    L1 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (XK, KS, CY, KC)
    L2 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (XK, CY, KS, KC)
    R0 = '( ( %s ` %s ) x. ( K ^c -u %s ) )' % (PX, ZRK, SCT)
    s1 = d('oveq2d', [cjp], '%s = %s' % (L0, L1))
    s2 = ringeq(w, X0, L1, L2, cl)
    s3 = d('eqcomd', [d('oveq12d', [pv, kk], '%s = %s' % (R0, L2))], '%s = %s' % (L2, R0))
    fin = chain(w, X0, [L0, L1, L2, R0], [s1, s2, s3])
    w.qed([fin], 'idi', S['gf1chc'])
    return run(w, only)


if __name__ == '__main__':
    gen_cxb()
    gen_chb()
    gen_chc()
