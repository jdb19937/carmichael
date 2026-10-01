"""Sortie C10: the Landau expansion for L with the zero count and the centre bound fed in (lndlchrc)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
from c10_freeze import S as FS, ZSL, W0
from c8_o import numst
import c9_h
patch_stmt(c9_h)
from c9_h import c0_facts, lf_hol
from c10_f import clo
import lin
lin.FASTPATH = True


def gen_lndlchrc():
    w = W('lndlchrc', 'The Landau expansion for ` L ( s , chi ) ` , ` chi ` nonprincipal, with the multiplicity mass bounded ( ~ lchrzc ) and the centre bounded below ( ~ lchrctr ): on the disc of radius ` 3 / 2 ` about ` 2 + i T ` the error is at most ` 6272 ( log ( 40 N ( abs T + 2 ) ) + W0 log 26 ) ` , ` W0 = 4 log ( 80 N ( abs T + 2 ) ) / log ( 25 / 24 ) ` ( ~ lndlchr ).')
    A0, GC = ante_of(FS['lndlchrc'])
    X1, X2 = top_and(A0)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    x1 = s([], 'simpl', X1); x2 = s([], 'simpr', X2)
    chi = s([x1, w.inst('simpl')], 'syl', CHI); tr = s([x1, w.inst('simpr')], 'syl', 'T e. RR')
    zc = s([x1, w.inst('lchrzc')], 'syl', '( %s e. Fin /\\ sum_ q e. %s ( %s holord q ) <_ %s )' % (ZSL, ZSL, LFN, W0))
    wle = s([zc, w.inst('simpr')], 'syl', 'sum_ q e. %s ( %s holord q ) <_ %s' % (ZSL, LFN, W0))
    # W0 e. RR+
    nn = s([s([chi, w.inst('simpl')], 'syl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), w.inst('simpl')], 'syl', 'N e. NN')
    nrp = s([nn], 'nnrpd', 'N e. RR+'); nr = s([nrp], 'rpred', 'N e. RR')
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    AT2 = '( ( abs ` T ) + 2 )'
    at2r = s([atr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % AT2)
    at2p = s([at2r, lin8(w, A0, [ag0], '0 < %s' % AT2, {'( abs ` T )': atr})], 'elrpd', '%s e. RR+' % AT2)
    xtp = s([nrp, at2p], 'rpmulcld', '%s e. RR+' % XT); xtr = s([xtp], 'rpred', '%s e. RR' % XT)
    b80p = s([numst(w, A0, '; 8 0', 'RR+'), xtp], 'rpmulcld', '%s e. RR+' % B80)
    b40p = s([numst(w, A0, '; 4 0', 'RR+'), xtp], 'rpmulcld', '%s e. RR+' % B40)
    # 1 <_ X, so 1 < 80 X
    n1 = s([nn], 'nnge1d', '1 <_ N')
    one = s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    pr = s([s([nr, one], 'resubcld', '( N - 1 ) e. RR'), s([at2r, one], 'resubcld', '( %s - 1 ) e. RR' % AT2),
            lin8(w, A0, [n1], '0 <_ ( N - 1 )', {'N': nr}), lin8(w, A0, [ag0], '0 <_ ( %s - 1 )' % AT2, {'( abs ` T )': atr})], 'mulge0d',
           '0 <_ ( ( N - 1 ) x. ( %s - 1 ) )' % AT2)
    x1_ = lin.linarith(w, A0, [n1, ag0, pr], '1 < %s' % B80, closure=clo(w, A0, {'N': nr, '( abs ` T )': atr}), products=True)
    L80, L25 = '( log ` %s )' % B80, '( log ` %s )' % R2524
    l80p = s([s([b80p], 'relogcld', '%s e. RR' % L80), s([x1_, s([b80p, w.inst('loggt0b')], 'syl', '( 0 < %s <-> 1 < %s )' % (L80, B80))], 'mpbird', '0 < %s' % L80)], 'elrpd',
             '%s e. RR+' % L80)
    l25p = s([s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25),
              s([lin8(w, A0, [], '1 < %s' % R2524, {}), s([numst(w, A0, R2524, 'RR+'), w.inst('loggt0b')], 'syl', '( 0 < %s <-> 1 < %s )' % (L25, R2524))], 'mpbird', '0 < %s' % L25)],
             'elrpd', '%s e. RR+' % L25)
    w0p = s([s([numst(w, A0, '4', 'RR+'), l80p], 'rpmulcld', '( 4 x. %s ) e. RR+' % L80), l25p], 'rpdivcld', '%s e. RR+' % W0)
    LL = tsub(stmt('lndlchr'), {'W': W0})
    lla, llc = ante_of(LL)
    ll = s([s([s([chi, s([tr, s([w0p, wle], 'jca', '( %s e. RR+ /\\ sum_ q e. %s ( %s holord q ) <_ %s )' % (W0, ZSL, LFN, W0))], 'jca', top_and(top_and(lla)[0])[1])], 'jca',
                 top_and(lla)[0]), x2], 'jca', lla), w.inst('lndlchr')], 'syl', llc)
    # log ( B20 / abs L ( C0 ) ) <_ log B40
    c0, re0, im0 = c0_facts(w, A0, tr)
    hol = lf_hol(w, A0, chi)
    LC = '( %s ` %s )' % (LFN, C0); ALC = '( abs ` %s )' % LC
    lb = s([s([chi, tr], 'jca', '( %s /\\ T e. RR )' % CHI), w.inst('lchrctr')], 'syl', '( 1 / 2 ) <_ %s' % ALC)
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)),
             s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))], 'mpbird', '%s e. %s' % (C0, HP0))
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), c0h], 'ffvelcdmd', '%s e. CC' % LC)
    alr = s([lfc], 'abscld', '%s e. RR' % ALC)
    alcp = s([alr, lin8(w, A0, [lb], '0 < %s' % ALC, {ALC: alr})], 'elrpd', '%s e. RR+' % ALC)
    b20p = s([s([numst(w, A0, '; 2 0', 'RR+'), nrp], 'rpmulcld', '( ; 2 0 x. N ) e. RR+'), at2p], 'rpmulcld', '%s e. RR+' % B20)
    qp = s([b20p, alcp], 'rpdivcld', '( %s / %s ) e. RR+' % (B20, ALC))
    b2x = s([s([numst(w, A0, '; 2 0', 'CC'), s([nr], 'recnd', 'N e. CC'), s([at2r], 'recnd', '%s e. CC' % AT2)], 'mulassd', '%s = ( ; 2 0 x. %s )' % (B20, XT))], 'eqcomd',
            '( ; 2 0 x. %s ) = %s' % (XT, B20))
    hint = s([s([alr, numst(w, A0, '( 1 / 2 )', 'RR')], 'resubcld', '( %s - ( 1 / 2 ) ) e. RR' % ALC), xtr,
              lin8(w, A0, [lb], '0 <_ ( %s - ( 1 / 2 ) )' % ALC, {ALC: alr}), s([xtp], 'rpge0d', '0 <_ %s' % XT)], 'mulge0d', '0 <_ ( ( %s - ( 1 / 2 ) ) x. %s )' % (ALC, XT))
    b20r = s([b20p], 'rpred', '%s e. RR' % B20)
    ml2 = lin.linarith(w, A0, [b2x, hint], '%s <_ ( %s x. %s )' % (B20, ALC, B40), closure=clo(w, A0, {ALC: alr, XT: xtr, B20: b20r}), products=True)
    dl = s([ml2, s([b20r, s([b40p], 'rpred', '%s e. RR' % B40), alcp], 'ledivmuld', '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B20, ALC, B40, B20, ALC, B40))], 'mpbird',
           '( %s / %s ) <_ %s' % (B20, ALC, B40))
    LQ, L40 = '( log ` ( %s / %s ) )' % (B20, ALC), '( log ` %s )' % B40
    lq = s([dl, s([qp, b40p], 'logled', '( ( %s / %s ) <_ %s <-> %s <_ %s )' % (B20, ALC, B40, LQ, L40))], 'mpbid', '%s <_ %s' % (LQ, L40))
    WL = '( %s x. ( log ` ; 2 6 ) )' % W0
    wlr = s([s([w0p], 'rpred', '%s e. RR' % W0), s([numst(w, A0, '; 2 6', 'RR+')], 'relogcld', '( log ` ; 2 6 ) e. RR')], 'remulcld', '%s e. RR' % WL)
    lv = {LQ: s([qp], 'relogcld', '%s e. RR' % LQ), L40: s([b40p], 'relogcld', '%s e. RR' % L40), WL: wlr}
    RHS0 = llc.split(' <_ ', 1)[1]
    RHS1 = '( %s x. ( %s + %s ) )' % (K6N, L40, WL)
    assert RHS0 == '( %s x. ( %s + %s ) )' % (K6N, LQ, WL), RHS0
    le = lin8(w, A0, [lq], '%s <_ %s' % (RHS0, RHS1), lv)
    LHS = llc.split(' <_ ', 1)[0]
    goal = FS['lndlchrc']
    assert goal == '( %s -> %s <_ %s )' % (A0, LHS, RHS1), goal
    lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
    br = w.s([lx], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (LHS, RHS0, LHS, RHS0))
    lhx = s([s([ll, br], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (LHS, RHS0)), w.inst('simpl')], 'syl', '%s e. RR*' % LHS)
    c_ = clo(w, A0, lv)
    r0x = s([c_.mem(RHS0, 'RR')], 'rexrd', '%s e. RR*' % RHS0)
    r1x = s([c_.mem(RHS1, 'RR')], 'rexrd', '%s e. RR*' % RHS1)
    w.qed([lhx, r0x, r1x, ll, le], 'xrletrd', goal)
    return run8(w)


if __name__ == '__main__':
    gen_lndlchrc()
