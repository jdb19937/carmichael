"""Sortie C10: the Landau expansion for L with an explicit constant times log ( N ( abs T + 2 ) ) (lndlchrk)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
import num
from c10_freeze import S as FS, ZSL, W0, KNUM
from c8_o import numst
from c10_f import clo
import lin
lin.FASTPATH = True


def gen_lndlchrk():
    w = W('lndlchrk', 'The Landau expansion for ` L ( s , chi ) ` , ` chi ` nonprincipal, with the constant ` 17500000 log ( N ( abs T + 2 ) ) ` ( Lean ` 520000 log ( N ( abs t + 2 ) ) ` , ~ lndlchrc ): ` log 40 <_ 6 log 2 ` , ` log 80 <_ 7 log 2 ` , ` log 26 <_ 5 log 2 < 253 / 73 ` , ` log ( 25 / 24 ) >_ 1 / 25 ` .')
    A0, GC = ante_of(FS['lndlchrk'])
    X1, X2 = top_and(A0)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    x1 = s([], 'simpl', X1)
    chi = s([x1, w.inst('simpl')], 'syl', CHI); tr = s([x1, w.inst('simpr')], 'syl', 'T e. RR')
    LC_ = ante_of(FS['lndlchrc'])[1]
    ll = w.s([], 'lndlchrc', FS['lndlchrc'])
    nn = s([s([chi, w.inst('simpl')], 'syl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), w.inst('simpl')], 'syl', 'N e. NN')
    nrp = s([nn], 'nnrpd', 'N e. RR+'); nr = s([nrp], 'rpred', 'N e. RR'); n1 = s([nn], 'nnge1d', '1 <_ N')
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    AT2 = '( ( abs ` T ) + 2 )'
    at2r = s([atr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % AT2)
    at2p = s([at2r, lin8(w, A0, [ag0], '0 < %s' % AT2, {'( abs ` T )': atr})], 'elrpd', '%s e. RR+' % AT2)
    xtp = s([nrp, at2p], 'rpmulcld', '%s e. RR+' % XT); xtr = s([xtp], 'rpred', '%s e. RR' % XT)
    lv0 = {'N': nr, '( abs ` T )': atr}
    one = s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    pr = s([s([nr, one], 'resubcld', '( N - 1 ) e. RR'), at2r, lin8(w, A0, [n1], '0 <_ ( N - 1 )', lv0), s([at2p], 'rpge0d', '0 <_ %s' % AT2)], 'mulge0d',
           '0 <_ ( ( N - 1 ) x. %s )' % AT2)
    x2 = lin.linarith(w, A0, [pr, ag0], '2 <_ %s' % XT, closure=clo(w, A0, lv0), products=True)
    LX, L2 = '( log ` %s )' % XT, '( log ` 2 )'
    two = numst(w, A0, '2', 'RR+')
    l2x = s([x2, s([two, xtp], 'logled', '( 2 <_ %s <-> %s <_ %s )' % (XT, L2, LX))], 'mpbid', '%s <_ %s' % (L2, LX))
    lx0 = s([xtr, lin8(w, A0, [x2], '1 <_ %s' % XT, {XT: xtr}), w.inst('logge0')], 'syl2anc', '0 <_ %s' % LX)
    def logpow(c, n, lab, P):
        """log c <_ n log 2 from c <_ P = 2 ^ n"""
        cp = numst(w, A0, c, 'RR+')
        e = w.s([], lab, '( 2 ^ %s ) = %s' % (n, P))
        le = s([w.s([num.le_lit(w, c, P)], 'a1i', '( %s -> %s <_ %s )' % (A0, c, P)), w.s([e], 'a1i', '( %s -> ( 2 ^ %s ) = %s )' % (A0, n, P))], 'breqtrrd',
               '%s <_ ( 2 ^ %s )' % (c, n))
        pp = s([two, w.s([num.fact(w, n, 'ZZ')], 'a1i', '( %s -> %s e. ZZ )' % (A0, n))], 'rpexpcld', '( 2 ^ %s ) e. RR+' % n)
        lg = s([le, s([cp, pp], 'logled', '( %s <_ ( 2 ^ %s ) <-> ( log ` %s ) <_ ( log ` ( 2 ^ %s ) ) )' % (c, n, c, n))], 'mpbid', '( log ` %s ) <_ ( log ` ( 2 ^ %s ) )' % (c, n))
        re_ = s([s([two, w.s([num.fact(w, n, 'ZZ')], 'a1i', '( %s -> %s e. ZZ )' % (A0, n))], 'jca', '( 2 e. RR+ /\\ %s e. ZZ )' % n), w.inst('relogexp')], 'syl',
                '( log ` ( 2 ^ %s ) ) = ( %s x. %s )' % (n, n, L2))
        return s([lg, re_], 'breqtrd', '( log ` %s ) <_ ( %s x. %s )' % (c, n, L2))
    l40 = logpow('; 4 0', '6', '2exp6', '; 6 4')
    l80 = logpow('; 8 0', '7', '2exp7', '; ; 1 2 8')
    l26 = logpow('; 2 6', '5', '2exp5', '; 3 2')
    l2u = w.s([w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L2)], 'a1i', '( %s -> %s < ( ; ; 2 5 3 / ; ; 3 6 5 ) )' % (A0, L2))
    L40, L80, L26, L25 = '( log ` %s )' % B40, '( log ` %s )' % B80, '( log ` ; 2 6 )', '( log ` %s )' % R2524
    e40 = s([numst(w, A0, '; 4 0', 'RR+'), xtp], 'relogmuld', '%s = ( ( log ` ; 4 0 ) + %s )' % (L40, LX))
    e80 = s([numst(w, A0, '; 8 0', 'RR+'), xtp], 'relogmuld', '%s = ( ( log ` ; 8 0 ) + %s )' % (L80, LX))
    # log ( 25 / 24 ) >_ 1 / 25
    zl = s([s([numst(w, A0, R2524, 'RR'), lin8(w, A0, [], '1 < %s' % R2524, {})], 'jca', '( %s e. RR /\\ 1 < %s )' % (R2524, R2524)), w.inst('zdmlogl1')], 'syl',
           '( 1 - ( 1 / %s ) ) <_ %s' % (R2524, L25))
    rc = s([s([numst(w, A0, '; 2 5', 'CC'), w.s([num.fact(w, '; 2 5', 'ne0')], 'a1i', '( %s -> ; 2 5 =/= 0 )' % A0)], 'jca', '( ; 2 5 e. CC /\\ ; 2 5 =/= 0 )'),
                s([numst(w, A0, '; 2 4', 'CC'), w.s([num.fact(w, '; 2 4', 'ne0')], 'a1i', '( %s -> ; 2 4 =/= 0 )' % A0)], 'jca', '( ; 2 4 e. CC /\\ ; 2 4 =/= 0 )')], 'jca',
           '( ( ; 2 5 e. CC /\\ ; 2 5 =/= 0 ) /\\ ( ; 2 4 e. CC /\\ ; 2 4 =/= 0 ) )')
    rd = s([rc, w.inst('recdiv')], 'syl', '( 1 / %s ) = ( ; 2 4 / ; 2 5 )' % R2524)
    r25 = s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25)
    q = s([s([numst(w, A0, R2524, 'RR+')], 'rpreccld', '( 1 / %s ) e. RR+' % R2524)], 'rpred', '( 1 / %s ) e. RR' % R2524)
    lv = {L25: r25, '( 1 / %s )' % R2524: q}
    g25 = lin8(w, A0, [zl, rd], '( 1 / ; 2 5 ) <_ %s' % L25, lv)
    l25p = s([r25, lin8(w, A0, [g25], '0 < %s' % L25, {L25: r25})], 'elrpd', '%s e. RR+' % L25)
    # L80 >_ 0, W0 >_ 0
    b80p = s([numst(w, A0, '; 8 0', 'RR+'), xtp], 'rpmulcld', '%s e. RR+' % B80)
    b80r = s([b80p], 'rpred', '%s e. RR' % B80)
    l80r = s([b80p], 'relogcld', '%s e. RR' % L80)
    l80g = s([b80r, lin8(w, A0, [x2], '1 <_ %s' % B80, {XT: xtr}), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L80)
    w0r = s([s([numst(w, A0, '4', 'RR'), l80r], 'remulcld', '( 4 x. %s ) e. RR' % L80), l25p], 'rerpdivcld', '%s e. RR' % W0)
    w0g = s([s([numst(w, A0, '4', 'RR'), l80r], 'remulcld', '( 4 x. %s ) e. RR' % L80), l25p, s([numst(w, A0, '4', 'RR'), l80r, numst(w, A0, '4', 'ge0'), l80g], 'mulge0d',
            '0 <_ ( 4 x. %s )' % L80)], 'divge0d', '0 <_ %s' % W0)
    hint = s([l80r, s([r25, numst(w, A0, '( 1 / ; 2 5 )', 'RR')], 'resubcld', '( %s - ( 1 / ; 2 5 ) ) e. RR' % L25), l80g, lin8(w, A0, [g25], '0 <_ ( %s - ( 1 / ; 2 5 ) )' % L25, {L25: r25})],
             'mulge0d', '0 <_ ( %s x. ( %s - ( 1 / ; 2 5 ) ) )' % (L80, L25))
    H100 = '( ; ; 1 0 0 x. %s )' % L80
    mm = lin.linarith(w, A0, [hint], '( 4 x. %s ) <_ ( %s x. %s )' % (L80, L25, H100), closure=clo(w, A0, {L80: l80r, L25: r25}), products=True)
    wle = s([mm, s([s([numst(w, A0, '4', 'RR'), l80r], 'remulcld', '( 4 x. %s ) e. RR' % L80), s([numst(w, A0, '; ; 1 0 0', 'RR'), l80r], 'remulcld', '%s e. RR' % H100), l25p], 'ledivmuld',
            '( %s <_ %s <-> ( 4 x. %s ) <_ ( %s x. %s ) )' % (W0, H100, L80, L25, H100))], 'mpbird', '%s <_ %s' % (W0, H100))
    # W0 log 26 <_ W0 ( 253 / 73 )
    C26 = '( ; ; 2 5 3 / ; 7 3 )'
    l26r = s([numst(w, A0, '; 2 6', 'RR+')], 'relogcld', '%s e. RR' % L26)
    l2r = s([two], 'relogcld', '%s e. RR' % L2)
    c26 = lin8(w, A0, [l26, l2u], '%s <_ %s' % (L26, C26), {L26: l26r, L2: l2r})
    wl = s([l26r, numst(w, A0, C26, 'RR'), w0r, w0g, c26], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (W0, L26, W0, C26))
    # assemble
    LHS, RHS0 = ante_of(FS['lndlchrc'])[1].split(' <_ ', 1)
    RHS1 = GC.split(' <_ ', 1)[1]
    WL = '( %s x. %s )' % (W0, L26)
    lvf = {L40: s([s([numst(w, A0, '; 4 0', 'RR+'), xtp], 'rpmulcld', '%s e. RR+' % B40)], 'relogcld', '%s e. RR' % L40), L80: l80r, LX: s([xtp], 'relogcld', '%s e. RR' % LX),
           L2: l2r, '( log ` ; 4 0 )': s([numst(w, A0, '; 4 0', 'RR+')], 'relogcld', '( log ` ; 4 0 ) e. RR'), '( log ` ; 8 0 )': s([numst(w, A0, '; 8 0', 'RR+')], 'relogcld', '( log ` ; 8 0 ) e. RR'),
           W0: w0r, WL: s([w0r, l26r], 'remulcld', '%s e. RR' % WL)}
    c_ = clo(w, A0, lvf)
    le = lin.linarith(w, A0, [e40, l40, l2x, wl, wle, e80, l80, lx0], '%s <_ %s' % (RHS0, RHS1), closure=c_)
    lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
    br = w.s([lx], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (LHS, RHS0, LHS, RHS0))
    lhx = s([s([ll, br], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (LHS, RHS0)), w.inst('simpl')], 'syl', '%s e. RR*' % LHS)
    r0x = s([c_.mem(RHS0, 'RR')], 'rexrd', '%s e. RR*' % RHS0)
    r1x = s([c_.mem(RHS1, 'RR')], 'rexrd', '%s e. RR*' % RHS1)
    w.qed([lhx, r0x, r1x, ll, le], 'xrletrd', FS['lndlchrk'])
    return run8(w)


if __name__ == '__main__':
    gen_lndlchrk()
