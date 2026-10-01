"""Sortie ZC1: the eta and L instances of jensq13 (etazc, lchrzc8)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import c9_h
patch(c9_h)
from c9_h import lf_hol
from c10_f import clo
import zc1_d
import zc1_c
import lin
lin.FASTPATH = True

AT2 = '( ( abs ` T ) + 2 )'
S['etarct'] = '( T e. RR -> A. x e. %s ( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s ) )' % (RCT('T'), ETA, AT2)
S['lchrrct'] = '( ( %s /\\ T e. RR ) -> A. x e. %s ( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s ) )' % (CHI, RCT('T'), LFN, XT)


def isyl(w, A0, label, sub, ante_step):
    a, c = ante_of(tsub(stmt(label), sub))
    return w.s([ante_step, w.inst(label)], 'syl', '( %s -> %s )' % (A0, c)), c


def gen_etazc(part=None):
    if part == 'rct':
        w = W('etarct', 'The Abel-summed eta function is at most ` 25 ( abs T + 2 ) ` in modulus on the rectangle ` [ 1 / 4 , 15 / 4 ] x. [ T - 3 , T + 3 ] ` ( ~ zc1rct , ~ etabnd4 ; Lean ` DiskData.bd ` for ` etaFun ` ).')
    else:
      w = W('etazc', 'Zero count for the Abel-summed eta function on the square of half-side ` 13 / 8 ` about ` 2 + i T ` : at most ` 800 log ( abs T + 2 ) ` (Lean ` sum_ord_etaFun_disk_le ` , ` 112 ` on the disc; ~ jensq13 with ` B = 25 ( abs T + 2 ) ` from ~ etabnd4 and ` M = 1 / 4 ` from ~ etactr ).')
    A0 = 'T e. RR'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'id', 'T e. RR')
    hol = s([s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0')], 'jca', '( 0 e. RR /\\ 0 <_ 0 )'), w.inst('etahol')], 'syl', HOLF(ETA, HP0))
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    x2r = s([atr, numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % AT2)
    B = '( ; 2 5 x. %s )' % AT2
    M = '( 1 / 4 )'
    br = s([numst(w, A0, '; 2 5', 'RR'), x2r], 'remulcld', '%s e. RR' % B)
    BODY = 'sum_ k e. NN ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) )'

    def bstep(Ax):
        sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ax, f))
        rc = sx([sx([lift(w, tr, Ax), sx([], 'simpr', 'x e. %s' % RCT('T'))], 'jca', '( T e. RR /\\ x e. %s )' % RCT('T')), w.inst('zc1rct')], 'syl',
                tsub(ante_of(stmt('zc1rct'))[1], {'U': 'x'}))
        xh = sx([rc, w.inst('simp1')], 'syl', 'x e. %s' % HP0)
        rg = sx([rc, w.inst('simp2')], 'syl', '( 1 / 4 ) <_ ( Re ` x )')
        an = sx([rc, w.inst('simp3')], 'syl', '( abs ` x ) <_ ( ( abs ` T ) + 7 )')
        xc = sx([xh, w.s([], 'hpss', '%s C_ CC' % HP0) if False else None], 'x', 'x') if False else None
        el = sx([sx([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( x e. %s <-> ( x e. CC /\\ 0 < ( Re ` x ) ) )' % HP0)
        xc = sx([sx([xh, el], 'mpbid', '( x e. CC /\\ 0 < ( Re ` x ) )'), w.inst('simpl')], 'syl', 'x e. CC')
        VAL = tsub(BODY, {'z': 'x'})
        vx = sx([w.s([], 'sumex', '%s e. _V' % VAL)], 'a1i', '%s e. _V' % VAL)
        fv, val = _cg.mptval(w, Ax, 'z', HP0, BODY, 'x', xh, exs=vx, gen=w.g)
        eb = sx([sx([xc, rg], 'jca', '( x e. CC /\\ ( 1 / 4 ) <_ ( Re ` x ) )'), w.inst('etabnd4')], 'syl', '( abs ` %s ) <_ ( 5 x. ( 2 + ( abs ` x ) ) )' % VAL)
        AF = '( abs ` ( %s ` x ) )' % ETA
        af = sx([sx([fv], 'fveq2d', '%s = ( abs ` %s )' % (AF, VAL)), eb], 'eqbrtrd', '%s <_ ( 5 x. ( 2 + ( abs ` x ) ) )' % AF)
        ef = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (ETA, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (ETA, HP0))
        efx = sx([lift(w, ef, Ax), xh], 'ffvelcdmd', '( %s ` x ) e. CC' % ETA)
        lv = {AF: sx([efx], 'abscld', '%s e. RR' % AF), '( abs ` x )': sx([xc], 'abscld', '( abs ` x ) e. RR'), '( abs ` T )': lift(w, atr, Ax)}
        return lin8(w, Ax, [af, an, lift(w, ag0, Ax)], '%s <_ %s' % (AF, B), lv)

    def mstep(At):
        tin = w.s([], 'simpr', '( %s -> t e. ( ( T - 2 ) [,] ( T + 2 ) ) )' % At)
        trr = w.s([lift(w, s([tr, numst(w, A0, '2', 'RR')], 'resubcld', '( T - 2 ) e. RR'), At), lift(w, s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), At), tin],
                  'iccssred', '( %s -> t e. RR )' % At) if False else None
        ts = w.s([w.s([lift(w, s([tr, numst(w, A0, '2', 'RR')], 'resubcld', '( T - 2 ) e. RR'), At), lift(w, s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), At)],
                      'iccssred', '( %s -> ( ( T - 2 ) [,] ( T + 2 ) ) C_ RR )' % At), tin], 'sseldd', '( %s -> t e. RR )' % At)
        return w.s([ts, w.inst('etactr')], 'syl', '( %s -> %s <_ ( abs ` ( %s ` ( 2 + ( _i x. t ) ) ) ) )' % (At, M, ETA))
    mrp = numst(w, A0, M, 'RR+')
    J = tsub(S['jensq13'], {'F': ETA, 'B': B, 'M': M})
    ja, jc = ante_of(J)
    Y1, Y2, Y3 = top_and(ja)
    Ax = '( %s /\\ x e. %s )' % (A0, RCT('T'))
    bx = s([bstep(Ax)], 'ralrimiva', top_and(Y2)[1])
    if part == 'rct':
        w.qed([bx], 'idi' if False else 'syl' if False else 'idi', '( %s -> %s )' % (A0, top_and(Y2)[1]))
        return run8(w)
    At = '( %s /\\ t e. ( ( T - 2 ) [,] ( T + 2 ) ) )' % A0
    mt = s([mstep(At)], 'ralrimiva', top_and(Y3)[1])
    jr = s([s([s([hol, tr], 'jca', Y1), s([br, bx], 'jca', Y2), s([mrp, mt], 'jca', Y3)], '3jca', ja), w.inst('jensq13')], 'syl', jc)
    C1, C2, C3 = top_and(jc)
    zf = s([jr, w.inst('simp1')], 'syl', C1); nn = s([jr, w.inst('simp2')], 'syl', C2); ms = s([jr, w.inst('simp3')], 'syl', C3)
    # zc1w8 at X = abs T + 2
    lv = {'( abs ` T )': atr}
    x2 = lin8(w, A0, [ag0], '2 <_ %s' % AT2, lv)
    brp = s([br, lin8(w, A0, [ag0], '0 < %s' % B, lv)], 'elrpd', '%s e. RR+' % B)
    mb = lin8(w, A0, [ag0], '%s <_ %s' % (M, B), lv)
    P = '( ; ; 1 2 8 x. %s )' % AT2
    bmx = s([lin8(w, A0, [ag0], '%s <_ ( %s x. %s )' % (B, M, P), lv), s([br, s([numst(w, A0, '; ; 1 2 8', 'RR'), x2r], 'remulcld', '%s e. RR' % P), mrp], 'ledivmuld',
             '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B, M, P, B, M, P))], 'mpbird', '( %s / %s ) <_ %s' % (B, M, P))
    Wz = tsub(S['zc1w8'], {'X': AT2, 'B': B, 'M': M})
    wa, wc = ante_of(Wz)
    w8 = s([s([s([x2r, x2], 'jca', top_and(wa)[0]), s([s([brp, mrp], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (B, M)), s([mb, bmx], 'jca', '( %s <_ %s /\\ ( %s / %s ) <_ %s )' % (M, B, B, M, P))], 'jca', top_and(wa)[1])],
                'jca', wa), w.inst('zc1w8')], 'syl', wc)
    MS = C3.split(' <_ ', 1)[0]
    fin = s([s([C3.split(' <_ ', 1)[0], None], 'x', 'x') if False else ms, w8], 'letrd', '%s <_ ( ; ; 8 0 0 x. ( log ` %s ) )' % (MS, AT2)) if False else None
    lvf = {MS: s([zf, w.s([w.s([nn], 'r19.21bi', '( ( %s /\\ q e. %s ) -> %s e. NN )' % (A0, ZS(ETA, 'T'), HO(ETA)))], 'nnred', '( ( %s /\\ q e. %s ) -> %s e. RR )' % (A0, ZS(ETA, 'T'), HO(ETA)))],
                 'fsumrecl', '%s e. RR' % MS)}
    W_ = JW(B, M)
    lvf[W_] = s([s([numst(w, A0, '4', 'RR'), s([s([brp, mrp], 'rpdivcld', '( %s / %s ) e. RR+' % (B, M))], 'relogcld', '( log ` ( %s / %s ) ) e. RR' % (B, M))], 'remulcld',
                   '( 4 x. ( log ` ( %s / %s ) ) ) e. RR' % (B, M)), numst(w, A0, R2524, 'RR+') and s([s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25),
                   lin8(w, A0, [], '0 < %s' % L25, {}) if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    fin = s([lvf[MS], s([s([numst(w, A0, '4', 'RR'), s([s([brp, mrp], 'rpdivcld', '( %s / %s ) e. RR+' % (B, M))], 'relogcld', '( log ` ( %s / %s ) ) e. RR' % (B, M))], 'remulcld',
                          '( 4 x. ( log ` ( %s / %s ) ) ) e. RR' % (B, M)), l25rp(w, A0)], 'rerpdivcld', '%s e. RR' % W_),
             s([numst(w, A0, '; ; 8 0 0', 'RR'), s([s([x2r, lin8(w, A0, [ag0], '0 < %s' % AT2, lv)], 'elrpd', '%s e. RR+' % AT2)], 'relogcld', '( log ` %s ) e. RR' % AT2)], 'remulcld',
               '( ; ; 8 0 0 x. ( log ` %s ) ) e. RR' % AT2), ms, w8], 'letrd', '%s <_ ( ; ; 8 0 0 x. ( log ` %s ) )' % (MS, AT2))
    w.qed([zf, nn, fin], '3jca', S['etazc'])
    return run8(w)


def gen_lchrzc8(part=None):
    if part == 'rct':
        w = W('lchrrct', 'For ` chi ` nonprincipal, ` L ( s , chi ) ` is at most ` 25 N ( abs T + 2 ) ` in modulus on the rectangle ` [ 1 / 4 , 15 / 4 ] x. [ T - 3 , T + 3 ] ` ( ~ zc1rct , ~ lchrab4 ; Lean ` DiskData.bd ` ).')
    else:
      w = W('lchrzc8', 'Zero count for ` L ( s , chi ) ` , ` chi ` nonprincipal, on the square of half-side ` 13 / 8 ` about ` 2 + i T ` : finitely many zeros, orders in ` NN ` , mass at most ` 800 log ( N ( abs T + 2 ) ) ` (Lean ` sum_ord_LFunction_disk_le ` , ` 112 ` on the disc; ~ jensq13 with ` B = 25 N ( abs T + 2 ) ` from ~ lchrab4 and ` M = 1 / 2 ` from ~ lchrctr ).')
    A0 = '( %s /\\ T e. RR )' % CHI
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tr = s([], 'simpr', 'T e. RR')
    hol = lf_hol(w, A0, chi)
    nn_ = s([s([chi, w.inst('simpl')], 'syl', NX), w.inst('simpl')], 'syl', 'N e. NN')
    nr = s([nn_], 'nnred', 'N e. RR'); n1 = s([nn_], 'nnge1d', '1 <_ N')
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    x2r = s([atr, numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % AT2)
    xtr = s([nr, x2r], 'remulcld', '%s e. RR' % XT)
    B = '( ; 2 5 x. %s )' % XT
    M = '( 1 / 2 )'
    br = s([numst(w, A0, '; 2 5', 'RR'), xtr], 'remulcld', '%s e. RR' % B)
    BODY = LSs('s')
    lv0 = {'N': nr, '( abs ` T )': atr}
    nt0 = s([nr, atr, lin8(w, A0, [n1], '0 <_ N', lv0), ag0], 'mulge0d', '0 <_ ( N x. ( abs ` T ) )')

    def bstep(Ax):
        sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ax, f))
        rc = sx([sx([lift(w, tr, Ax), sx([], 'simpr', 'x e. %s' % RCT('T'))], 'jca', '( T e. RR /\\ x e. %s )' % RCT('T')), w.inst('zc1rct')], 'syl',
                tsub(ante_of(stmt('zc1rct'))[1], {'U': 'x'}))
        xh = sx([rc, w.inst('simp1')], 'syl', 'x e. %s' % HP0)
        rg = sx([rc, w.inst('simp2')], 'syl', '( 1 / 4 ) <_ ( Re ` x )')
        an = sx([rc, w.inst('simp3')], 'syl', '( abs ` x ) <_ ( ( abs ` T ) + 7 )')
        el = sx([sx([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( x e. %s <-> ( x e. CC /\\ 0 < ( Re ` x ) ) )' % HP0)
        xc = sx([sx([xh, el], 'mpbid', '( x e. CC /\\ 0 < ( Re ` x ) )'), w.inst('simpl')], 'syl', 'x e. CC')
        VAL = tsub(BODY, {'s': 'x'})
        vx = sx([w.s([], 'sumex', '%s e. _V' % VAL)], 'a1i', '%s e. _V' % VAL)
        fv, val = _cg.mptval(w, Ax, 's', HP0, BODY, 'x', xh, exs=vx, gen=w.g)
        eb = sx([sx([lift(w, chi, Ax), sx([xc, rg], 'jca', '( x e. CC /\\ ( 1 / 4 ) <_ ( Re ` x ) )')], 'jca', '( %s /\\ ( x e. CC /\\ ( 1 / 4 ) <_ ( Re ` x ) ) )' % CHI), w.inst('lchrab4')], 'syl',
                '( abs ` %s ) <_ ( ( 5 x. N ) x. ( 2 + ( abs ` x ) ) )' % VAL)
        AF = '( abs ` ( %s ` x ) )' % LFN
        af = sx([sx([fv], 'fveq2d', '%s = ( abs ` %s )' % (AF, VAL)), eb], 'eqbrtrd', '%s <_ ( ( 5 x. N ) x. ( 2 + ( abs ` x ) ) )' % AF)
        ef = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0))
        efx = sx([lift(w, ef, Ax), xh], 'ffvelcdmd', '( %s ` x ) e. CC' % LFN)
        axr = sx([xc], 'abscld', '( abs ` x ) e. RR')
        lv = {AF: sx([efx], 'abscld', '%s e. RR' % AF), '( abs ` x )': axr, '( abs ` T )': lift(w, atr, Ax), 'N': lift(w, nr, Ax)}
        D7 = '( ( ( abs ` T ) + 7 ) - ( abs ` x ) )'
        h1 = sx([lift(w, nr, Ax), sx([sx([lift(w, atr, Ax), sx([w.s([], '7re', '7 e. RR')], 'a1i', '7 e. RR')], 'readdcld', '( ( abs ` T ) + 7 ) e. RR'), axr], 'resubcld', '%s e. RR' % D7),
                 lift(w, lin8(w, A0, [n1], '0 <_ N', lv0), Ax), lin8(w, Ax, [an], '0 <_ %s' % D7, lv)], 'mulge0d', '0 <_ ( N x. %s )' % D7)
        import cl as _cl
        c = _cl.Closure(w, Ax, lv)
        for k_ in lv:
            c.atom(k_)
        return lin.linarith(w, Ax, [af, h1, lift(w, nt0, Ax), lift(w, n1, Ax)], '%s <_ %s' % (AF, B), closure=c, products=True)

    def mstep(At):
        tin = w.s([], 'simpr', '( %s -> t e. ( ( T - 2 ) [,] ( T + 2 ) ) )' % At)
        ts = w.s([w.s([lift(w, s([tr, numst(w, A0, '2', 'RR')], 'resubcld', '( T - 2 ) e. RR'), At), lift(w, s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), At)],
                      'iccssred', '( %s -> ( ( T - 2 ) [,] ( T + 2 ) ) C_ RR )' % At), tin], 'sseldd', '( %s -> t e. RR )' % At)
        return w.s([w.s([lift(w, chi, At), ts], 'jca', '( %s -> ( %s /\\ t e. RR ) )' % (At, CHI)), w.inst('lchrctr')], 'syl',
                   '( %s -> %s <_ ( abs ` ( %s ` ( 2 + ( _i x. t ) ) ) ) )' % (At, M, LFN))
    mrp = numst(w, A0, M, 'RR+')
    J = tsub(S['jensq13'], {'F': LFN, 'B': B, 'M': M})
    ja, jc = ante_of(J)
    Y1, Y2, Y3 = top_and(ja)
    Ax = '( %s /\\ x e. %s )' % (A0, RCT('T'))
    bx = s([bstep(Ax)], 'ralrimiva', top_and(Y2)[1])
    if part == 'rct':
        w.qed([bx], 'idi' if False else 'syl' if False else 'idi', '( %s -> %s )' % (A0, top_and(Y2)[1]))
        return run8(w)
    At = '( %s /\\ t e. ( ( T - 2 ) [,] ( T + 2 ) ) )' % A0
    mt = s([mstep(At)], 'ralrimiva', top_and(Y3)[1])
    jr = s([s([s([hol, tr], 'jca', Y1), s([br, bx], 'jca', Y2), s([mrp, mt], 'jca', Y3)], '3jca', ja), w.inst('jensq13')], 'syl', jc)
    C1, C2, C3 = top_and(jc)
    zf = s([jr, w.inst('simp1')], 'syl', C1); nn = s([jr, w.inst('simp2')], 'syl', C2); ms = s([jr, w.inst('simp3')], 'syl', C3)
    pr = s([s([nr, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '( N - 1 ) e. RR'), x2r, lin8(w, A0, [n1], '0 <_ ( N - 1 )', lv0),
            lin8(w, A0, [ag0], '0 <_ %s' % AT2, lv0)], 'mulge0d', '0 <_ ( ( N - 1 ) x. %s )' % AT2)
    x2 = lin.linarith(w, A0, [pr, ag0], '2 <_ %s' % XT, closure=clo(w, A0, lv0), products=True)
    lvx = {XT: xtr}
    brp = s([br, lin8(w, A0, [x2], '0 < %s' % B, lvx)], 'elrpd', '%s e. RR+' % B)
    mb = lin8(w, A0, [x2], '%s <_ %s' % (M, B), lvx)
    P = '( ; ; 1 2 8 x. %s )' % XT
    bmx = s([lin8(w, A0, [x2], '%s <_ ( %s x. %s )' % (B, M, P), lvx), s([br, s([numst(w, A0, '; ; 1 2 8', 'RR'), xtr], 'remulcld', '%s e. RR' % P), mrp], 'ledivmuld',
             '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B, M, P, B, M, P))], 'mpbird', '( %s / %s ) <_ %s' % (B, M, P))
    Wz = tsub(S['zc1w8'], {'X': XT, 'B': B, 'M': M})
    wa, wc = ante_of(Wz)
    w8 = s([s([s([xtr, x2], 'jca', top_and(wa)[0]), s([s([brp, mrp], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (B, M)), s([mb, bmx], 'jca', '( %s <_ %s /\\ ( %s / %s ) <_ %s )' % (M, B, B, M, P))], 'jca', top_and(wa)[1])],
                'jca', wa), w.inst('zc1w8')], 'syl', wc)
    MS = C3.split(' <_ ', 1)[0]
    ZL = ZS(LFN, 'T')
    msr = s([zf, w.s([w.s([nn], 'r19.21bi', '( ( %s /\\ q e. %s ) -> %s e. NN )' % (A0, ZL, HO(LFN)))], 'nnred', '( ( %s /\\ q e. %s ) -> %s e. RR )' % (A0, ZL, HO(LFN)))],
            'fsumrecl', '%s e. RR' % MS)
    W_ = JW(B, M)
    wr = s([s([numst(w, A0, '4', 'RR'), s([s([brp, mrp], 'rpdivcld', '( %s / %s ) e. RR+' % (B, M))], 'relogcld', '( log ` ( %s / %s ) ) e. RR' % (B, M))], 'remulcld',
              '( 4 x. ( log ` ( %s / %s ) ) ) e. RR' % (B, M)), l25rp(w, A0)], 'rerpdivcld', '%s e. RR' % W_)
    xtp = s([xtr, lin8(w, A0, [x2], '0 < %s' % XT, lvx)], 'elrpd', '%s e. RR+' % XT)
    fin = s([msr, wr, s([numst(w, A0, '; ; 8 0 0', 'RR'), s([xtp], 'relogcld', '( log ` %s ) e. RR' % XT)], 'remulcld', '( ; ; 8 0 0 x. ( log ` %s ) ) e. RR' % XT), ms, w8], 'letrd',
            '%s <_ ( ; ; 8 0 0 x. ( log ` %s ) )' % (MS, XT))
    w.qed([zf, nn, fin], '3jca', S['lchrzc8'])
    return run8(w)


def l25rp(w, A0):
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    l25p = s([s([numst(w, A0, R2524, 'RR+'), w.inst('loggt0b')], 'syl', '( 0 < %s <-> 1 < %s )' % (L25, R2524)), lin8(w, A0, [], '1 < %s' % R2524, {})], 'mpbird', '0 < %s' % L25)
    return s([s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25), l25p], 'elrpd', '%s e. RR+' % L25)


if __name__ == '__main__':
    gen_etazc()
    gen_lchrzc8()
    gen_etazc('rct')
    gen_lchrzc8('rct')
