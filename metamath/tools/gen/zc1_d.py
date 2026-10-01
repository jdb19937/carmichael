"""Sortie ZC1: the numeric mass bound (zc1w8), the rectangle facts (zc1rct), the eta and L instances of jensq13 (etazc, lchrzc8)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
from c9_b import decode
from c10_f import crfacts, clo
import c9_h
patch(c9_h)
import lin
lin.FASTPATH = True

L2 = '( log ` 2 )'
S['zc1w8'] = ('( ( ( X e. RR /\\ 2 <_ X ) /\\ ( ( B e. RR+ /\\ M e. RR+ ) /\\ ( M <_ B /\\ ( B / M ) <_ ( ; ; 1 2 8 x. X ) ) ) ) -> '
              '%s <_ ( ; ; 8 0 0 x. ( log ` X ) ) )') % JW('B', 'M')
S['zc1rct'] = '( ( T e. RR /\\ U e. %s ) -> ( U e. %s /\\ ( 1 / 4 ) <_ ( Re ` U ) /\\ ( abs ` U ) <_ ( ( abs ` T ) + 7 ) ) )' % (RCT('T'), HP0)
ZE = ZS(ETA, 'T')
S['etazc'] = '( T e. RR -> ( %s e. Fin /\\ A. q e. %s %s e. NN /\\ %s <_ ( ; ; 8 0 0 x. ( log ` ( ( abs ` T ) + 2 ) ) ) ) )' % (ZE, ZE, HO(ETA), MASS(ZE, ETA))
ZL_ = ZS(LFN, 'T')
S['lchrzc8'] = '( ( %s /\\ T e. RR ) -> ( %s e. Fin /\\ A. q e. %s %s e. NN /\\ %s <_ ( ; ; 8 0 0 x. ( log ` %s ) ) ) )' % (CHI, ZL_, ZL_, HO(LFN), MASS(ZL_, LFN), XT)


def gen_zc1w8():
    w = W('zc1w8', 'Numeric form of the four-strip mass bound: ` 4 log ( B / M ) / log ( 25 / 24 ) <_ 800 log X ` when ` 1 <_ B / M <_ 128 X ` and ` X >_ 2 ` ( ` log ( 25 / 24 ) >_ 1 / 25 ` , ` log 128 = 7 log 2 ` ).')
    A0 = ante_of(S['zc1w8'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2 = top_and(A0)
    xr = s([], 'simpll', 'X e. RR'); x2 = s([], 'simplr', '2 <_ X')
    brp = s([], 'simprll', 'B e. RR+'); mrp = s([], 'simprlr', 'M e. RR+')
    mb = s([], 'simprrl', 'M <_ B'); bm = s([], 'simprrr', '( B / M ) <_ ( ; ; 1 2 8 x. X )')
    xp = s([xr, lin8(w, A0, [x2], '0 < X', {'X': xr})], 'elrpd', 'X e. RR+')
    two = numst(w, A0, '2', 'RR+')
    qp = s([brp, mrp], 'rpdivcld', '( B / M ) e. RR+')
    qr = s([qp], 'rpred', '( B / M ) e. RR')
    mr = s([mrp], 'rpred', 'M e. RR'); br = s([brp], 'rpred', 'B e. RR')
    one = s([s([s([mr], 'recnd', 'M e. CC')], 'mullidd', '( 1 x. M ) = M'), mb], 'eqbrtrd', '( 1 x. M ) <_ B')
    q1 = s([one, s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), br, mrp], 'lemuldivd', '( ( 1 x. M ) <_ B <-> 1 <_ ( B / M ) )')], 'mpbid', '1 <_ ( B / M )')
    LQ = '( log ` ( B / M ) )'
    lq0 = s([qr, q1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LQ)
    P = '( ; ; 1 2 8 x. X )'
    pp = s([numst(w, A0, '; ; 1 2 8', 'RR+'), xp], 'rpmulcld', '%s e. RR+' % P)
    lqp = s([bm, s([qp, pp], 'logled', '( ( B / M ) <_ %s <-> %s <_ ( log ` %s ) )' % (P, LQ, P))], 'mpbid', '%s <_ ( log ` %s )' % (LQ, P))
    lpe = s([numst(w, A0, '; ; 1 2 8', 'RR+'), xp], 'relogmuld', '( log ` %s ) = ( ( log ` ; ; 1 2 8 ) + ( log ` X ) )' % P)
    e7 = w.s([], '2exp7', '( 2 ^ 7 ) = ; ; 1 2 8')
    re_ = s([s([two, w.s([num.fact(w, '7', 'ZZ')], 'a1i', '( %s -> 7 e. ZZ )' % A0)], 'jca', '( 2 e. RR+ /\\ 7 e. ZZ )'), w.inst('relogexp')], 'syl', '( log ` ( 2 ^ 7 ) ) = ( 7 x. %s )' % L2)
    l128 = s([s([s([w.s([e7], 'a1i', '( %s -> ( 2 ^ 7 ) = ; ; 1 2 8 )' % A0)], 'fveq2d', '( log ` ( 2 ^ 7 ) ) = ( log ` ; ; 1 2 8 )')], 'eqcomd', '( log ` ; ; 1 2 8 ) = ( log ` ( 2 ^ 7 ) )'), re_],
             'eqtrd', '( log ` ; ; 1 2 8 ) = ( 7 x. %s )' % L2)
    LX = '( log ` X )'
    l2x = s([x2, s([two, xp], 'logled', '( 2 <_ X <-> %s <_ %s )' % (L2, LX))], 'mpbid', '%s <_ %s' % (L2, LX))
    L25_ = L25
    zl = s([s([numst(w, A0, R2524, 'RR'), lin8(w, A0, [], '1 < %s' % R2524, {})], 'jca', '( %s e. RR /\\ 1 < %s )' % (R2524, R2524)), w.inst('zdmlogl1')], 'syl',
           '( 1 - ( 1 / %s ) ) <_ %s' % (R2524, L25_))
    rc = s([s([numst(w, A0, '; 2 5', 'CC'), w.s([num.fact(w, '; 2 5', 'ne0')], 'a1i', '( %s -> ; 2 5 =/= 0 )' % A0)], 'jca', '( ; 2 5 e. CC /\\ ; 2 5 =/= 0 )'),
                s([numst(w, A0, '; 2 4', 'CC'), w.s([num.fact(w, '; 2 4', 'ne0')], 'a1i', '( %s -> ; 2 4 =/= 0 )' % A0)], 'jca', '( ; 2 4 e. CC /\\ ; 2 4 =/= 0 )')], 'jca',
           '( ( ; 2 5 e. CC /\\ ; 2 5 =/= 0 ) /\\ ( ; 2 4 e. CC /\\ ; 2 4 =/= 0 ) )')
    rd = s([rc, w.inst('recdiv')], 'syl', '( 1 / %s ) = ( ; 2 4 / ; 2 5 )' % R2524)
    r25 = s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25_)
    q = s([s([numst(w, A0, R2524, 'RR+')], 'rpreccld', '( 1 / %s ) e. RR+' % R2524)], 'rpred', '( 1 / %s ) e. RR' % R2524)
    g25 = lin8(w, A0, [zl, rd], '( 1 / ; 2 5 ) <_ %s' % L25_, {L25_: r25, '( 1 / %s )' % R2524: q})
    l25p = s([r25, lin8(w, A0, [g25], '0 < %s' % L25_, {L25_: r25})], 'elrpd', '%s e. RR+' % L25_)
    lqr = s([qp], 'relogcld', '%s e. RR' % LQ)
    hint = s([lqr, s([r25, numst(w, A0, '( 1 / ; 2 5 )', 'RR')], 'resubcld', '( %s - ( 1 / ; 2 5 ) ) e. RR' % L25_), lq0, lin8(w, A0, [g25], '0 <_ ( %s - ( 1 / ; 2 5 ) )' % L25_, {L25_: r25})],
             'mulge0d', '0 <_ ( %s x. ( %s - ( 1 / ; 2 5 ) ) )' % (LQ, L25_))
    H100 = '( ; ; 1 0 0 x. %s )' % LQ
    mm = lin.linarith(w, A0, [hint], '( 4 x. %s ) <_ ( %s x. %s )' % (LQ, L25_, H100), closure=clo(w, A0, {LQ: lqr, L25_: r25}), products=True)
    W_ = JW('B', 'M')
    wle = s([mm, s([s([numst(w, A0, '4', 'RR'), lqr], 'remulcld', '( 4 x. %s ) e. RR' % LQ), s([numst(w, A0, '; ; 1 0 0', 'RR'), lqr], 'remulcld', '%s e. RR' % H100), l25p], 'ledivmuld',
            '( %s <_ %s <-> ( 4 x. %s ) <_ ( %s x. %s ) )' % (W_, H100, LQ, L25_, H100))], 'mpbird', '%s <_ %s' % (W_, H100))
    lv = {LQ: lqr, '( log ` %s )' % P: s([pp], 'relogcld', '( log ` %s ) e. RR' % P), '( log ` ; ; 1 2 8 )': s([numst(w, A0, '; ; 1 2 8', 'RR+')], 'relogcld', '( log ` ; ; 1 2 8 ) e. RR'),
          LX: s([xp], 'relogcld', '%s e. RR' % LX), L2: s([two], 'relogcld', '%s e. RR' % L2), W_: s([s([numst(w, A0, '4', 'RR'), lqr], 'remulcld', '( 4 x. %s ) e. RR' % LQ), l25p], 'rerpdivcld', '%s e. RR' % W_)}
    fin = lin8(w, A0, [wle, lqp, lpe, l128, l2x], '%s <_ ( ; ; 8 0 0 x. %s )' % (W_, LX), lv)
    w.qed([fin], 'a1i' if False else 'mp1i' if False else 'syl', S['zc1w8']) if False else w.lines.append('qed:%s:idi |- %s' % (fin, S['zc1w8']))
    return run8(w)


def gen_zc1rct():
    w = W('zc1rct', 'Points of the rectangle ` [ 1 / 4 , 15 / 4 ] x. [ T - 3 , T + 3 ] ` lie in the right half-plane with ` 1 / 4 <_ Re U ` and ` abs U <_ abs T + 7 ` (Lean ` disk_re_ge ` , ` disk_norm_le ` ).')
    A0 = '( T e. RR /\\ U e. %s )' % RCT('T')
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'simpl', 'T e. RR'); um = s([], 'simpr', 'U e. %s' % RCT('T'))
    RA, RB = '( ( 1 / 4 ) + ( _i x. ( T - 3 ) ) )', '( ( ; 1 5 / 4 ) + ( _i x. ( T + 3 ) ) )'
    t3a = s([tr, numst(w, A0, '3', 'RR')], 'resubcld', '( T - 3 ) e. RR')
    t3b = s([tr, numst(w, A0, '3', 'RR')], 'readdcld', '( T + 3 ) e. RR')
    rac, rreA, rimA = crfacts(w, A0, '( 1 / 4 )', '( T - 3 )', numst(w, A0, '( 1 / 4 )', 'RR'), t3a)
    rbc, rreB, rimB = crfacts(w, A0, '( ; 1 5 / 4 )', '( T + 3 )', numst(w, A0, '( ; 1 5 / 4 )', 'RR'), t3b)
    d = decode(w, A0, um, rac, rbc, RA, RB, RCT('T'), U='U')
    uc = d[0]
    ru = s([uc], 'recld', '( Re ` U ) e. RR'); iu = s([uc], 'imcld', '( Im ` U ) e. RR')
    lv = {'( Re ` U )': ru, '( Im ` U )': iu, 'T': tr}
    for e, st in (('( Re ` %s )' % RA, rac), ('( Im ` %s )' % RA, rac), ('( Re ` %s )' % RB, rbc), ('( Im ` %s )' % RB, rbc)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hy = [rreA, rimA, rreB, rimB] + d[1:]
    rge = lin8(w, A0, hy, '( 1 / 4 ) <_ ( Re ` U )', lv)
    hp = s([s([uc, lin8(w, A0, [rge], '0 < ( Re ` U )', {'( Re ` U )': ru})], 'jca', '( U e. CC /\\ 0 < ( Re ` U ) )'),
            s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( U e. %s <-> ( U e. CC /\\ 0 < ( Re ` U ) ) )' % HP0)], 'mpbird', 'U e. %s' % HP0)
    ari = s([uc, w.inst('absreimle')], 'syl', '( abs ` U ) <_ ( ( abs ` ( Re ` U ) ) + ( abs ` ( Im ` U ) ) )')
    are = s([ru, lin8(w, A0, [rge], '0 <_ ( Re ` U )', {'( Re ` U )': ru})], 'absidd', '( abs ` ( Re ` U ) ) = ( Re ` U )')
    AT = '( abs ` T )'
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '%s e. RR' % AT)
    lt = s([tr], 'leabsd', 'T <_ %s' % AT)
    nt = s([s([s([tr], 'renegcld', '-u T e. RR')], 'leabsd', '-u T <_ ( abs ` -u T )'), s([s([tr], 'recnd', 'T e. CC')], 'absnegd', '( abs ` -u T ) = %s' % AT)], 'breqtrd', '-u T <_ %s' % AT)
    B3 = '( %s + 3 )' % AT
    b3 = s([atr, numst(w, A0, '3', 'RR')], 'readdcld', '%s e. RR' % B3)
    lv2 = dict(lv); lv2[AT] = atr
    ai = s([s([lin8(w, A0, hy + [lt, nt], '-u %s <_ ( Im ` U )' % B3, lv2), lin8(w, A0, hy + [lt, nt], '( Im ` U ) <_ %s' % B3, lv2)], 'jca', '( -u %s <_ ( Im ` U ) /\\ ( Im ` U ) <_ %s )' % (B3, B3)),
            s([iu, b3], 'absled', '( ( abs ` ( Im ` U ) ) <_ %s <-> ( -u %s <_ ( Im ` U ) /\\ ( Im ` U ) <_ %s ) )' % (B3, B3, B3))], 'mpbird', '( abs ` ( Im ` U ) ) <_ %s' % B3)
    lv3 = dict(lv2)
    for e in ('( abs ` U )', '( abs ` ( Re ` U ) )', '( abs ` ( Im ` U ) )'):
        lv3[e] = s([{'( abs ` U )': uc, '( abs ` ( Re ` U ) )': s([ru], 'recnd', '( Re ` U ) e. CC'), '( abs ` ( Im ` U ) )': s([iu], 'recnd', '( Im ` U ) e. CC')}[e]], 'abscld', '%s e. RR' % e)
    ab = lin8(w, A0, hy + [ari, are, ai], '( abs ` U ) <_ ( %s + 7 )' % AT, lv3)
    w.qed([hp, rge, ab], '3jca', S['zc1rct'])
    return run8(w)


if __name__ == '__main__':
    gen_zc1w8()
    gen_zc1rct()
