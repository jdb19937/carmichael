"""Sortie GF1, section A: the exponential on a real line (gf1edv, gf1em1).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_a.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *

only = sys.argv[1:]
EWT = '( exp ` ( W x. t ) )'
S['gf1edv'] = '( W e. CC -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( %s x. W ) ) )' % (EWT, EWT)


def gen_edv():
    w = W('gf1edv', 'The derivative of ` t |-> exp ( W t ) ` on the real line is ` exp ( W t ) W ` ( ~ dvmptco , ~ dvef ).')
    A = 'W e. CC'
    d = mk(w, A)
    At = '( W e. CC /\\ t e. RR )'
    dt = mk(w, At)
    idw = w.s([], 'id', '( W e. CC -> W e. CC )')
    rr = a1(w, A, 'reelprrecn', 'RR e. { RR , CC }')
    cc = a1(w, A, 'cnelprrecn', 'CC e. { RR , CC }')
    did = d('dvmptid', [rr], '( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 )')
    tr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    tc = dt('recnd', [tr], 't e. CC')
    one = dt('1cnd', [], '1 e. CC')
    dml = d('dvmptcmul', [rr, tc, one, did, idw], '( RR _D ( t e. RR |-> ( W x. t ) ) ) = ( t e. RR |-> ( W x. 1 ) )')
    wc = dt('adantr', [idw], 'W e. CC') if False else lift(w, idw, At)
    wt = dt('mulcld', [wc, tc], '( W x. t ) e. CC')
    w1 = dt('mulcld', [wc, one], '( W x. 1 ) e. CC')
    Ay = '( W e. CC /\\ y e. CC )'
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % Ay)
    ey = D(w, Ay, 'efcld', [yc], '( exp ` y ) e. CC')
    ef = a1(w, A, 'eff', 'exp : CC --> CC')
    feq = d('feqmptd', [ef], 'exp = ( y e. CC |-> ( exp ` y ) )')
    dve = a1(w, A, 'dvef', '( CC _D exp ) = exp')
    feq2 = d('eqcomd', [feq], '( y e. CC |-> ( exp ` y ) ) = exp')
    o2 = d('oveq2d', [feq2], '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( CC _D exp )')
    e1 = d('eqtrd', [o2, dve], '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = exp')
    e2 = d('eqtrd', [e1, feq], '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( y e. CC |-> ( exp ` y ) )')
    fv = w.s([], 'fveq2', '( y = ( W x. t ) -> ( exp ` y ) = %s )' % EWT)
    co = d('dvmptco', [rr, cc, wt, w1, ey, ey, dml, e2, fv, fv],
           '( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( %s x. ( W x. 1 ) ) )' % (EWT, EWT))
    mr = dt('mulridd', [wc], '( W x. 1 ) = W')
    o3 = dt('oveq2d', [mr], '( %s x. ( W x. 1 ) ) = ( %s x. W )' % (EWT, EWT))
    mp = d('mpteq2dva', [o3], '( t e. RR |-> ( %s x. ( W x. 1 ) ) ) = ( t e. RR |-> ( %s x. W ) )' % (EWT, EWT))
    fin = d('eqtrd', [co, mp], split_imp(S['gf1edv'])[1])
    w.qed([fin], 'idi', S['gf1edv'])
    return run(w, only)


if __name__ == '__main__':
    gen_edv()


FT = '( t e. RR |-> ( exp ` ( Z x. t ) ) )'
S['gf1em1'] = S['gf1em1']


def gen_em1():
    w = W('gf1em1', 'For ` 1 <_ M ` and ` exp ( Re Z ) <_ M ` , ` abs ( exp ( Z ) - 1 ) <_ M abs ( Z ) ` ( ~ dvlip on ` t |-> exp ( Z t ) ` over ` [ 0 , 1 ] ` ; Lean ` norm_exp_sub_one_le_of_re_nonpos ` is ` M = 1 ` ).')
    A, C = split_imp(S['gf1em1'])
    d = mk(w, A)
    zc = d('simpl', [], 'Z e. CC') if False else proj(w, A, 'Z e. CC')
    mr = proj(w, A, 'M e. RR')
    m1 = proj(w, A, '1 <_ M')
    em = proj(w, A, '( exp ` ( Re ` Z ) ) <_ M')
    At = '( %s /\\ t e. RR )' % A
    dt = mk(w, At)
    tr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    tc = dt('recnd', [tr], 't e. CC')
    zt = dt('mulcld', [lift(w, zc, At), tc], '( Z x. t ) e. CC')
    ez = dt('efcld', [zt], '( exp ` ( Z x. t ) ) e. CC')
    ff = d('fmptd', [ez], '%s : RR --> CC' % FT)
    edv = w.s([zc, w.inst('gf1edv')], 'syl', '( %s -> ( RR _D %s ) = ( t e. RR |-> ( ( exp ` ( Z x. t ) ) x. Z ) ) )' % (A, FT))
    ezz = dt('mulcld', [ez, lift(w, zc, At)], '( ( exp ` ( Z x. t ) ) x. Z ) e. CC')
    dm0 = d('dmmptd', [ezz], 'dom ( t e. RR |-> ( ( exp ` ( Z x. t ) ) x. Z ) ) = RR')
    dm1 = d('dmeqd', [edv], 'dom ( RR _D %s ) = dom ( t e. RR |-> ( ( exp ` ( Z x. t ) ) x. Z ) )' % FT)
    dm = d('eqtrd', [dm1, dm0], 'dom ( RR _D %s ) = RR' % FT)
    rc = a1(w, A, 'ax-resscn', 'RR C_ CC')
    rr = a1(w, A, 'ssid', 'RR C_ RR')
    j1 = d('3jca', [rc, ff, rr], '( RR C_ CC /\\ %s : RR --> CC /\\ RR C_ RR )' % FT)
    j2 = d('jca', [j1, dm], '( ( RR C_ CC /\\ %s : RR --> CC /\\ RR C_ RR ) /\\ dom ( RR _D %s ) = RR )' % (FT, FT))
    fcn = w.s([j2, w.inst('dvcn')], 'syl', '( %s -> %s e. ( RR -cn-> CC ) )' % (A, FT))
    U = '( 0 [,] 1 )'
    F1 = '( %s |` %s )' % (FT, U)
    us = a1(w, A, 'unitssre', '%s C_ RR' % U)
    rcn = w.s([us, w.inst('rescncf')], 'syl', '( %s -> ( %s e. ( RR -cn-> CC ) -> %s e. ( %s -cn-> CC ) ) )' % (A, FT, F1, U))
    f1cn = d('mpd', [fcn, rcn], '%s e. ( %s -cn-> CC )' % (F1, U))
    j3 = d('jca', [rc, ff], '( RR C_ CC /\\ %s : RR --> CC )' % FT)
    j4 = d('jca', [rr, us], '( RR C_ RR /\\ %s C_ RR )' % U)
    j5 = d('jca', [j3, j4], '( ( RR C_ CC /\\ %s : RR --> CC ) /\\ ( RR C_ RR /\\ %s C_ RR ) )' % (FT, U))
    TT = '( ( TopOpen ` CCfld ) |`t RR )'
    k1 = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    k2 = w.s([], 'eqid', '%s = %s' % (TT, TT))
    dres = w.s([k1, k2], 'dvres', '( ( ( RR C_ CC /\\ %s : RR --> CC ) /\\ ( RR C_ RR /\\ %s C_ RR ) ) -> ( RR _D %s ) = ( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (FT, U, F1, FT, TT, U))
    dr = w.s([j5, dres], 'syl', '( %s -> ( RR _D %s ) = ( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (A, F1, FT, TT, U))
    tg = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % TT)], 'eqcomi', '%s = ( topGen ` ran (,) )' % TT)
    tg2 = w.s([tg], 'fveq2i', '( int ` %s ) = ( int ` ( topGen ` ran (,) ) )' % TT)
    tg3 = w.s([tg2], 'fveq1i', '( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s )' % (TT, U, U))
    icn = w.s([w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR'), w.inst('iccntr')], 'mp2an', '( ( int ` ( topGen ` ran (,) ) ) ` %s ) = ( 0 (,) 1 )' % U)
    it = w.s([tg3, icn], 'eqtri', '( ( int ` %s ) ` %s ) = ( 0 (,) 1 )' % (TT, U))
    G = '( t e. RR |-> ( ( exp ` ( Z x. t ) ) x. Z ) )'
    G1_ = '( t e. ( 0 (,) 1 ) |-> ( ( exp ` ( Z x. t ) ) x. Z ) )'
    rs = d('reseq12d', [edv, a1(w, A, 'eqtri', '( ( int ` %s ) ` %s ) = ( 0 (,) 1 )' % (TT, U), [tg3, icn])],
           '( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( %s |` ( 0 (,) 1 ) )' % (FT, TT, U, G))
    rm = a1(w, A, 'ax-mp', '( %s |` ( 0 (,) 1 ) ) = %s' % (G, G1_), [w.s([], 'ioossre', '( 0 (,) 1 ) C_ RR'), w.inst('resmpt')])
    dF1 = chain(w, A, ['( RR _D %s )' % F1, '( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) )' % (FT, TT, U), '( %s |` ( 0 (,) 1 ) )' % G, G1_], [dr, rs, rm])
    Ax = '( %s /\\ x e. ( 0 (,) 1 ) )' % A
    dx = mk(w, Ax)
    xin = w.s([], 'simpr', '( %s -> x e. ( 0 (,) 1 ) )' % Ax)
    el = a1(w, Ax, 'mp2an', '( x e. ( 0 (,) 1 ) <-> ( x e. RR /\\ 0 < x /\\ x < 1 ) )', [w.s([], '0xr', '0 e. RR*'), w.s([], '1xr', '1 e. RR*'), w.inst('elioo2')])
    xe = dx('mpbid', [xin, el], '( x e. RR /\\ 0 < x /\\ x < 1 )')
    xr = dx('simp1d', [xe], 'x e. RR'); x0 = dx('simp2d', [xe], '0 < x'); x1 = dx('simp3d', [xe], 'x < 1')
    # x e. ( 0 (,) 1 ) inside the mpt domain: dmmptd for dom
    Atx = '( %s /\\ t e. ( 0 (,) 1 ) )' % A
    tr2 = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % Atx)
    tre = D(w, Atx, 'sseldi', [w.s([], 'ioossre', '( 0 (,) 1 ) C_ RR'), tr2], 't e. RR') if False else None
    tre = D(w, Atx, 'sseldd', [a1(w, Atx, 'ioossre', '( 0 (,) 1 ) C_ RR'), tr2], 't e. RR')
    tc2 = D(w, Atx, 'recnd', [tre], 't e. CC')
    ezz2 = D(w, Atx, 'mulcld', [D(w, Atx, 'efcld', [D(w, Atx, 'mulcld', [lift(w, zc, Atx), tc2], '( Z x. t ) e. CC')], '( exp ` ( Z x. t ) ) e. CC'), lift(w, zc, Atx)], '( ( exp ` ( Z x. t ) ) x. Z ) e. CC')
    dmg = d('dmmptd', [ezz2], 'dom %s = ( 0 (,) 1 )' % G1_)
    dmf1 = d('eqtrd', [d('dmeqd', [dF1], 'dom ( RR _D %s ) = dom %s' % (F1, G1_)), dmg], 'dom ( RR _D %s ) = ( 0 (,) 1 )' % F1)
    # the derivative at x
    xc = dx('recnd', [xr], 'x e. CC')
    zx = dx('mulcld', [lift(w, zc, Ax), xc], '( Z x. x ) e. CC')
    ezx = dx('efcld', [zx], '( exp ` ( Z x. x ) ) e. CC')
    val = dx('mulcld', [ezx, lift(w, zc, Ax)], '( ( exp ` ( Z x. x ) ) x. Z ) e. CC')
    fvx = w.s([], 'oveq2', '( t = x -> ( Z x. t ) = ( Z x. x ) )')
    fvx2 = w.s([fvx], 'fveq2d', '( t = x -> ( exp ` ( Z x. t ) ) = ( exp ` ( Z x. x ) ) )')
    fvx3 = w.s([fvx2], 'oveq1d', '( t = x -> ( ( exp ` ( Z x. t ) ) x. Z ) = ( ( exp ` ( Z x. x ) ) x. Z ) )')
    gdef = lift(w, dF1, Ax)
    fv1 = dx('fveq1d', [gdef], '( ( RR _D %s ) ` x ) = ( %s ` x )' % (F1, G1_))
    fv2 = D(w, Ax, 'fvmptd3', [w.s([], 'eqid', '%s = %s' % (G1_, G1_)), fvx3, xin, val], '( %s ` x ) = ( ( exp ` ( Z x. x ) ) x. Z )' % G1_) if False else None
    fv2 = dx('fvmptd', [a1(w, Ax, 'eqidd', '%s = %s' % (G1_, G1_)) if False else w.s([], 'eqidd', '( %s -> %s = %s )' % (Ax, G1_, G1_)),
                        dx('adantr', [], 'x') if False else w.s([fvx3], 'adantl', '( ( %s /\\ t = x ) -> ( ( exp ` ( Z x. t ) ) x. Z ) = ( ( exp ` ( Z x. x ) ) x. Z ) )' % Ax),
                        xin, val], '( %s ` x ) = ( ( exp ` ( Z x. x ) ) x. Z )' % G1_)
    dval = dx('eqtrd', [fv1, fv2], '( ( RR _D %s ) ` x ) = ( ( exp ` ( Z x. x ) ) x. Z )' % F1)
    # abs
    ab1 = dx('absmuld', [ezx, lift(w, zc, Ax)], '( abs ` ( ( exp ` ( Z x. x ) ) x. Z ) ) = ( ( abs ` ( exp ` ( Z x. x ) ) ) x. ( abs ` Z ) )')
    ab2 = dx('syl', [zx, w.inst('absef')], '( abs ` ( exp ` ( Z x. x ) ) ) = ( exp ` ( Re ` ( Z x. x ) ) )')
    zxc = dx('mulcomd', [lift(w, zc, Ax), xc], '( Z x. x ) = ( x x. Z )')
    re1 = dx('fveq2d', [zxc], '( Re ` ( Z x. x ) ) = ( Re ` ( x x. Z ) )')
    re2 = dx('syl2anc', [xr, lift(w, zc, Ax), w.inst('remul2')], '( Re ` ( x x. Z ) ) = ( x x. ( Re ` Z ) )')
    re3 = dx('eqtrd', [re1, re2], '( Re ` ( Z x. x ) ) = ( x x. ( Re ` Z ) )')
    ab3 = dx('fveq2d', [re3], '( exp ` ( Re ` ( Z x. x ) ) ) = ( exp ` ( x x. ( Re ` Z ) ) )')
    R = '( Re ` Z )'
    rre = dx('recld', [lift(w, zc, Ax)], '%s e. RR' % R)
    xrr = dx('remulcld', [xr, rre], '( x x. %s ) e. RR' % R)
    # case split on the sign of Re Z
    Ap = '( %s /\\ 0 <_ %s )' % (Ax, R)
    An = '( %s /\\ %s <_ 0 )' % (Ax, R)
    cl = Closure(w, Ap, {'x': lift(w, xr, Ap), R: lift(w, rre, Ap)})
    lp = lin.nlinarith(w, Ap, [lift(w, x1, Ap), w.s([], 'simpr', '( %s -> 0 <_ %s )' % (Ap, R))], '( x x. %s ) <_ %s' % (R, R), closure=cl)
    efp = D(w, Ap, 'mpbid', [lp, D(w, Ap, 'syl2anc', [lift(w, xrr, Ap), lift(w, rre, Ap), w.inst('efle')], '( ( x x. %s ) <_ %s <-> ( exp ` ( x x. %s ) ) <_ ( exp ` %s ) )' % (R, R, R, R))],
            '( exp ` ( x x. %s ) ) <_ ( exp ` %s )' % (R, R))
    bp = D(w, Ap, 'letrd', [D(w, Ap, 'efcld', [lift(w, xrr, Ap)], '( exp ` ( x x. %s ) ) e. RR' % R) if False else D(w, Ap, 'reefcld', [lift(w, xrr, Ap)], '( exp ` ( x x. %s ) ) e. RR' % R),
                            D(w, Ap, 'reefcld', [lift(w, rre, Ap)], '( exp ` %s ) e. RR' % R), lift(w, mr, Ap), efp, lift(w, em, Ap)],
           '( exp ` ( x x. %s ) ) <_ M' % R)
    cln = Closure(w, An, {'x': lift(w, xr, An), R: lift(w, rre, An)})
    ln = lin.nlinarith(w, An, [lift(w, x0, An), w.s([], 'simpr', '( %s -> %s <_ 0 )' % (An, R))], '( x x. %s ) <_ 0' % R, closure=cln)
    z0 = a1(w, An, '0re', '0 e. RR')
    efn = D(w, An, 'mpbid', [ln, D(w, An, 'syl2anc', [lift(w, xrr, An), z0, w.inst('efle')], '( ( x x. %s ) <_ 0 <-> ( exp ` ( x x. %s ) ) <_ ( exp ` 0 ) )' % (R, R))],
            '( exp ` ( x x. %s ) ) <_ ( exp ` 0 )' % R)
    efn2 = D(w, An, 'breqtrd', [efn, a1(w, An, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( x x. %s ) ) <_ 1' % R)
    bn = D(w, An, 'letrd', [D(w, An, 'reefcld', [lift(w, xrr, An)], '( exp ` ( x x. %s ) ) e. RR' % R), a1(w, An, '1re', '1 e. RR'), lift(w, mr, An), efn2, lift(w, m1, An)],
           '( exp ` ( x x. %s ) ) <_ M' % R)
    tri = dx('syl2anc', [a1(w, Ax, '0re', '0 e. RR'), rre, w.inst('letric')], '( 0 <_ %s \\/ %s <_ 0 )' % (R, R))
    bx = dx('mpjaodan', [bp, bn, tri], '( exp ` ( x x. %s ) ) <_ M' % R)
    ab4 = chain(w, Ax, ['( abs ` ( exp ` ( Z x. x ) ) )', '( exp ` ( Re ` ( Z x. x ) ) )', '( exp ` ( x x. %s ) )' % R, 'M'], [ab2, ab3, bx], ['=', '=', '<_'])
    azr = dx('abscld', [lift(w, zc, Ax)], '( abs ` Z ) e. RR')
    az0 = dx('absge0d', [lift(w, zc, Ax)], '0 <_ ( abs ` Z )')
    aer = dx('abscld', [ezx], '( abs ` ( exp ` ( Z x. x ) ) ) e. RR')
    mul = dx('lemul1ad', [aer, lift(w, mr, Ax), azr, az0, ab4], '( ( abs ` ( exp ` ( Z x. x ) ) ) x. ( abs ` Z ) ) <_ ( M x. ( abs ` Z ) )')
    dvb0 = dx('fveq2d', [dval], '( abs ` ( ( RR _D %s ) ` x ) ) = ( abs ` ( ( exp ` ( Z x. x ) ) x. Z ) )' % F1)
    dvb = chain(w, Ax, ['( abs ` ( ( RR _D %s ) ` x ) )' % F1, '( abs ` ( ( exp ` ( Z x. x ) ) x. Z ) )', '( ( abs ` ( exp ` ( Z x. x ) ) ) x. ( abs ` Z ) )', '( M x. ( abs ` Z ) )'],
                [dvb0, ab1, mul], ['=', '=', '<_'])
    MZ = '( M x. ( abs ` Z ) )'
    mzr = d('remulcld', [mr, d('abscld', [zc], '( abs ` Z ) e. RR')], '%s e. RR' % MZ)
    Aii = '( %s /\\ ( 1 e. %s /\\ 0 e. %s ) )' % (A, U, U)
    lip = w.s([a1(w, A, '0re', '0 e. RR'), a1(w, A, '1re', '1 e. RR'), f1cn, dmf1, mzr, dvb], 'dvlip',
              '( %s -> ( abs ` ( ( %s ` 1 ) - ( %s ` 0 ) ) ) <_ ( %s x. ( abs ` ( 1 - 0 ) ) ) )' % (Aii, F1, F1, MZ))
    ii = d('jca', [a1(w, A, '1elunit', '1 e. %s' % U), a1(w, A, '0elunit', '0 e. %s' % U)], '( 1 e. %s /\\ 0 e. %s )' % (U, U))
    lip2 = d('mpdan', [ii, lip], '( abs ` ( ( %s ` 1 ) - ( %s ` 0 ) ) ) <_ ( %s x. ( abs ` ( 1 - 0 ) ) )' % (F1, F1, MZ))
    # evaluate
    def fval(p, pin, pr, ev):
        """( A -> ( F1 ` p ) = ev )"""
        r1 = a1(w, A, 'ax-mp', '( %s ` %s ) = ( %s ` %s )' % (F1, p, FT, p), [w.s([], pin, '%s e. %s' % (p, U)), w.inst('fvres')])
        fvp = w.s([], 'oveq2', '( t = %s -> ( Z x. t ) = ( Z x. %s ) )' % (p, p))
        fvp2 = w.s([fvp], 'fveq2d', '( t = %s -> ( exp ` ( Z x. t ) ) = ( exp ` ( Z x. %s ) ) )' % (p, p))
        pc = a1(w, A, pr, '%s e. RR' % p)
        zp = d('mulcld', [zc, d('recnd', [pc], '%s e. CC' % p)], '( Z x. %s ) e. CC' % p)
        r2 = d('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (A, FT, FT)), w.s([fvp2], 'adantl', '( ( %s /\\ t = %s ) -> ( exp ` ( Z x. t ) ) = ( exp ` ( Z x. %s ) ) )' % (A, p, p)),
                               pc, d('efcld', [zp], '( exp ` ( Z x. %s ) ) e. CC' % p)], '( %s ` %s ) = ( exp ` ( Z x. %s ) )' % (FT, p, p))
        return chain(w, A, ['( %s ` %s )' % (F1, p), '( %s ` %s )' % (FT, p), '( exp ` ( Z x. %s ) )' % p, ev], [r1, r2, ev_step(p)])
    def ev_step(p):
        if p == '1':
            m = d('mulridd', [zc], '( Z x. 1 ) = Z')
            return d('fveq2d', [m], '( exp ` ( Z x. 1 ) ) = ( exp ` Z )')
        m = d('mul01d', [zc], '( Z x. 0 ) = 0')
        e = d('fveq2d', [m], '( exp ` ( Z x. 0 ) ) = ( exp ` 0 )')
        return d('eqtrd', [e, a1(w, A, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( Z x. 0 ) ) = 1')
    v1 = fval('1', '1elunit', '1re', '( exp ` Z )')
    v0 = fval('0', '0elunit', '0re', '1')
    dif = d('oveq12d', [v1, v0], '( ( %s ` 1 ) - ( %s ` 0 ) ) = ( ( exp ` Z ) - 1 )' % (F1, F1))
    adif = d('fveq2d', [dif], '( abs ` ( ( %s ` 1 ) - ( %s ` 0 ) ) ) = ( abs ` ( ( exp ` Z ) - 1 ) )' % (F1, F1))
    one = a1(w, A, 'eqtri', '( abs ` ( 1 - 0 ) ) = 1', [w.s([], '1m0e1', '( 1 - 0 ) = 1') if False else w.s([w.s([], '1m0e1', '( 1 - 0 ) = 1')], 'fveq2i', '( abs ` ( 1 - 0 ) ) = ( abs ` 1 )'), w.s([], 'abs1', '( abs ` 1 ) = 1')])
    rhs1 = d('oveq2d', [one], '( %s x. ( abs ` ( 1 - 0 ) ) ) = ( %s x. 1 )' % (MZ, MZ))
    rhs2 = d('eqtrd', [rhs1, d('mulridd', [d('recnd', [mzr], '%s e. CC' % MZ)], '( %s x. 1 ) = %s' % (MZ, MZ))], '( %s x. ( abs ` ( 1 - 0 ) ) ) = %s' % (MZ, MZ))
    fin = chain(w, A, ['( abs ` ( ( exp ` Z ) - 1 ) )', '( abs ` ( ( %s ` 1 ) - ( %s ` 0 ) ) )' % (F1, F1), '( %s x. ( abs ` ( 1 - 0 ) ) )' % MZ, MZ],
                [('r', adif), lip2, rhs2], ['=', '<_', '='])
    w.qed([fin], 'idi', S['gf1em1'])
    return run(w, only)


if __name__ == '__main__':
    gen_em1()
