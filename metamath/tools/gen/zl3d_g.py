"""ZL3d section G: the Mellin identity (zl3mel).  `MM_DB=sorties/zl3d.mm python3 tools/gen/zl3d_g.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl3d_f import *
from zl3c_b import cont

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL3D_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if L.HYPS.get(w.label) else w.run()


def want(label):
    return __name__ == '__main__' and (not only or label in only)


def FX(W, Lc, x='x'):
    return '( ( exp ` -u ( %s x. %s ) ) x. ( %s ^c ( %s - 1 ) ) )' % (Lc, x, x, W)


def gibl(w, A, P, Q, pr, qr, W, Lc, wc, lc, prp=None, w1=None):
    """( A -> ( x e. ( P (,) Q ) |-> FX ) e. L^1 ).  prp: ( A -> P e. RR+ ) (general W), or P = 0 with w1: ( A -> 0 < ( Re ` ( W - 1 ) ) )"""
    I = '( %s [,] %s )' % (P, Q); X = '( %s (,) %s )' % (P, Q)
    wm1 = D(w, A, 'subcld', [wc, cst(w, A, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % W)
    CXm = '( x e. %s |-> ( x ^c ( %s - 1 ) ) )' % (I, W)
    if prp is not None:
        both = D(w, A, 'syl2anc', [wm1, D(w, A, 'jca', [prp, qr], '( %s e. RR+ /\\ %s e. RR )' % (P, Q)), w.inst('zl3cxc')],
                 '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c ( %s - 1 ) ) ) ) e. ( %s -cn-> CC ) )' % (CXm, I, I, W, I))
        cx = D(w, A, 'simpld', [both], '%s e. ( %s -cn-> CC )' % (CXm, I))
    else:
        assert P == '0'
        cx = D(w, A, 'syl2anc', [D(w, A, 'jca', [wm1, w1], '( ( %s - 1 ) e. CC /\\ 0 < ( Re ` ( %s - 1 ) ) )' % (W, W)), qr if False else None, w.inst('zl3ccx')], '') if False else \
            D(w, A, 'syl2anc', [D(w, A, 'jca', [wm1, w1], '( ( %s - 1 ) e. CC /\\ 0 < ( Re ` ( %s - 1 ) ) )' % (W, W)), qr, w.inst('zl3ccx')], '%s e. ( %s -cn-> CC )' % (CXm, I))
    xss = D(w, A, 'syl2anc', [pr, D(w, A, 'rpred', [qr], '%s e. RR' % Q) if prp is None else qr, w.inst('iccssre')], '%s C_ RR' % I) if False else None
    qre = D(w, A, 'rpred', [qr], '%s e. RR' % Q) if prp is None else qr
    xss = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [pr, qre, w.inst('iccssre')], '%s C_ RR' % I), cst(w, A, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    cl = Closure(w, A, {Lc: lc})
    cfull = cont(w, A, I, FX(W, Lc), cl, xss, special={'( x ^c ( %s - 1 ) )' % W: cx})
    ib = D(w, A, 'syl2anc', [D(w, A, 'jca', [pr, qre], '( %s e. RR /\\ %s e. RR )' % (P, Q)), cfull, w.inst('zl3ibl')], '( ( x e. %s |-> %s ) |` %s ) e. L^1' % (I, FX(W, Lc), X))
    rs = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( ( x e. %s |-> %s ) |` %s ) = ( x e. %s |-> %s )' % (I, FX(W, Lc), X, X, FX(W, Lc)))
    return D(w, A, 'eqeltrrd', [w.s([rs], 'a1i', '( %s -> ( ( x e. %s |-> %s ) |` %s ) = ( x e. %s |-> %s ) )' % (A, I, FX(W, Lc), X, X, FX(W, Lc))), ib], '( x e. %s |-> %s ) e. L^1' % (X, FX(W, Lc)))


def fx_cl(w, A, P, Q, pr, W, Lc, wc, lc, p0):
    """( ( A /\\ x e. ( P (,) Q ) ) -> FX e. CC ), p0: ( A -> 0 <_ P )"""
    X = '( %s (,) %s )' % (P, Q)
    Ax = '( %s /\\ x e. %s )' % (A, X)
    xx = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, X))
    xr = D(w, Ax, 'sseldd', [cst(w, Ax, 'ioossre', '%s C_ RR' % X), xx], 'x e. RR')
    xc = D(w, Ax, 'recnd', [xr], 'x e. CC')
    e = D(w, Ax, 'efcld', [D(w, Ax, 'negcld', [D(w, Ax, 'mulcld', [ad(w, Ax, lc, '%s e. CC' % Lc), xc], '( %s x. x ) e. CC' % Lc)], '-u ( %s x. x ) e. CC' % Lc)], '( exp ` -u ( %s x. x ) ) e. CC' % Lc)
    c = D(w, Ax, 'cxpcld', [xc, D(w, Ax, 'subcld', [ad(w, Ax, wc, '%s e. CC' % W), cst(w, Ax, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % W)], '( x ^c ( %s - 1 ) ) e. CC' % W)
    return D(w, Ax, 'mulcld', [e, c], '%s e. CC' % FX(W, Lc))


# ---------------------------------------------------------------- zl3ew1
if want('zl3ew1'):
    w = W('zl3ew1', 'Euler integral over ` ( 1 / t , t ) ` on ` 1 < Re W ` ( from ~ zl3eul : the piece over ` ( 0 , 1 / t ) ` is at most ` 1 / t ` ).')
    A, Cc = ante_of('zl3ew1')
    wc = D(w, A, 'simpll', [], 'W e. CC'); w1 = D(w, A, 'simplr', [], '1 < ( Re ` W )'); lrp = D(w, A, 'simpr', [], 'L e. RR+')
    lc = D(w, A, 'rpcnd', [lrp], 'L e. CC')
    V = '( ( L ^c -u W ) x. ( _G ` W ) )'
    F0 = 'S. ( 0 (,) t ) %s _d x' % FX('W', 'L')
    G0 = 'S. ( 0 (,) ( 1 / t ) ) %s _d x' % FX('W', 'L')
    CT = L.EUI('W', 'L', 't')
    eul = D(w, A, 'id', [], A) and w.s([D(w, A, 'id', [], A), w.inst('zl3eul')], 'syl', '( %s -> ( t e. RR+ |-> %s ) ~~>r %s )' % (A, F0, V))
    wr1 = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    rw1 = D(w, A, 'eqtrd', [D(w, A, 'resubd', [wc, cst(w, A, 'ax-1cn', '1 e. CC')], '( Re ` ( W - 1 ) ) = ( ( Re ` W ) - ( Re ` 1 ) )'),
                            D(w, A, 'oveq2d', [cst(w, A, 're1', '( Re ` 1 ) = 1')], '( ( Re ` W ) - ( Re ` 1 ) ) = ( ( Re ` W ) - 1 )')], '( Re ` ( W - 1 ) ) = ( ( Re ` W ) - 1 )')
    rp1 = D(w, A, 'eqbrtrrd', [rw1, linarith(w, A, [w1], '0 < ( ( Re ` W ) - 1 )', leaves={'( Re ` W )': wr1}, atoms=['( Re ` W )'])], '0 < ( Re ` ( W - 1 ) )') if False else \
        D(w, A, 'breqtrrd', [linarith(w, A, [w1], '0 < ( ( Re ` W ) - 1 )', leaves={'( Re ` W )': wr1}, atoms=['( Re ` W )']), rw1], '0 < ( Re ` ( W - 1 ) )')
    At = '( %s /\\ t e. RR+ )' % A
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    tr = D(w, At, 'rpred', [trp], 't e. RR')
    def u(st, f):
        return ad(w, At, st, f)
    wct, lct, rp1t = u(wc, 'W e. CC'), u(lc, 'L e. CC'), u(rp1, '0 < ( Re ` ( W - 1 ) )')
    i0t = gibl(w, At, '0', 't', cst(w, At, '0re', '0 e. RR'), trp, 'W', 'L', wct, lct, w1=rp1t)
    c0t = fx_cl(w, At, '0', 't', cst(w, At, '0re', '0 e. RR'), 'W', 'L', wct, lct, None)
    f0c = D(w, At, 'itgcl', [i0t, c0t], '%s e. CC' % F0)
    # eventually ( t >_ 1 )
    Au = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % A
    trp2 = w.s([], 'simprl', '( %s -> t e. RR+ )' % Au); t1 = w.s([], 'simprr', '( %s -> 1 <_ t )' % Au)
    tr2 = D(w, Au, 'rpred', [trp2], 't e. RR')
    it = D(w, Au, 'rpreccld', [trp2], '( 1 / t ) e. RR+')
    itr = D(w, Au, 'rpred', [it], '( 1 / t ) e. RR')
    tc2 = D(w, Au, 'rpcnd', [trp2], 't e. CC'); tne2 = D(w, Au, 'rpne0d', [trp2], 't =/= 0')
    IT = '( 1 / t )'
    rid = D(w, Au, 'recid2d', [tc2, tne2], '( %s x. t ) = 1' % IT)
    itle1 = nlinarith(w, Au, [rid, t1, D(w, Au, 'rpge0d', [it], '0 <_ %s' % IT)], '%s <_ 1' % IT, leaves={IT: itr, 't': tr2}, atoms=[IT])
    itlet = D(w, Au, 'letrd', [itr, cst(w, Au, '1re', '1 e. RR'), tr2, itle1, t1], '%s <_ t' % IT)
    wcu, lcu, rp1u = ad(w, Au, wc, 'W e. CC'), ad(w, Au, lc, 'L e. CC'), ad(w, Au, rp1, '0 < ( Re ` ( W - 1 ) )')
    zre = cst(w, Au, '0re', '0 e. RR')
    i01 = gibl(w, Au, '0', IT, zre, it, 'W', 'L', wcu, lcu, w1=rp1u)
    i1t = gibl(w, Au, IT, 't', itr, tr2, 'W', 'L', wcu, lcu, prp=it)
    c0u = fx_cl(w, Au, '0', 't', zre, 'W', 'L', wcu, lcu, None)
    inI = D(w, Au, 'mpbir3and', [itr, D(w, Au, 'rpge0d', [it], '0 <_ %s' % IT), itlet, D(w, Au, 'syl2anc', [zre, tr2, w.inst('elicc2')], '( %s e. ( 0 [,] t ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ t ) )' % (IT, IT, IT, IT))],
            '%s e. ( 0 [,] t )' % IT)
    spl = D(w, Au, 'itgsplitioo', [zre, tr2, inI, c0u, i01, i1t], '%s = ( %s + %s )' % (F0, G0, CT))
    g0c = D(w, Au, 'itgcl', [i01, fx_cl(w, Au, '0', IT, zre, 'W', 'L', wcu, lcu, None)], '%s e. CC' % G0)
    ctc = D(w, Au, 'itgcl', [i1t, fx_cl(w, Au, IT, 't', itr, 'W', 'L', wcu, lcu, None)], '%s e. CC' % CT)
    # | G0 | <_ 1 / t
    X0 = '( 0 (,) %s )' % IT
    Ax = '( %s /\\ x e. %s )' % (Au, X0)
    xx = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, X0))
    bi = D(w, Ax, 'syl2anc', [D(w, Ax, 'rexrd', [cst(w, Ax, '0re', '0 e. RR')], '0 e. RR*'), D(w, Ax, 'rexrd', [ad(w, Ax, itr, '%s e. RR' % IT)], '%s e. RR*' % IT), w.inst('elioo2')],
           '( x e. %s <-> ( x e. RR /\\ 0 < x /\\ x < %s ) )' % (X0, IT))
    tr_ = D(w, Ax, 'mpbid', [xx, bi], '( x e. RR /\\ 0 < x /\\ x < %s )' % IT)
    xr = D(w, Ax, 'simp1d', [tr_], 'x e. RR'); x0 = D(w, Ax, 'simp2d', [tr_], '0 < x'); xlt = D(w, Ax, 'simp3d', [tr_], 'x < %s' % IT)
    xrp = D(w, Ax, 'elrpd', [xr, x0], 'x e. RR+')
    x1 = D(w, Ax, 'ltled', [xr, cst(w, Ax, '1re', '1 e. RR'), linarith(w, Ax, [xlt, ad(w, Ax, itle1, '%s <_ 1' % IT)], 'x < 1', leaves={'x': xr, IT: ad(w, Ax, itr, '%s e. RR' % IT)}, atoms=[IT])], 'x <_ 1')
    lx = D(w, Ax, 'mpbid', [x1, D(w, Ax, 'logled', [xrp, cst(w, Ax, '1rp', '1 e. RR+')], '( x <_ 1 <-> ( log ` x ) <_ ( log ` 1 ) )')], '( log ` x ) <_ ( log ` 1 )')
    lx0 = D(w, Ax, 'breqtrd', [lx, cst(w, Ax, 'log1', '( log ` 1 ) = 0')], '( log ` x ) <_ 0')
    RW = '( Re ` ( W - 1 ) )'
    rwr = D(w, Ax, 'recld', [D(w, Ax, 'subcld', [ad(w, Ax, wcu, 'W e. CC'), cst(w, Ax, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')], '%s e. RR' % RW)
    ax_ = D(w, Ax, 'eqtrd', [D(w, Ax, 'syl2anc', [xrp, D(w, Ax, 'subcld', [ad(w, Ax, wcu, 'W e. CC'), cst(w, Ax, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC'), w.inst('abscxp')],
                                  '( abs ` ( x ^c ( W - 1 ) ) ) = ( x ^c %s )' % RW),
                             D(w, Ax, 'syl3anc', [D(w, Ax, 'rpcnd', [xrp], 'x e. CC'), D(w, Ax, 'rpne0d', [xrp], 'x =/= 0'), D(w, Ax, 'recnd', [rwr], '%s e. CC' % RW), w.inst('cxpef')],
                               '( x ^c %s ) = ( exp ` ( %s x. ( log ` x ) ) )' % (RW, RW))], '( abs ` ( x ^c ( W - 1 ) ) ) = ( exp ` ( %s x. ( log ` x ) ) )' % RW)
    lxr = D(w, Ax, 'relogcld', [xrp], '( log ` x ) e. RR')
    ee = efle_(w, Ax, '( %s x. ( log ` x ) )' % RW, '0', D(w, Ax, 'remulcld', [rwr, lxr], '( %s x. ( log ` x ) ) e. RR' % RW), cst(w, Ax, '0re', '0 e. RR'),
               nlinarith(w, Ax, [ad(w, Ax, ad(w, Au, rp1u, '0 < %s' % RW) if False else rp1u, '0 < %s' % RW), lx0], '( %s x. ( log ` x ) ) <_ 0' % RW, leaves={RW: rwr, '( log ` x )': lxr}, atoms=[RW, '( log ` x )']))
    ab1 = D(w, Ax, 'eqbrtrd', [ax_, D(w, Ax, 'breqtrd', [ee, cst(w, Ax, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( %s x. ( log ` x ) ) ) <_ 1' % RW)], '( abs ` ( x ^c ( W - 1 ) ) ) <_ 1')
    EL = '( exp ` -u ( L x. x ) )'
    elr = D(w, Ax, 'reefcld', [D(w, Ax, 'renegcld', [D(w, Ax, 'remulcld', [D(w, Ax, 'rpred', [ad(w, Ax, ad(w, Au, lrp, 'L e. RR+'), 'L e. RR+')], 'L e. RR'), xr], '( L x. x ) e. RR')], '-u ( L x. x ) e. RR')], '%s e. RR' % EL)
    el1 = D(w, Ax, 'breqtrd', [efle_(w, Ax, '-u ( L x. x )', '0', D(w, Ax, 'renegcld', [D(w, Ax, 'remulcld', [D(w, Ax, 'rpred', [ad(w, Ax, ad(w, Au, lrp, 'L e. RR+'), 'L e. RR+')], 'L e. RR'), xr], '( L x. x ) e. RR')], '-u ( L x. x ) e. RR'),
                                     cst(w, Ax, '0re', '0 e. RR'), nlinarith(w, Ax, [D(w, Ax, 'rpgt0d', [ad(w, Ax, ad(w, Au, lrp, 'L e. RR+'), 'L e. RR+')], '0 < L'), x0], '-u ( L x. x ) <_ 0',
                                                                          leaves={'L': D(w, Ax, 'rpred', [ad(w, Ax, ad(w, Au, lrp, 'L e. RR+'), 'L e. RR+')], 'L e. RR'), 'x': xr})),
                                cst(w, Ax, 'ef0', '( exp ` 0 ) = 1')], '%s <_ 1' % EL)
    xc = D(w, Ax, 'recnd', [xr], 'x e. CC')
    cxc = D(w, Ax, 'cxpcld', [xc, D(w, Ax, 'subcld', [ad(w, Ax, wcu, 'W e. CC'), cst(w, Ax, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')], '( x ^c ( W - 1 ) ) e. CC')
    abf = D(w, Ax, 'eqtrd', [D(w, Ax, 'absmuld', [D(w, Ax, 'recnd', [elr], '%s e. CC' % EL), cxc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( x ^c ( W - 1 ) ) ) )' % (FX('W', 'L'), EL)),
                             D(w, Ax, 'oveq1d', [D(w, Ax, 'absidd', [elr, D(w, Ax, 'rpge0d', [D(w, Ax, 'rpefcld', [D(w, Ax, 'renegcld', [D(w, Ax, 'remulcld', [D(w, Ax, 'rpred', [ad(w, Ax, ad(w, Au, lrp, 'L e. RR+'), 'L e. RR+')], 'L e. RR'), xr], '( L x. x ) e. RR')], '-u ( L x. x ) e. RR')], '%s e. RR+' % EL)], '0 <_ %s' % EL)],
                                                  '( abs ` %s ) = %s' % (EL, EL))], '( ( abs ` %s ) x. ( abs ` ( x ^c ( W - 1 ) ) ) ) = ( %s x. ( abs ` ( x ^c ( W - 1 ) ) ) )' % (EL, EL))],
              '( abs ` %s ) = ( %s x. ( abs ` ( x ^c ( W - 1 ) ) ) )' % (FX('W', 'L'), EL))
    acr = D(w, Ax, 'abscld', [cxc], '( abs ` ( x ^c ( W - 1 ) ) ) e. RR')
    pb = D(w, Ax, 'eqbrtrd', [abf, D(w, Ax, 'breqtrd', [D(w, Ax, 'lemul12ad', [elr, cst(w, Ax, '1re', '1 e. RR'), acr, cst(w, Ax, '1re', '1 e. RR'), D(w, Ax, 'rpge0d', [D(w, Ax, 'rpefcld', [D(w, Ax, 'renegcld', [D(w, Ax, 'remulcld', [D(w, Ax, 'rpred', [ad(w, Ax, ad(w, Au, lrp, 'L e. RR+'), 'L e. RR+')], 'L e. RR'), xr], '( L x. x ) e. RR')], '-u ( L x. x ) e. RR')], '%s e. RR+' % EL)], '0 <_ %s' % EL),
                                                                       D(w, Ax, 'absge0d', [cxc], '0 <_ ( abs ` ( x ^c ( W - 1 ) ) )'), el1, ab1], '( %s x. ( abs ` ( x ^c ( W - 1 ) ) ) ) <_ ( 1 x. 1 )' % EL),
                                                    cst(w, Ax, '1t1e1', '( 1 x. 1 ) = 1')], '( %s x. ( abs ` ( x ^c ( W - 1 ) ) ) ) <_ 1' % EL)], '( abs ` %s ) <_ 1' % FX('W', 'L'))
    c01 = fx_cl(w, Au, '0', IT, zre, 'W', 'L', wcu, lcu, None)
    vol = D(w, Au, 'syl3anc', [zre, itr, D(w, Au, 'rpge0d', [it], '0 <_ %s' % IT), w.inst('volioo')], '( vol ` %s ) = ( %s - 0 )' % (X0, IT))
    vr = D(w, Au, 'eqeltrd', [vol, D(w, Au, 'resubcld', [itr, zre], '( %s - 0 ) e. RR' % IT)], '( vol ` %s ) e. RR' % X0)
    i1c = D(w, Au, 'eqeltrrd', [w.s([w.s([], 'fconstmpt', '( %s X. { 1 } ) = ( x e. %s |-> 1 )' % (X0, X0))], 'a1i', '( %s -> ( %s X. { 1 } ) = ( x e. %s |-> 1 ) )' % (Au, X0, X0)),
                                D(w, Au, 'syl3anc', [cst(w, Au, 'ioombl', '%s e. dom vol' % X0), vr, cst(w, Au, 'ax-1cn', '1 e. CC'), w.inst('iblconst')], '( %s X. { 1 } ) e. L^1' % X0)], '( x e. %s |-> 1 ) e. L^1' % X0)
    iab = D(w, Au, 'iblabs', [c01, i01], '( x e. %s |-> ( abs ` %s ) ) e. L^1' % (X0, FX('W', 'L')))
    le1 = D(w, Au, 'itgle', [iab, i1c, D(w, Ax, 'abscld', [c01], '( abs ` %s ) e. RR' % FX('W', 'L')), cst(w, Ax, '1re', '1 e. RR'), pb], 'S. %s ( abs ` %s ) _d x <_ S. %s 1 _d x' % (X0, FX('W', 'L'), X0))
    ic1 = D(w, Au, 'eqtrd', [D(w, Au, 'syl3anc', [cst(w, Au, 'ioombl', '%s e. dom vol' % X0), vr, cst(w, Au, 'ax-1cn', '1 e. CC'), w.inst('itgconst')], 'S. %s 1 _d x = ( 1 x. ( vol ` %s ) )' % (X0, X0)),
                             D(w, Au, 'eqtrd', [D(w, Au, 'mullidd', [D(w, Au, 'recnd', [vr], '( vol ` %s ) e. CC' % X0)], '( 1 x. ( vol ` %s ) ) = ( vol ` %s )' % (X0, X0)),
                                                D(w, Au, 'eqtrd', [vol, D(w, Au, 'subid1d', [D(w, Au, 'recnd', [itr], '%s e. CC' % IT)], '( %s - 0 ) = %s' % (IT, IT))], '( vol ` %s ) = %s' % (X0, IT))], '( 1 x. ( vol ` %s ) ) = %s' % (X0, IT))],
              'S. %s 1 _d x = %s' % (X0, IT))
    gb = D(w, Au, 'letrd', [D(w, Au, 'abscld', [g0c], '( abs ` %s ) e. RR' % G0), D(w, Au, 'itgrecl', [D(w, Ax, 'abscld', [c01], '( abs ` %s ) e. RR' % FX('W', 'L')), iab], 'S. %s ( abs ` %s ) _d x e. RR' % (X0, FX('W', 'L'))), itr,
                            D(w, Au, 'itgabs', [c01, i01], '( abs ` %s ) <_ S. %s ( abs ` %s ) _d x' % (G0, X0, FX('W', 'L'))), D(w, Au, 'breqtrd', [le1, ic1], 'S. %s ( abs ` %s ) _d x <_ %s' % (X0, FX('W', 'L'), IT))],
           '( abs ` %s ) <_ %s' % (G0, IT))
    # the squeeze
    vc = D(w, A, 'syl', [eul, w.inst('rlimcl')], '%s e. CC' % V)
    FV = '( abs ` ( %s - %s ) )' % (F0, V)
    Bt = '( %s + ( 1 / t ) )' % FV
    rsub = D(w, A, 'rlimsub', [f0c, ad(w, At, vc, '%s e. CC' % V), eul, D(w, A, 'rlimconst', [cst(w, A, 'rpssre', 'RR+ C_ RR'), vc], '( t e. RR+ |-> %s ) ~~>r %s' % (V, V)) if False else
                                D(w, A, 'syl2anc', [cst(w, A, 'rpssre', 'RR+ C_ RR'), vc, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (V, V))],
             '( t e. RR+ |-> ( %s - %s ) ) ~~>r ( %s - %s )' % (F0, V, V, V))
    rab = D(w, A, 'rlimabs', [D(w, At, 'subcld', [f0c, ad(w, At, vc, '%s e. CC' % V)], '( %s - %s ) e. CC' % (F0, V)), rsub], '( t e. RR+ |-> %s ) ~~>r ( abs ` ( %s - %s ) )' % (FV, V, V))
    vv0 = D(w, A, 'eqtrd', [D(w, A, 'fveq2d', [D(w, A, 'subidd', [vc], '( %s - %s ) = 0' % (V, V))], '( abs ` ( %s - %s ) ) = ( abs ` 0 )' % (V, V)), cst(w, A, 'abs0', '( abs ` 0 ) = 0')], '( abs ` ( %s - %s ) ) = 0' % (V, V))
    rab0 = D(w, A, 'breqtrd', [rab, vv0], '( t e. RR+ |-> %s ) ~~>r 0' % FV)
    r1t = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('divrcnv')], 'ax-mp', '( t e. RR+ |-> ( 1 / t ) ) ~~>r 0')], 'a1i', '( %s -> ( t e. RR+ |-> ( 1 / t ) ) ~~>r 0 )' % A)
    fvc = D(w, At, 'recnd', [D(w, At, 'abscld', [D(w, At, 'subcld', [f0c, ad(w, At, vc, '%s e. CC' % V)], '( %s - %s ) e. CC' % (F0, V))], '%s e. RR' % FV)], '%s e. CC' % FV)
    itc = D(w, At, 'rpcnd', [D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+')], '( 1 / t ) e. CC')
    radd = D(w, A, 'rlimadd', [fvc, itc, rab0, r1t], '( t e. RR+ |-> %s ) ~~>r ( 0 + 0 )' % Bt)
    radd0 = D(w, A, 'breqtrd', [radd, cst(w, A, '00id', '( 0 + 0 ) = 0')], '( t e. RR+ |-> %s ) ~~>r 0' % Bt)
    # the bound for t >_ 1
    ct_ = D(w, Au, 'eqcomd', [D(w, Au, 'eqtr4d', [D(w, Au, 'oveq1d', [spl], '( %s - %s ) = ( ( %s + %s ) - %s )' % (F0, G0, G0, CT, G0)), D(w, Au, 'pncan2d', [g0c, ctc], '( ( %s + %s ) - %s ) = %s' % (G0, CT, G0, CT))],
                                     '') if False else D(w, Au, 'eqtrd', [D(w, Au, 'oveq1d', [spl], '( %s - %s ) = ( ( %s + %s ) - %s )' % (F0, G0, G0, CT, G0)), D(w, Au, 'pncan2d', [g0c, ctc], '( ( %s + %s ) - %s ) = %s' % (G0, CT, G0, CT))],
                                                                       '( %s - %s ) = %s' % (F0, G0, CT))], '%s = ( %s - %s )' % (CT, F0, G0))
    f0u = ad(w, Au, D(w, A, 'idi', [], '') if False else None, '') if False else None
    f0cu = D(w, Au, 'itgcl', [gibl(w, Au, '0', 't', zre, trp2, 'W', 'L', wcu, lcu, w1=rp1u), c0u], '%s e. CC' % F0)
    vcu = ad(w, Au, vc, '%s e. CC' % V)
    d1 = D(w, Au, 'eqtrd', [D(w, Au, 'oveq1d', [ct_], '( %s - %s ) = ( ( %s - %s ) - %s )' % (CT, V, F0, G0, V)), D(w, Au, 'sub32d', [f0cu, g0c, vcu], '( ( %s - %s ) - %s ) = ( ( %s - %s ) - %s )' % (F0, G0, V, F0, V, G0))],
            '( %s - %s ) = ( ( %s - %s ) - %s )' % (CT, V, F0, V, G0))
    t2 = D(w, Au, 'eqbrtrd', [D(w, Au, 'fveq2d', [d1], '( abs ` ( %s - %s ) ) = ( abs ` ( ( %s - %s ) - %s ) )' % (CT, V, F0, V, G0)),
                              D(w, Au, 'abs2dif2d', [D(w, Au, 'subcld', [f0cu, vcu], '( %s - %s ) e. CC' % (F0, V)), g0c], '( abs ` ( ( %s - %s ) - %s ) ) <_ ( %s + ( abs ` %s ) )' % (F0, V, G0, FV, G0))],
             '( abs ` ( %s - %s ) ) <_ ( %s + ( abs ` %s ) )' % (CT, V, FV, G0))
    fvr = D(w, Au, 'abscld', [D(w, Au, 'subcld', [f0cu, vcu], '( %s - %s ) e. CC' % (F0, V))], '%s e. RR' % FV)
    t3 = D(w, Au, 'letrd', [D(w, Au, 'abscld', [D(w, Au, 'subcld', [ctc, vcu], '( %s - %s ) e. CC' % (CT, V))], '( abs ` ( %s - %s ) ) e. RR' % (CT, V)),
                            D(w, Au, 'readdcld', [fvr, D(w, Au, 'abscld', [g0c], '( abs ` %s ) e. RR' % G0)], '( %s + ( abs ` %s ) ) e. RR' % (FV, G0)), D(w, Au, 'readdcld', [fvr, itr], '%s e. RR' % Bt), t2,
                            D(w, Au, 'leadd2dd', [D(w, Au, 'abscld', [g0c], '( abs ` %s ) e. RR' % G0), itr, fvr, gb], '( %s + ( abs ` %s ) ) <_ %s' % (FV, G0, Bt))], '( abs ` ( %s - %s ) ) <_ %s' % (CT, V, Bt))
    br = D(w, Au, 'readdcld', [fvr, itr], '%s e. RR' % Bt)
    b0 = D(w, Au, 'addge0d', [fvr, itr, D(w, Au, 'absge0d', [D(w, Au, 'subcld', [f0cu, vcu], '( %s - %s ) e. CC' % (F0, V))], '0 <_ %s' % FV), D(w, Au, 'rpge0d', [it], '0 <_ %s' % IT)], '0 <_ %s' % Bt)
    bb = D(w, Au, 'eqtr4d', [D(w, Au, 'fveq2d', [D(w, Au, 'subid1d', [D(w, Au, 'recnd', [br], '%s e. CC' % Bt)], '( %s - 0 ) = %s' % (Bt, Bt))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (Bt, Bt)),
                             D(w, Au, 'absidd', [br, b0], '( abs ` %s ) = %s' % (Bt, Bt))], '( abs ` ( %s - 0 ) ) = %s' % (Bt, Bt)) if False else         D(w, Au, 'eqtrd', [D(w, Au, 'fveq2d', [D(w, Au, 'subid1d', [D(w, Au, 'recnd', [br], '%s e. CC' % Bt)], '( %s - 0 ) = %s' % (Bt, Bt))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (Bt, Bt)),
                           D(w, Au, 'absidd', [br, b0], '( abs ` %s ) = %s' % (Bt, Bt))], '( abs ` ( %s - 0 ) ) = %s' % (Bt, Bt))
    t4 = D(w, Au, 'breqtrrd', [t3, bb], '( abs ` ( %s - %s ) ) <_ ( abs ` ( %s - 0 ) )' % (CT, V, Bt))
    ctc_t = D(w, At, 'itgcl', [gibl(w, At, '( 1 / t )', 't', D(w, At, 'rpred', [D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+')], '( 1 / t ) e. RR'), tr, 'W', 'L', wct, lct, prp=D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+')),
                               fx_cl(w, At, '( 1 / t )', 't', D(w, At, 'rpred', [D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+')], '( 1 / t ) e. RR'), 'W', 'L', wct, lct, None)], '%s e. CC' % CT)
    fin = D(w, A, 'rlimsqzlem', [cst(w, A, '1re', '1 e. RR'), vc, radd0, D(w, At, 'addcld', [fvc, itc], '%s e. CC' % Bt), ctc_t, t4], '( t e. RR+ |-> %s ) ~~>r %s' % (CT, V))
    w.qed([fin], 'idi', S['zl3ew1'])
    go(w)


J_ = '( TopOpen ` CCfld )'


def open_ioo(w, A, P, Q):
    """( A -> ( P (,) Q ) e. ( J |`t RR ) )"""
    T = '( %s |`t RR )' % J_
    return w.s([w.s([w.s([], 'iooretop', '( %s (,) %s ) e. ( topGen ` ran (,) )' % (P, Q)), w.s([w.s([], 'eqid', '%s = %s' % (J_, J_))], 'tgioo2', '( topGen ` ran (,) ) = %s' % T)],
                    'eleqtri', '( %s (,) %s ) e. %s' % (P, Q, T))], 'a1i', '( %s -> ( %s (,) %s ) e. %s )' % (A, P, Q, T))


if want('zl3dvl'):
    w = W('zl3dvl', 'The derivative of ` exp ( -u ( L x ) ) ` on ` [ P , Q ] ` ( ~ dvmptco , ~ dvef , ~ zl3dvi ).')
    A, Cc = ante_of('zl3dvl')
    lc = D(w, A, 'simpl', [], 'L e. CC'); pr = D(w, A, 'simprl', [], 'P e. RR'); qr = D(w, A, 'simprr', [], 'Q e. RR')
    rr = cst(w, A, 'reelprrecn', 'RR e. { RR , CC }'); ccs = cst(w, A, 'cnelprrecn', 'CC e. { RR , CC }')
    Ax = '( %s /\\ x e. RR )' % A
    xc = D(w, Ax, 'recnd', [w.s([], 'simpr', '( %s -> x e. RR )' % Ax)], 'x e. CC')
    one = D(w, Ax, '1cnd', [], '1 e. CC')
    d1 = D(w, A, 'dvmptid', [rr], '( RR _D ( x e. RR |-> x ) ) = ( x e. RR |-> 1 )')
    d2 = D(w, A, 'dvmptcmul', [rr, xc, one, d1, lc], '( RR _D ( x e. RR |-> ( L x. x ) ) ) = ( x e. RR |-> ( L x. 1 ) )')
    lxc = D(w, Ax, 'mulcld', [ad(w, Ax, lc, 'L e. CC'), xc], '( L x. x ) e. CC'); l1c = D(w, Ax, 'mulcld', [ad(w, Ax, lc, 'L e. CC'), one], '( L x. 1 ) e. CC')
    d3 = D(w, A, 'dvmptneg', [rr, lxc, l1c, d2], '( RR _D ( x e. RR |-> -u ( L x. x ) ) ) = ( x e. RR |-> -u ( L x. 1 ) )')
    Ay = '( %s /\\ y e. CC )' % A
    ey = D(w, Ay, 'efcld', [w.s([], 'simpr', '( %s -> y e. CC )' % Ay)], '( exp ` y ) e. CC')
    fm = D(w, A, 'feqmptd', [cst(w, A, 'eff', 'exp : CC --> CC')], 'exp = ( y e. CC |-> ( exp ` y ) )')
    dexp = D(w, A, 'eqtr3d', [D(w, A, 'oveq2d', [fm], '( CC _D exp ) = ( CC _D ( y e. CC |-> ( exp ` y ) ) )'), D(w, A, 'eqtrd', [cst(w, A, 'dvef', '( CC _D exp ) = exp'), fm], '( CC _D exp ) = ( y e. CC |-> ( exp ` y ) )')],
             '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( y e. CC |-> ( exp ` y ) )')
    NL = '-u ( L x. x )'; EX = '( exp ` %s )' % NL
    e_ = w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = %s )' % (NL, EX))
    d4 = D(w, A, 'dvmptco', [rr, ccs, D(w, Ax, 'negcld', [lxc], '%s e. CC' % NL), D(w, Ax, 'negcld', [l1c], '-u ( L x. 1 ) e. CC'), ey, ey, d3, dexp, e_, e_],
           '( RR _D ( x e. RR |-> %s ) ) = ( x e. RR |-> ( %s x. -u ( L x. 1 ) ) )' % (EX, EX))
    X = '( P (,) Q )'; I = '( P [,] Q )'
    Axx = '( %s /\\ x e. RR )' % A
    exc = D(w, Axx, 'efcld', [D(w, Axx, 'negcld', [lxc], '%s e. CC' % NL)], '%s e. CC' % EX)
    bc = D(w, Axx, 'mulcld', [exc, D(w, Axx, 'negcld', [l1c], '-u ( L x. 1 ) e. CC')], '( %s x. -u ( L x. 1 ) ) e. CC' % EX)
    d5 = D(w, A, 'dvmptres', [rr, exc, bc, d4, cst(w, A, 'ioossre', '%s C_ RR' % X), w.s([], 'eqid', '( %s |`t RR ) = ( %s |`t RR )' % (J_, J_)), w.s([], 'eqid', '%s = %s' % (J_, J_)), open_ioo(w, A, 'P', 'Q')],
           '( RR _D ( x e. %s |-> %s ) ) = ( x e. %s |-> ( %s x. -u ( L x. 1 ) ) )' % (X, EX, X, EX))
    G = '( x e. %s |-> %s )' % (I, EX)
    Ai = '( %s /\\ x e. %s )' % (A, I)
    xi = D(w, Ai, 'sseldd', [D(w, Ai, 'syl2anc', [ad(w, Ai, pr, 'P e. RR'), ad(w, Ai, qr, 'Q e. RR'), w.inst('iccssre')], '%s C_ RR' % I), w.s([], 'simpr', '( %s -> x e. %s )' % (Ai, I))], 'x e. RR')
    gv = D(w, Ai, 'efcld', [D(w, Ai, 'negcld', [D(w, Ai, 'mulcld', [ad(w, Ai, lc, 'L e. CC'), D(w, Ai, 'recnd', [xi], 'x e. CC')], '( L x. x ) e. CC')], '%s e. CC' % NL)], '%s e. CC' % EX)
    gf = D(w, A, 'fmptd', [gv, eq_(w, G)], '%s : %s --> CC' % (G, I))
    dvi = D(w, A, 'syl2anc', [D(w, A, 'jca', [pr, qr], '( P e. RR /\\ Q e. RR )'), gf, w.inst('zl3dvi')], '( RR _D %s ) = ( RR _D ( %s |` %s ) )' % (G, G, X))
    rs = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = ( x e. %s |-> %s )' % (G, X, X, EX))], 'a1i', '( %s -> ( %s |` %s ) = ( x e. %s |-> %s ) )' % (A, G, X, X, EX))
    Ao = '( %s /\\ x e. %s )' % (A, X)
    xo = D(w, Ao, 'recnd', [D(w, Ao, 'sseldd', [cst(w, Ao, 'ioossre', '%s C_ RR' % X), w.s([], 'simpr', '( %s -> x e. %s )' % (Ao, X))], 'x e. RR')], 'x e. CC')
    lco = ad(w, Ao, lc, 'L e. CC')
    exo = D(w, Ao, 'efcld', [D(w, Ao, 'negcld', [D(w, Ao, 'mulcld', [lco, xo], '( L x. x ) e. CC')], '%s e. CC' % NL)], '%s e. CC' % EX)
    sim = chain(w, Ao, ['( %s x. -u ( L x. 1 ) )' % EX, '( %s x. -u L )' % EX, '( -u L x. %s )' % EX],
                [D(w, Ao, 'oveq2d', [D(w, Ao, 'negeqd', [D(w, Ao, 'mulridd', [lco], '( L x. 1 ) = L')], '-u ( L x. 1 ) = -u L')], '( %s x. -u ( L x. 1 ) ) = ( %s x. -u L )' % (EX, EX)),
                 D(w, Ao, 'mulcomd', [exo, D(w, Ao, 'negcld', [lco], '-u L e. CC')], '( %s x. -u L ) = ( -u L x. %s )' % (EX, EX))])
    m = D(w, A, 'mpteq2dva', [sim], '( x e. %s |-> ( %s x. -u ( L x. 1 ) ) ) = ( x e. %s |-> ( -u L x. %s ) )' % (X, EX, X, EX))
    fin = chain(w, A, ['( RR _D %s )' % G, '( RR _D ( %s |` %s ) )' % (G, X), '( RR _D ( x e. %s |-> %s ) )' % (X, EX), '( x e. %s |-> ( %s x. -u ( L x. 1 ) ) )' % (X, EX), '( x e. %s |-> ( -u L x. %s ) )' % (X, EX)],
                [dvi, D(w, A, 'oveq2d', [rs], '( RR _D ( %s |` %s ) ) = ( RR _D ( x e. %s |-> %s ) )' % (G, X, X, EX)), d5, m])
    w.qed([fin], 'idi', S['zl3dvl'])
    go(w)


if want('zl3dvw'):
    w = W('zl3dvw', 'The derivative of ` x ^c W / W ` on ` [ P , Q ] ` , ` 0 < P ` ( ~ dvcxp1 , ~ dvmptres , ~ zl3dvi ).')
    A, Cc = ante_of('zl3dvw')
    wc = D(w, A, 'simpll', [], 'W e. CC'); wn = D(w, A, 'simplr', [], 'W =/= 0'); prp = D(w, A, 'simprl', [], 'P e. RR+'); qr = D(w, A, 'simprr', [], 'Q e. RR')
    pr = D(w, A, 'rpred', [prp], 'P e. RR')
    I = '( P [,] Q )'; X = '( P (,) Q )'
    G = '( x e. %s |-> ( ( x ^c W ) / W ) )' % I
    Ai = '( %s /\\ x e. %s )' % (A, I)
    Ap = '( %s /\\ x e. RR+ )' % A
    ss2 = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [D(w, A, 'rexrd', [D(w, A, 'rpge0d' if False else 'rpred', [prp], 'P e. RR')], 'P e. RR*') if False else cst(w, A, '0xr', '0 e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*'),
                                                   D(w, A, 'rpge0d', [prp], '0 <_ P'), D(w, A, 'pnfged', [D(w, A, 'rexrd', [qr], 'Q e. RR*')], 'Q <_ +oo'), w.inst('ioossioo')], '') if False else
                             D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '0xr', '0 e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*')], '( 0 e. RR* /\\ +oo e. RR* )'),
                                                 D(w, A, 'jca', [D(w, A, 'rpge0d', [prp], '0 <_ P'), D(w, A, 'pnfged', [D(w, A, 'rexrd', [qr], 'Q e. RR*')], 'Q <_ +oo')], '( 0 <_ P /\\ Q <_ +oo )'), w.inst('ioossioo')],
                               '%s C_ ( 0 (,) +oo )' % X), cst(w, A, 'ioorp', '( 0 (,) +oo ) = RR+') if False else w.s([w.s([], 'ioorp', '( 0 (,) +oo ) = RR+')], 'eqimssi', '( 0 (,) +oo ) C_ RR+') and
                            w.s([w.s([w.s([], 'ioorp', '( 0 (,) +oo ) = RR+')], 'eqimssi', '( 0 (,) +oo ) C_ RR+')], 'a1i', '( %s -> ( 0 (,) +oo ) C_ RR+ )' % A)], '%s C_ RR+' % X)
    xpc = D(w, Ap, 'rpcnd', [w.s([], 'simpr', '( %s -> x e. RR+ )' % Ap)], 'x e. CC'); wcp = ad(w, Ap, wc, 'W e. CC')
    WM = '( W - 1 )'
    d0 = D(w, A, 'syl', [wc, w.inst('dvcxp1')], '( RR _D ( x e. RR+ |-> ( x ^c W ) ) ) = ( x e. RR+ |-> ( W x. ( x ^c %s ) ) )' % WM)
    wm1 = D(w, Ap, 'subcld', [wcp, cst(w, Ap, 'ax-1cn', '1 e. CC')], '%s e. CC' % WM)
    bb = D(w, Ap, 'mulcld', [wcp, D(w, Ap, 'cxpcld', [xpc, wm1], '( x ^c %s ) e. CC' % WM)], '( W x. ( x ^c %s ) ) e. CC' % WM)
    S_ = cst(w, A, 'reelprrecn', 'RR e. { RR , CC }')
    d1 = D(w, A, 'dvmptdivc', [S_, D(w, Ap, 'cxpcld', [xpc, wcp], '( x ^c W ) e. CC'), bb, d0, wc, wn], '( RR _D ( x e. RR+ |-> ( ( x ^c W ) / W ) ) ) = ( x e. RR+ |-> ( ( W x. ( x ^c %s ) ) / W ) )' % WM)
    GO = '( x e. %s |-> ( ( x ^c W ) / W ) )' % X
    bdiv = D(w, Ap, 'divcld', [bb, wcp, ad(w, Ap, wn, 'W =/= 0')], '( ( W x. ( x ^c %s ) ) / W ) e. CC' % WM)
    d2 = D(w, A, 'dvmptres', [S_, D(w, Ap, 'divcld', [D(w, Ap, 'cxpcld', [xpc, wcp], '( x ^c W ) e. CC'), wcp, ad(w, Ap, wn, 'W =/= 0')], '( ( x ^c W ) / W ) e. CC'), bdiv, d1, ss2,
                               w.s([], 'eqid', '( %s |`t RR ) = ( %s |`t RR )' % (J_, J_)), w.s([], 'eqid', '%s = %s' % (J_, J_)), open_ioo(w, A, 'P', 'Q')],
           '( RR _D %s ) = ( x e. %s |-> ( ( W x. ( x ^c %s ) ) / W ) )' % (GO, X, WM))
    xi = D(w, Ai, 'sseldd', [D(w, Ai, 'syl2anc', [ad(w, Ai, pr, 'P e. RR'), ad(w, Ai, qr, 'Q e. RR'), w.inst('iccssre')], '%s C_ RR' % I), w.s([], 'simpr', '( %s -> x e. %s )' % (Ai, I))], 'x e. RR')
    gv = D(w, Ai, 'divcld', [D(w, Ai, 'cxpcld', [D(w, Ai, 'recnd', [xi], 'x e. CC'), ad(w, Ai, wc, 'W e. CC')], '( x ^c W ) e. CC'), ad(w, Ai, wc, 'W e. CC'), ad(w, Ai, wn, 'W =/= 0')], '( ( x ^c W ) / W ) e. CC')
    gf = D(w, A, 'fmptd', [gv, eq_(w, G)], '%s : %s --> CC' % (G, I))
    dvi = D(w, A, 'syl2anc', [D(w, A, 'jca', [pr, qr], '( P e. RR /\\ Q e. RR )'), gf, w.inst('zl3dvi')], '( RR _D %s ) = ( RR _D ( %s |` %s ) )' % (G, G, X))
    rs = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (G, X, GO))], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A, G, X, GO))
    Aq = '( %s /\\ x e. %s )' % (A, X)
    xq = D(w, Aq, 'rpcnd', [D(w, Aq, 'sseldd', [ad(w, Aq, ss2, '%s C_ RR+' % X), w.s([], 'simpr', '( %s -> x e. %s )' % (Aq, X))], 'x e. RR+')], 'x e. CC')
    wq = ad(w, Aq, wc, 'W e. CC')
    sim = D(w, Aq, 'divcan3d', [D(w, Aq, 'cxpcld', [xq, D(w, Aq, 'subcld', [wq, cst(w, Aq, 'ax-1cn', '1 e. CC')], '%s e. CC' % WM)], '( x ^c %s ) e. CC' % WM), wq, ad(w, Aq, wn, 'W =/= 0')],
            '( ( W x. ( x ^c %s ) ) / W ) = ( x ^c %s )' % (WM, WM))
    m = D(w, A, 'mpteq2dva', [sim], '( x e. %s |-> ( ( W x. ( x ^c %s ) ) / W ) ) = ( x e. %s |-> ( x ^c %s ) )' % (X, WM, X, WM))
    fin = chain(w, A, ['( RR _D %s )' % G, '( RR _D ( %s |` %s ) )' % (G, X), '( RR _D %s )' % GO, '( x e. %s |-> ( ( W x. ( x ^c %s ) ) / W ) )' % (X, WM), '( x e. %s |-> ( x ^c %s ) )' % (X, WM)],
                [dvi, D(w, A, 'oveq2d', [rs], '( RR _D ( %s |` %s ) ) = ( RR _D %s )' % (G, X, GO)), d2, m])
    w.qed([fin], 'idi', S['zl3dvw'])
    go(w)


def wfacts(w, A):
    """from A = WA: W e. CC, 0 < Re W, L e. RR+, W =/= 0, abs W e. RR+"""
    wc = D(w, A, 'simpll', [], 'W e. CC'); w0 = D(w, A, 'simplr', [], '0 < ( Re ` W )'); lrp = D(w, A, 'simpr', [], 'L e. RR+')
    wne = D(w, A, 'neeq1d' if False else 'syl', [], '') if False else None
    rwr = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    wne = D(w, A, 'mpbird' if False else 'necon3bid' if False else 'idi', [], '') if False else None
    # W =/= 0 since Re W =/= 0
    rne = D(w, A, 'gt0ne0d', [w0], '( Re ` W ) =/= 0')
    wne = D(w, A, 'mtbird' if False else 'syl', [], '') if False else None
    wn0 = w.s([w.s([rne, w.s([w.s([w.s([], 'fveq2', '( W = 0 -> ( Re ` W ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( W = 0 -> ( Re ` W ) = 0 )')], 'a1i',
                                                   '( %s -> ( W = 0 -> ( Re ` W ) = 0 ) )' % A)], 'necon3ad' if False else 'necon3d', '( %s -> ( ( Re ` W ) =/= 0 -> W =/= 0 ) )' % A)], 'idi', '') if False else None
    wn0 = D(w, A, 'mpd', [rne, D(w, A, 'necon3d', [w.s([w.s([w.s([], 'fveq2', '( W = 0 -> ( Re ` W ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( W = 0 -> ( Re ` W ) = 0 )')], 'a1i',
                                                               '( %s -> ( W = 0 -> ( Re ` W ) = 0 ) )' % A)], '( ( Re ` W ) =/= 0 -> W =/= 0 )')], 'W =/= 0')
    awp = D(w, A, 'absrpcld', [wc, wn0], '( abs ` W ) e. RR+')
    return wc, w0, lrp, rwr, wn0, awp


if want('zl3wtf'):
    w = W('zl3wtf', 'The upper boundary term of the integration by parts vanishes: ` e ^ -Lt t ^ W / W -> 0 ` ( ~ zl3pxe ).')
    A, Cc = ante_of('zl3wtf')
    wc, w0, lrp, rwr, wn0, awp = wfacts(w, A)
    RS = '( Re ` W )'; R1 = '( %s + 1 )' % RS
    PSI = 'A. y e. ( 1 [,) +oo ) ( exp ` ( %s x. ( log ` y ) ) ) <_ ( c x. ( exp ` ( L x. y ) ) )' % R1
    ex = D(w, A, 'syl2anc', [D(w, A, 'readdcld', [rwr, cst(w, A, '1re', '1 e. RR')], '%s e. RR' % R1), lrp, w.inst('zl3pxe')], 'E. c e. RR+ %s' % PSI)
    Ac = '( ( %s /\\ c e. RR+ ) /\\ %s )' % (A, PSI)
    crp = w.s([], 'simplr', '( %s -> c e. RR+ )' % Ac); psi = w.s([], 'simpr', '( %s -> %s )' % (Ac, PSI))
    up = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Ac, f))
    K = '( c / ( abs ` W ) )'
    krp = D(w, Ac, 'rpdivcld', [crp, up(awp, '( abs ` W ) e. RR+')], '%s e. RR+' % K)
    Ft = '( ( exp ` -u ( L x. t ) ) x. ( ( t ^c W ) / W ) )'
    Act = '( %s /\\ t e. RR+ )' % Ac
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % Act)
    tc = D(w, Act, 'rpcnd', [trp], 't e. CC')
    ft_c = D(w, Act, 'mulcld', [D(w, Act, 'efcld', [D(w, Act, 'negcld', [D(w, Act, 'mulcld', [D(w, Act, 'rpcnd', [ad(w, Act, up(lrp, 'L e. RR+'), 'L e. RR+')], 'L e. CC'), tc], '( L x. t ) e. CC')], '-u ( L x. t ) e. CC')],
                                               '( exp ` -u ( L x. t ) ) e. CC'),
                                 D(w, Act, 'divcld', [D(w, Act, 'cxpcld', [tc, ad(w, Act, up(wc, 'W e. CC'), 'W e. CC')], '( t ^c W ) e. CC'), ad(w, Act, up(wc, 'W e. CC'), 'W e. CC'), ad(w, Act, up(wn0, 'W =/= 0'), 'W =/= 0')],
                                   '( ( t ^c W ) / W ) e. CC')], '%s e. CC' % Ft)
    kt = D(w, Act, 'rpcnd', [D(w, Act, 'rpdivcld', [ad(w, Act, krp, '%s e. RR+' % K), trp], '( %s / t ) e. RR+' % K)], '( %s / t ) e. CC' % K)
    # the bound for t >_ 1
    Au = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % Ac
    trpu = w.s([], 'simprl', '( %s -> t e. RR+ )' % Au); t1 = w.s([], 'simprr', '( %s -> 1 <_ t )' % Au)
    tru = D(w, Au, 'rpred', [trpu], 't e. RR'); tcu = D(w, Au, 'rpcnd', [trpu], 't e. CC')
    uu = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Au, f))
    ti = D(w, Au, 'mpbir2and', [tru, t1, D(w, Au, 'syl', [cst(w, Au, '1re', '1 e. RR'), w.inst('elicopnf')], '( t e. ( 1 [,) +oo ) <-> ( t e. RR /\\ 1 <_ t ) )')], 't e. ( 1 [,) +oo )')
    sub = w.s([w.s([w.s([w.s([], 'fveq2', '( y = t -> ( log ` y ) = ( log ` t ) )')], 'oveq2d', '( y = t -> ( %s x. ( log ` y ) ) = ( %s x. ( log ` t ) ) )' % (R1, R1))], 'fveq2d',
                   '( y = t -> ( exp ` ( %s x. ( log ` y ) ) ) = ( exp ` ( %s x. ( log ` t ) ) ) )' % (R1, R1)),
               w.s([w.s([w.s([], 'oveq2', '( y = t -> ( L x. y ) = ( L x. t ) )')], 'fveq2d', '( y = t -> ( exp ` ( L x. y ) ) = ( exp ` ( L x. t ) ) )')], 'oveq2d',
                   '( y = t -> ( c x. ( exp ` ( L x. y ) ) ) = ( c x. ( exp ` ( L x. t ) ) ) )')], 'breq12d',
              '( y = t -> ( ( exp ` ( %s x. ( log ` y ) ) ) <_ ( c x. ( exp ` ( L x. y ) ) ) <-> ( exp ` ( %s x. ( log ` t ) ) ) <_ ( c x. ( exp ` ( L x. t ) ) ) ) )' % (R1, R1))
    pt = D(w, Au, 'rspcdva', [sub, uu(psi, PSI), ti], '( exp ` ( %s x. ( log ` t ) ) ) <_ ( c x. ( exp ` ( L x. t ) ) )' % R1)
    LT = '( log ` t )'
    ltr = D(w, Au, 'relogcld', [trpu], '%s e. RR' % LT)
    rwu = uu(up(rwr, '%s e. RR' % RS), '%s e. RR' % RS)
    TS = '( t ^c %s )' % RS
    ex1 = chain(w, Au, ['( exp ` ( %s x. %s ) )' % (R1, LT), '( exp ` ( ( %s x. %s ) + ( 1 x. %s ) ) )' % (RS, LT, LT), '( exp ` ( ( %s x. %s ) + %s ) )' % (RS, LT, LT),
                        '( ( exp ` ( %s x. %s ) ) x. ( exp ` %s ) )' % (RS, LT, LT), '( %s x. t )' % TS],
                [D(w, Au, 'fveq2d', [D(w, Au, 'adddird', [D(w, Au, 'recnd', [rwu], '%s e. CC' % RS), cst(w, Au, 'ax-1cn', '1 e. CC'), D(w, Au, 'recnd', [ltr], '%s e. CC' % LT)],
                                       '( %s x. %s ) = ( ( %s x. %s ) + ( 1 x. %s ) )' % (R1, LT, RS, LT, LT))], '( exp ` ( %s x. %s ) ) = ( exp ` ( ( %s x. %s ) + ( 1 x. %s ) ) )' % (R1, LT, RS, LT, LT)),
                 D(w, Au, 'fveq2d', [D(w, Au, 'oveq2d', [D(w, Au, 'mullidd', [D(w, Au, 'recnd', [ltr], '%s e. CC' % LT)], '( 1 x. %s ) = %s' % (LT, LT))], '( ( %s x. %s ) + ( 1 x. %s ) ) = ( ( %s x. %s ) + %s )' % (RS, LT, LT, RS, LT, LT))],
                   '( exp ` ( ( %s x. %s ) + ( 1 x. %s ) ) ) = ( exp ` ( ( %s x. %s ) + %s ) )' % (RS, LT, LT, RS, LT, LT)),
                 efadd_(w, Au, '( %s x. %s )' % (RS, LT), LT, D(w, Au, 'recnd', [D(w, Au, 'remulcld', [rwu, ltr], '( %s x. %s ) e. RR' % (RS, LT))], '( %s x. %s ) e. CC' % (RS, LT)), D(w, Au, 'recnd', [ltr], '%s e. CC' % LT)),
                 D(w, Au, 'oveq12d', [D(w, Au, 'eqcomd', [D(w, Au, 'syl3anc', [tcu, D(w, Au, 'rpne0d', [trpu], 't =/= 0'), D(w, Au, 'recnd', [rwu], '%s e. CC' % RS), w.inst('cxpef')], '%s = ( exp ` ( %s x. %s ) )' % (TS, RS, LT))],
                                                          '( exp ` ( %s x. %s ) ) = %s' % (RS, LT, TS)), D(w, Au, 'syl', [trpu, w.inst('reeflog')], '( exp ` %s ) = t' % LT)],
                   '( ( exp ` ( %s x. %s ) ) x. ( exp ` %s ) ) = ( %s x. t )' % (RS, LT, LT, TS))])
    ELT = '( exp ` ( L x. t ) )'
    lt_ = D(w, Au, 'remulcld', [D(w, Au, 'rpred', [uu(up(lrp, 'L e. RR+'), 'L e. RR+')], 'L e. RR'), tru], '( L x. t ) e. RR')
    elp = D(w, Au, 'rpefcld', [lt_], '%s e. RR+' % ELT)
    tsr = D(w, Au, 'rpred', [D(w, Au, 'rpcxpcld', [trpu, rwu], '%s e. RR+' % TS)], '%s e. RR' % TS)
    b1 = D(w, Au, 'eqbrtrrd', [ex1, pt], '( %s x. t ) <_ ( c x. %s )' % (TS, ELT))
    cr_ = D(w, Au, 'rpred', [uu(crp, 'c e. RR+')], 'c e. RR')
    b2 = D(w, Au, 'mpbid', [D(w, Au, 'breqtrd', [b1, D(w, Au, 'mulcomd', [D(w, Au, 'recnd', [cr_], 'c e. CC'), D(w, Au, 'rpcnd', [elp], '%s e. CC' % ELT)], '( c x. %s ) = ( %s x. c )' % (ELT, ELT))],
                                 '( %s x. t ) <_ ( %s x. c )' % (TS, ELT)),
                            D(w, Au, 'ledivmuld' if False else 'bitr4d' if False else 'ledivmul2d' if False else 'syl', [], '') if False else
                            D(w, Au, 'bicomd', [D(w, Au, 'ledivmuld', [D(w, Au, 'remulcld', [tsr, tru], '( %s x. t ) e. RR' % TS), cr_, elp], '( ( ( %s x. t ) / %s ) <_ c <-> ( %s x. t ) <_ ( %s x. c ) )' % (TS, ELT, TS, ELT))],
                              '( ( %s x. t ) <_ ( %s x. c ) <-> ( ( %s x. t ) / %s ) <_ c )' % (TS, ELT, TS, ELT))], '( ( %s x. t ) / %s ) <_ c' % (TS, ELT))
    # ( TS / ELT ) <_ c / t
    b3 = D(w, Au, 'mpbid', [D(w, Au, 'eqbrtrrd', [D(w, Au, 'div23d', [D(w, Au, 'recnd', [tsr], '%s e. CC' % TS), tcu, D(w, Au, 'rpcnd', [elp], '%s e. CC' % ELT), D(w, Au, 'rpne0d', [elp], '%s =/= 0' % ELT)],
                                                                   '( ( %s x. t ) / %s ) = ( ( %s / %s ) x. t )' % (TS, ELT, TS, ELT)), b2], '( ( %s / %s ) x. t ) <_ c' % (TS, ELT)),
                            D(w, Au, 'lemuldivd', [D(w, Au, 'redivcld', [tsr, D(w, Au, 'rpred', [elp], '%s e. RR' % ELT), D(w, Au, 'rpne0d', [elp], '%s =/= 0' % ELT)], '( %s / %s ) e. RR' % (TS, ELT)), cr_, trpu],
                              '( ( ( %s / %s ) x. t ) <_ c <-> ( %s / %s ) <_ ( c / t ) )' % (TS, ELT, TS, ELT))], '( %s / %s ) <_ ( c / t )' % (TS, ELT))
    # | F ( t ) | = ( TS / ELT ) / | W |
    lcu = D(w, Au, 'rpcnd', [uu(up(lrp, 'L e. RR+'), 'L e. RR+')], 'L e. CC')
    e1 = D(w, Au, 'syl', [D(w, Au, 'mulcld', [lcu, tcu], '( L x. t ) e. CC'), w.inst('efneg')], '( exp ` -u ( L x. t ) ) = ( 1 / %s )' % ELT)
    wcu, wnu, awu = uu(up(wc, 'W e. CC'), 'W e. CC'), uu(up(wn0, 'W =/= 0'), 'W =/= 0'), uu(up(awp, '( abs ` W ) e. RR+'), '( abs ` W ) e. RR+')
    tw = D(w, Au, 'cxpcld', [tcu, wcu], '( t ^c W ) e. CC')
    af = chain(w, Au, ['( abs ` %s )' % Ft, '( ( abs ` ( exp ` -u ( L x. t ) ) ) x. ( abs ` ( ( t ^c W ) / W ) ) )', '( ( abs ` ( 1 / %s ) ) x. ( ( abs ` ( t ^c W ) ) / ( abs ` W ) ) )' % ELT,
                       '( ( 1 / %s ) x. ( %s / ( abs ` W ) ) )' % (ELT, TS), '( ( 1 x. %s ) / ( %s x. ( abs ` W ) ) )' % (TS, ELT), '( %s / ( %s x. ( abs ` W ) ) )' % (TS, ELT), '( ( %s / %s ) / ( abs ` W ) )' % (TS, ELT)],
               [D(w, Au, 'absmuld', [D(w, Au, 'efcld', [D(w, Au, 'negcld', [D(w, Au, 'mulcld', [lcu, tcu], '( L x. t ) e. CC')], '-u ( L x. t ) e. CC')], '( exp ` -u ( L x. t ) ) e. CC'),
                                     D(w, Au, 'divcld', [tw, wcu, wnu], '( ( t ^c W ) / W ) e. CC')], '( abs ` %s ) = ( ( abs ` ( exp ` -u ( L x. t ) ) ) x. ( abs ` ( ( t ^c W ) / W ) ) )' % Ft),
                D(w, Au, 'oveq12d', [D(w, Au, 'fveq2d', [e1], '( abs ` ( exp ` -u ( L x. t ) ) ) = ( abs ` ( 1 / %s ) )' % ELT), D(w, Au, 'absdivd', [tw, wcu, wnu], '( abs ` ( ( t ^c W ) / W ) ) = ( ( abs ` ( t ^c W ) ) / ( abs ` W ) )')],
                  '( ( abs ` ( exp ` -u ( L x. t ) ) ) x. ( abs ` ( ( t ^c W ) / W ) ) ) = ( ( abs ` ( 1 / %s ) ) x. ( ( abs ` ( t ^c W ) ) / ( abs ` W ) ) )' % ELT),
                D(w, Au, 'oveq12d', [D(w, Au, 'absidd', [D(w, Au, 'rpred', [D(w, Au, 'rpreccld', [elp], '( 1 / %s ) e. RR+' % ELT)], '( 1 / %s ) e. RR' % ELT), D(w, Au, 'rpge0d', [D(w, Au, 'rpreccld', [elp], '( 1 / %s ) e. RR+' % ELT)], '0 <_ ( 1 / %s )' % ELT)],
                                       '( abs ` ( 1 / %s ) ) = ( 1 / %s )' % (ELT, ELT)),
                                     D(w, Au, 'oveq1d', [D(w, Au, 'syl2anc', [trpu, wcu, w.inst('abscxp')], '( abs ` ( t ^c W ) ) = %s' % TS)], '( ( abs ` ( t ^c W ) ) / ( abs ` W ) ) = ( %s / ( abs ` W ) )' % TS)],
                  '( ( abs ` ( 1 / %s ) ) x. ( ( abs ` ( t ^c W ) ) / ( abs ` W ) ) ) = ( ( 1 / %s ) x. ( %s / ( abs ` W ) ) )' % (ELT, ELT, TS)),
                D(w, Au, 'divmuldivd', [cst(w, Au, 'ax-1cn', '1 e. CC'), D(w, Au, 'rpcnd', [elp], '%s e. CC' % ELT), D(w, Au, 'recnd', [tsr], '%s e. CC' % TS), D(w, Au, 'rpcnd', [awu], '( abs ` W ) e. CC'),
                                        D(w, Au, 'rpne0d', [elp], '%s =/= 0' % ELT), D(w, Au, 'rpne0d', [awu], '( abs ` W ) =/= 0')],
                  '( ( 1 / %s ) x. ( %s / ( abs ` W ) ) ) = ( ( 1 x. %s ) / ( %s x. ( abs ` W ) ) )' % (ELT, TS, TS, ELT)),
                D(w, Au, 'oveq1d', [D(w, Au, 'mullidd', [D(w, Au, 'recnd', [tsr], '%s e. CC' % TS)], '( 1 x. %s ) = %s' % (TS, TS))], '( ( 1 x. %s ) / ( %s x. ( abs ` W ) ) ) = ( %s / ( %s x. ( abs ` W ) ) )' % (TS, ELT, TS, ELT)),
                D(w, Au, 'eqcomd', [D(w, Au, 'divdiv1d', [D(w, Au, 'recnd', [tsr], '%s e. CC' % TS), D(w, Au, 'rpcnd', [elp], '%s e. CC' % ELT), D(w, Au, 'rpne0d', [elp], '%s =/= 0' % ELT),
                                                          D(w, Au, 'rpcnd', [awu], '( abs ` W ) e. CC'), D(w, Au, 'rpne0d', [awu], '( abs ` W ) =/= 0')], '( ( %s / %s ) / ( abs ` W ) ) = ( %s / ( %s x. ( abs ` W ) ) )' % (TS, ELT, TS, ELT))],
                  '( %s / ( %s x. ( abs ` W ) ) ) = ( ( %s / %s ) / ( abs ` W ) )' % (TS, ELT, TS, ELT))])
    tdr = D(w, Au, 'redivcld', [tsr, D(w, Au, 'rpred', [elp], '%s e. RR' % ELT), D(w, Au, 'rpne0d', [elp], '%s =/= 0' % ELT)], '( %s / %s ) e. RR' % (TS, ELT))
    ctr = D(w, Au, 'rpred', [D(w, Au, 'rpdivcld', [uu(crp, 'c e. RR+'), trpu], '( c / t ) e. RR+')], '( c / t ) e. RR')
    b4 = D(w, Au, 'mpbid', [b3, D(w, Au, 'lediv1d', [tdr, ctr, awu], '( ( %s / %s ) <_ ( c / t ) <-> ( ( %s / %s ) / ( abs ` W ) ) <_ ( ( c / t ) / ( abs ` W ) ) )' % (TS, ELT, TS, ELT))],
            '( ( %s / %s ) / ( abs ` W ) ) <_ ( ( c / t ) / ( abs ` W ) )' % (TS, ELT))
    kk = D(w, Au, 'divdiv32d', [D(w, Au, 'recnd', [cr_], 'c e. CC'), tcu, D(w, Au, 'rpcnd', [awu], '( abs ` W ) e. CC'), D(w, Au, 'rpne0d', [trpu], 't =/= 0'), D(w, Au, 'rpne0d', [awu], '( abs ` W ) =/= 0')],
            '( ( c / t ) / ( abs ` W ) ) = ( %s / t )' % K)
    kpos = D(w, Au, 'rpdivcld', [uu(krp, '%s e. RR+' % K), trpu], '( %s / t ) e. RR+' % K)
    bnd = D(w, Au, 'breqtrd', [D(w, Au, 'eqbrtrd', [af, b4], '( abs ` %s ) <_ ( ( c / t ) / ( abs ` W ) )' % Ft), kk], '( abs ` %s ) <_ ( %s / t )' % (Ft, K))
    ftc_u = D(w, Au, 'mulcld', [D(w, Au, 'efcld', [D(w, Au, 'negcld', [D(w, Au, 'mulcld', [lcu, tcu], '( L x. t ) e. CC')], '-u ( L x. t ) e. CC')], '( exp ` -u ( L x. t ) ) e. CC'), D(w, Au, 'divcld', [tw, wcu, wnu], '( ( t ^c W ) / W ) e. CC')], '%s e. CC' % Ft)
    lhs = D(w, Au, 'fveq2d', [D(w, Au, 'subid1d', [ftc_u], '( %s - 0 ) = %s' % (Ft, Ft))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (Ft, Ft))
    rhs = D(w, Au, 'eqtrd', [D(w, Au, 'fveq2d', [D(w, Au, 'subid1d', [D(w, Au, 'rpcnd', [kpos], '( %s / t ) e. CC' % K)], '( ( %s / t ) - 0 ) = ( %s / t )' % (K, K))], '( abs ` ( ( %s / t ) - 0 ) ) = ( abs ` ( %s / t ) )' % (K, K)),
                             D(w, Au, 'absidd', [D(w, Au, 'rpred', [kpos], '( %s / t ) e. RR' % K), D(w, Au, 'rpge0d', [kpos], '0 <_ ( %s / t )' % K)], '( abs ` ( %s / t ) ) = ( %s / t )' % (K, K))],
              '( abs ` ( ( %s / t ) - 0 ) ) = ( %s / t )' % (K, K))
    fb = D(w, Au, 'breqtrrd', [D(w, Au, 'eqbrtrd', [lhs, bnd], '( abs ` ( %s - 0 ) ) <_ ( %s / t )' % (Ft, K)), rhs], '( abs ` ( %s - 0 ) ) <_ ( abs ` ( ( %s / t ) - 0 ) )' % (Ft, K))
    kr_ = D(w, Ac, 'syl', [D(w, Ac, 'rpcnd', [krp], '%s e. CC' % K), w.inst('divrcnv')], '( t e. RR+ |-> ( %s / t ) ) ~~>r 0' % K)
    sq = D(w, Ac, 'rlimsqzlem', [cst(w, Ac, '1re', '1 e. RR'), D(w, Ac, '0cnd', [], '0 e. CC'), kr_, kt, ft_c, fb], '( t e. RR+ |-> %s ) ~~>r 0' % Ft)
    r = D(w, A, 'rexlimdva', [D(w, '( %s /\\ c e. RR+ )' % A, 'ex', [sq], '( %s -> ( t e. RR+ |-> %s ) ~~>r 0 )' % (PSI, Ft))], '( E. c e. RR+ %s -> ( t e. RR+ |-> %s ) ~~>r 0 )' % (PSI, Ft))
    w.qed([ex, r], 'mpd', S['zl3wtf'])
    go(w)


if want('zl3wte'):
    w = W('zl3wte', 'The lower boundary term of the integration by parts vanishes: ` e ^ ( -L / t ) ( 1 / t ) ^ W / W -> 0 ` ( ~ cxplim ).')
    A, Cc = ante_of('zl3wte')
    wc, w0, lrp, rwr, wn0, awp = wfacts(w, A)
    RS = '( Re ` W )'
    rsp = D(w, A, 'elrpd', [rwr, w0], '%s e. RR+' % RS)
    IW = '( 1 / ( abs ` W ) )'
    iwc = D(w, A, 'rpcnd', [D(w, A, 'rpreccld', [awp], '%s e. RR+' % IW)], '%s e. CC' % IW)
    Bt = '( ( 1 / ( t ^c %s ) ) x. %s )' % (RS, IW)
    cl_ = D(w, A, 'syl', [rsp, w.inst('cxplim')], '( t e. RR+ |-> ( 1 / ( t ^c %s ) ) ) ~~>r 0' % RS)
    At = '( %s /\\ t e. RR+ )' % A
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    tsp = D(w, At, 'rpcxpcld', [trp, ad(w, At, rwr, '%s e. RR' % RS)], '( t ^c %s ) e. RR+' % RS)
    itp = D(w, At, 'rpreccld', [tsp], '( 1 / ( t ^c %s ) ) e. RR+' % RS)
    bm = D(w, A, 'rlimmul', [D(w, At, 'rpcnd', [itp], '( 1 / ( t ^c %s ) ) e. CC' % RS), ad(w, At, iwc, '%s e. CC' % IW), cl_, D(w, A, 'syl2anc', [cst(w, A, 'rpssre', 'RR+ C_ RR'), iwc, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (IW, IW))],
           '( t e. RR+ |-> %s ) ~~>r ( 0 x. %s )' % (Bt, IW))
    b0 = D(w, A, 'breqtrd', [bm, D(w, A, 'mul02d', [iwc], '( 0 x. %s ) = 0' % IW)], '( t e. RR+ |-> %s ) ~~>r 0' % Bt)
    IT = '( 1 / t )'
    itr_ = D(w, At, 'rpreccld', [trp], '%s e. RR+' % IT)
    Et = '( ( exp ` -u ( L x. %s ) ) x. ( ( %s ^c W ) / W ) )' % (IT, IT)
    wct, wnt, awt, lct = ad(w, At, wc, 'W e. CC'), ad(w, At, wn0, 'W =/= 0'), ad(w, At, awp, '( abs ` W ) e. RR+'), D(w, At, 'rpcnd', [ad(w, At, lrp, 'L e. RR+')], 'L e. CC')
    itc = D(w, At, 'rpcnd', [itr_], '%s e. CC' % IT)
    EL = '( exp ` -u ( L x. %s ) )' % IT
    elr = D(w, At, 'reefcld', [D(w, At, 'renegcld', [D(w, At, 'remulcld', [D(w, At, 'rpred', [ad(w, At, lrp, 'L e. RR+')], 'L e. RR'), D(w, At, 'rpred', [itr_], '%s e. RR' % IT)], '( L x. %s ) e. RR' % IT)],
                                                    '-u ( L x. %s ) e. RR' % IT)], '%s e. RR' % EL)
    el0 = D(w, At, 'rpge0d', [D(w, At, 'rpefcld', [D(w, At, 'renegcld', [D(w, At, 'remulcld', [D(w, At, 'rpred', [ad(w, At, lrp, 'L e. RR+')], 'L e. RR'), D(w, At, 'rpred', [itr_], '%s e. RR' % IT)], '( L x. %s ) e. RR' % IT)],
                                                                   '-u ( L x. %s ) e. RR' % IT)], '%s e. RR+' % EL)], '0 <_ %s' % EL)
    el1 = D(w, At, 'breqtrd', [efle_(w, At, '-u ( L x. %s )' % IT, '0', D(w, At, 'renegcld', [D(w, At, 'remulcld', [D(w, At, 'rpred', [ad(w, At, lrp, 'L e. RR+')], 'L e. RR'), D(w, At, 'rpred', [itr_], '%s e. RR' % IT)], '( L x. %s ) e. RR' % IT)], '-u ( L x. %s ) e. RR' % IT),
                                     cst(w, At, '0re', '0 e. RR'), nlinarith(w, At, [D(w, At, 'rpgt0d', [ad(w, At, lrp, 'L e. RR+')], '0 < L'), D(w, At, 'rpgt0d', [itr_], '0 < %s' % IT)], '-u ( L x. %s ) <_ 0' % IT,
                                                                          leaves={'L': D(w, At, 'rpred', [ad(w, At, lrp, 'L e. RR+')], 'L e. RR'), IT: D(w, At, 'rpred', [itr_], '%s e. RR' % IT)}, atoms=[IT])),
                               cst(w, At, 'ef0', '( exp ` 0 ) = 1')], '%s <_ 1' % EL)
    tw = D(w, At, 'cxpcld', [itc, wct], '( %s ^c W ) e. CC' % IT)
    ITS = '( %s ^c %s )' % (IT, RS)
    its = D(w, At, 'eqtrd', [D(w, At, 'syl3anc', [D(w, At, 'jca', [cst(w, At, '1re', '1 e. RR'), cst(w, At, '0le1', '0 <_ 1')], '( 1 e. RR /\\ 0 <_ 1 )'), trp, D(w, At, 'recnd', [ad(w, At, rwr, '%s e. RR' % RS)], '%s e. CC' % RS), w.inst('divcxp')],
                                  '%s = ( ( 1 ^c %s ) / ( t ^c %s ) )' % (ITS, RS, RS)),
                             D(w, At, 'oveq1d', [D(w, At, 'syl', [D(w, At, 'recnd', [ad(w, At, rwr, '%s e. RR' % RS)], '%s e. CC' % RS), w.inst('1cxp')], '( 1 ^c %s ) = 1' % RS)], '( ( 1 ^c %s ) / ( t ^c %s ) ) = ( 1 / ( t ^c %s ) )' % (RS, RS, RS))],
              '%s = ( 1 / ( t ^c %s ) )' % (ITS, RS))
    aw_ = D(w, At, 'eqtrd', [D(w, At, 'absdivd', [tw, wct, wnt], '( abs ` ( ( %s ^c W ) / W ) ) = ( ( abs ` ( %s ^c W ) ) / ( abs ` W ) )' % (IT, IT)),
                             D(w, At, 'eqtrd', [D(w, At, 'oveq1d', [D(w, At, 'eqtrd', [D(w, At, 'syl2anc', [itr_, wct, w.inst('abscxp')], '( abs ` ( %s ^c W ) ) = %s' % (IT, ITS)), its], '( abs ` ( %s ^c W ) ) = ( 1 / ( t ^c %s ) )' % (IT, RS))],
                                                  '( ( abs ` ( %s ^c W ) ) / ( abs ` W ) ) = ( ( 1 / ( t ^c %s ) ) / ( abs ` W ) )' % (IT, RS)),
                                                D(w, At, 'divrecd', [D(w, At, 'rpcnd', [itp], '( 1 / ( t ^c %s ) ) e. CC' % RS), D(w, At, 'rpcnd', [awt], '( abs ` W ) e. CC'), D(w, At, 'rpne0d', [awt], '( abs ` W ) =/= 0')],
                                                  '( ( 1 / ( t ^c %s ) ) / ( abs ` W ) ) = %s' % (RS, Bt))], '( ( abs ` ( %s ^c W ) ) / ( abs ` W ) ) = %s' % (IT, Bt))],
              '( abs ` ( ( %s ^c W ) / W ) ) = %s' % (IT, Bt))
    elc = D(w, At, 'recnd', [elr], '%s e. CC' % EL)
    ae = D(w, At, 'eqtrd', [D(w, At, 'absmuld', [elc, D(w, At, 'divcld', [tw, wct, wnt], '( ( %s ^c W ) / W ) e. CC' % IT)], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( ( %s ^c W ) / W ) ) )' % (Et, EL, IT)),
                            D(w, At, 'oveq12d', [D(w, At, 'absidd', [elr, el0], '( abs ` %s ) = %s' % (EL, EL)), aw_], '( ( abs ` %s ) x. ( abs ` ( ( %s ^c W ) / W ) ) ) = ( %s x. %s )' % (EL, IT, EL, Bt))],
            '( abs ` %s ) = ( %s x. %s )' % (Et, EL, Bt))
    btr = D(w, At, 'rpred', [D(w, At, 'rpmulcld', [itp, D(w, At, 'rpreccld', [awt], '%s e. RR+' % IW)], '%s e. RR+' % Bt)], '%s e. RR' % Bt)
    bt0 = D(w, At, 'rpge0d', [D(w, At, 'rpmulcld', [itp, D(w, At, 'rpreccld', [awt], '%s e. RR+' % IW)], '%s e. RR+' % Bt)], '0 <_ %s' % Bt)
    b1 = D(w, At, 'lemul1ad', [elr, cst(w, At, '1re', '1 e. RR'), btr, bt0, el1], '( %s x. %s ) <_ ( 1 x. %s )' % (EL, Bt, Bt))
    b2 = D(w, At, 'breqtrd', [b1, D(w, At, 'mullidd', [D(w, At, 'recnd', [btr], '%s e. CC' % Bt)], '( 1 x. %s ) = %s' % (Bt, Bt))], '( %s x. %s ) <_ %s' % (EL, Bt, Bt))
    etc = D(w, At, 'mulcld', [elc, D(w, At, 'divcld', [tw, wct, wnt], '( ( %s ^c W ) / W ) e. CC' % IT)], '%s e. CC' % Et)
    lhs = D(w, At, 'eqtrd', [D(w, At, 'fveq2d', [D(w, At, 'subid1d', [etc], '( %s - 0 ) = %s' % (Et, Et))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (Et, Et)), ae], '( abs ` ( %s - 0 ) ) = ( %s x. %s )' % (Et, EL, Bt))
    rhs = D(w, At, 'eqtrd', [D(w, At, 'fveq2d', [D(w, At, 'subid1d', [D(w, At, 'recnd', [btr], '%s e. CC' % Bt)], '( %s - 0 ) = %s' % (Bt, Bt))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (Bt, Bt)),
                             D(w, At, 'absidd', [btr, bt0], '( abs ` %s ) = %s' % (Bt, Bt))], '( abs ` ( %s - 0 ) ) = %s' % (Bt, Bt))
    fb = D(w, At, 'breqtrrd', [D(w, At, 'eqbrtrd', [lhs, b2], '( abs ` ( %s - 0 ) ) <_ %s' % (Et, Bt)), rhs], '( abs ` ( %s - 0 ) ) <_ ( abs ` ( %s - 0 ) )' % (Et, Bt))
    Au = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % A
    fbu = D(w, Au, 'syl2anc' if False else 'sylan2' if False else 'adantrr', [fb], '') if False else w.s([fb], 'adantrr', '( %s -> ( abs ` ( %s - 0 ) ) <_ ( abs ` ( %s - 0 ) ) )' % (Au, Et, Bt))
    sq = D(w, A, 'rlimsqzlem', [cst(w, A, '1re', '1 e. RR'), D(w, A, '0cnd', [], '0 e. CC'), b0, D(w, At, 'recnd', [btr], '%s e. CC' % Bt), etc, fbu], '( t e. RR+ |-> %s ) ~~>r 0' % Et)
    w.qed([sq], 'idi', S['zl3wte'])
    go(w)


if want('zl3ew2'):
    w = W('zl3ew2', 'Euler integral over ` ( 1 / t , t ) ` on ` 0 < Re W ` : one integration by parts reduces it to ~ zl3ew1 at ` W + 1 ` ( ~ itgparts , ~ gamp1 ).')
    A, Cc = ante_of('zl3ew2')
    wc, w0, lrp, rwr, wn0, awp = wfacts(w, A)
    lc = D(w, A, 'rpcnd', [lrp], 'L e. CC'); lne = D(w, A, 'rpne0d', [lrp], 'L =/= 0')
    W1 = '( W + 1 )'
    w1c = D(w, A, 'addcld', [wc, cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % W1)
    rw1 = D(w, A, 'eqtrd', [D(w, A, 'readdd', [wc, cst(w, A, 'ax-1cn', '1 e. CC')], '( Re ` %s ) = ( ( Re ` W ) + ( Re ` 1 ) )' % W1),
                            D(w, A, 'oveq2d', [cst(w, A, 're1', '( Re ` 1 ) = 1')], '( ( Re ` W ) + ( Re ` 1 ) ) = ( ( Re ` W ) + 1 )')], '( Re ` %s ) = ( ( Re ` W ) + 1 )' % W1)
    gt1 = D(w, A, 'breqtrrd', [linarith(w, A, [w0], '1 < ( ( Re ` W ) + 1 )', leaves={'( Re ` W )': rwr}, atoms=['( Re ` W )']), rw1], '1 < ( Re ` %s )' % W1)
    V1 = '( ( L ^c -u %s ) x. ( _G ` %s ) )' % (W1, W1)
    ew1 = D(w, A, 'syl2anc', [D(w, A, 'jca', [w1c, gt1], '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (W1, W1)), lrp, w.inst('zl3ew1')],
            '( t e. RR+ |-> %s ) ~~>r %s' % (L.EUI(W1, 'L', 't'), V1))
    Ft = '( ( exp ` -u ( L x. t ) ) x. ( ( t ^c W ) / W ) )'
    Et = '( ( exp ` -u ( L x. ( 1 / t ) ) ) x. ( ( ( 1 / t ) ^c W ) / W ) )'
    ftl = D(w, A, 'syl', [D(w, A, 'id', [], A), w.inst('zl3wtf')], '( t e. RR+ |-> %s ) ~~>r 0' % Ft)
    etl = D(w, A, 'syl', [D(w, A, 'id', [], A), w.inst('zl3wte')], '( t e. RR+ |-> %s ) ~~>r 0' % Et)
    LW = '( L / W )'
    lwc = D(w, A, 'divcld', [lc, wc, wn0], '%s e. CC' % LW)
    I0 = L.EUI('W', 'L', 't'); I1 = L.EUI(W1, 'L', 't')
    Rt = '( ( %s - %s ) + ( %s x. %s ) )' % (Ft, Et, LW, I1)
    At = '( %s /\\ t e. RR+ )' % A
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    tr = D(w, At, 'rpred', [trp], 't e. RR'); tc = D(w, At, 'rpcnd', [trp], 't e. CC')
    itp = D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+'); itr = D(w, At, 'rpred', [itp], '( 1 / t ) e. RR')
    wct, lct, w1ct = ad(w, At, wc, 'W e. CC'), ad(w, At, lc, 'L e. CC'), ad(w, At, w1c, '%s e. CC' % W1)
    ftc = D(w, At, 'mulcld', [D(w, At, 'efcld', [D(w, At, 'negcld', [D(w, At, 'mulcld', [lct, tc], '( L x. t ) e. CC')], '-u ( L x. t ) e. CC')], '( exp ` -u ( L x. t ) ) e. CC'),
                              D(w, At, 'divcld', [D(w, At, 'cxpcld', [tc, wct], '( t ^c W ) e. CC'), wct, ad(w, At, wn0, 'W =/= 0')], '( ( t ^c W ) / W ) e. CC')], '%s e. CC' % Ft)
    itc = D(w, At, 'rpcnd', [itp], '( 1 / t ) e. CC')
    etc = D(w, At, 'mulcld', [D(w, At, 'efcld', [D(w, At, 'negcld', [D(w, At, 'mulcld', [lct, itc], '( L x. ( 1 / t ) ) e. CC')], '-u ( L x. ( 1 / t ) ) e. CC')], '( exp ` -u ( L x. ( 1 / t ) ) ) e. CC'),
                              D(w, At, 'divcld', [D(w, At, 'cxpcld', [itc, wct], '( ( 1 / t ) ^c W ) e. CC'), wct, ad(w, At, wn0, 'W =/= 0')], '( ( ( 1 / t ) ^c W ) / W ) e. CC')], '%s e. CC' % Et)
    i1l = gibl(w, At, '( 1 / t )', 't', itr, tr, W1, 'L', w1ct, lct, prp=itp)
    i1c = D(w, At, 'itgcl', [i1l, fx_cl(w, At, '( 1 / t )', 't', itr, W1, 'L', w1ct, lct, None)], '%s e. CC' % I1)
    i0l = gibl(w, At, '( 1 / t )', 't', itr, tr, 'W', 'L', wct, lct, prp=itp)
    i0c = D(w, At, 'itgcl', [i0l, fx_cl(w, At, '( 1 / t )', 't', itr, 'W', 'L', wct, lct, None)], '%s e. CC' % I0)
    rtc = D(w, At, 'addcld', [D(w, At, 'subcld', [ftc, etc], '( %s - %s ) e. CC' % (Ft, Et)), D(w, At, 'mulcld', [ad(w, At, lwc, '%s e. CC' % LW), i1c], '( %s x. %s ) e. CC' % (LW, I1))], '%s e. CC' % Rt)
    Au = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % A
    trpu = w.s([], 'simprl', '( %s -> t e. RR+ )' % Au); t1 = w.s([], 'simprr', '( %s -> 1 <_ t )' % Au)
    tru = D(w, Au, 'rpred', [trpu], 't e. RR'); tcu = D(w, Au, 'rpcnd', [trpu], 't e. CC')
    itpu = D(w, Au, 'rpreccld', [trpu], '( 1 / t ) e. RR+'); itru = D(w, Au, 'rpred', [itpu], '( 1 / t ) e. RR'); itcu = D(w, Au, 'rpcnd', [itpu], '( 1 / t ) e. CC')
    rid = D(w, Au, 'recid2d', [tcu, D(w, Au, 'rpne0d', [trpu], 't =/= 0')], '( ( 1 / t ) x. t ) = 1')
    itle1 = nlinarith(w, Au, [rid, t1, D(w, Au, 'rpge0d', [itpu], '0 <_ ( 1 / t )')], '( 1 / t ) <_ 1', leaves={'( 1 / t )': itru, 't': tru}, atoms=['( 1 / t )'])
    itlet = D(w, Au, 'letrd', [itru, cst(w, Au, '1re', '1 e. RR'), tru, itle1, t1], '( 1 / t ) <_ t')
    wcu, lcu, wnu, w1cu = ad(w, Au, wc, 'W e. CC'), ad(w, Au, lc, 'L e. CC'), ad(w, Au, wn0, 'W =/= 0'), ad(w, Au, w1c, '%s e. CC' % W1)
    XI = '( ( 1 / t ) [,] t )'; XO = '( ( 1 / t ) (,) t )'
    xssI = D(w, Au, 'sstrd', [D(w, Au, 'syl2anc', [itru, tru, w.inst('iccssre')], '%s C_ RR' % XI), cst(w, Au, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % XI)
    xssO = D(w, Au, 'sstrd', [cst(w, Au, 'ioossre', '%s C_ RR' % XO), cst(w, Au, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % XO)
    CXW = '( x e. %s |-> ( x ^c W ) )' % XI
    cxw = D(w, Au, 'simpld', [D(w, Au, 'syl2anc', [wcu, D(w, Au, 'jca', [itpu, tru], '( ( 1 / t ) e. RR+ /\\ t e. RR )'), w.inst('zl3cxc')],
                                '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c W ) ) ) e. ( %s -cn-> CC ) )' % (CXW, XI, XI, XI))], '%s e. ( %s -cn-> CC )' % (CXW, XI))
    WM = '( W - 1 )'
    CXM = '( x e. %s |-> ( x ^c %s ) )' % (XI, WM)
    cxm = D(w, Au, 'simpld', [D(w, Au, 'syl2anc', [D(w, Au, 'subcld', [wcu, cst(w, Au, 'ax-1cn', '1 e. CC')], '%s e. CC' % WM), D(w, Au, 'jca', [itpu, tru], '( ( 1 / t ) e. RR+ /\\ t e. RR )'), w.inst('zl3cxc')],
                                '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (CXM, XI, XI, WM, XI))], '%s e. ( %s -cn-> CC )' % (CXM, XI))
    def opn(cstep, body):
        """restriction of a continuous map on XI to XO"""
        MI = '( x e. %s |-> %s )' % (XI, body); MO = '( x e. %s |-> %s )' % (XO, body)
        rc = D(w, Au, 'sylc', [cst(w, Au, 'ioossicc', '%s C_ %s' % (XO, XI)), cstep, w.inst('rescncf')], '( %s |` %s ) e. ( %s -cn-> CC )' % (MI, XO, XO))
        rs = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (XO, XI)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (MI, XO, MO))], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (Au, MI, XO, MO))
        return D(w, Au, 'eqeltrrd', [rs, rc], '%s e. ( %s -cn-> CC )' % (MO, XO))
    clu = Closure(w, Au, {'L': lcu, 'W': [wcu, wnu]})
    Aexp = '( exp ` -u ( L x. x ) )'; Cq = '( ( x ^c W ) / W )'; Bq = '( -u L x. %s )' % Aexp; Dq = '( x ^c %s )' % WM
    ca = cont(w, Au, XI, Aexp, clu, xssI)
    cc_ = cont(w, Au, XI, Cq, clu, xssI, special={'( x ^c W )': cxw})
    cb = cont(w, Au, XO, Bq, clu, xssO)
    cd = opn(cxm, Dq)
    cbcI = cont(w, Au, XI, '( %s x. %s )' % (Bq, Cq), clu, xssI, special={'( x ^c W )': cxw})
    ibc = D(w, Au, 'eqeltrrd', [w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (XO, XI)), w.inst('resmpt')], 'ax-mp', '( ( x e. %s |-> ( %s x. %s ) ) |` %s ) = ( x e. %s |-> ( %s x. %s ) )' % (XI, Bq, Cq, XO, XO, Bq, Cq))],
                                    'a1i', '( %s -> ( ( x e. %s |-> ( %s x. %s ) ) |` %s ) = ( x e. %s |-> ( %s x. %s ) ) )' % (Au, XI, Bq, Cq, XO, XO, Bq, Cq)),
                                D(w, Au, 'syl2anc', [D(w, Au, 'jca', [itru, tru], '( ( 1 / t ) e. RR /\\ t e. RR )'), cbcI, w.inst('zl3ibl')], '( ( x e. %s |-> ( %s x. %s ) ) |` %s ) e. L^1' % (XI, Bq, Cq, XO))],
               '( x e. %s |-> ( %s x. %s ) ) e. L^1' % (XO, Bq, Cq))
    iad = gibl(w, Au, '( 1 / t )', 't', itru, tru, 'W', 'L', wcu, lcu, prp=itpu)
    da = D(w, Au, 'syl2anc', [lcu, D(w, Au, 'jca', [itru, tru], '( ( 1 / t ) e. RR /\\ t e. RR )'), w.inst('zl3dvl')], '( RR _D ( x e. %s |-> %s ) ) = ( x e. %s |-> %s )' % (XI, Aexp, XO, Bq))
    dc = D(w, Au, 'syl2anc', [D(w, Au, 'jca', [wcu, wnu], '( W e. CC /\\ W =/= 0 )'), D(w, Au, 'jca', [itpu, tru], '( ( 1 / t ) e. RR+ /\\ t e. RR )'), w.inst('zl3dvw')],
            '( RR _D ( x e. %s |-> %s ) ) = ( x e. %s |-> %s )' % (XI, Cq, XO, Dq))
    def bnd(v):
        Ab = '( %s /\\ x = %s )' % (Au, v)
        xe = w.s([], 'simpr', '( %s -> x = %s )' % (Ab, v))
        st_, new = w.rewrite('( %s x. %s )' % (Aexp, Cq), {'x': (v, xe)}, Ab)
        return st_, new
    ee, Enew = bnd('( 1 / t )'); ff, Fnew = bnd('t')
    assert Enew == Et and Fnew == Ft, (Enew, Fnew)
    ip = D(w, Au, 'itgparts', [itru, tru, itlet, ca, cc_, cb, cd, iad, ibc, da, dc, ee, ff],
           'S. %s ( %s x. %s ) _d x = ( ( %s - %s ) - S. %s ( %s x. %s ) _d x )' % (XO, Aexp, Dq, Ft, Et, XO, Bq, Cq))
    # B x. C = -u ( L / W ) x. FX ( W + 1 )
    Aux = '( %s /\\ x e. %s )' % (Au, XO)
    xr_ = D(w, Aux, 'sseldd', [cst(w, Aux, 'ioossre', '%s C_ RR' % XO), w.s([], 'simpr', '( %s -> x e. %s )' % (Aux, XO))], 'x e. RR')
    xc_ = D(w, Aux, 'recnd', [xr_], 'x e. CC')
    lcx, wcx, wnx = ad(w, Aux, lcu, 'L e. CC'), ad(w, Aux, wcu, 'W e. CC'), ad(w, Aux, wnu, 'W =/= 0')
    ec = D(w, Aux, 'efcld', [D(w, Aux, 'negcld', [D(w, Aux, 'mulcld', [lcx, xc_], '( L x. x ) e. CC')], '-u ( L x. x ) e. CC')], '%s e. CC' % Aexp)
    xw = D(w, Aux, 'cxpcld', [xc_, wcx], '( x ^c W ) e. CC')
    XW1 = '( x ^c ( %s - 1 ) )' % W1
    pw = D(w, Aux, 'oveq2d', [D(w, Aux, 'pncand', [wcx, cst(w, Aux, 'ax-1cn', '1 e. CC')], '( %s - 1 ) = W' % W1)], '%s = ( x ^c W )' % XW1)
    bc_eq = chain(w, Aux, ['( %s x. %s )' % (Bq, Cq), '( -u ( L x. %s ) x. %s )' % (Aexp, Cq), '-u ( ( L x. %s ) x. %s )' % (Aexp, Cq), '-u ( ( ( L x. %s ) x. ( x ^c W ) ) / W )' % Aexp,
                               '-u ( ( L x. ( %s x. ( x ^c W ) ) ) / W )' % Aexp, '-u ( %s x. ( %s x. ( x ^c W ) ) )' % (LW, Aexp), '( -u %s x. ( %s x. ( x ^c W ) ) )' % (LW, Aexp),
                               '( -u %s x. ( %s x. %s ) )' % (LW, Aexp, XW1)],
                  [D(w, Aux, 'oveq1d', [D(w, Aux, 'mulneg1d', [lcx, ec], '%s = -u ( L x. %s )' % (Bq, Aexp))], '( %s x. %s ) = ( -u ( L x. %s ) x. %s )' % (Bq, Cq, Aexp, Cq)),
                   D(w, Aux, 'mulneg1d', [D(w, Aux, 'mulcld', [lcx, ec], '( L x. %s ) e. CC' % Aexp), D(w, Aux, 'divcld', [xw, wcx, wnx], '%s e. CC' % Cq)], '( -u ( L x. %s ) x. %s ) = -u ( ( L x. %s ) x. %s )' % (Aexp, Cq, Aexp, Cq)),
                   D(w, Aux, 'negeqd', [D(w, Aux, 'eqcomd', [D(w, Aux, 'divassd', [D(w, Aux, 'mulcld', [lcx, ec], '( L x. %s ) e. CC' % Aexp), xw, wcx, wnx], '( ( ( L x. %s ) x. ( x ^c W ) ) / W ) = ( ( L x. %s ) x. %s )' % (Aexp, Aexp, Cq))],
                                                     '( ( L x. %s ) x. %s ) = ( ( ( L x. %s ) x. ( x ^c W ) ) / W )' % (Aexp, Cq, Aexp))], '-u ( ( L x. %s ) x. %s ) = -u ( ( ( L x. %s ) x. ( x ^c W ) ) / W )' % (Aexp, Cq, Aexp)),
                   D(w, Aux, 'negeqd', [D(w, Aux, 'oveq1d', [D(w, Aux, 'mulassd', [lcx, ec, xw], '( ( L x. %s ) x. ( x ^c W ) ) = ( L x. ( %s x. ( x ^c W ) ) )' % (Aexp, Aexp))],
                                                     '( ( ( L x. %s ) x. ( x ^c W ) ) / W ) = ( ( L x. ( %s x. ( x ^c W ) ) ) / W )' % (Aexp, Aexp))], '-u ( ( ( L x. %s ) x. ( x ^c W ) ) / W ) = -u ( ( L x. ( %s x. ( x ^c W ) ) ) / W )' % (Aexp, Aexp)),
                   D(w, Aux, 'negeqd', [D(w, Aux, 'div23d', [lcx, D(w, Aux, 'mulcld', [ec, xw], '( %s x. ( x ^c W ) ) e. CC' % Aexp), wcx, wnx], '( ( L x. ( %s x. ( x ^c W ) ) ) / W ) = ( %s x. ( %s x. ( x ^c W ) ) )' % (Aexp, LW, Aexp))],
                     '-u ( ( L x. ( %s x. ( x ^c W ) ) ) / W ) = -u ( %s x. ( %s x. ( x ^c W ) ) )' % (Aexp, LW, Aexp)),
                   D(w, Aux, 'eqcomd', [D(w, Aux, 'mulneg1d', [ad(w, Aux, ad(w, Au, D(w, A, 'divcld', [lc, wc, wn0], '%s e. CC' % LW), '%s e. CC' % LW), '%s e. CC' % LW), D(w, Aux, 'mulcld', [ec, xw], '( %s x. ( x ^c W ) ) e. CC' % Aexp)],
                                                   '( -u %s x. ( %s x. ( x ^c W ) ) ) = -u ( %s x. ( %s x. ( x ^c W ) ) )' % (LW, Aexp, LW, Aexp))], '-u ( %s x. ( %s x. ( x ^c W ) ) ) = ( -u %s x. ( %s x. ( x ^c W ) ) )' % (LW, Aexp, LW, Aexp)),
                   D(w, Aux, 'oveq2d', [D(w, Aux, 'oveq2d', [D(w, Aux, 'eqcomd', [pw], '( x ^c W ) = %s' % XW1)], '( %s x. ( x ^c W ) ) = ( %s x. %s )' % (Aexp, Aexp, XW1))],
                     '( -u %s x. ( %s x. ( x ^c W ) ) ) = ( -u %s x. ( %s x. %s ) )' % (LW, Aexp, LW, Aexp, XW1))])
    ibc_eq = D(w, Au, 'itgeq2dv', [bc_eq], 'S. %s ( %s x. %s ) _d x = S. %s ( -u %s x. ( %s x. %s ) ) _d x' % (XO, Bq, Cq, XO, LW, Aexp, XW1))
    nlw = D(w, Au, 'negcld', [ad(w, Au, D(w, A, 'divcld', [lc, wc, wn0], '%s e. CC' % LW), '%s e. CC' % LW)], '-u %s e. CC' % LW)
    i1lu = gibl(w, Au, '( 1 / t )', 't', itru, tru, W1, 'L', w1cu, lcu, prp=itpu)
    mc = D(w, Au, 'itgmulc2', [nlw, fx_cl(w, Au, '( 1 / t )', 't', itru, W1, 'L', w1cu, lcu, None), i1lu], '( -u %s x. %s ) = S. %s ( -u %s x. ( %s x. %s ) ) _d x' % (LW, I1, XO, LW, Aexp, XW1))
    i1cu = D(w, Au, 'itgcl', [i1lu, fx_cl(w, Au, '( 1 / t )', 't', itru, W1, 'L', w1cu, lcu, None)], '%s e. CC' % I1)
    lwcu = ad(w, Au, D(w, A, 'divcld', [lc, wc, wn0], '%s e. CC' % LW), '%s e. CC' % LW)
    ftcu = ad(w, Au, D(w, A, 'idi', [], '') if False else None, '') if False else None
    ident = chain(w, Au, [I0, '( ( %s - %s ) - S. %s ( %s x. %s ) _d x )' % (Ft, Et, XO, Bq, Cq), '( ( %s - %s ) - ( -u %s x. %s ) )' % (Ft, Et, LW, I1),
                          '( ( %s - %s ) - -u ( %s x. %s ) )' % (Ft, Et, LW, I1), Rt],
                  [ip, D(w, Au, 'oveq2d', [D(w, Au, 'eqtr4d', [ibc_eq, mc], 'S. %s ( %s x. %s ) _d x = ( -u %s x. %s )' % (XO, Bq, Cq, LW, I1))],
                         '( ( %s - %s ) - S. %s ( %s x. %s ) _d x ) = ( ( %s - %s ) - ( -u %s x. %s ) )' % (Ft, Et, XO, Bq, Cq, Ft, Et, LW, I1)),
                   D(w, Au, 'oveq2d', [D(w, Au, 'mulneg1d', [lwcu, i1cu], '( -u %s x. %s ) = -u ( %s x. %s )' % (LW, I1, LW, I1))], '( ( %s - %s ) - ( -u %s x. %s ) ) = ( ( %s - %s ) - -u ( %s x. %s ) )' % (Ft, Et, LW, I1, Ft, Et, LW, I1)),
                   D(w, Au, 'subnegd', [D(w, Au, 'subcld', [ad(w, Au, D(w, At, 'idi', [], '') if False else None, '') if False else D(w, Au, 'syl', [D(w, Au, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Au, A)), trpu], At), w.s([ftc], 'idi', '( %s -> %s e. CC )' % (At, Ft))], '%s e. CC' % Ft),
                                                              D(w, Au, 'syl', [D(w, Au, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Au, A)), trpu], At), w.s([etc], 'idi', '( %s -> %s e. CC )' % (At, Et))], '%s e. CC' % Et)],
                                         '( %s - %s ) e. CC' % (Ft, Et)), D(w, Au, 'mulcld', [lwcu, i1cu], '( %s x. %s ) e. CC' % (LW, I1))], '( ( %s - %s ) - -u ( %s x. %s ) ) = %s' % (Ft, Et, LW, I1, Rt))])
    V = '( ( L ^c -u W ) x. ( _G ` W ) )'
    X_ = '( ( 0 - 0 ) + ( %s x. %s ) )' % (LW, V1)
    rs_ = D(w, A, 'rlimsub', [ftc, etc, ftl, etl], '( t e. RR+ |-> ( %s - %s ) ) ~~>r ( 0 - 0 )' % (Ft, Et))
    rm_ = D(w, A, 'rlimmul', [ad(w, At, lwc, '%s e. CC' % LW), i1c, D(w, A, 'syl2anc', [cst(w, A, 'rpssre', 'RR+ C_ RR'), lwc, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (LW, LW)), ew1],
            '( t e. RR+ |-> ( %s x. %s ) ) ~~>r ( %s x. %s )' % (LW, I1, LW, V1))
    ra_ = D(w, A, 'rlimadd', [D(w, At, 'subcld', [ftc, etc], '( %s - %s ) e. CC' % (Ft, Et)), D(w, At, 'mulcld', [ad(w, At, lwc, '%s e. CC' % LW), i1c], '( %s x. %s ) e. CC' % (LW, I1)), rs_, rm_],
            '( t e. RR+ |-> %s ) ~~>r %s' % (Rt, X_))
    req = D(w, A, 'rlimeq', [i0c, rtc, cst(w, A, '1re', '1 e. RR'), ident], '( ( t e. RR+ |-> %s ) ~~>r %s <-> ( t e. RR+ |-> %s ) ~~>r %s )' % (I0, X_, Rt, X_))
    lim = D(w, A, 'mpbird', [ra_, req], '( t e. RR+ |-> %s ) ~~>r %s' % (I0, X_))
    # the value
    wg = D(w, A, 'syl', [D(w, A, 'jca', [wc, w0], '( W e. CC /\\ 0 < ( Re ` W ) )'), w.inst('zrenn')], 'W e. ( CC \\ ( ZZ \\ NN ) )')
    gc = D(w, A, 'syl', [wg, w.inst('gamcl')], '( _G ` W ) e. CC')
    gp = D(w, A, 'syl', [wg, w.inst('gamp1')], '( _G ` %s ) = ( ( _G ` W ) x. W )' % W1)
    ac = D(w, A, 'cxpcld', [lc, D(w, A, 'negcld', [wc], '-u W e. CC')], '( L ^c -u W ) e. CC')
    IL_ = '( 1 / L )'
    ilc = D(w, A, 'reccld', [lc, lne], '%s e. CC' % IL_)
    lp = chain(w, A, ['( L ^c -u %s )' % W1, '( L ^c ( -u W + -u 1 ) )', '( ( L ^c -u W ) x. ( L ^c -u 1 ) )', '( ( L ^c -u W ) x. ( 1 / ( L ^c 1 ) ) )', '( ( L ^c -u W ) x. %s )' % IL_],
               [D(w, A, 'oveq2d', [D(w, A, 'negdid', [wc, cst(w, A, 'ax-1cn', '1 e. CC')], '-u %s = ( -u W + -u 1 )' % W1)], '( L ^c -u %s ) = ( L ^c ( -u W + -u 1 ) )' % W1),
                D(w, A, 'cxpaddd', [lc, lne, D(w, A, 'negcld', [wc], '-u W e. CC'), D(w, A, 'negcld', [cst(w, A, 'ax-1cn', '1 e. CC')], '-u 1 e. CC')], '( L ^c ( -u W + -u 1 ) ) = ( ( L ^c -u W ) x. ( L ^c -u 1 ) )'),
                D(w, A, 'oveq2d', [D(w, A, 'syl3anc', [lc, lne, cst(w, A, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '( L ^c -u 1 ) = ( 1 / ( L ^c 1 ) )')], '( ( L ^c -u W ) x. ( L ^c -u 1 ) ) = ( ( L ^c -u W ) x. ( 1 / ( L ^c 1 ) ) )'),
                D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [D(w, A, 'syl', [lc, w.inst('cxp1')], '( L ^c 1 ) = L')], '( 1 / ( L ^c 1 ) ) = %s' % IL_)], '( ( L ^c -u W ) x. ( 1 / ( L ^c 1 ) ) ) = ( ( L ^c -u W ) x. %s )' % IL_)])
    a_, g_ = '( L ^c -u W )', '( _G ` W )'
    one = chain(w, A, ['( %s x. ( %s x. W ) )' % (LW, IL_), '( %s x. ( W / L ) )' % LW, '( ( L x. W ) / ( W x. L ) )', '( ( L x. W ) / ( L x. W ) )', '1'],
                [D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, 'divrec2d', [wc, lc, lne], '( W / L ) = ( %s x. W )' % IL_)], '( %s x. W ) = ( W / L )' % IL_)], '( %s x. ( %s x. W ) ) = ( %s x. ( W / L ) )' % (LW, IL_, LW)),
                 D(w, A, 'divmuldivd', [lc, wc, wc, lc, wn0, lne], '( %s x. ( W / L ) ) = ( ( L x. W ) / ( W x. L ) )' % LW),
                 D(w, A, 'oveq2d', [D(w, A, 'mulcomd', [wc, lc], '( W x. L ) = ( L x. W )')], '( ( L x. W ) / ( W x. L ) ) = ( ( L x. W ) / ( L x. W ) )'),
                 D(w, A, 'dividd', [D(w, A, 'mulcld', [lc, wc], '( L x. W ) e. CC'), D(w, A, 'mulne0d', [lc, lne, wc, wn0], '( L x. W ) =/= 0')], '( ( L x. W ) / ( L x. W ) ) = 1')])
    val = chain(w, A, [X_, '( 0 + ( %s x. %s ) )' % (LW, V1), '( %s x. %s )' % (LW, V1), '( %s x. ( ( %s x. %s ) x. ( %s x. W ) ) )' % (LW, a_, IL_, g_),
                       '( %s x. ( ( %s x. %s ) x. ( %s x. W ) ) )' % (LW, a_, g_, IL_), '( ( %s x. %s ) x. ( %s x. ( %s x. W ) ) )' % (a_, g_, LW, IL_), '( ( %s x. %s ) x. 1 )' % (a_, g_), V],
                [D(w, A, 'oveq1d', [cst(w, A, '0m0e0', '( 0 - 0 ) = 0')], '%s = ( 0 + ( %s x. %s ) )' % (X_, LW, V1)),
                 D(w, A, 'addlidd', [D(w, A, 'mulcld', [lwc, D(w, A, 'mulcld', [D(w, A, 'cxpcld', [lc, D(w, A, 'negcld', [w1c], '-u %s e. CC' % W1)], '( L ^c -u %s ) e. CC' % W1),
                                                                               D(w, A, 'syl', [D(w, A, 'syl', [D(w, A, 'jca', [w1c, D(w, A, 'lttrd', [cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), D(w, A, 'recld', [w1c], '( Re ` %s ) e. RR' % W1), cst(w, A, '0lt1', '0 < 1'), gt1], '0 < ( Re ` %s )' % W1)],
                                                                                                                     '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W1, W1)), w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % W1), w.inst('gamcl')], '( _G ` %s ) e. CC' % W1)],
                                                             '%s e. CC' % V1)], '( %s x. %s ) e. CC' % (LW, V1))], '( 0 + ( %s x. %s ) ) = ( %s x. %s )' % (LW, V1, LW, V1)),
                 D(w, A, 'oveq2d', [D(w, A, 'oveq12d', [lp, gp], '%s = ( ( %s x. %s ) x. ( %s x. W ) )' % (V1, a_, IL_, g_))], '( %s x. %s ) = ( %s x. ( ( %s x. %s ) x. ( %s x. W ) ) )' % (LW, V1, LW, a_, IL_, g_)),
                 D(w, A, 'oveq2d', [D(w, A, 'mul4d', [ac, ilc, gc, wc], '( ( %s x. %s ) x. ( %s x. W ) ) = ( ( %s x. %s ) x. ( %s x. W ) )' % (a_, IL_, g_, a_, g_, IL_))],
                   '( %s x. ( ( %s x. %s ) x. ( %s x. W ) ) ) = ( %s x. ( ( %s x. %s ) x. ( %s x. W ) ) )' % (LW, a_, IL_, g_, LW, a_, g_, IL_)),
                 D(w, A, 'mul12d', [lwc, D(w, A, 'mulcld', [ac, gc], '( %s x. %s ) e. CC' % (a_, g_)), D(w, A, 'mulcld', [ilc, wc], '( %s x. W ) e. CC' % IL_)],
                   '( %s x. ( ( %s x. %s ) x. ( %s x. W ) ) ) = ( ( %s x. %s ) x. ( %s x. ( %s x. W ) ) )' % (LW, a_, g_, IL_, a_, g_, LW, IL_)),
                 D(w, A, 'oveq2d', [one], '( ( %s x. %s ) x. ( %s x. ( %s x. W ) ) ) = ( ( %s x. %s ) x. 1 )' % (a_, g_, LW, IL_, a_, g_)),
                 D(w, A, 'mulridd', [D(w, A, 'mulcld', [ac, gc], '%s e. CC' % V)], '( ( %s x. %s ) x. 1 ) = %s' % (a_, g_, V))])
    w.qed([lim, val], 'breqtrd', S['zl3ew2'])
    go(w)


# ---------------------------------------------------------------- zl3ewb
def ioo_pos(w, Ax, P, Q, pr, qr, pp):
    """( Ax -> x e. RR+ ) for Ax = ( ... /\\ x e. ( P (,) Q ) ), pp: ( Ax -> 0 < P )"""
    X = '( %s (,) %s )' % (P, Q)
    xx = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, X))
    xr = D(w, Ax, 'sseldd', [cst(w, Ax, 'ioossre', '%s C_ RR' % X), xx], 'x e. RR')
    bi = D(w, Ax, 'syl2anc', [D(w, Ax, 'rexrd', [pr], '%s e. RR*' % P), D(w, Ax, 'rexrd', [qr], '%s e. RR*' % Q), w.inst('elioo2')],
           '( x e. %s <-> ( x e. RR /\\ %s < x /\\ x < %s ) )' % (X, P, Q))
    px = D(w, Ax, 'simp2d', [D(w, Ax, 'mpbid', [xx, bi], '( x e. RR /\\ %s < x /\\ x < %s )' % (P, Q))], '%s < x' % P)
    return xr, D(w, Ax, 'elrpd', [xr, D(w, Ax, 'lttrd', [cst(w, Ax, '0re', '0 e. RR'), pr, xr, pp, px], '0 < x')], 'x e. RR+')


def fxs_rp(w, Ax, S_, lrp, sr, xr, xrp):
    EL = '( exp ` -u ( L x. x ) )'
    e = D(w, Ax, 'rpefcld', [D(w, Ax, 'renegcld', [D(w, Ax, 'remulcld', [D(w, Ax, 'rpred', [lrp], 'L e. RR'), xr], '( L x. x ) e. RR')], '-u ( L x. x ) e. RR')], '%s e. RR+' % EL)
    c = D(w, Ax, 'rpcxpcld', [xrp, D(w, Ax, 'resubcld', [sr, cst(w, Ax, '1re', '1 e. RR')], '( %s - 1 ) e. RR' % S_)], '( x ^c ( %s - 1 ) ) e. RR+' % S_)
    return e, D(w, Ax, 'rpmulcld', [e, c], '%s e. RR+' % FX(S_, 'L'))


if want('zl3ewb'):
    w = W('zl3ewb', 'The truncated Euler integral is bounded by its real-part value: ` abs ( S. ( 1 / T , T ) e ^ -Lx x ^ ( W - 1 ) ) <_ L ^ -Re W Gamma ( Re W ) ` ( monotone in ` T ` , ~ rlimle ).')
    A, Cc = ante_of('zl3ewb')
    wc = D(w, A, 'simp1l', [], 'W e. CC'); w0 = D(w, A, 'simp1r', [], '0 < ( Re ` W )')
    lrp = D(w, A, 'simp2', [], 'L e. RR+'); Trp = D(w, A, 'simp3', [], 'T e. RR+')
    S_ = '( Re ` W )'
    sr = D(w, A, 'recld', [wc], '%s e. RR' % S_); sc = D(w, A, 'recnd', [sr], '%s e. CC' % S_)
    rs0 = D(w, A, 'breqtrrd', [w0, D(w, A, 'rered', [sr], '( Re ` %s ) = %s' % (S_, S_))], '0 < ( Re ` %s )' % S_)
    lc = D(w, A, 'rpcnd', [lrp], 'L e. CC')
    VS = '( ( L ^c -u %s ) x. ( _G ` %s ) )' % (S_, S_)
    lim = D(w, A, 'syl2anc', [D(w, A, 'jca', [sc, rs0], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (S_, S_)), lrp, w.inst('zl3ew2')],
            '( t e. RR+ |-> %s ) ~~>r %s' % (L.EUI(S_, 'L', 't'), VS))
    Tr = D(w, A, 'rpred', [Trp], 'T e. RR'); iTp = D(w, A, 'rpreccld', [Trp], '( 1 / T ) e. RR+'); iTr = D(w, A, 'rpred', [iTp], '( 1 / T ) e. RR')
    XT = '( ( 1 / T ) (,) T )'
    ib = gibl(w, A, '( 1 / T )', 'T', iTr, Tr, 'W', 'L', wc, lc, prp=iTp)
    ab = D(w, A, 'itgabs', [fx_cl(w, A, '( 1 / T )', 'T', iTr, 'W', 'L', wc, lc, None), ib],
           '( abs ` %s ) <_ S. %s ( abs ` %s ) _d x' % (L.EUI('W', 'L', 'T'), XT, FX('W', 'L')))
    Ax = '( %s /\\ x e. %s )' % (A, XT)
    xr, xrp = ioo_pos(w, Ax, '( 1 / T )', 'T', ad(w, Ax, iTr, '( 1 / T ) e. RR'), ad(w, Ax, Tr, 'T e. RR'), ad(w, Ax, D(w, A, 'rpgt0d', [iTp], '0 < ( 1 / T )'), '0 < ( 1 / T )'))
    wcx = ad(w, Ax, wc, 'W e. CC'); xc = D(w, Ax, 'rpcnd', [xrp], 'x e. CC')
    EL = '( exp ` -u ( L x. x ) )'
    elp, fsp = fxs_rp(w, Ax, S_, ad(w, Ax, lrp, 'L e. RR+'), ad(w, Ax, sr, '%s e. RR' % S_), xr, xrp)
    elr = D(w, Ax, 'rpred', [elp], '%s e. RR' % EL)
    wm = D(w, Ax, 'subcld', [wcx, cst(w, Ax, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    rwm = D(w, Ax, 'eqtrd', [D(w, Ax, 'resubd', [wcx, cst(w, Ax, 'ax-1cn', '1 e. CC')], '( Re ` ( W - 1 ) ) = ( %s - ( Re ` 1 ) )' % S_),
                             D(w, Ax, 'oveq2d', [cst(w, Ax, 're1', '( Re ` 1 ) = 1')], '( %s - ( Re ` 1 ) ) = ( %s - 1 )' % (S_, S_))], '( Re ` ( W - 1 ) ) = ( %s - 1 )' % S_)
    ax_ = D(w, Ax, 'eqtrd', [D(w, Ax, 'syl2anc', [xrp, wm, w.inst('abscxp')], '( abs ` ( x ^c ( W - 1 ) ) ) = ( x ^c ( Re ` ( W - 1 ) ) )'),
                             D(w, Ax, 'oveq2d', [rwm], '( x ^c ( Re ` ( W - 1 ) ) ) = ( x ^c ( %s - 1 ) )' % S_)], '( abs ` ( x ^c ( W - 1 ) ) ) = ( x ^c ( %s - 1 ) )' % S_)
    af = D(w, Ax, 'eqtrd', [D(w, Ax, 'absmuld', [D(w, Ax, 'recnd', [elr], '%s e. CC' % EL), D(w, Ax, 'cxpcld', [xc, wm], '( x ^c ( W - 1 ) ) e. CC')],
                              '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( x ^c ( W - 1 ) ) ) )' % (FX('W', 'L'), EL)),
                            D(w, Ax, 'oveq12d', [D(w, Ax, 'absidd', [elr, D(w, Ax, 'rpge0d', [elp], '0 <_ %s' % EL)], '( abs ` %s ) = %s' % (EL, EL)), ax_],
                              '( ( abs ` %s ) x. ( abs ` ( x ^c ( W - 1 ) ) ) ) = %s' % (EL, FX(S_, 'L')))], '( abs ` %s ) = %s' % (FX('W', 'L'), FX(S_, 'L')))
    GT = L.EUI(S_, 'L', 'T')
    ie = D(w, A, 'itgeq2dv', [af], 'S. %s ( abs ` %s ) _d x = %s' % (XT, FX('W', 'L'), GT))
    gtr = D(w, A, 'itgrecl', [D(w, Ax, 'rpred', [fsp], '%s e. RR' % FX(S_, 'L')), gibl(w, A, '( 1 / T )', 'T', iTr, Tr, S_, 'L', sc, lc, prp=iTp)], '%s e. RR' % GT)
    # monotone towards the limit on ( T + 1 / T ) [,) +oo
    T2 = '( T + ( 1 / T ) )'
    t2r = D(w, A, 'readdcld', [Tr, iTr], '%s e. RR' % T2)
    AP = '( %s [,) +oo )' % T2
    At = '( %s /\\ t e. %s )' % (A, AP)
    tt = D(w, At, 'mpbid', [w.s([], 'simpr', '( %s -> t e. %s )' % (At, AP)), D(w, At, 'syl', [ad(w, At, t2r, '%s e. RR' % T2), w.inst('elicopnf')], '( t e. %s <-> ( t e. RR /\\ %s <_ t ) )' % (AP, T2))],
           '( t e. RR /\\ %s <_ t )' % T2)
    tr = D(w, At, 'simpld', [tt], 't e. RR'); tge = D(w, At, 'simprd', [tt], '%s <_ t' % T2)
    Trt = ad(w, At, Tr, 'T e. RR'); iTrt = ad(w, At, iTr, '( 1 / T ) e. RR')
    iT0 = ad(w, At, D(w, A, 'rpgt0d', [iTp], '0 < ( 1 / T )'), '0 < ( 1 / T )'); T0 = ad(w, At, D(w, A, 'rpgt0d', [Trp], '0 < T'), '0 < T')
    lv = {'T': Trt, '( 1 / T )': iTrt, 't': tr}
    Tt = linarith(w, At, [tge, iT0], 'T <_ t', leaves=lv, atoms=['( 1 / T )'])
    trp = D(w, At, 'elrpd', [tr, linarith(w, At, [tge, iT0, T0], '0 < t', leaves=lv, atoms=['( 1 / T )'])], 't e. RR+')
    itt = D(w, At, 'mpbid', [Tt, D(w, At, 'lerecd', [ad(w, At, Trp, 'T e. RR+'), trp], '( T <_ t <-> ( 1 / t ) <_ ( 1 / T ) )')], '( 1 / t ) <_ ( 1 / T )')
    itp_ = D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+'); itr_ = D(w, At, 'rpred', [itp_], '( 1 / t ) e. RR')
    Xt = '( ( 1 / t ) (,) t )'
    sub = D(w, At, 'syl2anc', [D(w, At, 'jca', [D(w, At, 'rexrd', [itr_], '( 1 / t ) e. RR*'), D(w, At, 'rexrd', [tr], 't e. RR*')], '( ( 1 / t ) e. RR* /\\ t e. RR* )'),
                               D(w, At, 'jca', [itt, Tt], '( ( 1 / t ) <_ ( 1 / T ) /\\ T <_ t )'), w.inst('ioossioo')], '%s C_ %s' % (XT, Xt))
    Axt = '( %s /\\ x e. %s )' % (At, Xt)
    xrt, xrpt = ioo_pos(w, Axt, '( 1 / t )', 't', ad(w, Axt, itr_, '( 1 / t ) e. RR'), ad(w, Axt, tr, 't e. RR'), ad(w, Axt, D(w, At, 'rpgt0d', [itp_], '0 < ( 1 / t )'), '0 < ( 1 / t )'))
    _, fspt = fxs_rp(w, Axt, S_, ad(w, Axt, ad(w, At, lrp, 'L e. RR+'), 'L e. RR+'), ad(w, Axt, ad(w, At, sr, '%s e. RR' % S_), '%s e. RR' % S_), xrt, xrpt)
    ibt = gibl(w, At, '( 1 / t )', 't', itr_, tr, S_, 'L', ad(w, At, sc, '%s e. CC' % S_), ad(w, At, lc, 'L e. CC'), prp=itp_)
    Gt = L.EUI(S_, 'L', 't')
    le_ = D(w, At, 'itgless', [sub, cst(w, At, 'ioombl', '%s e. dom vol' % XT), D(w, Axt, 'rpred', [fspt], '%s e. RR' % FX(S_, 'L')), D(w, Axt, 'rpge0d', [fspt], '0 <_ %s' % FX(S_, 'L')), ibt],
            '%s <_ %s' % (GT, Gt))
    gttr = D(w, At, 'itgrecl', [D(w, Axt, 'rpred', [fspt], '%s e. RR' % FX(S_, 'L')), ibt], '%s e. RR' % Gt)
    # the limits along AP
    apss = D(w, A, 'ssrdv', [w.s([trp], 'ex', '( %s -> ( t e. %s -> t e. RR+ ) )' % (A, AP))], '%s C_ RR+' % AP)
    aprr = D(w, A, 'syl2anc', [t2r, cst(w, A, 'pnfxr', '+oo e. RR*'), w.inst('icossre')], '%s C_ RR' % AP)
    sup = D(w, A, 'syl2anc', [D(w, A, 'rexrd', [t2r], '%s e. RR*' % T2), D(w, A, 'renepnfd', [t2r], '%s =/= +oo' % T2), w.inst('icopnfsup')], 'sup ( %s , RR* , < ) = +oo' % AP)
    c1 = D(w, A, 'syl2anc', [aprr, D(w, A, 'recnd', [gtr], '%s e. CC' % GT), w.inst('rlimconst')], '( t e. %s |-> %s ) ~~>r %s' % (AP, GT, GT))
    MT = '( t e. RR+ |-> %s )' % Gt
    rsq = D(w, A, 'syl', [apss, w.inst('resmpt')], '( %s |` %s ) = ( t e. %s |-> %s )' % (MT, AP, AP, Gt))
    c2 = D(w, A, 'eqbrtrrd', [rsq, D(w, A, 'syl', [lim, w.inst('rlimres')], '( %s |` %s ) ~~>r %s' % (MT, AP, VS))], '( t e. %s |-> %s ) ~~>r %s' % (AP, Gt, VS))
    bnd = D(w, A, 'rlimle', [sup, c1, c2, ad(w, At, gtr, '%s e. RR' % GT), gttr, le_], '%s <_ %s' % (GT, VS))
    s1 = D(w, A, 'breqtrd', [ab, ie], '( abs ` %s ) <_ %s' % (L.EUI('W', 'L', 'T'), GT))
    ar = D(w, A, 'abscld', [D(w, A, 'itgcl', [ib, fx_cl(w, A, '( 1 / T )', 'T', iTr, 'W', 'L', wc, lc, None)], '%s e. CC' % L.EUI('W', 'L', 'T'))], '( abs ` %s ) e. RR' % L.EUI('W', 'L', 'T'))
    srp = D(w, A, 'elrpd', [sr, w0], '%s e. RR+' % S_)
    vsr = D(w, A, 'rpred', [D(w, A, 'rpmulcld', [D(w, A, 'rpcxpcld', [lrp, D(w, A, 'renegcld', [sr], '-u %s e. RR' % S_)], '( L ^c -u %s ) e. RR+' % S_),
                                                 D(w, A, 'syl', [srp, w.inst('rpgamcl')], '( _G ` %s ) e. RR+' % S_)], '%s e. RR+' % VS)], '%s e. RR' % VS)
    w.qed([ar, gtr, vsr, s1, bnd], 'letrd', S['zl3ewb'])
    go(w)
