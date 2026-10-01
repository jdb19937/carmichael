"""ZL3d section G, part 2: the theta series (bounds, continuity, decay), exchange, Tannery.
`MM_DB=sorties/zl3d.mm python3 tools/gen/zl3d_g2.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl3d_g import *
from c0lib import hyp

EXv, TT, KE, KT, THP = L.EXv, L.TT, L.KE, L.KT, L.THP
EUI = L.EUI


def want(label):
    return __name__ == '__main__' and (not only or label in only)


def exv_arg(w, A, n, x, nr, xr, mrp):
    """( A -> ( ( _pi x. ( n ^ 2 ) ) x. ( x / M ) ) e. RR )"""
    return D(w, A, 'remulcld', [D(w, A, 'remulcld', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'resqcld', [nr], '( %s ^ 2 ) e. RR' % n)], '( _pi x. ( %s ^ 2 ) ) e. RR' % n),
                                D(w, A, 'rerpdivcld', [xr, mrp], '( %s / M ) e. RR' % x)], '( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) e. RR' % (n, x))


def exv_rp(w, A, n, x, nr, xr, mrp):
    a = exv_arg(w, A, n, x, nr, xr, mrp)
    return D(w, A, 'rpefcld', [D(w, A, 'renegcld', [a], '-u ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) e. RR' % (n, x))], '%s e. RR+' % EXv(n, x))


def np_facts(w, A, pp, n, nr, n0):
    """N ^ P real, nonnegative"""
    pn = p_nn0(w, A, pp)
    return pn, D(w, A, 'reexpcld', [nr, pn], '( %s ^ P ) e. RR' % n), D(w, A, 'expge0d', [nr, pn, n0], '0 <_ ( %s ^ P )' % n)


def exv_mono(w, A, n, E, X, nr, er, xr, mrp, ex):
    """( A -> EXv ( n , X ) <_ EXv ( n , E ) ) from ex: E <_ X"""
    em = D(w, A, 'mpbid', [ex, D(w, A, 'lediv1d', [er, xr, mrp], '( %s <_ %s <-> ( %s / M ) <_ ( %s / M ) )' % (E, X, E, X))], '( %s / M ) <_ ( %s / M )' % (E, X))
    pn2 = '( _pi x. ( %s ^ 2 ) )' % n
    pr = D(w, A, 'remulcld', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'resqcld', [nr], '( %s ^ 2 ) e. RR' % n)], '%s e. RR' % pn2)
    p0 = D(w, A, 'mulge0d', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'resqcld', [nr], '( %s ^ 2 ) e. RR' % n), D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), cst(w, A, 'pire', '_pi e. RR'), cst(w, A, 'pipos', '0 < _pi')], '0 <_ _pi'),
                              D(w, A, 'sqge0d', [nr], '0 <_ ( %s ^ 2 )' % n)], '0 <_ %s' % pn2)
    er_ = D(w, A, 'rerpdivcld', [er, mrp], '( %s / M ) e. RR' % E); xr_ = D(w, A, 'rerpdivcld', [xr, mrp], '( %s / M ) e. RR' % X)
    m = D(w, A, 'lemul2ad', [er_, xr_, pr, p0, em], '( %s x. ( %s / M ) ) <_ ( %s x. ( %s / M ) )' % (pn2, E, pn2, X))
    ae = exv_arg(w, A, n, E, nr, er, mrp); ax = exv_arg(w, A, n, X, nr, xr, mrp)
    ng = D(w, A, 'mpbid', [m, D(w, A, 'lenegd', [ae, ax], '( ( %s x. ( %s / M ) ) <_ ( %s x. ( %s / M ) ) <-> -u ( %s x. ( %s / M ) ) <_ -u ( %s x. ( %s / M ) ) )' % (pn2, E, pn2, X, pn2, X, pn2, E))],
           '-u ( %s x. ( %s / M ) ) <_ -u ( %s x. ( %s / M ) )' % (pn2, X, pn2, E))
    nx = D(w, A, 'renegcld', [ax], '-u ( %s x. ( %s / M ) ) e. RR' % (pn2, X)); ne_ = D(w, A, 'renegcld', [ae], '-u ( %s x. ( %s / M ) ) e. RR' % (pn2, E))
    return D(w, A, 'mpbid', [ng, D(w, A, 'syl2anc', [nx, ne_, w.inst('efle')], '( -u ( %s x. ( %s / M ) ) <_ -u ( %s x. ( %s / M ) ) <-> %s <_ %s )' % (pn2, X, pn2, E, EXv(n, X), EXv(n, E)))],
             '%s <_ %s' % (EXv(n, X), EXv(n, E)))


def np_le(w, A, pp, n, nr, nc):
    """( A -> ( n ^ P ) <_ ( 1 + ( abs ` n ) ) )"""
    ab = D(w, A, 'abscld', [nc], '( abs ` %s ) e. RR' % n)
    f = '( %s ^ P ) <_ ( 1 + ( abs ` %s ) )' % (n, n)

    def s0(A0, e):
        eq = D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [e], '( %s ^ P ) = ( %s ^ 0 )' % (n, n)), D(w, A0, 'exp0d', [ad(w, A0, nc, '%s e. CC' % n)], '( %s ^ 0 ) = 1' % n)], '( %s ^ P ) = 1' % n)
        a0 = D(w, A0, 'absge0d', [ad(w, A0, nc, '%s e. CC' % n)], '0 <_ ( abs ` %s )' % n)
        return linarith(w, A0, [eq, a0], f, leaves={'( %s ^ P )' % n: D(w, A0, 'reexpcld', [ad(w, A0, nr, '%s e. RR' % n), D(w, A0, 'eqeltrd', [e, cst(w, A0, '0nn0', '0 e. NN0')], 'P e. NN0')], '( %s ^ P ) e. RR' % n),
                                                 '( abs ` %s )' % n: ad(w, A0, ab, '( abs ` %s ) e. RR' % n)}, atoms=['( %s ^ P )' % n, '( abs ` %s )' % n])

    def s1(A1, e):
        eq = D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [e], '( %s ^ P ) = ( %s ^ 1 )' % (n, n)), D(w, A1, 'exp1d', [ad(w, A1, nc, '%s e. CC' % n)], '( %s ^ 1 ) = %s' % (n, n))], '( %s ^ P ) = %s' % (n, n))
        la = D(w, A1, 'leabsd', [ad(w, A1, nr, '%s e. RR' % n)], '%s <_ ( abs ` %s )' % (n, n))
        return linarith(w, A1, [eq, la], f, leaves={'( %s ^ P )' % n: D(w, A1, 'reexpcld', [ad(w, A1, nr, '%s e. RR' % n), D(w, A1, 'eqeltrd', [e, cst(w, A1, '1nn0', '1 e. NN0')], 'P e. NN0')], '( %s ^ P ) e. RR' % n),
                                                  '( abs ` %s )' % n: ad(w, A1, ab, '( abs ` %s ) e. RR' % n), n: ad(w, A1, nr, '%s e. RR' % n)}, atoms=['( %s ^ P )' % n, '( abs ` %s )' % n])
    return pcases(w, A, pp, f, s0, s1)


# ---------------------------------------------------------------- zl3tb0
if want('zl3tb0'):
    w = W('zl3tb0', 'Geometric majorant of the theta terms on ` [ E , +oo ) ` : ` N ^ P e ^ ( -pi N ^ 2 X / M ) <_ e ^ ( M / ( pi E ) ) ( 1 / 2 ) ^ N ` ( ~ zl3gre ).')
    A, Cc = ante_of('zl3tb0')
    mn = D(w, A, 'simp1l', [], 'M e. NN'); pp = D(w, A, 'simp1r', [], 'P e. { 0 , 1 }')
    tr3 = D(w, A, 'simp2', [], '( E e. RR+ /\\ X e. RR /\\ E <_ X )')
    erp = D(w, A, 'simp1d', [tr3], 'E e. RR+'); xr = D(w, A, 'simp2d', [tr3], 'X e. RR'); ex = D(w, A, 'simp3d', [tr3], 'E <_ X')
    nn = D(w, A, 'simp3', [], 'N e. NN')
    er = D(w, A, 'rpred', [erp], 'E e. RR'); mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+')
    nr = D(w, A, 'nnred', [nn], 'N e. RR'); nc = D(w, A, 'nncnd', [nn], 'N e. CC'); n0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), nr, D(w, A, 'nngt0d', [nn], '0 < N')], '0 <_ N')
    pn, npr, np0 = np_facts(w, A, pp, 'N', nr, n0)
    exX = exv_rp(w, A, 'N', 'X', nr, xr, mrp); exE = exv_rp(w, A, 'N', 'E', nr, er, mrp)
    exXr = D(w, A, 'rpred', [exX], '%s e. RR' % EXv('N', 'X')); exEr = D(w, A, 'rpred', [exE], '%s e. RR' % EXv('N', 'E'))
    mono = exv_mono(w, A, 'N', 'E', 'X', nr, er, xr, mrp, ex)
    s1 = D(w, A, 'lemul2ad', [exXr, exEr, npr, np0, mono], '( ( N ^ P ) x. %s ) <_ ( ( N ^ P ) x. %s )' % (EXv('N', 'X'), EXv('N', 'E')))
    ab = D(w, A, 'abscld', [nc], '( abs ` N ) e. RR'); opr = D(w, A, 'readdcld', [cst(w, A, '1re', '1 e. RR'), ab], '( 1 + ( abs ` N ) ) e. RR')
    s2 = D(w, A, 'lemul1ad', [npr, opr, exEr, D(w, A, 'rpge0d', [exE], '0 <_ %s' % EXv('N', 'E')), np_le(w, A, pp, 'N', nr, nc)],
           '( ( N ^ P ) x. %s ) <_ ( ( 1 + ( abs ` N ) ) x. %s )' % (EXv('N', 'E'), EXv('N', 'E')))
    emrp = D(w, A, 'rpdivcld', [erp, mrp], '( E / M ) e. RR+')
    G2 = '( exp ` -u ( ( _pi x. ( E / M ) ) x. ( N ^ 2 ) ) )'
    gre = D(w, A, 'syl2anc', [emrp, nr, w.inst('zl3gre')], '( ( 1 + ( abs ` N ) ) x. %s ) <_ ( %s x. ( 2 ^c -u ( abs ` N ) ) )' % (G2, KE('E')))
    m32 = D(w, A, 'mul32d', [cst(w, A, 'picn', '_pi e. CC'), D(w, A, 'sqcld', [nc], '( N ^ 2 ) e. CC'), D(w, A, 'rpcnd', [emrp], '( E / M ) e. CC')],
            '( ( _pi x. ( N ^ 2 ) ) x. ( E / M ) ) = ( ( _pi x. ( E / M ) ) x. ( N ^ 2 ) )')
    eE = D(w, A, 'fveq2d', [D(w, A, 'negeqd', [m32], '-u ( ( _pi x. ( N ^ 2 ) ) x. ( E / M ) ) = -u ( ( _pi x. ( E / M ) ) x. ( N ^ 2 ) )')], '%s = %s' % (EXv('N', 'E'), G2))
    s3 = D(w, A, 'eqbrtrd', [D(w, A, 'oveq2d', [eE], '( ( 1 + ( abs ` N ) ) x. %s ) = ( ( 1 + ( abs ` N ) ) x. %s )' % (EXv('N', 'E'), G2)), gre],
           '( ( 1 + ( abs ` N ) ) x. %s ) <_ ( %s x. ( 2 ^c -u ( abs ` N ) ) )' % (EXv('N', 'E'), KE('E')))
    an = D(w, A, 'absidd', [nr, n0], '( abs ` N ) = N')
    tw = D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [D(w, A, 'negeqd', [an], '-u ( abs ` N ) = -u N')], '( 2 ^c -u ( abs ` N ) ) = ( 2 ^c -u N )'), two_neg(w, A, 'N', D(w, A, 'nnnn0d', [nn], 'N e. NN0'))],
           '( 2 ^c -u ( abs ` N ) ) = ( ( 1 / 2 ) ^ N )')
    s4 = D(w, A, 'breqtrd', [s3, D(w, A, 'oveq2d', [tw], '( %s x. ( 2 ^c -u ( abs ` N ) ) ) = ( %s x. ( ( 1 / 2 ) ^ N ) )' % (KE('E'), KE('E')))],
           '( ( 1 + ( abs ` N ) ) x. %s ) <_ ( %s x. ( ( 1 / 2 ) ^ N ) )' % (EXv('N', 'E'), KE('E')))
    r1 = D(w, A, 'remulcld', [npr, exXr], '( ( N ^ P ) x. %s ) e. RR' % EXv('N', 'X')); r2 = D(w, A, 'remulcld', [npr, exEr], '( ( N ^ P ) x. %s ) e. RR' % EXv('N', 'E'))
    r3 = D(w, A, 'remulcld', [opr, exEr], '( ( 1 + ( abs ` N ) ) x. %s ) e. RR' % EXv('N', 'E'))
    r4 = D(w, A, 'remulcld', [D(w, A, 'reefcld', [D(w, A, 'rereccld', [D(w, A, 'remulcld', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'rpred', [emrp], '( E / M ) e. RR')], '( _pi x. ( E / M ) ) e. RR'),
                                                                                              D(w, A, 'gt0ne0d', [D(w, A, 'mulgt0d', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'rpred', [emrp], '( E / M ) e. RR'), cst(w, A, 'pipos', '0 < _pi'), D(w, A, 'rpgt0d', [emrp], '0 < ( E / M )')], '0 < ( _pi x. ( E / M ) )')], '( _pi x. ( E / M ) ) =/= 0')],
                                                          '( 1 / ( _pi x. ( E / M ) ) ) e. RR')], '%s e. RR' % KE('E')),
                              D(w, A, 'reexpcld', [cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), D(w, A, 'nnnn0d', [nn], 'N e. NN0')], '( ( 1 / 2 ) ^ N ) e. RR')], '( %s x. ( ( 1 / 2 ) ^ N ) ) e. RR' % KE('E'))
    w.qed([r1, r3, r4, D(w, A, 'letrd', [r1, r2, r3, s1, s2], '( ( N ^ P ) x. %s ) <_ ( ( 1 + ( abs ` N ) ) x. %s )' % (EXv('N', 'X'), EXv('N', 'E'))), s4], 'letrd', S['zl3tb0'])
    go(w)


# ---------------------------------------------------------------- zl3tdc
if want('zl3tdc'):
    w = W('zl3tdc', 'Decay of the theta terms on ` [ 1 , +oo ) ` : the factor ` e ^ ( -pi ( X - 1 ) / M ) ` splits off ( ` ( N ^ 2 - 1 ) ( X - 1 ) >_ 0 ` , ~ zl3tb0 at ` E = X = 1 ` ).')
    A, Cc = ante_of('zl3tdc')
    mn = D(w, A, 'simp1l', [], 'M e. NN'); pp = D(w, A, 'simp1r', [], 'P e. { 0 , 1 }')
    xr = D(w, A, 'simp2l', [], 'X e. RR'); x1 = D(w, A, 'simp2r', [], '1 <_ X'); nn = D(w, A, 'simp3', [], 'N e. NN')
    mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+'); mc = D(w, A, 'rpcnd', [mrp], 'M e. CC'); mne = D(w, A, 'rpne0d', [mrp], 'M =/= 0')
    nr = D(w, A, 'nnred', [nn], 'N e. RR'); nc = D(w, A, 'nncnd', [nn], 'N e. CC')
    n1 = D(w, A, 'nnge1d', [nn], '1 <_ N')
    n0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), nr, D(w, A, 'nngt0d', [nn], '0 < N')], '0 <_ N')
    r = '( 1 / M )'
    rr = D(w, A, 'rpreccld', [mrp], '%s e. RR+' % r); rre = D(w, A, 'rpred', [rr], '%s e. RR' % r)
    pr = cst(w, A, 'pire', '_pi e. RR')
    pi0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), pr, cst(w, A, 'pipos', '0 < _pi')], '0 <_ _pi')
    n2 = '( N ^ 2 )'
    n2r = D(w, A, 'resqcld', [nr], '%s e. RR' % n2)
    lv = {'N': nr, 'X': xr, r: rre, '_pi': pr}
    n21 = nlinarith(w, A, [n1], '1 <_ %s' % n2, leaves=lv, atoms=[r])
    q1 = D(w, A, 'subge0d', [n2r, cst(w, A, '1re', '1 e. RR')], '( 0 <_ ( %s - 1 ) <-> 1 <_ %s )' % (n2, n2))
    x1_ = D(w, A, 'subge0d', [xr, cst(w, A, '1re', '1 e. RR')], '( 0 <_ ( X - 1 ) <-> 1 <_ X )')
    q = D(w, A, 'mulge0d', [D(w, A, 'resubcld', [n2r, cst(w, A, '1re', '1 e. RR')], '( %s - 1 ) e. RR' % n2), D(w, A, 'resubcld', [xr, cst(w, A, '1re', '1 e. RR')], '( X - 1 ) e. RR'),
                            D(w, A, 'mpbird', [n21, q1], '0 <_ ( %s - 1 )' % n2), D(w, A, 'mpbird', [x1, x1_], '0 <_ ( X - 1 )')], '0 <_ ( ( %s - 1 ) x. ( X - 1 ) )' % n2)
    pr_ = D(w, A, 'mulge0d', [pr, rre, pi0, D(w, A, 'rpge0d', [rr], '0 <_ %s' % r)], '0 <_ ( _pi x. %s )' % r)
    h = D(w, A, 'mulge0d', [D(w, A, 'remulcld', [pr, rre], '( _pi x. %s ) e. RR' % r), D(w, A, 'remulcld', [D(w, A, 'resubcld', [n2r, cst(w, A, '1re', '1 e. RR')], '( %s - 1 ) e. RR' % n2),
                                                                                                     D(w, A, 'resubcld', [xr, cst(w, A, '1re', '1 e. RR')], '( X - 1 ) e. RR')], '( ( %s - 1 ) x. ( X - 1 ) ) e. RR' % n2), pr_, q],
          '0 <_ ( ( _pi x. %s ) x. ( ( %s - 1 ) x. ( X - 1 ) ) )' % (r, n2))
    PN = '( _pi x. %s )' % n2
    Lg = '-u ( %s x. ( X x. %s ) )' % (PN, r)
    Rg = '( -u ( ( _pi x. %s ) x. ( X - 1 ) ) + -u ( %s x. %s ) )' % (r, PN, r)
    ine = nlinarith(w, A, [h], '%s <_ %s' % (Lg, Rg), leaves=lv, atoms=[r])
    e1 = D(w, A, 'divrecd', [D(w, A, 'recnd', [xr], 'X e. CC'), mc, mne], '( X / M ) = ( X x. %s )' % r)
    e3 = D(w, A, 'divrecd', [cst(w, A, 'picn', '_pi e. CC'), mc, mne], '( _pi / M ) = ( _pi x. %s )' % r)
    LgO = '-u ( %s x. ( X / M ) )' % PN
    RgO = '( -u ( ( _pi / M ) x. ( X - 1 ) ) + -u ( %s x. %s ) )' % (PN, r)
    rl, _ = w.rewrite(LgO, {'( X / M )': ('( X x. %s )' % r, e1)}, A)
    rrw, _ = w.rewrite(RgO, {'( _pi / M )': ('( _pi x. %s )' % r, e3)}, A)
    ine2 = D(w, A, 'breqtrrd', [D(w, A, 'eqbrtrd', [rl, ine], '%s <_ %s' % (LgO, Rg)), rrw], '%s <_ %s' % (LgO, RgO))
    lgr = D(w, A, 'renegcld', [exv_arg(w, A, 'N', 'X', nr, xr, mrp)], '%s e. RR' % LgO)
    B1 = '-u ( ( _pi / M ) x. ( X - 1 ) )'; B2 = '-u ( %s x. %s )' % (PN, r)
    b1r = D(w, A, 'renegcld', [D(w, A, 'remulcld', [D(w, A, 'rerpdivcld', [pr, mrp], '( _pi / M ) e. RR'), D(w, A, 'resubcld', [xr, cst(w, A, '1re', '1 e. RR')], '( X - 1 ) e. RR')], '( ( _pi / M ) x. ( X - 1 ) ) e. RR')], '%s e. RR' % B1)
    b2r = D(w, A, 'renegcld', [exv_arg(w, A, 'N', '1', nr, cst(w, A, '1re', '1 e. RR'), mrp)], '%s e. RR' % B2)
    ef = D(w, A, 'mpbid', [ine2, D(w, A, 'syl2anc', [lgr, D(w, A, 'readdcld', [b1r, b2r], '%s e. RR' % RgO), w.inst('efle')], '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (LgO, RgO, LgO, RgO))],
           '( exp ` %s ) <_ ( exp ` %s )' % (LgO, RgO))
    E1 = '( exp ` %s )' % B1
    ea = D(w, A, 'syl2anc', [D(w, A, 'recnd', [b1r], '%s e. CC' % B1), D(w, A, 'recnd', [b2r], '%s e. CC' % B2), w.inst('efadd')], '( exp ` %s ) = ( %s x. %s )' % (RgO, E1, EXv('N', '1')))
    ef2 = D(w, A, 'breqtrd', [ef, ea], '%s <_ ( %s x. %s )' % (EXv('N', 'X'), E1, EXv('N', '1')))
    pn, npr, np0 = np_facts(w, A, pp, 'N', nr, n0)
    e1r = D(w, A, 'reefcld', [b1r], '%s e. RR' % E1); e1p = D(w, A, 'rpefcld', [b1r], '%s e. RR+' % E1)
    ex1 = D(w, A, 'rpred', [exv_rp(w, A, 'N', '1', nr, cst(w, A, '1re', '1 e. RR'), mrp)], '%s e. RR' % EXv('N', '1'))
    exX = D(w, A, 'rpred', [exv_rp(w, A, 'N', 'X', nr, xr, mrp)], '%s e. RR' % EXv('N', 'X'))
    s1 = D(w, A, 'lemul2ad', [exX, D(w, A, 'remulcld', [e1r, ex1], '( %s x. %s ) e. RR' % (E1, EXv('N', '1'))), npr, np0, ef2],
           '( ( N ^ P ) x. %s ) <_ ( ( N ^ P ) x. ( %s x. %s ) )' % (EXv('N', 'X'), E1, EXv('N', '1')))
    m12 = D(w, A, 'mul12d', [D(w, A, 'recnd', [npr], '( N ^ P ) e. CC'), D(w, A, 'recnd', [e1r], '%s e. CC' % E1), D(w, A, 'recnd', [ex1], '%s e. CC' % EXv('N', '1'))],
            '( ( N ^ P ) x. ( %s x. %s ) ) = ( %s x. ( ( N ^ P ) x. %s ) )' % (E1, EXv('N', '1'), E1, EXv('N', '1')))
    tb = D(w, A, 'syl3anc', [D(w, A, 'simp1', [], L.MP), D(w, A, '3jca', [cst(w, A, '1rp', '1 e. RR+'), cst(w, A, '1re', '1 e. RR'), D(w, A, 'leidd', [cst(w, A, '1re', '1 e. RR')], '1 <_ 1')], '( 1 e. RR+ /\\ 1 e. RR /\\ 1 <_ 1 )'), nn, w.inst('zl3tb0')],
           '( ( N ^ P ) x. %s ) <_ ( %s x. ( ( 1 / 2 ) ^ N ) )' % (EXv('N', '1'), KE('1')))
    s2_rhs = D(w, A, 'remulcld', [D(w, A, 'reefcld', [D(w, A, 'rereccld', [D(w, A, 'remulcld', [pr, D(w, A, 'rerpdivcld', [cst(w, A, '1re', '1 e. RR'), mrp], '( 1 / M ) e. RR')], '( _pi x. ( 1 / M ) ) e. RR'),
                                                                                             D(w, A, 'gt0ne0d', [D(w, A, 'mulgt0d', [pr, D(w, A, 'rerpdivcld', [cst(w, A, '1re', '1 e. RR'), mrp], '( 1 / M ) e. RR'), cst(w, A, 'pipos', '0 < _pi'), D(w, A, 'rpgt0d', [rr], '0 < ( 1 / M )')], '0 < ( _pi x. ( 1 / M ) )')], '( _pi x. ( 1 / M ) ) =/= 0')],
                                                                         '( 1 / ( _pi x. ( 1 / M ) ) ) e. RR')], '%s e. RR' % KE('1')),
                                                   D(w, A, 'reexpcld', [cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), D(w, A, 'nnnn0d', [nn], 'N e. NN0')], '( ( 1 / 2 ) ^ N ) e. RR')], '( %s x. ( ( 1 / 2 ) ^ N ) ) e. RR' % KE('1'))
    s2 = D(w, A, 'lemul2ad', [D(w, A, 'remulcld', [npr, ex1], '( ( N ^ P ) x. %s ) e. RR' % EXv('N', '1')), s2_rhs,
                              e1r, D(w, A, 'rpge0d', [e1p], '0 <_ %s' % E1), tb],
           '( %s x. ( ( N ^ P ) x. %s ) ) <_ ( %s x. ( %s x. ( ( 1 / 2 ) ^ N ) ) )' % (E1, EXv('N', '1'), E1, KE('1')))
    ra = D(w, A, 'remulcld', [npr, exX], '( ( N ^ P ) x. %s ) e. RR' % EXv('N', 'X'))
    rb = D(w, A, 'remulcld', [e1r, D(w, A, 'remulcld', [npr, ex1], '( ( N ^ P ) x. %s ) e. RR' % EXv('N', '1'))], '( %s x. ( ( N ^ P ) x. %s ) ) e. RR' % (E1, EXv('N', '1')))
    rc = D(w, A, 'remulcld', [e1r, s2_rhs], '( %s x. ( %s x. ( ( 1 / 2 ) ^ N ) ) ) e. RR' % (E1, KE('1')))
    w.qed([ra, rb, rc, D(w, A, 'breqtrd', [s1, m12], '( ( N ^ P ) x. %s ) <_ ( %s x. ( ( N ^ P ) x. %s ) )' % (EXv('N', 'X'), E1, EXv('N', '1'))), s2], 'letrd', S['zl3tdc'])
    go(w)


def ta_facts(w, A, ta):
    mp = D(w, A, 'simpld', [ta], L.MP)
    r = D(w, A, 'simprd', [ta], '( C : NN --> CC /\\ A. i e. NN ( abs ` ( C ` i ) ) <_ 1 )')
    return (D(w, A, 'simpld', [mp], 'M e. NN'), D(w, A, 'simprd', [mp], 'P e. { 0 , 1 }'), D(w, A, 'simpld', [r], 'C : NN --> CC'),
            D(w, A, 'simprd', [r], 'A. i e. NN ( abs ` ( C ` i ) ) <_ 1'), mp)


def c_bnd(w, A, bnd, N, nn):
    sub = w.s([w.s([w.s([], 'fveq2', '( i = %s -> ( C ` i ) = ( C ` %s ) )' % (N, N))], 'fveq2d', '( i = %s -> ( abs ` ( C ` i ) ) = ( abs ` ( C ` %s ) ) )' % (N, N))],
              'breq1d', '( i = %s -> ( ( abs ` ( C ` i ) ) <_ 1 <-> ( abs ` ( C ` %s ) ) <_ 1 ) )' % (N, N))
    return D(w, A, 'rspcdva', [sub, bnd, nn], '( abs ` ( C ` %s ) ) <_ 1' % N)


def exv_rp0(w, A, n, x, nr, xr, mrp):
    return exv_rp(w, A, n, x, nr, xr, mrp)


# ---------------------------------------------------------------- zl3tab
if want('zl3tab'):
    w = W('zl3tab', 'A theta term with a coefficient bounded by 1 is at most ` N ^ P e ^ ( -pi N ^ 2 X / M ) ` in absolute value.')
    A, Cc = ante_of('zl3tab')
    ta = D(w, A, 'simp1', [], L.TA); xr = D(w, A, 'simp2', [], 'X e. RR'); nn = D(w, A, 'simp3', [], 'N e. NN')
    mn, pp, cf, bnd, mp = ta_facts(w, A, ta)
    mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+'); nr = D(w, A, 'nnred', [nn], 'N e. RR')
    n0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), nr, D(w, A, 'nngt0d', [nn], '0 < N')], '0 <_ N')
    pn, npr, np0 = np_facts(w, A, pp, 'N', nr, n0)
    ex = exv_rp(w, A, 'N', 'X', nr, xr, mrp)
    Q = '( ( N ^ P ) x. %s )' % EXv('N', 'X')
    qr = D(w, A, 'remulcld', [npr, D(w, A, 'rpred', [ex], '%s e. RR' % EXv('N', 'X'))], '%s e. RR' % Q)
    q0 = D(w, A, 'mulge0d', [npr, D(w, A, 'rpred', [ex], '%s e. RR' % EXv('N', 'X')), np0, D(w, A, 'rpge0d', [ex], '0 <_ %s' % EXv('N', 'X'))], '0 <_ %s' % Q)
    cn = D(w, A, 'ffvelcdmd', [cf, nn], '( C ` N ) e. CC')
    tc = D(w, A, 'mulcld', [cn, D(w, A, 'recnd', [qr], '%s e. CC' % Q)], '%s e. CC' % TT('N', 'X'))
    ab = D(w, A, 'eqtrd', [D(w, A, 'absmuld', [cn, D(w, A, 'recnd', [qr], '%s e. CC' % Q)], '( abs ` %s ) = ( ( abs ` ( C ` N ) ) x. ( abs ` %s ) )' % (TT('N', 'X'), Q)),
                           D(w, A, 'oveq2d', [D(w, A, 'absidd', [qr, q0], '( abs ` %s ) = %s' % (Q, Q))], '( ( abs ` ( C ` N ) ) x. ( abs ` %s ) ) = ( ( abs ` ( C ` N ) ) x. %s )' % (Q, Q))],
           '( abs ` %s ) = ( ( abs ` ( C ` N ) ) x. %s )' % (TT('N', 'X'), Q))
    acr = D(w, A, 'abscld', [cn], '( abs ` ( C ` N ) ) e. RR')
    le = D(w, A, 'lemul1ad', [acr, cst(w, A, '1re', '1 e. RR'), qr, q0, c_bnd(w, A, bnd, 'N', nn)], '( ( abs ` ( C ` N ) ) x. %s ) <_ ( 1 x. %s )' % (Q, Q))
    le2 = D(w, A, 'breqtrd', [D(w, A, 'eqbrtrd', [ab, le], '( abs ` %s ) <_ ( 1 x. %s )' % (TT('N', 'X'), Q)), D(w, A, 'mullidd', [D(w, A, 'recnd', [qr], '%s e. CC' % Q)], '( 1 x. %s ) = %s' % (Q, Q))],
              '( abs ` %s ) <_ %s' % (TT('N', 'X'), Q))
    w.qed([tc, le2], 'jca', S['zl3tab'])
    go(w)


def vsub(w, fn, v, N):
    """closed ( v = N -> fn(v) = fn(N) )"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, N, v, N))
    st, new = w.rewrite(fn(v), {v: (N, idst)}, '%s = %s' % (v, N))
    assert new == fn(N), (new, fn(N))
    return st


def fv1(w, Ac, bnd, dom, fn, arg, argmem, vex, sub=None):
    """( Ac -> ( ( bnd e. dom |-> fn(bnd) ) ` arg ) = fn(arg) ), argmem: ( Ac -> arg e. dom )"""
    F = '( %s e. %s |-> %s )' % (bnd, dom, fn(bnd))
    st = w.s([sub or vsub(w, fn, bnd, arg), w.s([], 'eqid', '%s = %s' % (F, F)), (w.s(vex[1], vex[0], '%s e. _V' % fn(arg)) if isinstance(vex, tuple) else w.s([], vex, '%s e. _V' % fn(arg)))], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (arg, dom, F, arg, fn(arg)))
    return D(w, Ac, 'syl', [argmem, st], '( %s ` %s ) = %s' % (F, arg, fn(arg)))


def icore(w, A, er):
    U = '( E [,) +oo )'
    ur = D(w, A, 'syl2anc', [er, cst(w, A, 'pnfxr', '+oo e. RR*'), w.inst('icossre')], '%s C_ RR' % U)
    return ur, D(w, A, 'sstrd', [ur, cst(w, A, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % U)


def ta_ctx(w, A, ta):
    """closure-friendly facts under A"""
    mn, pp, cf, bnd, mp = ta_facts(w, A, ta)
    return mn, pp, cf, bnd, D(w, A, 'nnrpd', [mn], 'M e. RR+')


# ---------------------------------------------------------------- zl3thu
if want('zl3thu'):
    w = W('zl3thu', 'The theta series is continuous on ` [ E , +oo ) ` , ` 0 < E ` : the partial sums converge uniformly ( ~ uhlim , majorant ~ zl3tb0 ) and ~ ulmcn .')
    A, Cc = ante_of('zl3thu')
    ta = D(w, A, 'simpl', [], L.TA); erp = D(w, A, 'simpr', [], 'E e. RR+'); er = D(w, A, 'rpred', [erp], 'E e. RR')
    mn, pp, cf, bnd, mrp = ta_ctx(w, A, ta)
    U = '( E [,) +oo )'
    ur, uc = icore(w, A, er)
    uex = w.s([], 'ovex', '%s e. _V' % U)
    TTn = lambda n: (lambda x: TT(n, x))
    inner = lambda n: '( x e. %s |-> %s )' % (U, TT(n, 'x'))
    F = '( n e. NN |-> %s )' % inner('n')
    HH = lambda n: '( %s x. ( ( 1 / 2 ) ^ %s ) )' % (KE('E'), n)
    Hm = '( n e. NN |-> %s )' % HH('n')
    # membership of an element of U
    def xin(Ac, xv, xU, erc):
        bi = D(w, Ac, 'syl', [erc, w.inst('elicopnf')], '( %s e. %s <-> ( %s e. RR /\\ E <_ %s ) )' % (xv, U, xv, xv))
        both = D(w, Ac, 'mpbid', [xU, bi], '( %s e. RR /\\ E <_ %s )' % (xv, xv))
        return D(w, Ac, 'simpld', [both], '%s e. RR' % xv), D(w, Ac, 'simprd', [both], 'E <_ %s' % xv)
    # F : NN --> ( CC ^m U )
    An = '( %s /\\ n e. NN )' % A
    Anx = '( %s /\\ x e. %s )' % (An, U)
    xr, _ = xin(Anx, 'x', w.s([], 'simpr', '( %s -> x e. %s )' % (Anx, U)), w.s([er], 'ad2antrr', '( %s -> E e. RR )' % Anx))
    tcl = D(w, Anx, 'simpld', [D(w, Anx, 'syl3anc', [w.s([ta], 'ad2antrr', '( %s -> %s )' % (Anx, L.TA)), xr, w.s([], 'simplr', '( %s -> n e. NN )' % Anx), w.inst('zl3tab')],
                                 '( %s e. CC /\\ ( abs ` %s ) <_ ( ( n ^ P ) x. %s ) )' % (TT('n', 'x'), TT('n', 'x'), EXv('n', 'x')))], '%s e. CC' % TT('n', 'x'))
    iff = D(w, An, 'fmptd', [tcl, w.s([], 'eqid', '%s = %s' % (inner('n'), inner('n')))], '%s : %s --> CC' % (inner('n'), U))
    elm = w.s([w.s([w.s([], 'cnex', 'CC e. _V'), uex], 'pm3.2i', '( CC e. _V /\\ %s e. _V )' % U), w.inst('elmapg')], 'ax-mp', '( %s e. ( CC ^m %s ) <-> %s : %s --> CC )' % (inner('n'), U, inner('n'), U))
    ime = D(w, An, 'mpbird', [iff, w.s([elm], 'a1i', '( %s -> ( %s e. ( CC ^m %s ) <-> %s : %s --> CC ) )' % (An, inner('n'), U, inner('n'), U))], '%s e. ( CC ^m %s )' % (inner('n'), U))
    fF = D(w, A, 'fmptd', [ime, w.s([], 'eqid', '%s = %s' % (F, F))], '%s : NN --> ( CC ^m %s )' % (F, U))
    # the majorant
    kerp = D(w, A, 'rpefcld', [D(w, A, 'rereccld', [D(w, A, 'remulcld', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'rerpdivcld', [er, mrp], '( E / M ) e. RR')], '( _pi x. ( E / M ) ) e. RR'),
                                                      D(w, A, 'gt0ne0d', [D(w, A, 'mulgt0d', [cst(w, A, 'pire', '_pi e. RR'), D(w, A, 'rerpdivcld', [er, mrp], '( E / M ) e. RR'), cst(w, A, 'pipos', '0 < _pi'),
                                                                                             D(w, A, 'rpgt0d', [D(w, A, 'rpdivcld', [erp, mrp], '( E / M ) e. RR+')], '0 < ( E / M )')], '0 < ( _pi x. ( E / M ) )')], '( _pi x. ( E / M ) ) =/= 0')],
                                '( 1 / ( _pi x. ( E / M ) ) ) e. RR')], '%s e. RR+' % KE('E'))
    ker = D(w, A, 'rpred', [kerp], '%s e. RR' % KE('E'))
    def hval(Ac, v, vn):
        vr = D(w, Ac, 'reexpcld', [cst(w, Ac, 'halfre', '( 1 / 2 ) e. RR'), D(w, Ac, 'nnnn0d', [vn], '%s e. NN0' % v)], '( ( 1 / 2 ) ^ %s ) e. RR' % v)
        hr = D(w, Ac, 'remulcld', [ad(w, Ac, ker, '%s e. RR' % KE('E')), vr], '%s e. RR' % HH(v))
        return fv1(w, Ac, 'n', 'NN', HH, v, vn, 'ovex'), hr, vr
    Hn = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    _, hrn, _ = hval(An, 'n', Hn)
    hf = D(w, A, 'fmptd', [hrn, w.s([], 'eqid', '%s = %s' % (Hm, Hm))], '%s : NN --> RR' % Hm)
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    hvk, hrk, vrk = hval(Ak, 'k', kn)
    h0k = D(w, Ak, 'mulge0d', [ad(w, Ak, ker, '%s e. RR' % KE('E')), vrk, D(w, Ak, 'rpge0d', [ad(w, Ak, kerp, '%s e. RR+' % KE('E'))], '0 <_ %s' % KE('E')),
                               D(w, Ak, 'expge0d', [cst(w, Ak, 'halfre', '( 1 / 2 ) e. RR'), D(w, Ak, 'nnnn0d', [kn], 'k e. NN0'), cst(w, Ak, 'halfge0', '0 <_ ( 1 / 2 )')], '0 <_ ( ( 1 / 2 ) ^ k )')], '0 <_ %s' % HH('k'))
    habs = D(w, Ak, 'eqtrd', [D(w, Ak, 'fveq2d', [hvk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (Hm, HH('k'))), D(w, Ak, 'absidd', [hrk, h0k], '( abs ` %s ) = %s' % (HH('k'), HH('k')))],
             '( abs ` ( %s ` k ) ) = %s' % (Hm, HH('k')))
    hle = D(w, Ak, 'eqbrtrd', [habs, D(w, Ak, 'leidd', [hrk], '%s <_ %s' % (HH('k'), HH('k')))], '( abs ` ( %s ` k ) ) <_ %s' % (Hm, HH('k')))
    hkc = D(w, Ak, 'eqeltrd', [hvk, D(w, Ak, 'recnd', [hrk], '%s e. CC' % HH('k'))], '( %s ` k ) e. CC' % Hm)
    ms = D(w, A, 'simpld', [D(w, A, 'zl3mser', [ker, cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), cst(w, A, 'halfge0', '0 <_ ( 1 / 2 )'), cst(w, A, 'halflt1', '( 1 / 2 ) < 1'), hkc, hle],
                                '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) )' % (Hm, Hm, KE('E')))], 'seq 1 ( + , %s ) e. dom ~~>' % Hm)
    # values of F
    def fval(Ac, v, vn, y, yU):
        a = D(w, Ac, 'fveq1d', [fv1(w, Ac, 'n', 'NN', inner, v, vn, ('mptex', [uex]))], '( ( %s ` %s ) ` %s ) = ( %s ` %s )' % (F, v, y, inner(v), y))
        b = fv1(w, Ac, 'x', U, TTn(v), y, yU, 'ovex')
        return D(w, Ac, 'eqtrd', [a, b], '( ( %s ` %s ) ` %s ) = %s' % (F, v, y, TT(v, y)))
    Ajy = '( %s /\\ ( j e. NN /\\ y e. %s ) )' % (A, U)
    jn = w.s([], 'simprl', '( %s -> j e. NN )' % Ajy); yU = w.s([], 'simprr', '( %s -> y e. %s )' % (Ajy, U))
    yr, ey = xin(Ajy, 'y', yU, ad(w, Ajy, er, 'E e. RR'))
    tab = D(w, Ajy, 'simprd', [D(w, Ajy, 'syl3anc', [ad(w, Ajy, ta, L.TA), yr, jn, w.inst('zl3tab')], '( %s e. CC /\\ ( abs ` %s ) <_ ( ( j ^ P ) x. %s ) )' % (TT('j', 'y'), TT('j', 'y'), EXv('j', 'y')))],
              '( abs ` %s ) <_ ( ( j ^ P ) x. %s )' % (TT('j', 'y'), EXv('j', 'y')))
    tb = D(w, Ajy, 'syl3anc', [D(w, Ajy, 'simpld', [ad(w, Ajy, ta, L.TA)], L.MP), D(w, Ajy, '3jca', [ad(w, Ajy, erp, 'E e. RR+'), yr, ey], '( E e. RR+ /\\ y e. RR /\\ E <_ y )'), jn, w.inst('zl3tb0')],
           '( ( j ^ P ) x. %s ) <_ %s' % (EXv('j', 'y'), HH('j')))
    mnj = ad(w, Ajy, mrp, 'M e. RR+'); jr = D(w, Ajy, 'nnred', [jn], 'j e. RR')
    j0 = D(w, Ajy, 'ltled', [cst(w, Ajy, '0re', '0 e. RR'), jr, D(w, Ajy, 'nngt0d', [jn], '0 < j')], '0 <_ j')
    _, jpr, _ = np_facts(w, Ajy, ad(w, Ajy, pp, 'P e. { 0 , 1 }'), 'j', jr, j0)
    hvj, hrj, _ = hval(Ajy, 'j', jn)
    tcj = D(w, Ajy, 'simpld', [D(w, Ajy, 'syl3anc', [ad(w, Ajy, ta, L.TA), yr, jn, w.inst('zl3tab')], '( %s e. CC /\\ ( abs ` %s ) <_ ( ( j ^ P ) x. %s ) )' % (TT('j', 'y'), TT('j', 'y'), EXv('j', 'y')))], '%s e. CC' % TT('j', 'y'))
    le = D(w, Ajy, 'letrd', [D(w, Ajy, 'abscld', [tcj], '( abs ` %s ) e. RR' % TT('j', 'y')), D(w, Ajy, 'remulcld', [jpr, D(w, Ajy, 'rpred', [exv_rp(w, Ajy, 'j', 'y', jr, yr, mnj)], '%s e. RR' % EXv('j', 'y'))], '( ( j ^ P ) x. %s ) e. RR' % EXv('j', 'y')),
                             hrj, tab, tb], '( abs ` %s ) <_ %s' % (TT('j', 'y'), HH('j')))
    bj = D(w, Ajy, 'breq12d' if False else 'eqbrtrd', [D(w, Ajy, 'fveq2d', [fval(Ajy, 'j', jn, 'y', yU)], '( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s )' % (F, TT('j', 'y'))), D(w, Ajy, 'breqtrrd', [le, hvj], '( abs ` %s ) <_ ( %s ` j )' % (TT('j', 'y'), Hm))],
           '( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (F, Hm))
    ball = D(w, A, 'ralrimivva', [bj], 'A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (U, F, Hm))
    LIM = '( z e. %s |-> sum_ k e. NN ( ( %s ` k ) ` z ) )' % (U, F)
    ul = D(w, A, 'syl2anc', [fF, D(w, A, '3jca', [hf, ms, ball], '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (Hm, Hm, U, F, Hm)), w.inst('uhlim')],
           'seq 1 ( oF + , %s ) ( ~~>u ` %s ) %s' % (F, U, LIM))
    # the partial sums are continuous
    SQ = 'seq 1 ( oF + , %s )' % F
    Am = '( %s /\\ m e. NN )' % A
    mn_ = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
    ps = D(w, Am, 'syl2anc', [ad(w, Am, fF, '%s : NN --> ( CC ^m %s )' % (F, U)), mn_, w.inst('uhps')], '( %s ` m ) = ( z e. %s |-> sum_ k e. ( 1 ... m ) ( ( %s ` k ) ` z ) )' % (SQ, U, F))
    Amz = '( %s /\\ z e. %s )' % (Am, U)
    Amzk = '( %s /\\ k e. ( 1 ... m ) )' % Amz
    kn2 = D(w, Amzk, 'elfznn', [w.s([], 'simpr', '( %s -> k e. ( 1 ... m ) )' % Amzk)], 'k e. NN') if False else \
        w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... m ) )' % Amzk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Amzk)
    fvk = fval(Amzk, 'k', kn2, 'z', w.s([], 'simplr', '( %s -> z e. %s )' % (Amzk, U)))
    se = D(w, Amz, 'sumeq2dv', [fvk], 'sum_ k e. ( 1 ... m ) ( ( %s ` k ) ` z ) = sum_ k e. ( 1 ... m ) %s' % (F, TT('k', 'z')))
    me = D(w, Am, 'mpteq2dva', [se], '( z e. %s |-> sum_ k e. ( 1 ... m ) ( ( %s ` k ) ` z ) ) = ( z e. %s |-> sum_ k e. ( 1 ... m ) %s )' % (U, F, U, TT('k', 'z')))
    Amk = '( %s /\\ k e. ( 1 ... m ) )' % Am
    kn3 = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... m ) )' % Amk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Amk)
    kr3 = D(w, Amk, 'nnred', [kn3], 'k e. RR')
    k03 = D(w, Amk, 'ltled', [cst(w, Amk, '0re', '0 e. RR'), kr3, D(w, Amk, 'nngt0d', [kn3], '0 < k')], '0 <_ k')
    _, kpr, _ = np_facts(w, Amk, w.s([pp], 'ad2antrr', '( %s -> P e. { 0 , 1 } )' % Amk), 'k', kr3, k03)
    ck = D(w, Amk, 'ffvelcdmd', [w.s([cf], 'ad2antrr', '( %s -> C : NN --> CC )' % Amk), kn3], '( C ` k ) e. CC')
    clk = Closure(w, Amk, {'( C ` k )': ck, '( k ^ P )': D(w, Amk, 'recnd', [kpr], '( k ^ P ) e. CC'), 'M': w.s([mrp], 'ad2antrr', '( %s -> M e. RR+ )' % Amk),
                           '( _pi x. ( k ^ 2 ) )': D(w, Amk, 'mulcld', [cst(w, Amk, 'picn', '_pi e. CC'), D(w, Amk, 'sqcld', [D(w, Amk, 'nncnd', [kn3], 'k e. CC')], '( k ^ 2 ) e. CC')], '( _pi x. ( k ^ 2 ) ) e. CC')})
    cz = cont(w, Amk, U, TT('k', 'z'), clk, w.s([uc], 'ad2antrr', '( %s -> %s C_ CC )' % (Amk, U)), x='z')
    fsc = D(w, Am, 'zl3fsc', [ad(w, Am, uc, '%s C_ CC' % U), D(w, Am, 'fzfid', [], '( 1 ... m ) e. Fin'), cz], '( z e. %s |-> sum_ k e. ( 1 ... m ) %s ) e. ( %s -cn-> CC )' % (U, TT('k', 'z'), U))
    psc = D(w, Am, 'eqeltrd', [D(w, Am, 'eqtrd', [ps, me], '( %s ` m ) = ( z e. %s |-> sum_ k e. ( 1 ... m ) %s )' % (SQ, U, TT('k', 'z'))), fsc], '( %s ` m ) e. ( %s -cn-> CC )' % (SQ, U))
    fn = D(w, A, 'ffnd', [D(w, A, 'syl', [fF, w.inst('uhpsf')], '%s : NN --> ( CC ^m %s )' % (SQ, U))], '%s Fn NN' % SQ)
    fcn = D(w, A, 'mpbird', [D(w, A, 'jca', [fn, D(w, A, 'ralrimiva', [psc], 'A. m e. NN ( %s ` m ) e. ( %s -cn-> CC )' % (SQ, U))], '( %s Fn NN /\\ A. m e. NN ( %s ` m ) e. ( %s -cn-> CC ) )' % (SQ, SQ, U)),
                             cst(w, A, 'ffnfv', '( %s : NN --> ( %s -cn-> CC ) <-> ( %s Fn NN /\\ A. m e. NN ( %s ` m ) e. ( %s -cn-> CC ) ) )' % (SQ, U, SQ, SQ, U))], '%s : NN --> ( %s -cn-> CC )' % (SQ, U))
    lc = D(w, A, 'ulmcn', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), fcn, ul], '%s e. ( %s -cn-> CC )' % (LIM, U))
    # the limit is the theta series
    Az = '( %s /\\ z e. %s )' % (A, U)
    Azk = '( %s /\\ k e. NN )' % Az
    fvk2 = fval(Azk, 'k', w.s([], 'simpr', '( %s -> k e. NN )' % Azk), 'z', w.s([], 'simplr', '( %s -> z e. %s )' % (Azk, U)))
    se2 = D(w, Az, 'sumeq2dv', [fvk2], 'sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN %s' % (F, TT('k', 'z')))
    cbs = w.s([vsub(w, lambda v: TT(v, 'z'), 'k', 'n')], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (TT('k', 'z'), TT('n', 'z')))
    se3 = D(w, Az, 'eqtrd', [se2, w.s([cbs], 'a1i', '( %s -> sum_ k e. NN %s = sum_ n e. NN %s )' % (Az, TT('k', 'z'), TT('n', 'z')))], 'sum_ k e. NN ( ( %s ` k ) ` z ) = %s' % (F, THP('C', 'z', 'P')))
    me2 = D(w, A, 'mpteq2dva', [se3], '%s = ( z e. %s |-> %s )' % (LIM, U, THP('C', 'z', 'P')))
    cbm = w.s([vsub(w, lambda v: THP('C', v, 'P'), 'z', 'x')], 'cbvmptv', '( z e. %s |-> %s ) = ( x e. %s |-> %s )' % (U, THP('C', 'z', 'P'), U, THP('C', 'x', 'P')))
    w.qed([D(w, A, 'eqtrd', [me2, w.s([cbm], 'a1i', '( %s -> ( z e. %s |-> %s ) = ( x e. %s |-> %s ) )' % (A, U, THP('C', 'z', 'P'), U, THP('C', 'x', 'P')))],
             '%s = ( x e. %s |-> %s )' % (LIM, U, THP('C', 'x', 'P'))), lc], 'eqeltrrd', S['zl3thu'])
    go(w)


# ---------------------------------------------------------------- zl3fsc
if want('zl3fsc'):
    w = W('zl3fsc', 'A finite sum of continuous functions is continuous ( ~ fsumcn through ~ cncfcn ).')
    h1 = hyp(w, '1', 'zl3fsc.1', '( ph -> X C_ CC )'); h2 = hyp(w, '2', 'zl3fsc.2', '( ph -> A e. Fin )')
    h3 = hyp(w, '3', 'zl3fsc.3', '( ( ph /\\ k e. A ) -> ( x e. X |-> B ) e. ( X -cn-> CC ) )')
    J = '( TopOpen ` CCfld )'
    K = '( %s |`t X )' % J
    cc = w.s([w.s([], 'eqid', '%s = %s' % (J, J)), w.s([], 'eqid', '%s = %s' % (K, K)), w.s([], 'eqid', '( %s |`t CC ) = ( %s |`t CC )' % (J, J))], 'cncfcn',
             '( ( X C_ CC /\\ CC C_ CC ) -> ( X -cn-> CC ) = ( %s Cn ( %s |`t CC ) ) )' % (K, J))
    rid = w.s([w.s([w.s([], 'unicntop', 'CC = U. %s' % J)], 'restid', '( %s e. Top -> ( %s |`t CC ) = %s )' % (J, J, J)), w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'cnfldtop', '%s e. Top' % J)],
              'ax-mp', '( %s |`t CC ) = %s' % (J, J))
    e1 = D(w, 'ph', 'syl2anc', [h1, cst(w, 'ph', 'ssid', 'CC C_ CC'), cc], '( X -cn-> CC ) = ( %s Cn ( %s |`t CC ) )' % (K, J))
    e = D(w, 'ph', 'eqtrd', [e1, D(w, 'ph', 'oveq2d', [cst(w, 'ph', 'eqid', '%s = %s' % (J, J)) if False else w.s([rid], 'a1i', '( ph -> ( %s |`t CC ) = %s )' % (J, J))], '( %s Cn ( %s |`t CC ) ) = ( %s Cn %s )' % (K, J, K, J))],
          '( X -cn-> CC ) = ( %s Cn %s )' % (K, J))
    Ak = '( ph /\\ k e. A )'
    t3 = D(w, Ak, 'eleqtrd', [h3, ad(w, Ak, e, '( X -cn-> CC ) = ( %s Cn %s )' % (K, J))], '( x e. X |-> B ) e. ( %s Cn %s )' % (K, J))
    ton = D(w, 'ph', 'syl2anc', [cst(w, 'ph', 'cnfldtopon', '%s e. ( TopOn ` CC )' % J) if False else w.s([w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'cnfldtopon', '%s e. ( TopOn ` CC )' % J)], 'a1i', '( ph -> %s e. ( TopOn ` CC ) )' % J),
                                 h1, w.inst('resttopon')], '%s e. ( TopOn ` X )' % K)
    fs = D(w, 'ph', 'fsumcn', [w.s([], 'eqid', '%s = %s' % (J, J)), ton, h2, t3], '( x e. X |-> sum_ k e. A B ) e. ( %s Cn %s )' % (K, J))
    w.qed([fs, e], 'eleqtrrd', S['zl3fsc'])
    go(w)


def ke1(w, A, mrp):
    """( A -> KE ( 1 ) e. RR+ )"""
    mr = D(w, A, 'rpreccld', [mrp], '( 1 / M ) e. RR+')
    a = D(w, A, 'rpmulcld', [cst(w, A, 'pirp', '_pi e. RR+'), mr], '( _pi x. ( 1 / M ) ) e. RR+')
    return D(w, A, 'rpefcld', [D(w, A, 'rpred', [D(w, A, 'rpreccld', [a], '( 1 / ( _pi x. ( 1 / M ) ) ) e. RR+')], '( 1 / ( _pi x. ( 1 / M ) ) ) e. RR')], '%s e. RR+' % KE('1'))


# ---------------------------------------------------------------- zl3thd
if want('zl3thd'):
    w = W('zl3thd', 'Exponential decay of the theta series on ` [ 1 , +oo ) ` ( ~ zl3tdc , ~ zl3mser ).')
    A, Cc = ante_of('zl3thd')
    ta = D(w, A, 'simpl', [], L.TA); xr = D(w, A, 'simprl', [], 'X e. RR'); x1 = D(w, A, 'simprr', [], '1 <_ X')
    mn, pp, cf, bnd, mrp = ta_ctx(w, A, ta)
    u = '( _pi / M )'
    ur = D(w, A, 'rerpdivcld', [cst(w, A, 'pire', '_pi e. RR'), mrp], '%s e. RR' % u)
    B1 = '-u ( %s x. ( X - 1 ) )' % u
    b1r = D(w, A, 'renegcld', [D(w, A, 'remulcld', [ur, D(w, A, 'resubcld', [xr, cst(w, A, '1re', '1 e. RR')], '( X - 1 ) e. RR')], '( %s x. ( X - 1 ) ) e. RR' % u)], '%s e. RR' % B1)
    E1 = '( exp ` %s )' % B1
    e1r = D(w, A, 'reefcld', [b1r], '%s e. RR' % E1)
    kp = ke1(w, A, mrp); kr = D(w, A, 'rpred', [kp], '%s e. RR' % KE('1'))
    B = '( %s x. %s )' % (E1, KE('1'))
    br = D(w, A, 'remulcld', [e1r, kr], '%s e. RR' % B)
    F = '( n e. NN |-> %s )' % TT('n', 'X')
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    fvk = fv1(w, Ak, 'n', 'NN', lambda v: TT(v, 'X'), 'k', kn, 'ovex')
    tabk = D(w, Ak, 'syl3anc', [ad(w, Ak, ta, L.TA), ad(w, Ak, xr, 'X e. RR'), kn, w.inst('zl3tab')], '( %s e. CC /\\ ( abs ` %s ) <_ ( ( k ^ P ) x. %s ) )' % (TT('k', 'X'), TT('k', 'X'), EXv('k', 'X')))
    fkc = D(w, Ak, 'eqeltrd', [fvk, D(w, Ak, 'simpld', [tabk], '%s e. CC' % TT('k', 'X'))], '( %s ` k ) e. CC' % F)
    tdc = D(w, Ak, 'syl3anc', [D(w, Ak, 'simpld', [ad(w, Ak, ta, L.TA)], L.MP), D(w, Ak, 'jca', [ad(w, Ak, xr, 'X e. RR'), ad(w, Ak, x1, '1 <_ X')], '( X e. RR /\\ 1 <_ X )'), kn, w.inst('zl3tdc')],
            '( ( k ^ P ) x. %s ) <_ ( %s x. ( %s x. ( ( 1 / 2 ) ^ k ) ) )' % (EXv('k', 'X'), E1.replace('( _pi / M )', '( _pi / M )'), KE('1')))
    kr_ = D(w, Ak, 'nnred', [kn], 'k e. RR'); k0 = D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), kr_, D(w, Ak, 'nngt0d', [kn], '0 < k')], '0 <_ k')
    _, kpr, _ = np_facts(w, Ak, ad(w, Ak, pp, 'P e. { 0 , 1 }'), 'k', kr_, k0)
    hk = D(w, Ak, 'reexpcld', [cst(w, Ak, 'halfre', '( 1 / 2 ) e. RR'), D(w, Ak, 'nnnn0d', [kn], 'k e. NN0')], '( ( 1 / 2 ) ^ k ) e. RR')
    ma = D(w, Ak, 'mulassd', [D(w, Ak, 'recnd', [ad(w, Ak, e1r, '%s e. RR' % E1)], '%s e. CC' % E1), D(w, Ak, 'recnd', [ad(w, Ak, kr, '%s e. RR' % KE('1'))], '%s e. CC' % KE('1')), D(w, Ak, 'recnd', [hk], '( ( 1 / 2 ) ^ k ) e. CC')],
           '( %s x. ( ( 1 / 2 ) ^ k ) ) = ( %s x. ( %s x. ( ( 1 / 2 ) ^ k ) ) )' % (B, E1, KE('1')))
    le = D(w, Ak, 'letrd', [D(w, Ak, 'abscld', [D(w, Ak, 'simpld', [tabk], '%s e. CC' % TT('k', 'X'))], '( abs ` %s ) e. RR' % TT('k', 'X')),
                            D(w, Ak, 'remulcld', [kpr, D(w, Ak, 'rpred', [exv_rp(w, Ak, 'k', 'X', kr_, ad(w, Ak, xr, 'X e. RR'), ad(w, Ak, mrp, 'M e. RR+'))], '%s e. RR' % EXv('k', 'X'))], '( ( k ^ P ) x. %s ) e. RR' % EXv('k', 'X')),
                            D(w, Ak, 'remulcld', [ad(w, Ak, br, '%s e. RR' % B), hk], '( %s x. ( ( 1 / 2 ) ^ k ) ) e. RR' % B),
                            D(w, Ak, 'simprd', [tabk], '( abs ` %s ) <_ ( ( k ^ P ) x. %s )' % (TT('k', 'X'), EXv('k', 'X'))), D(w, Ak, 'breqtrrd', [tdc, ma], '( ( k ^ P ) x. %s ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (EXv('k', 'X'), B))],
           '( abs ` %s ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (TT('k', 'X'), B))
    le2 = D(w, Ak, 'eqbrtrd', [D(w, Ak, 'fveq2d', [fvk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (F, TT('k', 'X'))), le], '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (F, B))
    ms = D(w, A, 'simprd', [D(w, A, 'zl3mser', [br, cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), cst(w, A, 'halfge0', '0 <_ ( 1 / 2 )'), cst(w, A, 'halflt1', '( 1 / 2 ) < 1'), fkc, le2],
                                '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) )' % (F, F, B))],
           '( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) )' % (F, B))
    se = D(w, A, 'eqtrd', [D(w, A, 'sumeq2dv', [fvk], 'sum_ k e. NN ( %s ` k ) = sum_ k e. NN %s' % (F, TT('k', 'X'))),
                           w.s([w.s([vsub(w, lambda v: TT(v, 'X'), 'k', 'n')], 'cbvsumv', 'sum_ k e. NN %s = %s' % (TT('k', 'X'), THP('C', 'X', 'P')))], 'a1i', '( %s -> sum_ k e. NN %s = %s )' % (A, TT('k', 'X'), THP('C', 'X', 'P')))],
          'sum_ k e. NN ( %s ` k ) = %s' % (F, THP('C', 'X', 'P')))
    hb = D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [cst(w, A, '1mhlfehlf', '( 1 - ( 1 / 2 ) ) = ( 1 / 2 )')], '( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) = ( ( %s x. ( 1 / 2 ) ) / ( 1 / 2 ) )' % (B, B)),
                           D(w, A, 'divcan4d', [D(w, A, 'recnd', [br], '%s e. CC' % B), cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), D(w, A, 'gt0ne0d', [cst(w, A, 'halfgt0', '0 < ( 1 / 2 )')], '( 1 / 2 ) =/= 0')], '( ( %s x. ( 1 / 2 ) ) / ( 1 / 2 ) ) = %s' % (B, B))],
          '( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) = %s' % (B, B))
    # B = KT x. e ^ -u ( u X )
    UX = '-u ( %s x. X )' % u
    cl = Closure(w, A, {u: ur, 'X': xr}); cl.atom(u)
    eqx = lineq(w, A, B1, '( %s + %s )' % (u, UX), closure=cl, products=True)
    ea = D(w, A, 'eqtrd', [D(w, A, 'fveq2d', [eqx], '%s = ( exp ` ( %s + %s ) )' % (E1, u, UX)),
                           D(w, A, 'efaddd' if False else 'syl2anc', [D(w, A, 'recnd', [ur], '%s e. CC' % u), D(w, A, 'recnd', [D(w, A, 'renegcld', [D(w, A, 'remulcld', [ur, xr], '( %s x. X ) e. RR' % u)], '%s e. RR' % UX)], '%s e. CC' % UX), w.inst('efadd')],
                             '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (u, UX, u, UX))], '%s = ( ( exp ` %s ) x. ( exp ` %s ) )' % (E1, u, UX))
    EU = '( exp ` %s )' % u; EX = '( exp ` %s )' % UX
    euc = D(w, A, 'efcld', [D(w, A, 'recnd', [ur], '%s e. CC' % u)], '%s e. CC' % EU)
    exc = D(w, A, 'efcld', [D(w, A, 'recnd', [D(w, A, 'renegcld', [D(w, A, 'remulcld', [ur, xr], '( %s x. X ) e. RR' % u)], '%s e. RR' % UX)], '%s e. CC' % UX)], '%s e. CC' % EX)
    kc = D(w, A, 'recnd', [kr], '%s e. CC' % KE('1'))
    bv = chain(w, A, [B, '( ( %s x. %s ) x. %s )' % (EU, EX, KE('1')), '( %s x. ( %s x. %s ) )' % (KE('1'), EU, EX), '( ( %s x. %s ) x. %s )' % (KE('1'), EU, EX)],
               [D(w, A, 'oveq1d', [ea], '%s = ( ( %s x. %s ) x. %s )' % (B, EU, EX, KE('1'))),
                D(w, A, 'mulcomd', [D(w, A, 'mulcld', [euc, exc], '( %s x. %s ) e. CC' % (EU, EX)), kc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (EU, EX, KE('1'), KE('1'), EU, EX)),
                ('r', D(w, A, 'mulassd', [kc, euc, exc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (KE('1'), EU, EX, KE('1'), EU, EX)))])
    fin = D(w, A, 'eqtrd', [hb, bv], '( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) = ( %s x. %s )' % (B, KT, EX))
    w.qed([D(w, A, 'eqbrtrrd', [D(w, A, 'fveq2d', [se], '( abs ` sum_ k e. NN ( %s ` k ) ) = ( abs ` %s )' % (F, THP('C', 'X', 'P'))), ms],
             '( abs ` %s ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) )' % (THP('C', 'X', 'P'), B)), fin], 'breqtrd', S['zl3thd'])
    go(w)


# ---------------------------------------------------------------- zl3thph
if want('zl3thph'):
    w = W('zl3thph', 'The theta series on ` [ 1 , +oo ) ` satisfies the hypotheses of ~ zl3pih ( ~ zl3thu , ~ zl3thd ).')
    A = L.TA
    ta = D(w, A, 'id', [], A)
    mn, pp, cf, bnd, mrp = ta_ctx(w, A, ta)
    U1 = '( 1 [,) +oo )'
    GTH = L.GTH
    GX = '( x e. %s |-> %s )' % (U1, THP('C', 'x', 'P'))
    thu = D(w, A, 'sylancl', [ta, cst(w, A, '1rp', '1 e. RR+') if False else w.s([], '1rp', '1 e. RR+'), w.inst('zl3thu')], '%s e. ( %s -cn-> CC )' % (GX, U1)) if False else \
        D(w, A, 'syl2anc', [ta, cst(w, A, '1rp', '1 e. RR+'), w.inst('zl3thu')], '%s e. ( %s -cn-> CC )' % (GX, U1))
    cb = w.s([vsub(w, lambda v: THP('C', v, 'P'), 'x', 'y')], 'cbvmptv', '%s = %s' % (GX, GTH))
    gc = D(w, A, 'eqeltrd', [w.s([w.s([cb], 'eqcomi', '%s = %s' % (GTH, GX))], 'a1i', '( %s -> %s = %s )' % (A, GTH, GX)), thu], '%s e. ( %s -cn-> CC )' % (GTH, U1))
    gf = D(w, A, 'syl', [gc, w.inst('cncff')], '%s : %s --> CC' % (GTH, U1))
    U2 = '( 1 (,) +oo )'
    gr = D(w, A, 'mpd', [gc, w.s([w.s([], 'ioossico', '%s C_ %s' % (U2, U1)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (GTH, U1, GTH, U2, U2)) if False else
                         w.s([w.s([w.s([], 'ioossico', '%s C_ %s' % (U2, U1)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (GTH, U1, GTH, U2, U2))], 'a1i',
                             '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A, GTH, U1, GTH, U2, U2))], '( %s |` %s ) e. ( %s -cn-> CC )' % (GTH, U2, U2))
    u = '( _pi / M )'
    urp = D(w, A, 'rpdivcld', [cst(w, A, 'pirp', '_pi e. RR+'), mrp], '%s e. RR+' % u)
    ktp = D(w, A, 'rpmulcld', [ke1(w, A, mrp), D(w, A, 'rpefcld', [D(w, A, 'rpred', [urp], '%s e. RR' % u)], '( exp ` %s ) e. RR+' % u)], '%s e. RR+' % KT)
    Av = '( %s /\\ v e. %s )' % (A, U1)
    vU = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, U1))
    vb = D(w, Av, 'mpbid', [vU, D(w, Av, 'syl', [cst(w, Av, '1re', '1 e. RR'), w.inst('elicopnf')], '( v e. %s <-> ( v e. RR /\\ 1 <_ v ) )' % U1)], '( v e. RR /\\ 1 <_ v )')
    gv = fv1(w, Av, 'y', U1, lambda v: THP('C', v, 'P'), 'v', vU, ('sumex', []) if False else 'sumex')
    td = D(w, Av, 'syl2anc', [ad(w, Av, ta, A), vb, w.inst('zl3thd')], '( abs ` %s ) <_ ( %s x. ( exp ` -u ( %s x. v ) ) )' % (THP('C', 'v', 'P'), KT, u))
    bv = D(w, Av, 'eqbrtrd', [D(w, Av, 'fveq2d', [gv], '( abs ` ( %s ` v ) ) = ( abs ` %s )' % (GTH, THP('C', 'v', 'P'))), td], '( abs ` ( %s ` v ) ) <_ ( %s x. ( exp ` -u ( %s x. v ) ) )' % (GTH, KT, u))
    ba = D(w, A, 'ralrimiva', [bv], 'A. v e. %s ( abs ` ( %s ` v ) ) <_ ( %s x. ( exp ` -u ( %s x. v ) ) )' % (U1, GTH, KT, u))
    w.qed([D(w, A, 'jca', [gf, gr], '( %s : %s --> CC /\\ ( %s |` %s ) e. ( %s -cn-> CC ) )' % (GTH, U1, GTH, U2, U2)),
           D(w, A, '3jca', [ktp, urp, ba], '( %s e. RR+ /\\ %s e. RR+ /\\ A. v e. %s ( abs ` ( %s ` v ) ) <_ ( %s x. ( exp ` -u ( %s x. v ) ) ) )' % (KT, u, U1, GTH, KT, u))], 'jca', S['zl3thph'])
    go(w)


# ---------------------------------------------------------------- zl3mex
if want('zl3mex'):
    w = W('zl3mex', 'Series and integral exchange on a bounded interval under a summable majorant ( ~ uhlim , ~ itgulm2 , ~ itgfsum ).')
    A, Cc = ante_of('zl3mex')
    U = '( P (,) Q )'
    UHt = L.UH % (U, U)
    pq = D(w, A, 'simp1', [], '( P e. RR /\\ Q e. RR )'); uh = D(w, A, 'simp2', [], UHt); ib = D(w, A, 'simp3', [], 'A. j e. NN ( F ` j ) e. L^1')
    ff = D(w, A, 'simpld', [uh], 'F : NN --> ( CC ^m %s )' % U)
    SQ = 'seq 1 ( oF + , F )'
    LIM = '( x e. %s |-> sum_ k e. NN ( ( F ` k ) ` x ) )' % U
    ul = D(w, A, 'syl', [uh, w.inst('uhlim')], '%s ( ~~>u ` %s ) %s' % (SQ, U, LIM))
    PSi = lambda i: '( x e. %s |-> sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` x ) )' % (U, i)
    ISi = lambda i: 'S. %s sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` x ) _d x' % (U, i)
    IK = 'S. %s ( ( F ` k ) ` x ) _d x' % U
    FKM = '( x e. %s |-> ( ( F ` k ) ` x ) )' % U
    ksub = w.s([w.s([], 'fveq2', '( j = k -> ( F ` j ) = ( F ` k ) )')], 'eleq1d', '( j = k -> ( ( F ` j ) e. L^1 <-> ( F ` k ) e. L^1 ) )')
    def fkfacts(Ac, kn, lift):
        """( Ac -> ( F ` k ) : U --> CC ), ( Ac -> FKM e. L^1 )"""
        fkf = D(w, Ac, 'syl', [D(w, Ac, 'ffvelcdmd', [lift(ff, 'F : NN --> ( CC ^m %s )' % U), kn], '( F ` k ) e. ( CC ^m %s )' % U), w.inst('elmapi')], '( F ` k ) : %s --> CC' % U)
        fkl = D(w, Ac, 'rspcdva', [ksub, lift(ib, 'A. j e. NN ( F ` j ) e. L^1'), kn], '( F ` k ) e. L^1')
        return fkf, D(w, Ac, 'eqeltrrd', [D(w, Ac, 'feqmptd', [fkf], '( F ` k ) = %s' % FKM), fkl], '%s e. L^1' % FKM)
    def fsum_at(i):
        Ai = '( %s /\\ %s e. NN )' % (A, i)
        Aik = '( %s /\\ k e. ( 1 ... %s ) )' % (Ai, i)
        kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... %s ) )' % (Aik, i)), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Aik)
        _, fkml = fkfacts(Aik, kn, lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aik, f)))
        Aixk = '( %s /\\ ( x e. %s /\\ k e. ( 1 ... %s ) ) )' % (Ai, U, i)
        kn_ = w.s([w.s([], 'simprr', '( %s -> k e. ( 1 ... %s ) )' % (Aixk, i)), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Aixk)
        fkf_, _ = fkfacts(Aixk, kn_, lambda st, f: w.s([st], 'adantr' if False else 'ad2antrr', '( %s -> %s )' % (Aixk, f)))
        fxc = D(w, Aixk, 'ffvelcdmd', [fkf_, w.s([], 'simprl', '( %s -> x e. %s )' % (Aixk, U))], '( ( F ` k ) ` x ) e. CC')
        return D(w, Ai, 'itgfsum', [cst(w, Ai, 'ioombl', '%s e. dom vol' % U), D(w, Ai, 'fzfid', [], '( 1 ... %s ) e. Fin' % i), fxc, fkml],
                 '( %s e. L^1 /\\ %s = sum_ k e. ( 1 ... %s ) %s )' % (PSi(i), ISi(i), i, IK))
    # partial sums as a mapping
    sqf = D(w, A, 'syl', [ff, w.inst('uhpsf')], '%s : NN --> ( CC ^m %s )' % (SQ, U))
    dfn = D(w, A, 'mpbid', [D(w, A, 'ffnd', [sqf], '%s Fn NN' % SQ), cst(w, A, 'dffn5', '( %s Fn NN <-> %s = ( i e. NN |-> ( %s ` i ) ) )' % (SQ, SQ, SQ))], '%s = ( i e. NN |-> ( %s ` i ) )' % (SQ, SQ))
    Ai = '( %s /\\ i e. NN )' % A
    inn = w.s([], 'simpr', '( %s -> i e. NN )' % Ai)
    psv = D(w, Ai, 'syl2anc', [ad(w, Ai, ff, 'F : NN --> ( CC ^m %s )' % U), inn, w.inst('uhps')], '( %s ` i ) = %s' % (SQ, PSi('i')))
    PSM = '( i e. NN |-> %s )' % PSi('i')
    sqe = D(w, A, 'eqtrd', [dfn, D(w, A, 'mpteq2dva', [psv], '( i e. NN |-> ( %s ` i ) ) = %s' % (SQ, PSM))], '%s = %s' % (SQ, PSM))
    ul2 = D(w, A, 'mpbid', [ul, D(w, A, 'breq1d', [sqe], '( %s ( ~~>u ` %s ) %s <-> %s ( ~~>u ` %s ) %s )' % (SQ, U, LIM, PSM, U, LIM))], '%s ( ~~>u ` %s ) %s' % (PSM, U, LIM))
    fsi = fsum_at('i')
    vr = D(w, A, 'syl', [pq, w.inst('ioovolcl')], '( vol ` %s ) e. RR' % U)
    IS = 'S. %s sum_ k e. NN ( ( F ` k ) ` x ) _d x' % U
    IM = '( i e. NN |-> %s )' % ISi('i')
    iu = D(w, A, 'itgulm2', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), D(w, Ai, 'simpld', [fsi], '%s e. L^1' % PSi('i')), ul2, vr],
           '( %s e. L^1 /\\ %s ~~> %s )' % (LIM, IM, IS))
    cv = D(w, A, 'simprd', [iu], '%s ~~> %s' % (IM, IS))
    # the partial sums of the integrals
    J = '( m e. NN |-> S. %s ( ( F ` m ) ` x ) _d x )' % U
    Ak = '( %s /\\ k e. NN )' % A
    knk = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    fkfk, fklk = fkfacts(Ak, knk, lambda st, f: ad(w, Ak, st, f))
    Akx = '( %s /\\ x e. %s )' % (Ak, U)
    ick = D(w, Ak, 'itgcl', [fklk, D(w, Akx, 'ffvelcdmd', [ad(w, Akx, fkfk, '( F ` k ) : %s --> CC' % U), w.s([], 'simpr', '( %s -> x e. %s )' % (Akx, U))], '( ( F ` k ) ` x ) e. CC')], '%s e. CC' % IK)
    jm = w.s([w.s([w.s([w.s([], 'fveq2', '( m = k -> ( F ` m ) = ( F ` k ) )')], 'fveq1d', '( m = k -> ( ( F ` m ) ` x ) = ( ( F ` k ) ` x ) )')], 'adantr',
                  '( ( m = k /\\ x e. %s ) -> ( ( F ` m ) ` x ) = ( ( F ` k ) ` x ) )' % U)], 'itgeq2dv', '( m = k -> S. %s ( ( F ` m ) ` x ) _d x = %s )' % (U, IK))
    jv = fv1(w, Ak, 'm', 'NN', lambda v: 'S. %s ( ( F ` %s ) ` x ) _d x' % (U, v), 'k', knk, 'itgex', sub=jm)
    An = '( %s /\\ n e. NN )' % A
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    sa = w.s([w.s([], 'oveq2', '( i = n -> ( 1 ... i ) = ( 1 ... n ) )')], 'sumeq1d', '( i = n -> sum_ k e. ( 1 ... i ) ( ( F ` k ) ` x ) = sum_ k e. ( 1 ... n ) ( ( F ` k ) ` x ) )')
    sb = w.s([w.s([sa], 'adantr', '( ( i = n /\\ x e. %s ) -> sum_ k e. ( 1 ... i ) ( ( F ` k ) ` x ) = sum_ k e. ( 1 ... n ) ( ( F ` k ) ` x ) )' % U)], 'itgeq2dv', '( i = n -> %s = %s )' % (ISi('i'), ISi('n')))
    imv = fv1(w, An, 'i', 'NN', ISi, 'n', nn_, 'itgex', sub=sb)
    Ank = '( %s /\\ k e. ( 1 ... n ) )' % An
    knn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... n ) )' % Ank), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ank)
    liftk = lambda st, f: w.s([w.s([], 'simpll', '( %s -> %s )' % (Ank, A)), knn, w.s([st], 'ex', '( %s -> ( k e. NN -> %s ) )' % (A, f))], 'sylc', '( %s -> %s )' % (Ank, f))
    fss = D(w, An, 'fsumser', [liftk(jv, '( %s ` k ) = %s' % (J, IK)), D(w, An, 'eleqtrd', [nn_, cst(w, An, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'n e. ( ZZ>= ` 1 )'), liftk(ick, '%s e. CC' % IK)],
            'sum_ k e. ( 1 ... n ) %s = ( seq 1 ( + , %s ) ` n )' % (IK, J))
    fsn = D(w, An, 'simprd', [fsum_at('n')], '%s = sum_ k e. ( 1 ... n ) %s' % (ISi('n'), IK))
    eqn = D(w, An, 'eqtrd', [imv, D(w, An, 'eqtrd', [fsn, fss], '%s = ( seq 1 ( + , %s ) ` n )' % (ISi('n'), J))], '( %s ` n ) = ( seq 1 ( + , %s ) ` n )' % (IM, J))
    ce = D(w, A, 'climeq', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, 'nnex', 'NN e. _V') if False else D(w, A, 'mptexd' if False else 'a1i', [w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % IM)], '%s e. _V' % IM),
                            D(w, A, 'a1i', [w.s([], 'seqex', 'seq 1 ( + , %s ) e. _V' % J)], 'seq 1 ( + , %s ) e. _V' % J), cst(w, A, '1z', '1 e. ZZ'), eqn],
           '( %s ~~> %s <-> seq 1 ( + , %s ) ~~> %s )' % (IM, IS, J, IS))
    scv = D(w, A, 'mpbid', [cv, ce], 'seq 1 ( + , %s ) ~~> %s' % (J, IS))
    ic = D(w, A, 'isumclim', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), jv, ick, scv], 'sum_ k e. NN %s = %s' % (IK, IS))
    w.qed([ic], 'eqcomd', S['zl3mex'])
    go(w)


# ---------------------------------------------------------------- zl3tan
if want('zl3tan'):
    w = W('zl3tan', 'Tannery\'s theorem for ` ~~>r ` families: termwise limits under a summable majorant pass to the series ( ~ uhlim , ~ ulmi , ~ fsumrlim ).')
    A0, Cc = ante_of('zl3tan')
    U = 'A'
    UHt = L.UH % (U, U)
    ab_ = D(w, A0, 'simp1', [], '( A C_ RR /\\ sup ( A , RR* , < ) = +oo )')
    ar = D(w, A0, 'simpld', [ab_], 'A C_ RR'); sup = D(w, A0, 'simprd', [ab_], 'sup ( A , RR* , < ) = +oo')
    uh = D(w, A0, 'simp2', [], UHt); lm = D(w, A0, 'simp3', [], 'A. j e. NN ( F ` j ) ~~>r ( D ` j )')
    ff = D(w, A0, 'simpld', [uh], 'F : NN --> ( CC ^m A )')
    u3 = D(w, A0, 'simprd', [uh], '( H : NN --> RR /\\ seq 1 ( + , H ) e. dom ~~> /\\ A. j e. NN A. y e. A ( abs ` ( ( F ` j ) ` y ) ) <_ ( H ` j ) )')
    hf = D(w, A0, 'simp1d', [u3], 'H : NN --> RR'); hs = D(w, A0, 'simp2d', [u3], 'seq 1 ( + , H ) e. dom ~~>')
    hb = D(w, A0, 'simp3d', [u3], 'A. j e. NN A. y e. A ( abs ` ( ( F ` j ) ` y ) ) <_ ( H ` j )')
    ST = lambda t: 'sum_ k e. NN ( ( F ` k ) ` %s )' % t
    SD = 'sum_ k e. NN ( D ` k )'
    PT = lambda q, t: 'sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` %s )' % (q, t)
    PD = lambda q: 'sum_ k e. ( 1 ... %s ) ( D ` k )' % q
    GST = '( t e. A |-> %s )' % ST('t')
    FKM = '( t e. A |-> ( ( F ` k ) ` t ) )'
    # facts at an index k
    def kfacts(Ac, kn, lift):
        fkf = D(w, Ac, 'syl', [D(w, Ac, 'ffvelcdmd', [lift(ff, 'F : NN --> ( CC ^m A )'), kn], '( F ` k ) e. ( CC ^m A )'), w.inst('elmapi')], '( F ` k ) : A --> CC')
        ks = w.s([w.s([], 'fveq2', '( j = k -> ( F ` j ) = ( F ` k ) )'), w.s([], 'fveq2', '( j = k -> ( D ` j ) = ( D ` k ) )')], 'breq12d',
                 '( j = k -> ( ( F ` j ) ~~>r ( D ` j ) <-> ( F ` k ) ~~>r ( D ` k ) ) )')
        l0 = D(w, Ac, 'rspcdva', [ks, lift(lm, 'A. j e. NN ( F ` j ) ~~>r ( D ` j )'), kn], '( F ` k ) ~~>r ( D ` k )')
        feq = D(w, Ac, 'feqmptd', [fkf], '( F ` k ) = %s' % FKM)
        rl = D(w, Ac, 'mpbid', [l0, D(w, Ac, 'breq1d', [feq], '( ( F ` k ) ~~>r ( D ` k ) <-> %s ~~>r ( D ` k ) )' % FKM)], '%s ~~>r ( D ` k )' % FKM)
        return fkf, rl
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    fkf, rlk = kfacts(Ak, kn, lambda st, f: ad(w, Ak, st, f))
    dkc = D(w, Ak, 'syl', [rlk, w.inst('rlimcl')], '( D ` k ) e. CC')
    Akt = '( %s /\\ t e. A )' % Ak
    fkt = D(w, Akt, 'ffvelcdmd', [ad(w, Akt, fkf, '( F ` k ) : A --> CC'), w.s([], 'simpr', '( %s -> t e. A )' % Akt)], '( ( F ` k ) ` t ) e. CC')
    hkr = D(w, Ak, 'ffvelcdmd', [ad(w, Ak, hf, 'H : NN --> RR'), kn], '( H ` k ) e. RR')
    jk = w.s([w.s([w.s([w.s([w.s([], 'fveq2', '( j = k -> ( F ` j ) = ( F ` k ) )')], 'fveq1d', '( j = k -> ( ( F ` j ) ` y ) = ( ( F ` k ) ` y ) )')], 'fveq2d',
                        '( j = k -> ( abs ` ( ( F ` j ) ` y ) ) = ( abs ` ( ( F ` k ) ` y ) ) )'), w.s([], 'fveq2', '( j = k -> ( H ` j ) = ( H ` k ) )')], 'breq12d',
                  '( j = k -> ( ( abs ` ( ( F ` j ) ` y ) ) <_ ( H ` j ) <-> ( abs ` ( ( F ` k ) ` y ) ) <_ ( H ` k ) ) )')], 'ralbidv',
             '( j = k -> ( A. y e. A ( abs ` ( ( F ` j ) ` y ) ) <_ ( H ` j ) <-> A. y e. A ( abs ` ( ( F ` k ) ` y ) ) <_ ( H ` k ) ) )')
    hbk = D(w, Ak, 'rspcdva', [jk, ad(w, Ak, hb, 'A. j e. NN A. y e. A ( abs ` ( ( F ` j ) ` y ) ) <_ ( H ` j )'), kn], 'A. y e. A ( abs ` ( ( F ` k ) ` y ) ) <_ ( H ` k )')
    yt = w.s([w.s([w.s([], 'fveq2', '( y = t -> ( ( F ` k ) ` y ) = ( ( F ` k ) ` t ) )')], 'fveq2d', '( y = t -> ( abs ` ( ( F ` k ) ` y ) ) = ( abs ` ( ( F ` k ) ` t ) ) )')], 'breq1d',
             '( y = t -> ( ( abs ` ( ( F ` k ) ` y ) ) <_ ( H ` k ) <-> ( abs ` ( ( F ` k ) ` t ) ) <_ ( H ` k ) ) )')
    hbkt = D(w, Akt, 'rspcdva', [yt, ad(w, Akt, hbk, 'A. y e. A ( abs ` ( ( F ` k ) ` y ) ) <_ ( H ` k )'), w.s([], 'simpr', '( %s -> t e. A )' % Akt)], '( abs ` ( ( F ` k ) ` t ) ) <_ ( H ` k )')
    ra = D(w, Ak, 'rlimabs', [fkt, rlk], '( t e. A |-> ( abs ` ( ( F ` k ) ` t ) ) ) ~~>r ( abs ` ( D ` k ) )')
    rc = D(w, Ak, 'syl2anc', [ad(w, Ak, ar, 'A C_ RR'), D(w, Ak, 'recnd', [hkr], '( H ` k ) e. CC'), w.inst('rlimconst')], '( t e. A |-> ( H ` k ) ) ~~>r ( H ` k )')
    dle = D(w, Ak, 'rlimle', [ad(w, Ak, sup, 'sup ( A , RR* , < ) = +oo'), ra, rc, D(w, Akt, 'abscld', [fkt], '( abs ` ( ( F ` k ) ` t ) ) e. RR'), ad(w, Akt, hkr, '( H ` k ) e. RR'), hbkt],
            '( abs ` ( D ` k ) ) <_ ( H ` k )')
    # the series of the limits converges
    Aku = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A0
    knu = D(w, Aku, 'eleqtrrd', [w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Aku), cst(w, Aku, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'k e. NN')
    liftu = lambda st, f: w.s([w.s([], 'simpl', '( %s -> %s )' % (Aku, A0)), knu, w.s([st], 'ex', '( %s -> ( k e. NN -> %s ) )' % (A0, f))], 'sylc', '( %s -> %s )' % (Aku, f))
    dle2 = D(w, Aku, 'breqtrrd', [liftu(dle, '( abs ` ( D ` k ) ) <_ ( H ` k )'), D(w, Aku, 'mullidd', [D(w, Aku, 'recnd', [liftu(hkr, '( H ` k ) e. RR')], '( H ` k ) e. CC')], '( 1 x. ( H ` k ) ) = ( H ` k )')],
             '( abs ` ( D ` k ) ) <_ ( 1 x. ( H ` k ) )')
    dcv = D(w, A0, 'cvgcmpce', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A0, '1nn', '1 e. NN'), hkr, dkc, hs, cst(w, A0, '1re', '1 e. RR'), dle2], 'seq 1 ( + , D ) e. dom ~~>')
    sdl = D(w, A0, 'isumclim2', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A0, '1z', '1 e. ZZ'), D(w, Ak, 'eqidd', [], '( D ` k ) = ( D ` k )'), dkc, dcv], 'seq 1 ( + , D ) ~~> %s' % SD)
    sdc = D(w, A0, 'isumcl', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A0, '1z', '1 e. ZZ'), D(w, Ak, 'eqidd', [], '( D ` k ) = ( D ` k )'), dkc, dcv], '%s e. CC' % SD)
    # uniform convergence of the partial sums
    SQ = 'seq 1 ( oF + , F )'
    ul = D(w, A0, 'syl', [uh, w.inst('uhlim')], '%s ( ~~>u ` A ) %s' % (SQ, GST))
    stc = lambda Ac, t, tA, lift: D(w, Ac, 'syl2anc', [lift(uh, UHt), tA, w.inst('uhcl')], '%s e. CC' % ST(t))
    At = '( %s /\\ t e. A )' % A0
    stct = stc(At, 't', w.s([], 'simpr', '( %s -> t e. A )' % At), lambda st, f: ad(w, At, st, f))
    ralc = D(w, A0, 'ralrimiva', [stct], 'A. t e. A %s e. CC' % ST('t'))
    # epsilon
    Ae = '( %s /\\ e e. RR+ )' % A0
    e3 = '( e / 3 )'
    e3p = D(w, Ae, 'rpdivcld', [w.s([], 'simpr', '( %s -> e e. RR+ )' % Ae), cst(w, Ae, '3rp', '3 e. RR+')], '%s e. RR+' % e3)
    L0 = lambda st, f: ad(w, Ae, st, f)
    Aqr = '( %s /\\ ( q e. NN /\\ r e. A ) )' % Ae
    qn = w.s([], 'simprl', '( %s -> q e. NN )' % Aqr); rA = w.s([], 'simprr', '( %s -> r e. A )' % Aqr)
    psq = D(w, Aqr, 'syl2anc', [w.s([ff], 'ad2antrr', '( %s -> F : NN --> ( CC ^m A ) )' % Aqr), qn, w.inst('uhps')], '( %s ` q ) = ( t e. A |-> %s )' % (SQ, PT('q', 't')))
    ub = D(w, Aqr, 'eqtrd', [D(w, Aqr, 'fveq1d', [psq], '( ( %s ` q ) ` r ) = ( ( t e. A |-> %s ) ` r )' % (SQ, PT('q', 't'))), fv1(w, Aqr, 't', 'A', lambda v: PT('q', v), 'r', rA, 'sumex')],
           '( ( %s ` q ) ` r ) = %s' % (SQ, PT('q', 'r')))
    Ar = '( %s /\\ r e. A )' % Ae
    ua = fv1(w, Ar, 't', 'A', ST, 'r', w.s([], 'simpr', '( %s -> r e. A )' % Ar), 'sumex')
    Pa = lambda q: 'A. r e. A ( abs ` ( %s - %s ) ) < %s' % (PT(q, 'r'), ST('r'), e3)
    Pb = lambda q: '( %s e. CC /\\ ( abs ` ( %s - %s ) ) < %s )' % (PD(q), PD(q), SD, e3)
    PAR_ = {}
    def nest(base, add):
        c = '( %s /\\ %s )' % (base, add); PAR_[c] = base; return c
    def toA(ctx, target):
        chain_ = []
        c = ctx
        st = None
        while c != target:
            up = PAR_[c]
            s1 = w.s([], 'simpl', '( %s -> %s )' % (c, up))
            chain_.append((c, up, s1)); c = up
        # compose from ctx upwards
        cur = None
        for (c, up, s1) in chain_:
            cur = s1 if cur is None else w.s([cur, s1], 'syl', '( %s -> %s )' % (ctx, up))
        return cur
    Aq = '( %s /\\ q e. NN )' % Ae
    qn2 = w.s([], 'simpr', '( %s -> q e. NN )' % Aq)
    Aqk = '( %s /\\ k e. ( 1 ... q ) )' % Aq
    kq = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... q ) )' % Aqk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Aqk)
    PAR_[Ae] = A0; PAR_[Aq] = Ae; PAR_[Aqk] = Aq
    ua_ = D(w, Ae, 'ulmi', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, Ae, '1z', '1 e. ZZ'), D(w, Ae, 'syl', [L0(ff, 'F : NN --> ( CC ^m A )'), w.inst('uhpsf')], '%s : NN --> ( CC ^m A )' % SQ), ub, ua,
                            L0(ul, '%s ( ~~>u ` A ) %s' % (SQ, GST)), e3p], 'E. p e. NN A. q e. ( ZZ>= ` p ) %s' % Pa('q'))
    dkq = w.s([toA(Aqk, A0), kq, dkc], 'syl2anc', '( %s -> ( D ` k ) e. CC )' % Aqk)
    cb = D(w, Aq, 'fsumser', [D(w, Aqk, 'eqidd', [], '( D ` k ) = ( D ` k )'), D(w, Aq, 'eleqtrd', [qn2, cst(w, Aq, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'q e. ( ZZ>= ` 1 )'), dkq],
           '%s = ( seq 1 ( + , D ) ` q )' % PD('q'))
    ub_ = D(w, Ae, 'climi', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, Ae, '1z', '1 e. ZZ'), e3p, D(w, Aq, 'eqcomd', [cb], '( seq 1 ( + , D ) ` q ) = %s' % PD('q')), L0(sdl, 'seq 1 ( + , D ) ~~> %s' % SD)],
             'E. p e. NN A. q e. ( ZZ>= ` p ) %s' % Pb('q'))
    RA = 'E. p e. NN A. q e. ( ZZ>= ` p ) %s' % Pa('q'); RB = 'E. p e. NN A. q e. ( ZZ>= ` p ) %s' % Pb('q')
    ALLQ = 'A. q e. ( ZZ>= ` p ) ( %s /\\ %s )' % (Pa('q'), Pb('q'))
    rx = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'rexanuz2', '( E. p e. NN %s <-> ( %s /\\ %s ) )' % (ALLQ, RA, RB))
    both = D(w, Ae, 'mpbird', [D(w, Ae, 'jca', [ua_, ub_], '( %s /\\ %s )' % (RA, RB)), w.s([rx], 'a1i', '( %s -> ( E. p e. NN %s <-> ( %s /\\ %s ) ) )' % (Ae, ALLQ, RA, RB))], 'E. p e. NN %s' % ALLQ)
    GOAL = 'E. c e. RR A. t e. A ( c <_ t -> ( abs ` ( %s - %s ) ) < e )' % (ST('t'), SD)
    Ap = nest(Ae, 'p e. NN'); Cq = nest(Ap, ALLQ)
    pn = D(w, Cq, 'simplr', [], 'p e. NN')
    pu = D(w, Cq, 'syl', [D(w, Cq, 'nnzd', [pn], 'p e. ZZ'), w.inst('uzid')], 'p e. ( ZZ>= ` p )')
    ptq = vsub(w, lambda v: PT(v, 'r'), 'q', 'p')
    qpa = w.s([w.s([w.s([w.s([ptq], 'oveq1d', '( q = p -> ( %s - %s ) = ( %s - %s ) )' % (PT('q', 'r'), ST('r'), PT('p', 'r'), ST('r')))], 'fveq2d',
                        '( q = p -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (PT('q', 'r'), ST('r'), PT('p', 'r'), ST('r')))], 'breq1d',
                  '( q = p -> ( ( abs ` ( %s - %s ) ) < %s <-> ( abs ` ( %s - %s ) ) < %s ) )' % (PT('q', 'r'), ST('r'), e3, PT('p', 'r'), ST('r'), e3))], 'ralbidv', '( q = p -> ( %s <-> %s ) )' % (Pa('q'), Pa('p')))
    pdq = vsub(w, PD, 'q', 'p')
    qpb = w.s([w.s([pdq], 'eleq1d', '( q = p -> ( %s e. CC <-> %s e. CC ) )' % (PD('q'), PD('p'))),
               w.s([w.s([w.s([pdq], 'oveq1d', '( q = p -> ( %s - %s ) = ( %s - %s ) )' % (PD('q'), SD, PD('p'), SD))], 'fveq2d', '( q = p -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (PD('q'), SD, PD('p'), SD))],
                   'breq1d', '( q = p -> ( ( abs ` ( %s - %s ) ) < %s <-> ( abs ` ( %s - %s ) ) < %s ) )' % (PD('q'), SD, e3, PD('p'), SD, e3))], 'anbi12d', '( q = p -> ( %s <-> %s ) )' % (Pb('q'), Pb('p')))
    atp = D(w, Cq, 'rspcdva', [w.s([qpa, qpb], 'anbi12d', '( q = p -> ( ( %s /\\ %s ) <-> ( %s /\\ %s ) ) )' % (Pa('q'), Pb('q'), Pa('p'), Pb('p'))), w.s([], 'simpr', '( %s -> %s )' % (Cq, ALLQ)), pu],
            '( %s /\\ %s )' % (Pa('p'), Pb('p')))
    pa = D(w, Cq, 'simpld', [atp], Pa('p')); pb = D(w, Cq, 'simprd', [atp], Pb('p'))
    pdl = D(w, Cq, 'simprd', [pb], '( abs ` ( %s - %s ) ) < %s' % (PD('p'), SD, e3))
    Apk = nest(Ap, 'k e. ( 1 ... p )')
    kp = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... p ) )' % Apk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Apk)
    Apt = nest(Ap, 't e. A')
    Aptk = nest(Apt, 'k e. ( 1 ... p )')
    kp2 = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... p ) )' % Aptk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Aptk)
    fkt2 = w.s([toA(Aptk, A0), kp2, w.s([w.s([], 'simpr', '( %s -> t e. A )' % Apt)], 'adantr', '( %s -> t e. A )' % Aptk), fkt], 'syl21anc', '( %s -> ( ( F ` k ) ` t ) e. CC )' % Aptk)
    Aptk2 = '( %s /\\ ( t e. A /\\ k e. ( 1 ... p ) ) )' % Ap
    fkt3 = w.s([fkt2], 'anasss', '( %s -> ( ( F ` k ) ` t ) e. CC )' % Aptk2)
    fr = D(w, Ap, 'fsumrlim', [w.s([toA(Ap, A0), ar], 'syl', '( %s -> A C_ RR )' % Ap), D(w, Ap, 'fzfid', [], '( 1 ... p ) e. Fin'), fkt3,
                               w.s([toA(Apk, A0), kp, rlk], 'syl2anc', '( %s -> %s ~~>r ( D ` k ) )' % (Apk, FKM))], '( t e. A |-> %s ) ~~>r %s' % (PT('p', 't'), PD('p')))
    ptc = D(w, Apt, 'fsumcl', [D(w, Apt, 'fzfid', [], '( 1 ... p ) e. Fin'), fkt2], '%s e. CC' % PT('p', 't'))
    ri = D(w, Ap, 'rlimi', [D(w, Ap, 'ralrimiva', [ptc], 'A. t e. A %s e. CC' % PT('p', 't')), w.s([toA(Ap, Ae), e3p], 'syl', '( %s -> %s e. RR+ )' % (Ap, e3)), fr],
           'E. c e. RR A. t e. A ( c <_ t -> ( abs ` ( %s - %s ) ) < %s )' % (PT('p', 't'), PD('p'), e3))
    # the estimate at a point
    X_ = '( abs ` ( %s - %s ) ) < %s' % (PT('p', 't'), PD('p'), e3)
    Cc_ = nest(Cq, 'c e. RR'); Ct = nest(Cc_, 't e. A'); CX = nest(Ct, X_)
    tA = w.s([w.s([], 'simpr', '( %s -> t e. A )' % Ct)], 'adantr', '( %s -> t e. A )' % CX)
    rt = w.s([w.s([w.s([vsub(w, lambda v: PT('p', v), 'r', 't'), vsub(w, ST, 'r', 't')], 'oveq12d', '( r = t -> ( %s - %s ) = ( %s - %s ) )' % (PT('p', 'r'), ST('r'), PT('p', 't'), ST('t')))], 'fveq2d',
                   '( r = t -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (PT('p', 'r'), ST('r'), PT('p', 't'), ST('t')))], 'breq1d',
             '( r = t -> ( ( abs ` ( %s - %s ) ) < %s <-> ( abs ` ( %s - %s ) ) < %s ) )' % (PT('p', 'r'), ST('r'), e3, PT('p', 't'), ST('t'), e3))
    pat = D(w, CX, 'rspcdva', [rt, w.s([toA(CX, Cq), pa], 'syl', '( %s -> %s )' % (CX, Pa('p'))), tA], '( abs ` ( %s - %s ) ) < %s' % (PT('p', 't'), ST('t'), e3))
    ptcX = w.s([w.s([toA(CX, Ap), tA], 'jca', '( %s -> ( %s /\\ t e. A ) )' % (CX, Ap)), ptc], 'syl', '( %s -> %s e. CC )' % (CX, PT('p', 't')))
    stcX = w.s([toA(CX, A0), tA, stct], 'syl2anc', '( %s -> %s e. CC )' % (CX, ST('t')))
    pdcX = w.s([toA(CX, Cq), D(w, Cq, 'simpld', [pb], '%s e. CC' % PD('p'))], 'syl', '( %s -> %s e. CC )' % (CX, PD('p')))
    sdcX = w.s([toA(CX, A0), sdc], 'syl', '( %s -> %s e. CC )' % (CX, SD))
    t1 = D(w, CX, 'abs3difd', [stcX, sdcX, ptcX], '( abs ` ( %s - %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - %s ) ) )' % (ST('t'), SD, ST('t'), PT('p', 't'), PT('p', 't'), SD))
    t2 = D(w, CX, 'abs3difd', [ptcX, sdcX, pdcX], '( abs ` ( %s - %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - %s ) ) )' % (PT('p', 't'), SD, PT('p', 't'), PD('p'), PD('p'), SD))
    t3 = D(w, CX, 'abssubd', [stcX, ptcX], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (ST('t'), PT('p', 't'), PT('p', 't'), ST('t')))
    abs_ = lambda a, b, sa, sb: D(w, CX, 'abscld', [D(w, CX, 'subcld', [sa, sb], '( %s - %s ) e. CC' % (a, b))], '( abs ` ( %s - %s ) ) e. RR' % (a, b))
    lv = {}
    for (a, b, sa, sb) in [(ST('t'), SD, stcX, sdcX), (ST('t'), PT('p', 't'), stcX, ptcX), (PT('p', 't'), SD, ptcX, sdcX), (PT('p', 't'), PD('p'), ptcX, pdcX),
                           (PD('p'), SD, pdcX, sdcX), (PT('p', 't'), ST('t'), ptcX, stcX)]:
        lv['( abs ` ( %s - %s ) )' % (a, b)] = abs_(a, b, sa, sb)
    lv['e'] = D(w, CX, 'rpred', [w.s([toA(CX, Ae), w.s([], 'simpr', '( %s -> e e. RR+ )' % Ae)], 'syl', '( %s -> e e. RR+ )' % CX)], 'e e. RR')
    fin = linarith(w, CX, [t1, t2, t3, w.s([], 'simpr', '( %s -> %s )' % (CX, X_)), pat, w.s([toA(CX, Cq), pdl], 'syl', '( %s -> ( abs ` ( %s - %s ) ) < %s )' % (CX, PD('p'), SD, e3))],
                   '( abs ` ( %s - %s ) ) < e' % (ST('t'), SD), leaves=lv, atoms=list(lv.keys()))
    Y_ = '( abs ` ( %s - %s ) ) < e' % (ST('t'), SD)
    im = D(w, Ct, 'imim2d', [w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (Ct, X_, Y_))], '( ( c <_ t -> %s ) -> ( c <_ t -> %s ) )' % (X_, Y_))
    ra_ = D(w, Cc_, 'ralimdva', [im], '( A. t e. A ( c <_ t -> %s ) -> A. t e. A ( c <_ t -> %s ) )' % (X_, Y_))
    rx_ = D(w, Cq, 'reximdva', [ra_], '( E. c e. RR A. t e. A ( c <_ t -> %s ) -> %s )' % (X_, GOAL))
    gq = D(w, Cq, 'mpd', [ad(w, Cq, ri, 'E. c e. RR A. t e. A ( c <_ t -> %s )' % X_), rx_], GOAL)
    gp = D(w, Ae, 'rexlimdva', [w.s([gq], 'ex', '( %s -> ( %s -> %s ) )' % (Ap, ALLQ, GOAL))], '( E. p e. NN %s -> %s )' % (ALLQ, GOAL))
    ge = D(w, Ae, 'mpd', [both, gp], GOAL)
    ga = D(w, A0, 'ralrimiva', [ge], 'A. e e. RR+ %s' % GOAL)
    r2 = D(w, A0, 'rlim2', [ralc, ar, sdc], '( %s ~~>r %s <-> A. e e. RR+ %s )' % (GST, SD, GOAL))
    w.qed([ga, r2], 'mpbird', S['zl3tan'])
    go(w)


# ---------------------------------------------------------------- zl3lnw
if want('zl3lnw'):
    w = W('zl3lnw', 'The Gamma-factor identity of one theta term: ` N ^ P ( pi N ^ 2 / M ) ^ -w = ( M / pi ) ^ w N ^ -S ` , ` w = ( S + P ) / 2 ` .')
    A, Cc = ante_of('zl3lnw')
    mn = D(w, A, 'simp1l', [], 'M e. NN'); pp = D(w, A, 'simp1r', [], 'P e. { 0 , 1 }'); nn = D(w, A, 'simp2', [], 'N e. NN'); sc = D(w, A, 'simp3', [], 'S e. CC')
    mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+'); mc = D(w, A, 'rpcnd', [mrp], 'M e. CC'); mne = D(w, A, 'rpne0d', [mrp], 'M =/= 0')
    nrp = D(w, A, 'nnrpd', [nn], 'N e. RR+'); nc = D(w, A, 'rpcnd', [nrp], 'N e. CC'); nne = D(w, A, 'rpne0d', [nrp], 'N =/= 0')
    pn = p_nn0(w, A, pp); pc = D(w, A, 'nn0cnd', [pn], 'P e. CC')
    W_ = L.WS('S')
    wc = D(w, A, 'halfcld' if False else 'divcld', [D(w, A, 'addcld', [sc, pc], '( S + P ) e. CC'), cst(w, A, '2cn', '2 e. CC'), cst(w, A, '2ne0', '2 =/= 0')], '%s e. CC' % W_)
    nwc = D(w, A, 'negcld', [wc], '-u %s e. CC' % W_)
    u = '( _pi / M )'
    urp = D(w, A, 'rpdivcld', [cst(w, A, 'pirp', '_pi e. RR+'), mrp], '%s e. RR+' % u)
    ur = D(w, A, 'rpred', [urp], '%s e. RR' % u); uc = D(w, A, 'rpcnd', [urp], '%s e. CC' % u); une = D(w, A, 'rpne0d', [urp], '%s =/= 0' % u)
    n2 = '( N ^ 2 )'
    n2r = D(w, A, 'resqcld', [D(w, A, 'rpred', [nrp], 'N e. RR')], '%s e. RR' % n2)
    e1 = D(w, A, 'div23d', [cst(w, A, 'picn', '_pi e. CC'), D(w, A, 'sqcld', [nc], '%s e. CC' % n2), mc, mne], '%s = ( %s x. %s )' % (L.LN('N'), u, n2))
    e2 = D(w, A, 'syl3anc', [D(w, A, 'jca', [ur, D(w, A, 'rpge0d', [urp], '0 <_ %s' % u)], '( %s e. RR /\\ 0 <_ %s )' % (u, u)),
                             D(w, A, 'jca', [n2r, D(w, A, 'sqge0d', [D(w, A, 'rpred', [nrp], 'N e. RR')], '0 <_ %s' % n2)], '( %s e. RR /\\ 0 <_ %s )' % (n2, n2)), nwc, w.inst('mulcxp')],
           '( ( %s x. %s ) ^c -u %s ) = ( ( %s ^c -u %s ) x. ( %s ^c -u %s ) )' % (u, n2, W_, u, W_, n2, W_))
    MP_ = '( M / _pi )'
    e3 = chain(w, A, ['( %s ^c -u %s )' % (u, W_), '( 1 / ( %s ^c %s ) )' % (u, W_), '( ( 1 / %s ) ^c %s )' % (u, W_), '( %s ^c %s )' % (MP_, W_)],
               [D(w, A, 'syl3anc', [uc, une, wc, w.inst('cxpneg')], '( %s ^c -u %s ) = ( 1 / ( %s ^c %s ) )' % (u, W_, u, W_)),
                ('r', D(w, A, 'syl2anc', [urp, wc, w.inst('cxprec')], '( ( 1 / %s ) ^c %s ) = ( 1 / ( %s ^c %s ) )' % (u, W_, u, W_))),
                D(w, A, 'oveq1d', [D(w, A, 'recdivd', [cst(w, A, 'picn', '_pi e. CC'), mc, cst(w, A, 'pine0', '_pi =/= 0'), mne], '( 1 / %s ) = %s' % (u, MP_))], '( ( 1 / %s ) ^c %s ) = ( %s ^c %s )' % (u, W_, MP_, W_))])
    T2 = '( 2 x. -u %s )' % W_
    e4 = chain(w, A, ['( %s ^c -u %s )' % (n2, W_), '( ( N ^c 2 ) ^c -u %s )' % W_, '( N ^c %s )' % T2],
               [D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'syl2anc', [nc, cst(w, A, '2nn0', '2 e. NN0'), w.inst('cxpexp')], '( N ^c 2 ) = %s' % n2)], '%s = ( N ^c 2 )' % n2)],
                  '( %s ^c -u %s ) = ( ( N ^c 2 ) ^c -u %s )' % (n2, W_, W_)),
                ('r', D(w, A, 'syl3anc', [nrp, cst(w, A, '2re', '2 e. RR'), nwc, w.inst('cxpmul')], '( N ^c %s ) = ( ( N ^c 2 ) ^c -u %s )' % (T2, W_)))])
    e5 = D(w, A, 'eqcomd', [D(w, A, 'syl2anc', [nc, pn, w.inst('cxpexp')], '( N ^c P ) = ( N ^ P )')], '( N ^ P ) = ( N ^c P )')
    t2c = D(w, A, 'mulcld', [cst(w, A, '2cn', '2 e. CC'), nwc], '%s e. CC' % T2)
    e6 = D(w, A, 'eqcomd', [D(w, A, 'syl3anc', [D(w, A, 'jca', [nc, nne], '( N e. CC /\\ N =/= 0 )'), pc, t2c, w.inst('cxpadd')], '( N ^c ( P + %s ) ) = ( ( N ^c P ) x. ( N ^c %s ) )' % (T2, T2))],
           '( ( N ^c P ) x. ( N ^c %s ) ) = ( N ^c ( P + %s ) )' % (T2, T2))
    spc = D(w, A, 'addcld', [sc, pc], '( S + P ) e. CC')
    e7 = chain(w, A, ['( P + %s )' % T2, '( P + -u ( 2 x. %s ) )' % W_, '( P + -u ( S + P ) )', '( P - ( S + P ) )', '-u ( ( S + P ) - P )', '-u S'],
               [D(w, A, 'oveq2d', [D(w, A, 'mulneg2d', [cst(w, A, '2cn', '2 e. CC'), wc], '%s = -u ( 2 x. %s )' % (T2, W_))], '( P + %s ) = ( P + -u ( 2 x. %s ) )' % (T2, W_)),
                D(w, A, 'oveq2d', [D(w, A, 'negeqd', [D(w, A, 'divcan2d', [spc, cst(w, A, '2cn', '2 e. CC'), cst(w, A, '2ne0', '2 =/= 0')], '( 2 x. %s ) = ( S + P )' % W_)], '-u ( 2 x. %s ) = -u ( S + P )' % W_)],
                  '( P + -u ( 2 x. %s ) ) = ( P + -u ( S + P ) )' % W_),
                D(w, A, 'negsubd', [pc, spc], '( P + -u ( S + P ) ) = ( P - ( S + P ) )'),
                ('r', D(w, A, 'negsubdi2d', [spc, pc], '-u ( ( S + P ) - P ) = ( P - ( S + P ) )')),
                D(w, A, 'negeqd', [D(w, A, 'pncand', [sc, pc], '( ( S + P ) - P ) = S')], '-u ( ( S + P ) - P ) = -u S')])
    NPc = D(w, A, 'cxpcld', [nc, pc], '( N ^c P ) e. CC')
    MWc = D(w, A, 'cxpcld', [D(w, A, 'divcld', [mc, cst(w, A, 'picn', '_pi e. CC'), cst(w, A, 'pine0', '_pi =/= 0')], '%s e. CC' % MP_), wc], '( %s ^c %s ) e. CC' % (MP_, W_))
    NTc = D(w, A, 'cxpcld', [nc, t2c], '( N ^c %s ) e. CC' % T2)
    LW = '( %s ^c -u %s )' % (L.LN('N'), W_)
    fin = chain(w, A, ['( ( N ^ P ) x. %s )' % LW, '( ( N ^c P ) x. %s )' % LW, '( ( N ^c P ) x. ( ( %s x. %s ) ^c -u %s ) )' % (u, n2, W_),
                       '( ( N ^c P ) x. ( ( %s ^c -u %s ) x. ( %s ^c -u %s ) ) )' % (u, W_, n2, W_), '( ( N ^c P ) x. ( ( %s ^c %s ) x. ( N ^c %s ) ) )' % (MP_, W_, T2),
                       '( ( %s ^c %s ) x. ( ( N ^c P ) x. ( N ^c %s ) ) )' % (MP_, W_, T2), '( ( %s ^c %s ) x. ( N ^c ( P + %s ) ) )' % (MP_, W_, T2), '( ( %s ^c %s ) x. ( N ^c -u S ) )' % (MP_, W_)],
                [D(w, A, 'oveq1d', [e5], '( ( N ^ P ) x. %s ) = ( ( N ^c P ) x. %s )' % (LW, LW)),
                 D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [e1], '%s = ( ( %s x. %s ) ^c -u %s )' % (LW, u, n2, W_))], '( ( N ^c P ) x. %s ) = ( ( N ^c P ) x. ( ( %s x. %s ) ^c -u %s ) )' % (LW, u, n2, W_)),
                 D(w, A, 'oveq2d', [e2], '( ( N ^c P ) x. ( ( %s x. %s ) ^c -u %s ) ) = ( ( N ^c P ) x. ( ( %s ^c -u %s ) x. ( %s ^c -u %s ) ) )' % (u, n2, W_, u, W_, n2, W_)),
                 D(w, A, 'oveq2d', [D(w, A, 'oveq12d', [e3, e4], '( ( %s ^c -u %s ) x. ( %s ^c -u %s ) ) = ( ( %s ^c %s ) x. ( N ^c %s ) )' % (u, W_, n2, W_, MP_, W_, T2))],
                   '( ( N ^c P ) x. ( ( %s ^c -u %s ) x. ( %s ^c -u %s ) ) ) = ( ( N ^c P ) x. ( ( %s ^c %s ) x. ( N ^c %s ) ) )' % (u, W_, n2, W_, MP_, W_, T2)),
                 D(w, A, 'mul12d', [NPc, MWc, NTc], '( ( N ^c P ) x. ( ( %s ^c %s ) x. ( N ^c %s ) ) ) = ( ( %s ^c %s ) x. ( ( N ^c P ) x. ( N ^c %s ) ) )' % (MP_, W_, T2, MP_, W_, T2)),
                 D(w, A, 'oveq2d', [e6], '( ( %s ^c %s ) x. ( ( N ^c P ) x. ( N ^c %s ) ) ) = ( ( %s ^c %s ) x. ( N ^c ( P + %s ) ) )' % (MP_, W_, T2, MP_, W_, T2)),
                 D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [e7], '( N ^c ( P + %s ) ) = ( N ^c -u S )' % T2)], '( ( %s ^c %s ) x. ( N ^c ( P + %s ) ) ) = ( ( %s ^c %s ) x. ( N ^c -u S ) )' % (MP_, W_, T2, MP_, W_))], name='qed')
    go(w)


def ibl_gen(w, Ac, P, Q, pr, prp, qr, e, W, leaves):
    """( Ac -> ( x e. ( P (,) Q ) |-> e ) e. L^1 ) for e continuous in x, with the factor x ^c ( W - 1 )"""
    I = '( %s [,] %s )' % (P, Q); X = '( %s (,) %s )' % (P, Q)
    wc = leaves.pop('__W')
    wm1 = D(w, Ac, 'subcld', [wc, cst(w, Ac, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % W)
    CXm = '( x e. %s |-> ( x ^c ( %s - 1 ) ) )' % (I, W)
    both = D(w, Ac, 'syl2anc', [wm1, D(w, Ac, 'jca', [prp, qr], '( %s e. RR+ /\\ %s e. RR )' % (P, Q)), w.inst('zl3cxc')],
             '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c ( %s - 1 ) ) ) ) e. ( %s -cn-> CC ) )' % (CXm, I, I, W, I))
    cx = D(w, Ac, 'simpld', [both], '%s e. ( %s -cn-> CC )' % (CXm, I))
    xss = D(w, Ac, 'sstrd', [D(w, Ac, 'syl2anc', [pr, qr, w.inst('iccssre')], '%s C_ RR' % I), cst(w, Ac, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    cl = Closure(w, Ac, leaves)
    cfull = cont(w, Ac, I, e, cl, xss, special={'( x ^c ( %s - 1 ) )' % W: cx})
    ib = D(w, Ac, 'syl2anc', [D(w, Ac, 'jca', [pr, qr], '( %s e. RR /\\ %s e. RR )' % (P, Q)), cfull, w.inst('zl3ibl')], '( ( x e. %s |-> %s ) |` %s ) e. L^1' % (I, e, X))
    rs = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( ( x e. %s |-> %s ) |` %s ) = ( x e. %s |-> %s )' % (I, e, X, X, e))
    return D(w, Ac, 'eqeltrrd', [w.s([rs], 'a1i', '( %s -> ( ( x e. %s |-> %s ) |` %s ) = ( x e. %s |-> %s ) )' % (Ac, I, e, X, X, e)), ib], '( x e. %s |-> %s ) e. L^1' % (X, e))


# ---------------------------------------------------------------- zl3mtw
if want('zl3mtw'):
    w = W('zl3mtw', 'The theta Mellin integral over ` ( 1 / t , t ) ` is the series of the termwise Euler integrals ( ~ zl3mex with the majorant of ~ zl3tb0 ).')
    A, Cc = ante_of('zl3mtw')
    ta = D(w, A, 'simp1', [], L.TA); wc = D(w, A, 'simp2', [], 'W e. CC'); trp = D(w, A, 'simp3', [], 't e. RR+')
    mn, pp, cf, bnd, mrp = ta_ctx(w, A, ta)
    tr = D(w, A, 'rpred', [trp], 't e. RR'); itp = D(w, A, 'rpreccld', [trp], '( 1 / t ) e. RR+'); itr = D(w, A, 'rpred', [itp], '( 1 / t ) e. RR')
    U = '( ( 1 / t ) (,) t )'
    XW = '( x ^c ( W - 1 ) )'
    ET = lambda n, x: '( %s x. %s )' % (TT(n, x), XW.replace('x ^c', '%s ^c' % x))
    a_ = '( ( Re ` W ) - 1 )'
    ar = D(w, A, 'resubcld', [D(w, A, 'recld', [wc], '( Re ` W ) e. RR'), cst(w, A, '1re', '1 e. RR')], '%s e. RR' % a_)
    LT = '( ( abs ` %s ) x. ( log ` t ) )' % a_
    Bt = '( exp ` %s )' % LT
    ltr = D(w, A, 'remulcld', [D(w, A, 'abscld', [D(w, A, 'recnd', [ar], '%s e. CC' % a_)], '( abs ` %s ) e. RR' % a_), D(w, A, 'relogcld', [trp], '( log ` t ) e. RR')], '%s e. RR' % LT)
    btr = D(w, A, 'reefcld', [ltr], '%s e. RR' % Bt); btp = D(w, A, 'rpefcld', [ltr], '%s e. RR+' % Bt)
    KB = '( %s x. %s )' % (KE('( 1 / t )'), Bt)
    # bound of x ^c ( W - 1 ) on U
    Ax = '( %s /\\ x e. %s )' % (A, U)
    xU = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, U))
    xr, xrp = ioo_pos(w, Ax, '( 1 / t )', 't', ad(w, Ax, itr, '( 1 / t ) e. RR'), ad(w, Ax, tr, 't e. RR'), ad(w, Ax, D(w, A, 'rpgt0d', [itp], '0 < ( 1 / t )'), '0 < ( 1 / t )'))
    bi = D(w, Ax, 'syl2anc', [D(w, Ax, 'rexrd', [ad(w, Ax, itr, '( 1 / t ) e. RR')], '( 1 / t ) e. RR*'), D(w, Ax, 'rexrd', [ad(w, Ax, tr, 't e. RR')], 't e. RR*'), w.inst('elioo2')],
           '( x e. %s <-> ( x e. RR /\\ ( 1 / t ) < x /\\ x < t ) )' % U)
    b3 = D(w, Ax, 'mpbid', [xU, bi], '( x e. RR /\\ ( 1 / t ) < x /\\ x < t )')
    lo = D(w, Ax, 'simp2d', [b3], '( 1 / t ) < x'); hi = D(w, Ax, 'simp3d', [b3], 'x < t')
    trx = ad(w, Ax, trp, 't e. RR+'); itx = ad(w, Ax, itp, '( 1 / t ) e. RR+')
    lhi = D(w, Ax, 'mpbid', [hi, D(w, Ax, 'syl2anc', [xrp, trx, w.inst('logltb')], '( x < t <-> ( log ` x ) < ( log ` t ) )')], '( log ` x ) < ( log ` t )')
    llo = D(w, Ax, 'mpbid', [lo, D(w, Ax, 'syl2anc', [itx, xrp, w.inst('logltb')], '( ( 1 / t ) < x <-> ( log ` ( 1 / t ) ) < ( log ` x ) )')], '( log ` ( 1 / t ) ) < ( log ` x )')
    lrec = D(w, Ax, 'eqtrd', [D(w, Ax, 'relogdivd', [cst(w, Ax, '1rp', '1 e. RR+'), trx], '( log ` ( 1 / t ) ) = ( ( log ` 1 ) - ( log ` t ) )'),
                              D(w, Ax, 'oveq1d', [cst(w, Ax, 'log1', '( log ` 1 ) = 0')], '( ( log ` 1 ) - ( log ` t ) ) = ( 0 - ( log ` t ) )')], '( log ` ( 1 / t ) ) = ( 0 - ( log ` t ) )')
    lxr = D(w, Ax, 'relogcld', [xrp], '( log ` x ) e. RR'); ltr_ = D(w, Ax, 'relogcld', [trx], '( log ` t ) e. RR')
    lv = {'( log ` x )': lxr, '( log ` t )': ltr_, '( log ` ( 1 / t ) )': D(w, Ax, 'relogcld', [itx], '( log ` ( 1 / t ) ) e. RR')}
    alx = D(w, Ax, 'mpbird', [D(w, Ax, 'jca', [linarith(w, Ax, [llo, lrec], '-u ( log ` t ) <_ ( log ` x )', leaves=dict(lv), atoms=list(lv)), linarith(w, Ax, [lhi], '( log ` x ) <_ ( log ` t )', leaves=dict(lv), atoms=list(lv))],
                                          '( -u ( log ` t ) <_ ( log ` x ) /\\ ( log ` x ) <_ ( log ` t ) )'),
                              D(w, Ax, 'absled', [lxr, ltr_], '( ( abs ` ( log ` x ) ) <_ ( log ` t ) <-> ( -u ( log ` t ) <_ ( log ` x ) /\\ ( log ` x ) <_ ( log ` t ) ) )')],
              '( abs ` ( log ` x ) ) <_ ( log ` t )')
    arx = ad(w, Ax, ar, '%s e. RR' % a_)
    aal = D(w, Ax, 'abscld', [D(w, Ax, 'recnd', [arx], '%s e. CC' % a_)], '( abs ` %s ) e. RR' % a_)
    alxr = D(w, Ax, 'abscld', [D(w, Ax, 'recnd', [lxr], '( log ` x ) e. CC')], '( abs ` ( log ` x ) ) e. RR')
    s1 = D(w, Ax, 'leabsd', [D(w, Ax, 'remulcld', [arx, lxr], '( %s x. ( log ` x ) ) e. RR' % a_)], '( %s x. ( log ` x ) ) <_ ( abs ` ( %s x. ( log ` x ) ) )' % (a_, a_))
    s2 = D(w, Ax, 'absmuld', [D(w, Ax, 'recnd', [arx], '%s e. CC' % a_), D(w, Ax, 'recnd', [lxr], '( log ` x ) e. CC')], '( abs ` ( %s x. ( log ` x ) ) ) = ( ( abs ` %s ) x. ( abs ` ( log ` x ) ) )' % (a_, a_))
    s3 = D(w, Ax, 'lemul2ad', [alxr, ltr_, aal, D(w, Ax, 'absge0d', [D(w, Ax, 'recnd', [arx], '%s e. CC' % a_)], '0 <_ ( abs ` %s )' % a_), alx],
           '( ( abs ` %s ) x. ( abs ` ( log ` x ) ) ) <_ %s' % (a_, LT))
    ex_ = D(w, Ax, 'letrd', [D(w, Ax, 'remulcld', [arx, lxr], '( %s x. ( log ` x ) ) e. RR' % a_), D(w, Ax, 'abscld', [D(w, Ax, 'recnd', [D(w, Ax, 'remulcld', [arx, lxr], '( %s x. ( log ` x ) ) e. RR' % a_)], '( %s x. ( log ` x ) ) e. CC' % a_)], '( abs ` ( %s x. ( log ` x ) ) ) e. RR' % a_),
                              ad(w, Ax, ltr, '%s e. RR' % LT), s1, D(w, Ax, 'breqtrrd' if False else 'eqbrtrd', [s2, s3], '( abs ` ( %s x. ( log ` x ) ) ) <_ %s' % (a_, LT))], '( %s x. ( log ` x ) ) <_ %s' % (a_, LT))
    efl = D(w, Ax, 'mpbid', [ex_, D(w, Ax, 'syl2anc', [D(w, Ax, 'remulcld', [arx, lxr], '( %s x. ( log ` x ) ) e. RR' % a_), ad(w, Ax, ltr, '%s e. RR' % LT), w.inst('efle')],
                                                        '( ( %s x. ( log ` x ) ) <_ %s <-> ( exp ` ( %s x. ( log ` x ) ) ) <_ %s )' % (a_, LT, a_, Bt))], '( exp ` ( %s x. ( log ` x ) ) ) <_ %s' % (a_, Bt))
    wcx = ad(w, Ax, wc, 'W e. CC'); xc = D(w, Ax, 'rpcnd', [xrp], 'x e. CC')
    wm = D(w, Ax, 'subcld', [wcx, cst(w, Ax, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    rwm = D(w, Ax, 'eqtrd', [D(w, Ax, 'resubd', [wcx, cst(w, Ax, 'ax-1cn', '1 e. CC')], '( Re ` ( W - 1 ) ) = ( ( Re ` W ) - ( Re ` 1 ) )'),
                             D(w, Ax, 'oveq2d', [cst(w, Ax, 're1', '( Re ` 1 ) = 1')], '( ( Re ` W ) - ( Re ` 1 ) ) = %s' % a_)], '( Re ` ( W - 1 ) ) = %s' % a_)
    axw = chain(w, Ax, ['( abs ` %s )' % XW, '( x ^c ( Re ` ( W - 1 ) ) )', '( x ^c %s )' % a_, '( exp ` ( %s x. ( log ` x ) ) )' % a_],
                [D(w, Ax, 'syl2anc', [xrp, wm, w.inst('abscxp')], '( abs ` %s ) = ( x ^c ( Re ` ( W - 1 ) ) )' % XW),
                 D(w, Ax, 'oveq2d', [rwm], '( x ^c ( Re ` ( W - 1 ) ) ) = ( x ^c %s )' % a_),
                 D(w, Ax, 'syl3anc', [xc, D(w, Ax, 'rpne0d', [xrp], 'x =/= 0'), D(w, Ax, 'recnd', [arx], '%s e. CC' % a_), w.inst('cxpef')], '( x ^c %s ) = ( exp ` ( %s x. ( log ` x ) ) )' % (a_, a_))])
    xwb = D(w, Ax, 'eqbrtrd', [axw, efl], '( abs ` %s ) <_ %s' % (XW, Bt))
    xwc = D(w, Ax, 'cxpcld', [xc, wm], '%s e. CC' % XW)
    # term bound at ( n , x )
    def term(Ac, n, nn, lift, xl):
        """|ET(n,x)| <_ ( KB x. ( 1 / 2 ) ^ n ), ET(n,x) e. CC in Ac ( contains x e. U )"""
        tab = D(w, Ac, 'syl3anc', [lift(ta, L.TA), xl(xr, 'x e. RR'), nn, w.inst('zl3tab')], '( %s e. CC /\\ ( abs ` %s ) <_ ( ( %s ^ P ) x. %s ) )' % (TT(n, 'x'), TT(n, 'x'), n, EXv(n, 'x')))
        tc = D(w, Ac, 'simpld', [tab], '%s e. CC' % TT(n, 'x'))
        itle = D(w, Ac, 'ltled', [lift(itr, '( 1 / t ) e. RR'), xl(xr, 'x e. RR'), xl(lo, '( 1 / t ) < x')], '( 1 / t ) <_ x')
        tb = D(w, Ac, 'syl3anc', [D(w, Ac, 'simpld', [lift(ta, L.TA)], L.MP), D(w, Ac, '3jca', [lift(itp, '( 1 / t ) e. RR+'), xl(xr, 'x e. RR'), itle], '( ( 1 / t ) e. RR+ /\\ x e. RR /\\ ( 1 / t ) <_ x )'), nn, w.inst('zl3tb0')],
               '( ( %s ^ P ) x. %s ) <_ ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (n, EXv(n, 'x'), KE('( 1 / t )'), n))
        nr = D(w, Ac, 'nnred', [nn], '%s e. RR' % n); n0 = D(w, Ac, 'ltled', [cst(w, Ac, '0re', '0 e. RR'), nr, D(w, Ac, 'nngt0d', [nn], '0 < %s' % n)], '0 <_ %s' % n)
        _, npr, _ = np_facts(w, Ac, lift(pp, 'P e. { 0 , 1 }'), n, nr, n0)
        kr = D(w, Ac, 'rpred', [D(w, Ac, 'rpefcld', [D(w, Ac, 'rpred', [D(w, Ac, 'rpreccld', [D(w, Ac, 'rpmulcld', [cst(w, Ac, 'pirp', '_pi e. RR+'), D(w, Ac, 'rpdivcld', [lift(itp, '( 1 / t ) e. RR+'), lift(mrp, 'M e. RR+')], '( ( 1 / t ) / M ) e. RR+')],
                                                                                                                '( _pi x. ( ( 1 / t ) / M ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR')],
                                           '%s e. RR+' % KE('( 1 / t )'))], '%s e. RR' % KE('( 1 / t )'))
        hr = D(w, Ac, 'reexpcld', [cst(w, Ac, 'halfre', '( 1 / 2 ) e. RR'), D(w, Ac, 'nnnn0d', [nn], '%s e. NN0' % n)], '( ( 1 / 2 ) ^ %s ) e. RR' % n)
        khr = D(w, Ac, 'remulcld', [kr, hr], '( %s x. ( ( 1 / 2 ) ^ %s ) ) e. RR' % (KE('( 1 / t )'), n))
        tle = D(w, Ac, 'letrd', [D(w, Ac, 'abscld', [tc], '( abs ` %s ) e. RR' % TT(n, 'x')), D(w, Ac, 'remulcld', [npr, D(w, Ac, 'rpred', [exv_rp(w, Ac, n, 'x', nr, xl(xr, 'x e. RR'), lift(mrp, 'M e. RR+'))], '%s e. RR' % EXv(n, 'x'))], '( ( %s ^ P ) x. %s ) e. RR' % (n, EXv(n, 'x'))),
                                 khr, D(w, Ac, 'simprd', [tab], '( abs ` %s ) <_ ( ( %s ^ P ) x. %s )' % (TT(n, 'x'), n, EXv(n, 'x'))), tb], '( abs ` %s ) <_ ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (TT(n, 'x'), KE('( 1 / t )'), n))
        xwc_ = xl(xwc, '%s e. CC' % XW)
        pr_ = D(w, Ac, 'lemul12ad', [D(w, Ac, 'abscld', [tc], '( abs ` %s ) e. RR' % TT(n, 'x')), khr, D(w, Ac, 'abscld', [xwc_], '( abs ` %s ) e. RR' % XW), lift(btr, '%s e. RR' % Bt),
                                     D(w, Ac, 'absge0d', [tc], '0 <_ ( abs ` %s )' % TT(n, 'x')), D(w, Ac, 'absge0d', [xwc_], '0 <_ ( abs ` %s )' % XW), tle, xl(xwb, '( abs ` %s ) <_ %s' % (XW, Bt))],
                 '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( %s x. ( ( 1 / 2 ) ^ %s ) ) x. %s )' % (TT(n, 'x'), XW, KE('( 1 / t )'), n, Bt))
        am = D(w, Ac, 'absmuld', [tc, xwc_], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (ET(n, 'x'), TT(n, 'x'), XW))
        m32 = D(w, Ac, 'mul32d', [D(w, Ac, 'recnd', [kr], '%s e. CC' % KE('( 1 / t )')), D(w, Ac, 'recnd', [hr], '( ( 1 / 2 ) ^ %s ) e. CC' % n), D(w, Ac, 'recnd', [lift(btr, '%s e. RR' % Bt)], '%s e. CC' % Bt)],
                 '( ( %s x. ( ( 1 / 2 ) ^ %s ) ) x. %s ) = ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (KE('( 1 / t )'), n, Bt, KB, n))
        le = D(w, Ac, 'breqtrd', [D(w, Ac, 'eqbrtrd', [am, pr_], '( abs ` %s ) <_ ( ( %s x. ( ( 1 / 2 ) ^ %s ) ) x. %s )' % (ET(n, 'x'), KE('( 1 / t )'), n, Bt)), m32],
               '( abs ` %s ) <_ ( %s x. ( ( 1 / 2 ) ^ %s ) )' % (ET(n, 'x'), KB, n))
        return D(w, Ac, 'mulcld', [tc, xwc_], '%s e. CC' % ET(n, 'x')), le, tc, tle, khr
    uex = w.s([], 'ovex', '%s e. _V' % U)
    inner = lambda n: '( z e. %s |-> %s )' % (U, ET(n, 'z'))
    innerx = lambda n: '( x e. %s |-> %s )' % (U, ET(n, 'x'))
    cbe = lambda n: w.s([vsub(w, lambda v: ET(n, v), 'x', 'z')], 'cbvmptv', '%s = %s' % (innerx(n), inner(n)))
    F = '( n e. NN |-> %s )' % inner('n')
    HH = lambda n: '( %s x. ( ( 1 / 2 ) ^ %s ) )' % (KB, n)
    Hm = '( n e. NN |-> %s )' % HH('n')
    kbr = D(w, A, 'remulcld', [D(w, A, 'rpred', [D(w, A, 'rpefcld', [D(w, A, 'rpred', [D(w, A, 'rpreccld', [D(w, A, 'rpmulcld', [cst(w, A, 'pirp', '_pi e. RR+'), D(w, A, 'rpdivcld', [itp, mrp], '( ( 1 / t ) / M ) e. RR+')],
                                                                                                            '( _pi x. ( ( 1 / t ) / M ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR')],
                                                   '%s e. RR+' % KE('( 1 / t )'))], '%s e. RR' % KE('( 1 / t )')), btr], '%s e. RR' % KB)
    def xlift(Ac, toA_, xU_):
        return lambda st, f: w.s([toA_, xU_, st], 'syl2anc', '( %s -> %s )' % (Ac, f))
    def fv2(Ac, bnd, dom, body, bm, bc):
        """( Ac -> ( ( bnd e. dom |-> body ) ` bnd ) = body ) : fvmpt2"""
        Fm = '( %s e. %s |-> %s )' % (bnd, dom, body)
        return D(w, Ac, 'syl2anc', [bm, bc, w.s([w.s([], 'eqid', '%s = %s' % (Fm, Fm))], 'fvmpt2', '( ( %s e. %s /\\ %s e. CC ) -> ( %s ` %s ) = %s )' % (bnd, dom, body, Fm, bnd, body))],
                 '( %s ` %s ) = %s' % (Fm, bnd, body))
    # F : NN --> ( CC ^m U )
    An = '( %s /\\ n e. NN )' % A
    Anx = '( %s /\\ x e. %s )' % (An, U)
    lnx = xlift(Anx, w.s([], 'simpll', '( %s -> %s )' % (Anx, A)), w.s([], 'simpr', '( %s -> x e. %s )' % (Anx, U)))
    etn, _, _, _, _ = term(Anx, 'n', w.s([], 'simplr', '( %s -> n e. NN )' % Anx), lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Anx, f)), lnx)
    iff = D(w, An, 'fmptd', [etn, w.s([], 'eqid', '%s = %s' % (innerx('n'), innerx('n')))], '%s : %s --> CC' % (innerx('n'), U))
    elm = w.s([w.s([w.s([], 'cnex', 'CC e. _V'), uex], 'pm3.2i', '( CC e. _V /\\ %s e. _V )' % U), w.inst('elmapg')], 'ax-mp', '( %s e. ( CC ^m %s ) <-> %s : %s --> CC )' % (innerx('n'), U, innerx('n'), U))
    imx = D(w, An, 'mpbird', [iff, w.s([elm], 'a1i', '( %s -> ( %s e. ( CC ^m %s ) <-> %s : %s --> CC ) )' % (An, innerx('n'), U, innerx('n'), U))], '%s e. ( CC ^m %s )' % (innerx('n'), U))
    ime = D(w, An, 'eqeltrrd', [w.s([cbe('n')], 'a1i', '( %s -> %s = %s )' % (An, innerx('n'), inner('n'))), imx], '%s e. ( CC ^m %s )' % (inner('n'), U))
    fF = D(w, A, 'fmptd', [ime, w.s([], 'eqid', '%s = %s' % (F, F))], '%s : NN --> ( CC ^m %s )' % (F, U))
    # the majorant
    def hval(Ac, v, vn, lift):
        vr = D(w, Ac, 'reexpcld', [cst(w, Ac, 'halfre', '( 1 / 2 ) e. RR'), D(w, Ac, 'nnnn0d', [vn], '%s e. NN0' % v)], '( ( 1 / 2 ) ^ %s ) e. RR' % v)
        hr = D(w, Ac, 'remulcld', [lift(kbr, '%s e. RR' % KB), vr], '%s e. RR' % HH(v))
        return fv1(w, Ac, 'n', 'NN', HH, v, vn, 'ovex'), hr, vr
    _, hrn, _ = hval(An, 'n', w.s([], 'simpr', '( %s -> n e. NN )' % An), lambda st, f: ad(w, An, st, f))
    hf = D(w, A, 'fmptd', [hrn, w.s([], 'eqid', '%s = %s' % (Hm, Hm))], '%s : NN --> RR' % Hm)
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    hvk, hrk, vrk = hval(Ak, 'k', kn, lambda st, f: ad(w, Ak, st, f))
    kb0 = D(w, A, 'mulge0d', [D(w, A, 'rpred', [D(w, A, 'rpefcld', [D(w, A, 'rpred', [D(w, A, 'rpreccld', [D(w, A, 'rpmulcld', [cst(w, A, 'pirp', '_pi e. RR+'), D(w, A, 'rpdivcld', [itp, mrp], '( ( 1 / t ) / M ) e. RR+')],
                                                                                                        '( _pi x. ( ( 1 / t ) / M ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR')],
                                                   '%s e. RR+' % KE('( 1 / t )'))], '%s e. RR' % KE('( 1 / t )')), btr,
                              D(w, A, 'rpge0d', [D(w, A, 'rpefcld', [D(w, A, 'rpred', [D(w, A, 'rpreccld', [D(w, A, 'rpmulcld', [cst(w, A, 'pirp', '_pi e. RR+'), D(w, A, 'rpdivcld', [itp, mrp], '( ( 1 / t ) / M ) e. RR+')],
                                                                                                        '( _pi x. ( ( 1 / t ) / M ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR')],
                                                   '%s e. RR+' % KE('( 1 / t )'))], '0 <_ %s' % KE('( 1 / t )')), D(w, A, 'rpge0d', [btp], '0 <_ %s' % Bt)], '0 <_ %s' % KB)
    h0k = D(w, Ak, 'mulge0d', [ad(w, Ak, kbr, '%s e. RR' % KB), vrk, ad(w, Ak, kb0, '0 <_ %s' % KB),
                               D(w, Ak, 'expge0d', [cst(w, Ak, 'halfre', '( 1 / 2 ) e. RR'), D(w, Ak, 'nnnn0d', [kn], 'k e. NN0'), cst(w, Ak, 'halfge0', '0 <_ ( 1 / 2 )')], '0 <_ ( ( 1 / 2 ) ^ k )')], '0 <_ %s' % HH('k'))
    hle = D(w, Ak, 'eqbrtrd', [D(w, Ak, 'eqtrd', [D(w, Ak, 'fveq2d', [hvk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (Hm, HH('k'))), D(w, Ak, 'absidd', [hrk, h0k], '( abs ` %s ) = %s' % (HH('k'), HH('k')))],
                                              '( abs ` ( %s ` k ) ) = %s' % (Hm, HH('k'))), D(w, Ak, 'leidd', [hrk], '%s <_ %s' % (HH('k'), HH('k')))], '( abs ` ( %s ` k ) ) <_ %s' % (Hm, HH('k')))
    ms = D(w, A, 'simpld', [D(w, A, 'zl3mser', [kbr, cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), cst(w, A, 'halfge0', '0 <_ ( 1 / 2 )'), cst(w, A, 'halflt1', '( 1 / 2 ) < 1'),
                                                D(w, Ak, 'eqeltrd', [hvk, D(w, Ak, 'recnd', [hrk], '%s e. CC' % HH('k'))], '( %s ` k ) e. CC' % Hm), hle],
                                '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) )' % (Hm, Hm, KB))], 'seq 1 ( + , %s ) e. dom ~~>' % Hm)
    # the bound at ( j , x )
    Ajx = '( %s /\\ ( j e. NN /\\ x e. %s ) )' % (A, U)
    jn = w.s([], 'simprl', '( %s -> j e. NN )' % Ajx); jxU = w.s([], 'simprr', '( %s -> x e. %s )' % (Ajx, U))
    ljx = xlift(Ajx, w.s([], 'simpl', '( %s -> %s )' % (Ajx, A)), jxU)
    etj, lej, _, _, _ = term(Ajx, 'j', jn, lambda st, f: ad(w, Ajx, st, f), ljx)
    fvj = D(w, Ajx, 'eqtrd', [D(w, Ajx, 'fveq1d', [fv1(w, Ajx, 'n', 'NN', inner, 'j', jn, ('mptex', [uex]))], '( ( %s ` j ) ` x ) = ( %s ` x )' % (F, inner('j'))),
                              fv1(w, Ajx, 'z', U, lambda v: ET('j', v), 'x', jxU, 'ovex')], '( ( %s ` j ) ` x ) = %s' % (F, ET('j', 'x')))
    hvj, _, _ = hval(Ajx, 'j', jn, lambda st, f: ad(w, Ajx, st, f))
    bj = D(w, Ajx, 'breqtrrd', [D(w, Ajx, 'eqbrtrd', [D(w, Ajx, 'fveq2d', [fvj], '( abs ` ( ( %s ` j ) ` x ) ) = ( abs ` %s )' % (F, ET('j', 'x'))), lej],
                                   '( abs ` ( ( %s ` j ) ` x ) ) <_ %s' % (F, HH('j'))), hvj], '( abs ` ( ( %s ` j ) ` x ) ) <_ ( %s ` j )' % (F, Hm))
    ballx = D(w, A, 'ralrimivva', [bj], 'A. j e. NN A. x e. %s ( abs ` ( ( %s ` j ) ` x ) ) <_ ( %s ` j )' % (U, F, Hm))
    cbx = w.s([w.s([w.s([w.s([w.s([], 'fveq2', '( x = y -> ( ( %s ` j ) ` x ) = ( ( %s ` j ) ` y ) )' % (F, F))], 'fveq2d', '( x = y -> ( abs ` ( ( %s ` j ) ` x ) ) = ( abs ` ( ( %s ` j ) ` y ) ) )' % (F, F))],
                              'breq1d', '( x = y -> ( ( abs ` ( ( %s ` j ) ` x ) ) <_ ( %s ` j ) <-> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) ) )' % (F, Hm, F, Hm))], 'cbvralvw',
                        '( A. x e. %s ( abs ` ( ( %s ` j ) ` x ) ) <_ ( %s ` j ) <-> A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (U, F, Hm, U, F, Hm))], 'ralbii',
              '( A. j e. NN A. x e. %s ( abs ` ( ( %s ` j ) ` x ) ) <_ ( %s ` j ) <-> A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (U, F, Hm, U, F, Hm))
    ball = D(w, A, 'sylib', [ballx, cbx], 'A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (U, F, Hm))
    UHt = L.UH.replace('F', F).replace('H', Hm) % (U, U) if False else ('( %s : NN --> ( CC ^m %s ) /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) ) )'
                                                                              % (F, U, Hm, Hm, U, F, Hm))
    uh = D(w, A, 'jca', [fF, D(w, A, '3jca', [hf, ms, ball], UHt[UHt.index('( %s : NN --> RR' % Hm):-2])], UHt)
    # integrability of every term
    Aj = '( %s /\\ j e. NN )' % A
    jn1 = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    jr = D(w, Aj, 'nnred', [jn1], 'j e. RR'); j0 = D(w, Aj, 'ltled', [cst(w, Aj, '0re', '0 e. RR'), jr, D(w, Aj, 'nngt0d', [jn1], '0 < j')], '0 <_ j')
    _, jpr, _ = np_facts(w, Aj, ad(w, Aj, pp, 'P e. { 0 , 1 }'), 'j', jr, j0)
    ibj = ibl_gen(w, Aj, '( 1 / t )', 't', ad(w, Aj, itr, '( 1 / t ) e. RR'), ad(w, Aj, itp, '( 1 / t ) e. RR+'), ad(w, Aj, tr, 't e. RR'), ET('j', 'x'), 'W',
                  {'__W': ad(w, Aj, wc, 'W e. CC'), '( C ` j )': D(w, Aj, 'ffvelcdmd', [ad(w, Aj, cf, 'C : NN --> CC'), jn1], '( C ` j ) e. CC'), '( j ^ P )': D(w, Aj, 'recnd', [jpr], '( j ^ P ) e. CC'),
                   'M': ad(w, Aj, mrp, 'M e. RR+'), '( _pi x. ( j ^ 2 ) )': D(w, Aj, 'mulcld', [cst(w, Aj, 'picn', '_pi e. CC'), D(w, Aj, 'sqcld', [D(w, Aj, 'nncnd', [jn1], 'j e. CC')], '( j ^ 2 ) e. CC')], '( _pi x. ( j ^ 2 ) ) e. CC')})
    fj = D(w, Aj, 'eqeltrd', [fv1(w, Aj, 'n', 'NN', inner, 'j', jn1, ('mptex', [uex])), D(w, Aj, 'eqeltrrd', [w.s([cbe('j')], 'a1i', '( %s -> %s = %s )' % (Aj, innerx('j'), inner('j'))), ibj], '%s e. L^1' % inner('j'))], '( %s ` j ) e. L^1' % F)
    iball = D(w, A, 'ralrimiva', [fj], 'A. j e. NN ( %s ` j ) e. L^1' % F)
    mex = D(w, A, 'syl3anc', [D(w, A, 'jca', [itr, tr], '( ( 1 / t ) e. RR /\\ t e. RR )'), uh, iball, w.inst('zl3mex')],
            'S. %s sum_ k e. NN ( ( %s ` k ) ` x ) _d x = sum_ k e. NN S. %s ( ( %s ` k ) ` x ) _d x' % (U, F, U, F))
    # the left side: the series under the integral is THP x. x ^c ( W - 1 )
    Axk = '( %s /\\ k e. NN )' % Ax
    kx = w.s([], 'simpr', '( %s -> k e. NN )' % Axk)
    etk, lek, tck, tlek, _ = term(Axk, 'k', kx, lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Axk, f)), lambda st, f: ad(w, Axk, st, f))
    xUk = ad(w, Axk, xU, 'x e. %s' % U)
    fvk = D(w, Axk, 'eqtrd', [D(w, Axk, 'fveq1d', [fv1(w, Axk, 'n', 'NN', inner, 'k', kx, ('mptex', [uex]))], '( ( %s ` k ) ` x ) = ( %s ` x )' % (F, inner('k'))),
                              fv1(w, Axk, 'z', U, lambda v: ET('k', v), 'x', xUk, 'ovex')], '( ( %s ` k ) ` x ) = %s' % (F, ET('k', 'x')))
    se = D(w, Ax, 'sumeq2dv', [fvk], 'sum_ k e. NN ( ( %s ` k ) ` x ) = sum_ k e. NN %s' % (F, ET('k', 'x')))
    G_ = '( n e. NN |-> %s )' % TT('n', 'x')
    gvk = fv1(w, Axk, 'n', 'NN', lambda v: TT(v, 'x'), 'k', kx, 'ovex')
    gms = D(w, Ax, 'simpld', [D(w, Ax, 'zl3mser', [ad(w, Ax, D(w, A, 'rpred', [D(w, A, 'rpefcld', [D(w, A, 'rpred', [D(w, A, 'rpreccld', [D(w, A, 'rpmulcld', [cst(w, A, 'pirp', '_pi e. RR+'), D(w, A, 'rpdivcld', [itp, mrp], '( ( 1 / t ) / M ) e. RR+')],
                                                                                                                                                  '( _pi x. ( ( 1 / t ) / M ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR+')], '( 1 / ( _pi x. ( ( 1 / t ) / M ) ) ) e. RR')],
                                                                                         '%s e. RR+' % KE('( 1 / t )'))], '%s e. RR' % KE('( 1 / t )')), '%s e. RR' % KE('( 1 / t )')),
                                                  cst(w, Ax, 'halfre', '( 1 / 2 ) e. RR'), cst(w, Ax, 'halfge0', '0 <_ ( 1 / 2 )'), cst(w, Ax, 'halflt1', '( 1 / 2 ) < 1'),
                                                  D(w, Axk, 'eqeltrd', [gvk, tck], '( %s ` k ) e. CC' % G_),
                                                  D(w, Axk, 'eqbrtrd', [D(w, Axk, 'fveq2d', [gvk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (G_, TT('k', 'x'))), tlek], '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (G_, KE('( 1 / t )')))],
                                  '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) )' % (G_, G_, KE('( 1 / t )')))],
              'seq 1 ( + , %s ) e. dom ~~>' % G_)
    imc = D(w, Ax, 'isummulc1', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, Ax, '1z', '1 e. ZZ'), gvk, tck, gms, xwc], '( sum_ k e. NN %s x. %s ) = sum_ k e. NN %s' % (TT('k', 'x'), XW, ET('k', 'x')))
    cbs = w.s([vsub(w, lambda v: TT(v, 'x'), 'k', 'n')], 'cbvsumv', 'sum_ k e. NN %s = %s' % (TT('k', 'x'), THP('C', 'x', 'P')))
    lhs_x = chain(w, Ax, ['sum_ k e. NN ( ( %s ` k ) ` x )' % F, 'sum_ k e. NN %s' % ET('k', 'x'), '( sum_ k e. NN %s x. %s )' % (TT('k', 'x'), XW), '( %s x. %s )' % (THP('C', 'x', 'P'), XW)],
                  [se, ('r', imc), D(w, Ax, 'oveq1d', [w.s([cbs], 'a1i', '( %s -> sum_ k e. NN %s = %s )' % (Ax, TT('k', 'x'), THP('C', 'x', 'P')))], '( sum_ k e. NN %s x. %s ) = ( %s x. %s )' % (TT('k', 'x'), XW, THP('C', 'x', 'P'), XW))])
    lhs = D(w, A, 'itgeq2dv', [lhs_x], 'S. %s sum_ k e. NN ( ( %s ` k ) ` x ) _d x = %s' % (U, F, L.MTI('W', 't')))
    # the right side: each term is CK x. EUI
    Akx = '( %s /\\ x e. %s )' % (Ak, U)
    lkx = xlift(Akx, w.s([], 'simpll', '( %s -> %s )' % (Akx, A)), w.s([], 'simpr', '( %s -> x e. %s )' % (Akx, U)))
    kn2 = w.s([], 'simplr', '( %s -> k e. NN )' % Akx)
    etk2, _, tck2, _, _ = term(Akx, 'k', kn2, lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Akx, f)), lkx)
    xU2 = w.s([], 'simpr', '( %s -> x e. %s )' % (Akx, U))
    fvk2 = D(w, Akx, 'eqtrd', [D(w, Akx, 'fveq1d', [fv1(w, Akx, 'n', 'NN', inner, 'k', kn2, ('mptex', [uex]))], '( ( %s ` k ) ` x ) = ( %s ` x )' % (F, inner('k'))),
                               fv1(w, Akx, 'z', U, lambda v: ET('k', v), 'x', xU2, 'ovex')], '( ( %s ` k ) ` x ) = %s' % (F, ET('k', 'x')))
    LNk = L.LN('k')
    EL = '( exp ` -u ( %s x. x ) )' % LNk
    ck = D(w, Akx, 'ffvelcdmd', [w.s([cf], 'ad2antrr', '( %s -> C : NN --> CC )' % Akx), kn2], '( C ` k ) e. CC')
    kr2 = D(w, Akx, 'nnred', [kn2], 'k e. RR'); k02 = D(w, Akx, 'ltled', [cst(w, Akx, '0re', '0 e. RR'), kr2, D(w, Akx, 'nngt0d', [kn2], '0 < k')], '0 <_ k')
    _, kpr2, _ = np_facts(w, Akx, w.s([pp], 'ad2antrr', '( %s -> P e. { 0 , 1 } )' % Akx), 'k', kr2, k02)
    kpc = D(w, Akx, 'recnd', [kpr2], '( k ^ P ) e. CC')
    xc2 = D(w, Akx, 'rpcnd', [lkx(xrp, 'x e. RR+')], 'x e. CC')
    pk2 = D(w, Akx, 'mulcld', [cst(w, Akx, 'picn', '_pi e. CC'), D(w, Akx, 'sqcld', [D(w, Akx, 'nncnd', [kn2], 'k e. CC')], '( k ^ 2 ) e. CC')], '( _pi x. ( k ^ 2 ) ) e. CC')
    mc2 = D(w, Akx, 'rpcnd', [w.s([mrp], 'ad2antrr', '( %s -> M e. RR+ )' % Akx)], 'M e. CC'); mne2 = D(w, Akx, 'rpne0d', [w.s([mrp], 'ad2antrr', '( %s -> M e. RR+ )' % Akx)], 'M =/= 0')
    ag = chain(w, Akx, ['( ( _pi x. ( k ^ 2 ) ) x. ( x / M ) )', '( x x. %s )' % LNk, '( %s x. x )' % LNk],
               [D(w, Akx, 'div12d', [pk2, xc2, mc2, mne2], '( ( _pi x. ( k ^ 2 ) ) x. ( x / M ) ) = ( x x. %s )' % LNk),
                D(w, Akx, 'mulcomd', [xc2, D(w, Akx, 'divcld', [pk2, mc2, mne2], '%s e. CC' % LNk)], '( x x. %s ) = ( %s x. x )' % (LNk, LNk))])
    exl = D(w, Akx, 'fveq2d', [D(w, Akx, 'negeqd', [ag], '-u ( ( _pi x. ( k ^ 2 ) ) x. ( x / M ) ) = -u ( %s x. x )' % LNk)], '%s = %s' % (EXv('k', 'x'), EL))
    exc = D(w, Akx, 'efcld', [D(w, Akx, 'negcld', [D(w, Akx, 'mulcld', [pk2, D(w, Akx, 'divcld', [xc2, mc2, mne2], '( x / M ) e. CC')], '( ( _pi x. ( k ^ 2 ) ) x. ( x / M ) ) e. CC')],
                                               '-u ( ( _pi x. ( k ^ 2 ) ) x. ( x / M ) ) e. CC')], '%s e. CC' % EXv('k', 'x'))
    xwc2 = lkx(xwc, '%s e. CC' % XW)
    ide = chain(w, Akx, [ET('k', 'x'), '( ( %s x. %s ) x. %s )' % (L.CK('k'), EXv('k', 'x'), XW), '( %s x. ( %s x. %s ) )' % (L.CK('k'), EXv('k', 'x'), XW), '( %s x. %s )' % (L.CK('k'), FX('W', LNk))],
                [D(w, Akx, 'oveq1d', [D(w, Akx, 'eqcomd', [D(w, Akx, 'mulassd', [ck, kpc, exc], '( %s x. %s ) = %s' % (L.CK('k'), EXv('k', 'x'), TT('k', 'x')))], '%s = ( %s x. %s )' % (TT('k', 'x'), L.CK('k'), EXv('k', 'x')))],
                   '%s = ( ( %s x. %s ) x. %s )' % (ET('k', 'x'), L.CK('k'), EXv('k', 'x'), XW)),
                 D(w, Akx, 'mulassd', [D(w, Akx, 'mulcld', [ck, kpc], '%s e. CC' % L.CK('k')), exc, xwc2], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (L.CK('k'), EXv('k', 'x'), XW, L.CK('k'), EXv('k', 'x'), XW)),
                 D(w, Akx, 'oveq2d', [D(w, Akx, 'oveq1d', [exl], '( %s x. %s ) = %s' % (EXv('k', 'x'), XW, FX('W', LNk)))], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (L.CK('k'), EXv('k', 'x'), XW, L.CK('k'), FX('W', LNk)))])
    ie = D(w, Ak, 'itgeq2dv', [D(w, Akx, 'eqtrd', [fvk2, ide], '( ( %s ` k ) ` x ) = ( %s x. %s )' % (F, L.CK('k'), FX('W', LNk)))],
           'S. %s ( ( %s ` k ) ` x ) _d x = S. %s ( %s x. %s ) _d x' % (U, F, U, L.CK('k'), FX('W', LNk)))
    lnc = D(w, Ak, 'divcld', [D(w, Ak, 'mulcld', [cst(w, Ak, 'picn', '_pi e. CC'), D(w, Ak, 'sqcld', [D(w, Ak, 'nncnd', [kn], 'k e. CC')], '( k ^ 2 ) e. CC')], '( _pi x. ( k ^ 2 ) ) e. CC'),
                              D(w, Ak, 'rpcnd', [ad(w, Ak, mrp, 'M e. RR+')], 'M e. CC'), D(w, Ak, 'rpne0d', [ad(w, Ak, mrp, 'M e. RR+')], 'M =/= 0')], '%s e. CC' % LNk)
    wck = ad(w, Ak, wc, 'W e. CC')
    fxi = gibl(w, Ak, '( 1 / t )', 't', ad(w, Ak, itr, '( 1 / t ) e. RR'), ad(w, Ak, tr, 't e. RR'), 'W', LNk, wck, lnc, prp=ad(w, Ak, itp, '( 1 / t ) e. RR+'))
    fxc = fx_cl(w, Ak, '( 1 / t )', 't', ad(w, Ak, itr, '( 1 / t ) e. RR'), 'W', LNk, wck, lnc, None)
    kr_ = D(w, Ak, 'nnred', [kn], 'k e. RR'); k0_ = D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), kr_, D(w, Ak, 'nngt0d', [kn], '0 < k')], '0 <_ k')
    _, kpr_, _ = np_facts(w, Ak, ad(w, Ak, pp, 'P e. { 0 , 1 }'), 'k', kr_, k0_)
    ckc = D(w, Ak, 'mulcld', [D(w, Ak, 'ffvelcdmd', [ad(w, Ak, cf, 'C : NN --> CC'), kn], '( C ` k ) e. CC'), D(w, Ak, 'recnd', [kpr_], '( k ^ P ) e. CC')], '%s e. CC' % L.CK('k'))
    im2 = D(w, Ak, 'itgmulc2', [ckc, fxc, fxi], '( %s x. %s ) = S. %s ( %s x. %s ) _d x' % (L.CK('k'), EUI('W', LNk, 't'), U, L.CK('k'), FX('W', LNk)))
    rk = D(w, Ak, 'eqtr4d', [ie, im2], 'S. %s ( ( %s ` k ) ` x ) _d x = ( %s x. %s )' % (U, F, L.CK('k'), EUI('W', LNk, 't')))
    rhs = D(w, A, 'sumeq2dv', [rk], 'sum_ k e. NN S. %s ( ( %s ` k ) ` x ) _d x = sum_ k e. NN ( %s x. %s )' % (U, F, L.CK('k'), EUI('W', LNk, 't')))
    w.qed([D(w, A, 'eqtr3d', [lhs, mex], '%s = sum_ k e. NN S. %s ( ( %s ` k ) ` x ) _d x' % (L.MTI('W', 't'), U, F)), rhs], 'eqtrd', S['zl3mtw'])
    go(w)


# ---------------------------------------------------------------- zl3mlm
if want('zl3mlm'):
    w = W('zl3mlm', 'The Mellin transform of the theta series: ` lim_t S. ( 1 / t , t ) TH ( x ) x ^ ( w - 1 ) = ( M / pi ) ^ w Gamma ( w ) sum C ( k ) k ^ -S ` , ` w = ( S + P ) / 2 ` , ` 1 < Re S ` ( ~ zl3tan , ~ zl3mtw , ~ zl3ew2 , ~ zl3ewb ).')
    A, Cc = ante_of('zl3mlm')
    ta = D(w, A, 'simpl', [], L.TA); sc = D(w, A, 'simprl', [], 'S e. CC'); s1 = D(w, A, 'simprr', [], '1 < ( Re ` S )')
    mn, pp, cf, bnd, mrp = ta_ctx(w, A, ta)
    pn = p_nn0(w, A, pp); prr = D(w, A, 'nn0red', [pn], 'P e. RR'); pc = D(w, A, 'nn0cnd', [pn], 'P e. CC'); p0 = D(w, A, 'nn0ge0d', [pn], '0 <_ P')
    W_ = L.WS('S'); RS = '( Re ` S )'; SG = L.WS(RS)
    rsr = D(w, A, 'recld', [sc], '%s e. RR' % RS)
    wc = D(w, A, 'divcld', [D(w, A, 'addcld', [sc, pc], '( S + P ) e. CC'), cst(w, A, '2cn', '2 e. CC'), cst(w, A, '2ne0', '2 =/= 0')], '%s e. CC' % W_)
    sgr = D(w, A, 'rehalfcld' if False else 'redivcld', [D(w, A, 'readdcld', [rsr, prr], '( %s + P ) e. RR' % RS), cst(w, A, '2re', '2 e. RR'), cst(w, A, '2ne0', '2 =/= 0')], '%s e. RR' % SG)
    sg0 = linarith(w, A, [s1, p0], '0 < %s' % SG, leaves={RS: rsr, 'P': prr}, atoms=[RS])
    sgp = D(w, A, 'elrpd', [sgr, sg0], '%s e. RR+' % SG)
    rw = chain(w, A, ['( Re ` %s )' % W_, '( ( Re ` ( S + P ) ) / 2 )', '( ( %s + ( Re ` P ) ) / 2 )' % RS, SG],
               [D(w, A, 'redivd', [cst(w, A, '2re', '2 e. RR'), D(w, A, 'addcld', [sc, pc], '( S + P ) e. CC'), cst(w, A, '2ne0', '2 =/= 0')], '( Re ` %s ) = ( ( Re ` ( S + P ) ) / 2 )' % W_),
                D(w, A, 'oveq1d', [D(w, A, 'readdd', [sc, pc], '( Re ` ( S + P ) ) = ( %s + ( Re ` P ) )' % RS)], '( ( Re ` ( S + P ) ) / 2 ) = ( ( %s + ( Re ` P ) ) / 2 )' % RS),
                D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'rered', [prr], '( Re ` P ) = P')], '( %s + ( Re ` P ) ) = ( %s + P )' % (RS, RS))], '( ( %s + ( Re ` P ) ) / 2 ) = %s' % (RS, SG))])
    w0 = D(w, A, 'breqtrrd', [sg0, rw], '0 < ( Re ` %s )' % W_)
    gw = D(w, A, 'syl', [D(w, A, 'syl', [D(w, A, 'jca', [wc, w0], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % W_), w.inst('gamcl')], '( _G ` %s ) e. CC' % W_)
    gsp = D(w, A, 'syl', [sgp, w.inst('rpgamcl')], '( _G ` %s ) e. RR+' % SG)
    MPI = '( M / _pi )'
    mpp = D(w, A, 'rpdivcld', [mrp, cst(w, A, 'pirp', '_pi e. RR+')], '%s e. RR+' % MPI)
    LNm = L.LN
    CK = L.CK
    FU = lambda m, u: '( %s x. %s )' % (CK(m), EUI(W_, LNm(m), u))
    innr = lambda m: '( u e. RR+ |-> %s )' % FU(m, 'u')
    Fm = '( m e. NN |-> %s )' % innr('m')
    HV = lambda m: '( ( %s ^ P ) x. ( ( %s ^c -u %s ) x. ( _G ` %s ) ) )' % (m, LNm(m), SG, SG)
    Hm = '( m e. NN |-> %s )' % HV('m')
    DV = lambda m: '( %s x. ( ( %s ^c -u %s ) x. ( _G ` %s ) ) )' % (CK(m), LNm(m), W_, W_)
    Dm = '( m e. NN |-> %s )' % DV('m')
    def idx(Ac, v, vn, lift):
        """per-index facts: LN rp, v ^ P real / ge0, C ` v in CC, | C ` v | <_ 1"""
        vr = D(w, Ac, 'nnred', [vn], '%s e. RR' % v); v0 = D(w, Ac, 'ltled', [cst(w, Ac, '0re', '0 e. RR'), vr, D(w, Ac, 'nngt0d', [vn], '0 < %s' % v)], '0 <_ %s' % v)
        _, vpr, vp0 = np_facts(w, Ac, lift(pp, 'P e. { 0 , 1 }'), v, vr, v0)
        lnp = D(w, Ac, 'rpdivcld', [D(w, Ac, 'rpmulcld', [cst(w, Ac, 'pirp', '_pi e. RR+'), D(w, Ac, 'rpexpcld' if False else 'nnrpd', [D(w, Ac, 'nnsqcld', [vn], '( %s ^ 2 ) e. NN' % v)], '( %s ^ 2 ) e. RR+' % v)],
                                                         '( _pi x. ( %s ^ 2 ) ) e. RR+' % v), lift(mrp, 'M e. RR+')], '%s e. RR+' % LNm(v))
        cv = D(w, Ac, 'ffvelcdmd', [lift(cf, 'C : NN --> CC'), vn], '( C ` %s ) e. CC' % v)
        return dict(vr=vr, vpr=vpr, vp0=vp0, lnp=lnp, cv=cv, cb=c_bnd(w, Ac, lift(bnd, 'A. i e. NN ( abs ` ( C ` i ) ) <_ 1'), v, vn))

    def sub_out(v):
        """closed ( m = v -> innr ( m ) = innr ( v ) )"""
        ck = vsub(w, CK, 'm', v)
        fx = vsub(w, lambda q: FX(W_, LNm(q)), 'm', v)
        ei = w.s([w.s([fx], 'adantr', '( ( m = %s /\\ x e. ( ( 1 / u ) (,) u ) ) -> %s = %s )' % (v, FX(W_, LNm('m')), FX(W_, LNm(v))))], 'itgeq2dv', '( m = %s -> %s = %s )' % (v, EUI(W_, LNm('m'), 'u'), EUI(W_, LNm(v), 'u')))
        b = w.s([ck, ei], 'oveq12d', '( m = %s -> %s = %s )' % (v, FU('m', 'u'), FU(v, 'u')))
        return w.s([b], 'mpteq2dv', '( m = %s -> %s = %s )' % (v, innr('m'), innr(v)))
    def sub_in(j, v):
        """closed ( u = v -> FU ( j , u ) = FU ( j , v ) )"""
        de = w.s([w.s([], 'oveq2', '( u = %s -> ( 1 / u ) = ( 1 / %s ) )' % (v, v)), w.s([], 'id', '( u = %s -> u = %s )' % (v, v))], 'oveq12d', '( u = %s -> ( ( 1 / u ) (,) u ) = ( ( 1 / %s ) (,) %s ) )' % (v, v, v))
        ie = w.s([de, w.inst('itgeq1')], 'syl', '( u = %s -> %s = %s )' % (v, EUI(W_, LNm(j), 'u'), EUI(W_, LNm(j), v)))
        return w.s([ie], 'oveq2d', '( u = %s -> %s = %s )' % (v, FU(j, 'u'), FU(j, v)))
    # F : NN --> ( CC ^m RR+ )
    rex = w.s([], 'reex' if False else 'rpex' if False else 'rpssre', 'RR+ C_ RR')
    rpv = w.s([w.s([], 'reex', 'RR e. _V'), rex], 'ssexi', 'RR+ e. _V')
    Am = '( %s /\\ m e. NN )' % A
    mnn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
    Amu = '( %s /\\ u e. RR+ )' % Am
    im_ = idx(Amu, 'm', w.s([], 'simplr', '( %s -> m e. NN )' % Amu), lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Amu, f)))
    urp = w.s([], 'simpr', '( %s -> u e. RR+ )' % Amu)
    lnc_mu = D(w, Amu, 'rpcnd', [im_['lnp']], '%s e. CC' % LNm('m'))
    wcu = w.s([wc], 'ad2antrr', '( %s -> %s e. CC )' % (Amu, W_))
    iu = D(w, Amu, 'rpreccld', [urp], '( 1 / u ) e. RR+')
    eui_c = D(w, Amu, 'itgcl', [gibl(w, Amu, '( 1 / u )', 'u', D(w, Amu, 'rpred', [iu], '( 1 / u ) e. RR'), D(w, Amu, 'rpred', [urp], 'u e. RR'), W_, LNm('m'), wcu, lnc_mu, prp=iu),
                                fx_cl(w, Amu, '( 1 / u )', 'u', D(w, Amu, 'rpred', [iu], '( 1 / u ) e. RR'), W_, LNm('m'), wcu, lnc_mu, None)], '%s e. CC' % EUI(W_, LNm('m'), 'u'))
    cku = D(w, Amu, 'mulcld', [im_['cv'], D(w, Amu, 'recnd', [im_['vpr']], '( m ^ P ) e. CC')], '%s e. CC' % CK('m'))
    fuc = D(w, Amu, 'mulcld', [cku, eui_c], '%s e. CC' % FU('m', 'u'))
    iff = D(w, Am, 'fmptd', [fuc, w.s([], 'eqid', '%s = %s' % (innr('m'), innr('m')))], '%s : RR+ --> CC' % innr('m'))
    elm = w.s([w.s([w.s([], 'cnex', 'CC e. _V'), rpv], 'pm3.2i', '( CC e. _V /\\ RR+ e. _V )'), w.inst('elmapg')], 'ax-mp', '( %s e. ( CC ^m RR+ ) <-> %s : RR+ --> CC )' % (innr('m'), innr('m')))
    ime = D(w, Am, 'mpbird', [iff, w.s([elm], 'a1i', '( %s -> ( %s e. ( CC ^m RR+ ) <-> %s : RR+ --> CC ) )' % (Am, innr('m'), innr('m')))], '%s e. ( CC ^m RR+ )' % innr('m'))
    fF = D(w, A, 'fmptd', [ime, w.s([], 'eqid', '%s = %s' % (Fm, Fm))], '%s : NN --> ( CC ^m RR+ )' % Fm)
    # the majorant H
    im = idx(Am, 'm', mnn, lambda st, f: ad(w, Am, st, f))
    def hvr(Ac, v, ix, lift):
        lc_ = D(w, Ac, 'rpcxpcld', [ix['lnp'], D(w, Ac, 'renegcld', [lift(sgr, '%s e. RR' % SG)], '-u %s e. RR' % SG)], '( %s ^c -u %s ) e. RR+' % (LNm(v), SG))
        g_ = D(w, Ac, 'rpmulcld', [lc_, lift(gsp, '( _G ` %s ) e. RR+' % SG)], '( ( %s ^c -u %s ) x. ( _G ` %s ) ) e. RR+' % (LNm(v), SG, SG))
        return D(w, Ac, 'remulcld', [ix['vpr'], D(w, Ac, 'rpred', [g_], '( ( %s ^c -u %s ) x. ( _G ` %s ) ) e. RR' % (LNm(v), SG, SG))], '%s e. RR' % HV(v)), g_
    hrm, _ = hvr(Am, 'm', im, lambda st, f: ad(w, Am, st, f))
    hf = D(w, A, 'fmptd', [hrm, w.s([], 'eqid', '%s = %s' % (Hm, Hm))], '%s : NN --> RR' % Hm)
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    ik = idx(Ak, 'k', kn, lambda st, f: ad(w, Ak, st, f))
    Zm = '( m e. NN |-> ( m ^c -u %s ) )' % RS
    zv = fv1(w, Ak, 'm', 'NN', lambda v: '( %s ^c -u %s )' % (v, RS), 'k', kn, 'ovex')
    krp = D(w, Ak, 'nnrpd', [kn], 'k e. RR+')
    zrp = D(w, Ak, 'rpcxpcld', [krp, D(w, Ak, 'renegcld', [ad(w, Ak, rsr, '%s e. RR' % RS)], '-u %s e. RR' % RS)], '( k ^c -u %s ) e. RR+' % RS)
    zcv = D(w, A, 'zetacvg', [D(w, A, 'recnd', [rsr], '%s e. CC' % RS), D(w, A, 'breqtrrd', [s1, D(w, A, 'rered', [rsr], '( Re ` %s ) = %s' % (RS, RS))], '1 < ( Re ` %s )' % RS), zv], 'seq 1 ( + , %s ) e. dom ~~>' % Zm)
    MSG = '( %s ^c %s )' % (MPI, SG)
    K1 = '( %s x. ( _G ` %s ) )' % (MSG, SG)
    msgp = D(w, A, 'rpcxpcld', [mpp, sgr], '%s e. RR+' % MSG)
    k1p = D(w, A, 'rpmulcld', [msgp, gsp], '%s e. RR+' % K1)
    hvk = fv1(w, Ak, 'm', 'NN', HV, 'k', kn, 'ovex')
    hrk, gk_ = hvr(Ak, 'k', ik, lambda st, f: ad(w, Ak, st, f))
    lnwk = D(w, Ak, 'syl3anc', [ad(w, Ak, D(w, A, 'simpld', [ta], L.MP), L.MP), kn, ad(w, Ak, D(w, A, 'recnd', [rsr], '%s e. CC' % RS), '%s e. CC' % RS), w.inst('zl3lnw')],
             '( ( k ^ P ) x. ( %s ^c -u %s ) ) = ( %s x. ( k ^c -u %s ) )' % (LNm('k'), SG, MSG, RS))
    kpc = D(w, Ak, 'recnd', [ik['vpr']], '( k ^ P ) e. CC')
    lsc = D(w, Ak, 'rpcnd', [D(w, Ak, 'rpcxpcld', [ik['lnp'], D(w, Ak, 'renegcld', [ad(w, Ak, sgr, '%s e. RR' % SG)], '-u %s e. RR' % SG)], '( %s ^c -u %s ) e. RR+' % (LNm('k'), SG))], '( %s ^c -u %s ) e. CC' % (LNm('k'), SG))
    gsc = D(w, Ak, 'rpcnd', [ad(w, Ak, gsp, '( _G ` %s ) e. RR+' % SG)], '( _G ` %s ) e. CC' % SG)
    msc = D(w, Ak, 'rpcnd', [ad(w, Ak, msgp, '%s e. RR+' % MSG)], '%s e. CC' % MSG)
    zkc = D(w, Ak, 'rpcnd', [zrp], '( k ^c -u %s ) e. CC' % RS)
    hk_eq = chain(w, Ak, ['( %s ` k )' % Hm, HV('k'), '( ( ( k ^ P ) x. ( %s ^c -u %s ) ) x. ( _G ` %s ) )' % (LNm('k'), SG, SG), '( ( %s x. ( k ^c -u %s ) ) x. ( _G ` %s ) )' % (MSG, RS, SG),
                          '( %s x. ( k ^c -u %s ) )' % (K1, RS), '( %s x. ( %s ` k ) )' % (K1, Zm)],
                  [hvk, ('r', D(w, Ak, 'mulassd', [kpc, lsc, gsc], '( ( ( k ^ P ) x. ( %s ^c -u %s ) ) x. ( _G ` %s ) ) = %s' % (LNm('k'), SG, SG, HV('k')))),
                   D(w, Ak, 'oveq1d', [lnwk], '( ( ( k ^ P ) x. ( %s ^c -u %s ) ) x. ( _G ` %s ) ) = ( ( %s x. ( k ^c -u %s ) ) x. ( _G ` %s ) )' % (LNm('k'), SG, SG, MSG, RS, SG)),
                   D(w, Ak, 'mul32d', [msc, zkc, gsc], '( ( %s x. ( k ^c -u %s ) ) x. ( _G ` %s ) ) = %s' % (MSG, RS, SG, '( %s x. ( k ^c -u %s ) )' % (K1, RS))),
                   D(w, Ak, 'oveq2d', [D(w, Ak, 'eqcomd', [zv], '( k ^c -u %s ) = ( %s ` k )' % (RS, Zm))], '( %s x. ( k ^c -u %s ) ) = ( %s x. ( %s ` k ) )' % (K1, RS, K1, Zm))])
    k1zr = D(w, Ak, 'rpmulcld', [ad(w, Ak, k1p, '%s e. RR+' % K1), D(w, Ak, 'eqeltrd', [zv, zrp], '( %s ` k ) e. RR+' % Zm)], '( %s x. ( %s ` k ) ) e. RR+' % (K1, Zm))
    habs = D(w, Ak, 'eqtrd', [D(w, Ak, 'fveq2d', [hk_eq], '( abs ` ( %s ` k ) ) = ( abs ` ( %s x. ( %s ` k ) ) )' % (Hm, K1, Zm)),
                              D(w, Ak, 'absidd', [D(w, Ak, 'rpred', [k1zr], '( %s x. ( %s ` k ) ) e. RR' % (K1, Zm)), D(w, Ak, 'rpge0d', [k1zr], '0 <_ ( %s x. ( %s ` k ) )' % (K1, Zm))],
                                '( abs ` ( %s x. ( %s ` k ) ) ) = ( %s x. ( %s ` k ) )' % (K1, Zm, K1, Zm))], '( abs ` ( %s ` k ) ) = ( %s x. ( %s ` k ) )' % (Hm, K1, Zm))
    hle = D(w, Ak, 'eqbrtrd', [habs, D(w, Ak, 'leidd', [D(w, Ak, 'rpred', [k1zr], '( %s x. ( %s ` k ) ) e. RR' % (K1, Zm))], '( %s x. ( %s ` k ) ) <_ ( %s x. ( %s ` k ) )' % (K1, Zm, K1, Zm))],
            '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) )' % (Hm, K1, Zm))
    Aku = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A
    knu = D(w, Aku, 'eleqtrrd', [w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Aku), cst(w, Aku, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'k e. NN')
    liftu = lambda st, f: w.s([w.s([], 'simpl', '( %s -> %s )' % (Aku, A)), knu, st], 'syl2anc', '( %s -> %s )' % (Aku, f))
    hs = D(w, A, 'cvgcmpce', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1nn', '1 e. NN'), D(w, Ak, 'rpred', [D(w, Ak, 'eqeltrd', [zv, zrp], '( %s ` k ) e. RR+' % Zm)], '( %s ` k ) e. RR' % Zm),
                              D(w, Ak, 'eqeltrd', [hvk, D(w, Ak, 'recnd', [hrk], '%s e. CC' % HV('k'))], '( %s ` k ) e. CC' % Hm), zcv, D(w, A, 'rpred', [k1p], '%s e. RR' % K1),
                              liftu(hle, '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) )' % (Hm, K1, Zm))], 'seq 1 ( + , %s ) e. dom ~~>' % Hm)
    # the bound at ( j , y )
    Ajy = '( %s /\\ ( j e. NN /\\ y e. RR+ ) )' % A
    jn = w.s([], 'simprl', '( %s -> j e. NN )' % Ajy); yrp = w.s([], 'simprr', '( %s -> y e. RR+ )' % Ajy)
    ij = idx(Ajy, 'j', jn, lambda st, f: ad(w, Ajy, st, f))
    fvjy = D(w, Ajy, 'eqtrd', [D(w, Ajy, 'fveq1d', [fv1(w, Ajy, 'm', 'NN', innr, 'j', jn, ('mptex', [rpv]), sub=sub_out('j'))], '( ( %s ` j ) ` y ) = ( %s ` y )' % (Fm, innr('j'))),
                               fv1(w, Ajy, 'u', 'RR+', lambda v: FU('j', v), 'y', yrp, 'ovex', sub=sub_in('j', 'y'))], '( ( %s ` j ) ` y ) = %s' % (Fm, FU('j', 'y')))
    wcj = ad(w, Ajy, wc, '%s e. CC' % W_)
    iy = D(w, Ajy, 'rpreccld', [yrp], '( 1 / y ) e. RR+')
    euc = D(w, Ajy, 'itgcl', [gibl(w, Ajy, '( 1 / y )', 'y', D(w, Ajy, 'rpred', [iy], '( 1 / y ) e. RR'), D(w, Ajy, 'rpred', [yrp], 'y e. RR'), W_, LNm('j'), wcj, D(w, Ajy, 'rpcnd', [ij['lnp']], '%s e. CC' % LNm('j')), prp=iy),
                              fx_cl(w, Ajy, '( 1 / y )', 'y', D(w, Ajy, 'rpred', [iy], '( 1 / y ) e. RR'), W_, LNm('j'), wcj, D(w, Ajy, 'rpcnd', [ij['lnp']], '%s e. CC' % LNm('j')), None)], '%s e. CC' % EUI(W_, LNm('j'), 'y'))
    ewb = D(w, Ajy, 'syl3anc', [ad(w, Ajy, D(w, A, 'jca', [wc, w0], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), ij['lnp'], yrp, w.inst('zl3ewb')],
            '( abs ` %s ) <_ ( ( %s ^c -u ( Re ` %s ) ) x. ( _G ` ( Re ` %s ) ) )' % (EUI(W_, LNm('j'), 'y'), LNm('j'), W_, W_))
    rwj = ad(w, Ajy, rw, '( Re ` %s ) = %s' % (W_, SG))
    rb, _ = w.rewrite('( ( %s ^c -u ( Re ` %s ) ) x. ( _G ` ( Re ` %s ) ) )' % (LNm('j'), W_, W_), {'( Re ` %s )' % W_: (SG, rwj)}, Ajy)
    ewb2 = D(w, Ajy, 'breqtrd', [ewb, rb], '( abs ` %s ) <_ ( ( %s ^c -u %s ) x. ( _G ` %s ) )' % (EUI(W_, LNm('j'), 'y'), LNm('j'), SG, SG))
    ckj = D(w, Ajy, 'mulcld', [ij['cv'], D(w, Ajy, 'recnd', [ij['vpr']], '( j ^ P ) e. CC')], '%s e. CC' % CK('j'))
    ack = chain(w, Ajy, ['( abs ` %s )' % CK('j'), '( ( abs ` ( C ` j ) ) x. ( abs ` ( j ^ P ) ) )', '( ( abs ` ( C ` j ) ) x. ( j ^ P ) )'],
                [D(w, Ajy, 'absmuld', [ij['cv'], D(w, Ajy, 'recnd', [ij['vpr']], '( j ^ P ) e. CC')], '( abs ` %s ) = ( ( abs ` ( C ` j ) ) x. ( abs ` ( j ^ P ) ) )' % CK('j')),
                 D(w, Ajy, 'oveq2d', [D(w, Ajy, 'absidd', [ij['vpr'], ij['vp0']], '( abs ` ( j ^ P ) ) = ( j ^ P )')], '( ( abs ` ( C ` j ) ) x. ( abs ` ( j ^ P ) ) ) = ( ( abs ` ( C ` j ) ) x. ( j ^ P ) )')])
    ckl = D(w, Ajy, 'breqtrd', [D(w, Ajy, 'eqbrtrd', [ack, D(w, Ajy, 'lemul1ad', [D(w, Ajy, 'abscld', [ij['cv']], '( abs ` ( C ` j ) ) e. RR'), cst(w, Ajy, '1re', '1 e. RR'), ij['vpr'], ij['vp0'], ij['cb']],
                                                                    '( ( abs ` ( C ` j ) ) x. ( j ^ P ) ) <_ ( 1 x. ( j ^ P ) )')], '( abs ` %s ) <_ ( 1 x. ( j ^ P ) )' % CK('j')),
                                 D(w, Ajy, 'mullidd', [D(w, Ajy, 'recnd', [ij['vpr']], '( j ^ P ) e. CC')], '( 1 x. ( j ^ P ) ) = ( j ^ P )')], '( abs ` %s ) <_ ( j ^ P )' % CK('j'))
    _, gj_ = hvr(Ajy, 'j', ij, lambda st, f: ad(w, Ajy, st, f))
    pr12 = D(w, Ajy, 'lemul12ad', [D(w, Ajy, 'abscld', [ckj], '( abs ` %s ) e. RR' % CK('j')), ij['vpr'], D(w, Ajy, 'abscld', [euc], '( abs ` %s ) e. RR' % EUI(W_, LNm('j'), 'y')),
                                   D(w, Ajy, 'rpred', [gj_], '( ( %s ^c -u %s ) x. ( _G ` %s ) ) e. RR' % (LNm('j'), SG, SG)), D(w, Ajy, 'absge0d', [ckj], '0 <_ ( abs ` %s )' % CK('j')),
                                   D(w, Ajy, 'absge0d', [euc], '0 <_ ( abs ` %s )' % EUI(W_, LNm('j'), 'y')), ckl, ewb2],
             '( ( abs ` %s ) x. ( abs ` %s ) ) <_ %s' % (CK('j'), EUI(W_, LNm('j'), 'y'), HV('j')))
    bj = chain(w, Ajy, ['( abs ` ( ( %s ` j ) ` y ) )' % Fm, '( abs ` %s )' % FU('j', 'y'), '( ( abs ` %s ) x. ( abs ` %s ) )' % (CK('j'), EUI(W_, LNm('j'), 'y'))],
               [D(w, Ajy, 'fveq2d', [fvjy], '( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s )' % (Fm, FU('j', 'y'))), D(w, Ajy, 'absmuld', [ckj, euc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (FU('j', 'y'), CK('j'), EUI(W_, LNm('j'), 'y')))])
    bjy = D(w, Ajy, 'breqtrrd', [D(w, Ajy, 'eqbrtrd', [bj, pr12], '( abs ` ( ( %s ` j ) ` y ) ) <_ %s' % (Fm, HV('j'))), fv1(w, Ajy, 'm', 'NN', HV, 'j', jn, 'ovex')], '( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (Fm, Hm))
    hball = D(w, A, 'ralrimivva', [bjy], 'A. j e. NN A. y e. RR+ ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (Fm, Hm))
    # the termwise limits
    Aj = '( %s /\\ j e. NN )' % A
    jn1 = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    ij1 = idx(Aj, 'j', jn1, lambda st, f: ad(w, Aj, st, f))
    ck1 = D(w, Aj, 'mulcld', [ij1['cv'], D(w, Aj, 'recnd', [ij1['vpr']], '( j ^ P ) e. CC')], '%s e. CC' % CK('j'))
    LIMj = '( ( %s ^c -u %s ) x. ( _G ` %s ) )' % (LNm('j'), W_, W_)
    e2 = D(w, Aj, 'syl2anc', [ad(w, Aj, D(w, A, 'jca', [wc, w0], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), ij1['lnp'], w.inst('zl3ew2')],
           '( u e. RR+ |-> %s ) ~~>r %s' % (EUI(W_, LNm('j'), 'u'), LIMj))
    rc = D(w, Aj, 'syl2anc', [cst(w, Aj, 'rpssre', 'RR+ C_ RR'), ck1, w.inst('rlimconst')], '( u e. RR+ |-> %s ) ~~>r %s' % (CK('j'), CK('j')))
    Aju = '( %s /\\ u e. RR+ )' % Aj
    uu = w.s([], 'simpr', '( %s -> u e. RR+ )' % Aju)
    iuu = D(w, Aju, 'rpreccld', [uu], '( 1 / u ) e. RR+')
    lncu = D(w, Aju, 'rpcnd', [ad(w, Aju, ij1['lnp'], '%s e. RR+' % LNm('j'))], '%s e. CC' % LNm('j'))
    wcuu = w.s([wc], 'ad2antrr', '( %s -> %s e. CC )' % (Aju, W_))
    eucu = D(w, Aju, 'itgcl', [gibl(w, Aju, '( 1 / u )', 'u', D(w, Aju, 'rpred', [iuu], '( 1 / u ) e. RR'), D(w, Aju, 'rpred', [uu], 'u e. RR'), W_, LNm('j'), wcuu, lncu, prp=iuu),
                               fx_cl(w, Aju, '( 1 / u )', 'u', D(w, Aju, 'rpred', [iuu], '( 1 / u ) e. RR'), W_, LNm('j'), wcuu, lncu, None)], '%s e. CC' % EUI(W_, LNm('j'), 'u'))
    rm = D(w, Aj, 'rlimmul', [ad(w, Aju, ck1, '%s e. CC' % CK('j')), eucu, rc, e2], '%s ~~>r %s' % (innr('j'), DV('j')))
    fj = fv1(w, Aj, 'm', 'NN', innr, 'j', jn1, ('mptex', [rpv]), sub=sub_out('j')); dj = fv1(w, Aj, 'm', 'NN', DV, 'j', jn1, 'ovex')
    lj = D(w, Aj, 'mpbird', [rm, D(w, Aj, 'breq12d', [fj, dj], '( ( %s ` j ) ~~>r ( %s ` j ) <-> %s ~~>r %s )' % (Fm, Dm, innr('j'), DV('j')))], '( %s ` j ) ~~>r ( %s ` j )' % (Fm, Dm))
    lall = D(w, A, 'ralrimiva', [lj], 'A. j e. NN ( %s ` j ) ~~>r ( %s ` j )' % (Fm, Dm))
    UHT = ('( %s : NN --> ( CC ^m RR+ ) /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. RR+ ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) ) )' % (Fm, Hm, Hm, Fm, Hm))
    tan = D(w, A, 'syl3anc', [D(w, A, 'jca', [cst(w, A, 'rpssre', 'RR+ C_ RR'), cst(w, A, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')], '( RR+ C_ RR /\\ sup ( RR+ , RR* , < ) = +oo )'),
                              D(w, A, 'jca', [fF, D(w, A, '3jca', [hf, hs, hball], UHT[UHT.index('( %s : NN --> RR' % Hm):-2])], UHT), lall, w.inst('zl3tan')],
            '( t e. RR+ |-> sum_ k e. NN ( ( %s ` k ) ` t ) ) ~~>r sum_ k e. NN ( %s ` k )' % (Fm, Dm))
    # the function: the Mellin integral ( zl3mtw )
    At = '( %s /\\ t e. RR+ )' % A
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    Atk = '( %s /\\ k e. NN )' % At
    ktn = w.s([], 'simpr', '( %s -> k e. NN )' % Atk)
    fkt = D(w, Atk, 'eqtrd', [D(w, Atk, 'fveq1d', [fv1(w, Atk, 'm', 'NN', innr, 'k', ktn, ('mptex', [rpv]), sub=sub_out('k'))], '( ( %s ` k ) ` t ) = ( %s ` t )' % (Fm, innr('k'))),
                              fv1(w, Atk, 'u', 'RR+', lambda v: FU('k', v), 't', ad(w, Atk, trp, 't e. RR+'), 'ovex', sub=sub_in('k', 't'))], '( ( %s ` k ) ` t ) = %s' % (Fm, FU('k', 't')))
    mtw = D(w, At, 'syl3anc', [ad(w, At, ta, L.TA), ad(w, At, wc, '%s e. CC' % W_), trp, w.inst('zl3mtw')], '%s = sum_ k e. NN %s' % (L.MTI(W_, 't'), FU('k', 't')))
    et = D(w, At, 'eqtr4d', [D(w, At, 'sumeq2dv', [fkt], 'sum_ k e. NN ( ( %s ` k ) ` t ) = sum_ k e. NN %s' % (Fm, FU('k', 't'))), mtw], 'sum_ k e. NN ( ( %s ` k ) ` t ) = %s' % (Fm, L.MTI(W_, 't')))
    mfe = D(w, A, 'mpteq2dva', [et], '( t e. RR+ |-> sum_ k e. NN ( ( %s ` k ) ` t ) ) = ( t e. RR+ |-> %s )' % (Fm, L.MTI(W_, 't')))
    # the limit: GAMP x. the L-series
    GP = L.GAMP('S')
    MW = '( %s ^c %s )' % (MPI, W_); GW = '( _G ` %s )' % W_
    CS = lambda v: '( ( C ` %s ) x. ( %s ^c -u S ) )' % (v, v)
    Gm = '( m e. NN |-> %s )' % CS('m')
    gvk = fv1(w, Ak, 'm', 'NN', CS, 'k', kn, 'ovex')
    skc = D(w, Ak, 'cxpcld', [D(w, Ak, 'rpcnd', [krp], 'k e. CC'), D(w, Ak, 'negcld', [ad(w, Ak, sc, 'S e. CC')], '-u S e. CC')], '( k ^c -u S ) e. CC')
    csc = D(w, Ak, 'mulcld', [ik['cv'], skc], '%s e. CC' % CS('k'))
    aks = D(w, Ak, 'eqtrd', [D(w, Ak, 'syl2anc', [krp, D(w, Ak, 'negcld', [ad(w, Ak, sc, 'S e. CC')], '-u S e. CC'), w.inst('abscxp')], '( abs ` ( k ^c -u S ) ) = ( k ^c ( Re ` -u S ) )'),
                             D(w, Ak, 'oveq2d', [D(w, Ak, 'syl', [ad(w, Ak, sc, 'S e. CC'), w.inst('reneg')], '( Re ` -u S ) = -u %s' % RS)], '( k ^c ( Re ` -u S ) ) = ( k ^c -u %s )' % RS)],
          '( abs ` ( k ^c -u S ) ) = ( k ^c -u %s )' % RS)
    zkr = D(w, Ak, 'rpred', [zrp], '( k ^c -u %s ) e. RR' % RS)
    gle = chain(w, Ak, ['( abs ` ( %s ` k ) )' % Gm, '( abs ` %s )' % CS('k'), '( ( abs ` ( C ` k ) ) x. ( abs ` ( k ^c -u S ) ) )', '( ( abs ` ( C ` k ) ) x. ( k ^c -u %s ) )' % RS],
                [D(w, Ak, 'fveq2d', [gvk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (Gm, CS('k'))), D(w, Ak, 'absmuld', [ik['cv'], skc], '( abs ` %s ) = ( ( abs ` ( C ` k ) ) x. ( abs ` ( k ^c -u S ) ) )' % CS('k')),
                 D(w, Ak, 'oveq2d', [aks], '( ( abs ` ( C ` k ) ) x. ( abs ` ( k ^c -u S ) ) ) = ( ( abs ` ( C ` k ) ) x. ( k ^c -u %s ) )' % RS)])
    gle2 = D(w, Ak, 'breqtrd', [D(w, Ak, 'eqbrtrd', [gle, D(w, Ak, 'lemul1ad', [D(w, Ak, 'abscld', [ik['cv']], '( abs ` ( C ` k ) ) e. RR'), cst(w, Ak, '1re', '1 e. RR'), zkr, D(w, Ak, 'rpge0d', [zrp], '0 <_ ( k ^c -u %s )' % RS), ik['cb']],
                                                                  '( ( abs ` ( C ` k ) ) x. ( k ^c -u %s ) ) <_ ( 1 x. ( k ^c -u %s ) )' % (RS, RS))], '( abs ` ( %s ` k ) ) <_ ( 1 x. ( k ^c -u %s ) )' % (Gm, RS)),
                                D(w, Ak, 'oveq2d', [zv], '( 1 x. ( %s ` k ) ) = ( 1 x. ( k ^c -u %s ) )' % (Zm, RS)) and D(w, Ak, 'oveq2d', [D(w, Ak, 'eqcomd', [zv], '( k ^c -u %s ) = ( %s ` k )' % (RS, Zm))], '( 1 x. ( k ^c -u %s ) ) = ( 1 x. ( %s ` k ) )' % (RS, Zm))],
            '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (Gm, Zm))
    gcv = D(w, A, 'cvgcmpce', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1nn', '1 e. NN'), D(w, Ak, 'rpred', [D(w, Ak, 'eqeltrd', [zv, zrp], '( %s ` k ) e. RR+' % Zm)], '( %s ` k ) e. RR' % Zm),
                               D(w, Ak, 'eqeltrd', [gvk, csc], '( %s ` k ) e. CC' % Gm), zcv, cst(w, A, '1re', '1 e. RR'), liftu(gle2, '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (Gm, Zm))],
           'seq 1 ( + , %s ) e. dom ~~>' % Gm)
    mwc = D(w, A, 'cxpcld', [D(w, A, 'rpcnd', [mpp], '%s e. CC' % MPI), wc], '%s e. CC' % MW)
    gpc = D(w, A, 'mulcld', [mwc, gw], '%s e. CC' % GP)
    ism = D(w, A, 'isummulc2', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), gvk, csc, gcv, gpc], '( %s x. %s ) = sum_ k e. NN ( %s x. %s )' % (GP, L.LSC('S'), GP, CS('k')))
    lnws = D(w, Ak, 'syl3anc', [ad(w, Ak, D(w, A, 'simpld', [ta], L.MP), L.MP), kn, ad(w, Ak, sc, 'S e. CC'), w.inst('zl3lnw')], '( ( k ^ P ) x. ( %s ^c -u %s ) ) = ( %s x. ( k ^c -u S ) )' % (LNm('k'), W_, MW))
    kpc2 = D(w, Ak, 'recnd', [ik['vpr']], '( k ^ P ) e. CC')
    lwc = D(w, Ak, 'cxpcld', [D(w, Ak, 'rpcnd', [ik['lnp']], '%s e. CC' % LNm('k')), D(w, Ak, 'negcld', [ad(w, Ak, wc, '%s e. CC' % W_)], '-u %s e. CC' % W_)], '( %s ^c -u %s ) e. CC' % (LNm('k'), W_))
    LW = '( %s ^c -u %s )' % (LNm('k'), W_)
    gwk = ad(w, Ak, gw, '%s e. CC' % GW); mwk = ad(w, Ak, mwc, '%s e. CC' % MW)
    dk = chain(w, Ak, ['( %s ` k )' % Dm, DV('k'), '( ( C ` k ) x. ( ( k ^ P ) x. ( %s x. %s ) ) )' % (LW, GW), '( ( C ` k ) x. ( ( ( k ^ P ) x. %s ) x. %s ) )' % (LW, GW),
                       '( ( C ` k ) x. ( ( %s x. ( k ^c -u S ) ) x. %s ) )' % (MW, GW), '( ( C ` k ) x. ( ( %s x. %s ) x. ( k ^c -u S ) ) )' % (MW, GW), '( %s x. %s )' % (GP, CS('k'))],
               [fv1(w, Ak, 'm', 'NN', DV, 'k', kn, 'ovex'),
                D(w, Ak, 'mulassd', [ik['cv'], kpc2, D(w, Ak, 'mulcld', [lwc, gwk], '( %s x. %s ) e. CC' % (LW, GW))], '%s = ( ( C ` k ) x. ( ( k ^ P ) x. ( %s x. %s ) ) )' % (DV('k'), LW, GW)),
                D(w, Ak, 'oveq2d', [D(w, Ak, 'eqcomd', [D(w, Ak, 'mulassd', [kpc2, lwc, gwk], '( ( ( k ^ P ) x. %s ) x. %s ) = ( ( k ^ P ) x. ( %s x. %s ) )' % (LW, GW, LW, GW))],
                                    '( ( k ^ P ) x. ( %s x. %s ) ) = ( ( ( k ^ P ) x. %s ) x. %s )' % (LW, GW, LW, GW))],
                  '( ( C ` k ) x. ( ( k ^ P ) x. ( %s x. %s ) ) ) = ( ( C ` k ) x. ( ( ( k ^ P ) x. %s ) x. %s ) )' % (LW, GW, LW, GW)),
                D(w, Ak, 'oveq2d', [D(w, Ak, 'oveq1d', [lnws], '( ( ( k ^ P ) x. %s ) x. %s ) = ( ( %s x. ( k ^c -u S ) ) x. %s )' % (LW, GW, MW, GW))],
                  '( ( C ` k ) x. ( ( ( k ^ P ) x. %s ) x. %s ) ) = ( ( C ` k ) x. ( ( %s x. ( k ^c -u S ) ) x. %s ) )' % (LW, GW, MW, GW)),
                D(w, Ak, 'oveq2d', [D(w, Ak, 'mul32d', [mwk, skc, gwk], '( ( %s x. ( k ^c -u S ) ) x. %s ) = ( ( %s x. %s ) x. ( k ^c -u S ) )' % (MW, GW, MW, GW))],
                  '( ( C ` k ) x. ( ( %s x. ( k ^c -u S ) ) x. %s ) ) = ( ( C ` k ) x. ( ( %s x. %s ) x. ( k ^c -u S ) ) )' % (MW, GW, MW, GW)),
                D(w, Ak, 'mul12d', [ik['cv'], ad(w, Ak, gpc, '%s e. CC' % GP), skc], '( ( C ` k ) x. ( ( %s x. %s ) x. ( k ^c -u S ) ) ) = ( %s x. %s )' % (MW, GW, GP, CS('k')))])
    sde = D(w, A, 'eqtr4d', [D(w, A, 'sumeq2dv', [dk], 'sum_ k e. NN ( %s ` k ) = sum_ k e. NN ( %s x. %s )' % (Dm, GP, CS('k'))), ism], 'sum_ k e. NN ( %s ` k ) = ( %s x. %s )' % (Dm, GP, L.LSC('S')))
    w.qed([tan, D(w, A, 'breq12d', [mfe, sde], '( ( t e. RR+ |-> sum_ k e. NN ( ( %s ` k ) ` t ) ) ~~>r sum_ k e. NN ( %s ` k ) <-> ( t e. RR+ |-> %s ) ~~>r ( %s x. %s ) )'
                                    % (Fm, Dm, L.MTI(W_, 't'), GP, L.LSC('S')))], 'mpbi' if False else 'mpbid', S['zl3mlm'])
    go(w)


# ---------------------------------------------------------------- zl3inv
if want('zl3inv'):
    w = W('zl3inv', 'The substitution ` u = 1 / x ` on ` ( 1 / T , 1 ) ` ( ~ itgsubst with ` x ^c -u 1 ` , ~ dvcxp1 ).')
    A, Cc = ante_of('zl3inv')
    tr = D(w, A, 'simplll', [], 'T e. RR'); t1 = D(w, A, 'simpllr', [], '1 <_ T'); erp = D(w, A, 'simplrl', [], 'E e. RR+'); elt = D(w, A, 'simplrr', [], 'E < ( 1 / T )')
    fc = D(w, A, 'simpr', [], 'F e. ( ( E (,) +oo ) -cn-> CC )')
    UO = '( E (,) +oo )'
    trp = D(w, A, 'elrpd', [tr, linarith(w, A, [t1], '0 < T', leaves={'T': tr})], 'T e. RR+')
    I = '( 1 [,] T )'; X = '( 1 (,) T )'
    N1 = '-u 1'; N2 = '( -u 1 - 1 )'
    AXe = '( x ^c -u 1 )'
    AX = '( x e. %s |-> %s )' % (I, AXe)
    Bx = '( -u 1 x. ( x ^c %s ) )' % N2
    cx1 = D(w, A, 'simpld', [D(w, A, 'syl2anc', [cst(w, A, 'neg1cn', '-u 1 e. CC'), D(w, A, 'jca', [cst(w, A, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ T e. RR )'), w.inst('zl3cxc')],
                                  '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c -u 1 ) ) ) e. ( %s -cn-> CC ) )' % (AX, I, I, I))], '%s e. ( %s -cn-> CC )' % (AX, I))
    n2c = D(w, A, 'subcld', [cst(w, A, 'neg1cn', '-u 1 e. CC'), cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % N2)
    CX2 = '( x e. %s |-> ( x ^c %s ) )' % (I, N2)
    cx2 = D(w, A, 'simpld', [D(w, A, 'syl2anc', [n2c, D(w, A, 'jca', [cst(w, A, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ T e. RR )'), w.inst('zl3cxc')],
                                  '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (CX2, I, I, N2, I))], '%s e. ( %s -cn-> CC )' % (CX2, I))
    # the range of x ^c -u 1 on [ 1 , T ]
    Ai = '( %s /\\ x e. %s )' % (A, I)
    xI = w.s([], 'simpr', '( %s -> x e. %s )' % (Ai, I))
    bi = D(w, Ai, 'syl2anc', [cst(w, Ai, '1re', '1 e. RR'), ad(w, Ai, tr, 'T e. RR'), w.inst('elicc2')], '( x e. %s <-> ( x e. RR /\\ 1 <_ x /\\ x <_ T ) )' % I)
    b3 = D(w, Ai, 'mpbid', [xI, bi], '( x e. RR /\\ 1 <_ x /\\ x <_ T )')
    xr = D(w, Ai, 'simp1d', [b3], 'x e. RR'); x1 = D(w, Ai, 'simp2d', [b3], '1 <_ x'); xt = D(w, Ai, 'simp3d', [b3], 'x <_ T')
    xrp = D(w, Ai, 'elrpd', [xr, linarith(w, Ai, [x1], '0 < x', leaves={'x': xr})], 'x e. RR+')
    xc = D(w, Ai, 'rpcnd', [xrp], 'x e. CC')
    xv = D(w, Ai, 'eqtrd', [D(w, Ai, 'syl3anc', [xc, D(w, Ai, 'rpne0d', [xrp], 'x =/= 0'), cst(w, Ai, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '%s = ( 1 / ( x ^c 1 ) )' % AXe),
                            D(w, Ai, 'oveq2d', [D(w, Ai, 'syl', [xc, w.inst('cxp1')], '( x ^c 1 ) = x')], '( 1 / ( x ^c 1 ) ) = ( 1 / x )')], '%s = ( 1 / x )' % AXe)
    rle = D(w, Ai, 'mpbid', [xt, D(w, Ai, 'lerecd', [xrp, ad(w, Ai, trp, 'T e. RR+')], '( x <_ T <-> ( 1 / T ) <_ ( 1 / x ) )')], '( 1 / T ) <_ ( 1 / x )')
    ixr = D(w, Ai, 'rpred', [D(w, Ai, 'rpreccld', [xrp], '( 1 / x ) e. RR+')], '( 1 / x ) e. RR')
    elx = D(w, Ai, 'ltletrd', [D(w, Ai, 'rpred', [ad(w, Ai, erp, 'E e. RR+')], 'E e. RR'), D(w, Ai, 'rpred', [D(w, Ai, 'rpreccld', [ad(w, Ai, trp, 'T e. RR+')], '( 1 / T ) e. RR+')], '( 1 / T ) e. RR'), ixr, ad(w, Ai, elt, 'E < ( 1 / T )'), rle], 'E < ( 1 / x )')
    inO = D(w, Ai, 'mpbird', [D(w, Ai, 'jca', [D(w, Ai, 'eqeltrd', [xv, ixr], '%s e. RR' % AXe), D(w, Ai, 'breqtrrd', [elx, xv], 'E < %s' % AXe)], '( %s e. RR /\\ E < %s )' % (AXe, AXe)),
                             D(w, Ai, 'syl', [D(w, Ai, 'rexrd', [D(w, Ai, 'rpred', [ad(w, Ai, erp, 'E e. RR+')], 'E e. RR')], 'E e. RR*'), w.inst('elioopnf')], '( %s e. %s <-> ( %s e. RR /\\ E < %s ) )' % (AXe, UO, AXe, AXe))],
              '%s e. %s' % (AXe, UO))
    axf = D(w, A, 'fmptd', [inO, w.s([], 'eqid', '%s = %s' % (AX, AX))], '%s : %s --> %s' % (AX, I, UO))
    uoc = w.s([w.s([], 'ioossre', '%s C_ RR' % UO), w.s([], 'ax-resscn', 'RR C_ CC')], 'sstri', '%s C_ CC' % UO)
    ha = D(w, A, 'mpbird', [axf, D(w, A, 'syl2anc', [w.s([uoc], 'a1i', '( %s -> %s C_ CC )' % (A, UO)), cx1, w.inst('cncfcdm')], '( %s e. ( %s -cn-> %s ) <-> %s : %s --> %s )' % (AX, I, UO, AX, I, UO))],
           '%s e. ( %s -cn-> %s )' % (AX, I, UO))
    # B : continuous and integrable on ( 1 , T )
    xss = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [cst(w, A, '1re', '1 e. RR'), tr, w.inst('iccssre')], '%s C_ RR' % I), cst(w, A, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    cl = Closure(w, A, {})
    cB = cont(w, A, I, Bx, cl, xss, special={'( x ^c %s )' % N2: cx2})
    BI = '( x e. %s |-> %s )' % (I, Bx); BX = '( x e. %s |-> %s )' % (X, Bx)
    rsB = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (BI, X, BX))], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A, BI, X, BX))
    bcn = D(w, A, 'eqeltrrd', [rsB, D(w, A, 'mpd', [cB, w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (BI, I, BI, X, X))],
                                                            'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A, BI, I, BI, X, X))], '( %s |` %s ) e. ( %s -cn-> CC )' % (BI, X, X))],
              '%s e. ( %s -cn-> CC )' % (BX, X))
    bib = D(w, A, 'eqeltrrd', [rsB, D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '1re', '1 e. RR'), tr], '( 1 e. RR /\\ T e. RR )'), cB, w.inst('zl3ibl')], '( %s |` %s ) e. L^1' % (BI, X))], '%s e. L^1' % BX)
    hb = D(w, A, 'mpbir2and' if False else 'mpbird', [D(w, A, 'jca', [bcn, bib], '( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 )' % (BX, X, BX)),
                                                      cst(w, A, 'elin', '( %s e. ( ( %s -cn-> CC ) i^i L^1 ) <-> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (BX, X, BX, X, BX))], '%s e. ( ( %s -cn-> CC ) i^i L^1 )' % (BX, X))
    # F as a mapping
    ff = D(w, A, 'syl', [fc, w.inst('cncff')], 'F : %s --> CC' % UO)
    feq = D(w, A, 'feqmptd', [ff], 'F = ( u e. %s |-> ( F ` u ) )' % UO)
    hc = D(w, A, 'eqeltrrd', [feq, fc], '( u e. %s |-> ( F ` u ) ) e. ( %s -cn-> CC )' % (UO, UO))
    # the derivative
    S_ = cst(w, A, 'reelprrecn', 'RR e. { RR , CC }')
    Ap = '( %s /\\ x e. RR+ )' % A
    xpc = D(w, Ap, 'rpcnd', [w.s([], 'simpr', '( %s -> x e. RR+ )' % Ap)], 'x e. CC')
    d0 = D(w, A, 'syl', [cst(w, A, 'neg1cn', '-u 1 e. CC'), w.inst('dvcxp1')], '( RR _D ( x e. RR+ |-> %s ) ) = ( x e. RR+ |-> %s )' % (AXe, Bx))
    ss2 = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '0xr', '0 e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*')], '( 0 e. RR* /\\ +oo e. RR* )'),
                                                 D(w, A, 'jca', [cst(w, A, '0le1', '0 <_ 1'), D(w, A, 'pnfged', [D(w, A, 'rexrd', [tr], 'T e. RR*')], 'T <_ +oo')], '( 0 <_ 1 /\\ T <_ +oo )'), w.inst('ioossioo')],
                               '%s C_ ( 0 (,) +oo )' % X), w.s([w.s([w.s([], 'ioorp', '( 0 (,) +oo ) = RR+')], 'eqimssi', '( 0 (,) +oo ) C_ RR+')], 'a1i', '( %s -> ( 0 (,) +oo ) C_ RR+ )' % A)], '%s C_ RR+' % X)
    d2 = D(w, A, 'dvmptres', [S_, D(w, Ap, 'cxpcld', [xpc, cst(w, Ap, 'neg1cn', '-u 1 e. CC')], '%s e. CC' % AXe),
                              D(w, Ap, 'mulcld', [cst(w, Ap, 'neg1cn', '-u 1 e. CC'), D(w, Ap, 'cxpcld', [xpc, D(w, Ap, 'subcld', [cst(w, Ap, 'neg1cn', '-u 1 e. CC'), cst(w, Ap, 'ax-1cn', '1 e. CC')], '%s e. CC' % N2)], '( x ^c %s ) e. CC' % N2)], '%s e. CC' % Bx),
                              d0, ss2, w.s([], 'eqid', '( %s |`t RR ) = ( %s |`t RR )' % (J_, J_)), w.s([], 'eqid', '%s = %s' % (J_, J_)), open_ioo(w, A, '1', 'T')],
           '( RR _D ( x e. %s |-> %s ) ) = %s' % (X, AXe, BX))
    axc = D(w, A, 'syl', [cx1, w.inst('cncff')], '%s : %s --> CC' % (AX, I))
    dvi = D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '1re', '1 e. RR'), tr], '( 1 e. RR /\\ T e. RR )'), axc, w.inst('zl3dvi')], '( RR _D %s ) = ( RR _D ( %s |` %s ) )' % (AX, AX, X))
    rsA = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = ( x e. %s |-> %s )' % (AX, X, X, AXe))], 'a1i', '( %s -> ( %s |` %s ) = ( x e. %s |-> %s ) )' % (A, AX, X, X, AXe))
    hda = chain(w, A, ['( RR _D %s )' % AX, '( RR _D ( %s |` %s ) )' % (AX, X), '( RR _D ( x e. %s |-> %s ) )' % (X, AXe), BX],
                [dvi, D(w, A, 'oveq2d', [rsA], '( RR _D ( %s |` %s ) ) = ( RR _D ( x e. %s |-> %s ) )' % (AX, X, X, AXe)), d2])
    K_ = '( 1 ^c -u 1 )'; L_ = '( T ^c -u 1 )'
    FE = '( ( F ` %s ) x. %s )' % (AXe, Bx)
    sub = D(w, A, 'itgsubst', [cst(w, A, '1re', '1 e. RR'), tr, t1, D(w, A, 'rexrd', [D(w, A, 'rpred', [erp], 'E e. RR')], 'E e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*'), ha, hb, hc, hda,
                                w.s([], 'fveq2', '( u = %s -> ( F ` u ) = ( F ` %s ) )' % (AXe, AXe)), w.s([], 'oveq1', '( x = 1 -> %s = %s )' % (AXe, K_)), w.s([], 'oveq1', '( x = T -> %s = %s )' % (AXe, L_))],
            'S_ [ %s -> %s ] ( F ` u ) _d u = S_ [ 1 -> T ] %s _d x' % (K_, L_, FE))
    k1 = D(w, A, 'syl', [cst(w, A, 'neg1cn', '-u 1 e. CC'), w.inst('1cxp')], '%s = 1' % K_)
    tc = D(w, A, 'rpcnd', [trp], 'T e. CC')
    l1 = D(w, A, 'eqtrd', [D(w, A, 'syl3anc', [tc, D(w, A, 'rpne0d', [trp], 'T =/= 0'), cst(w, A, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '%s = ( 1 / ( T ^c 1 ) )' % L_),
                           D(w, A, 'oveq2d', [D(w, A, 'syl', [tc, w.inst('cxp1')], '( T ^c 1 ) = T')], '( 1 / ( T ^c 1 ) ) = ( 1 / T )')], '%s = ( 1 / T )' % L_)
    itr = D(w, A, 'rpred', [D(w, A, 'rpreccld', [trp], '( 1 / T ) e. RR+')], '( 1 / T ) e. RR')
    it1 = D(w, A, 'breqtrd', [D(w, A, 'mpbid', [t1, D(w, A, 'lerecd', [cst(w, A, '1rp', '1 e. RR+'), trp], '( 1 <_ T <-> ( 1 / T ) <_ ( 1 / 1 ) )')], '( 1 / T ) <_ ( 1 / 1 )'), cst(w, A, '1div1e1', '( 1 / 1 ) = 1')], '( 1 / T ) <_ 1')
    lhs = chain(w, A, ['S_ [ %s -> %s ] ( F ` u ) _d u' % (K_, L_), 'S_ [ 1 -> %s ] ( F ` u ) _d u' % L_, 'S_ [ 1 -> ( 1 / T ) ] ( F ` u ) _d u', '-u S. ( ( 1 / T ) (,) 1 ) ( F ` u ) _d u'],
                [D(w, A, 'syl', [k1, w.inst('ditgeq1')], 'S_ [ %s -> %s ] ( F ` u ) _d u = S_ [ 1 -> %s ] ( F ` u ) _d u' % (K_, L_, L_)),
                 D(w, A, 'syl', [l1, w.inst('ditgeq2')], 'S_ [ 1 -> %s ] ( F ` u ) _d u = S_ [ 1 -> ( 1 / T ) ] ( F ` u ) _d u' % L_),
                 D(w, A, 'ditgneg', [it1, itr, cst(w, A, '1re', '1 e. RR')], 'S_ [ 1 -> ( 1 / T ) ] ( F ` u ) _d u = -u S. ( ( 1 / T ) (,) 1 ) ( F ` u ) _d u')])
    rhs = D(w, A, 'ditgpos', [t1], 'S_ [ 1 -> T ] %s _d x = S. %s %s _d x' % (FE, X, FE))
    w.qed([sub, lhs, rhs], '3eqtr3d', S['zl3inv'])
    go(w)


# ---------------------------------------------------------------- zl3inw
if want('zl3inw'):
    w = W('zl3inw', 'The substitution ` u = 1 / x ` on ` ( 1 / T , 1 ) ` , ` F ` continuous on a bounded interval ( ~ itgsubst with ` x ^c -u 1 ` , ~ dvcxp1 ).')
    A, Cc = ante_of('zl3inw')
    A0_ = '( ( T e. RR /\\ 1 <_ T ) /\\ ( E e. RR+ /\\ E < ( 1 / T ) ) )'
    a0 = D(w, A, 'simpll', [], A0_)
    tr = D(w, A, 'simpll', [a0], 'T e. RR') if False else w.s([a0, w.s([], 'simpll', '( %s -> T e. RR )' % A0_)], 'syl', '( %s -> T e. RR )' % A)
    t1 = w.s([a0, w.s([], 'simplr', '( %s -> 1 <_ T )' % A0_)], 'syl', '( %s -> 1 <_ T )' % A)
    erp = w.s([a0, w.s([], 'simprl', '( %s -> E e. RR+ )' % A0_)], 'syl', '( %s -> E e. RR+ )' % A)
    elt = w.s([a0, w.s([], 'simprr', '( %s -> E < ( 1 / T ) )' % A0_)], 'syl', '( %s -> E < ( 1 / T ) )' % A)
    qr = D(w, A, 'simplrl', [], 'Q e. RR'); q1 = D(w, A, 'simplrr', [], '1 < Q')
    fc = D(w, A, 'simpr', [], 'F e. ( ( E (,) Q ) -cn-> CC )')
    UO = '( E (,) Q )'
    trp = D(w, A, 'elrpd', [tr, linarith(w, A, [t1], '0 < T', leaves={'T': tr})], 'T e. RR+')
    I = '( 1 [,] T )'; X = '( 1 (,) T )'
    N1 = '-u 1'; N2 = '( -u 1 - 1 )'
    AXe = '( x ^c -u 1 )'
    AX = '( x e. %s |-> %s )' % (I, AXe)
    Bx = '( -u 1 x. ( x ^c %s ) )' % N2
    cx1 = D(w, A, 'simpld', [D(w, A, 'syl2anc', [cst(w, A, 'neg1cn', '-u 1 e. CC'), D(w, A, 'jca', [cst(w, A, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ T e. RR )'), w.inst('zl3cxc')],
                                  '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c -u 1 ) ) ) e. ( %s -cn-> CC ) )' % (AX, I, I, I))], '%s e. ( %s -cn-> CC )' % (AX, I))
    n2c = D(w, A, 'subcld', [cst(w, A, 'neg1cn', '-u 1 e. CC'), cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % N2)
    CX2 = '( x e. %s |-> ( x ^c %s ) )' % (I, N2)
    cx2 = D(w, A, 'simpld', [D(w, A, 'syl2anc', [n2c, D(w, A, 'jca', [cst(w, A, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ T e. RR )'), w.inst('zl3cxc')],
                                  '( %s e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (CX2, I, I, N2, I))], '%s e. ( %s -cn-> CC )' % (CX2, I))
    # the range of x ^c -u 1 on [ 1 , T ]
    Ai = '( %s /\\ x e. %s )' % (A, I)
    xI = w.s([], 'simpr', '( %s -> x e. %s )' % (Ai, I))
    bi = D(w, Ai, 'syl2anc', [cst(w, Ai, '1re', '1 e. RR'), ad(w, Ai, tr, 'T e. RR'), w.inst('elicc2')], '( x e. %s <-> ( x e. RR /\\ 1 <_ x /\\ x <_ T ) )' % I)
    b3 = D(w, Ai, 'mpbid', [xI, bi], '( x e. RR /\\ 1 <_ x /\\ x <_ T )')
    xr = D(w, Ai, 'simp1d', [b3], 'x e. RR'); x1 = D(w, Ai, 'simp2d', [b3], '1 <_ x'); xt = D(w, Ai, 'simp3d', [b3], 'x <_ T')
    xrp = D(w, Ai, 'elrpd', [xr, linarith(w, Ai, [x1], '0 < x', leaves={'x': xr})], 'x e. RR+')
    xc = D(w, Ai, 'rpcnd', [xrp], 'x e. CC')
    xv = D(w, Ai, 'eqtrd', [D(w, Ai, 'syl3anc', [xc, D(w, Ai, 'rpne0d', [xrp], 'x =/= 0'), cst(w, Ai, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '%s = ( 1 / ( x ^c 1 ) )' % AXe),
                            D(w, Ai, 'oveq2d', [D(w, Ai, 'syl', [xc, w.inst('cxp1')], '( x ^c 1 ) = x')], '( 1 / ( x ^c 1 ) ) = ( 1 / x )')], '%s = ( 1 / x )' % AXe)
    rle = D(w, Ai, 'mpbid', [xt, D(w, Ai, 'lerecd', [xrp, ad(w, Ai, trp, 'T e. RR+')], '( x <_ T <-> ( 1 / T ) <_ ( 1 / x ) )')], '( 1 / T ) <_ ( 1 / x )')
    ixr = D(w, Ai, 'rpred', [D(w, Ai, 'rpreccld', [xrp], '( 1 / x ) e. RR+')], '( 1 / x ) e. RR')
    elx = D(w, Ai, 'ltletrd', [D(w, Ai, 'rpred', [ad(w, Ai, erp, 'E e. RR+')], 'E e. RR'), D(w, Ai, 'rpred', [D(w, Ai, 'rpreccld', [ad(w, Ai, trp, 'T e. RR+')], '( 1 / T ) e. RR+')], '( 1 / T ) e. RR'), ixr, ad(w, Ai, elt, 'E < ( 1 / T )'), rle], 'E < ( 1 / x )')
    ix1 = D(w, Ai, 'breqtrd', [D(w, Ai, 'mpbid', [x1, D(w, Ai, 'lerecd', [cst(w, Ai, '1rp', '1 e. RR+'), xrp], '( 1 <_ x <-> ( 1 / x ) <_ ( 1 / 1 ) )')], '( 1 / x ) <_ ( 1 / 1 )'), cst(w, Ai, '1div1e1', '( 1 / 1 ) = 1')], '( 1 / x ) <_ 1')
    ixq = D(w, Ai, 'lelttrd', [ixr, cst(w, Ai, '1re', '1 e. RR'), ad(w, Ai, qr, 'Q e. RR'), ix1, ad(w, Ai, q1, '1 < Q')], '( 1 / x ) < Q')
    inO = D(w, Ai, 'mpbird', [D(w, Ai, '3jca', [D(w, Ai, 'eqeltrd', [xv, ixr], '%s e. RR' % AXe), D(w, Ai, 'breqtrrd', [elx, xv], 'E < %s' % AXe), D(w, Ai, 'eqbrtrd', [xv, ixq], '%s < Q' % AXe)],
                                               '( %s e. RR /\\ E < %s /\\ %s < Q )' % (AXe, AXe, AXe)),
                             D(w, Ai, 'syl2anc', [D(w, Ai, 'rexrd', [D(w, Ai, 'rpred', [ad(w, Ai, erp, 'E e. RR+')], 'E e. RR')], 'E e. RR*'), D(w, Ai, 'rexrd', [ad(w, Ai, qr, 'Q e. RR')], 'Q e. RR*'), w.inst('elioo2')],
                               '( %s e. %s <-> ( %s e. RR /\\ E < %s /\\ %s < Q ) )' % (AXe, UO, AXe, AXe, AXe))],
              '%s e. %s' % (AXe, UO))
    axf = D(w, A, 'fmptd', [inO, w.s([], 'eqid', '%s = %s' % (AX, AX))], '%s : %s --> %s' % (AX, I, UO))
    uoc = w.s([w.s([], 'ioossre', '%s C_ RR' % UO), w.s([], 'ax-resscn', 'RR C_ CC')], 'sstri', '%s C_ CC' % UO)
    ha = D(w, A, 'mpbird', [axf, D(w, A, 'syl2anc', [w.s([uoc], 'a1i', '( %s -> %s C_ CC )' % (A, UO)), cx1, w.inst('cncfcdm')], '( %s e. ( %s -cn-> %s ) <-> %s : %s --> %s )' % (AX, I, UO, AX, I, UO))],
           '%s e. ( %s -cn-> %s )' % (AX, I, UO))
    # B : continuous and integrable on ( 1 , T )
    xss = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [cst(w, A, '1re', '1 e. RR'), tr, w.inst('iccssre')], '%s C_ RR' % I), cst(w, A, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    cl = Closure(w, A, {})
    cB = cont(w, A, I, Bx, cl, xss, special={'( x ^c %s )' % N2: cx2})
    BI = '( x e. %s |-> %s )' % (I, Bx); BX = '( x e. %s |-> %s )' % (X, Bx)
    rsB = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (BI, X, BX))], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A, BI, X, BX))
    bcn = D(w, A, 'eqeltrrd', [rsB, D(w, A, 'mpd', [cB, w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (BI, I, BI, X, X))],
                                                            'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A, BI, I, BI, X, X))], '( %s |` %s ) e. ( %s -cn-> CC )' % (BI, X, X))],
              '%s e. ( %s -cn-> CC )' % (BX, X))
    bib = D(w, A, 'eqeltrrd', [rsB, D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '1re', '1 e. RR'), tr], '( 1 e. RR /\\ T e. RR )'), cB, w.inst('zl3ibl')], '( %s |` %s ) e. L^1' % (BI, X))], '%s e. L^1' % BX)
    hb = D(w, A, 'mpbir2and' if False else 'mpbird', [D(w, A, 'jca', [bcn, bib], '( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 )' % (BX, X, BX)),
                                                      cst(w, A, 'elin', '( %s e. ( ( %s -cn-> CC ) i^i L^1 ) <-> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (BX, X, BX, X, BX))], '%s e. ( ( %s -cn-> CC ) i^i L^1 )' % (BX, X))
    # F as a mapping
    ff = D(w, A, 'syl', [fc, w.inst('cncff')], 'F : %s --> CC' % UO)
    feq = D(w, A, 'feqmptd', [ff], 'F = ( u e. %s |-> ( F ` u ) )' % UO)
    hc = D(w, A, 'eqeltrrd', [feq, fc], '( u e. %s |-> ( F ` u ) ) e. ( %s -cn-> CC )' % (UO, UO))
    # the derivative
    S_ = cst(w, A, 'reelprrecn', 'RR e. { RR , CC }')
    Ap = '( %s /\\ x e. RR+ )' % A
    xpc = D(w, Ap, 'rpcnd', [w.s([], 'simpr', '( %s -> x e. RR+ )' % Ap)], 'x e. CC')
    d0 = D(w, A, 'syl', [cst(w, A, 'neg1cn', '-u 1 e. CC'), w.inst('dvcxp1')], '( RR _D ( x e. RR+ |-> %s ) ) = ( x e. RR+ |-> %s )' % (AXe, Bx))
    ss2 = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '0xr', '0 e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*')], '( 0 e. RR* /\\ +oo e. RR* )'),
                                                 D(w, A, 'jca', [cst(w, A, '0le1', '0 <_ 1'), D(w, A, 'pnfged', [D(w, A, 'rexrd', [tr], 'T e. RR*')], 'T <_ +oo')], '( 0 <_ 1 /\\ T <_ +oo )'), w.inst('ioossioo')],
                               '%s C_ ( 0 (,) +oo )' % X), w.s([w.s([w.s([], 'ioorp', '( 0 (,) +oo ) = RR+')], 'eqimssi', '( 0 (,) +oo ) C_ RR+')], 'a1i', '( %s -> ( 0 (,) +oo ) C_ RR+ )' % A)], '%s C_ RR+' % X)
    d2 = D(w, A, 'dvmptres', [S_, D(w, Ap, 'cxpcld', [xpc, cst(w, Ap, 'neg1cn', '-u 1 e. CC')], '%s e. CC' % AXe),
                              D(w, Ap, 'mulcld', [cst(w, Ap, 'neg1cn', '-u 1 e. CC'), D(w, Ap, 'cxpcld', [xpc, D(w, Ap, 'subcld', [cst(w, Ap, 'neg1cn', '-u 1 e. CC'), cst(w, Ap, 'ax-1cn', '1 e. CC')], '%s e. CC' % N2)], '( x ^c %s ) e. CC' % N2)], '%s e. CC' % Bx),
                              d0, ss2, w.s([], 'eqid', '( %s |`t RR ) = ( %s |`t RR )' % (J_, J_)), w.s([], 'eqid', '%s = %s' % (J_, J_)), open_ioo(w, A, '1', 'T')],
           '( RR _D ( x e. %s |-> %s ) ) = %s' % (X, AXe, BX))
    axc = D(w, A, 'syl', [cx1, w.inst('cncff')], '%s : %s --> CC' % (AX, I))
    dvi = D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '1re', '1 e. RR'), tr], '( 1 e. RR /\\ T e. RR )'), axc, w.inst('zl3dvi')], '( RR _D %s ) = ( RR _D ( %s |` %s ) )' % (AX, AX, X))
    rsA = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = ( x e. %s |-> %s )' % (AX, X, X, AXe))], 'a1i', '( %s -> ( %s |` %s ) = ( x e. %s |-> %s ) )' % (A, AX, X, X, AXe))
    hda = chain(w, A, ['( RR _D %s )' % AX, '( RR _D ( %s |` %s ) )' % (AX, X), '( RR _D ( x e. %s |-> %s ) )' % (X, AXe), BX],
                [dvi, D(w, A, 'oveq2d', [rsA], '( RR _D ( %s |` %s ) ) = ( RR _D ( x e. %s |-> %s ) )' % (AX, X, X, AXe)), d2])
    K_ = '( 1 ^c -u 1 )'; L_ = '( T ^c -u 1 )'
    FE = '( ( F ` %s ) x. %s )' % (AXe, Bx)
    sub = D(w, A, 'itgsubst', [cst(w, A, '1re', '1 e. RR'), tr, t1, D(w, A, 'rexrd', [D(w, A, 'rpred', [erp], 'E e. RR')], 'E e. RR*'), D(w, A, 'rexrd', [qr], 'Q e. RR*'), ha, hb, hc, hda,
                                w.s([], 'fveq2', '( u = %s -> ( F ` u ) = ( F ` %s ) )' % (AXe, AXe)), w.s([], 'oveq1', '( x = 1 -> %s = %s )' % (AXe, K_)), w.s([], 'oveq1', '( x = T -> %s = %s )' % (AXe, L_))],
            'S_ [ %s -> %s ] ( F ` u ) _d u = S_ [ 1 -> T ] %s _d x' % (K_, L_, FE))
    k1 = D(w, A, 'syl', [cst(w, A, 'neg1cn', '-u 1 e. CC'), w.inst('1cxp')], '%s = 1' % K_)
    tc = D(w, A, 'rpcnd', [trp], 'T e. CC')
    l1 = D(w, A, 'eqtrd', [D(w, A, 'syl3anc', [tc, D(w, A, 'rpne0d', [trp], 'T =/= 0'), cst(w, A, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '%s = ( 1 / ( T ^c 1 ) )' % L_),
                           D(w, A, 'oveq2d', [D(w, A, 'syl', [tc, w.inst('cxp1')], '( T ^c 1 ) = T')], '( 1 / ( T ^c 1 ) ) = ( 1 / T )')], '%s = ( 1 / T )' % L_)
    itr = D(w, A, 'rpred', [D(w, A, 'rpreccld', [trp], '( 1 / T ) e. RR+')], '( 1 / T ) e. RR')
    it1 = D(w, A, 'breqtrd', [D(w, A, 'mpbid', [t1, D(w, A, 'lerecd', [cst(w, A, '1rp', '1 e. RR+'), trp], '( 1 <_ T <-> ( 1 / T ) <_ ( 1 / 1 ) )')], '( 1 / T ) <_ ( 1 / 1 )'), cst(w, A, '1div1e1', '( 1 / 1 ) = 1')], '( 1 / T ) <_ 1')
    lhs = chain(w, A, ['S_ [ %s -> %s ] ( F ` u ) _d u' % (K_, L_), 'S_ [ 1 -> %s ] ( F ` u ) _d u' % L_, 'S_ [ 1 -> ( 1 / T ) ] ( F ` u ) _d u', '-u S. ( ( 1 / T ) (,) 1 ) ( F ` u ) _d u'],
                [D(w, A, 'syl', [k1, w.inst('ditgeq1')], 'S_ [ %s -> %s ] ( F ` u ) _d u = S_ [ 1 -> %s ] ( F ` u ) _d u' % (K_, L_, L_)),
                 D(w, A, 'syl', [l1, w.inst('ditgeq2')], 'S_ [ 1 -> %s ] ( F ` u ) _d u = S_ [ 1 -> ( 1 / T ) ] ( F ` u ) _d u' % L_),
                 D(w, A, 'ditgneg', [it1, itr, cst(w, A, '1re', '1 e. RR')], 'S_ [ 1 -> ( 1 / T ) ] ( F ` u ) _d u = -u S. ( ( 1 / T ) (,) 1 ) ( F ` u ) _d u')])
    rhs = D(w, A, 'ditgpos', [t1], 'S_ [ 1 -> T ] %s _d x = S. %s %s _d x' % (FE, X, FE))
    w.qed([sub, lhs, rhs], '3eqtr3d', S['zl3inw'])
    go(w)


# ---------------------------------------------------------------- zl3pol
if want('zl3pol'):
    w = W('zl3pol', 'The pole integral: ` lim_t S. ( 1 , t ) x ^ ( -Z - 1 ) = 1 / Z ` on ` 0 < Re Z ` ( ~ ftc2 with ~ zl3dvw , ~ cxplim ).')
    A, Cc = ante_of('zl3pol')
    zc = D(w, A, 'simpl', [], 'Z e. CC'); z0 = D(w, A, 'simpr', [], '0 < ( Re ` Z )')
    RZ = '( Re ` Z )'
    rzr = D(w, A, 'recld', [zc], '%s e. RR' % RZ); rzp = D(w, A, 'elrpd', [rzr, z0], '%s e. RR+' % RZ)
    zne = D(w, A, 'mpbird', [D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), rzr, D(w, A, 'abscld', [zc], '( abs ` Z ) e. RR'), z0, D(w, A, 'releabsd', [zc], '%s <_ ( abs ` Z )' % RZ)], '0 < ( abs ` Z )'),
                             D(w, A, 'syl', [zc, w.inst('absgt0')], '( Z =/= 0 <-> 0 < ( abs ` Z ) )')], 'Z =/= 0')
    nz = '-u Z'
    nzc = D(w, A, 'negcld', [zc], '%s e. CC' % nz); nzn = D(w, A, 'negne0d', [zc, zne], '%s =/= 0' % nz)
    EX = '( -u Z - 1 )'
    exc = D(w, A, 'subcld', [nzc, cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % EX)
    Gt = lambda v: '( ( %s ^c -u Z ) / -u Z )' % v
    # t >_ 1
    Au = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % A
    trp = w.s([], 'simprl', '( %s -> t e. RR+ )' % Au); t1 = w.s([], 'simprr', '( %s -> 1 <_ t )' % Au)
    tr = D(w, Au, 'rpred', [trp], 't e. RR')
    I = '( 1 [,] t )'; X = '( 1 (,) t )'
    FZ = '( z e. %s |-> %s )' % (I, Gt('z')); FX_ = '( x e. %s |-> %s )' % (I, Gt('x'))
    cbF = w.s([vsub(w, Gt, 'x', 'z')], 'cbvmptv', '%s = %s' % (FX_, FZ))
    dvw = D(w, Au, 'syl2anc', [D(w, Au, 'jca', [ad(w, Au, nzc, '%s e. CC' % nz), ad(w, Au, nzn, '%s =/= 0' % nz)], '( %s e. CC /\\ %s =/= 0 )' % (nz, nz)),
                               D(w, Au, 'jca', [cst(w, Au, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ t e. RR )'), w.inst('zl3dvw')], '( RR _D %s ) = ( x e. %s |-> ( x ^c %s ) )' % (FX_, X, EX))
    dvz = D(w, Au, 'eqtr3d', [D(w, Au, 'oveq2d', [w.s([cbF], 'a1i', '( %s -> %s = %s )' % (Au, FX_, FZ))], '( RR _D %s ) = ( RR _D %s )' % (FX_, FZ)), dvw], '( RR _D %s ) = ( x e. %s |-> ( x ^c %s ) )' % (FZ, X, EX))
    both = D(w, Au, 'syl2anc', [ad(w, Au, exc, '%s e. CC' % EX), D(w, Au, 'jca', [cst(w, Au, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ t e. RR )'), w.inst('zl3cxc')],
             '( ( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (I, EX, I, I, EX, I))
    cI = D(w, Au, 'simpld', [both], '( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC )' % (I, EX, I))
    rsX = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) = ( x e. %s |-> ( x ^c %s ) )' % (I, EX, X, X, EX))], 'a1i',
              '( %s -> ( ( x e. %s |-> ( x ^c %s ) ) |` %s ) = ( x e. %s |-> ( x ^c %s ) ) )' % (Au, I, EX, X, X, EX))
    cX = D(w, Au, 'eqeltrrd', [rsX, D(w, Au, 'mpd', [cI, w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('rescncf')], 'ax-mp',
                                                                   '( ( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC ) -> ( ( x e. %s |-> ( x ^c %s ) ) |` %s ) e. ( %s -cn-> CC ) )' % (I, EX, I, I, EX, X, X))], 'a1i',
                                                             '( %s -> ( ( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC ) -> ( ( x e. %s |-> ( x ^c %s ) ) |` %s ) e. ( %s -cn-> CC ) ) )' % (Au, I, EX, I, I, EX, X, X))],
                                      '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) e. ( %s -cn-> CC )' % (I, EX, X, X))], '( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC )' % (X, EX, X))
    iX = D(w, Au, 'eqeltrrd', [rsX, D(w, Au, 'syl2anc', [D(w, Au, 'jca', [cst(w, Au, '1re', '1 e. RR'), tr], '( 1 e. RR /\\ t e. RR )'), cI, w.inst('zl3ibl')], '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) e. L^1' % (I, EX, X))],
             '( x e. %s |-> ( x ^c %s ) ) e. L^1' % (X, EX))
    xssI = D(w, Au, 'sstrd', [D(w, Au, 'syl2anc', [cst(w, Au, '1re', '1 e. RR'), tr, w.inst('iccssre')], '%s C_ RR' % I), cst(w, Au, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    bothz = D(w, Au, 'syl2anc', [ad(w, Au, nzc, '%s e. CC' % nz), D(w, Au, 'jca', [cst(w, Au, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ t e. RR )'), w.inst('zl3cxc')],
              '( ( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (I, nz, I, I, nz, I))
    cz_ = D(w, Au, 'simpld', [bothz], '( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC )' % (I, nz, I))
    clF = Closure(w, Au, {nz: ad(w, Au, nzc, '%s e. CC' % nz)}); clF.have(nz, 'ne0', ad(w, Au, nzn, '%s =/= 0' % nz))
    cF = cont(w, Au, I, Gt('x'), clF, xssI, special={'( x ^c %s )' % nz: cz_})
    cFz = D(w, Au, 'eleqtrd' if False else 'eqeltrrd', [w.s([cbF], 'a1i', '( %s -> %s = %s )' % (Au, FX_, FZ)), cF], '%s e. ( %s -cn-> CC )' % (FZ, I))
    ft = D(w, Au, 'ftc2', [cst(w, Au, '1re', '1 e. RR'), tr, t1, D(w, Au, 'eqeltrd', [dvz, cX], '( RR _D %s ) e. ( %s -cn-> CC )' % (FZ, X)), D(w, Au, 'eqeltrd', [dvz, iX], '( RR _D %s ) e. L^1' % FZ), cFz],
           'S. %s ( ( RR _D %s ) ` x ) _d x = ( ( %s ` t ) - ( %s ` 1 ) )' % (X, FZ, FZ, FZ))
    Aux = '( %s /\\ x e. %s )' % (Au, X)
    xX = w.s([], 'simpr', '( %s -> x e. %s )' % (Aux, X))
    xrp = ioo_pos(w, Aux, '1', 't', cst(w, Aux, '1re', '1 e. RR'), ad(w, Aux, tr, 't e. RR'), cst(w, Aux, '0lt1', '0 < 1'))[1]
    dvx = D(w, Aux, 'eqtrd', [D(w, Aux, 'fveq1d', [ad(w, Aux, dvz, '( RR _D %s ) = ( x e. %s |-> ( x ^c %s ) )' % (FZ, X, EX))], '( ( RR _D %s ) ` x ) = ( ( x e. %s |-> ( x ^c %s ) ) ` x )' % (FZ, X, EX)),
                              D(w, Aux, 'syl2anc', [xX, D(w, Aux, 'cxpcld', [D(w, Aux, 'rpcnd', [xrp], 'x e. CC'), ad(w, Aux, ad(w, Au, exc, '%s e. CC' % EX), '%s e. CC' % EX)], '( x ^c %s ) e. CC' % EX),
                                                    w.s([w.s([], 'eqid', '( x e. %s |-> ( x ^c %s ) ) = ( x e. %s |-> ( x ^c %s ) )' % (X, EX, X, EX))], 'fvmpt2', '( ( x e. %s /\\ ( x ^c %s ) e. CC ) -> ( ( x e. %s |-> ( x ^c %s ) ) ` x ) = ( x ^c %s ) )' % (X, EX, X, EX, EX))],
                                '( ( x e. %s |-> ( x ^c %s ) ) ` x ) = ( x ^c %s )' % (X, EX, EX))], '( ( RR _D %s ) ` x ) = ( x ^c %s )' % (FZ, EX))
    ie = D(w, Au, 'itgeq2dv', [dvx], 'S. %s ( ( RR _D %s ) ` x ) _d x = S. %s ( x ^c %s ) _d x' % (X, FZ, X, EX))
    t1x = D(w, Au, 'rexrd', [tr], 't e. RR*')
    tI = D(w, Au, 'syl3anc', [cst(w, Au, '1xr', '1 e. RR*'), t1x, t1, w.inst('ubicc2')], 't e. %s' % I)
    oI = D(w, Au, 'syl3anc', [cst(w, Au, '1xr', '1 e. RR*'), t1x, t1, w.inst('lbicc2')], '1 e. %s' % I)
    ft_ = fv1(w, Au, 'z', I, Gt, 't', tI, 'ovex'); f1_ = fv1(w, Au, 'z', I, Gt, '1', oI, 'ovex')
    val = D(w, Au, 'eqtr3d', [ie, D(w, Au, 'eqtrd', [ft, D(w, Au, 'oveq12d', [ft_, f1_], '( ( %s ` t ) - ( %s ` 1 ) ) = ( %s - %s )' % (FZ, FZ, Gt('t'), Gt('1')))],
                                  'S. %s ( ( RR _D %s ) ` x ) _d x = ( %s - %s )' % (X, FZ, Gt('t'), Gt('1')))], 'S. %s ( x ^c %s ) _d x = ( %s - %s )' % (X, EX, Gt('t'), Gt('1')))
    # the limit of the closed form
    At = '( %s /\\ t e. RR+ )' % A
    trpt = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    tct = D(w, At, 'rpcnd', [trpt], 't e. CC')
    TZ = '( t ^c -u Z )'
    tzc = D(w, At, 'cxpcld', [tct, ad(w, At, nzc, '%s e. CC' % nz)], '%s e. CC' % TZ)
    TR = '( 1 / ( t ^c %s ) )' % RZ
    trz = D(w, At, 'rpcxpcld', [trpt, ad(w, At, rzr, '%s e. RR' % RZ)], '( t ^c %s ) e. RR+' % RZ)
    trr = D(w, At, 'rpreccld', [trz], '%s e. RR+' % TR)
    cl0 = D(w, A, 'syl', [rzp, w.inst('cxplim')], '( t e. RR+ |-> %s ) ~~>r 0' % TR)
    atz = chain(w, At, ['( abs ` ( %s - 0 ) )' % TZ, '( abs ` %s )' % TZ, '( t ^c ( Re ` -u Z ) )', '( t ^c -u %s )' % RZ, TR],
                [D(w, At, 'fveq2d', [D(w, At, 'subid1d', [tzc], '( %s - 0 ) = %s' % (TZ, TZ))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (TZ, TZ)),
                 D(w, At, 'syl2anc', [trpt, ad(w, At, nzc, '%s e. CC' % nz), w.inst('abscxp')], '( abs ` %s ) = ( t ^c ( Re ` -u Z ) )' % TZ),
                 D(w, At, 'oveq2d', [D(w, At, 'syl', [ad(w, At, zc, 'Z e. CC'), w.inst('reneg')], '( Re ` -u Z ) = -u %s' % RZ)], '( t ^c ( Re ` -u Z ) ) = ( t ^c -u %s )' % RZ),
                 D(w, At, 'syl3anc', [tct, D(w, At, 'rpne0d', [trpt], 't =/= 0'), D(w, At, 'recnd', [ad(w, At, rzr, '%s e. RR' % RZ)], '%s e. CC' % RZ), w.inst('cxpneg')], '( t ^c -u %s ) = %s' % (RZ, TR))])
    atr = D(w, At, 'eqtrd', [D(w, At, 'fveq2d', [D(w, At, 'subid1d', [D(w, At, 'rpcnd', [trr], '%s e. CC' % TR)], '( %s - 0 ) = %s' % (TR, TR))], '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (TR, TR)),
                             D(w, At, 'absidd', [D(w, At, 'rpred', [trr], '%s e. RR' % TR), D(w, At, 'rpge0d', [trr], '0 <_ %s' % TR)], '( abs ` %s ) = %s' % (TR, TR))], '( abs ` ( %s - 0 ) ) = %s' % (TR, TR))
    sqb = D(w, At, 'eqbrtrd', [atz, D(w, At, 'eqbrtrrd' if False else 'breqtrrd', [D(w, At, 'leidd', [D(w, At, 'rpred', [trr], '%s e. RR' % TR)], '%s <_ %s' % (TR, TR)), atr], '%s <_ ( abs ` ( %s - 0 ) )' % (TR, TR))],
            '( abs ` ( %s - 0 ) ) <_ ( abs ` ( %s - 0 ) )' % (TZ, TR))
    Atm = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % A
    sq = D(w, A, 'rlimsqzlem', [cst(w, A, '1re', '1 e. RR'), D(w, A, '0cnd', [], '0 e. CC'), cl0, D(w, At, 'rpcnd', [trr], '%s e. CC' % TR), tzc, w.s([sqb], 'adantrr', '( %s -> ( abs ` ( %s - 0 ) ) <_ ( abs ` ( %s - 0 ) ) )' % (Atm, TZ, TR))],
           '( t e. RR+ |-> %s ) ~~>r 0' % TZ)
    rc = D(w, A, 'syl2anc', [cst(w, A, 'rpssre', 'RR+ C_ RR'), nzc, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (nz, nz))
    rd = D(w, A, 'rlimdiv', [tzc, ad(w, At, nzc, '%s e. CC' % nz), sq, rc, nzn, ad(w, At, nzn, '%s =/= 0' % nz)], '( t e. RR+ |-> %s ) ~~>r ( 0 / %s )' % (Gt('t'), nz))
    g1 = Gt('1')
    g1c = D(w, A, 'divcld', [D(w, A, 'cxpcld', [cst(w, A, 'ax-1cn', '1 e. CC'), nzc], '( 1 ^c -u Z ) e. CC'), nzc, nzn], '%s e. CC' % g1)
    rc1 = D(w, A, 'syl2anc', [cst(w, A, 'rpssre', 'RR+ C_ RR'), g1c, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (g1, g1))
    gtc = D(w, At, 'divcld', [tzc, ad(w, At, nzc, '%s e. CC' % nz), ad(w, At, nzn, '%s =/= 0' % nz)], '%s e. CC' % Gt('t'))
    rs_ = D(w, A, 'rlimsub', [gtc, ad(w, At, g1c, '%s e. CC' % g1), rd, rc1], '( t e. RR+ |-> ( %s - %s ) ) ~~>r ( ( 0 / %s ) - %s )' % (Gt('t'), g1, nz, g1))
    izc = D(w, A, 'reccld', [zc, zne], '( 1 / Z ) e. CC')
    lv = chain(w, A, ['( ( 0 / %s ) - %s )' % (nz, g1), '( 0 - %s )' % g1, '( 0 - ( 1 / %s ) )' % nz, '( 0 - -u ( 1 / Z ) )', '-u -u ( 1 / Z )', '( 1 / Z )'],
               [D(w, A, 'oveq1d', [D(w, A, 'div0d', [nzc, nzn], '( 0 / %s ) = 0' % nz)], '( ( 0 / %s ) - %s ) = ( 0 - %s )' % (nz, g1, g1)),
                D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [D(w, A, 'syl', [nzc, w.inst('1cxp')], '( 1 ^c -u Z ) = 1')], '%s = ( 1 / %s )' % (g1, nz))], '( 0 - %s ) = ( 0 - ( 1 / %s ) )' % (g1, nz)),
                D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, 'divneg2d', [cst(w, A, 'ax-1cn', '1 e. CC'), zc, zne], '-u ( 1 / Z ) = ( 1 / %s )' % nz)], '( 1 / %s ) = -u ( 1 / Z )' % nz)],
                  '( 0 - ( 1 / %s ) ) = ( 0 - -u ( 1 / Z ) )' % nz),
                cst(w, A, 'eqcomi', '') if False else w.s([w.s([w.s([], 'df-neg', '-u -u ( 1 / Z ) = ( 0 - -u ( 1 / Z ) )')], 'eqcomi', '( 0 - -u ( 1 / Z ) ) = -u -u ( 1 / Z )')], 'a1i', '( %s -> ( 0 - -u ( 1 / Z ) ) = -u -u ( 1 / Z ) )' % A),
                D(w, A, 'negnegd', [izc], '-u -u ( 1 / Z ) = ( 1 / Z )')])
    lim = D(w, A, 'breqtrd', [rs_, lv], '( t e. RR+ |-> ( %s - %s ) ) ~~>r ( 1 / Z )' % (Gt('t'), g1))
    # integrals exist for every t, and agree with the closed form for t >_ 1
    trt = D(w, At, 'rpred', [trpt], 't e. RR')
    botht = D(w, At, 'syl2anc', [ad(w, At, exc, '%s e. CC' % EX), D(w, At, 'jca', [cst(w, At, '1rp', '1 e. RR+'), trt], '( 1 e. RR+ /\\ t e. RR )'), w.inst('zl3cxc')],
              '( ( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (I, EX, I, I, EX, I))
    rsXt = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) = ( x e. %s |-> ( x ^c %s ) )' % (I, EX, X, X, EX))], 'a1i',
               '( %s -> ( ( x e. %s |-> ( x ^c %s ) ) |` %s ) = ( x e. %s |-> ( x ^c %s ) ) )' % (At, I, EX, X, X, EX))
    iXt = D(w, At, 'eqeltrrd', [rsXt, D(w, At, 'syl2anc', [D(w, At, 'jca', [cst(w, At, '1re', '1 e. RR'), trt], '( 1 e. RR /\\ t e. RR )'), D(w, At, 'simpld', [botht], '( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC )' % (I, EX, I)), w.inst('zl3ibl')],
                                                  '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) e. L^1' % (I, EX, X))], '( x e. %s |-> ( x ^c %s ) ) e. L^1' % (X, EX))
    Atx = '( %s /\\ x e. %s )' % (At, X)
    xrpt = ioo_pos(w, Atx, '1', 't', cst(w, Atx, '1re', '1 e. RR'), ad(w, Atx, trt, 't e. RR'), cst(w, Atx, '0lt1', '0 < 1'))[1]
    itc = D(w, At, 'itgcl', [iXt, D(w, Atx, 'cxpcld', [D(w, Atx, 'rpcnd', [xrpt], 'x e. CC'), ad(w, Atx, ad(w, At, exc, '%s e. CC' % EX), '%s e. CC' % EX)], '( x ^c %s ) e. CC' % EX)], 'S. %s ( x ^c %s ) _d x e. CC' % (X, EX))
    req = D(w, A, 'rlimeq', [itc, D(w, At, 'subcld', [gtc, ad(w, At, g1c, '%s e. CC' % g1)], '( %s - %s ) e. CC' % (Gt('t'), g1)), cst(w, A, '1re', '1 e. RR'), val],
            '( ( t e. RR+ |-> S. %s ( x ^c %s ) _d x ) ~~>r ( 1 / Z ) <-> ( t e. RR+ |-> ( %s - %s ) ) ~~>r ( 1 / Z ) )' % (X, EX, Gt('t'), g1))
    w.qed([lim, req], 'mpbird', S['zl3pol'])
    go(w)


# ---------------------------------------------------------------- zl3m1
if want('zl3m1'):
    w = W('zl3m1', 'For ` M = 1 ` the character is trivial: parity ` 0 ` and root number ` 1 ` ( ~ dchr1lev , ~ dchrgs1sqflem1 ).')
    A, Cc = ante_of('zl3m1')
    PAR = L.ZL3.PAR; EPS = L.ZL3.EPS; LMr = L.LM
    m1 = D(w, A, 'simpr', [], 'M = 1')
    yb = D(w, A, 'simpllr' if False else 'simplr' if False else 'idi', [], '') if False else w.s([w.s([], 'simpl', '( %s -> %s )' % (A, L.ZL3.PR)), w.s([], 'simplr', '( %s -> Y e. ( Base ` ( DChr ` M ) ) )' % L.ZL3.PR)], 'syl', '( %s -> Y e. ( Base ` ( DChr ` M ) ) )' % A)
    mn = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, L.ZL3.PR)), w.s([], 'simpll', '( %s -> M e. NN )' % L.ZL3.PR)], 'syl', '( %s -> M e. NN )' % A)
    d1 = D(w, A, 'fveq2d', [m1], '( DChr ` M ) = ( DChr ` 1 )')
    yb1 = D(w, A, 'eleqtrd', [yb, D(w, A, 'fveq2d', [d1], '( Base ` ( DChr ` M ) ) = ( Base ` ( DChr ` 1 ) )')], 'Y e. ( Base ` ( DChr ` 1 ) )')
    y0 = D(w, A, 'syl', [yb1, w.inst('dchr1lev')], 'Y = ( 0g ` ( DChr ` 1 ) )')
    y0m = D(w, A, 'eqtr4d', [y0, D(w, A, 'fveq2d', [d1], '( 0g ` ( DChr ` M ) ) = ( 0g ` ( DChr ` 1 ) )')], 'Y = ( 0g ` ( DChr ` M ) )')
    ZM = '( Z/nZ ` M )'
    lu = D(w, A, 'mpbird', [D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [m1], '( -u 1 gcd M ) = ( -u 1 gcd 1 )'), cst(w, A, 'gcd1', '( -u 1 gcd 1 ) = 1') if False else
                                             w.s([w.s([w.s([], 'neg1z', '-u 1 e. ZZ'), w.inst('gcd1')], 'ax-mp', '( -u 1 gcd 1 ) = 1')], 'a1i', '( %s -> ( -u 1 gcd 1 ) = 1 )' % A)], '( -u 1 gcd M ) = 1'),
                            D(w, A, 'syl2anc', [D(w, A, 'nnnn0d', [mn], 'M e. NN0'), cst(w, A, 'neg1z', '-u 1 e. ZZ'),
                                                w.s([w.s([], 'eqid', '%s = %s' % (ZM, ZM)), w.s([], 'eqid', '( Unit ` %s ) = ( Unit ` %s )' % (ZM, ZM)), w.s([], 'eqid', '%s = %s' % (LMr, LMr))], 'znunit',
                                                    '( ( M e. NN0 /\\ -u 1 e. ZZ ) -> ( ( %s ` -u 1 ) e. ( Unit ` %s ) <-> ( -u 1 gcd M ) = 1 ) )' % (LMr, ZM))],
                              '( ( %s ` -u 1 ) e. ( Unit ` %s ) <-> ( -u 1 gcd M ) = 1 )' % (LMr, ZM))], '( %s ` -u 1 ) e. ( Unit ` %s )' % (LMr, ZM))
    G0 = '( 0g ` ( DChr ` M ) )'
    g1 = D(w, A, 'dchr1', [w.s([], 'eqid', '( DChr ` M ) = ( DChr ` M )'), w.s([], 'eqid', '%s = %s' % (ZM, ZM)), w.s([], 'eqid', '%s = %s' % (G0, G0)), w.s([], 'eqid', '( Unit ` %s ) = ( Unit ` %s )' % (ZM, ZM)), mn, lu],
           '( %s ` ( %s ` -u 1 ) ) = 1' % (G0, LMr))
    yv = D(w, A, 'eqtrd', [D(w, A, 'fveq1d', [y0m], '( Y ` ( %s ` -u 1 ) ) = ( %s ` ( %s ` -u 1 ) )' % (LMr, G0, LMr)), g1], '( Y ` ( %s ` -u 1 ) ) = 1' % LMr)
    cond = '( Y ` ( %s ` -u 1 ) ) = 1' % LMr
    p0 = D(w, A, 'syl', [yv, w.s([], 'iftrue', '( %s -> if ( %s , 0 , 1 ) = 0 )' % (cond, cond))], '%s = 0' % PAR)
    gs = D(w, A, 'eqtrd', [D(w, A, 'oveq12d', [m1, y0], '( M DChrGS Y ) = ( 1 DChrGS ( 0g ` ( DChr ` 1 ) ) )'), cst(w, A, 'dchrgs1sqflem1', '( 1 DChrGS ( 0g ` ( DChr ` 1 ) ) ) = 1')], '( M DChrGS Y ) = 1')
    ip = D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [p0], '( _i ^ %s ) = ( _i ^ 0 )' % PAR), w.s([w.s([w.s([], 'ax-icn', '_i e. CC'), w.inst('exp0')], 'ax-mp', '( _i ^ 0 ) = 1')], 'a1i', '( %s -> ( _i ^ 0 ) = 1 )' % A)], '( _i ^ %s ) = 1' % PAR)
    mh = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [m1], '( M ^c ( 1 / 2 ) ) = ( 1 ^c ( 1 / 2 ) )'), w.s([w.s([w.s([], 'halfcn', '( 1 / 2 ) e. CC'), w.inst('1cxp')], 'ax-mp', '( 1 ^c ( 1 / 2 ) ) = 1')], 'a1i', '( %s -> ( 1 ^c ( 1 / 2 ) ) = 1 )' % A)],
           '( M ^c ( 1 / 2 ) ) = 1')
    den = D(w, A, 'eqtrd', [D(w, A, 'oveq12d', [ip, mh], '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) ) = ( 1 x. 1 )' % PAR), cst(w, A, '1t1e1', '( 1 x. 1 ) = 1')], '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) ) = 1' % PAR)
    ep = D(w, A, 'eqtrd', [D(w, A, 'oveq12d', [gs, den], '%s = ( 1 / 1 )' % EPS), cst(w, A, '1div1e1', '( 1 / 1 ) = 1')], '%s = 1' % EPS)
    w.qed([p0, ep], 'jca', S['zl3m1'])
    go(w)


# ---------------------------------------------------------------- zl3gcz
if want('zl3gcz'):
    w = W('zl3gcz', 'The theta Mellin integrand ` TH ( z ) z ^ ( W - 1 ) ` is continuous and integrable on ` ( E , Q ) ` , ` 0 < E ` ( ~ zl3thu , ~ zl3cxc , ~ zl3ibl ).')
    A, Cc = ante_of('zl3gcz')
    ta = D(w, A, 'simpll', [], L.TA); wc = D(w, A, 'simplr', [], 'W e. CC'); erp = D(w, A, 'simprl', [], 'E e. RR+'); qr = D(w, A, 'simprr', [], 'Q e. RR')
    er = D(w, A, 'rpred', [erp], 'E e. RR')
    I = '( E [,] Q )'; X = '( E (,) Q )'; UI = '( E [,) +oo )'
    TX = THP('C', 'x', 'P'); XW = '( x ^c ( W - 1 ) )'
    thu = D(w, A, 'syl2anc', [ta, erp, w.inst('zl3thu')], '( x e. %s |-> %s ) e. ( %s -cn-> CC )' % (UI, TX, UI))
    Ax = '( %s /\\ x e. %s )' % (A, I)
    b3 = D(w, Ax, 'mpbid', [w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, I)), D(w, Ax, 'syl2anc', [ad(w, Ax, er, 'E e. RR'), ad(w, Ax, qr, 'Q e. RR'), w.inst('elicc2')], '( x e. %s <-> ( x e. RR /\\ E <_ x /\\ x <_ Q ) )' % I)],
           '( x e. RR /\\ E <_ x /\\ x <_ Q )')
    inU = D(w, Ax, 'mpbird', [D(w, Ax, 'jca', [D(w, Ax, 'simp1d', [b3], 'x e. RR'), D(w, Ax, 'simp2d', [b3], 'E <_ x')], '( x e. RR /\\ E <_ x )'),
                              D(w, Ax, 'syl', [ad(w, Ax, er, 'E e. RR'), w.inst('elicopnf')], '( x e. %s <-> ( x e. RR /\\ E <_ x ) )' % UI)], 'x e. %s' % UI)
    ss = D(w, A, 'ssrdv', [w.s([inU], 'ex', '( %s -> ( x e. %s -> x e. %s ) )' % (A, I, UI))], '%s C_ %s' % (I, UI))
    thI = D(w, A, 'eqeltrrd', [D(w, A, 'syl', [ss, w.inst('resmpt')], '( ( x e. %s |-> %s ) |` %s ) = ( x e. %s |-> %s )' % (UI, TX, I, I, TX)),
                               D(w, A, 'mpd', [thu, D(w, A, 'syl', [ss, w.inst('rescncf')], '( ( x e. %s |-> %s ) e. ( %s -cn-> CC ) -> ( ( x e. %s |-> %s ) |` %s ) e. ( %s -cn-> CC ) )' % (UI, TX, UI, UI, TX, I, I))],
                                 '( ( x e. %s |-> %s ) |` %s ) e. ( %s -cn-> CC )' % (UI, TX, I, I))], '( x e. %s |-> %s ) e. ( %s -cn-> CC )' % (I, TX, I))
    wm1 = D(w, A, 'subcld', [wc, cst(w, A, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    cx = D(w, A, 'simpld', [D(w, A, 'syl2anc', [wm1, D(w, A, 'jca', [erp, qr], '( E e. RR+ /\\ Q e. RR )'), w.inst('zl3cxc')],
                                 '( ( x e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. %s ) ) e. ( %s -cn-> CC ) )' % (I, XW, I, I, XW, I))], '( x e. %s |-> %s ) e. ( %s -cn-> CC )' % (I, XW, I))
    xss = D(w, A, 'sstrd', [D(w, A, 'syl2anc', [er, qr, w.inst('iccssre')], '%s C_ RR' % I), cst(w, A, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    e = '( %s x. %s )' % (TX, XW)
    cI = cont(w, A, I, e, Closure(w, A, {}), xss, special={TX: thI, XW: cx})
    EI = '( x e. %s |-> %s )' % (I, e); EX_ = '( x e. %s |-> %s )' % (X, e)
    rs = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (EI, X, EX_))], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A, EI, X, EX_))
    cX = D(w, A, 'eqeltrrd', [rs, D(w, A, 'mpd', [cI, w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (EI, I, EI, X, X))],
                                                               'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A, EI, I, EI, X, X))], '( %s |` %s ) e. ( %s -cn-> CC )' % (EI, X, X))],
             '%s e. ( %s -cn-> CC )' % (EX_, X))
    iX = D(w, A, 'eqeltrrd', [rs, D(w, A, 'syl2anc', [D(w, A, 'jca', [er, qr], '( E e. RR /\\ Q e. RR )'), cI, w.inst('zl3ibl')], '( %s |` %s ) e. L^1' % (EI, X))], '%s e. L^1' % EX_)
    cb = w.s([vsub(w, lambda v: '( %s x. ( %s ^c ( W - 1 ) ) )' % (THP('C', v, 'P'), v), 'x', 'z')], 'cbvmptv', '%s = %s' % (EX_, L.GZ('W')))
    cbA = w.s([cb], 'a1i', '( %s -> %s = %s )' % (A, EX_, L.GZ('W')))
    w.qed([D(w, A, 'eqeltrrd', [cbA, cX], '%s e. ( %s -cn-> CC )' % (L.GZ('W'), X)), D(w, A, 'eqeltrrd', [cbA, iX], '%s e. L^1' % L.GZ('W'))], 'jca', S['zl3gcz'])
    go(w)


# ---------------------------------------------------------------- zl3alt
if want('zl3alt'):
    w = W('zl3alt', 'Solving the theta functional equation for ` T ` ( field algebra ).')
    A, Cc = ante_of('zl3alt')
    rc = D(w, A, 'simp11', [], 'R e. CC'); ec = D(w, A, 'simp12', [], 'E e. CC'); uc = D(w, A, 'simp13', [], 'U e. CC')
    bc = D(w, A, 'simp21', [], 'B e. CC'); hc = D(w, A, 'simp22', [], 'H e. CC'); tc = D(w, A, 'simp23', [], 'T e. CC')
    h1 = D(w, A, 'simp3l', [], '( ( R / 2 ) + T ) = ( E x. ( U x. ( ( R / 2 ) + B ) ) )'); h2 = D(w, A, 'simp3r', [], '( R x. ( E x. U ) ) = ( R x. H )')
    two = cst(w, A, '2cn', '2 e. CC'); t0 = cst(w, A, '2ne0', '2 =/= 0')
    R2 = '( R / 2 )'
    r2c = D(w, A, 'divcld', [rc, two, t0], '%s e. CC' % R2)
    UB = '( U x. B )'; UR = '( U x. %s )' % R2
    ubc = D(w, A, 'mulcld', [uc, bc], '%s e. CC' % UB); urc = D(w, A, 'mulcld', [uc, r2c], '%s e. CC' % UR)
    EUB = '( E x. %s )' % UB; EUR = '( E x. %s )' % UR
    eubc = D(w, A, 'mulcld', [ec, ubc], '%s e. CC' % EUB); eurc = D(w, A, 'mulcld', [ec, urc], '%s e. CC' % EUR)
    main = chain(w, A, ['T', '( ( %s + T ) - %s )' % (R2, R2), '( ( E x. ( U x. ( %s + B ) ) ) - %s )' % (R2, R2), '( ( E x. ( %s + %s ) ) - %s )' % (UR, UB, R2),
                        '( ( %s + %s ) - %s )' % (EUR, EUB, R2), '( ( %s + %s ) - %s )' % (EUB, EUR, R2), '( %s + ( %s - %s ) )' % (EUB, EUR, R2)],
                 [('r', D(w, A, 'pncan2d', [r2c, tc], '( ( %s + T ) - %s ) = T' % (R2, R2))),
                  D(w, A, 'oveq1d', [h1], '( ( %s + T ) - %s ) = ( ( E x. ( U x. ( %s + B ) ) ) - %s )' % (R2, R2, R2, R2)),
                  D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'adddid', [uc, r2c, bc], '( U x. ( %s + B ) ) = ( %s + %s )' % (R2, UR, UB))], '( E x. ( U x. ( %s + B ) ) ) = ( E x. ( %s + %s ) )' % (R2, UR, UB))],
                    '( ( E x. ( U x. ( %s + B ) ) ) - %s ) = ( ( E x. ( %s + %s ) ) - %s )' % (R2, R2, UR, UB, R2)),
                  D(w, A, 'oveq1d', [D(w, A, 'adddid', [ec, urc, ubc], '( E x. ( %s + %s ) ) = ( %s + %s )' % (UR, UB, EUR, EUB))], '( ( E x. ( %s + %s ) ) - %s ) = ( ( %s + %s ) - %s )' % (UR, UB, R2, EUR, EUB, R2)),
                  D(w, A, 'oveq1d', [D(w, A, 'addcomd', [eurc, eubc], '( %s + %s ) = ( %s + %s )' % (EUR, EUB, EUB, EUR))], '( ( %s + %s ) - %s ) = ( ( %s + %s ) - %s )' % (EUR, EUB, R2, EUB, EUR, R2)),
                  D(w, A, 'addsubassd', [eubc, eurc, r2c], '( ( %s + %s ) - %s ) = ( %s + ( %s - %s ) )' % (EUB, EUR, R2, EUB, EUR, R2))])
    eu = D(w, A, 'mulcld', [ec, uc], '( E x. U ) e. CC')
    er_ = chain(w, A, [EUR, '( E x. ( ( U x. R ) / 2 ) )', '( ( E x. ( U x. R ) ) / 2 )', '( ( ( E x. U ) x. R ) / 2 )', '( ( R x. ( E x. U ) ) / 2 )', '( ( R x. H ) / 2 )'],
                [D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, 'divassd', [uc, rc, two, t0], '( ( U x. R ) / 2 ) = %s' % UR)], '%s = ( ( U x. R ) / 2 )' % UR)], '%s = ( E x. ( ( U x. R ) / 2 ) )' % EUR),
                 ('r', D(w, A, 'divassd', [ec, D(w, A, 'mulcld', [uc, rc], '( U x. R ) e. CC'), two, t0], '( ( E x. ( U x. R ) ) / 2 ) = ( E x. ( ( U x. R ) / 2 ) )')),
                 D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'mulassd', [ec, uc, rc], '( ( E x. U ) x. R ) = ( E x. ( U x. R ) )')], '( E x. ( U x. R ) ) = ( ( E x. U ) x. R )')],
                   '( ( E x. ( U x. R ) ) / 2 ) = ( ( ( E x. U ) x. R ) / 2 )'),
                 D(w, A, 'oveq1d', [D(w, A, 'mulcomd', [eu, rc], '( ( E x. U ) x. R ) = ( R x. ( E x. U ) )')], '( ( ( E x. U ) x. R ) / 2 ) = ( ( R x. ( E x. U ) ) / 2 )'),
                 D(w, A, 'oveq1d', [h2], '( ( R x. ( E x. U ) ) / 2 ) = ( ( R x. H ) / 2 )')])
    rh = D(w, A, 'mulcld', [rc, hc], '( R x. H ) e. CC')
    tail = chain(w, A, ['( %s - %s )' % (EUR, R2), '( ( ( R x. H ) / 2 ) - %s )' % R2, '( ( ( R x. H ) - R ) / 2 )', '( ( R x. ( H - 1 ) ) / 2 )', '( R x. ( ( H - 1 ) / 2 ) )'],
                 [D(w, A, 'oveq1d', [er_], '( %s - %s ) = ( ( ( R x. H ) / 2 ) - %s )' % (EUR, R2, R2)),
                  ('r', D(w, A, 'divsubdird', [rh, rc, two, t0], '( ( ( R x. H ) - R ) / 2 ) = ( ( ( R x. H ) / 2 ) - %s )' % R2)),
                  D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'eqtrd', [D(w, A, 'subdid', [rc, hc, cst(w, A, 'ax-1cn', '1 e. CC')], '( R x. ( H - 1 ) ) = ( ( R x. H ) - ( R x. 1 ) )'),
                                                                        D(w, A, 'oveq2d', [D(w, A, 'mulridd', [rc], '( R x. 1 ) = R')], '( ( R x. H ) - ( R x. 1 ) ) = ( ( R x. H ) - R )')], '( R x. ( H - 1 ) ) = ( ( R x. H ) - R )')],
                                     '( ( R x. H ) - R ) = ( R x. ( H - 1 ) )')], '( ( ( R x. H ) - R ) / 2 ) = ( ( R x. ( H - 1 ) ) / 2 )'),
                  D(w, A, 'divassd', [rc, D(w, A, 'subcld', [hc, cst(w, A, 'ax-1cn', '1 e. CC')], '( H - 1 ) e. CC'), two, t0], '( ( R x. ( H - 1 ) ) / 2 ) = ( R x. ( ( H - 1 ) / 2 ) )')])
    w.qed([main, D(w, A, 'oveq2d', [tail], '( %s + ( %s - %s ) ) = ( %s + ( R x. ( ( H - 1 ) / 2 ) ) )' % (EUB, EUR, R2, EUB))], 'eqtrd', S['zl3alt'])
    go(w)


def eps_cl(w, A, chs, pp):
    PAR = L.ZL3.PAR; EPS = L.ZL3.EPS
    mn = D(w, A, 'simpld', [chs], 'M e. NN')
    mc = D(w, A, 'nncnd', [mn], 'M e. CC'); mne = D(w, A, 'nnne0d', [mn], 'M =/= 0')
    pn = par_nn0(w, A, pp, PAR)
    qq = '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) )' % PAR
    ie = D(w, A, 'expcld', [cst(w, A, 'ax-icn', '_i e. CC'), pn], '( _i ^ %s ) e. CC' % PAR)
    mh = D(w, A, 'cxpcld', [mc, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) e. CC')
    return D(w, A, 'divcld', [D(w, A, 'syl', [chs, w.inst('dchrgscl')], '( M DChrGS Y ) e. CC'), D(w, A, 'mulcld', [ie, mh], '%s e. CC' % qq),
                              D(w, A, 'mulne0d', [ie, D(w, A, 'expne0d', [cst(w, A, 'ax-icn', '_i e. CC'), cst(w, A, 'ine0', '_i =/= 0'), D(w, A, 'nn0zd', [pn], '%s e. ZZ' % PAR)], '( _i ^ %s ) =/= 0' % PAR),
                                                  mh, D(w, A, 'cxpne0d', [mc, mne, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) =/= 0')], '%s =/= 0' % qq)], '%s e. CC' % EPS)


# ---------------------------------------------------------------- zl3tfe
if want('zl3tfe'):
    w = W('zl3tfe', 'The theta functional equation solved for ` Theta_Y ( 1 / X ) ` , with the ` M = 1 ` term written through ` RM ` alone ( ~ zl3thfe , ~ zl3m1 , ~ zl3alt ).')
    A, Cc = ante_of('zl3tfe')
    Z3 = L.ZL3
    PAR, EPS, RM, TH, CYM, CYBM, YB = Z3.PAR, Z3.EPS, Z3.RM, Z3.TH, Z3.CYM, Z3.CYBM, Z3.YB
    pr_ = D(w, A, 'simpl', [], Z3.PR); xrp = D(w, A, 'simpr', [], 'X e. RR+')
    chs = D(w, A, 'simpld', [pr_], L.CH())
    par = D(w, A, 'syl', [chs, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pq = D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (PAR, YB))
    pp = D(w, A, 'simpld', [pq], '%s e. { 0 , 1 }' % PAR); ybb = D(w, A, 'simprd', [pq], '%s e. ( Base ` ( DChr ` M ) )' % YB)
    pr2 = D(w, A, 'simprd', [par], '( ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (L.LM, PAR, YB, L.LM, PAR))
    yp = D(w, A, 'simpld', [pr2], '( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (L.LM, PAR)); ybp = D(w, A, 'simprd', [pr2], '( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (YB, L.LM, PAR))
    mn = D(w, A, 'simpld', [chs], 'M e. NN')
    thfe = D(w, A, 'syl', [pr_, w.inst('zl3thfe')], L.split_imp(S['zl3thfe'])[1])
    EQ = lambda y: '( ( %s / 2 ) + %s ) = ( %s x. ( ( %s ^c ( %s + ( 1 / 2 ) ) ) x. ( ( %s / 2 ) + %s ) ) )' % (RM, TH(CYM, '( 1 / %s )' % y), EPS, y, PAR, RM, TH(CYBM, y))
    idst = w.s([], 'id', '( y = X -> y = X )')
    sub, new = w.wcongr(EQ('y'), {}, 'y = X', {}, rules={'y': ('X', idst)})
    assert new == EQ('X'), new
    eqX = D(w, A, 'rspcdva', [sub, thfe, xrp], EQ('X'))
    ix = D(w, A, 'rpreccld', [xrp], '( 1 / X ) e. RR+')
    Tc = D(w, A, 'syl3anc', [chs, D(w, A, 'jca', [pp, yp], '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, L.LM, PAR)), ix, w.inst('zl3tc')], '%s e. CC' % TH(CYM, '( 1 / X )'))
    Bc = D(w, A, 'syl3anc', [D(w, A, 'jca', [mn, ybb], L.CH(YB)), D(w, A, 'jca', [pp, ybp], '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, L.LM, PAR)), xrp, w.inst('zl3tc')],
           '%s e. CC' % TH(CYBM, 'X'))
    xc = D(w, A, 'rpcnd', [xrp], 'X e. CC')
    pn = par_nn0(w, A, pp, PAR)
    U = '( X ^c ( %s + ( 1 / 2 ) ) )' % PAR; H = '( X ^c ( 1 / 2 ) )'
    uc = D(w, A, 'cxpcld', [xc, D(w, A, 'addcld', [D(w, A, 'nn0cnd', [pn], '%s e. CC' % PAR), cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( %s + ( 1 / 2 ) ) e. CC' % PAR)], '%s e. CC' % U)
    hc = D(w, A, 'cxpcld', [xc, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '%s e. CC' % H)
    ec = eps_cl(w, A, chs, pp)
    rmc = D(w, A, 'ifcld' if False else 'a1i', [w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'ifcli', '%s e. CC' % RM)], '%s e. CC' % RM)
    # the key fact RM ( EPS U ) = RM H
    KEY = '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (RM, EPS, U, RM, H)
    A1 = '( %s /\\ M = 1 )' % A
    m1 = D(w, A1, 'syl2anc', [ad(w, A1, pr_, Z3.PR), w.s([], 'simpr', '( %s -> M = 1 )' % A1), w.inst('zl3m1')], '( %s = 0 /\\ %s = 1 )' % (PAR, EPS))
    eu1 = chain(w, A1, ['( %s x. %s )' % (EPS, U), '( 1 x. %s )' % U, U, '( X ^c ( 0 + ( 1 / 2 ) ) )', H],
                [D(w, A1, 'oveq1d', [D(w, A1, 'simprd', [m1], '%s = 1' % EPS)], '( %s x. %s ) = ( 1 x. %s )' % (EPS, U, U)), D(w, A1, 'mullidd', [ad(w, A1, uc, '%s e. CC' % U)], '( 1 x. %s ) = %s' % (U, U)),
                 D(w, A1, 'oveq2d', [D(w, A1, 'oveq1d', [D(w, A1, 'simpld', [m1], '%s = 0' % PAR)], '( %s + ( 1 / 2 ) ) = ( 0 + ( 1 / 2 ) )' % PAR)], '%s = ( X ^c ( 0 + ( 1 / 2 ) ) )' % U),
                 D(w, A1, 'oveq2d', [D(w, A1, 'addlidd', [cst(w, A1, 'halfcn', '( 1 / 2 ) e. CC')], '( 0 + ( 1 / 2 ) ) = ( 1 / 2 )')], '( X ^c ( 0 + ( 1 / 2 ) ) ) = %s' % H)])
    k1 = D(w, A1, 'oveq2d', [eu1], KEY)
    A2 = '( %s /\\ M =/= 1 )' % A
    rm0 = D(w, A2, 'syl', [D(w, A2, 'neneqd', [w.s([], 'simpr', '( %s -> M =/= 1 )' % A2)], '-. M = 1'), w.s([], 'iffalse', '( -. M = 1 -> %s = 0 )' % RM)], '%s = 0' % RM)
    k2 = D(w, A2, 'eqtr4d', [D(w, A2, 'eqtrd', [D(w, A2, 'oveq1d', [rm0], '( %s x. ( %s x. %s ) ) = ( 0 x. ( %s x. %s ) )' % (RM, EPS, U, EPS, U)),
                                                D(w, A2, 'mul02d', [D(w, A2, 'mulcld', [ad(w, A2, ec, '%s e. CC' % EPS), ad(w, A2, uc, '%s e. CC' % U)], '( %s x. %s ) e. CC' % (EPS, U))], '( 0 x. ( %s x. %s ) ) = 0' % (EPS, U))],
                                 '( %s x. ( %s x. %s ) ) = 0' % (RM, EPS, U)),
                             D(w, A2, 'eqtrd', [D(w, A2, 'oveq1d', [rm0], '( %s x. %s ) = ( 0 x. %s )' % (RM, H, H)), D(w, A2, 'mul02d', [ad(w, A2, hc, '%s e. CC' % H)], '( 0 x. %s ) = 0' % H)], '( %s x. %s ) = 0' % (RM, H))], KEY)
    key = D(w, A, 'pm2.61dane', [k1, k2], KEY)
    TT_ = TH(CYM, '( 1 / X )')
    alt = D(w, A, 'syl3anc', [D(w, A, '3jca', [rmc, ec, uc], '( %s e. CC /\\ %s e. CC /\\ %s e. CC )' % (RM, EPS, U)), D(w, A, '3jca', [Bc, hc, Tc], '( %s e. CC /\\ %s e. CC /\\ %s e. CC )' % (TH(CYBM, 'X'), H, TT_)),
                              D(w, A, 'jca', [eqX, key], '( %s /\\ %s )' % (EQ('X'), KEY)), w.inst('zl3alt')], '%s = %s' % (TT_, L.TFE_R('X')))
    xv = D(w, A, 'eqtrd', [D(w, A, 'syl3anc', [xc, D(w, A, 'rpne0d', [xrp], 'X =/= 0'), cst(w, A, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '( X ^c -u 1 ) = ( 1 / ( X ^c 1 ) )'),
                           D(w, A, 'oveq2d', [D(w, A, 'syl', [xc, w.inst('cxp1')], '( X ^c 1 ) = X')], '( 1 / ( X ^c 1 ) ) = ( 1 / X )')], '( X ^c -u 1 ) = ( 1 / X )')
    rw, new2 = w.rewrite(TH(CYM, '( X ^c -u 1 )'), {'( X ^c -u 1 )': ('( 1 / X )', xv)}, A)
    assert new2 == TT_, new2
    w.qed([rw, alt], 'eqtrd', S['zl3tfe'])
    go(w)


# ---------------------------------------------------------------- zl3cxa
if want('zl3cxa'):
    w = W('zl3cxa', 'The substituted Mellin integrand splits into the dual theta integrand and the two pole integrands ( exponent algebra, ~ cxpmul , ~ cxpadd ).')
    A, Cc = ante_of('zl3cxa')
    xrp = D(w, A, 'simpll', [], 'X e. RR+'); sc = D(w, A, 'simplrl', [], 'S e. CC'); pc = D(w, A, 'simplrr', [], 'P e. CC')
    ec = D(w, A, 'simpr1', [], 'E e. CC'); rc = D(w, A, 'simpr2', [], 'R e. CC'); bc = D(w, A, 'simpr3', [], 'B e. CC')
    xc = D(w, A, 'rpcnd', [xrp], 'X e. CC'); xn = D(w, A, 'rpne0d', [xrp], 'X =/= 0'); xcn = D(w, A, 'jca', [xc, xn], '( X e. CC /\\ X =/= 0 )')
    one = cst(w, A, 'ax-1cn', '1 e. CC'); m1 = cst(w, A, 'neg1cn', '-u 1 e. CC'); two = cst(w, A, '2cn', '2 e. CC'); t0 = cst(w, A, '2ne0', '2 =/= 0'); hf = cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')
    W_ = L.WS('S'); V_ = L.VS('S')
    spc = D(w, A, 'addcld', [sc, pc], '( S + P ) e. CC')
    wc = D(w, A, 'divcld', [spc, two, t0], '%s e. CC' % W_)
    Q = '( %s - 1 )' % W_
    qc = D(w, A, 'subcld', [wc, one], '%s e. CC' % Q)
    NW = '( -u %s - 1 )' % W_
    nwc = D(w, A, 'subcld', [D(w, A, 'negcld', [wc], '-u %s e. CC' % W_), one], '%s e. CC' % NW)
    N = '( X ^c %s )' % NW
    nc = D(w, A, 'cxpcld', [xc, nwc], '%s e. CC' % N)
    M2 = '( -u 1 - 1 )'
    m2c = D(w, A, 'subcld', [m1, one], '%s e. CC' % M2)
    # identity ( i )
    i1 = chain(w, A, ['( ( -u 1 x. %s ) + %s )' % (Q, M2), '( -u %s + %s )' % (Q, M2), '( ( 1 - %s ) + %s )' % (W_, M2), '( ( ( 1 - %s ) + -u 1 ) - 1 )' % W_,
                      '( ( ( 1 + -u 1 ) - %s ) - 1 )' % W_, '( ( 0 - %s ) - 1 )' % W_, NW],
               [D(w, A, 'oveq1d', [D(w, A, 'mulm1d', [qc], '( -u 1 x. %s ) = -u %s' % (Q, Q))], '( ( -u 1 x. %s ) + %s ) = ( -u %s + %s )' % (Q, M2, Q, M2)),
                D(w, A, 'oveq1d', [D(w, A, 'negsubdi2d', [wc, one], '-u %s = ( 1 - %s )' % (Q, W_))], '( -u %s + %s ) = ( ( 1 - %s ) + %s )' % (Q, M2, W_, M2)),
                ('r', D(w, A, 'addsubassd', [D(w, A, 'subcld', [one, wc], '( 1 - %s ) e. CC' % W_), m1, one], '( ( ( 1 - %s ) + -u 1 ) - 1 ) = ( ( 1 - %s ) + %s )' % (W_, W_, M2))),
                D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'addsubd', [one, m1, wc], '( ( 1 + -u 1 ) - %s ) = ( ( 1 - %s ) + -u 1 )' % (W_, W_))], '( ( 1 - %s ) + -u 1 ) = ( ( 1 + -u 1 ) - %s )' % (W_, W_))],
                  '( ( ( 1 - %s ) + -u 1 ) - 1 ) = ( ( ( 1 + -u 1 ) - %s ) - 1 )' % (W_, W_)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq1d', [D(w, A, 'negidd', [one], '( 1 + -u 1 ) = 0')], '( ( 1 + -u 1 ) - %s ) = ( 0 - %s )' % (W_, W_))], '( ( ( 1 + -u 1 ) - %s ) - 1 ) = ( ( 0 - %s ) - 1 )' % (W_, W_)),
                D(w, A, 'oveq1d', [w.s([w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (W_, W_))], 'eqcomi', '( 0 - %s ) = -u %s' % (W_, W_))], 'a1i', '( %s -> ( 0 - %s ) = -u %s )' % (A, W_, W_))],
                  '( ( 0 - %s ) - 1 ) = %s' % (W_, NW))])
    # identity ( iii )
    i3 = chain(w, A, ['( ( 1 / 2 ) + %s )' % NW, '( ( ( 1 / 2 ) + -u %s ) - 1 )' % W_, '( ( ( 1 / 2 ) - %s ) - 1 )' % W_, '( -u ( %s - ( 1 / 2 ) ) - 1 )' % W_],
               [('r', D(w, A, 'addsubassd', [hf, D(w, A, 'negcld', [wc], '-u %s e. CC' % W_), one], '( ( ( 1 / 2 ) + -u %s ) - 1 ) = ( ( 1 / 2 ) + %s )' % (W_, NW))),
                D(w, A, 'oveq1d', [D(w, A, 'negsubd', [hf, wc], '( ( 1 / 2 ) + -u %s ) = ( ( 1 / 2 ) - %s )' % (W_, W_))], '( ( ( 1 / 2 ) + -u %s ) - 1 ) = ( ( ( 1 / 2 ) - %s ) - 1 )' % (W_, W_)),
                D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'negsubdi2d', [wc, hf], '-u ( %s - ( 1 / 2 ) ) = ( ( 1 / 2 ) - %s )' % (W_, W_))], '( ( 1 / 2 ) - %s ) = -u ( %s - ( 1 / 2 ) )' % (W_, W_))],
                  '( ( ( 1 / 2 ) - %s ) - 1 ) = ( -u ( %s - ( 1 / 2 ) ) - 1 )' % (W_, W_))])
    # identity ( ii )
    PH = '( P + ( 1 / 2 ) )'
    phc = D(w, A, 'addcld', [pc, hf], '%s e. CC' % PH)
    D0 = '( %s - %s )' % (PH, W_)
    d0c = D(w, A, 'subcld', [phc, wc], '%s e. CC' % D0)
    twoP = '( 2 x. P )'
    tw = chain(w, A, ['( 2 x. %s )' % D0, '( ( 2 x. %s ) - ( 2 x. %s ) )' % (PH, W_), '( ( %s + ( 2 x. ( 1 / 2 ) ) ) - ( S + P ) )' % twoP, '( ( %s + 1 ) - ( S + P ) )' % twoP,
                      '( ( ( P + P ) + 1 ) - ( S + P ) )', '( ( ( P + 1 ) + P ) - ( S + P ) )', '( ( ( P + 1 ) - S ) + ( P - P ) )', '( ( ( P + 1 ) - S ) + 0 )', '( ( P + 1 ) - S )', '( ( 1 + P ) - S )',
                      '( ( 1 - S ) + P )'],
               [D(w, A, 'subdid', [two, phc, wc], '( 2 x. %s ) = ( ( 2 x. %s ) - ( 2 x. %s ) )' % (D0, PH, W_)),
                D(w, A, 'oveq12d', [D(w, A, 'adddid', [two, pc, hf], '( 2 x. %s ) = ( %s + ( 2 x. ( 1 / 2 ) ) )' % (PH, twoP)), D(w, A, 'divcan2d', [spc, two, t0], '( 2 x. %s ) = ( S + P )' % W_)],
                  '( ( 2 x. %s ) - ( 2 x. %s ) ) = ( ( %s + ( 2 x. ( 1 / 2 ) ) ) - ( S + P ) )' % (PH, W_, twoP)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'divcan2d', [one, two, t0], '( 2 x. ( 1 / 2 ) ) = 1')], '( %s + ( 2 x. ( 1 / 2 ) ) ) = ( %s + 1 )' % (twoP, twoP))],
                  '( ( %s + ( 2 x. ( 1 / 2 ) ) ) - ( S + P ) ) = ( ( %s + 1 ) - ( S + P ) )' % (twoP, twoP)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq1d', [D(w, A, '2timesd', [pc], '%s = ( P + P )' % twoP)], '( %s + 1 ) = ( ( P + P ) + 1 )' % twoP)], '( ( %s + 1 ) - ( S + P ) ) = ( ( ( P + P ) + 1 ) - ( S + P ) )' % twoP),
                D(w, A, 'oveq1d', [D(w, A, 'add32d', [pc, pc, one], '( ( P + P ) + 1 ) = ( ( P + 1 ) + P )')], '( ( ( P + P ) + 1 ) - ( S + P ) ) = ( ( ( P + 1 ) + P ) - ( S + P ) )'),
                D(w, A, 'addsub4d', [D(w, A, 'addcld', [pc, one], '( P + 1 ) e. CC'), pc, sc, pc], '( ( ( P + 1 ) + P ) - ( S + P ) ) = ( ( ( P + 1 ) - S ) + ( P - P ) )'),
                D(w, A, 'oveq2d', [D(w, A, 'subidd', [pc], '( P - P ) = 0')], '( ( ( P + 1 ) - S ) + ( P - P ) ) = ( ( ( P + 1 ) - S ) + 0 )'),
                D(w, A, 'addridd', [D(w, A, 'subcld', [D(w, A, 'addcld', [pc, one], '( P + 1 ) e. CC'), sc], '( ( P + 1 ) - S ) e. CC')], '( ( ( P + 1 ) - S ) + 0 ) = ( ( P + 1 ) - S )'),
                D(w, A, 'oveq1d', [D(w, A, 'addcomd', [pc, one], '( P + 1 ) = ( 1 + P )')], '( ( P + 1 ) - S ) = ( ( 1 + P ) - S )'),
                D(w, A, 'addsubd', [one, pc, sc], '( ( 1 + P ) - S ) = ( ( 1 - S ) + P )')])
    d0v = D(w, A, 'eqtr3d', [D(w, A, 'divcan3d', [d0c, two, t0], '( ( 2 x. %s ) / 2 ) = %s' % (D0, D0)), D(w, A, 'oveq1d', [tw], '( ( 2 x. %s ) / 2 ) = %s' % (D0, V_))], '%s = %s' % (D0, V_))
    i2 = chain(w, A, ['( %s + %s )' % (PH, NW), '( ( %s + -u %s ) - 1 )' % (PH, W_), '( %s - 1 )' % D0, '( %s - 1 )' % V_],
               [('r', D(w, A, 'addsubassd', [phc, D(w, A, 'negcld', [wc], '-u %s e. CC' % W_), one], '( ( %s + -u %s ) - 1 ) = ( %s + %s )' % (PH, W_, PH, NW))),
                D(w, A, 'oveq1d', [D(w, A, 'negsubd', [phc, wc], '( %s + -u %s ) = %s' % (PH, W_, D0))], '( ( %s + -u %s ) - 1 ) = ( %s - 1 )' % (PH, W_, D0)),
                D(w, A, 'oveq1d', [d0v], '( %s - 1 ) = ( %s - 1 )' % (D0, V_))])
    # the two factors of the substitution
    X1Q = '( ( X ^c -u 1 ) ^c %s )' % Q
    XQ = '( X ^c ( -u 1 x. %s ) )' % Q
    lq = D(w, A, 'eqcomd', [D(w, A, 'syl3anc', [xrp, cst(w, A, 'neg1rr', '-u 1 e. RR'), qc, w.inst('cxpmul')], '%s = %s' % (XQ, X1Q))], '%s = %s' % (X1Q, XQ))
    X2 = '( X ^c %s )' % M2
    xqc = D(w, A, 'cxpcld', [xc, D(w, A, 'mulcld', [m1, qc], '( -u 1 x. %s ) e. CC' % Q)], '%s e. CC' % XQ)
    x2c = D(w, A, 'cxpcld', [xc, m2c], '%s e. CC' % X2)
    MF = '( -u 1 x. %s )' % X2
    fac = chain(w, A, ['( %s x. %s )' % (X1Q, MF), '( %s x. -u %s )' % (XQ, X2), '-u ( %s x. %s )' % (XQ, X2), '-u ( X ^c ( ( -u 1 x. %s ) + %s ) )' % (Q, M2), '-u %s' % N],
                [D(w, A, 'oveq12d', [lq, D(w, A, 'mulm1d', [x2c], '%s = -u %s' % (MF, X2))], '( %s x. %s ) = ( %s x. -u %s )' % (X1Q, MF, XQ, X2)),
                 D(w, A, 'mulneg2d', [xqc, x2c], '( %s x. -u %s ) = -u ( %s x. %s )' % (XQ, X2, XQ, X2)),
                 D(w, A, 'negeqd', [D(w, A, 'eqcomd', [D(w, A, 'syl3anc', [xcn, D(w, A, 'mulcld', [m1, qc], '( -u 1 x. %s ) e. CC' % Q), m2c, w.inst('cxpadd')],
                                                         '( X ^c ( ( -u 1 x. %s ) + %s ) ) = ( %s x. %s )' % (Q, M2, XQ, X2))], '( %s x. %s ) = ( X ^c ( ( -u 1 x. %s ) + %s ) )' % (XQ, X2, Q, M2))],
                   '-u ( %s x. %s ) = -u ( X ^c ( ( -u 1 x. %s ) + %s ) )' % (XQ, X2, Q, M2)),
                 D(w, A, 'negeqd', [D(w, A, 'oveq2d', [i1], '( X ^c ( ( -u 1 x. %s ) + %s ) ) = %s' % (Q, M2, N))], '-u ( X ^c ( ( -u 1 x. %s ) + %s ) ) = -u %s' % (Q, M2, N))])
    U = '( X ^c %s )' % PH; H = '( X ^c ( 1 / 2 ) )'
    uc = D(w, A, 'cxpcld', [xc, phc], '%s e. CC' % U); hc = D(w, A, 'cxpcld', [xc, hf], '%s e. CC' % H)
    T1 = '( E x. ( %s x. B ) )' % U; T2 = '( R x. ( ( %s - 1 ) / 2 ) )' % H
    T = '( %s + %s )' % (T1, T2)
    ubc = D(w, A, 'mulcld', [uc, bc], '( %s x. B ) e. CC' % U)
    t1c = D(w, A, 'mulcld', [ec, ubc], '%s e. CC' % T1)
    h1c = D(w, A, 'subcld', [hc, one], '( %s - 1 ) e. CC' % H)
    t2c = D(w, A, 'mulcld', [rc, D(w, A, 'divcld', [h1c, two, t0], '( ( %s - 1 ) / 2 ) e. CC' % H)], '%s e. CC' % T2)
    tc = D(w, A, 'addcld', [t1c, t2c], '%s e. CC' % T)
    XV = '( X ^c ( %s - 1 ) )' % V_
    XA = '( X ^c ( -u ( %s - ( 1 / 2 ) ) - 1 ) )' % W_
    e1 = chain(w, A, ['( %s x. %s )' % (T1, N), '( E x. ( ( %s x. B ) x. %s ) )' % (U, N), '( E x. ( ( %s x. %s ) x. B ) )' % (U, N), '( E x. ( B x. ( %s x. %s ) ) )' % (U, N),
                      '( E x. ( B x. ( X ^c ( %s + %s ) ) ) )' % (PH, NW), '( E x. ( B x. %s ) )' % XV],
               [D(w, A, 'mulassd', [ec, ubc, nc], '( %s x. %s ) = ( E x. ( ( %s x. B ) x. %s ) )' % (T1, N, U, N)),
                D(w, A, 'oveq2d', [D(w, A, 'mul32d', [uc, bc, nc], '( ( %s x. B ) x. %s ) = ( ( %s x. %s ) x. B )' % (U, N, U, N))], '( E x. ( ( %s x. B ) x. %s ) ) = ( E x. ( ( %s x. %s ) x. B ) )' % (U, N, U, N)),
                D(w, A, 'oveq2d', [D(w, A, 'mulcomd', [D(w, A, 'mulcld', [uc, nc], '( %s x. %s ) e. CC' % (U, N)), bc], '( ( %s x. %s ) x. B ) = ( B x. ( %s x. %s ) )' % (U, N, U, N))],
                  '( E x. ( ( %s x. %s ) x. B ) ) = ( E x. ( B x. ( %s x. %s ) ) )' % (U, N, U, N)),
                D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, 'syl3anc', [xcn, phc, nwc, w.inst('cxpadd')], '( X ^c ( %s + %s ) ) = ( %s x. %s )' % (PH, NW, U, N))], '( %s x. %s ) = ( X ^c ( %s + %s ) )' % (U, N, PH, NW))],
                                                  '( B x. ( %s x. %s ) ) = ( B x. ( X ^c ( %s + %s ) ) )' % (U, N, PH, NW))], '( E x. ( B x. ( %s x. %s ) ) ) = ( E x. ( B x. ( X ^c ( %s + %s ) ) ) )' % (U, N, PH, NW)),
                D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [i2], '( X ^c ( %s + %s ) ) = %s' % (PH, NW, XV))], '( B x. ( X ^c ( %s + %s ) ) ) = ( B x. %s )' % (PH, NW, XV))],
                  '( E x. ( B x. ( X ^c ( %s + %s ) ) ) ) = ( E x. ( B x. %s ) )' % (PH, NW, XV))])
    R2 = '( R / 2 )'
    r2c = D(w, A, 'divcld', [rc, two, t0], '%s e. CC' % R2)
    e2 = chain(w, A, ['( %s x. %s )' % (T2, N), '( ( ( R x. ( %s - 1 ) ) / 2 ) x. %s )' % (H, N), '( ( %s x. ( %s - 1 ) ) x. %s )' % (R2, H, N), '( %s x. ( ( %s - 1 ) x. %s ) )' % (R2, H, N),
                      '( %s x. ( ( %s x. %s ) - ( 1 x. %s ) ) )' % (R2, H, N, N), '( %s x. ( ( X ^c ( ( 1 / 2 ) + %s ) ) - %s ) )' % (R2, NW, N), '( %s x. ( %s - %s ) )' % (R2, XA, N)],
               [D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [D(w, A, 'divassd', [rc, h1c, two, t0], '( ( R x. ( %s - 1 ) ) / 2 ) = %s' % (H, T2))], '%s = ( ( R x. ( %s - 1 ) ) / 2 )' % (T2, H))],
                  '( %s x. %s ) = ( ( ( R x. ( %s - 1 ) ) / 2 ) x. %s )' % (T2, N, H, N)),
                D(w, A, 'oveq1d', [D(w, A, 'div23d', [rc, h1c, two, t0], '( ( R x. ( %s - 1 ) ) / 2 ) = ( %s x. ( %s - 1 ) )' % (H, R2, H))], '( ( ( R x. ( %s - 1 ) ) / 2 ) x. %s ) = ( ( %s x. ( %s - 1 ) ) x. %s )' % (H, N, R2, H, N)),
                D(w, A, 'mulassd', [r2c, h1c, nc], '( ( %s x. ( %s - 1 ) ) x. %s ) = ( %s x. ( ( %s - 1 ) x. %s ) )' % (R2, H, N, R2, H, N)),
                D(w, A, 'oveq2d', [D(w, A, 'subdird', [hc, one, nc], '( ( %s - 1 ) x. %s ) = ( ( %s x. %s ) - ( 1 x. %s ) )' % (H, N, H, N, N))], '( %s x. ( ( %s - 1 ) x. %s ) ) = ( %s x. ( ( %s x. %s ) - ( 1 x. %s ) ) )' % (R2, H, N, R2, H, N, N)),
                D(w, A, 'oveq2d', [D(w, A, 'oveq12d', [D(w, A, 'eqcomd', [D(w, A, 'syl3anc', [xcn, hf, nwc, w.inst('cxpadd')], '( X ^c ( ( 1 / 2 ) + %s ) ) = ( %s x. %s )' % (NW, H, N))], '( %s x. %s ) = ( X ^c ( ( 1 / 2 ) + %s ) )' % (H, N, NW)),
                                                       D(w, A, 'mullidd', [nc], '( 1 x. %s ) = %s' % (N, N))], '( ( %s x. %s ) - ( 1 x. %s ) ) = ( ( X ^c ( ( 1 / 2 ) + %s ) ) - %s )' % (H, N, N, NW, N))],
                  '( %s x. ( ( %s x. %s ) - ( 1 x. %s ) ) ) = ( %s x. ( ( X ^c ( ( 1 / 2 ) + %s ) ) - %s ) )' % (R2, H, N, N, R2, NW, N)),
                D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [i3], '( X ^c ( ( 1 / 2 ) + %s ) ) = %s' % (NW, XA))], '( ( X ^c ( ( 1 / 2 ) + %s ) ) - %s ) = ( %s - %s )' % (NW, N, XA, N))],
                  '( %s x. ( ( X ^c ( ( 1 / 2 ) + %s ) ) - %s ) ) = ( %s x. ( %s - %s ) )' % (R2, NW, N, R2, XA, N))])
    x1qc = D(w, A, 'cxpcld', [D(w, A, 'cxpcld', [xc, m1], '( X ^c -u 1 ) e. CC'), qc], '%s e. CC' % X1Q)
    mfc = D(w, A, 'mulcld', [m1, x2c], '%s e. CC' % MF)
    RHS = L.CXA_R
    w.qed([chain(w, A, [L.CXA_L, '( %s x. ( %s x. %s ) )' % (T, X1Q, MF), '( %s x. -u %s )' % (T, N), '-u ( %s x. %s )' % (T, N), '-u ( ( %s x. %s ) + ( %s x. %s ) )' % (T1, N, T2, N), RHS],
                     [D(w, A, 'mulassd', [tc, x1qc, mfc], '%s = ( %s x. ( %s x. %s ) )' % (L.CXA_L, T, X1Q, MF)),
                      D(w, A, 'oveq2d', [fac], '( %s x. ( %s x. %s ) ) = ( %s x. -u %s )' % (T, X1Q, MF, T, N)),
                      D(w, A, 'mulneg2d', [tc, nc], '( %s x. -u %s ) = -u ( %s x. %s )' % (T, N, T, N)),
                      D(w, A, 'negeqd', [D(w, A, 'adddird', [t1c, t2c, nc], '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (T, N, T1, N, T2, N))], '-u ( %s x. %s ) = -u ( ( %s x. %s ) + ( %s x. %s ) )' % (T, N, T1, N, T2, N)),
                      D(w, A, 'negeqd', [D(w, A, 'oveq12d', [e1, e2], '( ( %s x. %s ) + ( %s x. %s ) ) = %s' % (T1, N, T2, N, RHS[3:]))], '-u ( ( %s x. %s ) + ( %s x. %s ) ) = %s' % (T1, N, T2, N, RHS))])],
          'idi', S['zl3cxa'])
    go(w)


# ---------------------------------------------------------------- zl3ppa
if want('zl3ppa'):
    w = W('zl3ppa', 'The pole terms for ` a = 0 ` : ` 1 / ( S / 2 - 1 / 2 ) - 1 / ( S / 2 ) = -u 2 ( 1 / S + 1 / ( 1 - S ) ) ` .')
    A, Cc = ante_of('zl3ppa')
    sc = D(w, A, 'simp1', [], 'S e. CC'); s0 = D(w, A, 'simp2', [], 'S =/= 0'); s1 = D(w, A, 'simp3', [], 'S =/= 1')
    one = cst(w, A, 'ax-1cn', '1 e. CC'); two = cst(w, A, '2cn', '2 e. CC'); t0 = cst(w, A, '2ne0', '2 =/= 0')
    sm = '( S - 1 )'
    smc = D(w, A, 'subcld', [sc, one], '%s e. CC' % sm); smn = D(w, A, 'subne0d', [sc, one, s1], '%s =/= 0' % sm)
    W0 = '( ( S + 0 ) / 2 )'
    w0 = D(w, A, 'oveq1d', [D(w, A, 'addridd', [sc], '( S + 0 ) = S')], '%s = ( S / 2 )' % W0)
    isc = D(w, A, 'reccld', [sc, s0], '( 1 / S ) e. CC'); ismc = D(w, A, 'reccld', [smc, smn], '( 1 / %s ) e. CC' % sm)
    a1 = chain(w, A, ['( 1 / ( %s - ( 1 / 2 ) ) )' % W0, '( 1 / ( ( S / 2 ) - ( 1 / 2 ) ) )', '( 1 / ( %s / 2 ) )' % sm, '( 2 / %s )' % sm, '( 2 x. ( 1 / %s ) )' % sm],
               [D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [w0], '( %s - ( 1 / 2 ) ) = ( ( S / 2 ) - ( 1 / 2 ) )' % W0)], '( 1 / ( %s - ( 1 / 2 ) ) ) = ( 1 / ( ( S / 2 ) - ( 1 / 2 ) ) )' % W0),
                D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, 'divsubdird', [sc, one, two, t0], '( %s / 2 ) = ( ( S / 2 ) - ( 1 / 2 ) )' % sm)], '( ( S / 2 ) - ( 1 / 2 ) ) = ( %s / 2 )' % sm)],
                  '( 1 / ( ( S / 2 ) - ( 1 / 2 ) ) ) = ( 1 / ( %s / 2 ) )' % sm),
                D(w, A, 'recdivd', [smc, two, smn, t0], '( 1 / ( %s / 2 ) ) = ( 2 / %s )' % (sm, sm)),
                D(w, A, 'divrecd', [two, smc, smn], '( 2 / %s ) = ( 2 x. ( 1 / %s ) )' % (sm, sm))])
    a2 = chain(w, A, ['( 1 / %s )' % W0, '( 1 / ( S / 2 ) )', '( 2 / S )', '( 2 x. ( 1 / S ) )'],
               [D(w, A, 'oveq2d', [w0], '( 1 / %s ) = ( 1 / ( S / 2 ) )' % W0), D(w, A, 'recdivd', [sc, two, s0, t0], '( 1 / ( S / 2 ) ) = ( 2 / S )'),
                D(w, A, 'divrecd', [two, sc, s0], '( 2 / S ) = ( 2 x. ( 1 / S ) )')])
    om = '( 1 - S )'
    i1s = D(w, A, 'eqtr3d', [D(w, A, 'oveq2d', [D(w, A, 'negsubdi2d', [sc, one], '-u %s = %s' % (sm, om))], '( 1 / -u %s ) = ( 1 / %s )' % (sm, om)),
                             D(w, A, 'eqcomd', [D(w, A, 'divneg2d', [one, smc, smn], '-u ( 1 / %s ) = ( 1 / -u %s )' % (sm, sm))], '( 1 / -u %s ) = -u ( 1 / %s )' % (sm, sm))], '( 1 / %s ) = -u ( 1 / %s )' % (om, sm))
    dz = chain(w, A, ['-u %s' % L.PPZ, '-u ( ( 1 / S ) + -u ( 1 / %s ) )' % sm, '( -u ( 1 / S ) + -u -u ( 1 / %s ) )' % sm, '( -u ( 1 / S ) + ( 1 / %s ) )' % sm,
                      '( ( 1 / %s ) + -u ( 1 / S ) )' % sm, '( ( 1 / %s ) - ( 1 / S ) )' % sm],
               [D(w, A, 'negeqd', [D(w, A, 'oveq2d', [i1s], '%s = ( ( 1 / S ) + -u ( 1 / %s ) )' % (L.PPZ, sm))], '-u %s = -u ( ( 1 / S ) + -u ( 1 / %s ) )' % (L.PPZ, sm)),
                D(w, A, 'negdid', [isc, D(w, A, 'negcld', [ismc], '-u ( 1 / %s ) e. CC' % sm)], '-u ( ( 1 / S ) + -u ( 1 / %s ) ) = ( -u ( 1 / S ) + -u -u ( 1 / %s ) )' % (sm, sm)),
                D(w, A, 'oveq2d', [D(w, A, 'negnegd', [ismc], '-u -u ( 1 / %s ) = ( 1 / %s )' % (sm, sm))], '( -u ( 1 / S ) + -u -u ( 1 / %s ) ) = ( -u ( 1 / S ) + ( 1 / %s ) )' % (sm, sm)),
                D(w, A, 'addcomd', [D(w, A, 'negcld', [isc], '-u ( 1 / S ) e. CC'), ismc], '( -u ( 1 / S ) + ( 1 / %s ) ) = ( ( 1 / %s ) + -u ( 1 / S ) )' % (sm, sm)),
                D(w, A, 'negsubd', [ismc, isc], '( ( 1 / %s ) + -u ( 1 / S ) ) = ( ( 1 / %s ) - ( 1 / S ) )' % (sm, sm))])
    fin = chain(w, A, ['( ( 1 / ( %s - ( 1 / 2 ) ) ) - ( 1 / %s ) )' % (W0, W0), '( ( 2 x. ( 1 / %s ) ) - ( 2 x. ( 1 / S ) ) )' % sm, '( 2 x. ( ( 1 / %s ) - ( 1 / S ) ) )' % sm,
                       '( 2 x. -u %s )' % L.PPZ, '-u ( 2 x. %s )' % L.PPZ],
                [D(w, A, 'oveq12d', [a1, a2], '( ( 1 / ( %s - ( 1 / 2 ) ) ) - ( 1 / %s ) ) = ( ( 2 x. ( 1 / %s ) ) - ( 2 x. ( 1 / S ) ) )' % (W0, W0, sm)),
                 ('r', D(w, A, 'subdid', [two, ismc, isc], '( 2 x. ( ( 1 / %s ) - ( 1 / S ) ) ) = ( ( 2 x. ( 1 / %s ) ) - ( 2 x. ( 1 / S ) ) )' % (sm, sm))),
                 D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [dz], '( ( 1 / %s ) - ( 1 / S ) ) = -u %s' % (sm, L.PPZ))], '( 2 x. ( ( 1 / %s ) - ( 1 / S ) ) ) = ( 2 x. -u %s )' % (sm, L.PPZ)),
                 D(w, A, 'mulneg2d', [two, D(w, A, 'addcld', [isc, D(w, A, 'reccld', [D(w, A, 'subcld', [one, sc], '%s e. CC' % om), D(w, A, 'eqnetrrd', [D(w, A, 'negsubdi2d', [sc, one], '-u %s = %s' % (sm, om)), D(w, A, 'negne0d', [smc, smn], '-u %s =/= 0' % sm)], '%s =/= 0' % om)],
                                                                             '( 1 / %s ) e. CC' % om)], '%s e. CC' % L.PPZ)], '( 2 x. -u %s ) = -u ( 2 x. %s )' % (L.PPZ, L.PPZ))], name='qed')
    go(w)


# ---------------------------------------------------------------- zl3ta
if want('zl3ta'):
    w = W('zl3ta', 'A Dirichlet character read on ` NN ` is a coefficient function bounded by 1 ( ~ dchrf , ~ dchrabs2 ).')
    A, Cc = ante_of('zl3ta')
    ch = D(w, A, 'simpl', [], L.CH('Z')); pp = D(w, A, 'simpr', [], 'P e. { 0 , 1 }')
    mn = D(w, A, 'simpld', [ch], 'M e. NN'); zd = D(w, A, 'simprd', [ch], 'Z e. ( Base ` ( DChr ` M ) )')
    CZZ = L.CZ('Z'); LMr = L.LM
    GD, ZN, DB, BZ = '( DChr ` M )', '( Z/nZ ` M )', '( Base ` ( DChr ` M ) )', '( Base ` ( Z/nZ ` M ) )'
    Aa = '( %s /\\ a e. NN )' % A
    an = w.s([], 'simpr', '( %s -> a e. NN )' % Aa)
    lb = lm_base(w, Aa, ad(w, Aa, mn, 'M e. NN'), 'a', D(w, Aa, 'nnzd', [an], 'a e. ZZ'))
    zf = D(w, Aa, 'dchrf', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, BZ), ad(w, Aa, zd, 'Z e. %s' % DB)], 'Z : %s --> CC' % BZ)
    zc = D(w, Aa, 'ffvelcdmd', [zf, lb], '( Z ` ( %s ` a ) ) e. CC' % LMr)
    cf = D(w, A, 'fmptd', [zc, eq_(w, CZZ)], '%s : NN --> CC' % CZZ)
    Ai = '( %s /\\ i e. NN )' % A
    inn = w.s([], 'simpr', '( %s -> i e. NN )' % Ai)
    lbi = lm_base(w, Ai, ad(w, Ai, mn, 'M e. NN'), 'i', D(w, Ai, 'nnzd', [inn], 'i e. ZZ'))
    zfi = D(w, Ai, 'dchrf', [eq_(w, GD), eq_(w, ZN), eq_(w, DB), eq_(w, BZ), ad(w, Ai, zd, 'Z e. %s' % DB)], 'Z : %s --> CC' % BZ)
    cv = fv1(w, Ai, 'a', 'NN', lambda v: '( Z ` ( %s ` %s ) )' % (LMr, v), 'i', inn, 'fvex')
    ab = D(w, Ai, 'dchrabs2', [eq_(w, GD), eq_(w, DB), eq_(w, ZN), eq_(w, BZ), ad(w, Ai, zd, 'Z e. %s' % DB), lbi], '( abs ` ( Z ` ( %s ` i ) ) ) <_ 1' % LMr)
    bi = D(w, Ai, 'eqbrtrd', [D(w, Ai, 'fveq2d', [cv], '( abs ` ( %s ` i ) ) = ( abs ` ( Z ` ( %s ` i ) ) )' % (CZZ, LMr)), ab], '( abs ` ( %s ` i ) ) <_ 1' % CZZ)
    ball = D(w, A, 'ralrimiva', [bi], 'A. i e. NN ( abs ` ( %s ` i ) ) <_ 1' % CZZ)
    w.qed([D(w, A, 'jca', [mn, pp], L.MP), D(w, A, 'jca', [cf, ball], '( %s : NN --> CC /\\ A. i e. NN ( abs ` ( %s ` i ) ) <_ 1 )' % (CZZ, CZZ))], 'jca', S['zl3ta'])
    go(w)


def ibl_pow(w, Ac, P, Q, prp, qr, e, ec):
    """( Ac -> ( x e. ( P (,) Q ) |-> ( x ^c e ) ) e. L^1 ), ( Ac -> that mapping restricted cont ... ) : via zl3cxc , zl3ibl"""
    I = '( %s [,] %s )' % (P, Q); X = '( %s (,) %s )' % (P, Q)
    both = D(w, Ac, 'syl2anc', [ec, D(w, Ac, 'jca', [prp, qr], '( %s e. RR+ /\\ %s e. RR )' % (P, Q)), w.inst('zl3cxc')],
             '( ( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC ) /\\ ( x e. %s |-> ( ( log ` x ) x. ( x ^c %s ) ) ) e. ( %s -cn-> CC ) )' % (I, e, I, I, e, I))
    cI = D(w, Ac, 'simpld', [both], '( x e. %s |-> ( x ^c %s ) ) e. ( %s -cn-> CC )' % (I, e, I))
    rs = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, I)), w.inst('resmpt')], 'ax-mp', '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) = ( x e. %s |-> ( x ^c %s ) )' % (I, e, X, X, e))], 'a1i',
             '( %s -> ( ( x e. %s |-> ( x ^c %s ) ) |` %s ) = ( x e. %s |-> ( x ^c %s ) ) )' % (Ac, I, e, X, X, e))
    pr = D(w, Ac, 'rpred', [prp], '%s e. RR' % P)
    return D(w, Ac, 'eqeltrrd', [rs, D(w, Ac, 'syl2anc', [D(w, Ac, 'jca', [pr, qr], '( %s e. RR /\\ %s e. RR )' % (P, Q)), cI, w.inst('zl3ibl')], '( ( x e. %s |-> ( x ^c %s ) ) |` %s ) e. L^1' % (I, e, X))],
             '( x e. %s |-> ( x ^c %s ) ) e. L^1' % (X, e))


# ---------------------------------------------------------------- zl3kt
if want('zl3kt'):
    w = W('zl3kt', 'The Mellin integral over ` ( 1 / t , 1 ) ` in terms of the dual theta integral and the pole integrals over ` ( 1 , t ) ` ( ~ zl3inw , ~ zl3tfe , ~ zl3cxa ).')
    A, Cc = ante_of('zl3kt')
    Z3 = L.ZL3
    PAR, EPS, RM, TH, CYM, CYBM, YB = Z3.PAR, Z3.EPS, Z3.RM, Z3.TH, Z3.CYM, Z3.CYBM, Z3.YB
    Wm, Vm = L.WM, L.VM
    pr_ = D(w, A, 'simpll', [], Z3.PR); sc = D(w, A, 'simplr', [], 's e. CC'); tr = D(w, A, 'simprl', [], 't e. RR'); t1 = D(w, A, 'simprr', [], '1 <_ t')
    chs = D(w, A, 'simpld', [pr_], L.CH())
    par = D(w, A, 'syl', [chs, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pq = D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (PAR, YB))
    pp = D(w, A, 'simpld', [pq], '%s e. { 0 , 1 }' % PAR); ybb = D(w, A, 'simprd', [pq], '%s e. ( Base ` ( DChr ` M ) )' % YB)
    mn = D(w, A, 'simpld', [chs], 'M e. NN')
    pn = par_nn0(w, A, pp, PAR); pc = D(w, A, 'nn0cnd', [pn], '%s e. CC' % PAR)
    sub_P = lambda txt: ' '.join(PAR if tk == 'P' else tk for tk in txt.split())
    taY = D(w, A, 'syl2anc', [chs, pp, w.inst('zl3ta')], sub_P(L.TAZ('Y')))
    taB = D(w, A, 'syl2anc', [D(w, A, 'jca', [mn, ybb], L.CH(YB)), pp, w.inst('zl3ta')], sub_P(L.TAZ(YB)))
    one = cst(w, A, 'ax-1cn', '1 e. CC'); two = cst(w, A, '2cn', '2 e. CC'); t0 = cst(w, A, '2ne0', '2 =/= 0')
    wc = D(w, A, 'divcld', [D(w, A, 'addcld', [sc, pc], '( s + %s ) e. CC' % PAR), two, t0], '%s e. CC' % Wm)
    vc = D(w, A, 'divcld', [D(w, A, 'addcld', [D(w, A, 'subcld', [one, sc], '( 1 - s ) e. CC'), pc], '( ( 1 - s ) + %s ) e. CC' % PAR), two, t0], '%s e. CC' % Vm)
    trp = D(w, A, 'elrpd', [tr, linarith(w, A, [t1], '0 < t', leaves={'t': tr})], 't e. RR+')
    E0 = '( 1 / ( 2 x. t ) )'
    t2p = D(w, A, 'rpmulcld', [cst(w, A, '2rp', '2 e. RR+'), trp], '( 2 x. t ) e. RR+')
    e0p = D(w, A, 'rpreccld', [t2p], '%s e. RR+' % E0)
    e0l = D(w, A, 'mpbid', [linarith(w, A, [D(w, A, 'rpgt0d', [trp], '0 < t')], 't < ( 2 x. t )', leaves={'t': tr}), D(w, A, 'ltrecd', [trp, t2p], '( t < ( 2 x. t ) <-> %s < ( 1 / t ) )' % E0)], '%s < ( 1 / t )' % E0)
    GZs = lambda z: '( %s x. ( %s ^c ( %s - 1 ) ) )' % (TH(CYM, z), z, Wm)
    FZ = '( z e. ( %s (,) 2 ) |-> %s )' % (E0, GZs('z'))
    UO = '( %s (,) 2 )' % E0
    gcz = D(w, A, 'syl2anc', [D(w, A, 'jca', [taY, wc], '( %s /\\ %s e. CC )' % (sub_P(L.TAZ('Y')), Wm)), D(w, A, 'jca', [e0p, cst(w, A, '2re', '2 e. RR')], '( %s e. RR+ /\\ 2 e. RR )' % E0), w.inst('zl3gcz')],
             '( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 )' % (FZ, UO, FZ))
    fcn = D(w, A, 'simpld', [gcz], '%s e. ( %s -cn-> CC )' % (FZ, UO))
    Mx = '( -u 1 x. ( x ^c ( -u 1 - 1 ) ) )'
    inw = D(w, A, 'syl2anc', [D(w, A, 'jca', [D(w, A, 'jca', [D(w, A, 'jca', [tr, t1], '( t e. RR /\\ 1 <_ t )'), D(w, A, 'jca', [e0p, e0l], '( %s e. RR+ /\\ %s < ( 1 / t ) )' % (E0, E0))],
                                                          '( ( t e. RR /\\ 1 <_ t ) /\\ ( %s e. RR+ /\\ %s < ( 1 / t ) ) )' % (E0, E0)), D(w, A, 'jca', [cst(w, A, '2re', '2 e. RR'), cst(w, A, '1lt2', '1 < 2')], '( 2 e. RR /\\ 1 < 2 )')],
                                            '( ( ( t e. RR /\\ 1 <_ t ) /\\ ( %s e. RR+ /\\ %s < ( 1 / t ) ) ) /\\ ( 2 e. RR /\\ 1 < 2 ) )' % (E0, E0)), fcn, w.inst('zl3inw')],
            '-u S. ( ( 1 / t ) (,) 1 ) ( %s ` u ) _d u = S. ( 1 (,) t ) ( ( %s ` ( x ^c -u 1 ) ) x. %s ) _d x' % (FZ, FZ, Mx))
    itr = D(w, A, 'rpred', [D(w, A, 'rpreccld', [trp], '( 1 / t ) e. RR+')], '( 1 / t ) e. RR')
    e0r = D(w, A, 'rpred', [e0p], '%s e. RR' % E0)
    # the left side
    KU = '( ( 1 / t ) (,) 1 )'
    Au = '( %s /\\ u e. %s )' % (A, KU)
    uK = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, KU))
    bu = D(w, Au, 'mpbid', [uK, D(w, Au, 'syl2anc', [D(w, Au, 'rexrd', [ad(w, Au, itr, '( 1 / t ) e. RR')], '( 1 / t ) e. RR*'), cst(w, Au, '1xr', '1 e. RR*'), w.inst('elioo2')],
                                                  '( u e. %s <-> ( u e. RR /\\ ( 1 / t ) < u /\\ u < 1 ) )' % KU)], '( u e. RR /\\ ( 1 / t ) < u /\\ u < 1 )')
    ur = D(w, Au, 'simp1d', [bu], 'u e. RR')
    uU = D(w, Au, 'mpbird', [D(w, Au, '3jca', [ur, D(w, Au, 'lttrd', [ad(w, Au, e0r, '%s e. RR' % E0), ad(w, Au, itr, '( 1 / t ) e. RR'), ur, ad(w, Au, e0l, '%s < ( 1 / t )' % E0), D(w, Au, 'simp2d', [bu], '( 1 / t ) < u')], '%s < u' % E0),
                                               D(w, Au, 'lttrd', [ur, cst(w, Au, '1re', '1 e. RR'), cst(w, Au, '2re', '2 e. RR'), D(w, Au, 'simp3d', [bu], 'u < 1'), cst(w, Au, '1lt2', '1 < 2')], 'u < 2')],
                                    '( u e. RR /\\ %s < u /\\ u < 2 )' % E0),
                             D(w, Au, 'syl2anc', [D(w, Au, 'rexrd', [ad(w, Au, e0r, '%s e. RR' % E0)], '%s e. RR*' % E0), cst(w, Au, '2xr' if False else 'idi', '') if False else D(w, Au, 'rexrd', [cst(w, Au, '2re', '2 e. RR')], '2 e. RR*'), w.inst('elioo2')],
                               '( u e. %s <-> ( u e. RR /\\ %s < u /\\ u < 2 ) )' % (UO, E0))], 'u e. %s' % UO)
    fu = fv1(w, Au, 'z', UO, GZs, 'u', uU, 'ovex')
    lint = D(w, A, 'itgeq2dv', [fu], 'S. %s ( %s ` u ) _d u = S. %s %s _d u' % (KU, FZ, KU, GZs('u')))
    cbl = w.s([vsub(w, GZs, 'u', 'x')], 'cbvitgv', 'S. %s %s _d u = %s' % (KU, GZs('u'), L.KT_('t')))
    kk = D(w, A, 'eqtrd', [lint, w.s([cbl], 'a1i', '( %s -> S. %s %s _d u = %s )' % (A, KU, GZs('u'), L.KT_('t')))], 'S. %s ( %s ` u ) _d u = %s' % (KU, FZ, L.KT_('t')))
    # the right side, pointwise
    X_ = '( 1 (,) t )'
    Ax = '( %s /\\ x e. %s )' % (A, X_)
    xX = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, X_))
    bx = D(w, Ax, 'mpbid', [xX, D(w, Ax, 'syl2anc', [cst(w, Ax, '1xr', '1 e. RR*'), D(w, Ax, 'rexrd', [ad(w, Ax, tr, 't e. RR')], 't e. RR*'), w.inst('elioo2')], '( x e. %s <-> ( x e. RR /\\ 1 < x /\\ x < t ) )' % X_)],
           '( x e. RR /\\ 1 < x /\\ x < t )')
    xr = D(w, Ax, 'simp1d', [bx], 'x e. RR')
    xrp = D(w, Ax, 'elrpd', [xr, linarith(w, Ax, [D(w, Ax, 'simp2d', [bx], '1 < x')], '0 < x', leaves={'x': xr})], 'x e. RR+')
    xc = D(w, Ax, 'rpcnd', [xrp], 'x e. CC')
    xv = D(w, Ax, 'eqtrd', [D(w, Ax, 'syl3anc', [xc, D(w, Ax, 'rpne0d', [xrp], 'x =/= 0'), cst(w, Ax, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '( x ^c -u 1 ) = ( 1 / ( x ^c 1 ) )'),
                            D(w, Ax, 'oveq2d', [D(w, Ax, 'syl', [xc, w.inst('cxp1')], '( x ^c 1 ) = x')], '( 1 / ( x ^c 1 ) ) = ( 1 / x )')], '( x ^c -u 1 ) = ( 1 / x )')
    ixr = D(w, Ax, 'rpred', [D(w, Ax, 'rpreccld', [xrp], '( 1 / x ) e. RR+')], '( 1 / x ) e. RR')
    itx = D(w, Ax, 'mpbid', [D(w, Ax, 'simp3d', [bx], 'x < t'), D(w, Ax, 'ltrecd', [xrp, ad(w, Ax, trp, 't e. RR+')], '( x < t <-> ( 1 / t ) < ( 1 / x ) )')], '( 1 / t ) < ( 1 / x )')
    ix1 = D(w, Ax, 'breqtrd', [D(w, Ax, 'mpbid', [D(w, Ax, 'simp2d', [bx], '1 < x'), D(w, Ax, 'ltrecd', [cst(w, Ax, '1rp', '1 e. RR+'), xrp], '( 1 < x <-> ( 1 / x ) < ( 1 / 1 ) )')], '( 1 / x ) < ( 1 / 1 )'),
                               cst(w, Ax, '1div1e1', '( 1 / 1 ) = 1')], '( 1 / x ) < 1')
    ixU = D(w, Ax, 'mpbird', [D(w, Ax, '3jca', [ixr, D(w, Ax, 'lttrd', [ad(w, Ax, e0r, '%s e. RR' % E0), ad(w, Ax, itr, '( 1 / t ) e. RR'), ixr, ad(w, Ax, e0l, '%s < ( 1 / t )' % E0), itx], '%s < ( 1 / x )' % E0),
                                                D(w, Ax, 'lttrd', [ixr, cst(w, Ax, '1re', '1 e. RR'), cst(w, Ax, '2re', '2 e. RR'), ix1, cst(w, Ax, '1lt2', '1 < 2')], '( 1 / x ) < 2')],
                                     '( ( 1 / x ) e. RR /\\ %s < ( 1 / x ) /\\ ( 1 / x ) < 2 )' % E0),
                              D(w, Ax, 'syl2anc', [D(w, Ax, 'rexrd', [ad(w, Ax, e0r, '%s e. RR' % E0)], '%s e. RR*' % E0), D(w, Ax, 'rexrd', [cst(w, Ax, '2re', '2 e. RR')], '2 e. RR*'), w.inst('elioo2')],
                                '( ( 1 / x ) e. %s <-> ( ( 1 / x ) e. RR /\\ %s < ( 1 / x ) /\\ ( 1 / x ) < 2 ) )' % (UO, E0))], '( 1 / x ) e. %s' % UO)
    x1U = D(w, Ax, 'eqeltrd', [xv, ixU], '( x ^c -u 1 ) e. %s' % UO)
    fx = fv1(w, Ax, 'z', UO, GZs, '( x ^c -u 1 )', x1U, 'ovex')
    tfe = D(w, Ax, 'syl2anc', [ad(w, Ax, pr_, Z3.PR), xrp, w.inst('zl3tfe')], '%s = %s' % (TH(CYM, '( x ^c -u 1 )'), L.TFE_R('x')))
    X1W = '( ( x ^c -u 1 ) ^c ( %s - 1 ) )' % Wm
    ORIG = '( ( %s ` ( x ^c -u 1 ) ) x. %s )' % (FZ, Mx)
    oe = D(w, Ax, 'oveq1d', [D(w, Ax, 'eqtrd', [fx, D(w, Ax, 'oveq1d', [tfe], '%s = ( %s x. %s )' % (GZs('( x ^c -u 1 )'), L.TFE_R('x'), X1W))], '( %s ` ( x ^c -u 1 ) ) = ( %s x. %s )' % (FZ, L.TFE_R('x'), X1W))],
           '%s = ( ( %s x. %s ) x. %s )' % (ORIG, L.TFE_R('x'), X1W, Mx))
    subs = {'X': 'x', 'S': 's', 'P': PAR, 'E': EPS, 'R': RM, 'B': TH(CYBM, 'x')}
    tr_ = lambda txt: ' '.join(subs.get(tk, tk) for tk in txt.split())
    CL, CR = tr_(L.CXA_L), tr_(L.CXA_R)
    assert CL == '( ( %s x. %s ) x. %s )' % (L.TFE_R('x'), X1W, Mx), CL
    par2 = D(w, A, 'simprd', [par], '( ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (L.LM, PAR, YB, L.LM, PAR))
    ybp = D(w, A, 'simprd', [par2], '( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (YB, L.LM, PAR))
    thbc = D(w, Ax, 'syl3anc', [ad(w, Ax, D(w, A, 'jca', [mn, ybb], L.CH(YB)), L.CH(YB)), ad(w, Ax, D(w, A, 'jca', [pp, ybp], '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, L.LM, PAR)),
                                                                                       '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, L.LM, PAR)), xrp, w.inst('zl3tc')], '%s e. CC' % TH(CYBM, 'x'))
    ec = eps_cl(w, A, chs, pp)
    rmc = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'ifcli', '%s e. CC' % RM)], 'a1i', '( %s -> %s e. CC )' % (A, RM))
    cxa = D(w, Ax, 'syl2anc', [D(w, Ax, 'jca', [xrp, ad(w, Ax, D(w, A, 'jca', [sc, pc], '( s e. CC /\\ %s e. CC )' % PAR), '( s e. CC /\\ %s e. CC )' % PAR)], '( x e. RR+ /\\ ( s e. CC /\\ %s e. CC ) )' % PAR),
                               D(w, Ax, '3jca', [ad(w, Ax, ec, '%s e. CC' % EPS), ad(w, Ax, rmc, '%s e. CC' % RM), thbc], '( %s e. CC /\\ %s e. CC /\\ %s e. CC )' % (EPS, RM, TH(CYBM, 'x'))), w.inst('zl3cxa')],
            '%s = %s' % (CL, CR))
    ptw = D(w, Ax, 'eqtrd', [oe, cxa], '%s = %s' % (ORIG, CR))
    # the pieces over ( 1 , t )
    XV = '( x ^c ( %s - 1 ) )' % Vm
    eA = '( -u ( %s - ( 1 / 2 ) ) - 1 )' % Wm; eN = '( -u %s - 1 )' % Wm
    XA = '( x ^c %s )' % eA; XN = '( x ^c %s )' % eN
    THBV = '( %s x. %s )' % (TH(CYBM, 'x'), XV)
    G1 = '( %s x. %s )' % (EPS, THBV); R2 = '( %s / 2 )' % RM; G2 = '( %s x. ( %s - %s ) )' % (R2, XA, XN)
    assert CR == '-u ( %s + %s )' % (G1, G2), CR
    eAc = D(w, A, 'subcld', [D(w, A, 'negcld', [D(w, A, 'subcld', [wc, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( %s - ( 1 / 2 ) ) e. CC' % Wm)], '-u ( %s - ( 1 / 2 ) ) e. CC' % Wm), one], '%s e. CC' % eA)
    eNc = D(w, A, 'subcld', [D(w, A, 'negcld', [wc], '-u %s e. CC' % Wm), one], '%s e. CC' % eN)
    GBz = lambda z: '( %s x. ( %s ^c ( %s - 1 ) ) )' % (TH(CYBM, z), z, Vm)
    GB = '( z e. %s |-> %s )' % (X_, GBz('z'))
    gczB = D(w, A, 'syl2anc', [D(w, A, 'jca', [taB, vc], '( %s /\\ %s e. CC )' % (sub_P(L.TAZ(YB)), Vm)), D(w, A, 'jca', [cst(w, A, '1rp', '1 e. RR+'), tr], '( 1 e. RR+ /\\ t e. RR )'), w.inst('zl3gcz')],
              '( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 )' % (GB, X_, GB))
    cbB = w.s([vsub(w, GBz, 'x', 'z')], 'cbvmptv', '( x e. %s |-> %s ) = %s' % (X_, THBV, GB))
    iTB = D(w, A, 'eqeltrd', [w.s([cbB], 'a1i', '( %s -> ( x e. %s |-> %s ) = %s )' % (A, X_, THBV, GB)), D(w, A, 'simprd', [gczB], '%s e. L^1' % GB)], '( x e. %s |-> %s ) e. L^1' % (X_, THBV))
    iA = ibl_pow(w, A, '1', 't', cst(w, A, '1rp', '1 e. RR+'), tr, eA, eAc)
    iN = ibl_pow(w, A, '1', 't', cst(w, A, '1rp', '1 e. RR+'), tr, eN, eNc)
    vcx = ad(w, Ax, vc, '%s e. CC' % Vm)
    tbvc = D(w, Ax, 'mulcld', [thbc, D(w, Ax, 'cxpcld', [xc, D(w, Ax, 'subcld', [vcx, cst(w, Ax, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % Vm)], '%s e. CC' % XV)], '%s e. CC' % THBV)
    xac = D(w, Ax, 'cxpcld', [xc, ad(w, Ax, eAc, '%s e. CC' % eA)], '%s e. CC' % XA); xnc = D(w, Ax, 'cxpcld', [xc, ad(w, Ax, eNc, '%s e. CC' % eN)], '%s e. CC' % XN)
    dfc = D(w, Ax, 'subcld', [xac, xnc], '( %s - %s ) e. CC' % (XA, XN))
    r2c = D(w, A, 'divcld', [rmc, two, t0], '%s e. CC' % R2)
    g1c = D(w, Ax, 'mulcld', [ad(w, Ax, ec, '%s e. CC' % EPS), tbvc], '%s e. CC' % G1); g2c = D(w, Ax, 'mulcld', [ad(w, Ax, r2c, '%s e. CC' % R2), dfc], '%s e. CC' % G2)
    iG1 = D(w, A, 'iblmulc2', [ec, tbvc, iTB], '( x e. %s |-> %s ) e. L^1' % (X_, G1))
    iD = D(w, A, 'iblsub', [xac, iA, xnc, iN], '( x e. %s |-> ( %s - %s ) ) e. L^1' % (X_, XA, XN))
    iG2 = D(w, A, 'iblmulc2', [r2c, dfc, iD], '( x e. %s |-> %s ) e. L^1' % (X_, G2))
    sG1 = D(w, A, 'itgmulc2', [ec, tbvc, iTB], '( %s x. %s ) = S. %s %s _d x' % (EPS, L.JB('t'), X_, G1))
    sD = D(w, A, 'itgsub', [xac, iA, xnc, iN], 'S. %s ( %s - %s ) _d x = ( %s - %s )' % (X_, XA, XN, L.P1('t'), L.P2('t')))
    sG2 = D(w, A, 'itgmulc2', [r2c, dfc, iD], '( %s x. S. %s ( %s - %s ) _d x ) = S. %s %s _d x' % (R2, X_, XA, XN, X_, G2))
    sadd = D(w, A, 'itgadd', [g1c, iG1, g2c, iG2], 'S. %s ( %s + %s ) _d x = ( S. %s %s _d x + S. %s %s _d x )' % (X_, G1, G2, X_, G1, X_, G2))
    sneg = D(w, A, 'itgneg', [D(w, Ax, 'addcld', [g1c, g2c], '( %s + %s ) e. CC' % (G1, G2)), D(w, A, 'ibladd', [g1c, iG1, g2c, iG2], '( x e. %s |-> ( %s + %s ) ) e. L^1' % (X_, G1, G2))],
             '-u S. %s ( %s + %s ) _d x = S. %s %s _d x' % (X_, G1, G2, X_, CR))
    sorig = D(w, A, 'itgeq2dv', [ptw], 'S. %s %s _d x = S. %s %s _d x' % (X_, ORIG, X_, CR))
    KR = L.KR('t'); K_ = L.KT_('t')
    nk = chain(w, A, ['-u %s' % K_, '-u S. %s ( %s ` u ) _d u' % (KU, FZ), 'S. %s %s _d x' % (X_, ORIG), 'S. %s %s _d x' % (X_, CR), '-u S. %s ( %s + %s ) _d x' % (X_, G1, G2),
                      '-u ( S. %s %s _d x + S. %s %s _d x )' % (X_, G1, X_, G2), '-u %s' % KR],
               [D(w, A, 'negeqd', [D(w, A, 'eqcomd', [kk], '%s = S. %s ( %s ` u ) _d u' % (K_, KU, FZ))], '-u %s = -u S. %s ( %s ` u ) _d u' % (K_, KU, FZ)), inw, sorig, ('r', sneg),
                D(w, A, 'negeqd', [sadd], '-u S. %s ( %s + %s ) _d x = -u ( S. %s %s _d x + S. %s %s _d x )' % (X_, G1, G2, X_, G1, X_, G2)),
                D(w, A, 'negeqd', [D(w, A, 'oveq12d', [D(w, A, 'eqcomd', [sG1], 'S. %s %s _d x = ( %s x. %s )' % (X_, G1, EPS, L.JB('t'))),
                                                       D(w, A, 'eqtr3d', [sG2, D(w, A, 'oveq2d', [sD], '( %s x. S. %s ( %s - %s ) _d x ) = ( %s x. ( %s - %s ) )' % (R2, X_, XA, XN, R2, L.P1('t'), L.P2('t')))],
                                                         'S. %s %s _d x = ( %s x. ( %s - %s ) )' % (X_, G2, R2, L.P1('t'), L.P2('t')))], '( S. %s %s _d x + S. %s %s _d x ) = %s' % (X_, G1, X_, G2, KR))],
                  '-u ( S. %s %s _d x + S. %s %s _d x ) = -u %s' % (X_, G1, X_, G2, KR))])
    # K and KR are complex numbers
    GKz = '( z e. %s |-> %s )' % (KU, GZs('z'))
    gczK = D(w, A, 'syl2anc', [D(w, A, 'jca', [taY, wc], '( %s /\\ %s e. CC )' % (sub_P(L.TAZ('Y')), Wm)), D(w, A, 'jca', [D(w, A, 'rpreccld', [trp], '( 1 / t ) e. RR+'), cst(w, A, '1re', '1 e. RR')], '( ( 1 / t ) e. RR+ /\\ 1 e. RR )'),
                               w.inst('zl3gcz')], '( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 )' % (GKz, KU, GKz))
    cbK = w.s([vsub(w, GZs, 'x', 'z')], 'cbvmptv', '( x e. %s |-> %s ) = %s' % (KU, GZs('x'), GKz))
    iK = D(w, A, 'eqeltrd', [w.s([cbK], 'a1i', '( %s -> ( x e. %s |-> %s ) = %s )' % (A, KU, GZs('x'), GKz)), D(w, A, 'simprd', [gczK], '%s e. L^1' % GKz)], '( x e. %s |-> %s ) e. L^1' % (KU, GZs('x')))
    AxK = '( %s /\\ x e. %s )' % (A, KU)
    bxk = D(w, AxK, 'mpbid', [w.s([], 'simpr', '( %s -> x e. %s )' % (AxK, KU)), D(w, AxK, 'syl2anc', [D(w, AxK, 'rexrd', [ad(w, AxK, itr, '( 1 / t ) e. RR')], '( 1 / t ) e. RR*'), cst(w, AxK, '1xr', '1 e. RR*'), w.inst('elioo2')],
                                                                              '( x e. %s <-> ( x e. RR /\\ ( 1 / t ) < x /\\ x < 1 ) )' % KU)], '( x e. RR /\\ ( 1 / t ) < x /\\ x < 1 )')
    xrk = D(w, AxK, 'simp1d', [bxk], 'x e. RR')
    xrpk = D(w, AxK, 'elrpd', [xrk, D(w, AxK, 'lttrd', [cst(w, AxK, '0re', '0 e. RR'), ad(w, AxK, itr, '( 1 / t ) e. RR'), xrk, D(w, AxK, 'rpgt0d', [ad(w, AxK, D(w, A, 'rpreccld', [trp], '( 1 / t ) e. RR+'), '( 1 / t ) e. RR+')], '0 < ( 1 / t )'),
                                                         D(w, AxK, 'simp2d', [bxk], '( 1 / t ) < x')], '0 < x')], 'x e. RR+')
    thck = D(w, AxK, 'syl3anc', [ad(w, AxK, chs, L.CH()), ad(w, AxK, D(w, A, 'jca', [pp, D(w, A, 'simpld', [par2], '( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (L.LM, PAR))], '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, L.LM, PAR)),
                                                                           '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, L.LM, PAR)), xrpk, w.inst('zl3tc')], '%s e. CC' % TH(CYM, 'x'))
    gkc = D(w, AxK, 'mulcld', [thck, D(w, AxK, 'cxpcld', [D(w, AxK, 'rpcnd', [xrpk], 'x e. CC'), D(w, AxK, 'subcld', [ad(w, AxK, wc, '%s e. CC' % Wm), cst(w, AxK, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % Wm)],
                                                     '( x ^c ( %s - 1 ) ) e. CC' % Wm)], '%s e. CC' % GZs('x'))
    kc = D(w, A, 'itgcl', [iK, gkc], '%s e. CC' % K_)
    jbc = D(w, A, 'itgcl', [iTB, tbvc], '%s e. CC' % L.JB('t'))
    p1c = D(w, A, 'itgcl', [iA, xac], '%s e. CC' % L.P1('t')); p2c = D(w, A, 'itgcl', [iN, xnc], '%s e. CC' % L.P2('t'))
    krc = D(w, A, 'addcld', [D(w, A, 'mulcld', [ec, jbc], '( %s x. %s ) e. CC' % (EPS, L.JB('t'))), D(w, A, 'mulcld', [r2c, D(w, A, 'subcld', [p1c, p2c], '( %s - %s ) e. CC' % (L.P1('t'), L.P2('t')))],
                                                                                                           '( %s x. ( %s - %s ) ) e. CC' % (R2, L.P1('t'), L.P2('t')))], '%s e. CC' % KR)
    w.qed([kc, krc, nk], 'neg11d', S['zl3kt'])
    go(w)


# ---------------------------------------------------------------- zl3ilm
if want('zl3ilm'):
    w = W('zl3ilm', 'The integral over ` ( 1 , t ) ` of the theta Mellin integrand converges to ` GAMF LS - ( EPS IL~ + pole terms ) ` ( ~ zl3mlm , ~ zl3kt , ~ zl3pcv , ~ zl3pol ).')
    A, Cc = ante_of('zl3ilm')
    Z3 = L.ZL3
    PAR, EPS, RM, TH, CYM, CYBM, YB = Z3.PAR, Z3.EPS, Z3.RM, Z3.TH, Z3.CYM, Z3.CYBM, Z3.YB
    Wm, Vm = L.WM, L.VM
    prs = D(w, A, 'simpl', [], '( %s /\\ s e. CC )' % Z3.PR)
    pr_ = D(w, A, 'simpll', [], Z3.PR); sc = D(w, A, 'simplr', [], 's e. CC'); s1 = D(w, A, 'simpr', [], '1 < ( Re ` s )')
    chs = D(w, A, 'simpld', [pr_], L.CH())
    par = D(w, A, 'syl', [chs, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pq = D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (PAR, YB))
    pp = D(w, A, 'simpld', [pq], '%s e. { 0 , 1 }' % PAR); ybb = D(w, A, 'simprd', [pq], '%s e. ( Base ` ( DChr ` M ) )' % YB)
    par2 = D(w, A, 'simprd', [par], '( ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (L.LM, PAR, YB, L.LM, PAR))
    yp = D(w, A, 'simpld', [par2], '( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (L.LM, PAR)); ybp = D(w, A, 'simprd', [par2], '( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (YB, L.LM, PAR))
    mn = D(w, A, 'simpld', [chs], 'M e. NN')
    pn = par_nn0(w, A, pp, PAR); pc = D(w, A, 'nn0cnd', [pn], '%s e. CC' % PAR); prr = D(w, A, 'nn0red', [pn], '%s e. RR' % PAR); p0 = D(w, A, 'nn0ge0d', [pn], '0 <_ %s' % PAR)
    sub_P = lambda txt: ' '.join(PAR if tk == 'P' else tk for tk in txt.split())
    TAY, TAB = sub_P(L.TAZ('Y')), sub_P(L.TAZ(YB))
    taY = D(w, A, 'syl2anc', [chs, pp, w.inst('zl3ta')], TAY)
    chB = D(w, A, 'jca', [mn, ybb], L.CH(YB))
    taB = D(w, A, 'syl2anc', [chB, pp, w.inst('zl3ta')], TAB)
    one = cst(w, A, 'ax-1cn', '1 e. CC'); two = cst(w, A, '2cn', '2 e. CC'); t0 = cst(w, A, '2ne0', '2 =/= 0'); hf = cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')
    spc = D(w, A, 'addcld', [sc, pc], '( s + %s ) e. CC' % PAR)
    wc = D(w, A, 'divcld', [spc, two, t0], '%s e. CC' % Wm)
    vc = D(w, A, 'divcld', [D(w, A, 'addcld', [D(w, A, 'subcld', [one, sc], '( 1 - s ) e. CC'), pc], '( ( 1 - s ) + %s ) e. CC' % PAR), two, t0], '%s e. CC' % Vm)
    RS = '( Re ` s )'
    rsr = D(w, A, 'recld', [sc], '%s e. RR' % RS)
    SG = '( ( %s + %s ) / 2 )' % (RS, PAR)
    rw = chain(w, A, ['( Re ` %s )' % Wm, '( ( Re ` ( s + %s ) ) / 2 )' % PAR, '( ( %s + ( Re ` %s ) ) / 2 )' % (RS, PAR), SG],
               [D(w, A, 'redivd', [cst(w, A, '2re', '2 e. RR'), spc, t0], '( Re ` %s ) = ( ( Re ` ( s + %s ) ) / 2 )' % (Wm, PAR)),
                D(w, A, 'oveq1d', [D(w, A, 'readdd', [sc, pc], '( Re ` ( s + %s ) ) = ( %s + ( Re ` %s ) )' % (PAR, RS, PAR))], '( ( Re ` ( s + %s ) ) / 2 ) = ( ( %s + ( Re ` %s ) ) / 2 )' % (PAR, RS, PAR)),
                D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'rered', [prr], '( Re ` %s ) = %s' % (PAR, PAR))], '( %s + ( Re ` %s ) ) = ( %s + %s )' % (RS, PAR, RS, PAR))], '( ( %s + ( Re ` %s ) ) / 2 ) = %s' % (RS, PAR, SG))])
    sgr = D(w, A, 'redivcld', [D(w, A, 'readdcld', [rsr, prr], '( %s + %s ) e. RR' % (RS, PAR)), cst(w, A, '2re', '2 e. RR'), t0], '%s e. RR' % SG)
    lvs = {RS: rsr, PAR: prr}
    w0 = D(w, A, 'breqtrrd', [linarith(w, A, [s1, p0], '0 < %s' % SG, leaves=dict(lvs), atoms=[RS, PAR]), rw], '0 < ( Re ` %s )' % Wm)
    Wh = '( %s - ( 1 / 2 ) )' % Wm
    whc = D(w, A, 'subcld', [wc, hf], '%s e. CC' % Wh)
    rwh = chain(w, A, ['( Re ` %s )' % Wh, '( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) )' % Wm, '( %s - ( 1 / 2 ) )' % SG],
                [D(w, A, 'resubd', [wc, hf], '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) )' % (Wh, Wm)),
                 D(w, A, 'oveq12d', [rw, D(w, A, 'rered', [cst(w, A, 'halfre', '( 1 / 2 ) e. RR')], '( Re ` ( 1 / 2 ) ) = ( 1 / 2 )')], '( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) ) = ( %s - ( 1 / 2 ) )' % (Wm, SG))])
    wh0 = D(w, A, 'breqtrrd', [linarith(w, A, [s1, p0], '0 < ( %s - ( 1 / 2 ) )' % SG, leaves=dict(lvs), atoms=[RS, PAR]), rwh], '0 < ( Re ` %s )' % Wh)
    ec = eps_cl(w, A, chs, pp)
    rmc = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'ifcli', '%s e. CC' % RM)], 'a1i', '( %s -> %s e. CC )' % (A, RM))
    tsub = lambda txt, m: ' '.join(m.get(tk, tk) for tk in txt.split())
    def gib(Ac, Cf, taz, tazt, Wv, wvc, P, Q, prp, qr, var):
        body = lambda v: '( %s x. ( %s ^c ( %s - 1 ) ) )' % (TH(Cf, v), v, Wv)
        GZt = '( z e. ( %s (,) %s ) |-> %s )' % (P, Q, body('z'))
        inst = D(w, Ac, 'syl2anc', [D(w, Ac, 'jca', [taz, wvc], '( %s /\\ %s e. CC )' % (tazt, Wv)), D(w, Ac, 'jca', [prp, qr], '( %s e. RR+ /\\ %s e. RR )' % (P, Q)), w.inst('zl3gcz')],
                 '( %s e. ( ( %s (,) %s ) -cn-> CC ) /\\ %s e. L^1 )' % (GZt, P, Q, GZt))
        cb = w.s([vsub(w, body, var, 'z')], 'cbvmptv', '( %s e. ( %s (,) %s ) |-> %s ) = %s' % (var, P, Q, body(var), GZt))
        return D(w, Ac, 'eqeltrd', [w.s([cb], 'a1i', '( %s -> ( %s e. ( %s (,) %s ) |-> %s ) = %s )' % (Ac, var, P, Q, body(var), GZt)), D(w, Ac, 'simprd', [inst], '%s e. L^1' % GZt)],
                 '( %s e. ( %s (,) %s ) |-> %s ) e. L^1' % (var, P, Q, body(var)))
    def thcc(Ac, Cf, X, xrp_, lift):
        if Cf == CYM:
            chz, zp = lift(chs, L.CH()), lift(D(w, A, 'jca', [pp, yp], '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, L.LM, PAR)), '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, L.LM, PAR))
        else:
            chz, zp = lift(chB, L.CH(YB)), lift(D(w, A, 'jca', [pp, ybp], '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, L.LM, PAR)), '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, L.LM, PAR))
        return D(w, Ac, 'syl3anc', [chz, zp, xrp_, w.inst('zl3tc')], '%s e. CC' % TH(Cf, X))
    def iopos(Ac, P, Q, v, pr_, qr_, p0_):
        """v e. ( P (,) Q ) in Ac (last conjunct): v real, P < v, v < Q, v e. RR+"""
        X = '( %s (,) %s )' % (P, Q)
        vX = w.s([], 'simpr', '( %s -> %s e. %s )' % (Ac, v, X))
        b = D(w, Ac, 'mpbid', [vX, D(w, Ac, 'syl2anc', [D(w, Ac, 'rexrd', [pr_], '%s e. RR*' % P), D(w, Ac, 'rexrd', [qr_], '%s e. RR*' % Q), w.inst('elioo2')],
                                                     '( %s e. %s <-> ( %s e. RR /\\ %s < %s /\\ %s < %s ) )' % (v, X, v, P, v, v, Q))], '( %s e. RR /\\ %s < %s /\\ %s < %s )' % (v, P, v, v, Q))
        vr = D(w, Ac, 'simp1d', [b], '%s e. RR' % v); lo = D(w, Ac, 'simp2d', [b], '%s < %s' % (P, v)); hi = D(w, Ac, 'simp3d', [b], '%s < %s' % (v, Q))
        vrp = D(w, Ac, 'elrpd', [vr, D(w, Ac, 'lttrd', [cst(w, Ac, '0re', '0 e. RR'), pr_, vr, p0_, lo], '0 < %s' % v)], '%s e. RR+' % v)
        return vr, lo, hi, vrp
    # C1 : the Mellin limit
    MTIm = 'S. ( ( 1 / t ) (,) t ) ( %s x. ( x ^c ( %s - 1 ) ) ) _d x' % (TH(CYM, 'x'), Wm)
    assert MTIm == tsub(L.MTI(Wm, 't'), {'C': CYM, 'P': PAR})
    GLM = L.GLM
    assert '( ( t e. RR+ |-> %s ) ~~>r %s )' % (MTIm, GLM) == '( %s )' % tsub(L.split_imp(S['zl3mlm'])[1], {'C': CYM, 'P': PAR, 'S': 's'})[2:-2] or True
    mlm = D(w, A, 'syl2anc', [taY, D(w, A, 'jca', [sc, s1], '( s e. CC /\\ 1 < ( Re ` s ) )'), w.inst('zl3mlm')], '( t e. RR+ |-> %s ) ~~>r %s' % (MTIm, GLM))
    # C2 : the dual theta integral converges
    GTH0 = tsub(L.GTH, {'C': CYBM, 'P': PAR}); PHT0 = tsub(L.PHT, {'C': CYBM, 'P': PAR})
    thph0 = D(w, A, 'syl', [taB, w.inst('zl3thph')], PHT0)
    THm = lambda v: tsub(TH(CYBM, v), {'n': 'm'})
    GTHB = '( r e. ( 1 [,) +oo ) |-> %s )' % THm('r')
    SMD = lambda v, q: tsub(TH(CYBM, v)[len('sum_ n e. NN '):], {'n': q})
    cbs_r = w.s([vsub(w, lambda q: SMD('r', q), 'n', 'm')], 'cbvsumv', '%s = %s' % (TH(CYBM, 'r'), THm('r')))
    eyr = w.s([vsub(w, lambda v: TH(CYBM, v), 'y', 'r'), w.s([cbs_r], 'a1i', '( y = r -> %s = %s )' % (TH(CYBM, 'r'), THm('r')))], 'eqtrd', '( y = r -> %s = %s )' % (TH(CYBM, 'y'), THm('r')))
    eqG = w.s([w.s([eyr], 'cbvmptv', '%s = %s' % (GTH0, GTHB))], 'a1i', '( %s -> %s = %s )' % (A, GTH0, GTHB))
    wb, PHTB = w.wcongr(PHT0, {}, A, {}, rules={GTH0: (GTHB, eqG)})
    thph = D(w, A, 'mpbid', [thph0, wb], PHTB)
    V1 = '( %s - 1 )' % Vm
    v1c = D(w, A, 'subcld', [vc, one], '%s e. CC' % V1)
    PCV = tsub(L.split_imp(S['zl3pcv'])[1], {'G': GTHB, 'K': L.KT, 'B': '( _pi / M )', 'S': V1})
    pcv = D(w, A, 'syl2anc', [thph, v1c, w.inst('zl3pcv')], PCV)
    LSUM = PCV[PCV.index(' ~~>r ') + 6:]
    JBG = lambda t: 'S. ( 1 (,) %s ) ( ( %s ` y ) x. ( y ^c %s ) ) _d y' % (t, GTHB, V1)
    JBY = lambda t: 'S. ( 1 (,) %s ) ( %s x. ( y ^c %s ) ) _d y' % (t, TH(CYBM, 'y'), V1)
    assert PCV.startswith('( t e. RR+ |-> %s ) ~~>r' % JBG('t')), PCV[:200]
    At = '( %s /\\ t e. RR+ )' % A
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % At); trt = D(w, At, 'rpred', [trp], 't e. RR')
    Aty = '( %s /\\ y e. ( 1 (,) t ) )' % At
    yr, y1, _, yrp = iopos(Aty, '1', 't', 'y', cst(w, Aty, '1re', '1 e. RR'), ad(w, Aty, trt, 't e. RR'), cst(w, Aty, '0lt1', '0 < 1'))
    yU = D(w, Aty, 'mpbird', [D(w, Aty, 'jca', [yr, D(w, Aty, 'ltled', [cst(w, Aty, '1re', '1 e. RR'), yr, y1], '1 <_ y')], '( y e. RR /\\ 1 <_ y )'),
                              D(w, Aty, 'syl', [cst(w, Aty, '1re', '1 e. RR'), w.inst('elicopnf')], '( y e. ( 1 [,) +oo ) <-> ( y e. RR /\\ 1 <_ y ) )')], 'y e. ( 1 [,) +oo )')
    lty = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aty, f))
    thby = thcc(Aty, CYBM, 'y', yrp, lty)
    cbs_y = w.s([vsub(w, lambda q: SMD('y', q), 'm', 'n')], 'cbvsumv', '%s = %s' % (THm('y'), TH(CYBM, 'y')))
    gv = D(w, Aty, 'eqtrd', [fv1(w, Aty, 'r', '( 1 [,) +oo )', THm, 'y', yU, 'sumex'), w.s([cbs_y], 'a1i', '( %s -> %s = %s )' % (Aty, THm('y'), TH(CYBM, 'y')))],
           '( %s ` y ) = %s' % (GTHB, TH(CYBM, 'y')))
    jbe = D(w, At, 'itgeq2dv', [D(w, Aty, 'oveq1d', [gv], '( ( %s ` y ) x. ( y ^c %s ) ) = ( %s x. ( y ^c %s ) )' % (GTHB, V1, TH(CYBM, 'y'), V1))], '%s = %s' % (JBG('t'), JBY('t')))
    IMB = L.IMAP(CYBM)
    assert IMB == '( t e. RR+ |-> %s )' % JBY('t')
    cvB = D(w, A, 'mpbid', [pcv, D(w, A, 'breq1d', [D(w, A, 'mpteq2dva', [jbe], '( t e. RR+ |-> %s ) = %s' % (JBG('t'), IMB))], '( ( t e. RR+ |-> %s ) ~~>r %s <-> %s ~~>r %s )' % (JBG('t'), LSUM, IMB, LSUM))],
            '%s ~~>r %s' % (IMB, LSUM))
    lt_ = lambda st, f: ad(w, At, st, f)
    ibB = gib(At, CYBM, lt_(taB, TAB), TAB, Vm, lt_(vc, '%s e. CC' % Vm), '1', 't', cst(w, At, '1rp', '1 e. RR+'), trt, 'y')
    ybc = D(w, Aty, 'mulcld', [thby, D(w, Aty, 'cxpcld', [D(w, Aty, 'rpcnd', [yrp], 'y e. CC'), lty(v1c, '%s e. CC' % V1)], '( y ^c %s ) e. CC' % V1)], '( %s x. ( y ^c %s ) ) e. CC' % (TH(CYBM, 'y'), V1))
    jbyc = D(w, At, 'itgcl', [ibB, ybc], '%s e. CC' % JBY('t'))
    fB = D(w, A, 'fmptd', [jbyc, w.s([], 'eqid', '%s = %s' % (IMB, IMB))], '%s : RR+ --> CC' % IMB)
    sup = cst(w, A, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    def rl_val(fm, fmap, conv, lim):
        dm = D(w, A, 'syl2anc' if False else 'sylancr' if False else 'syl2anc', [cst(w, A, 'rlimrel', 'Rel ~~>r'), conv, w.inst('releldm')], '%s e. dom ~~>r' % fmap)
        return D(w, A, 'mpbid', [dm, D(w, A, 'rlimdm', [fm, sup], '( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) )' % (fmap, fmap, fmap))], '%s ~~>r ( ~~>r ` %s )' % (fmap, fmap))
    cvB2 = rl_val(fB, IMB, cvB, LSUM)
    assert L.ILB == '( ~~>r ` %s )' % IMB
    # C3 : the pole integrals
    pol1 = D(w, A, 'syl2anc', [whc, wh0, w.inst('zl3pol')], '( t e. RR+ |-> %s ) ~~>r ( 1 / %s )' % (L.P1('t'), Wh))
    pol2 = D(w, A, 'syl2anc', [wc, w0, w.inst('zl3pol')], '( t e. RR+ |-> %s ) ~~>r ( 1 / %s )' % (L.P2('t'), Wm))
    # C4 : for t >_ 1 the integral over ( 1 , t ) is MTI - KR
    gx = lambda Cf, Wv, v: '( %s x. ( %s ^c ( %s - 1 ) ) )' % (TH(Cf, v), v, Wv)
    IX = lambda t: 'S. ( 1 (,) %s ) %s _d x' % (t, gx(CYM, Wm, 'x'))
    IY = lambda t: 'S. ( 1 (,) %s ) %s _d y' % (t, gx(CYM, Wm, 'y'))
    Au = '( %s /\\ ( t e. RR+ /\\ 1 <_ t ) )' % A
    trpu = w.s([], 'simprl', '( %s -> t e. RR+ )' % Au); t1u = w.s([], 'simprr', '( %s -> 1 <_ t )' % Au)
    tru = D(w, Au, 'rpred', [trpu], 't e. RR'); itpu = D(w, Au, 'rpreccld', [trpu], '( 1 / t ) e. RR+'); itru = D(w, Au, 'rpred', [itpu], '( 1 / t ) e. RR')
    lu = lambda st, f: ad(w, Au, st, f)
    it1 = D(w, Au, 'breqtrd', [D(w, Au, 'mpbid', [t1u, D(w, Au, 'lerecd', [cst(w, Au, '1rp', '1 e. RR+'), trpu], '( 1 <_ t <-> ( 1 / t ) <_ ( 1 / 1 ) )')], '( 1 / t ) <_ ( 1 / 1 )'), cst(w, Au, '1div1e1', '( 1 / 1 ) = 1')], '( 1 / t ) <_ 1')
    oneI = D(w, Au, 'mpbird', [D(w, Au, '3jca', [cst(w, Au, '1re', '1 e. RR'), it1, t1u], '( 1 e. RR /\\ ( 1 / t ) <_ 1 /\\ 1 <_ t )'),
                               D(w, Au, 'syl2anc', [itru, tru, w.inst('elicc2')], '( 1 e. ( ( 1 / t ) [,] t ) <-> ( 1 e. RR /\\ ( 1 / t ) <_ 1 /\\ 1 <_ t ) )')], '1 e. ( ( 1 / t ) [,] t )')
    Aux = '( %s /\\ x e. ( ( 1 / t ) (,) t ) )' % Au
    _, _, _, xrpu = iopos(Aux, '( 1 / t )', 't', 'x', ad(w, Aux, itru, '( 1 / t ) e. RR'), ad(w, Aux, tru, 't e. RR'), D(w, Aux, 'rpgt0d', [ad(w, Aux, itpu, '( 1 / t ) e. RR+')], '0 < ( 1 / t )'))
    lux = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aux, f))
    gxc = lambda Ac, xrp_, lift: D(w, Ac, 'mulcld', [thcc(Ac, CYM, 'x', xrp_, lift), D(w, Ac, 'cxpcld', [D(w, Ac, 'rpcnd', [xrp_], 'x e. CC'), D(w, Ac, 'subcld', [lift(wc, '%s e. CC' % Wm), cst(w, Ac, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % Wm)],
                                                                                    '( x ^c ( %s - 1 ) ) e. CC' % Wm)], '%s e. CC' % gx(CYM, Wm, 'x'))
    gcu = gxc(Aux, xrpu, lux)
    ib1 = gib(Au, CYM, lu(taY, TAY), TAY, Wm, lu(wc, '%s e. CC' % Wm), '( 1 / t )', '1', itpu, cst(w, Au, '1re', '1 e. RR'), 'x')
    ib2 = gib(Au, CYM, lu(taY, TAY), TAY, Wm, lu(wc, '%s e. CC' % Wm), '1', 't', cst(w, Au, '1rp', '1 e. RR+'), tru, 'x')
    K_ = L.KT_('t')
    spl = D(w, Au, 'itgsplitioo', [itru, tru, oneI, gcu, ib1, ib2], '%s = ( %s + %s )' % (MTIm, K_, IX('t')))
    Aux1 = '( %s /\\ x e. ( ( 1 / t ) (,) 1 ) )' % Au
    _, _, _, xrp1 = iopos(Aux1, '( 1 / t )', '1', 'x', ad(w, Aux1, itru, '( 1 / t ) e. RR'), cst(w, Aux1, '1re', '1 e. RR'), D(w, Aux1, 'rpgt0d', [ad(w, Aux1, itpu, '( 1 / t ) e. RR+')], '0 < ( 1 / t )'))
    kc = D(w, Au, 'itgcl', [ib1, gxc(Aux1, xrp1, lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aux1, f)))], '%s e. CC' % K_)
    Aux2 = '( %s /\\ x e. ( 1 (,) t ) )' % Au
    _, _, _, xrp2 = iopos(Aux2, '1', 't', 'x', cst(w, Aux2, '1re', '1 e. RR'), ad(w, Aux2, tru, 't e. RR'), cst(w, Aux2, '0lt1', '0 < 1'))
    ixc = D(w, Au, 'itgcl', [ib2, gxc(Aux2, xrp2, lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aux2, f)))], '%s e. CC' % IX('t'))
    kt = D(w, Au, 'syl2anc', [lu(prs, '( %s /\\ s e. CC )' % Z3.PR), D(w, Au, 'jca', [tru, t1u], '( t e. RR /\\ 1 <_ t )'), w.inst('zl3kt')], '%s = %s' % (K_, L.KR('t')))
    KR = L.KR('t')
    ixe = chain(w, Au, [IX('t'), '( ( %s + %s ) - %s )' % (K_, IX('t'), K_), '( %s - %s )' % (MTIm, K_), '( %s - %s )' % (MTIm, KR)],
                [('r', D(w, Au, 'pncan2d', [kc, ixc], '( ( %s + %s ) - %s ) = %s' % (K_, IX('t'), K_, IX('t')))),
                 D(w, Au, 'oveq1d', [D(w, Au, 'eqcomd', [spl], '( %s + %s ) = %s' % (K_, IX('t'), MTIm))], '( ( %s + %s ) - %s ) = ( %s - %s )' % (K_, IX('t'), K_, MTIm, K_)),
                 D(w, Au, 'oveq2d', [kt], '( %s - %s ) = ( %s - %s )' % (MTIm, K_, MTIm, KR))])
    cyx = w.s([vsub(w, lambda v: gx(CYM, Wm, v), 'y', 'x')], 'cbvitgv', '%s = %s' % (IY('t'), IX('t')))
    eqL = D(w, Au, 'eqtrd', [w.s([cyx], 'a1i', '( %s -> %s = %s )' % (Au, IY('t'), IX('t'))), ixe], '%s = ( %s - %s )' % (IY('t'), MTIm, KR))
    # C5 : the limit of MTI - KR over all t e. RR+
    itpt = D(w, At, 'rpreccld', [trp], '( 1 / t ) e. RR+'); itrt = D(w, At, 'rpred', [itpt], '( 1 / t ) e. RR')
    ibM = gib(At, CYM, lt_(taY, TAY), TAY, Wm, lt_(wc, '%s e. CC' % Wm), '( 1 / t )', 't', itpt, trt, 'x')
    Atx = '( %s /\\ x e. ( ( 1 / t ) (,) t ) )' % At
    _, _, _, xrpt = iopos(Atx, '( 1 / t )', 't', 'x', ad(w, Atx, itrt, '( 1 / t ) e. RR'), ad(w, Atx, trt, 't e. RR'), D(w, Atx, 'rpgt0d', [ad(w, Atx, itpt, '( 1 / t ) e. RR+')], '0 < ( 1 / t )'))
    mtc = D(w, At, 'itgcl', [ibM, gxc(Atx, xrpt, lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Atx, f)))], '%s e. CC' % MTIm)
    JBX = L.JB('t')
    ibJ = gib(At, CYBM, lt_(taB, TAB), TAB, Vm, lt_(vc, '%s e. CC' % Vm), '1', 't', cst(w, At, '1rp', '1 e. RR+'), trt, 'x')
    Atx2 = '( %s /\\ x e. ( 1 (,) t ) )' % At
    _, _, _, xrpt2 = iopos(Atx2, '1', 't', 'x', cst(w, Atx2, '1re', '1 e. RR'), ad(w, Atx2, trt, 't e. RR'), cst(w, Atx2, '0lt1', '0 < 1'))
    l2 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Atx2, f))
    jbxc = D(w, At, 'itgcl', [ibJ, D(w, Atx2, 'mulcld', [thcc(Atx2, CYBM, 'x', xrpt2, l2), D(w, Atx2, 'cxpcld', [D(w, Atx2, 'rpcnd', [xrpt2], 'x e. CC'), l2(v1c, '%s e. CC' % V1)], '( x ^c %s ) e. CC' % V1)],
                                           '%s e. CC' % gx(CYBM, Vm, 'x'))], '%s e. CC' % JBX)
    eA = '( -u %s - 1 )' % Wh; eN = '( -u %s - 1 )' % Wm
    eAc = D(w, A, 'subcld', [D(w, A, 'negcld', [whc], '-u %s e. CC' % Wh), one], '%s e. CC' % eA); eNc = D(w, A, 'subcld', [D(w, A, 'negcld', [wc], '-u %s e. CC' % Wm), one], '%s e. CC' % eN)
    p1c = D(w, At, 'itgcl', [ibl_pow(w, At, '1', 't', cst(w, At, '1rp', '1 e. RR+'), trt, eA, lt_(eAc, '%s e. CC' % eA)),
                             D(w, Atx2, 'cxpcld', [D(w, Atx2, 'rpcnd', [xrpt2], 'x e. CC'), l2(eAc, '%s e. CC' % eA)], '( x ^c %s ) e. CC' % eA)], '%s e. CC' % L.P1('t'))
    p2c = D(w, At, 'itgcl', [ibl_pow(w, At, '1', 't', cst(w, At, '1rp', '1 e. RR+'), trt, eN, lt_(eNc, '%s e. CC' % eN)),
                             D(w, Atx2, 'cxpcld', [D(w, Atx2, 'rpcnd', [xrpt2], 'x e. CC'), l2(eNc, '%s e. CC' % eN)], '( x ^c %s ) e. CC' % eN)], '%s e. CC' % L.P2('t'))
    JBYv = 'S. ( 1 (,) t ) %s _d y' % gx(CYBM, Vm, 'y')
    cbj = w.s([vsub(w, lambda v: gx(CYBM, Vm, v), 'x', 'y')], 'cbvitgv', '%s = %s' % (JBX, JBYv))
    JMX = '( t e. RR+ |-> %s )' % JBX
    cvJ = D(w, A, 'mpbird', [cvB, D(w, A, 'breq1d', [D(w, A, 'mpteq2dva', [w.s([cbj], 'a1i', '( %s -> %s = %s )' % (At, JBX, JBYv))], '%s = %s' % (JMX, IMB))],
                                                      '( %s ~~>r %s <-> %s ~~>r %s )' % (JMX, LSUM, IMB, LSUM))], '%s ~~>r %s' % (JMX, LSUM))
    lsi = D(w, A, 'rlimuni', [fB, sup, cvB, cvB2], '%s = %s' % (LSUM, L.ILB))
    rpre = cst(w, A, 'rpssre', 'RR+ C_ RR')
    const = lambda c, cc: D(w, A, 'syl2anc', [rpre, cc, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (c, c))
    ILB = LSUM
    r1 = D(w, A, 'rlimmul', [lt_(ec, '%s e. CC' % EPS), jbxc, const(EPS, ec), cvJ], '( t e. RR+ |-> ( %s x. %s ) ) ~~>r ( %s x. %s )' % (EPS, JBX, EPS, ILB))
    PD_ = '( %s - %s )' % (L.P1('t'), L.P2('t'))
    r2 = D(w, A, 'rlimsub', [p1c, p2c, pol1, pol2], '( t e. RR+ |-> %s ) ~~>r ( ( 1 / %s ) - ( 1 / %s ) )' % (PD_, Wh, Wm))
    R2 = '( %s / 2 )' % RM
    r2c = D(w, A, 'divcld', [rmc, two, t0], '%s e. CC' % R2)
    pdc = D(w, At, 'subcld', [p1c, p2c], '%s e. CC' % PD_)
    r3 = D(w, A, 'rlimmul', [lt_(r2c, '%s e. CC' % R2), pdc, const(R2, r2c), r2], '( t e. RR+ |-> ( %s x. %s ) ) ~~>r %s' % (R2, PD_, L.PT))
    ejc = D(w, At, 'mulcld', [lt_(ec, '%s e. CC' % EPS), jbxc], '( %s x. %s ) e. CC' % (EPS, JBX))
    rpc = D(w, At, 'mulcld', [lt_(r2c, '%s e. CC' % R2), pdc], '( %s x. %s ) e. CC' % (R2, PD_))
    r4 = D(w, A, 'rlimadd', [ejc, rpc, r1, r3], '( t e. RR+ |-> %s ) ~~>r ( ( %s x. %s ) + %s )' % (KR, EPS, ILB, L.PT))
    krc = D(w, At, 'addcld', [ejc, rpc], '%s e. CC' % KR)
    XVL = '( %s - ( ( %s x. %s ) + %s ) )' % (L.GLM, EPS, LSUM, L.PT)
    r5 = D(w, A, 'rlimsub', [mtc, krc, mlm, r4], '( t e. RR+ |-> ( %s - %s ) ) ~~>r %s' % (MTIm, KR, XVL))
    # C6 : transfer to the integral over ( 1 , t )
    Aty2 = '( %s /\\ y e. ( 1 (,) t ) )' % At
    _, _, _, yrp2 = iopos(Aty2, '1', 't', 'y', cst(w, Aty2, '1re', '1 e. RR'), ad(w, Aty2, trt, 't e. RR'), cst(w, Aty2, '0lt1', '0 < 1'))
    ly2 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aty2, f))
    ibY = gib(At, CYM, lt_(taY, TAY), TAY, Wm, lt_(wc, '%s e. CC' % Wm), '1', 't', cst(w, At, '1rp', '1 e. RR+'), trt, 'y')
    iyc = D(w, At, 'itgcl', [ibY, D(w, Aty2, 'mulcld', [thcc(Aty2, CYM, 'y', yrp2, ly2), D(w, Aty2, 'cxpcld', [D(w, Aty2, 'rpcnd', [yrp2], 'y e. CC'), D(w, Aty2, 'subcld', [ly2(wc, '%s e. CC' % Wm), cst(w, Aty2, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % Wm)],
                                                                                                              '( y ^c ( %s - 1 ) ) e. CC' % Wm)], '%s e. CC' % gx(CYM, Wm, 'y'))], '%s e. CC' % IY('t'))
    req = D(w, A, 'rlimeq', [iyc, D(w, At, 'subcld', [mtc, krc], '( %s - %s ) e. CC' % (MTIm, KR)), cst(w, A, '1re', '1 e. RR'), eqL],
            '( ( t e. RR+ |-> %s ) ~~>r %s <-> ( t e. RR+ |-> ( %s - %s ) ) ~~>r %s )' % (IY('t'), XVL, MTIm, KR, XVL))
    xve = D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [lsi], '( %s x. %s ) = ( %s x. %s )' % (EPS, LSUM, EPS, L.ILB))], '( ( %s x. %s ) + %s ) = ( ( %s x. %s ) + %s )' % (EPS, LSUM, L.PT, EPS, L.ILB, L.PT))],
            '%s = %s' % (XVL, L.XV_))
    w.qed([D(w, A, 'mpbird', [r5, req], '( t e. RR+ |-> %s ) ~~>r %s' % (IY('t'), XVL)), xve], 'breqtrd', S['zl3ilm'])
    go(w)


# ---------------------------------------------------------------- zl3ilc
if want('zl3ilc'):
    w = W('zl3ilc', 'Closure facts for ~ zl3mel : the integral function is complex-valued, and the dual integral limit, ` GAMF LS ` and the pole difference are complex numbers.')
    import textwrap
    exec(textwrap.dedent('    A, Cc = ante_of(\'zl3ilc\')\n    Z3 = L.ZL3\n    PAR, EPS, RM, TH, CYM, CYBM, YB = Z3.PAR, Z3.EPS, Z3.RM, Z3.TH, Z3.CYM, Z3.CYBM, Z3.YB\n    Wm, Vm = L.WM, L.VM\n    prs = D(w, A, \'simpl\', [], \'( %s /\\\\ s e. CC )\' % Z3.PR)\n    pr_ = D(w, A, \'simpll\', [], Z3.PR); sc = D(w, A, \'simplr\', [], \'s e. CC\'); s1 = D(w, A, \'simpr\', [], \'1 < ( Re ` s )\')\n    chs = D(w, A, \'simpld\', [pr_], L.CH())\n    par = D(w, A, \'syl\', [chs, w.inst(\'zl3par\')], L.split_imp(S[\'zl3par\'])[1])\n    pq = D(w, A, \'simpld\', [par], \'( %s e. { 0 , 1 } /\\\\ %s e. ( Base ` ( DChr ` M ) ) )\' % (PAR, YB))\n    pp = D(w, A, \'simpld\', [pq], \'%s e. { 0 , 1 }\' % PAR); ybb = D(w, A, \'simprd\', [pq], \'%s e. ( Base ` ( DChr ` M ) )\' % YB)\n    par2 = D(w, A, \'simprd\', [par], \'( ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) /\\\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )\' % (L.LM, PAR, YB, L.LM, PAR))\n    yp = D(w, A, \'simpld\', [par2], \'( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )\' % (L.LM, PAR)); ybp = D(w, A, \'simprd\', [par2], \'( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )\' % (YB, L.LM, PAR))\n    mn = D(w, A, \'simpld\', [chs], \'M e. NN\')\n    pn = par_nn0(w, A, pp, PAR); pc = D(w, A, \'nn0cnd\', [pn], \'%s e. CC\' % PAR); prr = D(w, A, \'nn0red\', [pn], \'%s e. RR\' % PAR); p0 = D(w, A, \'nn0ge0d\', [pn], \'0 <_ %s\' % PAR)\n    sub_P = lambda txt: \' \'.join(PAR if tk == \'P\' else tk for tk in txt.split())\n    TAY, TAB = sub_P(L.TAZ(\'Y\')), sub_P(L.TAZ(YB))\n    taY = D(w, A, \'syl2anc\', [chs, pp, w.inst(\'zl3ta\')], TAY)\n    chB = D(w, A, \'jca\', [mn, ybb], L.CH(YB))\n    taB = D(w, A, \'syl2anc\', [chB, pp, w.inst(\'zl3ta\')], TAB)\n    one = cst(w, A, \'ax-1cn\', \'1 e. CC\'); two = cst(w, A, \'2cn\', \'2 e. CC\'); t0 = cst(w, A, \'2ne0\', \'2 =/= 0\'); hf = cst(w, A, \'halfcn\', \'( 1 / 2 ) e. CC\')\n    spc = D(w, A, \'addcld\', [sc, pc], \'( s + %s ) e. CC\' % PAR)\n    wc = D(w, A, \'divcld\', [spc, two, t0], \'%s e. CC\' % Wm)\n    vc = D(w, A, \'divcld\', [D(w, A, \'addcld\', [D(w, A, \'subcld\', [one, sc], \'( 1 - s ) e. CC\'), pc], \'( ( 1 - s ) + %s ) e. CC\' % PAR), two, t0], \'%s e. CC\' % Vm)\n    RS = \'( Re ` s )\'\n    rsr = D(w, A, \'recld\', [sc], \'%s e. RR\' % RS)\n    SG = \'( ( %s + %s ) / 2 )\' % (RS, PAR)\n    rw = chain(w, A, [\'( Re ` %s )\' % Wm, \'( ( Re ` ( s + %s ) ) / 2 )\' % PAR, \'( ( %s + ( Re ` %s ) ) / 2 )\' % (RS, PAR), SG],\n               [D(w, A, \'redivd\', [cst(w, A, \'2re\', \'2 e. RR\'), spc, t0], \'( Re ` %s ) = ( ( Re ` ( s + %s ) ) / 2 )\' % (Wm, PAR)),\n                D(w, A, \'oveq1d\', [D(w, A, \'readdd\', [sc, pc], \'( Re ` ( s + %s ) ) = ( %s + ( Re ` %s ) )\' % (PAR, RS, PAR))], \'( ( Re ` ( s + %s ) ) / 2 ) = ( ( %s + ( Re ` %s ) ) / 2 )\' % (PAR, RS, PAR)),\n                D(w, A, \'oveq1d\', [D(w, A, \'oveq2d\', [D(w, A, \'rered\', [prr], \'( Re ` %s ) = %s\' % (PAR, PAR))], \'( %s + ( Re ` %s ) ) = ( %s + %s )\' % (RS, PAR, RS, PAR))], \'( ( %s + ( Re ` %s ) ) / 2 ) = %s\' % (RS, PAR, SG))])\n    sgr = D(w, A, \'redivcld\', [D(w, A, \'readdcld\', [rsr, prr], \'( %s + %s ) e. RR\' % (RS, PAR)), cst(w, A, \'2re\', \'2 e. RR\'), t0], \'%s e. RR\' % SG)\n    lvs = {RS: rsr, PAR: prr}\n    w0 = D(w, A, \'breqtrrd\', [linarith(w, A, [s1, p0], \'0 < %s\' % SG, leaves=dict(lvs), atoms=[RS, PAR]), rw], \'0 < ( Re ` %s )\' % Wm)\n    Wh = \'( %s - ( 1 / 2 ) )\' % Wm\n    whc = D(w, A, \'subcld\', [wc, hf], \'%s e. CC\' % Wh)\n    rwh = chain(w, A, [\'( Re ` %s )\' % Wh, \'( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) )\' % Wm, \'( %s - ( 1 / 2 ) )\' % SG],\n                [D(w, A, \'resubd\', [wc, hf], \'( Re ` %s ) = ( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) )\' % (Wh, Wm)),\n                 D(w, A, \'oveq12d\', [rw, D(w, A, \'rered\', [cst(w, A, \'halfre\', \'( 1 / 2 ) e. RR\')], \'( Re ` ( 1 / 2 ) ) = ( 1 / 2 )\')], \'( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) ) = ( %s - ( 1 / 2 ) )\' % (Wm, SG))])\n    wh0 = D(w, A, \'breqtrrd\', [linarith(w, A, [s1, p0], \'0 < ( %s - ( 1 / 2 ) )\' % SG, leaves=dict(lvs), atoms=[RS, PAR]), rwh], \'0 < ( Re ` %s )\' % Wh)\n    ec = eps_cl(w, A, chs, pp)\n    rmc = w.s([w.s([w.s([], \'ax-1cn\', \'1 e. CC\'), w.s([], \'0cn\', \'0 e. CC\')], \'ifcli\', \'%s e. CC\' % RM)], \'a1i\', \'( %s -> %s e. CC )\' % (A, RM))\n    tsub = lambda txt, m: \' \'.join(m.get(tk, tk) for tk in txt.split())\n    def gib(Ac, Cf, taz, tazt, Wv, wvc, P, Q, prp, qr, var):\n        body = lambda v: \'( %s x. ( %s ^c ( %s - 1 ) ) )\' % (TH(Cf, v), v, Wv)\n        GZt = \'( z e. ( %s (,) %s ) |-> %s )\' % (P, Q, body(\'z\'))\n        inst = D(w, Ac, \'syl2anc\', [D(w, Ac, \'jca\', [taz, wvc], \'( %s /\\\\ %s e. CC )\' % (tazt, Wv)), D(w, Ac, \'jca\', [prp, qr], \'( %s e. RR+ /\\\\ %s e. RR )\' % (P, Q)), w.inst(\'zl3gcz\')],\n                 \'( %s e. ( ( %s (,) %s ) -cn-> CC ) /\\\\ %s e. L^1 )\' % (GZt, P, Q, GZt))\n        cb = w.s([vsub(w, body, var, \'z\')], \'cbvmptv\', \'( %s e. ( %s (,) %s ) |-> %s ) = %s\' % (var, P, Q, body(var), GZt))\n        return D(w, Ac, \'eqeltrd\', [w.s([cb], \'a1i\', \'( %s -> ( %s e. ( %s (,) %s ) |-> %s ) = %s )\' % (Ac, var, P, Q, body(var), GZt)), D(w, Ac, \'simprd\', [inst], \'%s e. L^1\' % GZt)],\n                 \'( %s e. ( %s (,) %s ) |-> %s ) e. L^1\' % (var, P, Q, body(var)))\n    def thcc(Ac, Cf, X, xrp_, lift):\n        if Cf == CYM:\n            chz, zp = lift(chs, L.CH()), lift(D(w, A, \'jca\', [pp, yp], \'( %s e. { 0 , 1 } /\\\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )\' % (PAR, L.LM, PAR)), \'( %s e. { 0 , 1 } /\\\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )\' % (PAR, L.LM, PAR))\n        else:\n            chz, zp = lift(chB, L.CH(YB)), lift(D(w, A, \'jca\', [pp, ybp], \'( %s e. { 0 , 1 } /\\\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )\' % (PAR, YB, L.LM, PAR)), \'( %s e. { 0 , 1 } /\\\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )\' % (PAR, YB, L.LM, PAR))\n        return D(w, Ac, \'syl3anc\', [chz, zp, xrp_, w.inst(\'zl3tc\')], \'%s e. CC\' % TH(Cf, X))\n    def iopos(Ac, P, Q, v, pr_, qr_, p0_):\n        """v e. ( P (,) Q ) in Ac (last conjunct): v real, P < v, v < Q, v e. RR+"""\n        X = \'( %s (,) %s )\' % (P, Q)\n        vX = w.s([], \'simpr\', \'( %s -> %s e. %s )\' % (Ac, v, X))\n        b = D(w, Ac, \'mpbid\', [vX, D(w, Ac, \'syl2anc\', [D(w, Ac, \'rexrd\', [pr_], \'%s e. RR*\' % P), D(w, Ac, \'rexrd\', [qr_], \'%s e. RR*\' % Q), w.inst(\'elioo2\')],\n                                                     \'( %s e. %s <-> ( %s e. RR /\\\\ %s < %s /\\\\ %s < %s ) )\' % (v, X, v, P, v, v, Q))], \'( %s e. RR /\\\\ %s < %s /\\\\ %s < %s )\' % (v, P, v, v, Q))\n        vr = D(w, Ac, \'simp1d\', [b], \'%s e. RR\' % v); lo = D(w, Ac, \'simp2d\', [b], \'%s < %s\' % (P, v)); hi = D(w, Ac, \'simp3d\', [b], \'%s < %s\' % (v, Q))\n        vrp = D(w, Ac, \'elrpd\', [vr, D(w, Ac, \'lttrd\', [cst(w, Ac, \'0re\', \'0 e. RR\'), pr_, vr, p0_, lo], \'0 < %s\' % v)], \'%s e. RR+\' % v)\n        return vr, lo, hi, vrp\n    # C1 : the Mellin limit\n    MTIm = \'S. ( ( 1 / t ) (,) t ) ( %s x. ( x ^c ( %s - 1 ) ) ) _d x\' % (TH(CYM, \'x\'), Wm)\n    assert MTIm == tsub(L.MTI(Wm, \'t\'), {\'C\': CYM, \'P\': PAR})\n    GLM = L.GLM\n    assert \'( ( t e. RR+ |-> %s ) ~~>r %s )\' % (MTIm, GLM) == \'( %s )\' % tsub(L.split_imp(S[\'zl3mlm\'])[1], {\'C\': CYM, \'P\': PAR, \'S\': \'s\'})[2:-2] or True\n    mlm = D(w, A, \'syl2anc\', [taY, D(w, A, \'jca\', [sc, s1], \'( s e. CC /\\\\ 1 < ( Re ` s ) )\'), w.inst(\'zl3mlm\')], \'( t e. RR+ |-> %s ) ~~>r %s\' % (MTIm, GLM))\n    # C2 : the dual theta integral converges\n    GTH0 = tsub(L.GTH, {\'C\': CYBM, \'P\': PAR}); PHT0 = tsub(L.PHT, {\'C\': CYBM, \'P\': PAR})\n    thph0 = D(w, A, \'syl\', [taB, w.inst(\'zl3thph\')], PHT0)\n    THm = lambda v: tsub(TH(CYBM, v), {\'n\': \'m\'})\n    GTHB = \'( r e. ( 1 [,) +oo ) |-> %s )\' % THm(\'r\')\n    SMD = lambda v, q: tsub(TH(CYBM, v)[len(\'sum_ n e. NN \'):], {\'n\': q})\n    cbs_r = w.s([vsub(w, lambda q: SMD(\'r\', q), \'n\', \'m\')], \'cbvsumv\', \'%s = %s\' % (TH(CYBM, \'r\'), THm(\'r\')))\n    eyr = w.s([vsub(w, lambda v: TH(CYBM, v), \'y\', \'r\'), w.s([cbs_r], \'a1i\', \'( y = r -> %s = %s )\' % (TH(CYBM, \'r\'), THm(\'r\')))], \'eqtrd\', \'( y = r -> %s = %s )\' % (TH(CYBM, \'y\'), THm(\'r\')))\n    eqG = w.s([w.s([eyr], \'cbvmptv\', \'%s = %s\' % (GTH0, GTHB))], \'a1i\', \'( %s -> %s = %s )\' % (A, GTH0, GTHB))\n    wb, PHTB = w.wcongr(PHT0, {}, A, {}, rules={GTH0: (GTHB, eqG)})\n    thph = D(w, A, \'mpbid\', [thph0, wb], PHTB)\n    V1 = \'( %s - 1 )\' % Vm\n    v1c = D(w, A, \'subcld\', [vc, one], \'%s e. CC\' % V1)\n    PCV = tsub(L.split_imp(S[\'zl3pcv\'])[1], {\'G\': GTHB, \'K\': L.KT, \'B\': \'( _pi / M )\', \'S\': V1})\n    pcv = D(w, A, \'syl2anc\', [thph, v1c, w.inst(\'zl3pcv\')], PCV)\n    LSUM = PCV[PCV.index(\' ~~>r \') + 6:]\n    JBG = lambda t: \'S. ( 1 (,) %s ) ( ( %s ` y ) x. ( y ^c %s ) ) _d y\' % (t, GTHB, V1)\n    JBY = lambda t: \'S. ( 1 (,) %s ) ( %s x. ( y ^c %s ) ) _d y\' % (t, TH(CYBM, \'y\'), V1)\n    assert PCV.startswith(\'( t e. RR+ |-> %s ) ~~>r\' % JBG(\'t\')), PCV[:200]\n    At = \'( %s /\\\\ t e. RR+ )\' % A\n    trp = w.s([], \'simpr\', \'( %s -> t e. RR+ )\' % At); trt = D(w, At, \'rpred\', [trp], \'t e. RR\')\n    Aty = \'( %s /\\\\ y e. ( 1 (,) t ) )\' % At\n    yr, y1, _, yrp = iopos(Aty, \'1\', \'t\', \'y\', cst(w, Aty, \'1re\', \'1 e. RR\'), ad(w, Aty, trt, \'t e. RR\'), cst(w, Aty, \'0lt1\', \'0 < 1\'))\n    yU = D(w, Aty, \'mpbird\', [D(w, Aty, \'jca\', [yr, D(w, Aty, \'ltled\', [cst(w, Aty, \'1re\', \'1 e. RR\'), yr, y1], \'1 <_ y\')], \'( y e. RR /\\\\ 1 <_ y )\'),\n                              D(w, Aty, \'syl\', [cst(w, Aty, \'1re\', \'1 e. RR\'), w.inst(\'elicopnf\')], \'( y e. ( 1 [,) +oo ) <-> ( y e. RR /\\\\ 1 <_ y ) )\')], \'y e. ( 1 [,) +oo )\')\n    lty = lambda st, f: w.s([st], \'ad2antrr\', \'( %s -> %s )\' % (Aty, f))\n    thby = thcc(Aty, CYBM, \'y\', yrp, lty)\n    cbs_y = w.s([vsub(w, lambda q: SMD(\'y\', q), \'m\', \'n\')], \'cbvsumv\', \'%s = %s\' % (THm(\'y\'), TH(CYBM, \'y\')))\n    gv = D(w, Aty, \'eqtrd\', [fv1(w, Aty, \'r\', \'( 1 [,) +oo )\', THm, \'y\', yU, \'sumex\'), w.s([cbs_y], \'a1i\', \'( %s -> %s = %s )\' % (Aty, THm(\'y\'), TH(CYBM, \'y\')))],\n           \'( %s ` y ) = %s\' % (GTHB, TH(CYBM, \'y\')))\n    jbe = D(w, At, \'itgeq2dv\', [D(w, Aty, \'oveq1d\', [gv], \'( ( %s ` y ) x. ( y ^c %s ) ) = ( %s x. ( y ^c %s ) )\' % (GTHB, V1, TH(CYBM, \'y\'), V1))], \'%s = %s\' % (JBG(\'t\'), JBY(\'t\')))\n    IMB = L.IMAP(CYBM)\n    assert IMB == \'( t e. RR+ |-> %s )\' % JBY(\'t\')\n    cvB = D(w, A, \'mpbid\', [pcv, D(w, A, \'breq1d\', [D(w, A, \'mpteq2dva\', [jbe], \'( t e. RR+ |-> %s ) = %s\' % (JBG(\'t\'), IMB))], \'( ( t e. RR+ |-> %s ) ~~>r %s <-> %s ~~>r %s )\' % (JBG(\'t\'), LSUM, IMB, LSUM))],\n            \'%s ~~>r %s\' % (IMB, LSUM))\n    lt_ = lambda st, f: ad(w, At, st, f)\n    ibB = gib(At, CYBM, lt_(taB, TAB), TAB, Vm, lt_(vc, \'%s e. CC\' % Vm), \'1\', \'t\', cst(w, At, \'1rp\', \'1 e. RR+\'), trt, \'y\')\n    ybc = D(w, Aty, \'mulcld\', [thby, D(w, Aty, \'cxpcld\', [D(w, Aty, \'rpcnd\', [yrp], \'y e. CC\'), lty(v1c, \'%s e. CC\' % V1)], \'( y ^c %s ) e. CC\' % V1)], \'( %s x. ( y ^c %s ) ) e. CC\' % (TH(CYBM, \'y\'), V1))\n    jbyc = D(w, At, \'itgcl\', [ibB, ybc], \'%s e. CC\' % JBY(\'t\'))\n    fB = D(w, A, \'fmptd\', [jbyc, w.s([], \'eqid\', \'%s = %s\' % (IMB, IMB))], \'%s : RR+ --> CC\' % IMB)\n    sup = cst(w, A, \'rpsup\', \'sup ( RR+ , RR* , < ) = +oo\')\n    def rl_val(fm, fmap, conv, lim):\n        dm = D(w, A, \'syl2anc\' if False else \'sylancr\' if False else \'syl2anc\', [cst(w, A, \'rlimrel\', \'Rel ~~>r\'), conv, w.inst(\'releldm\')], \'%s e. dom ~~>r\' % fmap)\n        return D(w, A, \'mpbid\', [dm, D(w, A, \'rlimdm\', [fm, sup], \'( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) )\' % (fmap, fmap, fmap))], \'%s ~~>r ( ~~>r ` %s )\' % (fmap, fmap))\n    cvB2 = rl_val(fB, IMB, cvB, LSUM)\n    assert L.ILB == \'( ~~>r ` %s )\' % IMB\n'))
    # the integral function is complex valued
    IMY = L.IMAP(CYM)
    gyb = lambda v: '( %s x. ( %s ^c ( %s - 1 ) ) )' % (TH(CYM, v), v, Wm)
    ibY = gib(At, CYM, lt_(taY, TAY), TAY, Wm, lt_(wc, '%s e. CC' % Wm), '1', 't', cst(w, At, '1rp', '1 e. RR+'), trt, 'y')
    Aty3 = '( %s /\\ y e. ( 1 (,) t ) )' % At
    _, _, _, yrp3 = iopos(Aty3, '1', 't', 'y', cst(w, Aty3, '1re', '1 e. RR'), ad(w, Aty3, trt, 't e. RR'), cst(w, Aty3, '0lt1', '0 < 1'))
    ly3 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Aty3, f))
    iyc = D(w, At, 'itgcl', [ibY, D(w, Aty3, 'mulcld', [thcc(Aty3, CYM, 'y', yrp3, ly3), D(w, Aty3, 'cxpcld', [D(w, Aty3, 'rpcnd', [yrp3], 'y e. CC'), D(w, Aty3, 'subcld', [ly3(wc, '%s e. CC' % Wm), cst(w, Aty3, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % Wm)],
                                                                                                               '( y ^c ( %s - 1 ) ) e. CC' % Wm)], '%s e. CC' % gyb('y'))], 'S. ( 1 (,) t ) %s _d y e. CC' % gyb('y'))
    fY = D(w, A, 'fmptd', [iyc, w.s([], 'eqid', '%s = %s' % (IMY, IMY))], '%s : RR+ --> CC' % IMY)
    ilbc = D(w, A, 'syl', [cvB2, w.inst('rlimcl')], '%s e. CC' % L.ILB)
    glc = D(w, A, 'syl', [mlm, w.inst('rlimcl')], '%s e. CC' % GLM)
    def ne0_(z, zc_, z0_):
        return D(w, A, 'mpbird', [D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), D(w, A, 'recld', [zc_], '( Re ` %s ) e. RR' % z), D(w, A, 'abscld', [zc_], '( abs ` %s ) e. RR' % z), z0_,
                                                      D(w, A, 'releabsd', [zc_], '( Re ` %s ) <_ ( abs ` %s )' % (z, z))], '0 < ( abs ` %s )' % z),
                                  D(w, A, 'syl', [zc_, w.inst('absgt0')], '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (z, z))], '%s =/= 0' % z)
    dpc = D(w, A, 'subcld', [D(w, A, 'reccld', [whc, ne0_(Wh, whc, wh0)], '( 1 / %s ) e. CC' % Wh), D(w, A, 'reccld', [wc, ne0_(Wm, wc, w0)], '( 1 / %s ) e. CC' % Wm)], '%s e. CC' % L.DP)
    w.qed([D(w, A, 'jca', [fY, ilbc], '( %s : RR+ --> CC /\\ %s e. CC )' % (IMY, L.ILB)), D(w, A, 'jca', [glc, dpc], '( %s e. CC /\\ %s e. CC )' % (GLM, L.DP))], 'jca', S['zl3ilc'])
    go(w)


# ---------------------------------------------------------------- zl3mel
if want('zl3mel'):
    w = W('zl3mel', 'The Mellin identity: ` Lambda ( s ) = I ( s ) + EPS I~ ( 1 - s ) - RM ( 1 / s + 1 / ( 1 - s ) ) ` on ` 1 < Re s ` ( ~ zl3ilm , ~ zl3ppa ).')
    Z3 = L.ZL3
    PAR, EPS, RM, CYM, CYBM = Z3.PAR, Z3.EPS, Z3.RM, Z3.CYM, Z3.CYBM
    Wm = L.WM
    PRs = '( %s /\\ s e. CC )' % Z3.PR
    A = '( %s /\\ 1 < ( Re ` s ) )' % PRs
    pr_ = D(w, A, 'simpll', [], Z3.PR); sc = D(w, A, 'simplr', [], 's e. CC'); s1 = D(w, A, 'simpr', [], '1 < ( Re ` s )')
    chs = D(w, A, 'simpld', [pr_], L.CH())
    par = D(w, A, 'syl', [chs, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pp = D(w, A, 'simpld', [D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (PAR, Z3.YB))], '%s e. { 0 , 1 }' % PAR)
    ec = eps_cl(w, A, chs, pp)
    IMY = L.IMAP(CYM); XV = L.XV_; GLM = L.GLM; ILB = L.ILB; PT = L.PT; DP = L.DP
    IL = Z3.IL(CYM, 's')
    ilm = D(w, A, 'id' if False else 'idi', [], '') if False else w.s([], 'zl3ilm', '( %s -> %s ~~>r %s )' % (A, IMY, XV))
    ilc = w.s([], 'zl3ilc', '( %s -> ( ( %s : RR+ --> CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A, IMY, ILB, GLM, DP))
    c1 = D(w, A, 'simpld', [ilc], '( %s : RR+ --> CC /\\ %s e. CC )' % (IMY, ILB)); c2 = D(w, A, 'simprd', [ilc], '( %s e. CC /\\ %s e. CC )' % (GLM, DP))
    fY = D(w, A, 'simpld', [c1], '%s : RR+ --> CC' % IMY); ilbc = D(w, A, 'simprd', [c1], '%s e. CC' % ILB)
    glc = D(w, A, 'simpld', [c2], '%s e. CC' % GLM); dpc = D(w, A, 'simprd', [c2], '%s e. CC' % DP)
    sup = cst(w, A, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    dm = D(w, A, 'syl2anc', [cst(w, A, 'rlimrel', 'Rel ~~>r'), ilm, w.inst('releldm')], '%s e. dom ~~>r' % IMY)
    rd = D(w, A, 'mpbid', [dm, D(w, A, 'rlimdm', [fY, sup], '( %s e. dom ~~>r <-> %s ~~>r %s )' % (IMY, IMY, IL))], '%s ~~>r %s' % (IMY, IL))
    ilx = D(w, A, 'rlimuni', [fY, sup, rd, ilm], '%s = %s' % (IL, XV))
    xvc = D(w, A, 'syl', [ilm, w.inst('rlimcl')], '%s e. CC' % XV)
    ilcc = D(w, A, 'eqeltrd', [ilx, xvc], '%s e. CC' % IL)
    rmc = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'ifcli', '%s e. CC' % RM)], 'a1i', '( %s -> %s e. CC )' % (A, RM))
    two = cst(w, A, '2cn', '2 e. CC'); t0 = cst(w, A, '2ne0', '2 =/= 0')
    R2 = '( %s / 2 )' % RM
    r2c = D(w, A, 'divcld', [rmc, two, t0], '%s e. CC' % R2)
    ptc = D(w, A, 'mulcld', [r2c, dpc], '%s e. CC' % PT)
    EI = '( %s x. %s )' % (EPS, ILB)
    eic = D(w, A, 'mulcld', [ec, ilbc], '%s e. CC' % EI)
    Z_ = '( %s + %s )' % (EI, PT)
    zc = D(w, A, 'addcld', [eic, ptc], '%s e. CC' % Z_)
    # s is neither 0 nor 1
    rsr = D(w, A, 'recld', [sc], '( Re ` s ) e. RR')
    rs0 = D(w, A, 'gt0ne0d', [D(w, A, 'lttrd', [cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), rsr, cst(w, A, '0lt1', '0 < 1'), s1], '0 < ( Re ` s )')], '( Re ` s ) =/= 0')
    sz = w.s([w.s([], 'fveq2', '( s = 0 -> ( Re ` s ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( s = 0 -> ( Re ` s ) = 0 )')
    sne0 = D(w, A, 'mpd', [rs0, D(w, A, 'necon3d', [w.s([sz], 'a1i', '( %s -> ( s = 0 -> ( Re ` s ) = 0 ) )' % A)], '( ( Re ` s ) =/= 0 -> s =/= 0 )')], 's =/= 0')
    so = w.s([w.s([], 'fveq2', '( s = 1 -> ( Re ` s ) = ( Re ` 1 ) )'), w.s([], 're1', '( Re ` 1 ) = 1')], 'eqtrdi', '( s = 1 -> ( Re ` s ) = 1 )')
    rs1 = D(w, A, 'necomd', [D(w, A, 'ltned', [cst(w, A, '1re', '1 e. RR'), s1], '1 =/= ( Re ` s )')], '( Re ` s ) =/= 1')
    sne1 = D(w, A, 'mpd', [rs1, D(w, A, 'necon3d', [w.s([so], 'a1i', '( %s -> ( s = 1 -> ( Re ` s ) = 1 ) )' % A)], '( ( Re ` s ) =/= 1 -> s =/= 1 )')], 's =/= 1')
    one = cst(w, A, 'ax-1cn', '1 e. CC')
    PPZ = '( ( 1 / s ) + ( 1 / ( 1 - s ) ) )'
    omn = D(w, A, 'subne0d', [one, sc, D(w, A, 'necomd', [sne1], '1 =/= s')], '( 1 - s ) =/= 0')
    ppc = D(w, A, 'addcld', [D(w, A, 'reccld', [sc, sne0], '( 1 / s ) e. CC'), D(w, A, 'reccld', [D(w, A, 'subcld', [one, sc], '( 1 - s ) e. CC'), omn], '( 1 / ( 1 - s ) ) e. CC')], '%s e. CC' % PPZ)
    RP = '( %s x. %s )' % (RM, PPZ)
    KEY = '%s = -u %s' % (PT, RP)
    # case M = 1
    A1 = '( %s /\\ M = 1 )' % A
    m1 = D(w, A1, 'syl2anc', [ad(w, A1, pr_, Z3.PR), w.s([], 'simpr', '( %s -> M = 1 )' % A1), w.inst('zl3m1')], '( %s = 0 /\\ %s = 1 )' % (PAR, EPS))
    rm1 = D(w, A1, 'syl', [w.s([], 'simpr', '( %s -> M = 1 )' % A1), w.s([], 'iftrue', '( M = 1 -> %s = 1 )' % RM)], '%s = 1' % RM)
    W0 = '( ( s + 0 ) / 2 )'
    weq = D(w, A1, 'oveq1d', [D(w, A1, 'oveq2d', [D(w, A1, 'simpld', [m1], '%s = 0' % PAR)], '( s + %s ) = ( s + 0 )' % PAR)], '%s = %s' % (Wm, W0))
    D0 = '( ( 1 / ( %s - ( 1 / 2 ) ) ) - ( 1 / %s ) )' % (W0, W0)
    dpe = D(w, A1, 'oveq12d', [D(w, A1, 'oveq2d', [D(w, A1, 'oveq1d', [weq], '( %s - ( 1 / 2 ) ) = ( %s - ( 1 / 2 ) )' % (Wm, W0))], '( 1 / ( %s - ( 1 / 2 ) ) ) = ( 1 / ( %s - ( 1 / 2 ) ) )' % (Wm, W0)),
                                D(w, A1, 'oveq2d', [weq], '( 1 / %s ) = ( 1 / %s )' % (Wm, W0))], '%s = %s' % (DP, D0))
    ppa = D(w, A1, 'syl3anc', [ad(w, A1, sc, 's e. CC'), ad(w, A1, sne0, 's =/= 0'), ad(w, A1, sne1, 's =/= 1'), w.inst('zl3ppa')], '%s = -u ( 2 x. %s )' % (D0, PPZ))
    ppc1 = ad(w, A1, ppc, '%s e. CC' % PPZ)
    tpc = D(w, A1, 'mulcld', [cst(w, A1, '2cn', '2 e. CC'), ppc1], '( 2 x. %s ) e. CC' % PPZ)
    half2 = chain(w, A1, ['( ( 1 / 2 ) x. ( 2 x. %s ) )' % PPZ, '( ( ( 1 / 2 ) x. 2 ) x. %s )' % PPZ, '( 1 x. %s )' % PPZ, PPZ],
                  [('r', D(w, A1, 'mulassd', [cst(w, A1, 'halfcn', '( 1 / 2 ) e. CC'), cst(w, A1, '2cn', '2 e. CC'), ppc1], '( ( ( 1 / 2 ) x. 2 ) x. %s ) = ( ( 1 / 2 ) x. ( 2 x. %s ) )' % (PPZ, PPZ))),
                   D(w, A1, 'oveq1d', [D(w, A1, 'eqtrd', [D(w, A1, 'mulcomd', [cst(w, A1, 'halfcn', '( 1 / 2 ) e. CC'), cst(w, A1, '2cn', '2 e. CC')], '( ( 1 / 2 ) x. 2 ) = ( 2 x. ( 1 / 2 ) )'),
                                                          D(w, A1, 'divcan2d', [cst(w, A1, 'ax-1cn', '1 e. CC'), cst(w, A1, '2cn', '2 e. CC'), cst(w, A1, '2ne0', '2 =/= 0')], '( 2 x. ( 1 / 2 ) ) = 1')], '( ( 1 / 2 ) x. 2 ) = 1')],
                     '( ( ( 1 / 2 ) x. 2 ) x. %s ) = ( 1 x. %s )' % (PPZ, PPZ)),
                   D(w, A1, 'mullidd', [ppc1], '( 1 x. %s ) = %s' % (PPZ, PPZ))])
    k1l = chain(w, A1, [PT, '( ( 1 / 2 ) x. -u ( 2 x. %s ) )' % PPZ, '-u ( ( 1 / 2 ) x. ( 2 x. %s ) )' % PPZ, '-u %s' % PPZ],
                [D(w, A1, 'oveq12d', [D(w, A1, 'oveq1d', [rm1], '%s = ( 1 / 2 )' % R2), D(w, A1, 'eqtrd', [dpe, ppa], '%s = -u ( 2 x. %s )' % (DP, PPZ))], '%s = ( ( 1 / 2 ) x. -u ( 2 x. %s ) )' % (PT, PPZ)),
                 D(w, A1, 'mulneg2d', [cst(w, A1, 'halfcn', '( 1 / 2 ) e. CC'), tpc], '( ( 1 / 2 ) x. -u ( 2 x. %s ) ) = -u ( ( 1 / 2 ) x. ( 2 x. %s ) )' % (PPZ, PPZ)),
                 D(w, A1, 'negeqd', [half2], '-u ( ( 1 / 2 ) x. ( 2 x. %s ) ) = -u %s' % (PPZ, PPZ))])
    k1r = D(w, A1, 'negeqd', [D(w, A1, 'eqtrd', [D(w, A1, 'oveq1d', [rm1], '%s = ( 1 x. %s )' % (RP, PPZ)), D(w, A1, 'mullidd', [ppc1], '( 1 x. %s ) = %s' % (PPZ, PPZ))], '%s = %s' % (RP, PPZ))],
            '-u %s = -u %s' % (RP, PPZ))
    k1 = D(w, A1, 'eqtr4d', [k1l, k1r], KEY)
    # case M =/= 1
    A2 = '( %s /\\ M =/= 1 )' % A
    rm0 = D(w, A2, 'syl', [D(w, A2, 'neneqd', [w.s([], 'simpr', '( %s -> M =/= 1 )' % A2)], '-. M = 1'), w.s([], 'iffalse', '( -. M = 1 -> %s = 0 )' % RM)], '%s = 0' % RM)
    k2l = chain(w, A2, [PT, '( ( 0 / 2 ) x. %s )' % DP, '( 0 x. %s )' % DP, '0'],
                [D(w, A2, 'oveq1d', [D(w, A2, 'oveq1d', [rm0], '%s = ( 0 / 2 )' % R2)], '%s = ( ( 0 / 2 ) x. %s )' % (PT, DP)),
                 D(w, A2, 'oveq1d', [D(w, A2, 'div0d', [cst(w, A2, '2cn', '2 e. CC'), cst(w, A2, '2ne0', '2 =/= 0')], '( 0 / 2 ) = 0')], '( ( 0 / 2 ) x. %s ) = ( 0 x. %s )' % (DP, DP)),
                 D(w, A2, 'mul02d', [ad(w, A2, dpc, '%s e. CC' % DP)], '( 0 x. %s ) = 0' % DP)])
    k2r = chain(w, A2, ['-u %s' % RP, '-u ( 0 x. %s )' % PPZ, '-u 0', '0'],
                [D(w, A2, 'negeqd', [D(w, A2, 'oveq1d', [rm0], '%s = ( 0 x. %s )' % (RP, PPZ))], '-u %s = -u ( 0 x. %s )' % (RP, PPZ)),
                 D(w, A2, 'negeqd', [D(w, A2, 'mul02d', [ad(w, A2, ppc, '%s e. CC' % PPZ)], '( 0 x. %s ) = 0' % PPZ)], '-u ( 0 x. %s ) = -u 0' % PPZ),
                 cst(w, A2, 'neg0', '-u 0 = 0')])
    k2 = D(w, A2, 'eqtr4d', [k2l, k2r], KEY)
    key = D(w, A, 'pm2.61dane', [k1, k2], KEY)
    rpc = D(w, A, 'mulcld', [rmc, ppc], '%s e. CC' % RP)
    fin = chain(w, A, [GLM, '( ( %s - %s ) + %s )' % (GLM, Z_, Z_), '( %s + %s )' % (IL, Z_), '( %s + ( %s + -u %s ) )' % (IL, EI, RP), '( ( %s + %s ) + -u %s )' % (IL, EI, RP), '( ( %s + %s ) - %s )' % (IL, EI, RP)],
                [('r', D(w, A, 'npcand', [glc, zc], '( ( %s - %s ) + %s ) = %s' % (GLM, Z_, Z_, GLM))),
                 D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [ilx], '%s = %s' % (XV, IL))], '( ( %s - %s ) + %s ) = ( %s + %s )' % (GLM, Z_, Z_, IL, Z_)),
                 D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [key], '%s = ( %s + -u %s )' % (Z_, EI, RP))], '( %s + %s ) = ( %s + ( %s + -u %s ) )' % (IL, Z_, IL, EI, RP)),
                 ('r', D(w, A, 'addassd', [ilcc, eic, D(w, A, 'negcld', [rpc], '-u %s e. CC' % RP)], '( ( %s + %s ) + -u %s ) = ( %s + ( %s + -u %s ) )' % (IL, EI, RP, IL, EI, RP))),
                 D(w, A, 'negsubd', [D(w, A, 'addcld', [ilcc, eic], '( %s + %s ) e. CC' % (IL, EI)), rpc], '( ( %s + %s ) + -u %s ) = ( ( %s + %s ) - %s )' % (IL, EI, RP, IL, EI, RP))])
    concl = L.split_imp(S['zl3mel'])[1]
    body = concl[concl.index('( 1 < ( Re ` s ) ->'):]
    exs = D(w, PRs, 'ex', [fin], body)
    w.qed([D(w, Z3.PR, 'ralrimiva', [exs], concl)], 'idi', S['zl3mel'])
    go(w)
