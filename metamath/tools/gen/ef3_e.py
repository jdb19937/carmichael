"""Sortie EF3: the weighted mass of a square (ef3zw), the window integrals (ef3adj), the harmonic sum of the window
centres (ef3hm), and the weight lemma (ef3wt: Lean weight_sum_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
from c10_f import crfacts
import lin
lin.FASTPATH = True
import ef3_a, ef3_c


def gen_zw():
    w = W('ef3zw', 'The weighted mass ` sum m_q / ( 1 + abs Im q ) ` of zeros in the square about ` 2 + i T ` is at most ` 2400 log ( A ( abs T + 2 ) ) / ( 1 + abs T ) ` (Lean ` exists_good_sigma ` , ` hW ` ).')
    A0, G = ante_of(S['ef3zw'])
    s = St(w, A0)
    dt = s([], 'simpl', '( %s /\\ T e. RR )' % DD())
    dd, tr = conj_split(w, A0, dt)
    gs = s([], 'simpr', 'G C_ %s' % ZS('F', 'T'))
    zs = s([dt, w.inst('ef2zs')], 'syl', ante_of(stmt('ef2zs'))[1])
    zf, zo, _ = conj_split(w, A0, zs)
    gf = s([zf, gs], 'ssfid', 'G e. Fin')
    mass = s([s([dt, gs], 'jca', ante_of(stmt('ef2zss'))[0]), w.inst('ef2zss')], 'syl', ante_of(stmt('ef2zss'))[1])
    tc = s([tr], 'recnd', 'T e. CC')
    at = s([tc], 'abscld', '( abs ` T ) e. RR')
    b = '( 1 + ( abs ` T ) )'
    bp = s([s([numst(w, A0, '1', 'RR'), at], 'readdcld', '%s e. RR' % b), lin8(w, A0, [s([tc], 'absge0d', '0 <_ ( abs ` T )')], '0 < %s' % b, {'( abs ` T )': at})], 'elrpd', '%s e. RR+' % b)
    A1 = '( %s /\\ q e. G )' % A0
    s1 = St(w, A1)
    L1 = lambda st: lift(w, st, A1)
    qg = s1([], 'simpr', 'q e. G')
    qz = s1([L1(gs), qg], 'sseldd', 'q e. %s' % ZS('F', 'T'))
    reb = s1([s1([L1(tr), qz], 'jca', '( T e. RR /\\ q e. %s )' % ZS('F', 'T')), w.inst('ef2reb')], 'syl', tsub(ante_of(stmt('ef2reb'))[1], {'P': 'q'}))
    _, _, imb = conj_split(w, A1, reb)
    mn = s1([L1(zo), qz, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    mr = s1([mn], 'nnred', '( F holord q ) e. RR')
    m0 = s1([mr, lin8(w, A1, [s1([mn], 'nnge1d', '1 <_ ( F holord q )')], '0 <_ ( F holord q )', {'( F holord q )': mr})], 'id', '0 <_ ( F holord q )') if False else \
        lin8(w, A1, [s1([mn], 'nnge1d', '1 <_ ( F holord q )')], '0 <_ ( F holord q )', {'( F holord q )': mr})
    qc = s1([s1([s1([L1(tr), qz], 'jca', '( T e. RR /\\ q e. %s )' % ZS('F', 'T'))], 'id', '( T e. RR /\\ q e. %s )' % ZS('F', 'T')) if False else
             s1([L1(zf), qz], 'id', 'x') if False else None], 'id', 'x') if False else None
    z = zs_unpack(w, A1, 'F', 'T', L1(tr), 'q', qz)
    qc = z['cc']
    iq = s1([qc], 'imcld', '( Im ` q ) e. RR')
    aiq = s1([s1([iq], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    a = '( 1 + ( abs ` ( Im ` q ) ) )'
    ap = s1([s1([numst(w, A1, '1', 'RR'), aiq], 'readdcld', '%s e. RR' % a), lin8(w, A1, [s1([s1([iq], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < %s' % a, {'( abs ` ( Im ` q ) )': aiq})], 'elrpd', '%s e. RR+' % a)
    d1 = s1([L1(tc), s1([iq], 'recnd', '( Im ` q ) e. CC')], 'abs2difd', '( ( abs ` T ) - ( abs ` ( Im ` q ) ) ) <_ ( abs ` ( T - ( Im ` q ) ) )')
    d2 = s1([L1(tc), s1([iq], 'recnd', '( Im ` q ) e. CC')], 'abssubd', '( abs ` ( T - ( Im ` q ) ) ) = ( abs ` ( ( Im ` q ) - T ) )')
    dtq = s1([s1([L1(tc), s1([iq], 'recnd', '( Im ` q ) e. CC')], 'subcld', '( T - ( Im ` q ) ) e. CC')], 'abscld', '( abs ` ( T - ( Im ` q ) ) ) e. RR')
    lvq = {'( abs ` T )': L1(at), '( abs ` ( Im ` q ) )': aiq, '( abs ` ( T - ( Im ` q ) ) )': dtq,
           '( abs ` ( ( Im ` q ) - T ) )': s1([s1([s1([iq], 'recnd', '( Im ` q ) e. CC'), L1(tc)], 'subcld', '( ( Im ` q ) - T ) e. CC')], 'abscld', '( abs ` ( ( Im ` q ) - T ) ) e. RR')}
    ble = lin8(w, A1, [d1, d2, imb, s1([s1([iq], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '%s <_ ( 3 x. %s )' % (b, a), lvq)
    M3 = '( 3 x. ( F holord q ) )'
    m3r = s1([numst(w, A1, '3', 'RR'), mr], 'remulcld', '%s e. RR' % M3)
    m30 = lin8(w, A1, [m0], '0 <_ %s' % M3, {'( F holord q )': mr})
    a3p = s1([numst(w, A1, '3', 'RR+'), ap], 'rpmulcld', '( 3 x. %s ) e. RR+' % a)
    l1 = s1([L1(bp), a3p, m3r, m30, ble], 'lediv2ad', '( %s / ( 3 x. %s ) ) <_ ( %s / %s )' % (M3, a, M3, b))
    e1 = s1([s1([mr], 'recnd', '( F holord q ) e. CC'), s1([s1([ap], 'rpred', '%s e. RR' % a)], 'recnd', '%s e. CC' % a), numst(w, A1, '3', 'CC'), s1([ap], 'rpne0d', '%s =/= 0' % a),
             s1([numst(w, A1, '3', 'RR+')], 'rpne0d', '3 =/= 0')], 'divcan5d', '( %s / ( 3 x. %s ) ) = %s' % (M3, a, WQ()))
    wle = s1([e1, l1], 'eqbrtrrd', '%s <_ ( %s / %s )' % (WQ(), M3, b))
    wr = s1([mr, ap], 'rerpdivcld', '%s e. RR' % WQ())
    tr_ = s1([m3r, L1(bp)], 'rerpdivcld', '( %s / %s ) e. RR' % (M3, b))
    sle = s([gf, wr, tr_, wle], 'fsumle', 'sum_ q e. G %s <_ sum_ q e. G ( %s / %s )' % (WQ(), M3, b))
    m3c = s1([m3r], 'recnd', '%s e. CC' % M3)
    fd = s([gf, s([s([bp], 'rpred', '%s e. RR' % b)], 'recnd', '%s e. CC' % b), m3c, s([bp], 'rpne0d', '%s =/= 0' % b)], 'fsumdivc', '( sum_ q e. G %s / %s ) = sum_ q e. G ( %s / %s )' % (M3, b, M3, b))
    MS = 'sum_ q e. G ( F holord q )'
    fm = s([gf, numst(w, A0, '3', 'CC'), s1([mr], 'recnd', '( F holord q ) e. CC')], 'fsummulc2', '( 3 x. %s ) = sum_ q e. G %s' % (MS, M3))
    msr = s([gf, mr], 'fsumrecl', '%s e. RR' % MS)
    L_ = '( log ` %s )' % XA()
    x2 = s([dt, w.inst('ef2x2')], 'syl', '2 <_ %s' % XA())
    xr = s([s([s([dd, w.inst('simp2')], 'syl', '( A e. RR /\\ 1 <_ A )'), w.inst('simpl')], 'syl', 'A e. RR'), s([at, numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` T ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % XA())
    xp = s([xr, lin8(w, A0, [x2], '0 < %s' % XA(), {XA(): xr})], 'elrpd', '%s e. RR+' % XA())
    lr = s([xp], 'relogcld', '%s e. RR' % L_)
    K8 = '( ; ; 8 0 0 x. %s )' % L_
    k8r = s([numst(w, A0, '; ; 8 0 0', 'RR'), lr], 'remulcld', '%s e. RR' % K8)
    c3 = lin8(w, A0, [mass], '( 3 x. %s ) <_ ( 3 x. %s )' % (MS, K8), {MS: msr, K8: k8r})
    c4 = s([s([numst(w, A0, '3', 'RR'), msr], 'remulcld', '( 3 x. %s ) e. RR' % MS), s([numst(w, A0, '3', 'RR'), k8r], 'remulcld', '( 3 x. %s ) e. RR' % K8), bp, c3], 'lediv1dd',
            '( ( 3 x. %s ) / %s ) <_ ( ( 3 x. %s ) / %s )' % (MS, b, K8, b))
    c5 = s([s([fm], 'oveq1d', '( ( 3 x. %s ) / %s ) = ( sum_ q e. G %s / %s )' % (MS, b, M3, b)), fd], 'eqtrd', '( ( 3 x. %s ) / %s ) = sum_ q e. G ( %s / %s )' % (MS, b, M3, b))
    c6 = s([c5, c4], 'eqbrtrrd', 'sum_ q e. G ( %s / %s ) <_ ( ( 3 x. %s ) / %s )' % (M3, b, K8, b))
    cl = Closure(w, A0, {L_: ('RR', lr)}); cl.atom(L_)
    e7 = s([ringeq(w, A0, '( 3 x. %s )' % K8, '( ; ; ; 2 4 0 0 x. %s )' % L_, cl)], 'oveq1d', '( ( 3 x. %s ) / %s ) = ( ( ; ; ; 2 4 0 0 x. %s ) / %s )' % (K8, b, L_, b))
    c8 = s([sle, c6], 'letrd' if False else 'id', 'x') if False else None
    wsum = s([gf, wr], 'fsumrecl', 'sum_ q e. G %s e. RR' % WQ())
    tsum = s([gf, tr_], 'fsumrecl', 'sum_ q e. G ( %s / %s ) e. RR' % (M3, b))
    rhs = s([s([numst(w, A0, '3', 'RR'), k8r], 'remulcld', '( 3 x. %s ) e. RR' % K8), bp], 'rerpdivcld', '( ( 3 x. %s ) / %s ) e. RR' % (K8, b))
    c9 = s([wsum, tsum, rhs, sle, c6], 'letrd', 'sum_ q e. G %s <_ ( ( 3 x. %s ) / %s )' % (WQ(), K8, b))
    w.qed([c9, e7], 'breqtrd', S['ef3zw'])
    return run8(w)


TOP = '( P + ( M / 2 ) )'
IADJ = '( P (,) %s )' % TOP
HADJ = ['( ph -> P e. RR )', '( ph -> M e. NN0 )', '( ( ph /\\ l e. %s ) -> B e. CC )' % IADJ, '( ph -> ( l e. %s |-> B ) e. L^1 )' % IADJ]
S['ef3adj'] = '( ph -> S. %s B _d l = sum_ j e. ( 0 ..^ M ) S. %s B _d l )' % (IADJ, WIN())
AK = lambda k: 'S. ( P (,) ( P + ( %s / 2 ) ) ) B _d l' % k


def gen_adj():
    from c0lib import hyp
    w = W('ef3adj', 'Lean ` intervalIntegral.sum_integral_adjacent_intervals ` on the half-unit windows: the integral over ` ( P , P + M / 2 ) ` is the sum of the integrals over the windows ` ( P + j / 2 , P + j / 2 + 1 / 2 ) ` (a telescoping sum of ~ itgsplitioo ).')
    h = [hyp(w, str(i + 1), 'ef3adj.%d' % (i + 1), f) for i, f in enumerate(HADJ)]
    s = St(w, 'ph')
    pr, mn = h[0], h[1]
    mr = s([mn], 'nn0red', 'M e. RR')
    topr = s([pr, s([mr, numst(w, 'ph', '2', 'RR+')], 'rerpdivcld', '( M / 2 ) e. RR')], 'readdcld', '%s e. RR' % TOP)

    def half(A, x, xr):
        return w.s([w.s([lift(w, pr, A), w.s([xr, numst(w, A, '2', 'RR+')], 'rerpdivcld', '( %s -> ( %s / 2 ) e. RR )' % (A, x))], 'readdcld', '( %s -> ( P + ( %s / 2 ) ) e. RR )' % (A, x))], 'id', 'x') if False else \
            w.s([lift(w, pr, A), w.s([xr, numst(w, A, '2', 'RR+')], 'rerpdivcld', '( %s -> ( %s / 2 ) e. RR )' % (A, x))], 'readdcld', '( %s -> ( P + ( %s / 2 ) ) e. RR )' % (A, x))

    def piece(A, a, b, ar_, br_, ale, ble):
        """under A (one level above ph): ( A -> ( l e. ( a (,) b ) |-> B ) e. L^1 ), ( ( A /\\ l e. ( a (,) b ) ) -> B e. CC ), ( A -> S. ( a (,) b ) B _d l e. CC )"""
        sA = St(w, A)
        ss = sA([sA([sA([sA([lift(w, pr, A)], 'rexrd', 'P e. RR*'), sA([lift(w, topr, A)], 'rexrd', '%s e. RR*' % TOP)], 'jca', '( P e. RR* /\\ %s e. RR* )' % TOP),
                     sA([ale, ble], 'jca', '( P <_ %s /\\ %s <_ %s )' % (a, b, TOP))], 'jca', '( ( P e. RR* /\\ %s e. RR* ) /\\ ( P <_ %s /\\ %s <_ %s ) )' % (TOP, a, b, TOP)), w.inst('ioossioo')], 'syl',
                '( %s (,) %s ) C_ %s' % (a, b, IADJ))
        h3A = w.s([h[2]], 'adantlr', '( ( %s /\\ l e. %s ) -> B e. CC )' % (A, IADJ))
        h4A = lift(w, h[3], A)
        ib = sA([ss, sA([], 'ioombl', '( %s (,) %s ) e. dom vol' % (a, b)) if False else sA([w.s([], 'ioombl', '( %s (,) %s ) e. dom vol' % (a, b))], 'a1i', '( %s (,) %s ) e. dom vol' % (a, b)), h3A, h4A], 'iblss',
                '( l e. ( %s (,) %s ) |-> B ) e. L^1' % (a, b))
        A2 = '( %s /\\ l e. ( %s (,) %s ) )' % (A, a, b)
        lin_ = w.s([ss], 'sselda', '( %s -> l e. %s )' % (A2, IADJ))
        pt = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (A2, A)), lin_], 'jca', '( %s -> ( %s /\\ l e. %s ) )' % (A2, A, IADJ)), h3A], 'syl', '( %s -> B e. CC )' % A2)
        cc = sA([pt, ib], 'itgcl', 'S. ( %s (,) %s ) B _d l e. CC' % (a, b))
        return ib, pt, cc
    # telfsumo2 closure
    K = '( ph /\\ k e. ( 0 ... M ) )'
    sk = St(w, K)
    kin = sk([], 'simpr', 'k e. ( 0 ... M )')
    kr = sk([sk([kin, w.inst('elfznn0')], 'syl', 'k e. NN0')], 'nn0red', 'k e. RR')
    kle = sk([kin, w.inst('elfzle2')], 'syl', 'k <_ M')
    kb = half(K, 'k', kr)
    lvk = {'P': lift(w, pr, K), 'k': kr, 'M': lift(w, mr, K)}
    k0 = sk([sk([kin, w.inst('elfznn0')], 'syl', 'k e. NN0')], 'nn0ge0d', '0 <_ k')
    _, _, kcc = piece(K, 'P', '( P + ( k / 2 ) )', lift(w, pr, K), kb, lin8(w, K, [], 'P <_ P', lvk), lin8(w, K, [kle], '( P + ( k / 2 ) ) <_ %s' % TOP, lvk))
    # per window
    J = '( ph /\\ j e. ( 0 ..^ M ) )'
    sj = St(w, J)
    jin = sj([], 'simpr', 'j e. ( 0 ..^ M )')
    jn = sj([jin, w.inst('elfzonn0')], 'syl', 'j e. NN0')
    jr = sj([jn], 'nn0red', 'j e. RR')
    j1 = sj([sj([jin, w.inst('fzofzp1')], 'syl', '( j + 1 ) e. ( 0 ... M )'), w.inst('elfzle2')], 'syl', '( j + 1 ) <_ M')
    a, c = '( P + ( j / 2 ) )', '( P + ( ( j + 1 ) / 2 ) )'
    ar_ = half(J, 'j', jr)
    j1r = sj([jr, numst(w, J, '1', 'RR')], 'readdcld', '( j + 1 ) e. RR')
    cr = half(J, '( j + 1 )', j1r)
    lvj = {'P': lift(w, pr, J), 'j': jr, 'M': lift(w, mr, J)}
    j0 = sj([jn], 'nn0ge0d', '0 <_ j')
    pa = lin8(w, J, [j0], 'P <_ %s' % a, lvj); ac = lin8(w, J, [], '%s <_ %s' % (a, c), lvj); ctop = lin8(w, J, [j1], '%s <_ %s' % (c, TOP), lvj)
    ib1, _, c1 = piece(J, 'P', a, lift(w, pr, J), ar_, lin8(w, J, [], 'P <_ P', lvj), lin8(w, J, [ac, ctop], '%s <_ %s' % (a, TOP), lvj))
    ib2, _, c2 = piece(J, a, c, ar_, cr, pa, ctop)
    _, pt3, _ = piece(J, 'P', c, lift(w, pr, J), cr, lin8(w, J, [], 'P <_ P', lvj), ctop)
    from ef3_a import icc_mem
    ain = icc_mem(w, J, a, 'P', c, ar_, lift(w, pr, J), cr, pa, ac)
    sp = sj([lift(w, pr, J), cr, ain, pt3, ib1, ib2], 'itgsplitioo', 'S. ( P (,) %s ) B _d l = ( S. ( P (,) %s ) B _d l + S. ( %s (,) %s ) B _d l )' % (c, a, a, c))
    d1 = sj([sp], 'oveq1d', '( S. ( P (,) %s ) B _d l - S. ( P (,) %s ) B _d l ) = ( ( S. ( P (,) %s ) B _d l + S. ( %s (,) %s ) B _d l ) - S. ( P (,) %s ) B _d l )' % (c, a, a, a, c, a))
    d2 = sj([c1, c2], 'pncan2d', '( ( S. ( P (,) %s ) B _d l + S. ( %s (,) %s ) B _d l ) - S. ( P (,) %s ) B _d l ) = S. ( %s (,) %s ) B _d l' % (a, a, c, a, a, c))
    ce = lin.lineq(w, J, c, '( %s + ( 1 / 2 ) )' % a, [], closure=Closure(w, J, {'P': ('RR', lift(w, pr, J)), 'j': ('RR', jr)}))
    ie = sj([sj([ce], 'oveq2d', '( %s (,) %s ) = %s' % (a, c, WIN())), w.inst('itgeq1')], 'syl', 'S. ( %s (,) %s ) B _d l = S. %s B _d l' % (a, c, WIN()))
    pw = sj([sj([d1, d2], 'eqtrd', '( %s - %s ) = S. ( %s (,) %s ) B _d l' % (AK('( j + 1 )'), AK('j'), a, c)), ie], 'eqtrd', '( %s - %s ) = S. %s B _d l' % (AK('( j + 1 )'), AK('j'), WIN()))
    se = s([sj([pw], 'eqcomd', 'S. %s B _d l = ( %s - %s )' % (WIN(), AK('( j + 1 )'), AK('j')))], 'sumeq2dv', 'sum_ j e. ( 0 ..^ M ) S. %s B _d l = sum_ j e. ( 0 ..^ M ) ( %s - %s )' % (WIN(), AK('( j + 1 )'), AK('j')))
    def cgk(val):
        e1 = w.s([], 'oveq1', '( k = %s -> ( k / 2 ) = ( %s / 2 ) )' % (val, val))
        e2 = w.s([e1], 'oveq2d', '( k = %s -> ( P + ( k / 2 ) ) = ( P + ( %s / 2 ) ) )' % (val, val))
        e3 = w.s([e2], 'oveq2d', '( k = %s -> ( P (,) ( P + ( k / 2 ) ) ) = ( P (,) ( P + ( %s / 2 ) ) ) )' % (val, val))
        return w.s([e3, w.inst('itgeq1')], 'syl', '( k = %s -> %s = %s )' % (val, AK('k'), AK(val)))
    muz = s([mn, w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi' if False else 'id', 'x') if False else s([s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', 'NN0 = ( ZZ>= ` 0 )'), mn], 'eleqtrrd', 'M e. ( ZZ>= ` 0 )') if False else s([mn, s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrd', 'M e. ( ZZ>= ` 0 )')
    tel = s([cgk('j'), cgk('( j + 1 )'), cgk('0'), cgk('M'), muz, kcc], 'telfsumo2', 'sum_ j e. ( 0 ..^ M ) ( %s - %s ) = ( %s - %s )' % (AK('( j + 1 )'), AK('j'), AK('M'), AK('0')))
    # A ( 0 ) = 0
    z1 = s([s([s([s([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC'), s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')], 'div0d' if False else 'jca', '( 2 e. CC /\\ 2 =/= 0 )'), w.inst('div0')], 'syl', '( 0 / 2 ) = 0')], 'oveq2d', '( P + ( 0 / 2 ) ) = ( P + 0 )')
    z2 = s([z1, s([s([pr], 'recnd', 'P e. CC'), w.inst('addrid')], 'syl', '( P + 0 ) = P')], 'eqtrd', '( P + ( 0 / 2 ) ) = P')
    z3 = s([s([z2], 'oveq2d', '( P (,) ( P + ( 0 / 2 ) ) ) = ( P (,) P )'), s([w.s([], 'iooid', '( P (,) P ) = (/)')], 'a1i', '( P (,) P ) = (/)')], 'eqtrd', '( P (,) ( P + ( 0 / 2 ) ) ) = (/)')
    z4 = s([s([z3, w.inst('itgeq1')], 'syl', '%s = S. (/) B _d l' % AK('0')), s([w.s([], 'itg0', 'S. (/) B _d l = 0')], 'a1i', 'S. (/) B _d l = 0')], 'eqtrd', '%s = 0' % AK('0'))
    t2 = s([tel, s([z4], 'oveq2d', '( %s - %s ) = ( %s - 0 )' % (AK('M'), AK('0'), AK('M')))], 'eqtrd', 'sum_ j e. ( 0 ..^ M ) ( %s - %s ) = ( %s - 0 )' % (AK('( j + 1 )'), AK('j'), AK('M')))
    mcc = piece('( ph /\\ M e. NN0 )', 'P', TOP, None, None, None, None) if False else None
    ibM = h[3]
    amc = s([h[2], ibM], 'itgcl', 'S. %s B _d l e. CC' % IADJ)
    t3 = s([t2, s([amc], 'subid1d', '( %s - 0 ) = %s' % (AK('M'), AK('M')))], 'eqtrd', 'sum_ j e. ( 0 ..^ M ) ( %s - %s ) = %s' % (AK('( j + 1 )'), AK('j'), AK('M')))
    w.qed([s([se, t3], 'eqtrd', 'sum_ j e. ( 0 ..^ M ) S. %s B _d l = %s' % (WIN(), AK('M')))], 'eqcomd', S['ef3adj'])
    return run8(w)




G_ = '( 1 / ( 1 + ( abs ` t ) ) )'


def gen_hm():
    from ef3_a import icc_mem
    w = W('ef3hm', 'Lean ` exists_good_sigma ` , ` hharm ` : the harmonic sum of the window centres ` P + j / 2 + 1 / 4 ` over ` j < M ` is at most ` 5 log ( 1 + W ) ` when ` [ P , P + M / 2 ] ` contains 0 and lies in ` [ - W , W ] ` (window integrals of ` 1 / ( 1 + abs t ) ` ).')
    A0, G = ante_of(S['ef3hm'])
    s = St(w, A0)
    H1, H2 = top_and(A0)
    h1 = s([], 'simpl', H1); h2 = s([], 'simpr', H2)
    pr, mn, wr = conj_split(w, A0, h1)
    o1, o2 = conj_split(w, A0, h2)
    p0, m0 = conj_split(w, A0, o1); wp, mw = conj_split(w, A0, o2)
    mr = s([mn], 'nn0red', 'M e. RR')
    topr = s([pr, s([mr, numst(w, A0, '2', 'RR+')], 'rerpdivcld', '( M / 2 ) e. RR')], 'readdcld', '%s e. RR' % TOP)
    ibA = s([pr, topr, w.inst('ef1iac')], 'syl2anc', '( t e. %s |-> %s ) e. L^1' % (IADJ, G_))
    def gpt(A, tin, I):
        """( A -> G_ e. RR ) and ( A -> 0 < ( 1 + abs t ) ) from tin : ( A -> t e. I ) (I an open interval of reals)"""
        sA = St(w, A)
        tr = sA([sA([], 'ioossre', '%s C_ RR' % I) if False else sA([w.s([], 'ioossre', '%s C_ RR' % I)], 'a1i', '%s C_ RR' % I), tin], 'sseldd', 't e. RR')
        at = sA([sA([tr], 'recnd', 't e. CC')], 'abscld', '( abs ` t ) e. RR')
        ap = sA([sA([numst(w, A, '1', 'RR'), at], 'readdcld', '( 1 + ( abs ` t ) ) e. RR'), lin8(w, A, [sA([sA([tr], 'recnd', 't e. CC')], 'absge0d', '0 <_ ( abs ` t )')], '0 < ( 1 + ( abs ` t ) )', {'( abs ` t )': at})], 'elrpd', '( 1 + ( abs ` t ) ) e. RR+')
        return sA([ap], 'rpreccld', '%s e. RR+' % G_), tr, at, ap
    Aa = '( %s /\\ t e. %s )' % (A0, IADJ)
    gA, _, _, _ = gpt(Aa, St(w, Aa)([], 'simpr', 't e. %s' % IADJ), IADJ)
    gAc = St(w, Aa)([St(w, Aa)([gA], 'rpred', '%s e. RR' % G_)], 'recnd', '%s e. CC' % G_)
    adj = s([pr, mn, gAc, ibA], 'ef3adj', tsub(S['ef3adj'], {'ph': A0, 'l': 't', 'B': G_}).split(' -> ', 1)[1][:-2])
    ial = s([s([s([pr, topr, wr], '3jca', '( P e. RR /\\ %s e. RR /\\ W e. RR )' % TOP), s([s([p0, m0], 'jca', '( P <_ 0 /\\ 0 <_ %s )' % TOP), s([wp, mw], 'jca', '( -u W <_ P /\\ %s <_ W )' % TOP)], 'jca',
                                                                                              '( ( P <_ 0 /\\ 0 <_ %s ) /\\ ( -u W <_ P /\\ %s <_ W ) )' % (TOP, TOP))], 'jca',
                 '( ( P e. RR /\\ %s e. RR /\\ W e. RR ) /\\ ( ( P <_ 0 /\\ 0 <_ %s ) /\\ ( -u W <_ P /\\ %s <_ W ) ) )' % (TOP, TOP, TOP)), w.inst('ef1ial')], 'syl',
            'S. %s %s _d t <_ ( 2 x. ( log ` ( 1 + W ) ) )' % (IADJ, G_))
    # per window
    J = '( %s /\\ j e. ( 0 ..^ M ) )' % A0
    sj = St(w, J)
    jr = sj([sj([sj([], 'simpr', 'j e. ( 0 ..^ M )'), w.inst('elfzonn0')], 'syl', 'j e. NN0')], 'nn0red', 'j e. RR')
    a = WLO()
    ar_ = sj([lift(w, pr, J), sj([jr, numst(w, J, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '%s e. RR' % a)
    a2 = sj([ar_, numst(w, J, '( 1 / 2 )', 'RR')], 'readdcld', '( %s + ( 1 / 2 ) ) e. RR' % a)
    t0 = T0()
    t0r = sj([ar_, numst(w, J, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % t0)
    at0 = sj([sj([t0r], 'recnd', '%s e. CC' % t0)], 'abscld', '( abs ` %s ) e. RR' % t0)
    b = '( 1 + ( abs ` %s ) )' % t0
    bp = sj([sj([numst(w, J, '1', 'RR'), at0], 'readdcld', '%s e. RR' % b), lin8(w, J, [sj([sj([t0r], 'recnd', '%s e. CC' % t0)], 'absge0d', '0 <_ ( abs ` %s )' % t0)], '0 < %s' % b, {'( abs ` %s )' % t0: at0})], 'elrpd', '%s e. RR+' % b)
    X = '( 1 / %s )' % b
    xr = sj([bp], 'rpreccld', '%s e. RR+' % X)
    K = '( ( 4 / 5 ) x. %s )' % X
    kr = sj([numst(w, J, '( 4 / 5 )', 'RR'), sj([xr], 'rpred', '%s e. RR' % X)], 'remulcld', '%s e. RR' % K)
    B54 = '( ( 5 / 4 ) x. %s )' % b
    b54 = sj([numst(w, J, '( 5 / 4 )', 'RR+'), bp], 'rpmulcld', '%s e. RR+' % B54)
    # K = 1 / ( ( 5 / 4 ) b )
    bc = sj([sj([bp], 'rpred', '%s e. RR' % b)], 'recnd', '%s e. CC' % b)
    k1 = sj([numst(w, J, '1', 'CC'), numst(w, J, '( 5 / 4 )', 'CC'), bc, sj([numst(w, J, '( 5 / 4 )', 'RR+')], 'rpne0d', '( 5 / 4 ) =/= 0'), sj([bp], 'rpne0d', '%s =/= 0' % b)], 'divdiv1d',
            '( ( 1 / ( 5 / 4 ) ) / %s ) = ( 1 / %s )' % (b, B54))
    rd = w.s([w.s([w.s([w.s([], '5cn', '5 e. CC'), w.s([w.s([], '5re', '5 e. RR'), w.s([], '5pos', '0 < 5')], 'gt0ne0ii', '5 =/= 0')], 'pm3.2i', '( 5 e. CC /\\ 5 =/= 0 )'),
                    w.s([w.s([], '4cn', '4 e. CC'), w.s([], '4ne0', '4 =/= 0')], 'pm3.2i', '( 4 e. CC /\\ 4 =/= 0 )')], 'pm3.2i', '( ( 5 e. CC /\\ 5 =/= 0 ) /\\ ( 4 e. CC /\\ 4 =/= 0 ) )'), w.inst('recdiv')], 'ax-mp', '( 1 / ( 5 / 4 ) ) = ( 4 / 5 )')
    k2 = sj([sj([rd], 'a1i', '( 1 / ( 5 / 4 ) ) = ( 4 / 5 )')], 'oveq1d', '( ( 1 / ( 5 / 4 ) ) / %s ) = ( ( 4 / 5 ) / %s )' % (b, b))
    k3 = sj([numst(w, J, '( 4 / 5 )', 'CC'), bc, sj([bp], 'rpne0d', '%s =/= 0' % b)], 'divrecd', '( ( 4 / 5 ) / %s ) = %s' % (b, K))
    keq = sj([sj([k1], 'eqcomd', '( 1 / %s ) = ( ( 1 / ( 5 / 4 ) ) / %s )' % (B54, b)), sj([k2, k3], 'eqtrd', '( ( 1 / ( 5 / 4 ) ) / %s ) = %s' % (b, K))], 'eqtrd', '( 1 / %s ) = %s' % (B54, K))
    # pointwise K <_ G_ on the window
    Jt = '( %s /\\ t e. %s )' % (J, WIN())
    st_ = St(w, Jt)
    Lt = lambda x: lift(w, x, Jt)
    tin = st_([], 'simpr', 't e. %s' % WIN())
    gW, tr, at, ap = gpt(Jt, tin, WIN())
    tb = st_([tin, w.inst('eliooord')], 'syl', '( %s < t /\\ t < ( %s + ( 1 / 2 ) ) )' % (a, a))
    tlo, thi = conj_split(w, Jt, tb)
    d1 = st_([st_([tr], 'recnd', 't e. CC'), st_([Lt(t0r)], 'recnd', '%s e. CC' % t0)], 'abs2difd', '( ( abs ` t ) - ( abs ` %s ) ) <_ ( abs ` ( t - %s ) )' % (t0, t0))
    dr = st_([st_([tr, Lt(t0r)], 'resubcld', '( t - %s ) e. RR' % t0)], 'id', 'x') if False else st_([tr, Lt(t0r)], 'resubcld', '( t - %s ) e. RR' % t0)
    lvt = {'t': tr, a: Lt(ar_), '( abs ` t )': at, '( abs ` %s )' % t0: Lt(at0)}
    lvt['( abs ` ( t - %s ) )' % t0] = st_([st_([dr], 'recnd', '( t - %s ) e. CC' % t0)], 'abscld', '( abs ` ( t - %s ) ) e. RR' % t0)
    ab = st_([st_([lin8(w, Jt, [tlo, thi], '-u ( 1 / 4 ) <_ ( t - %s )' % t0, lvt), lin8(w, Jt, [tlo, thi], '( t - %s ) <_ ( 1 / 4 )' % t0, lvt)], 'jca', '( -u ( 1 / 4 ) <_ ( t - %s ) /\\ ( t - %s ) <_ ( 1 / 4 ) )' % (t0, t0)),
              st_([dr, numst(w, Jt, '( 1 / 4 )', 'RR')], 'absled', '( ( abs ` ( t - %s ) ) <_ ( 1 / 4 ) <-> ( -u ( 1 / 4 ) <_ ( t - %s ) /\\ ( t - %s ) <_ ( 1 / 4 ) ) )' % (t0, t0, t0))], 'mpbird', '( abs ` ( t - %s ) ) <_ ( 1 / 4 )' % t0)
    ale = lin8(w, Jt, [d1, ab, st_([st_([Lt(t0r)], 'recnd', '%s e. CC' % t0)], 'absge0d', '0 <_ ( abs ` %s )' % t0)], '( 1 + ( abs ` t ) ) <_ %s' % B54, lvt)
    rec = st_([ap, Lt(b54), numst(w, Jt, '1', 'RR'), lin8(w, Jt, [], '0 <_ 1', {}), ale], 'lediv2ad', '( 1 / %s ) <_ %s' % (B54, G_))
    kle = st_([Lt(keq), rec], 'eqbrtrrd', '%s <_ %s' % (K, G_))
    ibK = sj([sj([w.s([], 'ioombl', '%s e. dom vol' % WIN())], 'a1i', '%s e. dom vol' % WIN()), sj([sj([ar_, a2, lin8(w, J, [], '%s <_ ( %s + ( 1 / 2 ) )' % (a, a), {a: ar_}), w.inst('volioo')], 'syl3anc', '( vol ` %s ) = ( ( %s + ( 1 / 2 ) ) - %s )' % (WIN(), a, a)),
                                                                                                                                         sj([sj([ar_, a2], 'resubcld', '( ( %s + ( 1 / 2 ) ) - %s ) e. RR' % (a, a))], 'id', 'x')], 'id', 'x') if False else None,
                 sj([kr], 'recnd', '%s e. CC' % K)], 'id', 'x') if False else None
    vol = sj([ar_, a2, lin8(w, J, [], '%s <_ ( %s + ( 1 / 2 ) )' % (a, a), {a: ar_}), w.inst('volioo')], 'syl3anc', '( vol ` %s ) = ( ( %s + ( 1 / 2 ) ) - %s )' % (WIN(), a, a))
    vol2 = sj([vol, sj([sj([ar_], 'recnd', '%s e. CC' % a), numst(w, J, '( 1 / 2 )', 'CC')], 'pncan2d', '( ( %s + ( 1 / 2 ) ) - %s ) = ( 1 / 2 )' % (a, a))], 'eqtrd', '( vol ` %s ) = ( 1 / 2 )' % WIN())
    volr = sj([vol2, numst(w, J, '( 1 / 2 )', 'RR')], 'eqeltrrd', '( vol ` %s ) e. RR' % WIN()) if False else sj([numst(w, J, '( 1 / 2 )', 'RR'), vol2], 'eqeltrrd', '( vol ` %s ) e. RR' % WIN()) if False else \
        sj([sj([vol2], 'eqcomd', '( 1 / 2 ) = ( vol ` %s )' % WIN()), numst(w, J, '( 1 / 2 )', 'RR')], 'eqeltrrd', '( vol ` %s ) e. RR' % WIN()) if False else None
    volr = sj([vol2, numst(w, J, '( 1 / 2 )', 'RR')], 'eqeltrd', '( vol ` %s ) e. RR' % WIN())
    wv = sj([w.s([], 'ioombl', '%s e. dom vol' % WIN())], 'a1i', '%s e. dom vol' % WIN())
    kc = sj([kr], 'recnd', '%s e. CC' % K)
    ic = sj([sj([wv, volr, kc], '3jca', '( %s e. dom vol /\\ ( vol ` %s ) e. RR /\\ %s e. CC )' % (WIN(), WIN(), K)), w.inst('iblconst')], 'syl', '( %s X. { %s } ) e. L^1' % (WIN(), K))
    ibK = sj([sj([w.s([], 'fconstmpt', '( %s X. { %s } ) = ( t e. %s |-> %s )' % (WIN(), K, WIN(), K))], 'a1i', '( %s X. { %s } ) = ( t e. %s |-> %s )' % (WIN(), K, WIN(), K)), ic], 'eqeltrrd', '( t e. %s |-> %s ) e. L^1' % (WIN(), K))
    ibG = sj([ar_, a2, w.inst('ef1iac')], 'syl2anc', '( t e. %s |-> %s ) e. L^1' % (WIN(), G_))
    ile = sj([ibK, ibG, lift(w, kr, Jt), st_([gW], 'rpred', '%s e. RR' % G_), kle], 'itgle', 'S. %s %s _d t <_ S. %s %s _d t' % (WIN(), K, WIN(), G_))
    ik = sj([sj([wv, volr, kc], '3jca', '( %s e. dom vol /\\ ( vol ` %s ) e. RR /\\ %s e. CC )' % (WIN(), WIN(), K)), w.inst('itgconst')], 'syl', 'S. %s %s _d t = ( %s x. ( vol ` %s ) )' % (WIN(), K, K, WIN()))
    ik2 = sj([ik, sj([vol2], 'oveq2d', '( %s x. ( vol ` %s ) ) = ( %s x. ( 1 / 2 ) )' % (K, WIN(), K))], 'eqtrd', 'S. %s %s _d t = ( %s x. ( 1 / 2 ) )' % (WIN(), K, K))
    IW = 'S. %s %s _d t' % (WIN(), G_)
    iwr = sj([ibG, st_([gW], 'rpred', '%s e. RR' % G_)], 'itgrecl' if False else 'id', 'x') if False else None
    gWr = st_([gW], 'rpred', '%s e. RR' % G_)
    iwr = sj([gWr, ibG], 'itgrecl', '%s e. RR' % IW)
    low = sj([ik2, ile], 'eqbrtrrd', '( %s x. ( 1 / 2 ) ) <_ %s' % (K, IW))
    xrr = sj([xr], 'rpred', '%s e. RR' % X)
    clj = Closure(w, J, {X: ('RR', xrr)}); clj.atom(X)
    e52 = ringeq(w, J, '( ( 5 / 2 ) x. ( %s x. ( 1 / 2 ) ) )' % K, X, clj)
    m52 = sj([sj([kr, numst(w, J, '( 1 / 2 )', 'RR')], 'remulcld', '( %s x. ( 1 / 2 ) ) e. RR' % K), iwr, numst(w, J, '( 5 / 2 )', 'RR'), numst(w, J, '( 5 / 2 )', 'ge0'), low], 'lemul2ad',
             '( ( 5 / 2 ) x. ( %s x. ( 1 / 2 ) ) ) <_ ( ( 5 / 2 ) x. %s )' % (K, IW))
    pw = sj([e52, m52], 'eqbrtrrd', '%s <_ ( ( 5 / 2 ) x. %s )' % (X, IW))
    SX = 'sum_ j e. ( 0 ..^ M ) %s' % X
    SI = 'sum_ j e. ( 0 ..^ M ) %s' % IW
    fz = s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin')
    s1 = s([fz, sj([xr], 'rpred', '%s e. RR' % X), sj([numst(w, J, '( 5 / 2 )', 'RR'), iwr], 'remulcld', '( ( 5 / 2 ) x. %s ) e. RR' % IW), pw], 'fsumle', '%s <_ sum_ j e. ( 0 ..^ M ) ( ( 5 / 2 ) x. %s )' % (SX, IW))
    s2 = s([fz, numst(w, A0, '( 5 / 2 )', 'CC'), sj([iwr], 'recnd', '%s e. CC' % IW)], 'fsummulc2', '( ( 5 / 2 ) x. %s ) = sum_ j e. ( 0 ..^ M ) ( ( 5 / 2 ) x. %s )' % (SI, IW))
    IA = 'S. %s %s _d t' % (IADJ, G_)
    iar = s([s([gA], 'id', 'x') if False else None], 'id', 'x') if False else None
    Aa2 = Aa
    iar = s([St(w, Aa)([gA], 'rpred', '%s e. RR' % G_), ibA], 'itgrecl', '%s e. RR' % IA)
    sir = s([fz, iwr], 'fsumrecl', '%s e. RR' % SI)
    sxr = s([fz, sj([xr], 'rpred', '%s e. RR' % X)], 'fsumrecl', '%s e. RR' % SX)
    lg = s([s([s([numst(w, A0, '1', 'RR'), wr], 'readdcld', '( 1 + W ) e. RR'), lin8(w, A0, [p0, wp], '0 < ( 1 + W )', {'P': pr, 'W': wr})], 'elrpd', '( 1 + W ) e. RR+')], 'relogcld', '( log ` ( 1 + W ) ) e. RR')
    s3 = s([s1, s2], 'breqtrrd', '%s <_ ( ( 5 / 2 ) x. %s )' % (SX, SI))
    s4 = s([s3, s([adj], 'oveq2d', '( ( 5 / 2 ) x. %s ) = ( ( 5 / 2 ) x. %s )' % (IA, SI))], 'breqtrrd', '%s <_ ( ( 5 / 2 ) x. %s )' % (SX, IA))
    L2 = '( 2 x. ( log ` ( 1 + W ) ) )'
    s5 = s([iar, s([numst(w, A0, '2', 'RR'), lg], 'remulcld', '%s e. RR' % L2), numst(w, A0, '( 5 / 2 )', 'RR'), numst(w, A0, '( 5 / 2 )', 'ge0'), ial], 'lemul2ad', '( ( 5 / 2 ) x. %s ) <_ ( ( 5 / 2 ) x. %s )' % (IA, L2))
    cl0 = Closure(w, A0, {'( log ` ( 1 + W ) )': ('RR', lg)}); cl0.atom('( log ` ( 1 + W ) )')
    e5 = ringeq(w, A0, '( ( 5 / 2 ) x. %s )' % L2, '( 5 x. ( log ` ( 1 + W ) ) )', cl0)
    s6 = s([s5, e5], 'breqtrd', '( ( 5 / 2 ) x. %s ) <_ ( 5 x. ( log ` ( 1 + W ) ) )' % IA)
    w.qed([sxr, s([numst(w, A0, '( 5 / 2 )', 'RR'), iar], 'remulcld', '( ( 5 / 2 ) x. %s ) e. RR' % IA), s([numst(w, A0, '5', 'RR'), lg], 'remulcld', '( 5 x. ( log ` ( 1 + W ) ) ) e. RR'), s4, s6], 'letrd', S['ef3hm'])
    return run8(w)


def gen_wt():
    from ef3_c import JQ, NB, TJ
    w = W('ef3wt', 'Lean ` weight_sum_le ` : the weighted count ` sum m_q / ( 1 + abs Im q ) ` of any set of zeros in the box ` [ 1 / 2 , 3 / 2 ] x. [ - U , U ] ` is at most ` 24000 log ^ 2 ( A ( U + 2 ) ) ` (half-unit fibres of ` Im q ` , ~ ef3zw on each, ~ ef3hm ).')
    A0, G = ante_of(S['ef3wt'])
    s = St(w, A0)
    du = s([], 'simpl', '( %s /\\ ( U e. RR /\\ 2 <_ U ) )' % DD())
    dd, u2 = conj_split(w, A0, du)
    ur, u2_ = conj_split(w, A0, u2)
    gs = s([], 'simpr', 'G C_ %s' % BZ())
    bz = s([s([dd, ur], 'jca', '( %s /\\ U e. RR )' % DD()), w.inst('ef3bz')], 'syl', ante_of(S['ef3bz'])[1])
    bzf, bzo = conj_split(w, A0, bz)
    gf = s([bzf, gs], 'ssfid', 'G e. Fin')
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    IX = '( 0 ..^ %s )' % NB
    JY = JQ.replace('Q', 'y')
    FB = lambda j: '{ y e. G | %s = %s }' % (JY, j)
    # G = U_ j FB ( j )
    Aq = '( %s /\\ q e. G )' % A0
    sq = St(w, Aq)
    Lq = lambda st: lift(w, st, Aq)
    JQq = JQ.replace('Q', 'q')
    fq = sq([sq([Lq(ur), sq([Lq(gs), sq([], 'simpr', 'q e. G')], 'sseldd', 'q e. %s' % BZ())], 'jca', '( U e. RR /\\ q e. %s )' % BZ()), w.inst('ef3fib')], 'syl', tsub(ante_of(S['ef3fib'])[1], {'Q': 'q'}))
    jqi, _ = conj_split(w, Aq, fq)
    rs = w.s([w.s([], 'risset', '( %s e. %s <-> E. j e. %s j = %s )' % (JQq, IX, IX, JQq)), w.s([w.s([], 'eqcom', '( j = %s <-> %s = j )' % (JQq, JQq))], 'rexbii', '( E. j e. %s j = %s <-> E. j e. %s %s = j )' % (IX, JQq, IX, JQq))],
             'bitri', '( %s e. %s <-> E. j e. %s %s = j )' % (JQq, IX, IX, JQq))
    exq = sq([jqi, rs], 'sylib', 'E. j e. %s %s = j' % (IX, JQq))
    alq = s([exq], 'ralrimiva', 'A. q e. G E. j e. %s %s = j' % (IX, JQq))
    equ, _ = w.wcongr('E. j e. %s %s = j' % (IX, JQq), {'q': 'y'}, 'q = y', {'q': w.s([], 'id', '( q = y -> q = y )')})
    aly = s([alq, w.s([equ], 'cbvralvw', '( A. q e. G E. j e. %s %s = j <-> A. y e. G E. j e. %s %s = j )' % (IX, JQq, IX, JY))], 'sylib', 'A. y e. G E. j e. %s %s = j' % (IX, JY))
    rid = s([aly, w.s([], 'rabid2', '( G = { y e. G | E. j e. %s %s = j } <-> A. y e. G E. j e. %s %s = j )' % (IX, JY, IX, JY))], 'sylibr', 'G = { y e. G | E. j e. %s %s = j }' % (IX, JY))
    IU = 'U_ j e. %s %s' % (IX, FB('j'))
    iu = s([w.s([], 'iunrab', '%s = { y e. G | E. j e. %s %s = j }' % (IU, IX, JY))], 'a1i', '%s = { y e. G | E. j e. %s %s = j }' % (IU, IX, JY))
    geq = s([rid, s([iu], 'eqcomd', '{ y e. G | E. j e. %s %s = j } = %s' % (IX, JY, IU))], 'eqtrd', 'G = %s' % IU)
    # fsumiun
    Ak = '( %s /\\ j e. %s )' % (A0, IX)
    sk = St(w, Ak)
    Lk = lambda st: lift(w, st, Ak)
    fbs = sk([w.s([], 'ssrab2', '%s C_ G' % FB('j'))], 'a1i', '%s C_ G' % FB('j'))
    fbf = sk([Lk(gf), fbs], 'ssfid', '%s e. Fin' % FB('j'))
    dj = s([w.s([], 'invdisjrab', 'Disj_ j e. %s %s' % (IX, FB('j')))], 'a1i', 'Disj_ j e. %s %s' % (IX, FB('j')))
    Akq = '( %s /\\ ( j e. %s /\\ q e. %s ) )' % (A0, IX, FB('j'))
    skq = St(w, Akq)
    qg = skq([skq([], 'simprr', 'q e. %s' % FB('j')), w.inst('elrabi')], 'syl', 'q e. G')
    def wq_facts(A, qgst):
        """( A -> WQ e. RR ), ( A -> 0 <_ WQ ) from q e. G"""
        sA = St(w, A)
        qb = sA([lift(w, gs, A), qgst], 'sseldd', 'q e. %s' % BZ())
        on = sA([lift(w, bzo, A), qb, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
        from ef3_c import box_unpack
        bu = box_unpack(w, A, 'U', lift(w, ur, A), 'q', qb)
        iq = bu['lv']['( Im ` q )']
        aq = sA([sA([iq], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
        ap = sA([sA([numst(w, A, '1', 'RR'), aq], 'readdcld', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR'), lin8(w, A, [sA([sA([iq], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < ( 1 + ( abs ` ( Im ` q ) ) )', {'( abs ` ( Im ` q ) )': aq})], 'elrpd', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR+')
        wr = sA([sA([on], 'nnred', '( F holord q ) e. RR'), ap], 'rerpdivcld', '%s e. RR' % WQ())
        return wr
    wkq = wq_facts(Akq, qg)
    fsi = s([s([w.s([], 'fzofi', '%s e. Fin' % IX)], 'a1i', '%s e. Fin' % IX), fbf, dj, skq([wkq], 'recnd', '%s e. CC' % WQ())], 'fsumiun', 'sum_ q e. %s %s = sum_ j e. %s sum_ q e. %s %s' % (IU, WQ(), IX, FB('j'), WQ()))
    sg = s([s([geq], 'sumeq1d', 'sum_ q e. G %s = sum_ q e. %s %s' % (WQ(), IU, WQ())), fsi], 'eqtrd', 'sum_ q e. G %s = sum_ j e. %s sum_ q e. %s %s' % (WQ(), IX, FB('j'), WQ()))
    # per fibre
    tjr = sk([sk([sk([Lk(ur)], 'renegcld', '-u U e. RR'), sk([sk([sk([sk([], 'simpr', 'j e. %s' % IX), w.inst('elfzonn0')], 'syl', 'j e. NN0')], 'nn0red', 'j e. RR'), numst(w, Ak, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '( -u U + ( j / 2 ) ) e. RR'),
              numst(w, Ak, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % TJ('j'))
    ZJ = ZS('F', TJ('j'))
    JZ = JQ.replace('Q', 'z')
    Ay = '( %s /\\ z e. %s )' % (Ak, FB('j'))
    sy = St(w, Ay)
    Ly = lambda st: lift(w, st, Ay)
    yfb = sy([], 'simpr', 'z e. %s' % FB('j'))
    elz, _ = elrab_(w, 'y', 'G', '%s = j' % JY, 'z')
    ybt = sy([yfb, elz], 'sylib', '( z e. G /\\ %s = j )' % JZ)
    yg, yj = conj_split(w, Ay, ybt)
    fy = sy([sy([Ly(Lk(ur)), sy([Ly(Lk(gs)), yg], 'sseldd', 'z e. %s' % BZ())], 'jca', '( U e. RR /\\ z e. %s )' % BZ()), w.inst('ef3fib')], 'syl', tsub(ante_of(S['ef3fib'])[1], {'Q': 'z'}))
    _, yzs = conj_split(w, Ay, fy)
    eqz, _ = w.wcongr('z e. %s' % ZJ, {'j': JZ}, 'j = %s' % JZ, {'j': w.s([], 'id', '( j = %s -> j = %s )' % (JZ, JZ))})
    yz = sy([yzs, sy([sy([yj], 'eqcomd', 'j = %s' % JZ), eqz], 'syl', '( z e. %s <-> z e. %s )' % (ZJ, tsub(ZJ, {'j': JZ})))], 'mpbird', 'z e. %s' % ZJ)
    fbz = sk([w.s([yz], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (Ak, FB('j'), ZJ))], 'ssrdv', '%s C_ %s' % (FB('j'), ZJ))
    zwa = tsub(ante_of(S['ef3zw'])[0], {'T': TJ('j'), 'G': FB('j')})
    zw = sk([sk([sk([Lk(dd), tjr], 'jca', '( %s /\\ %s e. RR )' % (DD(), TJ('j'))), fbz], 'jca', zwa), w.inst('ef3zw')], 'syl', tsub(ante_of(S['ef3zw'])[1], {'T': TJ('j'), 'G': FB('j')}))
    # log XA ( TJ ) <_ 2 LA
    LA_ = LA
    AU = '( A x. ( U + 2 ) )'
    X1 = XA(TJ('j'))
    atj = sk([sk([tjr], 'recnd', '%s e. CC' % TJ('j'))], 'abscld', '( abs ` %s ) e. RR' % TJ('j'))
    jn = sk([sk([], 'simpr', 'j e. %s' % IX), w.inst('elfzonn0')], 'syl', 'j e. NN0')
    jr = sk([jn], 'nn0red', 'j e. RR')
    F4 = '( |_ ` ( 4 x. U ) )'
    f4r = sk([sk([sk([numst(w, Ak, '4', 'RR'), Lk(ur)], 'remulcld', '( 4 x. U ) e. RR')], 'flcld', '%s e. ZZ' % F4)], 'zred', '%s e. RR' % F4)
    jle = sk([sk([sk([], 'simpr', 'j e. %s' % IX), w.inst('fzofzp1')], 'syl', '( j + 1 ) e. ( 0 ... %s )' % NB), w.inst('elfzle2')], 'syl', '( j + 1 ) <_ %s' % NB)
    f4le = sk([sk([numst(w, Ak, '4', 'RR'), Lk(ur)], 'remulcld', '( 4 x. U ) e. RR'), w.inst('flle')], 'syl', '%s <_ ( 4 x. U )' % F4)
    lvj = {'j': jr, 'U': Lk(ur), F4: f4r, '( abs ` %s )' % TJ('j'): atj}
    tb = sk([sk([lin8(w, Ak, [sk([jn], 'nn0ge0d', '0 <_ j'), Lk(u2_)], '-u ( U + ( 1 / 4 ) ) <_ %s' % TJ('j'), lvj), lin8(w, Ak, [jle, f4le], '%s <_ ( U + ( 1 / 4 ) )' % TJ('j'), lvj)], 'jca',
                 '( -u ( U + ( 1 / 4 ) ) <_ %s /\\ %s <_ ( U + ( 1 / 4 ) ) )' % (TJ('j'), TJ('j'))),
             sk([tjr, sk([Lk(ur), numst(w, Ak, '( 1 / 4 )', 'RR')], 'readdcld', '( U + ( 1 / 4 ) ) e. RR')], 'absled', '( ( abs ` %s ) <_ ( U + ( 1 / 4 ) ) <-> ( -u ( U + ( 1 / 4 ) ) <_ %s /\\ %s <_ ( U + ( 1 / 4 ) ) ) )' % (TJ('j'), TJ('j'), TJ('j')))],
            'mpbird', '( abs ` %s ) <_ ( U + ( 1 / 4 ) )' % TJ('j'))
    arr = Lk(ar)
    a0 = lin8(w, Ak, [Lk(a1)], '0 <_ A', {'A': arr})
    x1a = sk([sk([atj, numst(w, Ak, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % TJ('j')), sk([numst(w, Ak, '2', 'RR'), sk([Lk(ur), numst(w, Ak, '2', 'RR')], 'readdcld', '( U + 2 ) e. RR')], 'remulcld', '( 2 x. ( U + 2 ) ) e. RR'),
              arr, a0, lin8(w, Ak, [tb, Lk(u2_)], '( ( abs ` %s ) + 2 ) <_ ( 2 x. ( U + 2 ) )' % TJ('j'), lvj)], 'lemul2ad', '%s <_ ( A x. ( 2 x. ( U + 2 ) ) )' % X1)
    cla = Closure(w, Ak, {'A': ('RR', arr), 'U': ('RR', Lk(ur))}); cla.atom('A'); cla.atom('U')
    x1b = sk([x1a, ringeq(w, Ak, '( A x. ( 2 x. ( U + 2 ) ) )', '( 2 x. %s )' % AU, cla)], 'breqtrd', '%s <_ ( 2 x. %s )' % (X1, AU))
    aur = sk([arr, sk([Lk(ur), numst(w, Ak, '2', 'RR')], 'readdcld', '( U + 2 ) e. RR')], 'remulcld', '%s e. RR' % AU)
    a4 = sk([s([ar], 'id', 'x') if False else lin.linarith(w, Ak, [Lk(a1), Lk(u2_)], '4 <_ %s' % AU, closure=cla, products=True)], 'id', 'x') if False else lin.linarith(w, Ak, [Lk(a1), Lk(u2_)], '4 <_ %s' % AU, closure=cla, products=True)
    aup = sk([aur, lin8(w, Ak, [a4], '0 < %s' % AU, {AU: aur})], 'elrpd', '%s e. RR+' % AU)
    x1r = sk([arr, sk([atj, numst(w, Ak, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % TJ('j'))], 'remulcld', '%s e. RR' % X1)
    x1p = sk([x1r, lin.linarith(w, Ak, [Lk(a1), sk([sk([tjr], 'recnd', '%s e. CC' % TJ('j'))], 'absge0d', '0 <_ ( abs ` %s )' % TJ('j'))], '0 < %s' % X1, closure=Closure(w, Ak, {'A': ('RR', arr), '( abs ` %s )' % TJ('j'): ('RR', atj)}), products=True)], 'elrpd', '%s e. RR+' % X1)
    x2p = sk([numst(w, Ak, '2', 'RR+'), aup], 'rpmulcld', '( 2 x. %s ) e. RR+' % AU)
    lx = sk([x1b, sk([x1p, x2p], 'logled', '( %s <_ ( 2 x. %s ) <-> ( log ` %s ) <_ ( log ` ( 2 x. %s ) ) )' % (X1, AU, X1, AU))], 'mpbid', '( log ` %s ) <_ ( log ` ( 2 x. %s ) )' % (X1, AU))
    lm = sk([numst(w, Ak, '2', 'RR+'), aup], 'relogmuld', '( log ` ( 2 x. %s ) ) = ( ( log ` 2 ) + %s )' % (AU, LA_))
    l2a = sk([lin8(w, Ak, [a4], '2 <_ %s' % AU, {AU: aur}), sk([numst(w, Ak, '2', 'RR+'), aup], 'logled', '( 2 <_ %s <-> ( log ` 2 ) <_ %s )' % (AU, LA_))], 'mpbid', '( log ` 2 ) <_ %s' % LA_)
    lvl = {'( log ` %s )' % X1: sk([x1p], 'relogcld', '( log ` %s ) e. RR' % X1), '( log ` ( 2 x. %s ) )' % AU: sk([x2p], 'relogcld', '( log ` ( 2 x. %s ) ) e. RR' % AU),
           '( log ` 2 )': sk([numst(w, Ak, '2', 'RR+')], 'relogcld', '( log ` 2 ) e. RR'), LA_: sk([aup], 'relogcld', '%s e. RR' % LA_)}
    b = '( 1 + ( abs ` %s ) )' % TJ('j')
    bp = sk([sk([numst(w, Ak, '1', 'RR'), atj], 'readdcld', '%s e. RR' % b), lin8(w, Ak, [sk([sk([tjr], 'recnd', '%s e. CC' % TJ('j'))], 'absge0d', '0 <_ ( abs ` %s )' % TJ('j'))], '0 < %s' % b, {'( abs ` %s )' % TJ('j'): atj})], 'elrpd', '%s e. RR+' % b)
    N1 = '( ; ; ; 2 4 0 0 x. ( log ` %s ) )' % X1
    N2 = '( ; ; ; 2 4 0 0 x. ( 2 x. %s ) )' % LA_
    nle = lin8(w, Ak, [lx, lm, l2a], '%s <_ %s' % (N1, N2), lvl)
    dle = sk([sk([numst(w, Ak, '; ; ; 2 4 0 0', 'RR'), lvl['( log ` %s )' % X1]], 'remulcld', '%s e. RR' % N1), sk([numst(w, Ak, '; ; ; 2 4 0 0', 'RR'), sk([numst(w, Ak, '2', 'RR'), lvl[LA_]], 'remulcld', '( 2 x. %s ) e. RR' % LA_)], 'remulcld', '%s e. RR' % N2), bp, nle], 'lediv1dd',
             '( %s / %s ) <_ ( %s / %s )' % (N1, b, N2, b))
    K48 = '( ; ; ; 4 8 0 0 x. %s )' % LA_
    cll = Closure(w, Ak, {LA_: ('RR', lvl[LA_])}); cll.atom(LA_)
    n2c = sk([numst(w, Ak, '; ; ; 2 4 0 0', 'CC'), sk([numst(w, Ak, '2', 'CC'), sk([lvl[LA_]], 'recnd', '%s e. CC' % LA_)], 'mulcld', '( 2 x. %s ) e. CC' % LA_)], 'mulcld', '%s e. CC' % N2)
    dr1 = sk([n2c, sk([sk([bp], 'rpred', '%s e. RR' % b)], 'recnd', '%s e. CC' % b), sk([bp], 'rpne0d', '%s =/= 0' % b)], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (N2, b, N2, b))
    dr2 = sk([ringeq(w, Ak, N2, K48, cll)], 'oveq1d', '( %s x. ( 1 / %s ) ) = ( %s x. ( 1 / %s ) )' % (N2, b, K48, b))
    RB = '( %s x. ( 1 / %s ) )' % (K48, b)
    SB = 'sum_ q e. %s %s' % (FB('j'), WQ())
    pfb = sk([sk([zw, dle], 'letrd' if False else 'id', 'x') if False else None], 'id', 'x') if False else None
    sbr = sk([fbf, St(w, '( %s /\\ q e. %s )' % (Ak, FB('j')))([wq_facts('( %s /\\ q e. %s )' % (Ak, FB('j')), St(w, '( %s /\\ q e. %s )' % (Ak, FB('j')))([St(w, '( %s /\\ q e. %s )' % (Ak, FB('j')))([], 'simpr', 'q e. %s' % FB('j')), w.inst('elrabi')], 'syl', 'q e. G'))], 'id', 'x') if False else
              wq_facts('( %s /\\ q e. %s )' % (Ak, FB('j')), St(w, '( %s /\\ q e. %s )' % (Ak, FB('j')))([St(w, '( %s /\\ q e. %s )' % (Ak, FB('j')))([], 'simpr', 'q e. %s' % FB('j')), w.inst('elrabi')], 'syl', 'q e. G'))], 'fsumrecl', '%s e. RR' % SB)
    D1 = '( %s / %s )' % (N1, b); D2 = '( %s / %s )' % (N2, b)
    d1r = sk([sk([numst(w, Ak, '; ; ; 2 4 0 0', 'RR'), lvl['( log ` %s )' % X1]], 'remulcld', '%s e. RR' % N1), bp], 'rerpdivcld', '%s e. RR' % D1)
    d2r = sk([sk([numst(w, Ak, '; ; ; 2 4 0 0', 'RR'), sk([numst(w, Ak, '2', 'RR'), lvl[LA_]], 'remulcld', '( 2 x. %s ) e. RR' % LA_)], 'remulcld', '%s e. RR' % N2), bp], 'rerpdivcld', '%s e. RR' % D2)
    p1 = sk([sbr, d1r, d2r, zw, dle], 'letrd', '%s <_ %s' % (SB, D2))
    pf = sk([p1, sk([dr1, dr2], 'eqtrd', '%s = %s' % (D2, RB))], 'breqtrd', '%s <_ %s' % (SB, RB))
    # sum over the fibres
    fz = s([w.s([], 'fzofi', '%s e. Fin' % IX)], 'a1i', '%s e. Fin' % IX)
    XB = '( 1 / %s )' % b
    xbr = sk([bp], 'rpreccld', '%s e. RR+' % XB)
    SS = 'sum_ j e. %s %s' % (IX, SB)
    k48r = sk([numst(w, Ak, '; ; ; 4 8 0 0', 'RR'), lvl[LA_]], 'remulcld', '%s e. RR' % K48)
    rbr = sk([k48r, sk([xbr], 'rpred', '%s e. RR' % XB)], 'remulcld', '%s e. RR' % RB)
    t1 = s([fz, sbr, rbr, pf], 'fsumle', '%s <_ sum_ j e. %s %s' % (SS, IX, RB))
    HS = 'sum_ j e. %s %s' % (IX, XB)
    # LA at the top level
    aur0 = s([ar, s([ur, numst(w, A0, '2', 'RR')], 'readdcld', '( U + 2 ) e. RR')], 'remulcld', '%s e. RR' % AU)
    cl0 = Closure(w, A0, {'A': ('RR', ar), 'U': ('RR', ur)}); cl0.atom('A'); cl0.atom('U')
    a40 = lin.linarith(w, A0, [a1, u2_], '4 <_ %s' % AU, closure=cl0, products=True)
    aup0 = s([aur0, lin8(w, A0, [a40], '0 < %s' % AU, {AU: aur0})], 'elrpd', '%s e. RR+' % AU)
    lar = s([aup0], 'relogcld', '%s e. RR' % LA_)
    k480 = s([numst(w, A0, '; ; ; 4 8 0 0', 'RR'), lar], 'remulcld', '%s e. RR' % K48)
    t2 = s([fz, s([k480], 'recnd', '%s e. CC' % K48), sk([sk([xbr], 'rpred', '%s e. RR' % XB)], 'recnd', '%s e. CC' % XB)], 'fsummulc2', '( %s x. %s ) = sum_ j e. %s %s' % (K48, HS, IX, RB))
    # ef3hm at P = -u U, M = NB, W = U + 1/2
    W2 = '( U + ( 1 / 2 ) )'
    PT_ = '( -u U + ( %s / 2 ) )' % NB
    f40 = s([s([numst(w, A0, '4', 'RR'), ur], 'remulcld', '( 4 x. U ) e. RR'), lin8(w, A0, [u2_], '0 <_ ( 4 x. U )', {'U': ur}), w.inst('flge0nn0')], 'syl2anc', '%s e. NN0' % F4)
    nbn = s([f40, w.inst('peano2nn0')], 'syl', '%s e. NN0' % NB)
    f4r0 = s([f40], 'nn0red', '%s e. RR' % F4)
    fl1 = s([s([numst(w, A0, '4', 'RR'), ur], 'remulcld', '( 4 x. U ) e. RR'), w.inst('flle')], 'syl', '%s <_ ( 4 x. U )' % F4)
    fl2 = s([s([numst(w, A0, '4', 'RR'), ur], 'remulcld', '( 4 x. U ) e. RR'), w.inst('flltp1')], 'syl', '( 4 x. U ) < ( %s + 1 )' % F4)
    lvh = {'U': ur, F4: f4r0}
    HA = tsub(ante_of(S['ef3hm'])[0], {'P': '-u U', 'M': NB, 'W': W2})
    ha1, ha2 = top_and(HA)
    hm = s([s([s([s([ur], 'renegcld', '-u U e. RR'), nbn, s([ur, numst(w, A0, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % W2)], '3jca', ha1),
               s([s([lin8(w, A0, [u2_], '-u U <_ 0', lvh), lin8(w, A0, [fl2, u2_], '0 <_ %s' % PT_, lvh)], 'jca', top_and(ha2)[0]),
                  s([lin8(w, A0, [], '-u %s <_ -u U' % W2, lvh), lin8(w, A0, [fl1], '%s <_ %s' % (PT_, W2), lvh)], 'jca', top_and(ha2)[1])], 'jca', ha2)], 'jca', HA), w.inst('ef3hm')], 'syl',
           tsub(ante_of(S['ef3hm'])[1], {'P': '-u U', 'M': NB, 'W': W2}))
    L1W = '( log ` ( 1 + %s ) )' % W2
    w1p = s([s([numst(w, A0, '1', 'RR'), s([ur, numst(w, A0, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % W2)], 'readdcld', '( 1 + %s ) e. RR' % W2), lin8(w, A0, [u2_], '0 < ( 1 + %s )' % W2, {'U': ur})], 'elrpd', '( 1 + %s ) e. RR+' % W2)
    au_ge = lin.linarith(w, A0, [a1, u2_], '( 1 + %s ) <_ %s' % (W2, AU), closure=cl0, products=True)
    lw = s([au_ge, s([w1p, aup0], 'logled', '( ( 1 + %s ) <_ %s <-> %s <_ %s )' % (W2, AU, L1W, LA_))], 'mpbid', '%s <_ %s' % (L1W, LA_))
    hsr = s([fz, sk([xbr], 'rpred', '%s e. RR' % XB)], 'fsumrecl', '%s e. RR' % HS)
    l1wr = s([w1p], 'relogcld', '%s e. RR' % L1W)
    hs5 = lin8(w, A0, [hm, lw], '%s <_ ( 5 x. %s )' % (HS, LA_), {HS: hsr, L1W: l1wr, LA_: lar})
    la0 = s([lin8(w, A0, [a40], '1 <_ %s' % AU, {AU: aur0}), s([aur0, w.inst('log1ge0' if False else 'logge0')], 'syl', 'x') if False else None], 'id', 'x') if False else None
    la0 = s([aur0, lin8(w, A0, [a40], '1 <_ %s' % AU, {AU: aur0})], 'logge0d', '0 <_ %s' % LA_)
    k0 = lin8(w, A0, [la0], '0 <_ %s' % K48, {LA_: lar})
    t3 = s([hsr, s([numst(w, A0, '5', 'RR'), lar], 'remulcld', '( 5 x. %s ) e. RR' % LA_), k480, k0, hs5], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 5 x. %s ) )' % (K48, HS, K48, LA_))
    cl1 = Closure(w, A0, {LA_: ('RR', lar)}); cl1.atom(LA_)
    sqv = s([s([lar], 'recnd', '%s e. CC' % LA_)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (LA_, LA_, LA_))
    e1 = ringeq(w, A0, '( %s x. ( 5 x. %s ) )' % (K48, LA_), '( %s x. ( %s x. %s ) )' % (KW, LA_, LA_), cl1)
    e2 = s([e1, s([sqv], 'oveq2d', '( %s x. ( %s ^ 2 ) ) = ( %s x. ( %s x. %s ) )' % (KW, LA_, KW, LA_, LA_))], 'eqtr4d', '( %s x. ( 5 x. %s ) ) = ( %s x. ( %s ^ 2 ) )' % (K48, LA_, KW, LA_))
    t4 = s([t3, e2], 'breqtrd', '( %s x. %s ) <_ ( %s x. ( %s ^ 2 ) )' % (K48, HS, KW, LA_))
    t5 = s([t1, t2], 'breqtrrd', '%s <_ ( %s x. %s )' % (SS, K48, HS))
    ssr = s([fz, sbr], 'fsumrecl', '%s e. RR' % SS)
    t6 = s([ssr, s([k480, hsr], 'remulcld', '( %s x. %s ) e. RR' % (K48, HS)), s([numst(w, A0, KW, 'RR'), s([lar], 'resqcld', '( %s ^ 2 ) e. RR' % LA_)], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (KW, LA_)), t5, t4], 'letrd',
           '%s <_ ( %s x. ( %s ^ 2 ) )' % (SS, KW, LA_))
    w.qed([sg, t6], 'eqbrtrd', S['ef3wt'])
    return run8(w)


if __name__ == '__main__':
    gen_zw()
    gen_adj()
    gen_hm()
    gen_wt()
