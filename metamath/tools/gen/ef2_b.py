"""Sortie EF2: the square zero set of a DiskData function (ef2zs, ef2zss, ef2reb) and the Landau expansion (ef2lnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import c9_h
patch(c9_h)
from c9_h import c0_facts
from c8_n import sqparts, sqre_at, sqcc
import cl as _cl
import lin
lin.FASTPATH = True

X_ = XA()
B_ = '( ; 2 5 x. %s )' % X_
M_ = '( 1 / 4 )'
IV = '( ( T - 2 ) [,] ( T + 2 ) )'


def zs_core(w, A0, dd, tr):
    """( A0 -> jensq13 conclusion at B_, M_ ) and ( A0 -> JW <_ 800 log X ), X >_ 2"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    lo, bd = dd_at(w, A0, allt, 'T', tr)
    # A. t e. RR low  ->  A. t e. IV low
    LO = '( ( 1 / 4 ) <_ ( abs ` ( F ` %s ) ) )' % CT('t')
    LO = LO[2:-2]
    BDt = 'A. x e. %s ( abs ` ( F ` x ) ) <_ ( ; 2 5 x. %s )' % (RCT('t'), XA('t'))
    r26 = w.s([], 'r19.26', '( A. t e. RR ( %s /\\ %s ) <-> ( A. t e. RR %s /\\ A. t e. RR %s ) )' % (LO, BDt, LO, BDt))
    alo = s([s([allt, r26], 'sylib', '( A. t e. RR %s /\\ A. t e. RR %s )' % (LO, BDt)), w.inst('simpl')], 'syl', 'A. t e. RR %s' % LO)
    two = numst(w, A0, '2', 'RR')
    ta = s([tr, two], 'resubcld', '( T - 2 ) e. RR'); tb = s([tr, two], 'readdcld', '( T + 2 ) e. RR')
    iss = s([ta, tb], 'iccssred', '%s C_ RR' % IV)
    ilo = s([iss, alo, w.inst('ssralv')], 'sylc', 'A. t e. %s %s' % (IV, LO))
    xr = s([ar, s([s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR'), two], 'readdcld', '( ( abs ` T ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % X_)
    x2 = s([dd, tr, w.inst('ef2x2')], 'syl2anc', '2 <_ %s' % X_)
    lv = {X_: xr}
    br = s([numst(w, A0, '; 2 5', 'RR'), xr], 'remulcld', '%s e. RR' % B_)
    J = tsub(stmt('jensq13'), {'B': B_, 'M': M_})
    ja, jc = ante_of(J)
    j1, j2, j3 = top_and(ja)
    mrp = numst(w, A0, M_, 'RR+')
    jan = s([s([hol, tr], 'jca', j1), s([br, bd], 'jca', j2), s([mrp, ilo], 'jca', j3)], '3jca', ja)
    jcs = s([jan, w.inst('jensq13')], 'syl', jc)
    # the numerals
    brp = s([br, lin8(w, A0, [x2], '0 < %s' % B_, lv)], 'elrpd', '%s e. RR+' % B_)
    P = '( ; ; 1 2 8 x. %s )' % X_
    bmx = s([lin8(w, A0, [x2], '%s <_ ( %s x. %s )' % (B_, M_, P), lv),
             s([br, s([numst(w, A0, '; ; 1 2 8', 'RR'), xr], 'remulcld', '%s e. RR' % P), mrp], 'ledivmuld',
               '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B_, M_, P, B_, M_, P))], 'mpbird', '( %s / %s ) <_ %s' % (B_, M_, P))
    W8 = tsub(stmt('zc1w8'), {'X': X_, 'B': B_, 'M': M_})
    wa, wc = ante_of(W8)
    w8 = s([s([s([xr, x2], 'jca', '( %s e. RR /\\ 2 <_ %s )' % (X_, X_)),
               s([s([brp, mrp], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (B_, M_)),
                  s([lin8(w, A0, [x2], '%s <_ %s' % (M_, B_), lv), bmx], 'jca', '( %s <_ %s /\\ ( %s / %s ) <_ %s )' % (M_, B_, B_, M_, P))], 'jca',
                 top_and(wa)[1])], 'jca', wa), w.inst('zc1w8')], 'syl', wc)
    return jcs, jc, w8, wc, xr


def gen_zs():
    w = W('ef2zs', 'Lean ` finite_diskZeroSet ` , ` one_le_ord_of_mem_diskZeros ` , ` sum_ord_le_of_diskData ` on the square: the zero set of a ` DiskData ` function in the ` 13 / 8 ` square about ` 2 + i T ` is finite, its orders are positive integers, and its mass is at most ` 800 log ( A ( abs T + 2 ) ) ` ( ~ jensq13 , ~ zc1w8 ).')
    A0, _ = ante_of(S['ef2zs'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dd = s([], 'simpl', DD()); tr = s([], 'simpr', 'T e. RR')
    jcs, jc, w8, wc, xr = zs_core(w, A0, dd, tr)
    c1, c2, c3 = top_and(jc)
    lhs, rhs = c3.split(' <_ ')
    ms = le_tr(w, A0, s([jcs, w.inst('simp3')], 'syl', c3), lhs, rhs, w8, wc.split(' <_ ')[1])
    w.qed([s([jcs, w.inst('simp1')], 'syl', c1), s([jcs, w.inst('simp2')], 'syl', c2), ms], '3jca', S['ef2zs'])
    return run8(w)



def gen_zss():
    w = W('ef2zss', 'Lean ` sum_ord_le_of_diskData ` for a sub-finset: any subset of the square zero set of a ` DiskData ` function has mass at most ` 800 log ( A ( abs T + 2 ) ) ` .')
    A0, _ = ante_of(S['ef2zss'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dt = s([], 'simpl', DT); gs = s([], 'simpr', 'G C_ %s' % Z13)
    zc = ante_of(S['ef2zs'])[1]
    zs = s([dt, w.inst('ef2zs')], 'syl', zc)
    c1, c2, c3 = top_and(zc)
    fin = s([zs, w.inst('simp1')], 'syl', c1)
    alln = s([zs, w.inst('simp2')], 'syl', c2)
    mass = s([zs, w.inst('simp3')], 'syl', c3)
    Aq = '( %s /\\ q e. %s )' % (A0, Z13)
    nn = w.s([alln], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)
    re_ = w.s([nn], 'nnred', '( %s -> ( F holord q ) e. RR )' % Aq)
    ge0 = w.s([w.s([nn], 'nnnn0d', '( %s -> ( F holord q ) e. NN0 )' % Aq)], 'nn0ge0d', '( %s -> 0 <_ ( F holord q ) )' % Aq)
    le = s([fin, re_, ge0, gs], 'fsumless', '%s <_ %s' % (MASS('G', 'F'), MASS(Z13, 'F')))
    rhs = c3.split(' <_ ')[1]
    le_tr(w, A0, le, MASS('G', 'F'), MASS(Z13, 'F'), mass, rhs, name='qed')
    return run8(w)


def gen_reb():
    w = W('ef2reb', 'Lean ` re_bounds_of_mem_diskZeros ` on the square: a member of the ` 13 / 8 ` square about ` 2 + i T ` has real part in ` [ 3 / 8 , 29 / 8 ] ` and imaginary part within ` 13 / 8 ` of ` T ` .')
    A0, _ = ante_of(S['ef2reb'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'simpl', 'T e. RR'); pz = s([], 'simpr', 'P e. %s' % Z13)
    psq = s([pz, w.inst('elrabi')], 'syl', 'P e. %s' % SQ(CT('T'), R138))
    c0, re0, im0 = c0_facts(w, A0, tr)
    rr = numst(w, A0, R138, 'RR')
    ps = sqparts(w, A0, sqre_at(w, A0, c0, rr, c=CT('T'), r=R138), c=CT('T'), r=R138)
    a, b = sqcc(w, A0, c0, rr, c=CT('T'), r=R138)
    bnd = crect_bounds(w, A0, a, b, psq, SQA(CT('T'), R138), SQB(CT('T'), R138), 'P')
    lv = {}
    for e in ['( Re ` P )', '( Im ` P )', '( Re ` %s )' % SQA(CT('T'), R138), '( Re ` %s )' % SQB(CT('T'), R138),
              '( Im ` %s )' % SQA(CT('T'), R138), '( Im ` %s )' % SQB(CT('T'), R138), '( Re ` %s )' % CT('T'), '( Im ` %s )' % CT('T')]:
        lv[e] = bnd['cl'][e] if e in bnd['cl'] else None
    lv['( Re ` %s )' % CT('T')] = s([c0], 'recld', '( Re ` %s ) e. RR' % CT('T'))
    lv['( Im ` %s )' % CT('T')] = s([c0], 'imcld', '( Im ` %s ) e. RR' % CT('T'))
    lv['T'] = tr
    hy = ps + [re0, im0] + bnd['le']
    r1 = lin8(w, A0, hy, '( 3 / 8 ) <_ ( Re ` P )', lv)
    r2 = lin8(w, A0, hy, '( Re ` P ) <_ ( ; 2 9 / 8 )', lv)
    i1 = lin8(w, A0, hy, '( T - %s ) <_ ( Im ` P )' % R138, lv)
    i2 = lin8(w, A0, hy, '( Im ` P ) <_ ( T + %s )' % R138, lv)
    ab = s([s([lv['( Im ` P )'], tr, rr], 'absdifled', '( ( abs ` ( ( Im ` P ) - T ) ) <_ %s <-> ( ( T - %s ) <_ ( Im ` P ) /\\ ( Im ` P ) <_ ( T + %s ) ) )' % (R138, R138, R138)),
            s([i1, i2], 'jca', '( ( T - %s ) <_ ( Im ` P ) /\\ ( Im ` P ) <_ ( T + %s ) )' % (R138, R138))], 'mpbird', '( abs ` ( ( Im ` P ) - T ) ) <_ %s' % R138)
    w.qed([r1, r2, ab], '3jca', S['ef2reb'])
    return run8(w)


def gen_lnd():
    w = W('ef2lnd', 'Lean ` norm_logDeriv_sub_sum_diskZeros_le ` on squares: for a ` DiskData ` function, ` F \' / F ` minus the partial fractions of the ` 13 / 8 ` square zeros is at most ` 17500000 log ( A ( abs T + 2 ) ) ` on the ` 3 / 2 ` disc about ` 2 + i T ` ( ~ lndk ).')
    A0, _ = ante_of(S['ef2lnd'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dt = s([], 'simpl', DT); sd = s([], 'simpr', SDF)
    dd = s([dt, w.inst('simpl')], 'syl', DD()); tr = s([dt, w.inst('simpr')], 'syl', 'T e. RR')
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    lo, bd = dd_at(w, A0, allt, 'T', tr)
    two = numst(w, A0, '2', 'RR')
    xr = s([ar, s([s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR'), two], 'readdcld', '( ( abs ` T ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % X_)
    x2 = s([dt, w.inst('ef2x2')], 'syl', '2 <_ %s' % X_)
    lv = {X_: xr}
    br = s([numst(w, A0, '; 2 5', 'RR'), xr], 'remulcld', '%s e. RR' % B_)
    brp = s([br, lin8(w, A0, [x2], '0 < %s' % B_, lv)], 'elrpd', '%s e. RR+' % B_)
    mrp = numst(w, A0, M_, 'RR+')
    P = '( ; ; 1 2 8 x. %s )' % X_
    bmx = s([lin8(w, A0, [x2], '%s <_ ( %s x. %s )' % (B_, M_, P), lv),
             s([br, s([numst(w, A0, '; ; 1 2 8', 'RR'), xr], 'remulcld', '%s e. RR' % P), mrp], 'ledivmuld',
               '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B_, M_, P, B_, M_, P))], 'mpbird', '( %s / %s ) <_ %s' % (B_, M_, P))
    zc = ante_of(S['ef2zs'])[1]
    mass = s([s([dt, w.inst('ef2zs')], 'syl', zc), w.inst('simp3')], 'syl', top_and(zc)[2])
    LK = tsub(stmt('lndk'), {'X': X_, 'B': B_, 'M': M_})
    la, lc = ante_of(LK)
    K1, K2, K3 = top_and(la)
    Q1, Q2, Q3 = top_and(K2)
    k2 = s([s([xr, x2], 'jca', Q1), s([brp, bd], 'jca', Q2), s([mrp, lo, bmx], '3jca', Q3)], '3jca', K2)
    w.qed([s([s([hol, tr], 'jca', K1), k2, s([mass, sd], 'jca', K3)], '3jca', la), w.inst('lndk')], 'syl', S['ef2lnd'])
    return run8(w)


S['ef2card'] = '( %s -> ( # ` %s ) <_ ( ; ; 8 0 0 x. ( log ` %s ) ) )' % (DT, Z13, XA())


def gen_card():
    w = W('ef2card', 'Lean ` card_diskZeros_le ` on the square: the number of distinct zeros of a ` DiskData ` function in the ` 13 / 8 ` square about ` 2 + i T ` is at most ` 800 log ( A ( abs T + 2 ) ) ` .')
    A0, _ = ante_of(S['ef2card'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    zc = ante_of(S['ef2zs'])[1]
    zs = w.s([], 'ef2zs', S['ef2zs'])
    c1, c2, c3 = top_and(zc)
    fin = s([zs, w.inst('simp1')], 'syl', c1); alln = s([zs, w.inst('simp2')], 'syl', c2); mass = s([zs, w.inst('simp3')], 'syl', c3)
    Aq = '( %s /\\ q e. %s )' % (A0, Z13)
    nn = w.s([alln], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)
    one = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Aq)
    le = s([fin, one, w.s([nn], 'nnred', '( %s -> ( F holord q ) e. RR )' % Aq), w.s([nn], 'nnge1d', '( %s -> 1 <_ ( F holord q ) )' % Aq)], 'fsumle',
           'sum_ q e. %s 1 <_ %s' % (Z13, MASS(Z13, 'F')))
    hc = s([fin, s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ q e. %s 1 = ( ( # ` %s ) x. 1 )' % (Z13, Z13))
    hn = s([s([fin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % Z13)], 'nn0cnd', '( # ` %s ) e. CC' % Z13)
    he = s([hc, s([hn], 'mulridd', '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (Z13, Z13))], 'eqtrd', 'sum_ q e. %s 1 = ( # ` %s )' % (Z13, Z13))
    l2 = s([he, le], 'eqbrtrrd', '( # ` %s ) <_ %s' % (Z13, MASS(Z13, 'F')))
    le_tr(w, A0, l2, '( # ` %s )' % Z13, MASS(Z13, 'F'), mass, c3.split(' <_ ')[1], name='qed')
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2zs', 'ef2zss', 'ef2reb', 'ef2lnd', 'ef2card']:
        {'ef2zs': gen_zs, 'ef2zss': gen_zss, 'ef2reb': gen_reb, 'ef2lnd': gen_lnd, 'ef2card': gen_card}[g]()
