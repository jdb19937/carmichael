"""Sortie ZBV2, section 1 part A: the exponential inequalities and the chord
lemmas of the discrete Abel route (ZBV2-blueprint.md section 1.2).

bvefge1p    ( ( A e. RR /\\ 0 <_ A ) -> ( 1 + A ) <_ ( exp ` A ) )
bvexpl1     ( ( A e. RR /\\ 0 <_ A ) -> ( 1 - ( exp ` -u A ) ) <_ A )
bvexpl2     ( ( A e. RR /\\ 0 <_ A ) -> ( ( exp ` -u A ) x. A ) <_ ( 1 - ( exp ` -u A ) ) )
bvchordlem2 the lower chord certificate     bvchordlem3 the upper chord certificate
bvchordlem4 ( ( K + 1 ) ^c -u E ) = ( ( K ^c -u E ) x. ( exp ` -u ( E x. ELL(K) ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *

HA = '( A e. RR /\\ 0 <_ A )'


def afacts(w, ante):
    st = mkst(w, ante)
    ar = lift(w, w.s([], 'simpl', '( %s -> A e. RR )' % HA), ante)
    a0 = lift(w, w.s([], 'simpr', '( %s -> 0 <_ A )' % HA), ante)
    return st, ar, a0, st([ar], 'recnd', 'A e. CC')


def bvefge1p():
    w = W('bvefge1p', 'The exponential dominates 1 + A for A >= 0 (from the A layer\'s extrwlogle).')
    st, ar, a0, ac = afacts(w, HA)
    one = st([], '1red', '1 e. RR'); onec = st([], '1cnd', '1 e. CC')
    pa = st([one, ar], 'readdcld', '( 1 + A ) e. RR')
    pa1 = linarith(w, HA, [a0], '1 <_ ( 1 + A )', leaves={'A': ar})
    lg = sy2(w, HA, pa, pa1, 'extrwlogle', '( log ` ( 1 + A ) ) <_ ( ( 1 + A ) - 1 )')
    pc = st([onec, ac], 'pncan2d', '( ( 1 + A ) - 1 ) = A')
    lg2 = st([lg, pc], 'breqtrd', '( log ` ( 1 + A ) ) <_ A')
    parp = st([pa, linarith(w, HA, [a0], '0 < ( 1 + A )', leaves={'A': ar})], 'elrpd', '( 1 + A ) e. RR+')
    lgr = st([parp], 'relogcld', '( log ` ( 1 + A ) ) e. RR')
    efbi = sy2(w, HA, lgr, ar, 'efle', '( ( log ` ( 1 + A ) ) <_ A <-> ( exp ` ( log ` ( 1 + A ) ) ) <_ ( exp ` A ) )')
    ef1 = st([lg2, efbi], 'mpbid', '( exp ` ( log ` ( 1 + A ) ) ) <_ ( exp ` A )')
    rl = sy(w, HA, parp, 'reeflog', '( exp ` ( log ` ( 1 + A ) ) ) = ( 1 + A )')
    w.qed([rl, ef1], 'eqbrtrrd', '( %s -> ( 1 + A ) <_ ( exp ` A ) )' % HA)
    return w


def bvexpl1():
    w = W('bvexpl1', '1 - exp ( -u A ) <= A for A >= 0 (zdmlogl1 at exp A; the case A = 0 apart).')
    Q = '( exp ` -u A )'
    st, ar, a0, ac = afacts(w, HA)
    # case 0 < A
    A1 = '( %s /\\ 0 < A )' % HA
    s1 = mkst(w, A1)
    ar1 = lift(w, ar, A1); ac1 = lift(w, ac, A1)
    arp = s1([ar1, s1([], 'simpr', '0 < A')], 'elrpd', 'A e. RR+')
    ea = s1([ar1], 'reefcld', '( exp ` A ) e. RR')
    e1 = sy(w, A1, arp, 'efgt1', '1 < ( exp ` A )')
    core = sy2(w, A1, ea, e1, 'zdmlogl1', '( 1 - ( 1 / ( exp ` A ) ) ) <_ ( log ` ( exp ` A ) )')
    rl = sy(w, A1, ar1, 'relogef', '( log ` ( exp ` A ) ) = A')
    en = sy(w, A1, ac1, 'efneg', '%s = ( 1 / ( exp ` A ) )' % Q)
    lhs = s1([en], 'oveq2d', '( 1 - %s ) = ( 1 - ( 1 / ( exp ` A ) ) )' % Q)
    c1 = s1([lhs, s1([core, rl], 'breqtrd', '( 1 - ( 1 / ( exp ` A ) ) ) <_ A')], 'eqbrtrd', '( 1 - %s ) <_ A' % Q)
    # case 0 = A
    A2 = '( %s /\\ 0 = A )' % HA
    s2 = mkst(w, A2)
    z = s2([], 'simpr', '0 = A')
    na = s2([s2([z], 'negeqd', '-u 0 = -u A')], 'eqcomd', '-u A = -u 0')
    na0 = s2([na, s2([clo(w, 'neg0', '-u 0 = 0')], 'a1i', '-u 0 = 0')], 'eqtrd', '-u A = 0')
    e0 = s2([s2([na0], 'fveq2d', '%s = ( exp ` 0 )' % Q), s2([clo(w, 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( exp ` 0 ) = 1')], 'eqtrd', '%s = 1' % Q)
    d0 = s2([s2([e0], 'oveq2d', '( 1 - %s ) = ( 1 - 1 )' % Q), s2([clo(w, '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( 1 - 1 ) = 0')], 'eqtrd', '( 1 - %s ) = 0' % Q)
    dA = s2([d0, z], 'eqtrd', '( 1 - %s ) = A' % Q)
    qr2 = s2([s2([lift(w, ar, A2)], 'renegcld', '-u A e. RR')], 'reefcld', '%s e. RR' % Q)
    dr = s2([s2([], '1red', '1 e. RR'), qr2], 'resubcld', '( 1 - %s ) e. RR' % Q)
    c2 = s2([dr, dA], 'eqled', '( 1 - %s ) <_ A' % Q)
    bi = sy2(w, HA, st([], '0red', '0 e. RR'), ar, 'leloe', '( 0 <_ A <-> ( 0 < A \\/ 0 = A ) )')
    disj = st([a0, bi], 'mpbid', '( 0 < A \\/ 0 = A )')
    w.qed([c1, c2, disj], 'mpjaodan', '( %s -> ( 1 - %s ) <_ A )' % (HA, Q))
    return w


def bvexpl2():
    w = W('bvexpl2', 'exp ( -u A ) A <= 1 - exp ( -u A ) for A >= 0 (bvefge1p times exp ( -u A )).')
    Q = '( exp ` -u A )'
    st, ar, a0, ac = afacts(w, HA)
    ge = st([], 'bvefge1p', '( 1 + A ) <_ ( exp ` A )')
    qrp = st([st([ar], 'renegcld', '-u A e. RR')], 'rpefcld', '%s e. RR+' % Q)
    qr = st([qrp], 'rpred', '%s e. RR' % Q); qc = st([qr], 'recnd', '%s e. CC' % Q); q0 = st([qrp], 'rpge0d', '0 <_ %s' % Q)
    pa = st([st([], '1red', '1 e. RR'), ar], 'readdcld', '( 1 + A ) e. RR')
    ea = st([ar], 'reefcld', '( exp ` A ) e. RR'); eac = st([ea], 'recnd', '( exp ` A ) e. CC')
    m = st([pa, ea, qr, q0, ge], 'lemul2ad', '( %s x. ( 1 + A ) ) <_ ( %s x. ( exp ` A ) )' % (Q, Q))
    can = sy(w, HA, ac, 'efcan', '( ( exp ` A ) x. %s ) = 1' % Q)
    qe1 = st([st([qc, eac], 'mulcomd', '( %s x. ( exp ` A ) ) = ( ( exp ` A ) x. %s )' % (Q, Q)), can], 'eqtrd', '( %s x. ( exp ` A ) ) = 1' % Q)
    m1 = st([m, qe1], 'breqtrd', '( %s x. ( 1 + A ) ) <_ 1' % Q)
    dist = st([st([qc, st([], '1cnd', '1 e. CC'), ac], 'adddid', '( %s x. ( 1 + A ) ) = ( ( %s x. 1 ) + ( %s x. A ) )' % (Q, Q, Q)),
               st([st([qc], 'mulridd', '( %s x. 1 ) = %s' % (Q, Q))], 'oveq1d', '( ( %s x. 1 ) + ( %s x. A ) ) = ( %s + ( %s x. A ) )' % (Q, Q, Q, Q))], 'eqtrd',
              '( %s x. ( 1 + A ) ) = ( %s + ( %s x. A ) )' % (Q, Q, Q))
    m2 = st([dist, m1], 'eqbrtrrd', '( %s + ( %s x. A ) ) <_ 1' % (Q, Q))
    qar = st([qr, ar], 'remulcld', '( %s x. A ) e. RR' % Q)
    linarith(w, HA, [m2], '( %s x. A ) <_ ( 1 - %s )' % (Q, Q), leaves={Q: qr, '( %s x. A )' % Q: qar}, name='qed')
    return w


def chfacts(w):
    """the six facts of ANTE_CH with their closures"""
    A = ANTE_CH
    st = mkst(w, A)
    trip = st([], 'simpl', '( ( Q e. RR /\\ 0 <_ Q ) /\\ ( E e. RR /\\ 0 <_ E ) /\\ ( U e. RR /\\ 0 <_ U ) )')
    qh = st([trip], 'simp1d', '( Q e. RR /\\ 0 <_ Q )'); eh = st([trip], 'simp2d', '( E e. RR /\\ 0 <_ E )'); uh = st([trip], 'simp3d', '( U e. RR /\\ 0 <_ U )')
    qr = st([qh], 'simpld', 'Q e. RR'); q0 = st([qh], 'simprd', '0 <_ Q')
    er = st([eh], 'simpld', 'E e. RR'); e0 = st([eh], 'simprd', '0 <_ E')
    ur = st([uh], 'simpld', 'U e. RR'); u0 = st([uh], 'simprd', '0 <_ U')
    rest = st([], 'simpr', '( ( T e. RR /\\ U <_ T ) /\\ ( ( 1 - Q ) <_ ( E x. U ) /\\ ( Q x. ( E x. U ) ) <_ ( 1 - Q ) ) )')
    th = st([rest], 'simpld', '( T e. RR /\\ U <_ T )'); h56 = st([rest], 'simprd', '( ( 1 - Q ) <_ ( E x. U ) /\\ ( Q x. ( E x. U ) ) <_ ( 1 - Q ) )')
    tr = st([th], 'simpld', 'T e. RR'); ut = st([th], 'simprd', 'U <_ T')
    h5 = st([h56], 'simpld', '( 1 - Q ) <_ ( E x. U )'); h6 = st([h56], 'simprd', '( Q x. ( E x. U ) ) <_ ( 1 - Q )')
    eur = st([er, ur], 'remulcld', '( E x. U ) e. RR')
    h7 = st([er, ur, e0, u0], 'mulge0d', '0 <_ ( E x. U )')
    return dict(st=st, qr=qr, q0=q0, er=er, e0=e0, ur=ur, u0=u0, tr=tr, ut=ut, h5=h5, h6=h6, eur=eur, h7=h7,
                leaves={'Q': qr, 'E': er, 'U': ur, 'T': tr})


def bvchordlem3():
    w = W('bvchordlem3', 'The upper chord inequality of the kernel: s - q ( s - u ) <= ( 1 + E s ) u, '
                         'from 1 - q <= E u (certificate h5 ( T - U ) + ( E U ) U).')
    f = chfacts(w)
    goal = '( T - ( Q x. ( T - U ) ) ) <_ ( ( 1 + ( E x. T ) ) x. U )'
    nlinarith(w, ANTE_CH, [f['h5'], f['ut'], f['h7'], f['u0']], goal, leaves=f['leaves'],
              cert={(f['h5'], f['ut']): 1, (f['h7'], f['u0']): 1}, name='qed')
    return w


def bvchordlem2():
    w = W('bvchordlem2', 'The lower chord inequality of the kernel: q ( 1 + E ( s - u ) ) u <= s - q ( s - u ), '
                         'from q E u <= 1 - q (certificate h6 ( T - U ) + U ( 1 - Q )).')
    f = chfacts(w)
    st = f['st']
    h8 = st([f['qr'], f['eur'], f['q0'], f['h7']], 'mulge0d', '0 <_ ( Q x. ( E x. U ) )')
    q1 = linarith(w, ANTE_CH, [f['h6'], h8], 'Q <_ 1', leaves={'Q': f['qr'], '( Q x. ( E x. U ) )': st([f['qr'], f['eur']], 'remulcld', '( Q x. ( E x. U ) ) e. RR')})
    goal = '( ( Q x. ( 1 + ( E x. ( T - U ) ) ) ) x. U ) <_ ( T - ( Q x. ( T - U ) ) )'
    nlinarith(w, ANTE_CH, [f['h6'], f['ut'], f['u0'], q1], goal, leaves=f['leaves'],
              cert={(f['h6'], f['ut']): 1, (f['u0'], q1): 1}, name='qed')
    return w


def bvchordlem4():
    w = W('bvchordlem4', 'The power of K + 1 as the power of K times the exponential of the log gap: '
                         '( K + 1 ) ^c -u E = ( K ^c -u E ) exp ( -u ( E log ( ( K + 1 ) / K ) ) ).')
    A = '( %s /\\ K e. NN )' % HS
    st = mkst(w, A)
    sr = st([st([], 'simpl', HS)], 'simpld', 'S e. RR')
    er = st([sr, st([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % E); ec = st([er], 'recnd', '%s e. CC' % E)
    ner = st([er], 'renegcld', '%s e. RR' % NE); nec = st([ner], 'recnd', '%s e. CC' % NE)
    kf = kfacts(w, A, st([], 'simpr', 'K e. NN'), 'K')
    Q = '( ( K + 1 ) / K )'
    qrp = st([kf['p1rp'], kf['rp']], 'rpdivcld', '%s e. RR+' % Q)
    qr = st([qrp], 'rpred', '%s e. RR' % Q); qc = st([qrp], 'rpcnd', '%s e. CC' % Q); qne = st([qrp], 'rpne0d', '%s =/= 0' % Q); q0 = st([qrp], 'rpge0d', '0 <_ %s' % Q)
    can = st([kf['p1cc'], kf['cc'], kf['ne']], 'divcan2d', '( K x. %s ) = ( K + 1 )' % Q)
    e1 = st([st([can], 'eqcomd', '( K + 1 ) = ( K x. %s )' % Q)], 'oveq1d', '%s = ( ( K x. %s ) ^c %s )' % (CX(P1('K')), Q, NE))
    e2 = st([kf['re'], st([kf['rp']], 'rpge0d', '0 <_ K'), qr, q0, nec], 'mulcxpd', '( ( K x. %s ) ^c %s ) = ( %s x. ( %s ^c %s ) )' % (Q, NE, CX('K'), Q, NE))
    e3 = st([qc, qne, nec], 'cxpefd', '( %s ^c %s ) = ( exp ` ( %s x. ( log ` %s ) ) )' % (Q, NE, NE, Q))
    lqc = st([st([qrp], 'relogcld', '( log ` %s ) e. RR' % Q)], 'recnd', '( log ` %s ) e. CC' % Q)
    e4 = st([ec, lqc], 'mulneg1d', '( %s x. ( log ` %s ) ) = -u ( %s x. %s )' % (NE, Q, E, ELL('K')))
    e5 = st([e3, st([e4], 'fveq2d', '( exp ` ( %s x. ( log ` %s ) ) ) = ( exp ` -u ( %s x. %s ) )' % (NE, Q, E, ELL('K')))], 'eqtrd',
            '( %s ^c %s ) = ( exp ` -u ( %s x. %s ) )' % (Q, NE, E, ELL('K')))
    e6 = st([e2, st([e5], 'oveq2d', '( %s x. ( %s ^c %s ) ) = ( %s x. ( exp ` -u ( %s x. %s ) ) )' % (CX('K'), Q, NE, CX('K'), E, ELL('K')))], 'eqtrd',
            '( ( K x. %s ) ^c %s ) = ( %s x. ( exp ` -u ( %s x. %s ) ) )' % (Q, NE, CX('K'), E, ELL('K')))
    w.qed([e1, e6], 'eqtrd', '( %s -> %s = ( %s x. ( exp ` -u ( %s x. %s ) ) ) )' % (A, CX(P1('K')), CX('K'), E, ELL('K')))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvefge1p', 'bvexpl1', 'bvexpl2', 'bvchordlem3', 'bvchordlem2', 'bvchordlem4']:
        globals()[f]().run()
