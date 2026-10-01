"""Sortie ZD1: the values of the definitions df-bvlam, df-bva, and zdl2star (I4* at bvA)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import Closure, lift


def cg(w, expr, v, V):
    """( v = V -> expr = expr[V/v] )"""
    idv = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, V, v, V))
    st, new = w.congr(expr, {v: V}, '%s = %s' % (v, V), {v: idv})
    return st


def bvlamval():
    w = W('bvlamval', "Value of the Barban-Vehov weight operation: ( A bvLam B ) is the function on NN with value "
                      "mmu ( z ) ( log+ ( B / z ) - log+ ( A / z ) ) / log ( B / A ) (Lean bvLam, Detector.lean).")
    Sa = lambda a, b: '( z e. NN |-> ( ( ( mmu ` z ) x. ( %s - %s ) ) / ( log ` ( %s / %s ) ) ) )' % (
        PL('( %s / z )' % b), PL('( %s / z )' % a), b, a)
    ante = '( A e. V /\\ B e. W )'
    # x = a -> R = G ; y = b -> G = S
    e1 = cg(w, Sa('a', 'b'), 'a', 'A')
    e2 = cg(w, Sa('A', 'b'), 'b', 'B')
    df = w.s([], 'df-bvlam', 'bvLam = ( a e. _V , b e. _V |-> %s )' % Sa('a', 'b'))
    ex = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % Sa('A', 'B'))
    ov = w.s([e1, e2, df, ex], 'ovmpo', '( ( A e. _V /\\ B e. _V ) -> ( A bvLam B ) = %s )' % Sa('A', 'B'))
    va = w.s([], 'elex', '( A e. V -> A e. _V )'); vb = w.s([], 'elex', '( B e. W -> B e. _V )')
    both = w.s([va, vb], 'anim12i', '( %s -> ( A e. _V /\\ B e. _V ) )' % ante)
    w.qed([both, ov], 'syl', STATEMENTS['bvlamval'])
    return w


def bvaval():
    w = W('bvaval', "Value of the Barban-Vehov divisor sum: ( ( A bvA B ) ` N ) is the sum of ( ( A bvLam B ) ` d ) over "
                    "the divisors d of N (Lean bvA, Detector.lean).")
    Sa = lambda a, b: '( n e. NN |-> sum_ d e. { x e. NN | x || n } ( ( %s bvLam %s ) ` d ) )' % (a, b)
    ante = '( ( A e. V /\\ B e. W ) /\\ N e. NN )'
    e1 = cg(w, Sa('a', 'b'), 'a', 'A')
    e2 = cg(w, Sa('A', 'b'), 'b', 'B')
    df = w.s([], 'df-bva', 'bvA = ( a e. _V , b e. _V |-> %s )' % Sa('a', 'b'))
    ex = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % Sa('A', 'B'))
    ov = w.s([e1, e2, df, ex], 'ovmpo', '( ( A e. _V /\\ B e. _V ) -> ( A bvA B ) = %s )' % Sa('A', 'B'))
    va = w.s([], 'elex', '( A e. V -> A e. _V )'); vb = w.s([], 'elex', '( B e. W -> B e. _V )')
    both = w.s([va, vb], 'anim12i', '( ( A e. V /\\ B e. W ) -> ( A e. _V /\\ B e. _V ) )')
    ovA = w.s([both, ov], 'syl', '( ( A e. V /\\ B e. W ) -> ( A bvA B ) = %s )' % Sa('A', 'B'))
    ovA2 = w.s([ovA], 'adantr', '( %s -> ( A bvA B ) = %s )' % (ante, Sa('A', 'B')))
    fv = w.s([ovA2], 'fveq1d', '( %s -> ( ( A bvA B ) ` N ) = ( %s ` N ) )' % (ante, Sa('A', 'B')))
    body = 'sum_ d e. { x e. NN | x || N } ( ( A bvLam B ) ` d )'
    e3 = cg(w, 'sum_ d e. { x e. NN | x || n } ( ( A bvLam B ) ` d )', 'n', 'N')
    eq = w.s([], 'eqid', '%s = %s' % (Sa('A', 'B'), Sa('A', 'B')))
    fm = w.s([e3, eq, w.s([], 'sumex', '%s e. _V' % body)], 'fvmpt', '( N e. NN -> ( %s ` N ) = %s )' % (Sa('A', 'B'), body))
    fm2 = w.s([fm], 'adantl', '( %s -> ( %s ` N ) = %s )' % (ante, Sa('A', 'B'), body))
    w.qed([fv, fm2], 'eqtrd', STATEMENTS['bvaval'])
    return w


def zdl2star():
    w = W('zdl2star', "I4* at the definition (Lean bvL2_star_uncond, as ZeroDensity.lean line 413 uses it): for 1 < D, "
                      "100 <_ z1 = D ^c ( 31 / 50 ) <_ Y and 1 / 2 <_ T <_ 1, sum_ n <= Y n ^c ( 1 - 2 T ) ( ( z1 bvA z2 ) ` n ) ^ 2 "
                      "<_ 500000 Y ^c ( 2 - 2 T ) log Y / ( log D / 100 ) (bvl2star with its weight discharged by bvlamval).")
    L = '( %s bvLam %s )' % (Z1, Z2)
    BVLz = lambda y: '( ( ( mmu ` %s ) x. ( %s - %s ) ) / ( log ` ( %s / %s ) ) )' % (y, PL('( %s / %s )' % (Z2, y)), PL('( %s / %s )' % (Z1, y)), Z2, Z1)
    ex1 = w.s([], 'ovex', '%s e. _V' % Z1); ex2 = w.s([], 'ovex', '%s e. _V' % Z2)
    lv = w.s([ex1, ex2, w.inst('bvlamval')], 'mp2an', '%s = ( z e. NN |-> %s )' % (L, BVLz('z')))
    h1 = w.s([], 'eqid', '%s = %s' % (Z1, Z1)); h2 = w.s([], 'eqid', '%s = %s' % (Z2, Z2))
    HD = '( ( D e. RR /\\ 1 < D ) /\\ ( ; ; 1 0 0 <_ %s /\\ ( Y e. RR /\\ %s <_ Y ) ) )' % (Z1, Z1)
    A = '( %s /\\ ( T e. RR /\\ ( ( 1 / 2 ) <_ T /\\ T <_ 1 ) ) )' % HD
    R = '( 1 ... ( |_ ` Y ) )'
    DVn = '{ x e. NN | x || n }'
    SL = 'sum_ d e. %s ( %s ` d )' % (DVn, L)
    RHS = '( ( ( %s x. ( Y ^c %s ) ) x. ( log ` Y ) ) / %s )' % (C5, B2, ELLD)
    main = w.s([h1, h2, lv], 'bvl2star', '( %s -> sum_ n e. %s ( ( n ^c %s ) x. ( %s ^ 2 ) ) <_ %s )' % (A, R, B1, SL, RHS))
    AF = '( %s /\\ n e. %s )' % (A, R)
    fnn = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (AF, R)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AF)
    pr = w.s([ex1, ex2], 'pm3.2i', '( %s e. _V /\\ %s e. _V )' % (Z1, Z2))
    bv = w.s([pr, w.inst('bvaval')], 'mpan', '( n e. NN -> %s = %s )' % (BA('n'), SL))
    e = w.s([fnn, bv], 'syl', '( %s -> %s = %s )' % (AF, BA('n'), SL))
    e2 = w.s([e], 'oveq1d', '( %s -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (AF, BA('n'), SL))
    e3 = w.s([e2], 'oveq2d', '( %s -> ( ( n ^c %s ) x. ( %s ^ 2 ) ) = ( ( n ^c %s ) x. ( %s ^ 2 ) ) )' % (AF, B1, BA('n'), B1, SL))
    e4 = w.s([e3], 'sumeq2dv', '( %s -> sum_ n e. %s ( ( n ^c %s ) x. ( %s ^ 2 ) ) = sum_ n e. %s ( ( n ^c %s ) x. ( %s ^ 2 ) ) )'
             % (A, R, B1, BA('n'), R, B1, SL))
    w.qed([e4, main], 'eqbrtrd', STATEMENTS['zdl2star'])
    return w



def bvlamre():
    w = W('bvlamre', "The Barban-Vehov weight is real for 0 < A < B.")
    ante = '( %s /\\ N e. NN )' % HABP
    st = mkst(w, ante)
    h = st([], 'simpl', HABP)
    arp = st([h], 'simp1d', 'A e. RR+'); brp = st([h], 'simp2d', 'B e. RR+'); ab = st([h], 'simp3d', 'A < B')
    nn = st([], 'simpr', 'N e. NN')
    L = '( A bvLam B )'
    MP = '( z e. NN |-> %s )' % BVL('z')
    lv = st([arp, brp, w.inst('bvlamval')], 'syl2anc', '%s = %s' % (L, MP))
    val, _v = mpv(w, ante, 'z', 'NN', BVL('z'), 'N', nn)
    ev = st([st([lv], 'fveq1d', '( %s ` N ) = ( %s ` N )' % (L, MP)), val], 'eqtrd', '( %s ` N ) = %s' % (L, BVL('N')))
    nrp = st([nn], 'nnrpd', 'N e. RR+')
    br_ = st([brp], 'rpred', 'B e. RR'); ar_ = st([arp], 'rpred', 'A e. RR')
    q1 = st([st([], '1red', '1 e. RR'), br_, arp], 'ltmuldivd', '( ( 1 x. A ) < B <-> 1 < ( B / A ) )')
    g1 = st([st([st([st([ar_], 'recnd', 'A e. CC')], 'mullidd', '( 1 x. A ) = A'), ab], 'eqbrtrd', '( 1 x. A ) < B'), q1], 'mpbid', '1 < ( B / A )')
    lrp = sy2(w, ante, st([st([brp, arp], 'rpdivcld', '( B / A ) e. RR+')], 'rpred', '( B / A ) e. RR'), g1, 'rplogcl', '( log ` ( B / A ) ) e. RR+')
    c = Closure(w, ante, {'N': ('NN', nn), '( B / N )': ('RR+', st([brp, nrp], 'rpdivcld', '( B / N ) e. RR+')),
                          '( A / N )': ('RR+', st([arp, nrp], 'rpdivcld', '( A / N ) e. RR+')), '( log ` ( B / A ) )': ('RR+', lrp)})
    r = c.mem(BVL('N'), 'RR')
    w.qed([ev, r], 'eqeltrd', STATEMENTS['bvlamre'])
    return w


def bvare():
    w = W('bvare', "The Barban-Vehov divisor sum is real for 0 < A < B.")
    ante = '( %s /\\ N e. NN )' % HABP
    st = mkst(w, ante)
    h = st([], 'simpl', HABP)
    arp = st([h], 'simp1d', 'A e. RR+'); brp = st([h], 'simp2d', 'B e. RR+')
    nn = st([], 'simpr', 'N e. NN')
    SL = 'sum_ d e. %s ( ( A bvLam B ) ` d )' % DV('N')
    ev = st([arp, brp, nn, w.inst('bvaval')], 'syl21anc', '( ( A bvA B ) ` N ) = %s' % SL)
    fin = sy(w, ante, nn, 'dvdsfi', '%s e. Fin' % DV('N'))
    AD = '( %s /\\ d e. %s )' % (ante, DV('N'))
    elr = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || N ) )' % DV('N'))
    dn = w.s([w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (AD, DV('N'))), elr], 'sylib', '( %s -> ( d e. NN /\\ d || N ) )' % AD)], 'simpld', '( %s -> d e. NN )' % AD)
    ld = w.s([lift(w, h, AD), dn, w.inst('bvlamre')], 'syl2anc', '( %s -> ( ( A bvLam B ) ` d ) e. RR )' % AD)
    r = st([fin, ld], 'fsumrecl', '%s e. RR' % SL)
    w.qed([ev, r], 'eqeltrd', STATEMENTS['bvare'])
    return w


def zdz12():
    w = W('zdz12', "The Barban-Vehov cuts z1 = D ^c ( 31 / 50 ) < z2 = D ^c ( 63 / 100 ) are positive reals for 1 < D.")
    ante = '( D e. RR /\\ 1 < D )'
    st = mkst(w, ante)
    dr = st([], 'simpl', 'D e. RR'); d1 = st([], 'simpr', '1 < D')
    drp = st([dr, linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    a = st([drp, litr(w, ante, C31)], 'rpcxpcld', '%s e. RR+' % Z1)
    b = st([drp, litr(w, ante, C63)], 'rpcxpcld', '%s e. RR+' % Z2)
    lt = st([litle(w, ante, C31, C63, strict=True), st([dr, d1, litr(w, ante, C31), litr(w, ante, C63)], 'cxpltd', '( %s < %s <-> %s < %s )' % (C31, C63, Z1, Z2))],
            'mpbid', '%s < %s' % (Z1, Z2))
    w.qed([a, b, lt], '3jca', STATEMENTS['zdz12'])
    return w


def zdbvare():
    w = W('zdbvare', "The weight's divisor sum at the Detector cuts is real.")
    ante = '( ( D e. RR /\\ 1 < D ) /\\ N e. NN )'
    z = w.s([w.s([], 'simpl', '( %s -> ( D e. RR /\\ 1 < D ) )' % ante), w.inst('zdz12')], 'syl', '( %s -> ( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s ) )' % (ante, Z1, Z2, Z1, Z2))
    w.qed([z, w.s([], 'simpr', '( %s -> N e. NN )' % ante), w.inst('bvare')], 'syl2anc', STATEMENTS['zdbvare'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvlamval', 'bvaval', 'zdl2star']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
