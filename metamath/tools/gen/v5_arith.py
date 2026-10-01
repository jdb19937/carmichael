"""Sortie V5: the pure real arithmetic of SmoothShifted.lean
(smshlog, smshdiv, smshe).  MM_DB=sorties/v5.mm python3 tools/gen/v5_arith.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from lin import linarith
from cl import lift
import num
import v5lib
from v5lib import mkst, lit, Proj, E3, HALF

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    ok = w.run()
    assert ok, w.label
    return ok


# ------------------------------------------------------------------ smshlog
def smshlog():
    w = W('smshlog', 'The logarithm of a number at least ( X ^c ( 1 - E ) ) / 2 is at least a quarter of '
                     'the logarithm of X, for E <_ 1 / 2 and log X >= 4 (Lean: hlogt of smooth_shifted_weak).')
    A = v5lib.STATEMENTS['smshlog'].split(' -> ( ( log')[0][2:]
    st = mkst(w, A); pj = Proj(w, A)
    L = '( log ` X )'
    xrp = pj('X e. RR+'); l4 = pj('4 <_ %s' % L)
    ere = pj('E e. RR'); eh = pj('E <_ %s' % HALF)
    zre = pj('Z e. RR')
    AX = '( X ^c ( 1 - E ) )'
    az = pj('( %s / 2 ) <_ Z' % AX)
    lre = st([xrp], 'relogcld', '%s e. RR' % L)
    ome = st([st([], '1red', '1 e. RR'), ere], 'resubcld', '( 1 - E ) e. RR')
    arp = st([xrp, ome], 'rpcxpcld', '%s e. RR+' % AX)
    a2rp = st([arp], 'rphalfcld', '( %s / 2 ) e. RR+' % AX)
    a2re = st([a2rp], 'rpred', '( %s / 2 ) e. RR' % AX)
    zgt = st([st([], '0red', '0 e. RR'), a2re, zre, st([a2rp], 'rpgt0d', '0 < ( %s / 2 )' % AX), az], 'ltletrd', '0 < Z')
    zrp = st([zre, zgt], 'elrpd', 'Z e. RR+')
    h1 = st([az, st([a2rp, zrp], 'logled', '( ( %s / 2 ) <_ Z <-> ( log ` ( %s / 2 ) ) <_ ( log ` Z ) )' % (AX, AX))],
            'mpbid', '( log ` ( %s / 2 ) ) <_ ( log ` Z )' % AX)
    two = st([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')
    h2 = st([arp, two, w.inst('relogdiv')], 'syl2anc', '( log ` ( %s / 2 ) ) = ( ( log ` %s ) - ( log ` 2 ) )' % (AX, AX))
    h3 = st([xrp, ome], 'logcxpd', '( log ` %s ) = ( ( 1 - E ) x. %s )' % (AX, L))
    lcn = st([lre], 'recnd', '%s e. CC' % L)
    h4a = st([st([], '1cnd', '1 e. CC'), st([ere], 'recnd', 'E e. CC'), lcn], 'subdird',
             '( ( 1 - E ) x. %s ) = ( ( 1 x. %s ) - ( E x. %s ) )' % (L, L, L))
    h4b = st([st([lcn], 'mullidd', '( 1 x. %s ) = %s' % (L, L))], 'oveq1d',
             '( ( 1 x. %s ) - ( E x. %s ) ) = ( %s - ( E x. %s ) )' % (L, L, L, L))
    h4 = st([h4a, h4b], 'eqtrd', '( ( 1 - E ) x. %s ) = ( %s - ( E x. %s ) )' % (L, L, L))
    l0 = st([st([], '0red', '0 e. RR'), lit(w, A, '4', 'RR'), lre, lit(w, A, '4', 'ge0'), l4], 'letrd', '0 <_ %s' % L)
    h5 = st([ere, lit(w, A, HALF, 'RR'), lre, l0, eh], 'lemul1ad', '( E x. %s ) <_ ( %s x. %s )' % (L, HALF, L))
    h6 = st([w.s([], 'log2le1', '( log ` 2 ) < 1')], 'a1i', '( log ` 2 ) < 1')
    la2 = st([a2rp], 'relogcld', '( log ` ( %s / 2 ) ) e. RR' % AX)
    lz = st([zrp], 'relogcld', '( log ` Z ) e. RR')
    la = st([arp], 'relogcld', '( log ` %s ) e. RR' % AX)
    l2 = st([two], 'relogcld', '( log ` 2 ) e. RR')
    oml = st([ome, lre], 'remulcld', '( ( 1 - E ) x. %s ) e. RR' % L)
    el = st([ere, lre], 'remulcld', '( E x. %s ) e. RR' % L)
    linarith(w, A, [h1, h2, h3, h4, h5, h6, l4], '( %s / 4 ) <_ ( log ` Z )' % L,
             leaves={'( log ` ( %s / 2 ) )' % AX: la2, '( log ` Z )': lz, '( log ` %s )' % AX: la,
                     '( log ` 2 )': l2, '( ( 1 - E ) x. %s )' % L: oml, '( E x. %s )' % L: el, L: lre},
             name='qed')
    return run(w)


# ------------------------------------------------------------------ smshdiv
def smshdiv():
    w = W('smshdiv', 'The per-cofactor arithmetic of the twin-type bound: the sieve bound at Z <_ X / N with '
                     'log Z >= ( log X ) / 4 is at most 16 C X / ( log X ) ^ 2 times R / N (Lean: h1 and the calc of hterm).')
    A = v5lib.STATEMENTS['smshdiv'].split(' -> ( ( ( C x. R')[0][2:]
    st = mkst(w, A); pj = Proj(w, A)
    cre, c0 = pj('C e. RR'), pj('0 <_ C'); rre, r0 = pj('R e. RR'), pj('0 <_ R')
    nre, n0 = pj('N e. RR'), pj('0 < N'); xre, x0 = pj('X e. RR'), pj('0 <_ X')
    lre, l0 = pj('L e. RR'), pj('0 < L'); wre, lw = pj('W e. RR'), pj('( L / 4 ) <_ W')
    zre, z0, zxn = pj('Z e. RR'), pj('0 <_ Z'), pj('Z <_ ( X / N )')
    P, Y, D = '( C x. R )', '( X / N )', '( ( L ^ 2 ) / ; 1 6 )'
    KK = v5lib.K('C', 'X', 'L')
    nrp = st([nre, n0], 'elrpd', 'N e. RR+'); lrp = st([lre, l0], 'elrpd', 'L e. RR+')
    pre = st([cre, rre], 'remulcld', '%s e. RR' % P); p0 = st([cre, rre, c0, r0], 'mulge0d', '0 <_ %s' % P)
    yre = st([xre, nrp], 'rerpdivcld', '%s e. RR' % Y)
    four = st([w.s([], '4rp', '4 e. RR+')], 'a1i', '4 e. RR+')
    l4rp = st([lrp, four], 'rpdivcld', '( L / 4 ) e. RR+')
    l4re = st([l4rp], 'rpred', '( L / 4 ) e. RR')
    w0 = st([st([], '0red', '0 e. RR'), l4re, wre, st([l4rp], 'rpgt0d', '0 < ( L / 4 )'), lw], 'ltletrd', '0 < W')
    wrp = st([wre, w0], 'elrpd', 'W e. RR+')
    two = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    w2rp = st([wrp, two], 'rpexpcld', '( W ^ 2 ) e. RR+')
    l2rp = st([lrp, two], 'rpexpcld', '( L ^ 2 ) e. RR+')
    s16 = st([num.fact(w, '; 1 6', 'RR+')], 'a1i', '; 1 6 e. RR+')
    drp = st([l2rp, s16], 'rpdivcld', '%s e. RR+' % D)
    # D <_ W ^ 2
    sq = st([st([st([l4re, st([l4rp], 'rpge0d', '0 <_ ( L / 4 )')], 'jca', '( ( L / 4 ) e. RR /\\ 0 <_ ( L / 4 ) )'),
                 st([wre, st([wrp], 'rpge0d', '0 <_ W')], 'jca', '( W e. RR /\\ 0 <_ W )')], 'jca',
                '( ( ( L / 4 ) e. RR /\\ 0 <_ ( L / 4 ) ) /\\ ( W e. RR /\\ 0 <_ W ) )'), w.inst('le2sq')], 'syl',
            '( ( L / 4 ) <_ W <-> ( ( L / 4 ) ^ 2 ) <_ ( W ^ 2 ) )')
    sq2 = st([lw, sq], 'mpbid', '( ( L / 4 ) ^ 2 ) <_ ( W ^ 2 )')
    lcn = st([lre], 'recnd', 'L e. CC')
    fcn = st([w.s([], '4cn', '4 e. CC')], 'a1i', '4 e. CC'); fne = st([w.s([], '4ne0', '4 =/= 0')], 'a1i', '4 =/= 0')
    sqd = st([lcn, fcn, fne], 'sqdivd', '( ( L / 4 ) ^ 2 ) = ( ( L ^ 2 ) / ( 4 ^ 2 ) )')
    sq4 = w.s([w.s([w.s([], '4cn', '4 e. CC'), w.inst('sqval')], 'ax-mp', '( 4 ^ 2 ) = ( 4 x. 4 )'), num.mul_nat(w, 4, 4)], 'eqtri',
              '( 4 ^ 2 ) = ; 1 6')
    sqe = st([st([sq4], 'a1i', '( 4 ^ 2 ) = ; 1 6')], 'oveq2d',
             '( ( L ^ 2 ) / ( 4 ^ 2 ) ) = %s' % D)
    sqD = st([sqd, sqe], 'eqtrd', '( ( L / 4 ) ^ 2 ) = %s' % D)
    dw = st([sqD, sq2], 'eqbrtrrd', '%s <_ ( W ^ 2 )' % D)
    # s1: ( P Z ) / W^2 <_ ( P Z ) / D
    pz = st([pre, zre], 'remulcld', '( %s x. Z ) e. RR' % P)
    pz0 = st([pre, zre, p0, z0], 'mulge0d', '0 <_ ( %s x. Z )' % P)
    s1 = st([drp, w2rp, pz, pz0, dw], 'lediv2ad', '( ( %s x. Z ) / ( W ^ 2 ) ) <_ ( ( %s x. Z ) / %s )' % (P, P, D))
    # s2: ( P Z ) / D <_ ( P Y ) / D
    pzy = st([zre, yre, pre, p0, zxn], 'lemul2ad', '( %s x. Z ) <_ ( %s x. %s )' % (P, P, Y))
    py = st([pre, yre], 'remulcld', '( %s x. %s ) e. RR' % (P, Y))
    s2 = st([pz, py, drp, pzy], 'lediv1dd', '( ( %s x. Z ) / %s ) <_ ( ( %s x. %s ) / %s )' % (P, D, P, Y, D))
    # s3: the identity ( P Y ) / D = K ( R / N )
    pycn = st([py], 'recnd', '( %s x. %s ) e. CC' % (P, Y))
    l2cn = st([l2rp], 'rpcnd', '( L ^ 2 ) e. CC'); l2ne = st([l2rp], 'rpne0d', '( L ^ 2 ) =/= 0')
    c16 = st([num.cc(w, '; 1 6')], 'a1i', '; 1 6 e. CC'); n16 = st([num.fact(w, '; 1 6', 'ne0')], 'a1i', '; 1 6 =/= 0')
    e1 = st([pycn, l2cn, c16, l2ne, n16], 'divdiv2d',
            '( ( %s x. %s ) / %s ) = ( ( ( %s x. %s ) x. ; 1 6 ) / ( L ^ 2 ) )' % (P, Y, D, P, Y))
    e2 = st([pycn, c16], 'mulcomd', '( ( %s x. %s ) x. ; 1 6 ) = ( ; 1 6 x. ( %s x. %s ) )' % (P, Y, P, Y))
    xcn = st([xre], 'recnd', 'X e. CC'); rcn = st([rre], 'recnd', 'R e. CC'); ccn = st([cre], 'recnd', 'C e. CC')
    ncn = st([nre], 'recnd', 'N e. CC'); nne = st([n0], 'gt0ne0d', 'N =/= 0')
    e3 = st([xcn, ncn, nne], 'divrecd', '( X / N ) = ( X x. ( 1 / N ) )')
    e4 = st([rcn, ncn, nne], 'divrecd', '( R / N ) = ( R x. ( 1 / N ) )')
    rn = st([ncn, nne], 'reccld', '( 1 / N ) e. CC')
    e5 = st([ccn, rcn, xcn, rn], 'mul4d',
            '( ( C x. R ) x. ( X x. ( 1 / N ) ) ) = ( ( C x. X ) x. ( R x. ( 1 / N ) ) )')
    e6 = st([e3], 'oveq2d', '( %s x. %s ) = ( ( C x. R ) x. ( X x. ( 1 / N ) ) )' % (P, Y))
    e6b = st([e6, e5], 'eqtrd', '( %s x. %s ) = ( ( C x. X ) x. ( R x. ( 1 / N ) ) )' % (P, Y))
    e7 = st([st([e4], 'eqcomd', '( R x. ( 1 / N ) ) = ( R / N )')], 'oveq2d',
            '( ( C x. X ) x. ( R x. ( 1 / N ) ) ) = ( ( C x. X ) x. ( R / N ) )')
    e7b = st([e6b, e7], 'eqtrd', '( %s x. %s ) = ( ( C x. X ) x. ( R / N ) )' % (P, Y))
    e8 = st([e7b], 'oveq2d', '( ; 1 6 x. ( %s x. %s ) ) = ( ; 1 6 x. ( ( C x. X ) x. ( R / N ) ) )' % (P, Y))
    cxcn = st([ccn, xcn], 'mulcld', '( C x. X ) e. CC'); rncn = st([rcn, ncn, nne], 'divcld', '( R / N ) e. CC')
    e9 = st([st([c16, cxcn, rncn], 'mulassd',
                '( ( ; 1 6 x. ( C x. X ) ) x. ( R / N ) ) = ( ; 1 6 x. ( ( C x. X ) x. ( R / N ) ) )')], 'eqcomd',
            '( ; 1 6 x. ( ( C x. X ) x. ( R / N ) ) ) = ( ( ; 1 6 x. ( C x. X ) ) x. ( R / N ) )')
    e10 = st([st([e2, e8], 'eqtrd', '( ( %s x. %s ) x. ; 1 6 ) = ( ; 1 6 x. ( ( C x. X ) x. ( R / N ) ) )' % (P, Y)), e9],
             'eqtrd', '( ( %s x. %s ) x. ; 1 6 ) = ( ( ; 1 6 x. ( C x. X ) ) x. ( R / N ) )' % (P, Y))
    e11 = st([e10], 'oveq1d',
             '( ( ( %s x. %s ) x. ; 1 6 ) / ( L ^ 2 ) ) = ( ( ( ; 1 6 x. ( C x. X ) ) x. ( R / N ) ) / ( L ^ 2 ) )' % (P, Y))
    e12 = st([st([c16, cxcn], 'mulcld', '( ; 1 6 x. ( C x. X ) ) e. CC'), rncn, l2cn, l2ne], 'div23d',
             '( ( ( ; 1 6 x. ( C x. X ) ) x. ( R / N ) ) / ( L ^ 2 ) ) = ( %s x. ( R / N ) )' % KK)
    s3 = st([st([e1, e11], 'eqtrd',
                '( ( %s x. %s ) / %s ) = ( ( ( ; 1 6 x. ( C x. X ) ) x. ( R / N ) ) / ( L ^ 2 ) )' % (P, Y, D)), e12],
            'eqtrd', '( ( %s x. %s ) / %s ) = ( %s x. ( R / N ) )' % (P, Y, D, KK))
    q1 = st([pz, w2rp], 'rerpdivcld', '( ( %s x. Z ) / ( W ^ 2 ) ) e. RR' % P)
    q2 = st([pz, drp], 'rerpdivcld', '( ( %s x. Z ) / %s ) e. RR' % (P, D))
    q3 = st([py, drp], 'rerpdivcld', '( ( %s x. %s ) / %s ) e. RR' % (P, Y, D))
    s12 = st([q1, q2, q3, s1, s2], 'letrd', '( ( %s x. Z ) / ( W ^ 2 ) ) <_ ( ( %s x. %s ) / %s )' % (P, P, Y, D))
    w.qed([s12, s3], 'breqtrd', '( %s -> ( ( %s x. Z ) / ( W ^ 2 ) ) <_ ( %s x. ( R / N ) ) )' % (A, P, KK))
    return run(w)


# ------------------------------------------------------------------ smshe
def smshe():
    w = W('smshe', 'The smoothness exponent at twin constant C: E = 1 / ( 2 + 200 e^3 C ) is positive, at most '
                   '1 / 2, and satisfies 96 C e^3 E <_ 1 / 2 (Lean: hEpos, hE2, h96 of smooth_shifted_weak).')
    A = '( C e. RR /\\ 0 < C )'
    st = mkst(w, A)
    D = '( 2 + ( ; ; 2 0 0 x. ( %s x. C ) ) )' % E3
    EE = v5lib.EE('C')
    cre = st([], 'simpl', 'C e. RR'); c0 = st([], 'simpr', '0 < C')
    crp = st([cre, c0], 'elrpd', 'C e. RR+')
    e3rp = st([lit(w, A, '3', 'RR')], 'rpefcld', '%s e. RR+' % E3)
    ecrp = st([e3rp, crp], 'rpmulcld', '( %s x. C ) e. RR+' % E3)
    ecre = st([ecrp], 'rpred', '( %s x. C ) e. RR' % E3)
    t200 = st([num.fact(w, '; ; 2 0 0', 'RR+')], 'a1i', '; ; 2 0 0 e. RR+')
    drp = st([st([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), st([t200, ecrp], 'rpmulcld',
             '( ; ; 2 0 0 x. ( %s x. C ) ) e. RR+' % E3)], 'rpaddcld', '%s e. RR+' % D)
    dre = st([drp], 'rpred', '%s e. RR' % D)
    erp = st([drp], 'rpreccld', '%s e. RR+' % EE)
    ere = st([erp], 'rpred', '%s e. RR' % EE); e0 = st([erp], 'rpgt0d', '0 < %s' % EE)
    ec0 = st([ecrp], 'rpge0d', '0 <_ ( %s x. C )' % E3)
    d2 = linarith(w, A, [ec0], '2 <_ %s' % D, leaves={'( %s x. C )' % E3: ecre})
    two = st([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')
    eh = st([d2, st([two, drp], 'lerecd', '( 2 <_ %s <-> ( 1 / %s ) <_ ( 1 / 2 ) )' % (D, D))], 'mpbid',
            '%s <_ %s' % (EE, HALF))
    # h96
    cerp = st([crp, e3rp], 'rpmulcld', '( C x. %s ) e. RR+' % E3)
    cecn = st([cerp], 'rpcnd', '( C x. %s ) e. CC' % E3); cere = st([cerp], 'rpred', '( C x. %s ) e. RR' % E3)
    dcn = st([drp], 'rpcnd', '%s e. CC' % D); dne = st([drp], 'rpne0d', '%s =/= 0' % D)
    g1 = st([st([cecn, dcn, dne], 'divrecd', '( ( C x. %s ) / %s ) = ( ( C x. %s ) x. %s )' % (E3, D, E3, EE))],
            'eqcomd', '( ( C x. %s ) x. %s ) = ( ( C x. %s ) / %s )' % (E3, EE, E3, D))
    c96 = st([num.cc(w, '; 9 6')], 'a1i', '; 9 6 e. CC')
    g2 = st([st([c96, cecn, dcn, dne], 'divassd',
                '( ( ; 9 6 x. ( C x. %s ) ) / %s ) = ( ; 9 6 x. ( ( C x. %s ) / %s ) )' % (E3, D, E3, D))], 'eqcomd',
            '( ; 9 6 x. ( ( C x. %s ) / %s ) ) = ( ( ; 9 6 x. ( C x. %s ) ) / %s )' % (E3, D, E3, D))
    g12 = st([st([g1], 'oveq2d', '( ; 9 6 x. ( ( C x. %s ) x. %s ) ) = ( ; 9 6 x. ( ( C x. %s ) / %s ) )' % (E3, EE, E3, D)), g2],
             'eqtrd', '( ; 9 6 x. ( ( C x. %s ) x. %s ) ) = ( ( ; 9 6 x. ( C x. %s ) ) / %s )' % (E3, EE, E3, D))
    n96 = st([lit(w, A, '; 9 6', 'RR'), cere], 'remulcld', '( ; 9 6 x. ( C x. %s ) ) e. RR' % E3)
    g3 = st([n96, lit(w, A, HALF, 'RR'), drp], 'ledivmuld',
            '( ( ( ; 9 6 x. ( C x. %s ) ) / %s ) <_ %s <-> ( ; 9 6 x. ( C x. %s ) ) <_ ( %s x. %s ) )' % (E3, D, HALF, E3, D, HALF))
    com = st([st([e3rp], 'rpcnd', '%s e. CC' % E3), st([cre], 'recnd', 'C e. CC')], 'mulcomd',
             '( %s x. C ) = ( C x. %s )' % (E3, E3))
    ce0 = st([cerp], 'rpge0d', '0 <_ ( C x. %s )' % E3)
    g4 = linarith(w, A, [com, ce0], '( ; 9 6 x. ( C x. %s ) ) <_ ( %s x. %s )' % (E3, D, HALF),
                  leaves={'( %s x. C )' % E3: ecre, '( C x. %s )' % E3: cere})
    h96 = st([g12, st([g4, g3], 'mpbird', '( ( ; 9 6 x. ( C x. %s ) ) / %s ) <_ %s' % (E3, D, HALF))], 'eqbrtrd',
             '( ; 9 6 x. ( ( C x. %s ) x. %s ) ) <_ %s' % (E3, EE, HALF))
    w.qed([st([ere, e0, eh], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ %s )' % (EE, EE, EE, HALF)), h96], 'jca',
          v5lib.STATEMENTS['smshe'])
    return run(w)


if __name__ == '__main__':
    smshlog(); smshdiv(); smshe()
