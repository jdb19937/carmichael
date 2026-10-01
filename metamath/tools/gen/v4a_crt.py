"""Sortie v4a: multiplicativity of the root count in coprime moduli (CRT)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import QF, RT, mkst
from cl import lift

AM = '( M e. NN /\\ ( D e. NN /\\ E e. NN /\\ ( D gcd E ) = 1 ) )'
FZ = '( 0 ..^ ( D x. E ) )'
BB = '( ( 0 ..^ D ) X. ( 0 ..^ E ) )'
PAIRX = '<. ( x mod D ) , ( x mod E ) >.'
FM = '( x e. %s |-> %s )' % (FZ, PAIRX)
Y1 = '( 1st ` y )'
Y2 = '( 2nd ` y )'
CHY = '( D || %s /\\ E || %s )' % (QF(Y1), QF(Y2))


def RTX(A, v='x'):
    return '{ %s e. ( 0 ..^ %s ) | %s || %s }' % (v, A, A, QF(v))


def qfsub(w, Y, x='x'):
    """( x = Y -> ( A || QF( x ) <-> A || QF( Y ) ) ) -- returns the QF equation step"""
    a = w.s([], 'oveq2', '( %s = %s -> ( M x. %s ) = ( M x. %s ) )' % (x, Y, x, Y))
    b = w.s([a], 'oveq1d',
            '( %s = %s -> ( ( M x. %s ) + 1 ) = ( ( M x. %s ) + 1 ) )' % (x, Y, x, Y))
    i = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, Y, x, Y))
    return w.s([i, b], 'oveq12d', '( %s = %s -> %s = %s )' % (x, Y, QF(x), QF(Y)))


def rcmul():
    w = WS('rcmul', 'The number of roots of X ( M X + 1 ) is multiplicative in coprime '
                    'moduli, by the Chinese remainder theorem.')
    st = mkst(w, AM)
    mnn = st([], 'simpl', 'M e. NN')
    mz = st([mnn], 'nnzd', 'M e. ZZ')
    trip = st([], 'simpr', '( D e. NN /\\ E e. NN /\\ ( D gcd E ) = 1 )')
    dnn = st([trip], 'simp1d', 'D e. NN')
    enn = st([trip], 'simp2d', 'E e. NN')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    ez = st([enn], 'nnzd', 'E e. ZZ')
    gcd1 = st([trip], 'simp3d', '( D gcd E ) = 1')
    denn = st([dnn, enn], 'nnmulcld', '( D x. E ) e. NN')
    dez = st([denn], 'nnzd', '( D x. E ) e. ZZ')
    # the CRT bijection
    e1 = w.s([], 'eqid', '%s = %s' % (FZ, FZ))
    e2 = w.s([], 'eqid', '%s = %s' % (BB, BB))
    e3 = w.s([], 'eqid', '%s = %s' % (FM, FM))
    bij = w.s([e1, e2, e3, trip], 'crth', '( %s -> %s : %s -1-1-onto-> %s )' % (AM, FM, FZ, BB))
    # the transported predicate
    AX = '( ( %s /\\ x e. %s ) /\\ y = %s )' % (AM, FZ, PAIRX)
    sx = mkst(w, AX)
    xfzo = sx([sx([], 'simpl', '( %s /\\ x e. %s )' % (AM, FZ))], 'simprd', 'x e. %s' % FZ)
    xz = sx([xfzo, w.inst('elfzoelz')], 'syl', 'x e. ZZ')
    yeq = sx([], 'simpr', 'y = %s' % PAIRX)
    xdex = w.s([], 'ovex', '( x mod D ) e. _V')
    xeex = w.s([], 'ovex', '( x mod E ) e. _V')
    o1 = w.s([xdex, xeex], 'op1st', '( 1st ` %s ) = ( x mod D )' % PAIRX)
    o2 = w.s([xdex, xeex], 'op2nd', '( 2nd ` %s ) = ( x mod E )' % PAIRX)
    f1 = sx([sx([yeq], 'fveq2d', '%s = ( 1st ` %s )' % (Y1, PAIRX)),
             sx([o1], 'a1i', '( 1st ` %s ) = ( x mod D )' % PAIRX)], 'eqtrd',
            '%s = ( x mod D )' % Y1)
    f2 = sx([sx([yeq], 'fveq2d', '%s = ( 2nd ` %s )' % (Y2, PAIRX)),
             sx([o2], 'a1i', '( 2nd ` %s ) = ( x mod E )' % PAIRX)], 'eqtrd',
            '%s = ( x mod E )' % Y2)
    # D || QF( x mod D ) <-> D || QF( x )
    mdfzo = sx([xz, lift(w, dnn, AX), w.inst('zmodfzo')], 'syl2anc', '( x mod D ) e. ( 0 ..^ D )')
    mdz = sx([mdfzo, w.inst('elfzoelz')], 'syl', '( x mod D ) e. ZZ')
    mdid = sx([mdfzo, w.inst('zmodidfzoimp')], 'syl', '( ( x mod D ) mod D ) = ( x mod D )')
    qd = sx([sx([sx([lift(w, dnn, AX), lift(w, mz, AX)], 'jca', '( D e. NN /\\ M e. ZZ )'),
                 sx([mdz, xz], 'jca', '( ( x mod D ) e. ZZ /\\ x e. ZZ )'), mdid], '3jca',
                '( ( D e. NN /\\ M e. ZZ ) /\\ ( ( x mod D ) e. ZZ /\\ x e. ZZ ) /\\ '
                '( ( x mod D ) mod D ) = ( x mod D ) )'), w.inst('quadmod')], 'syl',
            '( D || %s <-> D || %s )' % (QF('( x mod D )'), QF('x')))
    mefzo = sx([xz, lift(w, enn, AX), w.inst('zmodfzo')], 'syl2anc', '( x mod E ) e. ( 0 ..^ E )')
    mez = sx([mefzo, w.inst('elfzoelz')], 'syl', '( x mod E ) e. ZZ')
    meid = sx([mefzo, w.inst('zmodidfzoimp')], 'syl', '( ( x mod E ) mod E ) = ( x mod E )')
    qe = sx([sx([sx([lift(w, enn, AX), lift(w, mz, AX)], 'jca', '( E e. NN /\\ M e. ZZ )'),
                 sx([mez, xz], 'jca', '( ( x mod E ) e. ZZ /\\ x e. ZZ )'), meid], '3jca',
                '( ( E e. NN /\\ M e. ZZ ) /\\ ( ( x mod E ) e. ZZ /\\ x e. ZZ ) /\\ '
                '( ( x mod E ) mod E ) = ( x mod E ) )'), w.inst('quadmod')], 'syl',
            '( E || %s <-> E || %s )' % (QF('( x mod E )'), QF('x')))
    yq1 = sx([f1], 'oveq2d', '( M x. %s ) = ( M x. ( x mod D ) )' % Y1)
    yq1b = sx([sx([yq1], 'oveq1d',
                  '( ( M x. %s ) + 1 ) = ( ( M x. ( x mod D ) ) + 1 )' % Y1)], 'oveq2d',
              '( %s x. ( ( M x. %s ) + 1 ) ) = ( %s x. ( ( M x. ( x mod D ) ) + 1 ) )'
              % (Y1, Y1, Y1))
    yq1c = sx([yq1b, sx([f1], 'oveq1d',
                        '( %s x. ( ( M x. ( x mod D ) ) + 1 ) ) = %s' % (Y1, QF('( x mod D )')))],
              'eqtrd', '%s = %s' % (QF(Y1), QF('( x mod D )')))
    yq2 = sx([f2], 'oveq2d', '( M x. %s ) = ( M x. ( x mod E ) )' % Y2)
    yq2b = sx([sx([yq2], 'oveq1d',
                  '( ( M x. %s ) + 1 ) = ( ( M x. ( x mod E ) ) + 1 )' % Y2)], 'oveq2d',
              '( %s x. ( ( M x. %s ) + 1 ) ) = ( %s x. ( ( M x. ( x mod E ) ) + 1 ) )'
              % (Y2, Y2, Y2))
    yq2c = sx([yq2b, sx([f2], 'oveq1d',
                        '( %s x. ( ( M x. ( x mod E ) ) + 1 ) ) = %s' % (Y2, QF('( x mod E )')))],
              'eqtrd', '%s = %s' % (QF(Y2), QF('( x mod E )')))
    b1 = sx([sx([yq1c], 'breq2d', '( D || %s <-> D || %s )' % (QF(Y1), QF('( x mod D )'))), qd],
            'bitrd', '( D || %s <-> D || %s )' % (QF(Y1), QF('x')))
    b2 = sx([sx([yq2c], 'breq2d', '( E || %s <-> E || %s )' % (QF(Y2), QF('( x mod E )'))), qe],
            'bitrd', '( E || %s <-> E || %s )' % (QF(Y2), QF('x')))
    conj = sx([b1, b2], 'anbi12d',
              '( %s <-> ( D || %s /\\ E || %s ) )' % (CHY, QF('x'), QF('x')))
    # ( D || QF( x ) /\ E || QF( x ) ) <-> ( D x. E ) || QF( x )
    qz = sx([xz, sx([sx([lift(w, mz, AX), xz], 'zmulcld', '( M x. x ) e. ZZ'),
                     sx([], '1zzd', '1 e. ZZ')], 'zaddcld', '( ( M x. x ) + 1 ) e. ZZ')],
            'zmulcld', '%s e. ZZ' % QF('x'))
    fw = sx([sx([sx([lift(w, dz, AX), lift(w, ez, AX), qz], '3jca',
                    '( D e. ZZ /\\ E e. ZZ /\\ %s e. ZZ )' % QF('x')), lift(w, gcd1, AX)], 'jca',
                '( ( D e. ZZ /\\ E e. ZZ /\\ %s e. ZZ ) /\\ ( D gcd E ) = 1 )' % QF('x')),
             w.inst('coprmdvds2')], 'syl',
            '( ( D || %s /\\ E || %s ) -> ( D x. E ) || %s )' % (QF('x'), QF('x'), QF('x')))
    bk1 = sx([sx([lift(w, dz, AX), lift(w, ez, AX), qz], '3jca',
                 '( D e. ZZ /\\ E e. ZZ /\\ %s e. ZZ )' % QF('x')), w.inst('muldvds1')], 'syl',
             '( ( D x. E ) || %s -> D || %s )' % (QF('x'), QF('x')))
    bk2 = sx([sx([lift(w, dz, AX), lift(w, ez, AX), qz], '3jca',
                 '( D e. ZZ /\\ E e. ZZ /\\ %s e. ZZ )' % QF('x')), w.inst('muldvds2')], 'syl',
             '( ( D x. E ) || %s -> E || %s )' % (QF('x'), QF('x')))
    bk = sx([bk1, bk2], 'jcad',
            '( ( D x. E ) || %s -> ( D || %s /\\ E || %s ) )' % (QF('x'), QF('x'), QF('x')))
    cop = sx([fw, bk], 'impbid',
             '( ( D || %s /\\ E || %s ) <-> ( D x. E ) || %s )' % (QF('x'), QF('x'), QF('x')))
    hyp3 = sx([conj, cop], 'bitrd', '( %s <-> ( D x. E ) || %s )' % (CHY, QF('x')))
    # f1oresrab
    hyp3a = w.s([hyp3], '3impa',
                '( ( %s /\\ x e. %s /\\ y = %s ) -> ( %s <-> ( D x. E ) || %s ) )'
                % (AM, FZ, PAIRX, CHY, QF('x')))
    res = w.s([e3, bij, hyp3a], 'f1oresrab',
              '( %s -> ( %s |` %s ) : %s -1-1-onto-> { y e. %s | %s } )'
              % (AM, FM, RTX('( D x. E )'), RTX('( D x. E )'), BB, CHY))
    # the target set is a Cartesian product of root sets
    RTD = RT('D')
    RTE = RT('E')
    RTDE = RTX('( D x. E )')
    PROD = '( %s X. %s )' % (RTD, RTE)
    AY = '( %s /\\ y e. %s )' % (AM, BB)
    sy = mkst(w, AY)
    yb = sy([], 'simpr', 'y e. %s' % BB)
    yvv = sy([sy([w.s([], 'xpss', '%s C_ ( _V X. _V )' % BB)], 'a1i',
                 '%s C_ ( _V X. _V )' % BB), yb], 'sseldd', 'y e. ( _V X. _V )')
    y1d = sy([yb, w.inst('xp1st')], 'syl', '%s e. ( 0 ..^ D )' % Y1)
    y2e = sy([yb, w.inst('xp2nd')], 'syl', '%s e. ( 0 ..^ E )' % Y2)
    sb1 = w.s([qfsub(w, Y1, 'v')], 'breq2d',
              '( v = %s -> ( D || %s <-> D || %s ) )' % (Y1, QF('v'), QF(Y1)))
    er1 = w.s([sb1], 'elrab',
              '( %s e. %s <-> ( %s e. ( 0 ..^ D ) /\\ D || %s ) )' % (Y1, RTD, Y1, QF(Y1)))
    m1 = sy([sy([er1], 'a1i',
                '( %s e. %s <-> ( %s e. ( 0 ..^ D ) /\\ D || %s ) )' % (Y1, RTD, Y1, QF(Y1))),
             sy([sy([y1d], 'biantrurd',
                    '( D || %s <-> ( %s e. ( 0 ..^ D ) /\\ D || %s ) )' % (QF(Y1), Y1, QF(Y1)))],
                'bicomd',
                '( ( %s e. ( 0 ..^ D ) /\\ D || %s ) <-> D || %s )' % (Y1, QF(Y1), QF(Y1)))],
            'bitrd', '( %s e. %s <-> D || %s )' % (Y1, RTD, QF(Y1)))
    sb2 = w.s([qfsub(w, Y2, 'v')], 'breq2d',
              '( v = %s -> ( E || %s <-> E || %s ) )' % (Y2, QF('v'), QF(Y2)))
    er2 = w.s([sb2], 'elrab',
              '( %s e. %s <-> ( %s e. ( 0 ..^ E ) /\\ E || %s ) )' % (Y2, RTE, Y2, QF(Y2)))
    m2 = sy([sy([er2], 'a1i',
                '( %s e. %s <-> ( %s e. ( 0 ..^ E ) /\\ E || %s ) )' % (Y2, RTE, Y2, QF(Y2))),
             sy([sy([y2e], 'biantrurd',
                    '( E || %s <-> ( %s e. ( 0 ..^ E ) /\\ E || %s ) )' % (QF(Y2), Y2, QF(Y2)))],
                'bicomd',
                '( ( %s e. ( 0 ..^ E ) /\\ E || %s ) <-> E || %s )' % (Y2, QF(Y2), QF(Y2)))],
            'bitrd', '( %s e. %s <-> E || %s )' % (Y2, RTE, QF(Y2)))
    ex7 = sy([sy([w.s([], 'elxp7',
                      '( y e. %s <-> ( y e. ( _V X. _V ) /\\ ( %s e. %s /\\ %s e. %s ) ) )'
                      % (PROD, Y1, RTD, Y2, RTE))], 'a1i',
                 '( y e. %s <-> ( y e. ( _V X. _V ) /\\ ( %s e. %s /\\ %s e. %s ) ) )'
                 % (PROD, Y1, RTD, Y2, RTE)),
              sy([sy([yvv], 'biantrurd',
                     '( ( %s e. %s /\\ %s e. %s ) <-> ( y e. ( _V X. _V ) /\\ ( %s e. %s /\\ %s e. %s ) ) )'
                     % (Y1, RTD, Y2, RTE, Y1, RTD, Y2, RTE))], 'bicomd',
                 '( ( y e. ( _V X. _V ) /\\ ( %s e. %s /\\ %s e. %s ) ) <-> ( %s e. %s /\\ %s e. %s ) )'
                 % (Y1, RTD, Y2, RTE, Y1, RTD, Y2, RTE))], 'bitrd',
             '( y e. %s <-> ( %s e. %s /\\ %s e. %s ) )' % (PROD, Y1, RTD, Y2, RTE))
    yiff = sy([sy([ex7, sy([m1, m2], 'anbi12d',
                           '( ( %s e. %s /\\ %s e. %s ) <-> %s )' % (Y1, RTD, Y2, RTE, CHY))],
                  'bitrd', '( y e. %s <-> %s )' % (PROD, CHY))], 'bicomd',
              '( %s <-> y e. %s )' % (CHY, PROD))
    rb = st([yiff], 'rabbidva',
            '{ y e. %s | %s } = { y e. %s | y e. %s }' % (BB, CHY, BB, PROD))
    din = w.s([], 'dfin5', '( %s i^i %s ) = { x e. %s | x e. %s }' % (BB, PROD, BB, PROD))
    cbv = w.s([w.s([], 'eleq1', '( x = y -> ( x e. %s <-> y e. %s ) )' % (PROD, PROD))],
              'cbvrabv', '{ x e. %s | x e. %s } = { y e. %s | y e. %s }' % (BB, PROD, BB, PROD))
    ssd = st([w.s([], 'ssrab2', '%s C_ ( 0 ..^ D )' % RTD)], 'a1i', '%s C_ ( 0 ..^ D )' % RTD)
    sse = st([w.s([], 'ssrab2', '%s C_ ( 0 ..^ E )' % RTE)], 'a1i', '%s C_ ( 0 ..^ E )' % RTE)
    ssp = st([ssd, sse, w.inst('xpss12')], 'syl2anc', '%s C_ %s' % (PROD, BB))
    ineq = st([st([w.s([], 'sseqin2',
                       '( %s C_ %s <-> ( %s i^i %s ) = %s )' % (PROD, BB, BB, PROD, PROD))], 'a1i',
                  '( %s C_ %s <-> ( %s i^i %s ) = %s )' % (PROD, BB, BB, PROD, PROD)), ssp],
              'mpbid', '( %s i^i %s ) = %s' % (BB, PROD, PROD))
    seteq = st([rb, st([st([st([din], 'a1i',
                               '( %s i^i %s ) = { x e. %s | x e. %s }' % (BB, PROD, BB, PROD)),
                            st([cbv], 'a1i',
                               '{ x e. %s | x e. %s } = { y e. %s | y e. %s }'
                               % (BB, PROD, BB, PROD))], 'eqtrd',
                           '( %s i^i %s ) = { y e. %s | y e. %s }' % (BB, PROD, BB, PROD)),
                        ineq], 'eqtr3d',
                       '{ y e. %s | y e. %s } = %s' % (BB, PROD, PROD))], 'eqtrd',
               '{ y e. %s | %s } = %s' % (BB, CHY, PROD))
    bij2 = st([res, st([seteq], 'f1oeq3d',
                       '( ( %s |` %s ) : %s -1-1-onto-> { y e. %s | %s } <-> '
                       '( %s |` %s ) : %s -1-1-onto-> %s )'
                       % (FM, RTDE, RTDE, BB, CHY, FM, RTDE, RTDE, PROD))], 'mpbid',
               '( %s |` %s ) : %s -1-1-onto-> %s' % (FM, RTDE, RTDE, PROD))
    # cardinalities
    fin0 = st([st([w.s([], 'fzofi', '%s e. Fin' % FZ)], 'a1i', '%s e. Fin' % FZ),
               st([w.s([], 'ssrab2', '%s C_ %s' % (RTDE, FZ))], 'a1i', '%s C_ %s' % (RTDE, FZ))],
              'ssfid', '%s e. Fin' % RTDE)
    find = st([st([w.s([], 'fzofi', '( 0 ..^ D ) e. Fin')], 'a1i',
                   '( 0 ..^ D ) e. Fin'), ssd], 'ssfid', '%s e. Fin' % RTD)
    fine = st([st([w.s([], 'fzofi', '( 0 ..^ E ) e. Fin')], 'a1i',
                   '( 0 ..^ E ) e. Fin'), sse], 'ssfid', '%s e. Fin' % RTE)
    heq = st([fin0, bij2], 'hasheqf1od', '( # ` %s ) = ( # ` %s )' % (RTDE, PROD))
    hxp = st([find, fine, w.inst('hashxp')], 'syl2anc',
             '( # ` %s ) = ( ( # ` %s ) x. ( # ` %s ) )' % (PROD, RTD, RTE))
    final = st([heq, hxp], 'eqtrd',
               '( # ` %s ) = ( ( # ` %s ) x. ( # ` %s ) )' % (RTDE, RTD, RTE))
    # back to the v-form
    cb0 = w.s([w.s([qfsub(w, 'v')], 'breq2d',
                   '( x = v -> ( ( D x. E ) || %s <-> ( D x. E ) || %s ) )'
                   % (QF('x'), QF('v')))],
              'cbvrabv', '%s = %s' % (RTDE, RT('( D x. E )')))
    c0 = st([cb0], 'a1i', '%s = %s' % (RTDE, RT('( D x. E )')))
    l0 = st([st([c0], 'eqcomd', '%s = %s' % (RT('( D x. E )'), RTDE))], 'fveq2d',
            '( # ` %s ) = ( # ` %s )' % (RT('( D x. E )'), RTDE))
    w.qed([l0, final], 'eqtrd',
          '( %s -> ( # ` %s ) = ( ( # ` %s ) x. ( # ` %s ) ) )'
          % (AM, RT('( D x. E )'), RTD, RTE))
    return w


ALL = {'rcmul': rcmul}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
