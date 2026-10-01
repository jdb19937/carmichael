"""Sortie KD2: the derivative kernel (kd2dv, kd2kb).  MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_f.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from kd2lib import *
from cl import formula_of, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, nlinarith
from mvlib import ringeq, ringeqp
import num

only = sys.argv[1:]
RP = 'RR+'


def logmap(w, A):
    """( A -> ( RR _D ( u e. RR+ |-> ( log ` u ) ) ) = ( u e. RR+ |-> ( 1 / u ) ) )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    lf = w.s([w.s([], 'logf1o', "log : ( CC \\ { 0 } ) -1-1-onto-> ran log"), w.inst('f1of')], 'ax-mp', "log : ( CC \\ { 0 } ) --> ran log")
    Au = '( %s /\\ u e. RR+ )' % A
    ss = d('ssrdv', [w.s([w.s([], 'rpcndif0', "( u e. RR+ -> u e. ( CC \\ { 0 } ) )")], 'a1i', "( %s -> ( u e. RR+ -> u e. ( CC \\ { 0 } ) ) )" % A)], "RR+ C_ ( CC \\ { 0 } )")
    fr = d('feqresmpt', [w.s([lf], 'a1i', "( %s -> log : ( CC \\ { 0 } ) --> ran log )" % A), ss], "( log |` RR+ ) = ( u e. RR+ |-> ( log ` u ) )")
    dl = w.s([w.s([], 'dvrelog', "( RR _D ( log |` RR+ ) ) = ( x e. RR+ |-> ( 1 / x ) )"),
              w.s([w.s([], 'oveq2', '( x = u -> ( 1 / x ) = ( 1 / u ) )')], 'cbvmptv', '( x e. RR+ |-> ( 1 / x ) ) = ( u e. RR+ |-> ( 1 / u ) )')], 'eqtri',
             "( RR _D ( log |` RR+ ) ) = ( u e. RR+ |-> ( 1 / u ) )")
    return d('eqtr3d', [d('oveq2d', [fr], "( RR _D ( log |` RR+ ) ) = ( RR _D ( u e. RR+ |-> ( log ` u ) ) )"), w.s([dl], 'a1i', "( %s -> ( RR _D ( log |` RR+ ) ) = ( u e. RR+ |-> ( 1 / u ) ) )" % A)],
             "( RR _D ( u e. RR+ |-> ( log ` u ) ) ) = ( u e. RR+ |-> ( 1 / u ) )")


def cxpmap(w, A, a, ac):
    """( A -> ( RR _D ( u e. RR+ |-> ( u ^c a ) ) ) = ( u e. RR+ |-> ( a x. ( u ^c ( a - 1 ) ) ) ) ), ac : ( A -> a e. CC )"""
    e = D(w, A, 'syl', [ac, w.inst('dvcxp1')], '( RR _D ( x e. RR+ |-> ( x ^c %s ) ) ) = ( x e. RR+ |-> ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (a, a, a))
    c1 = w.s([w.s([], 'oveq1', '( x = u -> ( x ^c %s ) = ( u ^c %s ) )' % (a, a))], 'cbvmptv', '( x e. RR+ |-> ( x ^c %s ) ) = ( u e. RR+ |-> ( u ^c %s ) )' % (a, a))
    c2 = w.s([w.s([w.s([], 'oveq1', '( x = u -> ( x ^c ( %s - 1 ) ) = ( u ^c ( %s - 1 ) ) )' % (a, a))], 'oveq2d', '( x = u -> ( %s x. ( x ^c ( %s - 1 ) ) ) = ( %s x. ( u ^c ( %s - 1 ) ) ) )' % (a, a, a, a))],
             'cbvmptv', '( x e. RR+ |-> ( %s x. ( x ^c ( %s - 1 ) ) ) ) = ( u e. RR+ |-> ( %s x. ( u ^c ( %s - 1 ) ) ) )' % (a, a, a, a))
    e2 = D(w, A, 'eqtr3d', [D(w, A, 'oveq2d', [w.s([c1], 'a1i', '( %s -> ( x e. RR+ |-> ( x ^c %s ) ) = ( u e. RR+ |-> ( u ^c %s ) ) )' % (A, a, a))],
                              '( RR _D ( x e. RR+ |-> ( x ^c %s ) ) ) = ( RR _D ( u e. RR+ |-> ( u ^c %s ) ) )' % (a, a)), e],
           '( RR _D ( u e. RR+ |-> ( u ^c %s ) ) ) = ( x e. RR+ |-> ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (a, a, a))
    return D(w, A, 'eqtrd', [e2, w.s([c2], 'a1i', '( %s -> ( x e. RR+ |-> ( %s x. ( x ^c ( %s - 1 ) ) ) ) = ( u e. RR+ |-> ( %s x. ( u ^c ( %s - 1 ) ) ) ) )' % (A, a, a, a, a))],
             '( RR _D ( u e. RR+ |-> ( u ^c %s ) ) ) = ( u e. RR+ |-> ( %s x. ( u ^c ( %s - 1 ) ) ) )' % (a, a, a))


def contdv(w, A, B, dvst, dval, bval):
    """continuity of ( u e. RR+ |-> B ) from its derivative"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    F = '( u e. RR+ |-> %s )' % B
    Dm = formula_of(w, dvst).split(' = ')[-1][:-2]
    dm = d('eqtrd', [d('dmeqd', [dvst], 'dom ( RR _D %s ) = dom %s' % (F, Dm)), d('dmmptd', [w.s([], 'eqid', '%s = %s' % (Dm, Dm)), dval], 'dom %s = RR+' % Dm)], 'dom ( RR _D %s ) = RR+' % F)
    ff = d('fmptd', [bval, w.s([], 'eqid', '%s = %s' % (F, F))], '%s : RR+ --> CC' % F)
    j = d('3jca', [a1(w, A, 'ax-resscn', 'RR C_ CC'), ff, a1(w, A, 'rpssre', 'RR+ C_ RR')], '( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR )' % F)
    return d('syl2anc', [j, dm, w.inst('dvcn')], '%s e. ( RR+ -cn-> CC )' % F)


def gen_dv():
    w = W('kd2dv', 'Lean ` KDerivDetect.hasDerivAt_detWeight ` : on ` RR+ ` the weight ` ( log u )^(j+1) u^-eta ` has derivative ` detKernel = u^(-1-eta) ( log u )^j ( ( j + 1 ) - eta log u ) ` , which is continuous ( ~ dvmptmul , ~ dvmptco , ~ dvrelog , ~ dvcxp1 ).')
    A0 = '( E e. RR /\\ J e. NN0 )'
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    er = d('simpl', [], 'E e. RR'); jn = d('simpr', [], 'J e. NN0')
    ec = d('recnd', [er], 'E e. CC')
    j1n = d('nnnn0d' if False else 'syl', [jn, w.inst('nn0p1nn')], '( J + 1 ) e. NN')
    Au = '( %s /\\ u e. RR+ )' % A0
    du = lambda ref, h, c: D(w, Au, ref, h, c)
    up = w.s([], 'simpr', '( %s -> u e. RR+ )' % Au)
    uc = du('rpcnd', [up], 'u e. CC'); un0 = du('rpne0d', [up], 'u =/= 0')
    lg = du('relogcld', [up], '( log ` u ) e. RR'); lgc = du('recnd', [lg], '( log ` u ) e. CC')
    J1 = '( J + 1 )'
    # chain rule for ( log u )^(J+1)
    dlog = logmap(w, A0)
    Ay = '( %s /\\ y e. CC )' % A0
    dex = d('syl', [j1n, w.inst('dvexp')], '( CC _D ( x e. CC |-> ( x ^ %s ) ) ) = ( x e. CC |-> ( %s x. ( x ^ ( %s - 1 ) ) ) )' % (J1, J1, J1))
    cy1 = w.s([w.s([], 'oveq1', '( x = y -> ( x ^ %s ) = ( y ^ %s ) )' % (J1, J1))], 'cbvmptv', '( x e. CC |-> ( x ^ %s ) ) = ( y e. CC |-> ( y ^ %s ) )' % (J1, J1))
    cy2 = w.s([w.s([w.s([], 'oveq1', '( x = y -> ( x ^ ( %s - 1 ) ) = ( y ^ ( %s - 1 ) ) )' % (J1, J1))], 'oveq2d', '( x = y -> ( %s x. ( x ^ ( %s - 1 ) ) ) = ( %s x. ( y ^ ( %s - 1 ) ) ) )' % (J1, J1, J1, J1))],
              'cbvmptv', '( x e. CC |-> ( %s x. ( x ^ ( %s - 1 ) ) ) ) = ( y e. CC |-> ( %s x. ( y ^ ( %s - 1 ) ) ) )' % (J1, J1, J1, J1))
    dey = d('eqtr3d', [d('oveq2d', [w.s([cy1], 'a1i', '( %s -> ( x e. CC |-> ( x ^ %s ) ) = ( y e. CC |-> ( y ^ %s ) ) )' % (A0, J1, J1))],
                         '( CC _D ( x e. CC |-> ( x ^ %s ) ) ) = ( CC _D ( y e. CC |-> ( y ^ %s ) ) )' % (J1, J1)), dex],
              '( CC _D ( y e. CC |-> ( y ^ %s ) ) ) = ( x e. CC |-> ( %s x. ( x ^ ( %s - 1 ) ) ) )' % (J1, J1, J1))
    dey = d('eqtrd', [dey, w.s([cy2], 'a1i', '( %s -> ( x e. CC |-> ( %s x. ( x ^ ( %s - 1 ) ) ) ) = ( y e. CC |-> ( %s x. ( y ^ ( %s - 1 ) ) ) ) )' % (A0, J1, J1, J1, J1))],
            '( CC _D ( y e. CC |-> ( y ^ %s ) ) ) = ( y e. CC |-> ( %s x. ( y ^ ( %s - 1 ) ) ) )' % (J1, J1, J1))
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % Ay)
    j1c = d('nncnd', [j1n], '%s e. CC' % J1)
    jm = d('nnm1nn0d' if False else 'syl', [j1n, w.inst('nnm1nn0')], '( %s - 1 ) e. NN0' % J1)
    yp = D(w, Ay, 'expcld', [yc, lift(w, d('nnnn0d', [j1n], '%s e. NN0' % J1), Ay)], '( y ^ %s ) e. CC' % J1)
    ydp = D(w, Ay, 'mulcld', [lift(w, j1c, Ay), D(w, Ay, 'expcld', [yc, lift(w, jm, Ay)], '( y ^ ( %s - 1 ) ) e. CC' % J1)], '( %s x. ( y ^ ( %s - 1 ) ) ) e. CC' % (J1, J1))
    iu = du('reccld', [uc, un0], '( 1 / u ) e. CC')
    H1 = 'y = ( log ` u )'
    ch1 = w.s([], 'oveq1', '( %s -> ( y ^ %s ) = ( ( log ` u ) ^ %s ) )' % (H1, J1, J1))
    ch2 = w.s([w.s([], 'oveq1', '( %s -> ( y ^ ( %s - 1 ) ) = ( ( log ` u ) ^ ( %s - 1 ) ) )' % (H1, J1, J1))], 'oveq2d',
              '( %s -> ( %s x. ( y ^ ( %s - 1 ) ) ) = ( %s x. ( ( log ` u ) ^ ( %s - 1 ) ) ) )' % (H1, J1, J1, J1, J1))
    LJ1 = '( ( log ` u ) ^ %s )' % J1
    DL = '( ( %s x. ( ( log ` u ) ^ ( %s - 1 ) ) ) x. ( 1 / u ) )' % (J1, J1)
    co = d('dvmptco', [a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }'), a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }'), lgc, iu, yp, ydp, dlog, dey, ch1, ch2],
           '( RR _D ( u e. RR+ |-> %s ) ) = ( u e. RR+ |-> %s )' % (LJ1, DL))
    # u ^c -u E
    mec = d('negcld', [ec], '-u E e. CC')
    dcx = cxpmap(w, A0, '-u E', mec)
    UE = '( u ^c -u E )'; DU = '( -u E x. ( u ^c ( -u E - 1 ) ) )'
    lj1c = du('expcld', [lgc, lift(w, d('nnnn0d', [j1n], '%s e. NN0' % J1), Au)], '%s e. CC' % LJ1)
    dlc = du('mulcld', [du('mulcld', [lift(w, j1c, Au), du('expcld', [lgc, lift(w, jm, Au)], '( ( log ` u ) ^ ( %s - 1 ) ) e. CC' % J1)], '( %s x. ( ( log ` u ) ^ ( %s - 1 ) ) ) e. CC' % (J1, J1)), iu],
             '%s e. CC' % DL)
    uec = du('cxpcld', [uc, lift(w, mec, Au)], '%s e. CC' % UE)
    duc = du('mulcld', [lift(w, mec, Au), du('cxpcld', [uc, du('subcld', [lift(w, mec, Au), a1(w, Au, 'ax-1cn', '1 e. CC')], '( -u E - 1 ) e. CC')], '( u ^c ( -u E - 1 ) ) e. CC')], '%s e. CC' % DU)
    pr = d('dvmptmul', [a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }'), lj1c, dlc, co, uec, duc, dcx],
           '( RR _D ( u e. RR+ |-> ( %s x. %s ) ) ) = ( u e. RR+ |-> ( ( %s x. %s ) + ( %s x. %s ) ) )' % (LJ1, UE, DL, UE, DU, LJ1))
    # pointwise identification with PSI
    LJ = '( ( log ` u ) ^ J )'; CX = '( u ^c ( -u 1 - E ) )'
    p1 = du('pncand', [lift(w, d('nn0cnd', [jn], 'J e. CC'), Au), a1(w, Au, 'ax-1cn', '1 e. CC')], '( %s - 1 ) = J' % J1)
    p2 = du('oveq2d', [p1], '( ( log ` u ) ^ ( %s - 1 ) ) = %s' % (J1, LJ))
    p3 = du('expp1d', [lgc, lift(w, jn, Au)], '%s = ( %s x. ( log ` u ) )' % (LJ1, LJ))
    cla = Closure(w, Au, {'E': ('CC', lift(w, ec, Au))})
    q1 = du('cxpaddd', [uc, un0, du('negcld', [a1(w, Au, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), lift(w, mec, Au)], '( u ^c ( -u 1 + -u E ) ) = ( ( u ^c -u 1 ) x. %s )' % UE)
    q2 = du('oveq2d', [ringeq(w, Au, '( -u 1 + -u E )', '( -u 1 - E )', cla)], '( u ^c ( -u 1 + -u E ) ) = %s' % CX)
    q3 = du('eqtrd', [du('cxpnegd', [uc, un0, a1(w, Au, 'ax-1cn', '1 e. CC')], '( u ^c -u 1 ) = ( 1 / ( u ^c 1 ) )'), du('oveq2d', [du('cxp1d', [uc], '( u ^c 1 ) = u')], '( 1 / ( u ^c 1 ) ) = ( 1 / u )')],
              '( u ^c -u 1 ) = ( 1 / u )')
    q4 = du('eqtr3d', [q1, q2], '( ( u ^c -u 1 ) x. %s ) = %s' % (UE, CX))
    q5 = du('eqtr3d', [du('oveq1d', [q3], '( ( u ^c -u 1 ) x. %s ) = ( ( 1 / u ) x. %s )' % (UE, UE)), q4], '( ( 1 / u ) x. %s ) = %s' % (UE, CX))
    q6 = du('oveq2d', [ringeq(w, Au, '( -u E - 1 )', '( -u 1 - E )', cla)], '( u ^c ( -u E - 1 ) ) = %s' % CX)
    ljc = du('expcld', [lgc, lift(w, jn, Au)], '%s e. CC' % LJ)
    clr = Closure(w, Au, {'E': ('CC', lift(w, ec, Au)), 'J': ('CC', lift(w, d('nn0cnd', [jn], 'J e. CC'), Au)), LJ: ('CC', ljc), '( log ` u )': ('CC', lgc), '( 1 / u )': ('CC', iu), UE: ('CC', uec),
                          CX: ('CC', du('cxpcld', [uc, du('subcld', [du('negcld', [a1(w, Au, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), lift(w, ec, Au)], '( -u 1 - E ) e. CC')], '%s e. CC' % CX)),
                          '( u ^c ( -u E - 1 ) )': ('CC', du('cxpcld', [uc, du('subcld', [lift(w, mec, Au), a1(w, Au, 'ax-1cn', '1 e. CC')], '( -u E - 1 ) e. CC')], '( u ^c ( -u E - 1 ) ) e. CC'))})
    for a in (LJ, '( log ` u )', '( 1 / u )', UE, CX, '( u ^c ( -u E - 1 ) )'):
        clr.atom(a)
    SUM = '( ( %s x. %s ) + ( %s x. %s ) )' % (DL, UE, DU, LJ1)
    M1 = '( ( ( %s x. %s ) x. ( ( 1 / u ) x. %s ) ) + ( ( -u E x. ( u ^c ( -u E - 1 ) ) ) x. ( %s x. ( log ` u ) ) ) )' % (J1, LJ, UE, LJ)
    r1 = ringeq(w, Au, '( ( ( %s x. %s ) x. ( 1 / u ) ) x. %s )' % (J1, LJ, UE), '( ( %s x. %s ) x. ( ( 1 / u ) x. %s ) )' % (J1, LJ, UE), clr)
    s1 = du('oveq12d', [du('eqtrd', [du('oveq1d', [du('oveq1d', [du('oveq2d', [p2], '( %s x. ( ( log ` u ) ^ ( %s - 1 ) ) ) = ( %s x. %s )' % (J1, J1, J1, LJ))],
                                                                   '%s = ( ( %s x. %s ) x. ( 1 / u ) )' % (DL, J1, LJ))], '( %s x. %s ) = ( ( ( %s x. %s ) x. ( 1 / u ) ) x. %s )' % (DL, UE, J1, LJ, UE)), r1],
                                     '( %s x. %s ) = ( ( %s x. %s ) x. ( ( 1 / u ) x. %s ) )' % (DL, UE, J1, LJ, UE)),
                        du('oveq2d', [p3], '( %s x. %s ) = ( %s x. ( %s x. ( log ` u ) ) )' % (DU, LJ1, DU, LJ))], '%s = %s' % (SUM, M1))
    M2 = '( ( ( %s x. %s ) x. %s ) + ( ( -u E x. %s ) x. ( %s x. ( log ` u ) ) ) )' % (J1, LJ, CX, CX, LJ)
    s2 = du('oveq12d', [du('oveq2d', [q5], '( ( %s x. %s ) x. ( ( 1 / u ) x. %s ) ) = ( ( %s x. %s ) x. %s )' % (J1, LJ, UE, J1, LJ, CX)),
                        du('oveq1d', [du('oveq2d', [q6], '( -u E x. ( u ^c ( -u E - 1 ) ) ) = ( -u E x. %s )' % CX)], '( ( -u E x. ( u ^c ( -u E - 1 ) ) ) x. ( %s x. ( log ` u ) ) ) = ( ( -u E x. %s ) x. ( %s x. ( log ` u ) ) )' % (LJ, CX, LJ))],
            '%s = %s' % (M1, M2))
    s3 = ringeq(w, Au, M2, PSI('J', 'u'), clr)
    pe = chain(w, Au, [SUM, M1, M2, PSI('J', 'u')], [s1, s2, s3])
    dv = d('eqtrd', [pr, d('mpteq2dva', [pe], '( u e. RR+ |-> %s ) = ( u e. RR+ |-> %s )' % (SUM, PSI('J', 'u')))], '( RR _D ( u e. RR+ |-> %s ) ) = ( u e. RR+ |-> %s )' % (PHI('J', 'u'), PSI('J', 'u')))
    # continuity of PSI
    lcont = contdv(w, A0, '( log ` u )', dlog, iu, lgc)
    m1e = d('subcld', [d('negcld', [a1(w, A0, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), ec], '( -u 1 - E ) e. CC')
    dcx2 = cxpmap(w, A0, '( -u 1 - E )', m1e)
    cxc = clr.mem(CX, 'CC')
    ccont = contdv(w, A0, CX, dcx2, du('mulcld', [lift(w, m1e, Au), du('cxpcld', [uc, du('subcld', [lift(w, m1e, Au), a1(w, Au, 'ax-1cn', '1 e. CC')], '( ( -u 1 - E ) - 1 ) e. CC')],
                                                                      '( u ^c ( ( -u 1 - E ) - 1 ) ) e. CC')], '( ( -u 1 - E ) x. ( u ^c ( ( -u 1 - E ) - 1 ) ) ) e. CC'), cxc)
    ecj = d('syl', [jn, w.inst('expcncf')], '( x e. CC |-> ( x ^ J ) ) e. ( CC -cn-> CC )')
    ljcont = d('cncfmpt1f', [ecj, lcont], '( u e. RR+ |-> ( ( x e. CC |-> ( x ^ J ) ) ` ( log ` u ) ) ) e. ( RR+ -cn-> CC )')
    fvx = du('fvmptd', [a1(w, Au, 'eqid', '( x e. CC |-> ( x ^ J ) ) = ( x e. CC |-> ( x ^ J ) )'), w.s([w.s([], 'oveq1', '( x = ( log ` u ) -> ( x ^ J ) = %s )' % LJ)], 'adantl', '( ( %s /\\ x = ( log ` u ) ) -> ( x ^ J ) = %s )' % (Au, LJ)),
                        lgc, ljc], '( ( x e. CC |-> ( x ^ J ) ) ` ( log ` u ) ) = %s' % LJ)
    ljcont2 = d('eqeltrd', [d('mpteq2dva', [fvx], '( u e. RR+ |-> ( ( x e. CC |-> ( x ^ J ) ) ` ( log ` u ) ) ) = ( u e. RR+ |-> %s )' % LJ) if False else
                            d('eqcomd', [d('mpteq2dva', [fvx], '( u e. RR+ |-> ( ( x e. CC |-> ( x ^ J ) ) ` ( log ` u ) ) ) = ( u e. RR+ |-> %s )' % LJ)], '( u e. RR+ |-> %s ) = ( u e. RR+ |-> ( ( x e. CC |-> ( x ^ J ) ) ` ( log ` u ) ) )' % LJ),
                            ljcont], '( u e. RR+ |-> %s ) e. ( RR+ -cn-> CC )' % LJ)
    rpc = d('sstrd', [a1(w, A0, 'rpssre', 'RR+ C_ RR'), a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'RR+ C_ CC')
    cst = lambda c, cc_: d('syl', [d('3jca', [cc_, rpc, d('ssidd', [], 'CC C_ CC')], '( %s e. CC /\\ RR+ C_ CC /\\ CC C_ CC )' % c), w.inst('cncfmptc')], '( u e. RR+ |-> %s ) e. ( RR+ -cn-> CC )' % c)
    jc1 = cst(J1, j1c); ecn = cst('E', ec)
    el = d('mulcncf', [ecn, lcont], '( u e. RR+ |-> ( E x. ( log ` u ) ) ) e. ( RR+ -cn-> CC )')
    fac = d('subcncf', [jc1, el], '( u e. RR+ |-> ( %s - ( E x. ( log ` u ) ) ) ) e. ( RR+ -cn-> CC )' % J1)
    c1 = d('mulcncf', [ccont, ljcont2], '( u e. RR+ |-> ( %s x. %s ) ) e. ( RR+ -cn-> CC )' % (CX, LJ))
    c2 = d('mulcncf', [c1, fac], '( u e. RR+ |-> %s ) e. ( RR+ -cn-> CC )' % PSI('J', 'u'))
    fin = d('jca', [dv, c2], S['kd2dv'].split(' -> ', 1)[1][:-2])
    w.qed([fin], 'idi', S['kd2dv'])
    return only_run(w, only)


def gen_kb():
    w = W('kd2kb', 'Lean ` KDerivDetect.abs_detKernel_mul_le ` : for ` 1 <_ u ` , ` eta log u <_ 16 M <_ 16 ( j + 1 ) ` , ` abs psi ( u ) . u <_ 17 ( j + 1 ) j! / eta^j ` ( TP ~ tppowfac at ` eta log u ` ).')
    A0 = S['kd2kb'].split(' -> ( ( abs `')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simpl', [], '( E e. RR+ /\\ ( J e. NN0 /\\ M e. RR /\\ M <_ ( J + 1 ) ) )'); g2 = d('simpr', [], '( U e. RR /\\ 1 <_ U /\\ ( E x. ( log ` U ) ) <_ ( ; 1 6 x. M ) )')
    ep = d('simpld', [g1], 'E e. RR+'); g1b = d('simprd', [g1], '( J e. NN0 /\\ M e. RR /\\ M <_ ( J + 1 ) )')
    jn = d('simp1d', [g1b], 'J e. NN0'); mr = d('simp2d', [g1b], 'M e. RR'); mj = d('simp3d', [g1b], 'M <_ ( J + 1 )')
    ur = d('simp1d', [g2], 'U e. RR'); u1 = d('simp2d', [g2], '1 <_ U'); elu = d('simp3d', [g2], '( E x. ( log ` U ) ) <_ ( ; 1 6 x. M )')
    er = d('rpred', [ep], 'E e. RR'); ec = d('rpcnd', [ep], 'E e. CC')
    up = d('elrpd', [ur, linarith(w, A0, [u1], '0 < U', closure=Closure(w, A0, {'U': ('RR', ur)}))], 'U e. RR+')
    uc = d('rpcnd', [up], 'U e. CC'); un0 = d('rpne0d', [up], 'U =/= 0')
    LU = '( log ` U )'
    lu = d('relogcld', [up], '%s e. RR' % LU); lu0 = d('logge0d', [ur, u1], '0 <_ %s' % LU)
    X = '( E x. %s )' % LU
    xr = d('remulcld', [er, lu], '%s e. RR' % X); x0 = d('mulge0d', [er, lu, d('rpge0d', [ep], '0 <_ E'), lu0], '0 <_ %s' % X)
    tp = d('syl3anc', [xr, x0, jn, w.inst('tppowfac')], '( %s ^ J ) <_ ( ( ! ` J ) x. ( exp ` %s ) )' % (X, X))
    UE = '( U ^c E )'; UmE = '( U ^c -u E )'; LJ = '( %s ^ J )' % LU; EJ = '( E ^ J )'; FJ = '( ! ` J )'
    ce = d('cxpefd', [uc, un0, ec], '%s = ( exp ` %s )' % (UE, X))
    me = d('mulexpd', [ec, d('recnd', [lu], '%s e. CC' % LU), jn], '( %s ^ J ) = ( %s x. %s )' % (X, EJ, LJ))
    k1 = d('breqtrrd', [d('eqbrtrrd', [me, tp], '( %s x. %s ) <_ ( %s x. ( exp ` %s ) )' % (EJ, LJ, FJ, X)), d('oveq2d', [ce], '( %s x. %s ) = ( %s x. ( exp ` %s ) )' % (FJ, UE, FJ, X))],
            '( %s x. %s ) <_ ( %s x. %s )' % (EJ, LJ, FJ, UE))
    ejp = d('rpexpcld', [ep, d('nn0zd', [jn], 'J e. ZZ')], '%s e. RR+' % EJ)
    fjr = d('nnred', [d('faccld', [jn], '%s e. NN' % FJ)], '%s e. RR' % FJ)
    uep = d('rpcxpcld', [up, er], '%s e. RR+' % UE); umep = d('rpcxpcld', [up, d('renegcld', [er], '-u E e. RR')], '%s e. RR+' % UmE)
    ljr = d('reexpcld', [lu, jn], '%s e. RR' % LJ); lj0 = d('expge0d', [lu, jn, lu0], '0 <_ %s' % LJ)
    k2 = d('mpbid', [k1, d('lemuldiv2d', [ljr, d('remulcld', [fjr, d('rpred', [uep], '%s e. RR' % UE)], '( %s x. %s ) e. RR' % (FJ, UE)), ejp],
                                         '( ( %s x. %s ) <_ ( %s x. %s ) <-> %s <_ ( ( %s x. %s ) / %s ) )' % (EJ, LJ, FJ, UE, LJ, FJ, UE, EJ))], '%s <_ ( ( %s x. %s ) / %s )' % (LJ, FJ, UE, EJ))
    Q = '( ( %s x. %s ) / %s )' % (FJ, UE, EJ)
    k3 = d('lemul1ad', [ljr, d('rerpdivcld', [d('remulcld', [fjr, d('rpred', [uep], '%s e. RR' % UE)], '( %s x. %s ) e. RR' % (FJ, UE)), ejp], '%s e. RR' % Q),
                        d('rpred', [umep], '%s e. RR' % UmE), d('rpge0d', [umep], '0 <_ %s' % UmE), k2], '( %s x. %s ) <_ ( %s x. %s )' % (LJ, UmE, Q, UmE))
    IE = '( 1 / %s )' % EJ
    ejc = d('rpcnd', [ejp], '%s e. CC' % EJ); ejn = d('rpne0d', [ejp], '%s =/= 0' % EJ)
    dq = d('divrecd', [d('mulcld', [d('recnd', [fjr], '%s e. CC' % FJ), d('rpcnd', [uep], '%s e. CC' % UE)], '( %s x. %s ) e. CC' % (FJ, UE)), ejc, ejn], '%s = ( ( %s x. %s ) x. %s )' % (Q, FJ, UE, IE))
    ue1 = d('eqtr3d', [d('cxpaddd', [uc, un0, ec, d('negcld', [ec], '-u E e. CC')], '( U ^c ( E + -u E ) ) = ( %s x. %s )' % (UE, UmE)),
                       d('eqtrd', [d('oveq2d', [d('negidd', [ec], '( E + -u E ) = 0')], '( U ^c ( E + -u E ) ) = ( U ^c 0 )'), d('cxp0d', [uc], '( U ^c 0 ) = 1')], '( U ^c ( E + -u E ) ) = 1')],
             '( %s x. %s ) = 1' % (UE, UmE))
    cl = Closure(w, A0, {FJ: ('CC', d('recnd', [fjr], '%s e. CC' % FJ)), UE: ('CC', d('rpcnd', [uep], '%s e. CC' % UE)), UmE: ('CC', d('rpcnd', [umep], '%s e. CC' % UmE)),
                         IE: ('CC', d('reccld', [ejc, ejn], '%s e. CC' % IE)), LJ: ('CC', d('recnd', [ljr], '%s e. CC' % LJ)), 'J': ('CC', d('nn0cnd', [jn], 'J e. CC'))})
    for a in (FJ, UE, UmE, IE, LJ):
        cl.atom(a)
    r1 = ringeq(w, A0, '( ( ( %s x. %s ) x. %s ) x. %s )' % (FJ, UE, IE, UmE), '( ( %s x. %s ) x. ( %s x. %s ) )' % (FJ, IE, UE, UmE), cl)
    r2 = d('eqtrd', [r1, d('eqtrd', [d('oveq2d', [ue1], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. 1 )' % (FJ, IE, UE, UmE, FJ, IE)),
                                     d('mulridd', [cl.mem('( %s x. %s )' % (FJ, IE), 'CC')], '( ( %s x. %s ) x. 1 ) = ( %s x. %s )' % (FJ, IE, FJ, IE))],
                                    '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. %s )' % (FJ, IE, UE, UmE, FJ, IE))], '( ( ( %s x. %s ) x. %s ) x. %s ) = ( %s x. %s )' % (FJ, UE, IE, UmE, FJ, IE))
    k4 = d('breqtrd', [k3, d('eqtrd', [d('oveq1d', [dq], '( %s x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (Q, UmE, FJ, UE, IE, UmE)), r2], '( %s x. %s ) = ( %s x. %s )' % (Q, UmE, FJ, IE))],
            '( %s x. %s ) <_ ( %s x. %s )' % (LJ, UmE, FJ, IE))
    # | ( J + 1 ) - E log U | <_ 17 ( J + 1 )
    F_ = '( ( J + 1 ) - %s )' % X
    clf = Closure(w, A0, {'J': ('RR', d('nn0red', [jn], 'J e. RR')), X: ('RR', xr), 'M': ('RR', mr)}); clf.atom(X)
    fr = clf.mem(F_, 'RR')
    fa = d('mpbird', [d('jca', [linarith(w, A0, [elu, mj, x0], '-u ( ; 1 7 x. ( J + 1 ) ) <_ %s' % F_, closure=clf), linarith(w, A0, [elu, mj, x0, d('nn0ge0d', [jn], '0 <_ J')], '%s <_ ( ; 1 7 x. ( J + 1 ) )' % F_, closure=clf)],
                                '( -u ( ; 1 7 x. ( J + 1 ) ) <_ %s /\\ %s <_ ( ; 1 7 x. ( J + 1 ) ) )' % (F_, F_)),
                      d('absled', [fr, clf.mem('( ; 1 7 x. ( J + 1 ) )', 'RR')], '( ( abs ` %s ) <_ ( ; 1 7 x. ( J + 1 ) ) <-> ( -u ( ; 1 7 x. ( J + 1 ) ) <_ %s /\\ %s <_ ( ; 1 7 x. ( J + 1 ) ) ) )' % (F_, F_, F_))],
            '( abs ` %s ) <_ ( ; 1 7 x. ( J + 1 ) )' % F_)
    # | PSI | . U
    CX = '( U ^c ( -u 1 - E ) )'
    cxp_ = d('rpcxpcld', [up, d('resubcld', [d('renegcld', [a1(w, A0, '1re', '1 e. RR')], '-u 1 e. RR'), er], '( -u 1 - E ) e. RR')], '%s e. RR+' % CX)
    PS_ = PSI('J', 'U')
    a1_ = d('absmuld', [d('mulcld', [d('rpcnd', [cxp_], '%s e. CC' % CX), d('recnd', [ljr], '%s e. CC' % LJ)], '( %s x. %s ) e. CC' % (CX, LJ)), d('recnd', [fr], '%s e. CC' % F_)],
            '( abs ` %s ) = ( ( abs ` ( %s x. %s ) ) x. ( abs ` %s ) )' % (PS_, CX, LJ, F_))
    a2_ = d('absidd', [d('remulcld', [d('rpred', [cxp_], '%s e. RR' % CX), ljr], '( %s x. %s ) e. RR' % (CX, LJ)), d('mulge0d', [d('rpred', [cxp_], '%s e. RR' % CX), ljr, d('rpge0d', [cxp_], '0 <_ %s' % CX), lj0], '0 <_ ( %s x. %s )' % (CX, LJ))],
            '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (CX, LJ, CX, LJ))
    ab = d('eqtrd', [a1_, d('oveq1d', [a2_], '( ( abs ` ( %s x. %s ) ) x. ( abs ` %s ) ) = ( ( %s x. %s ) x. ( abs ` %s ) )' % (CX, LJ, F_, CX, LJ, F_))], '( abs ` %s ) = ( ( %s x. %s ) x. ( abs ` %s ) )' % (PS_, CX, LJ, F_))
    cu1 = d('cxpaddd', [uc, un0, d('subcld', [d('negcld', [a1(w, A0, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), ec], '( -u 1 - E ) e. CC'), a1(w, A0, 'ax-1cn', '1 e. CC')], '( U ^c ( ( -u 1 - E ) + 1 ) ) = ( %s x. ( U ^c 1 ) )' % CX)
    cla = Closure(w, A0, {'E': ('CC', ec)})
    cu2 = d('oveq2d', [ringeq(w, A0, '( ( -u 1 - E ) + 1 )', '-u E', cla)], '( U ^c ( ( -u 1 - E ) + 1 ) ) = %s' % UmE)
    cu3 = d('eqtr3d', [cu1, cu2], '( %s x. ( U ^c 1 ) ) = %s' % (CX, UmE))
    cu = d('eqtr3d', [d('oveq2d', [d('cxp1d', [uc], '( U ^c 1 ) = U')], '( %s x. ( U ^c 1 ) ) = ( %s x. U )' % (CX, CX)), cu3], '( %s x. U ) = %s' % (CX, UmE))
    AF = '( abs ` %s )' % F_
    cl2 = Closure(w, A0, {CX: ('CC', d('rpcnd', [cxp_], '%s e. CC' % CX)), LJ: ('CC', d('recnd', [ljr], '%s e. CC' % LJ)), AF: ('CC', d('recnd', [d('abscld', [d('recnd', [fr], '%s e. CC' % F_)], '%s e. RR' % AF)], '%s e. CC' % AF)),
                          'U': ('CC', uc), UmE: ('CC', d('rpcnd', [umep], '%s e. CC' % UmE))})
    for a in (CX, LJ, AF, UmE):
        cl2.atom(a)
    L1 = '( ( abs ` %s ) x. U )' % PS_
    e1 = d('oveq1d', [ab], '%s = ( ( ( %s x. %s ) x. %s ) x. U )' % (L1, CX, LJ, AF))
    e2 = ringeq(w, A0, '( ( ( %s x. %s ) x. %s ) x. U )' % (CX, LJ, AF), '( ( %s x. U ) x. ( %s x. %s ) )' % (CX, LJ, AF), cl2)
    e3 = d('oveq1d', [cu], '( ( %s x. U ) x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (CX, LJ, AF, UmE, LJ, AF))
    e4 = ringeq(w, A0, '( %s x. ( %s x. %s ) )' % (UmE, LJ, AF), '( ( %s x. %s ) x. %s )' % (LJ, UmE, AF), cl2)
    ee = chain(w, A0, [L1, '( ( ( %s x. %s ) x. %s ) x. U )' % (CX, LJ, AF), '( ( %s x. U ) x. ( %s x. %s ) )' % (CX, LJ, AF), '( %s x. ( %s x. %s ) )' % (UmE, LJ, AF), '( ( %s x. %s ) x. %s )' % (LJ, UmE, AF)],
               [e1, e2, e3, e4])
    k5 = d('lemul12ad', [d('remulcld', [ljr, d('rpred', [umep], '%s e. RR' % UmE)], '( %s x. %s ) e. RR' % (LJ, UmE)), d('remulcld', [fjr, d('rpred', [d('rpreccld', [ejp], '%s e. RR+' % IE)], '%s e. RR' % IE)], '( %s x. %s ) e. RR' % (FJ, IE)),
                         d('abscld', [d('recnd', [fr], '%s e. CC' % F_)], '%s e. RR' % AF), clf.mem('( ; 1 7 x. ( J + 1 ) )', 'RR'),
                         d('mulge0d', [ljr, d('rpred', [umep], '%s e. RR' % UmE), lj0, d('rpge0d', [umep], '0 <_ %s' % UmE)], '0 <_ ( %s x. %s )' % (LJ, UmE)), d('absge0d', [d('recnd', [fr], '%s e. CC' % F_)], '0 <_ %s' % AF), k4, fa],
            '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. ( ; 1 7 x. ( J + 1 ) ) )' % (LJ, UmE, AF, FJ, IE))
    RH = '( ( ( ; 1 7 x. ( J + 1 ) ) x. %s ) / %s )' % (FJ, EJ)
    rq = d('divrecd', [cl.mem('( ( ; 1 7 x. ( J + 1 ) ) x. %s )' % FJ, 'CC'), ejc, ejn], '%s = ( ( ( ; 1 7 x. ( J + 1 ) ) x. %s ) x. %s )' % (RH, FJ, IE))
    rq2 = ringeq(w, A0, '( ( %s x. %s ) x. ( ; 1 7 x. ( J + 1 ) ) )' % (FJ, IE), '( ( ( ; 1 7 x. ( J + 1 ) ) x. %s ) x. %s )' % (FJ, IE), cl)
    fin = d('breqtrrd', [d('breqtrd', [d('eqbrtrd', [ee, k5], '%s <_ ( ( %s x. %s ) x. ( ; 1 7 x. ( J + 1 ) ) )' % (L1, FJ, IE)), rq2], '%s <_ ( ( ( ; 1 7 x. ( J + 1 ) ) x. %s ) x. %s )' % (L1, FJ, IE)), rq],
            '%s <_ %s' % (L1, RH))
    w.qed([fin], 'idi', S['kd2kb'])
    return only_run(w, only)


if __name__ == '__main__':
    gen_dv()
    gen_kb()
