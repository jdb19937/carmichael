"""Sortie C6 section B, part 3: the power mapping, the restriction of the
quotient function off P, its holomorphy off P and at P, and on all of D
(holpowp, holqres, holqdvo, holqdvp, holqhol)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

DP = '( D \\ { P } )'
PW = '( y e. %s |-> ( ( y - P ) ^ N ) )'


def cnel(w, A0):
    return closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')


def topsteps(w, A0):
    """ej: TOP = TOP, jr: TOP = ( TOP |`t CC ), tp: ( A0 -> TOP e. Top ), un: CC = U. TOP"""
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    tp = w.s([w.s([ej], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
    un = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    return ej, jr, tp, un


if __name__ == '__main__':
    # ---- holpowp: ( y e. E |-> ( ( y - P ) ^ N ) ) is holomorphic on an open E ----
    w = W('holpowp', 'The power of ( y - P ) is holomorphic on an open subset E of the plane.')
    A0 = '( ( E e. %s /\\ E C_ CC ) /\\ ( P e. CC /\\ N e. NN ) )' % TOP
    A1 = '( %s /\\ y e. E )' % A0
    A2 = '( %s /\\ y e. CC )' % A0
    A3 = '( %s /\\ v e. CC )' % A0
    et = w.s([], 'simpll', '( %s -> E e. %s )' % (A0, TOP))
    ec = w.s([], 'simplr', '( %s -> E C_ CC )' % A0)
    pc = w.s([], 'simprl', '( %s -> P e. CC )' % A0)
    nn = w.s([], 'simprr', '( %s -> N e. NN )' % A0)
    hn = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    PWE = PW % 'E'
    LIN = '( y e. E |-> ( y - P ) )'
    # continuity
    ej, jr, tp, un = topsteps(w, A0)
    sub = w.s([w.s([ej], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
    cid = w.s([ec, closed(w, A0, 'ssid', 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( %s -> ( y e. E |-> y ) e. ( E -cn-> CC ) )' % A0)
    ccst = w.s([pc, ec, closed(w, A0, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( %s -> ( y e. E |-> P ) e. ( E -cn-> CC ) )' % A0)
    lcn = w.s([ej, sub, cid, ccst], 'cncfmpt2f', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, LIN))
    pcn = w.s([lcn, hn, w.inst('cncfexpb')], 'syl2anc', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, PWE))
    # derivative of y - P on CC, then on E
    ce = cnel(w, A0)
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % A2)
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % A2)
    pc2 = ad(w, pc, A2, 'P e. CC')
    zero = w.s([], '0cnd', '( %s -> 0 e. CC )' % A2)
    dvid = w.s([ce], 'dvmptid', '( %s -> ( CC _D ( y e. CC |-> y ) ) = ( y e. CC |-> 1 ) )' % A0)
    dvc = w.s([ce, pc], 'dvmptc', '( %s -> ( CC _D ( y e. CC |-> P ) ) = ( y e. CC |-> 0 ) )' % A0)
    dvl = w.s([ce, yc, one, dvid, pc2, zero, dvc], 'dvmptsub', '( %s -> ( CC _D ( y e. CC |-> ( y - P ) ) ) = ( y e. CC |-> ( 1 - 0 ) ) )' % A0)
    ypc = w.s([yc, pc2], 'subcld', '( %s -> ( y - P ) e. CC )' % A2)
    d10 = w.s([one, zero], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % A2)
    dvle = w.s([ce, ypc, d10, dvl, ec, jr, ej, et], 'dvmptres', '( %s -> ( CC _D %s ) = ( y e. E |-> ( 1 - 0 ) ) )' % (A0, LIN))
    # composition with the power
    ye = w.s([], 'simpr', '( %s -> y e. E )' % A1)
    yc1 = w.s([ad(w, ec, A1, 'E C_ CC'), ye], 'sseldd', '( %s -> y e. CC )' % A1)
    ypc1 = w.s([yc1, ad(w, pc, A1, 'P e. CC')], 'subcld', '( %s -> ( y - P ) e. CC )' % A1)
    d101 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), w.s([], '0cnd', '( %s -> 0 e. CC )' % A1)], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % A1)
    vc = w.s([], 'simpr', '( %s -> v e. CC )' % A3)
    vn = w.s([vc, ad(w, hn, A3, 'N e. NN0')], 'expcld', '( %s -> ( v ^ N ) e. CC )' % A3)
    vd = w.s([w.s([ad(w, nn, A3, 'N e. NN')], 'nncnd', '( %s -> N e. CC )' % A3), w.s([vc, w.s([ad(w, nn, A3, 'N e. NN'), w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A3)], 'expcld', '( %s -> ( v ^ ( N - 1 ) ) e. CC )' % A3)],
             'mulcld', '( %s -> ( N x. ( v ^ ( N - 1 ) ) ) e. CC )' % A3)
    dve = w.s([nn, w.inst('dvexp')], 'syl', '( %s -> ( CC _D ( v e. CC |-> ( v ^ N ) ) ) = ( v e. CC |-> ( N x. ( v ^ ( N - 1 ) ) ) ) )' % A0)
    se = w.s([], 'oveq1', '( v = ( y - P ) -> ( v ^ N ) = ( ( y - P ) ^ N ) )')
    sf = w.s([w.s([], 'oveq1', '( v = ( y - P ) -> ( v ^ ( N - 1 ) ) = ( ( y - P ) ^ ( N - 1 ) ) )')], 'oveq2d', '( v = ( y - P ) -> ( N x. ( v ^ ( N - 1 ) ) ) = ( N x. ( ( y - P ) ^ ( N - 1 ) ) ) )')
    RHS = '( ( N x. ( ( y - P ) ^ ( N - 1 ) ) ) x. ( 1 - 0 ) )'
    dvp = w.s([ce, ce, ypc1, d101, vn, vd, dvle, dve, se, sf], 'dvmptco', '( %s -> ( CC _D %s ) = ( y e. E |-> %s ) )' % (A0, PWE, RHS))
    rhsc = w.s([w.s([w.s([ad(w, nn, A1, 'N e. NN')], 'nncnd', '( %s -> N e. CC )' % A1), w.s([ypc1, w.s([ad(w, nn, A1, 'N e. NN'), w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A1)], 'expcld', '( %s -> ( ( y - P ) ^ ( N - 1 ) ) e. CC )' % A1)],
                    'mulcld', '( %s -> ( N x. ( ( y - P ) ^ ( N - 1 ) ) ) e. CC )' % A1), d101], 'mulcld', '( %s -> %s e. CC )' % (A1, RHS))
    dm = dvdom(w, A0, PWE, 'y', 'E', RHS, dvp, rhsc)
    w.qed([pcn, dm], 'jca', '( %s -> ( %s e. ( E -cn-> CC ) /\\ E C_ dom ( CC _D %s ) ) )' % (A0, PWE, PWE))
    run1(w)

    # ---- holqres: the restriction of Q off P is the quotient mapping ----------------
    w = W('holqres', 'The restriction of the quotient function to D minus P is the quotient mapping.')
    hyp(w, '1', 'holqres.c', CDEF)
    hyp(w, '2', 'holqres.q', QDEF)
    A0 = CTX
    QM = '( z e. %s |-> ( ( F ` z ) / ( ( z - P ) ^ N ) ) )' % DP
    A1 = '( %s /\\ z e. %s )' % (A0, DP)
    r1 = w.s([w.s([w.s([], 'difss', '%s C_ D' % DP), w.inst('resmpt')], 'ax-mp', '( ( z e. D |-> %s ) |` %s ) = ( z e. %s |-> %s )' % (QB('z'), DP, DP, QB('z')))], 'a1i',
             '( %s -> ( ( z e. D |-> %s ) |` %s ) = ( z e. %s |-> %s ) )' % (A0, QB('z'), DP, DP, QB('z')))
    r0 = w.s([w.s(['2'], 'reseq1i', '( Q |` %s ) = ( ( z e. D |-> %s ) |` %s )' % (DP, QB('z'), DP))], 'a1i', '( %s -> ( Q |` %s ) = ( ( z e. D |-> %s ) |` %s ) )' % (A0, DP, QB('z'), DP))
    zne = w.s([w.s([w.s([], 'simpr', '( %s -> z e. %s )' % (A1, DP)), w.inst('eldifsn')], 'sylib', '( %s -> ( z e. D /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
    body = w.s([w.s([zne], 'neneqd', '( %s -> -. z = P )' % A1)], 'iffalsed', '( %s -> %s = ( ( F ` z ) / ( ( z - P ) ^ N ) ) )' % (A1, QB('z')))
    r2 = w.s([body], 'mpteq2dva', '( %s -> ( z e. %s |-> %s ) = %s )' % (A0, DP, QB('z'), QM))
    w.qed([w.s([r0, r1], 'eqtrd', '( %s -> ( Q |` %s ) = ( z e. %s |-> %s ) )' % (A0, DP, DP, QB('z'))), r2], 'eqtrd', '( %s -> ( Q |` %s ) = %s )' % (A0, DP, QM))
    run1(w, h=True)

    # ---- holqdvo: Q is differentiable at every point of D other than P ------------
    w = W('holqdvo', 'The quotient function is differentiable at every point of D other than the centre P.')
    hyp(w, '1', 'holqdvo.c', CDEF)
    hyp(w, '2', 'holqdvo.q', QDEF)
    A0 = CTX
    d = ctxq(w)
    ej, jr, tp, un = topsteps(w, A0)
    PWD = PW % DP
    FR_ = '( F |` %s )' % DP
    QM = '( z e. %s |-> ( ( F ` z ) / ( ( z - P ) ^ N ) ) )' % DP
    QM2 = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (DP, FR_, PWD)
    dpss = w.s([w.s([], 'difss', '%s C_ D' % DP)], 'a1i', '( %s -> %s C_ D )' % (A0, DP))
    dpc = w.s([dpss, d['dss']], 'sstrd', '( %s -> %s C_ CC )' % (A0, DP))
    haus = w.s([w.s([ej], 'cnfldhaus', '%s e. Haus' % TOP)], 'a1i', '( %s -> %s e. Haus )' % (A0, TOP))
    pcld = w.s([haus, d['pc'], w.s([un], 'sncld', '( ( %s e. Haus /\\ P e. CC ) -> { P } e. ( Clsd ` %s ) )' % (TOP, TOP))], 'syl2anc', '( %s -> { P } e. ( Clsd ` %s ) )' % (A0, TOP))
    dpopn = w.s([d['dopn'], pcld, w.s([un], 'difopn', '( ( D e. %s /\\ { P } e. ( Clsd ` %s ) ) -> %s e. %s )' % (TOP, TOP, DP, TOP))], 'syl2anc', '( %s -> %s e. %s )' % (A0, DP, TOP))
    intdp = w.s([tp, dpopn, w.inst('isopn3i')], 'syl2anc', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, TOP, DP, DP))
    # HOL of F |` DP on DP
    frcn = w.s([dpss, d['fcn'], w.s([], 'rescncf', '( %s C_ D -> ( F e. ( D -cn-> CC ) -> %s e. ( %s -cn-> CC ) ) )' % (DP, FR_, DP))], 'sylc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, FR_, DP))
    ssc = closed(w, A0, 'ssid', 'CC C_ CC')
    dvrf = w.s([w.s([ssc, d['ff']], 'jca', '( %s -> ( CC C_ CC /\\ F : D --> CC ) )' % A0), w.s([d['dss'], dpc], 'jca', '( %s -> ( D C_ CC /\\ %s C_ CC ) )' % (A0, DP)),
                w.s([ej, jr], 'dvres', '( ( ( CC C_ CC /\\ F : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) -> ( CC _D %s ) = ( ( CC _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (DP, FR_, TOP, DP))], 'syl2anc',
               '( %s -> ( CC _D %s ) = ( ( CC _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (A0, FR_, TOP, DP))
    dvrf2 = w.s([dvrf, w.s([intdp], 'reseq2d', '( %s -> ( ( CC _D F ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D F ) |` %s ) )' % (A0, TOP, DP, DP))], 'eqtrd', '( %s -> ( CC _D %s ) = ( ( CC _D F ) |` %s ) )' % (A0, FR_, DP))
    dmf = w.s([w.s([dvrf2], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( ( CC _D F ) |` %s ) )' % (A0, FR_, DP)), w.s([w.s([], 'dmres', 'dom ( ( CC _D F ) |` %s ) = ( %s i^i dom ( CC _D F ) )' % (DP, DP))], 'a1i',
                                                                                                                  '( %s -> dom ( ( CC _D F ) |` %s ) = ( %s i^i dom ( CC _D F ) ) )' % (A0, DP, DP))], 'eqtrd',
              '( %s -> dom ( CC _D %s ) = ( %s i^i dom ( CC _D F ) ) )' % (A0, FR_, DP))
    frd = w.s([w.s([closed(w, A0, 'ssid', '%s C_ %s' % (DP, DP)), w.s([dpss, d['dhol']], 'sstrd', '( %s -> %s C_ dom ( CC _D F ) )' % (A0, DP))], 'ssind', '( %s -> %s C_ ( %s i^i dom ( CC _D F ) ) )' % (A0, DP, DP)), dmf], 'sseqtrrd',
              '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, DP, FR_))
    holf = w.s([frcn, frd], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, FR_, DP, DP, FR_))
    # HOL of the power mapping and its nonvanishing
    holp = w.s([w.s([dpopn, dpc], 'jca', '( %s -> ( %s e. %s /\\ %s C_ CC ) )' % (A0, DP, TOP, DP)), w.s([d['pc'], d['nn']], 'jca', '( %s -> ( P e. CC /\\ N e. NN ) )' % A0), w.inst('holpowp')], 'syl2anc',
               '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, PWD, DP, DP, PWD))
    A1 = '( %s /\\ v e. %s )' % (A0, DP)
    vdp = w.s([], 'simpr', '( %s -> v e. %s )' % (A1, DP))
    vne = w.s([w.s([vdp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. D /\\ v =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> v =/= P )' % A1)
    vc = w.s([ad(w, dpc, A1, '%s C_ CC' % DP), vdp], 'sseldd', '( %s -> v e. CC )' % A1)
    vp = w.s([vc, ad(w, d['pc'], A1, 'P e. CC')], 'subcld', '( %s -> ( v - P ) e. CC )' % A1)
    vpn = w.s([vc, ad(w, d['pc'], A1, 'P e. CC'), vne], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A1)
    vk = w.s([vp, ad(w, d['hn'], A1, 'N e. NN0')], 'expcld', '( %s -> ( ( v - P ) ^ N ) e. CC )' % A1)
    vkn = w.s([vp, vpn, w.s([ad(w, d['hn'], A1, 'N e. NN0')], 'nn0zd', '( %s -> N e. ZZ )' % A1), w.inst('expne0i')], 'syl3anc', '( %s -> ( ( v - P ) ^ N ) =/= 0 )' % A1)
    subv = w.s([w.s([], 'oveq1', '( y = v -> ( y - P ) = ( v - P ) )')], 'oveq1d', '( y = v -> ( ( y - P ) ^ N ) = ( ( v - P ) ^ N ) )')
    pwv = mptval(w, A1, 'y', DP, PWD, 'v', '( ( v - P ) ^ N )', subv, vdp)
    nv = w.s([pwv, vkn], 'eqnetrd', '( %s -> ( %s ` v ) =/= 0 )' % (A1, PWD))
    allv = w.s([nv], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (A0, DP, PWD))
    hdiv = w.s([holf, holp, allv, w.inst('holdiv')], 'syl3anc', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, QM2, DP, DP, QM2))
    qmd = w.s([hdiv, w.inst('simpr')], 'syl', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, DP, QM2))
    # QM2 = Q |` DP
    A2 = '( %s /\\ z e. %s )' % (A0, DP)
    zdp = w.s([], 'simpr', '( %s -> z e. %s )' % (A2, DP))
    fvr = w.s([zdp, w.inst('fvres')], 'syl', '( %s -> ( %s ` z ) = ( F ` z ) )' % (A2, FR_))
    subz = w.s([w.s([], 'oveq1', '( y = z -> ( y - P ) = ( z - P ) )')], 'oveq1d', '( y = z -> ( ( y - P ) ^ N ) = ( ( z - P ) ^ N ) )')
    pwz = mptval(w, A2, 'y', DP, PWD, 'z', '( ( z - P ) ^ N )', subz, zdp)
    bd = w.s([fvr, pwz], 'oveq12d', '( %s -> ( ( %s ` z ) / ( %s ` z ) ) = ( ( F ` z ) / ( ( z - P ) ^ N ) ) )' % (A2, FR_, PWD))
    qmeq = w.s([bd], 'mpteq2dva', '( %s -> %s = %s )' % (A0, QM2, QM))
    qres = w.s(['1', '2'], 'holqres', '( %s -> ( Q |` %s ) = %s )' % (CTX, DP, QM))
    qmq = w.s([qmeq, w.s([qres], 'eqcomd', '( %s -> %s = ( Q |` %s ) )' % (A0, QM, DP))], 'eqtrd', '( %s -> %s = ( Q |` %s ) )' % (A0, QM2, DP))
    qrd = w.s([qmd, w.s([w.s([qmq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D ( Q |` %s ) ) )' % (A0, QM2, DP))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D ( Q |` %s ) ) )' % (A0, QM2, DP))], 'sseqtrd',
              '( %s -> %s C_ dom ( CC _D ( Q |` %s ) ) )' % (A0, DP, DP))
    # dvres for Q
    qf = w.s(['1', '2'], 'holqf', '( %s -> Q : D --> CC )' % CTX)
    dvrq = w.s([w.s([ssc, qf], 'jca', '( %s -> ( CC C_ CC /\\ Q : D --> CC ) )' % A0), w.s([d['dss'], dpc], 'jca', '( %s -> ( D C_ CC /\\ %s C_ CC ) )' % (A0, DP)),
                w.s([ej, jr], 'dvres', '( ( ( CC C_ CC /\\ Q : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( Q |` %s ) ) = ( ( CC _D Q ) |` ( ( int ` %s ) ` %s ) ) )' % (DP, DP, TOP, DP))], 'syl2anc',
               '( %s -> ( CC _D ( Q |` %s ) ) = ( ( CC _D Q ) |` ( ( int ` %s ) ` %s ) ) )' % (A0, DP, TOP, DP))
    dvrq2 = w.s([dvrq, w.s([intdp], 'reseq2d', '( %s -> ( ( CC _D Q ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D Q ) |` %s ) )' % (A0, TOP, DP, DP))], 'eqtrd', '( %s -> ( CC _D ( Q |` %s ) ) = ( ( CC _D Q ) |` %s ) )' % (A0, DP, DP))
    dmq = w.s([w.s([dvrq2], 'dmeqd', '( %s -> dom ( CC _D ( Q |` %s ) ) = dom ( ( CC _D Q ) |` %s ) )' % (A0, DP, DP)), w.s([w.s([], 'dmres', 'dom ( ( CC _D Q ) |` %s ) = ( %s i^i dom ( CC _D Q ) )' % (DP, DP))], 'a1i',
                                                                                                                    '( %s -> dom ( ( CC _D Q ) |` %s ) = ( %s i^i dom ( CC _D Q ) ) )' % (A0, DP, DP))], 'eqtrd',
              '( %s -> dom ( CC _D ( Q |` %s ) ) = ( %s i^i dom ( CC _D Q ) ) )' % (A0, DP, DP))
    w.qed([w.s([qrd, dmq], 'sseqtrd', '( %s -> %s C_ ( %s i^i dom ( CC _D Q ) ) )' % (A0, DP, DP)), w.s([w.s([], 'inss2', '( %s i^i dom ( CC _D Q ) ) C_ dom ( CC _D Q )' % DP)], 'a1i', '( %s -> ( %s i^i dom ( CC _D Q ) ) C_ dom ( CC _D Q ) )' % (A0, DP))],
          'sstrd', '( %s -> %s C_ dom ( CC _D Q ) )' % (A0, DP))
    run1(w, h=True)

    # ---- holqdvp: Q is differentiable at P ------------------------------------------
    w = W('holqdvp', 'The quotient function is differentiable at the centre P, with derivative the ( N + 1 )-th Taylor coefficient over 2 pi i.')
    hyp(w, '1', 'holqdvp.c', CDEF)
    hyp(w, '2', 'holqdvp.q', QDEF)
    A0 = CTX
    d = ctxq(w)
    ej, jr, tp, un = topsteps(w, A0)
    L = '( ( C ` ( N + 1 ) ) / %s )' % TPI
    DQ = '( z e. %s |-> ( ( ( Q ` z ) - ( Q ` P ) ) / ( z - P ) ) )' % DP
    qf = w.s(['1', '2'], 'holqf', '( %s -> Q : D --> CC )' % CTX)
    ssc = closed(w, A0, 'ssid', 'CC C_ CC')
    gdef = w.s([], 'eqid', '%s = %s' % (DQ, DQ))
    bic = w.s([jr, ej, gdef, ssc, qf, d['dss']], 'eldv', '( %s -> ( P ( CC _D Q ) %s <-> ( P e. ( ( int ` %s ) ` D ) /\\ %s e. ( %s limCC P ) ) ) )' % (A0, L, TOP, L, DQ))
    intd = w.s([tp, d['dopn'], w.inst('isopn3i')], 'syl2anc', '( %s -> ( ( int ` %s ) ` D ) = D )' % (A0, TOP))
    pint = w.s([d['pd'], intd], 'eleqtrrd', '( %s -> P e. ( ( int ` %s ) ` D ) )' % (A0, TOP))
    # the limit through limcbnd
    hn1 = w.s([d['hn'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    c1 = ccl(w, A0, '( N + 1 )', hn1, d['abih'], '1')
    tpic, tne = tpisteps(w, A0)
    lc = w.s([c1, tpic, tne], 'divcld', '( %s -> %s e. CC )' % (A0, L))
    dpss = w.s([w.s([], 'difss', '%s C_ D' % DP)], 'a1i', '( %s -> %s C_ D )' % (A0, DP))
    dpc = w.s([dpss, d['dss']], 'sstrd', '( %s -> %s C_ CC )' % (A0, DP))
    A1 = '( %s /\\ z e. %s )' % (A0, DP)
    zdp = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, DP))
    zd = w.s([w.s([zdp, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. D /\\ z =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> z e. D )' % A1)
    zne = w.s([w.s([zdp, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. D /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
    zc = w.s([ad(w, d['dss'], A1, 'D C_ CC'), zd], 'sseldd', '( %s -> z e. CC )' % A1)
    qz = w.s([ad(w, qf, A1, 'Q : D --> CC'), zd], 'ffvelcdmd', '( %s -> ( Q ` z ) e. CC )' % A1)
    qp = w.s([ad(w, qf, A1, 'Q : D --> CC'), ad(w, d['pd'], A1, 'P e. D')], 'ffvelcdmd', '( %s -> ( Q ` P ) e. CC )' % A1)
    zp = w.s([zc, ad(w, d['pc'], A1, 'P e. CC')], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
    zpn = w.s([zc, ad(w, d['pc'], A1, 'P e. CC'), zne], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
    bcl = w.s([w.s([qz, qp], 'subcld', '( %s -> ( ( Q ` z ) - ( Q ` P ) ) e. CC )' % A1), zp, zpn], 'divcld', '( %s -> ( ( ( Q ` z ) - ( Q ` P ) ) / ( z - P ) ) e. CC )' % A1)
    dqf = w.s([bcl, gdef], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, DQ, DP))
    geo, reals = geo_of_int(w, A0, d)
    kr, k0 = kreal(w, A0, d, geo, reals)
    TP2 = '( 2 x. _pi )'; R2 = '( R ^ ( N + 2 ) )'
    tp2rp = w.s([closed(w, A0, '2rp', '2 e. RR+'), closed(w, A0, 'pirp', '_pi e. RR+')], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, TP2))
    n2 = w.s([w.s([w.s([d['hn']], 'nn0cnd', '( %s -> N e. CC )' % A0), w.inst('add1p1')], 'syl', '( %s -> ( ( N + 1 ) + 1 ) = ( N + 2 ) )' % A0), w.s([hn1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( N + 1 ) + 1 ) e. NN0 )' % A0)], 'eqeltrrd',
             '( %s -> ( N + 2 ) e. NN0 )' % A0)
    r2rp = w.s([d['Rrp'], w.s([n2], 'nn0zd', '( %s -> ( N + 2 ) e. ZZ )' % A0)], 'rpexpcld', '( %s -> %s e. RR+ )' % (A0, R2))
    den = w.s([tp2rp, r2rp], 'rpmulcld', '( %s -> ( %s x. %s ) e. RR+ )' % (A0, TP2, R2))
    K2 = '( %s / ( %s x. %s ) )' % (KK, TP2, R2)
    k2r = w.s([kr, den], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, K2))
    k20 = w.s([kr, den, k0], 'divge0d', '( %s -> 0 <_ %s )' % (A0, K2))
    hrp = w.s([d['Rrp']], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % A0)
    # the pointwise bound at w
    AW = '( abs ` ( w - P ) )'
    A2 = '( %s /\\ w e. %s )' % (A0, DP)
    CND = '( w =/= P /\\ %s < ( R / 2 ) )' % AW
    A3 = '( %s /\\ %s )' % (A2, CND)
    wdp = w.s([w.s([], 'simpr', '( %s -> w e. %s )' % (A2, DP))], 'adantr', '( %s -> w e. %s )' % (A3, DP))
    wd = w.s([w.s([wdp, w.inst('eldifsn')], 'sylib', '( %s -> ( w e. D /\\ w =/= P ) )' % A3), w.inst('simpl')], 'syl', '( %s -> w e. D )' % A3)
    wne = w.s([w.s([], 'simpr', '( %s -> %s )' % (A3, CND)), w.inst('simpl')], 'syl', '( %s -> w =/= P )' % A3)
    wlt = w.s([w.s([], 'simpr', '( %s -> %s )' % (A3, CND)), w.inst('simpr')], 'syl', '( %s -> %s < ( R / 2 ) )' % (A3, AW))
    wc = w.s([w.s([d['dss']], 'ad2antrr', '( %s -> D C_ CC )' % A3), wd], 'sseldd', '( %s -> w e. CC )' % A3)
    aw = w.s([w.s([wc, w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % A3)], 'subcld', '( %s -> ( w - P ) e. CC )' % A3)], 'abscld', '( %s -> %s e. RR )' % (A3, AW))
    hr3 = w.s([w.s([hrp], 'ad2antrr', '( %s -> ( R / 2 ) e. RR+ )' % A3)], 'rpred', '( %s -> ( R / 2 ) e. RR )' % A3)
    wle = w.s([aw, hr3, wlt], 'ltled', '( %s -> %s <_ ( R / 2 ) )' % (A3, AW))
    ctx3 = w.s([], 'ad2antrr', '( %s -> %s )' % (A3, CTX))
    DQW = '( ( ( Q ` w ) - ( Q ` P ) ) / ( w - P ) )'
    dq2 = w.s(['1', '2'], 'holqdq2', '( ( %s /\\ ( X e. D /\\ X =/= P /\\ ( abs ` ( X - P ) ) <_ ( R / 2 ) ) ) -> ( abs ` ( ( ( ( Q ` X ) - ( Q ` P ) ) / ( X - P ) ) - %s ) ) <_ ( %s x. ( abs ` ( X - P ) ) ) )'.replace('X', 'w') % (CTX, L, K2))
    bnd = w.s([w.s([ctx3, w.s([wd, wne, wle], '3jca', '( %s -> ( w e. D /\\ w =/= P /\\ %s <_ ( R / 2 ) ) )' % (A3, AW))], 'jca', '( %s -> ( %s /\\ ( w e. D /\\ w =/= P /\\ %s <_ ( R / 2 ) ) ) )' % (A3, CTX, AW)), dq2], 'syl',
              '( %s -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )' % (A3, DQW, L, K2, AW))
    subw = w.s([w.s([w.s([], 'fveq2', '( z = w -> ( Q ` z ) = ( Q ` w ) )')], 'oveq1d', '( z = w -> ( ( Q ` z ) - ( Q ` P ) ) = ( ( Q ` w ) - ( Q ` P ) ) )'), w.s([], 'oveq1', '( z = w -> ( z - P ) = ( w - P ) )')], 'oveq12d',
               '( z = w -> ( ( ( Q ` z ) - ( Q ` P ) ) / ( z - P ) ) = %s )' % DQW)
    dqw = mptval(w, A3, 'z', DP, DQ, 'w', DQW, subw, wdp)
    bnd2 = w.s([w.s([w.s([dqw], 'oveq1d', '( %s -> ( ( %s ` w ) - %s ) = ( %s - %s ) )' % (A3, DQ, L, DQW, L))], 'fveq2d', '( %s -> ( abs ` ( ( %s ` w ) - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A3, DQ, L, DQW, L)), bnd], 'eqbrtrd',
               '( %s -> ( abs ` ( ( %s ` w ) - %s ) ) <_ ( %s x. %s ) )' % (A3, DQ, L, K2, AW))
    HYP = 'A. w e. %s ( %s -> ( abs ` ( ( %s ` w ) - %s ) ) <_ ( %s x. %s ) )' % (DP, CND, DQ, L, K2, AW)
    ral = w.s([w.s([bnd2], 'ex', '( %s -> ( %s -> ( abs ` ( ( %s ` w ) - %s ) ) <_ ( %s x. %s ) ) )' % (A2, CND, DQ, L, K2, AW))], 'ralrimiva', '( %s -> %s )' % (A0, HYP))
    lim = w.s([w.s([dqf, dpc], 'jca', '( %s -> ( %s : %s --> CC /\\ %s C_ CC ) )' % (A0, DQ, DP, DP)), w.s([d['pc'], lc], 'jca', '( %s -> ( P e. CC /\\ %s e. CC ) )' % (A0, L)),
               w.s([w.s([k2r, k20], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, K2, K2)), w.s([hrp, ral], 'jca', '( %s -> ( ( R / 2 ) e. RR+ /\\ %s ) )' % (A0, HYP))], 'jca',
                   '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( ( R / 2 ) e. RR+ /\\ %s ) ) )' % (A0, K2, K2, HYP)), w.inst('limcbnd')], 'syl3anc', '( %s -> %s e. ( %s limCC P ) )' % (A0, L, DQ))
    w.qed([w.s([pint, lim], 'jca', '( %s -> ( P e. ( ( int ` %s ) ` D ) /\\ %s e. ( %s limCC P ) ) )' % (A0, TOP, L, DQ)), bic], 'mpbird', '( %s -> P ( CC _D Q ) %s )' % (A0, L))
    run1(w, h=True)

    # ---- holqhol: Q is holomorphic on D -----------------------------------------------
    w = W('holqhol', 'The quotient function is holomorphic on D: the singularity at the centre is removable.')
    hyp(w, '1', 'holqhol.c', CDEF)
    hyp(w, '2', 'holqhol.q', QDEF)
    A0 = CTX
    d = ctxq(w)
    L = '( ( C ` ( N + 1 ) ) / %s )' % TPI
    qf = w.s(['1', '2'], 'holqf', '( %s -> Q : D --> CC )' % CTX)
    dvo = w.s(['1', '2'], 'holqdvo', '( %s -> %s C_ dom ( CC _D Q ) )' % (CTX, DP))
    dvp = w.s(['1', '2'], 'holqdvp', '( %s -> P ( CC _D Q ) %s )' % (CTX, L))
    hn1 = w.s([d['hn'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    c1 = ccl(w, A0, '( N + 1 )', hn1, d['abih'], '1')
    tpic, tne = tpisteps(w, A0)
    lc = w.s([c1, tpic, tne], 'divcld', '( %s -> %s e. CC )' % (A0, L))
    pdm = w.s([d['pc'], lc, dvp, w.inst('breldmg')], 'syl3anc', '( %s -> P e. dom ( CC _D Q ) )' % A0)
    uss = w.s([dvo, w.s([pdm], 'snssd', '( %s -> { P } C_ dom ( CC _D Q ) )' % A0)], 'unssd', '( %s -> ( %s u. { P } ) C_ dom ( CC _D Q ) )' % (A0, DP))
    dss2 = w.s([w.s([d['pd'], w.inst('difsnid')], 'syl', '( %s -> ( %s u. { P } ) = D )' % (A0, DP)), uss], 'eqsstrrd', '( %s -> D C_ dom ( CC _D Q ) )' % A0)
    ssc = closed(w, A0, 'ssid', 'CC C_ CC')
    dbs = w.s([ssc, qf, d['dss']], 'dvbss', '( %s -> dom ( CC _D Q ) C_ D )' % A0)
    dmeq = w.s([dbs, dss2], 'eqssd', '( %s -> dom ( CC _D Q ) = D )' % A0)
    cn = w.s([w.s([ssc, qf, d['dss']], '3jca', '( %s -> ( CC C_ CC /\\ Q : D --> CC /\\ D C_ CC ) )' % A0), dmeq, w.inst('dvcn')], 'syl2anc', '( %s -> Q e. ( D -cn-> CC ) )' % A0)
    w.qed([cn, dss2], 'jca', '( %s -> ( Q e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D Q ) ) )' % A0)
    run1(w, h=True)
