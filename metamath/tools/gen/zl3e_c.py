"""ZL3e section C: characters (conductor bridge, the inverse character, root numbers).
`MM_DB=sorties/zl3e.mm python3 tools/gen/zl3e_c.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl3e_base import *

MAIN = __name__ == '__main__'
MC, YP = LE.MC, LE.YP

# ---------------------------------------------------------------- zl3brg
if wante('zl3brg', MAIN):
    w = W('zl3brg', 'The conductor bridge: the primitive character ` Y = N DChrPrim X ` is primitive modulo ` M = N DChrCond X ` , and ` M = 1 ` exactly when ` X ` is principal.')
    A, Cc = ante_e('zl3brg')
    a = D(w, A, 'jca', [w.s([], 'dchrcondnn', '( %s -> %s e. NN )' % (A, MC)), w.s([], 'dchrprimcl', '( %s -> %s e. ( Base ` ( DChr ` %s ) ) )' % (A, YP, MC))],
          '( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) )' % (MC, YP, MC))
    b = w.s([], 'dchrprimprim', '( %s -> ( %s DChrCond %s ) = %s )' % (A, MC, YP, MC))
    c = D(w, A, 'ifbid', [w.s([], 'dchrcondeq1', '( %s -> ( X = ( 0g ` ( DChr ` N ) ) <-> %s = 1 ) )' % (A, MC))], '%s = %s' % (LE.RP, LE.RMC))
    w.qed([D(w, A, 'jca', [D(w, A, 'jca', [a, b], LE.PRC), c], Cc)], 'idi', SE['zl3brg'])
    goe(w)


import zf4lib as Z4
LM = LE.LM
YB = LE.YB
INV = '( invg ` ( DChr ` M ) )'


def pr_facts(w, A, pr):
    """from ( A -> PR ): M e. NN, Y e. Base, cond"""
    ch = D(w, A, 'simpld', [pr], '( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) )')
    return ch, D(w, A, 'simpld', [ch], 'M e. NN'), D(w, A, 'simprd', [ch], 'Y e. ( Base ` ( DChr ` M ) )'), D(w, A, 'simprd', [pr], '( M DChrCond Y ) = M')


def invinv(w, A, mn, yd):
    """( A -> ( INV ` ( INV ` Y ) ) = Y )"""
    g = w.s([], 'eqid', '( DChr ` M ) = ( DChr ` M )')
    grp = D(w, A, 'syl', [D(w, A, 'dchrabl', [g, mn], '( DChr ` M ) e. Abel') if False else w.s([mn, w.s([g], 'dchrabl', '( M e. NN -> ( DChr ` M ) e. Abel )')], 'syl', '( %s -> ( DChr ` M ) e. Abel )' % A),
                         w.inst('ablgrp')], '( DChr ` M ) e. Grp')
    return w.s([grp, yd, w.s([w.s([], 'eqid', '( Base ` ( DChr ` M ) ) = ( Base ` ( DChr ` M ) )'), w.s([], 'eqid', '%s = %s' % (INV, INV))], 'grpinvinv',
                             '( ( ( DChr ` M ) e. Grp /\\ Y e. ( Base ` ( DChr ` M ) ) ) -> ( %s ` ( %s ` Y ) ) = Y )' % (INV, INV))], 'syl2anc', '( %s -> ( %s ` ( %s ` Y ) ) = Y )' % (A, INV, INV))


# ---------------------------------------------------------------- zl3gsp
if wante('zl3gsp', MAIN):
    w = W('zl3gsp', 'Gauss sums of a primitive character and of its inverse: ` tau ( Y ) tau ( YB ) = Y ( -1 ) M ` ( ~ dchrgsabs , ~ dchrgsshiftr at ` -1 ` , ~ root1cjz ).')
    A, Cc = ante_e('zl3gsp')
    pr = w.s([], 'id', '( %s -> %s )' % (A, A))
    ch, mn, yd, cond = pr_facts(w, A, pr)
    par = D(w, A, 'syl', [ch, w.inst('zl3par')], L.split_imp(L.STATEMENTS['zl3par'])[1])
    ybd = D(w, A, 'simprd', [D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (LE.PAR, YB))], '%s e. ( Base ` ( DChr ` M ) )' % YB)
    Z = lambda a: '( %s ` %s )' % (LM, a)
    zeta = Z4.R('M')
    TY = lambda a: '( ( Y ` %s ) x. ( %s ^ %s ) )' % (Z(a), zeta, a)
    TB = lambda a: '( ( %s ` %s ) x. ( %s ^ ( -u 1 x. %s ) ) )' % (YB, Z(a), zeta, a)
    SUM = lambda b: 'sum_ a e. ( 0 ..^ M ) %s' % b
    gY = D(w, A, 'syl', [ch, w.inst('dchrgsval2')], '( M DChrGS Y ) = %s' % SUM(TY('a')))
    fin = cst(w, A, 'fzofi', '( 0 ..^ M ) e. Fin')
    Aa = '( %s /\\ a e. ( 0 ..^ M ) )' % A
    aa = w.s([], 'simpr', '( %s -> a e. ( 0 ..^ M ) )' % Aa)
    az = D(w, Aa, 'elfzoelz', [aa], 'a e. ZZ') if False else D(w, Aa, 'syl', [aa, w.inst('elfzoelz')], 'a e. ZZ')
    an0 = D(w, Aa, 'syl', [aa, w.inst('elfzonn0')], 'a e. NN0')
    mna = ad(w, Aa, mn, 'M e. NN'); yda = ad(w, Aa, yd, 'Y e. ( Base ` ( DChr ` M ) )')
    g_, z_, d_, l_ = Z4.dchyp(w, 'M')
    yf = D(w, Aa, 'dchrf', [g_, z_, d_, w.s([], 'eqid', '( Base ` ( Z/nZ ` M ) ) = ( Base ` ( Z/nZ ` M ) )'), yda], 'Y : ( Base ` ( Z/nZ ` M ) ) --> CC')
    zel = Z4.zrh_el(w, Aa, mna, az, 'M', 'a')
    yv = D(w, Aa, 'ffvelcdmd', [yf, zel], '( Y ` %s ) e. CC' % Z('a'))
    zc = D(w, Aa, 'root1cl' if False else 'cxpcld', [cst(w, Aa, 'neg1cn', '-u 1 e. CC'), D(w, Aa, 'nndivcld' if False else 'divcld', [cst(w, Aa, '2cn', '2 e. CC'), D(w, Aa, 'nncnd', [mna], 'M e. CC'), D(w, Aa, 'nnne0d', [mna], 'M =/= 0')], '( 2 / M ) e. CC')],
           '%s e. CC' % zeta)
    zpa = D(w, Aa, 'expcld', [zc, an0], '( %s ^ a ) e. CC' % zeta)
    tyc = D(w, Aa, 'mulcld', [yv, zpa], '%s e. CC' % TY('a'))
    cj1 = D(w, A, 'fsumcj', [fin, tyc], '( * ` %s ) = %s' % (SUM(TY('a')), SUM('( * ` %s )' % TY('a'))))
    # term by term
    cjm = D(w, Aa, 'cjmuld', [yv, zpa], '( * ` %s ) = ( ( * ` ( Y ` %s ) ) x. ( * ` ( %s ^ a ) ) )' % (TY('a'), Z('a'), zeta))
    dc = Z4.dchr_conj(w, Aa, mna, yda, az, 'M', 'Y', 'a')      # ( INV ` Y ) ` Z a = * ( Y ` Z a )
    rc = D(w, Aa, 'syl2anc', [mna, az, w.inst('root1cjz')], '( * ` ( %s ^ a ) ) = ( %s ^ -u a )' % (zeta, zeta))
    m1 = D(w, Aa, 'syl', [D(w, Aa, 'zcnd', [az], 'a e. CC'), w.inst('mulm1')], '( -u 1 x. a ) = -u a')
    tt = chain(w, Aa, ['( * ` %s )' % TY('a'), '( ( * ` ( Y ` %s ) ) x. ( * ` ( %s ^ a ) ) )' % (Z('a'), zeta), '( ( %s ` %s ) x. ( %s ^ -u a ) )' % (YB, Z('a'), zeta), TB('a')],
               [cjm, D(w, Aa, 'oveq12d', [D(w, Aa, 'eqcomd', [dc], '( * ` ( Y ` %s ) ) = ( %s ` %s )' % (Z('a'), YB, Z('a'))), rc],
                       '( ( * ` ( Y ` %s ) ) x. ( * ` ( %s ^ a ) ) ) = ( ( %s ` %s ) x. ( %s ^ -u a ) )' % (Z('a'), zeta, YB, Z('a'), zeta)),
                ('r', D(w, Aa, 'oveq2d', [D(w, Aa, 'oveq2d', [m1], '( %s ^ ( -u 1 x. a ) ) = ( %s ^ -u a )' % (zeta, zeta))], '%s = ( ( %s ` %s ) x. ( %s ^ -u a ) )' % (TB('a'), YB, Z('a'), zeta)))])
    cj2 = D(w, A, 'eqtrd', [cj1, D(w, A, 'sumeq2dv', [tt], '%s = %s' % (SUM('( * ` %s )' % TY('a')), SUM(TB('a'))))], '( * ` %s ) = %s' % (SUM(TY('a')), SUM(TB('a'))))
    n1z = cst(w, A, 'neg1z', '-u 1 e. ZZ')
    g1 = D(w, A, 'eqtrd', [D(w, A, 'syl2anc', [cst(w, A, '1z', '1 e. ZZ'), D(w, A, 'nnzd', [mn], 'M e. ZZ'), w.inst('neggcd')], '( -u 1 gcd M ) = ( 1 gcd M )'),
                           D(w, A, 'syl', [D(w, A, 'nnzd', [mn], 'M e. ZZ'), w.inst('1gcd')], '( 1 gcd M ) = 1')], '( -u 1 gcd M ) = 1')
    sh = D(w, A, 'syl3anc', [D(w, A, 'jca', [mn, ybd], '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % YB), n1z, g1, w.inst('dchrgsshiftr')],
           '%s = ( ( ( %s ` %s ) ` %s ) x. ( M DChrGS %s ) )' % (SUM(TB('a')), INV, YB, Z('-u 1'), YB))
    ii = invinv(w, A, mn, yd)
    y1 = '( Y ` %s )' % Z('-u 1')
    sh2 = D(w, A, 'eqtrd', [sh, D(w, A, 'oveq1d', [D(w, A, 'fveq1d', [ii], '( ( %s ` %s ) ` %s ) = %s' % (INV, YB, Z('-u 1'), y1))],
                                                  '( ( ( %s ` %s ) ` %s ) x. ( M DChrGS %s ) ) = ( %s x. ( M DChrGS %s ) )' % (INV, YB, Z('-u 1'), YB, y1, YB))],
            '%s = ( %s x. ( M DChrGS %s ) )' % (SUM(TB('a')), y1, YB))
    TAU, TAUB = '( M DChrGS Y )', '( M DChrGS %s )' % YB
    cjt = D(w, A, 'eqtrd', [D(w, A, 'fveq2d', [gY], '( * ` %s ) = ( * ` %s )' % (TAU, SUM(TY('a')))), D(w, A, 'eqtrd', [cj2, sh2], '( * ` %s ) = ( %s x. %s )' % (SUM(TY('a')), y1, TAUB))],
            '( * ` %s ) = ( %s x. %s )' % (TAU, y1, TAUB))
    tc = D(w, A, 'syl', [ch, w.inst('dchrgscl')], '%s e. CC' % TAU)
    tbc = D(w, A, 'syl', [D(w, A, 'jca', [mn, ybd], '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % YB), w.inst('dchrgscl')], '%s e. CC' % TAUB)
    ab = D(w, A, 'syl', [pr, w.inst('dchrgsabs')], '( ( abs ` %s ) ^ 2 ) = M' % TAU)
    av = D(w, A, 'syl', [tc, w.inst('absvalsq')], '( ( abs ` %s ) ^ 2 ) = ( %s x. ( * ` %s ) )' % (TAU, TAU, TAU))
    k1 = D(w, A, 'eqtr3d', [av, ab], '( %s x. ( * ` %s ) ) = M' % (TAU, TAU))
    k2 = D(w, A, 'eqtr3d', [D(w, A, 'oveq2d', [cjt], '( %s x. ( * ` %s ) ) = ( %s x. ( %s x. %s ) )' % (TAU, TAU, TAU, y1, TAUB)), k1], '( %s x. ( %s x. %s ) ) = M' % (TAU, y1, TAUB))
    # Y ( -1 ) ^ 2 = 1
    y1e = D(w, A, 'simpld', [D(w, A, 'simprd', [par], '( %s = ( -u 1 ^ %s ) /\\ ( %s ` %s ) = ( -u 1 ^ %s ) )' % (y1, LE.PAR, YB, Z('-u 1'), LE.PAR))], '%s = ( -u 1 ^ %s )' % (y1, LE.PAR))
    ppar = D(w, A, 'simpld', [D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (LE.PAR, YB))], '%s e. { 0 , 1 }' % LE.PAR)
    PAR = LE.PAR
    A0 = '( %s /\\ %s = 0 )' % (A, PAR); A1 = '( %s /\\ %s = 1 )' % (A, PAR)
    SQ = '( ( -u 1 ^ %s ) x. ( -u 1 ^ %s ) ) = 1' % (PAR, PAR)
    s0 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (A0, PAR))], 'oveq2d', '( %s -> ( -u 1 ^ %s ) = ( -u 1 ^ 0 ) )' % (A0, PAR)),
                   w.s([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'exp0i' if False else 'a1i', '( %s -> -u 1 e. CC )' % A0)], 'exp0d', '( %s -> ( -u 1 ^ 0 ) = 1 )' % A0)], 'eqtrd', '( %s -> ( -u 1 ^ %s ) = 1 )' % (A0, PAR))], 'idi',
             '( %s -> ( -u 1 ^ %s ) = 1 )' % (A0, PAR))
    s0b = w.s([w.s([s0, s0], 'oveq12d', '( %s -> ( ( -u 1 ^ %s ) x. ( -u 1 ^ %s ) ) = ( 1 x. 1 ) )' % (A0, PAR, PAR)), cst(w, A0, '1t1e1', '( 1 x. 1 ) = 1')], 'eqtrd', '( %s -> %s )' % (A0, SQ))
    e1 = w.s([w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, PAR))], 'oveq2d', '( %s -> ( -u 1 ^ %s ) = ( -u 1 ^ 1 ) )' % (A1, PAR))
    e1b = w.s([e1, w.s([cst(w, A1, 'neg1cn', '-u 1 e. CC')], 'exp1d', '( %s -> ( -u 1 ^ 1 ) = -u 1 )' % A1)], 'eqtrd', '( %s -> ( -u 1 ^ %s ) = -u 1 )' % (A1, PAR))
    s1b = w.s([w.s([e1b, e1b], 'oveq12d', '( %s -> ( ( -u 1 ^ %s ) x. ( -u 1 ^ %s ) ) = ( -u 1 x. -u 1 ) )' % (A1, PAR, PAR)),
               cst(w, A1, 'neg1mulneg1e1', '( -u 1 x. -u 1 ) = 1')], 'eqtrd', '( %s -> %s )' % (A1, SQ))
    sq = w.s([s0b, s1b, w.s([ppar, w.inst('elpri')], 'syl', '( %s -> ( %s = 0 \\/ %s = 1 ) )' % (A, PAR, PAR))], 'mpjaodan', '( %s -> %s )' % (A, SQ))
    yy = D(w, A, 'eqtrd', [D(w, A, 'oveq12d', [y1e, y1e], '( %s x. %s ) = ( ( -u 1 ^ %s ) x. ( -u 1 ^ %s ) )' % (y1, y1, PAR, PAR)), sq], '( %s x. %s ) = 1' % (y1, y1))
    y1c = D(w, A, 'eqeltrd', [y1e, D(w, A, 'expcld', [cst(w, A, 'neg1cn', '-u 1 e. CC'), par_nn0(w, A, ppar, PAR)], '( -u 1 ^ %s ) e. CC' % PAR)], '%s e. CC' % y1)
    # Y1 ( tau ( Y1 tau~ ) ) = Y1 M ; left = ( Y1 Y1 ) ( tau tau~ ) = tau tau~
    tt2 = chain(w, A, ['( %s x. %s )' % (TAU, TAUB), '( 1 x. ( %s x. %s ) )' % (TAU, TAUB), '( ( %s x. %s ) x. ( %s x. %s ) )' % (y1, y1, TAU, TAUB),
                       '( %s x. ( %s x. ( %s x. %s ) ) )' % (y1, TAU, y1, TAUB), '( %s x. M )' % y1],
                [('r', D(w, A, 'mullidd', [D(w, A, 'mulcld', [tc, tbc], '( %s x. %s ) e. CC' % (TAU, TAUB))], '( 1 x. ( %s x. %s ) ) = ( %s x. %s )' % (TAU, TAUB, TAU, TAUB))),
                 ('r', D(w, A, 'oveq1d', [yy], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( 1 x. ( %s x. %s ) )' % (y1, y1, TAU, TAUB, TAU, TAUB))),
                 D(w, A, 'mul4d', [y1c, y1c, tc, tbc], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (y1, y1, TAU, TAUB, y1, TAU, y1, TAUB)) if False else
                 D(w, A, 'eqtrd', [D(w, A, 'mul4d', [y1c, y1c, tc, tbc], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (y1, y1, TAU, TAUB, y1, TAU, y1, TAUB)),
                                   D(w, A, 'mulassd', [y1c, tc, D(w, A, 'mulcld', [y1c, tbc], '( %s x. %s ) e. CC' % (y1, TAUB))], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (y1, TAU, y1, TAUB, y1, TAU, y1, TAUB))],
                   '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (y1, y1, TAU, TAUB, y1, TAU, y1, TAUB)),
                 D(w, A, 'oveq2d', [k2], '( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. M )' % (y1, TAU, y1, TAUB, y1))])
    w.qed([tt2], 'idi', SE['zl3gsp'])
    goe(w)


# ---------------------------------------------------------------- zl3yb
if wante('zl3yb', MAIN):
    w = W('zl3yb', 'The inverse character ` YB ` of a primitive ` Y ` is primitive with the same parity, its inverse is ` Y ` , and the two root numbers multiply to 1 ( ~ zl3gsp ).')
    A, Cc = ante_e('zl3yb')
    pr = w.s([], 'id', '( %s -> %s )' % (A, A))
    ch, mn, yd, cond = pr_facts(w, A, pr)
    PAR, PARB, EPS, EPSB = LE.PAR, LE.PARB, LE.EPS, LE.EPSB
    par = D(w, A, 'syl', [ch, w.inst('zl3par')], L.split_imp(L.STATEMENTS['zl3par'])[1])
    pq = D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (PAR, YB))
    ppar = D(w, A, 'simpld', [pq], '%s e. { 0 , 1 }' % PAR); ybd = D(w, A, 'simprd', [pq], '%s e. ( Base ` ( DChr ` M ) )' % YB)
    Z = lambda a: '( %s ` %s )' % (LM, a)
    y1, yb1 = '( Y ` %s )' % Z('-u 1'), '( %s ` %s )' % (YB, Z('-u 1'))
    pv = D(w, A, 'simprd', [par], '( %s = ( -u 1 ^ %s ) /\\ %s = ( -u 1 ^ %s ) )' % (y1, PAR, yb1, PAR))
    ye, ybe = D(w, A, 'simpld', [pv], '%s = ( -u 1 ^ %s )' % (y1, PAR)), D(w, A, 'simprd', [pv], '%s = ( -u 1 ^ %s )' % (yb1, PAR))
    cinv = D(w, A, 'eqtrd', [D(w, A, 'syl', [ch, w.inst('dchrcondinv')], '( M DChrCond %s ) = ( M DChrCond Y )' % YB), cond], '( M DChrCond %s ) = M' % YB)
    prb = D(w, A, 'jca', [D(w, A, 'jca', [mn, ybd], '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % YB), cinv], LE.PRB)
    yy = D(w, A, 'eqtr4d', [ybe, ye], '%s = %s' % (yb1, y1))
    pe = D(w, A, 'ifbid', [D(w, A, 'eqeq1d', [yy], '( %s = 1 <-> %s = 1 )' % (yb1, y1))], '%s = %s' % (PARB, PAR))
    ii = invinv(w, A, mn, yd)
    # root numbers
    pn = par_nn0(w, A, ppar, PAR)
    ic = cst(w, A, 'ax-icn', '_i e. CC')
    ia = D(w, A, 'expcld', [ic, pn], '( _i ^ %s ) e. CC' % PAR)
    mc = D(w, A, 'nncnd', [mn], 'M e. CC'); mne = D(w, A, 'nnne0d', [mn], 'M =/= 0')
    hc = cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')
    sm = '( M ^c ( 1 / 2 ) )'
    smc = D(w, A, 'cxpcld', [mc, hc], '%s e. CC' % sm); smne = D(w, A, 'cxpne0d', [mc, mne, hc], '%s =/= 0' % sm)
    ian = D(w, A, 'expne0d', [ic, cst(w, A, 'ine0', '_i =/= 0'), D(w, A, 'nn0zd', [pn], '%s e. ZZ' % PAR)], '( _i ^ %s ) =/= 0' % PAR)
    Q = '( ( _i ^ %s ) x. %s )' % (PAR, sm)
    qc = D(w, A, 'mulcld', [ia, smc], '%s e. CC' % Q); qne = D(w, A, 'mulne0d', [ia, ian, smc, smne], '%s =/= 0' % Q)
    EPSB2 = '( ( M DChrGS %s ) / %s )' % (YB, Q)
    eb = D(w, A, 'oveq2d', [D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [pe], '( _i ^ %s ) = ( _i ^ %s )' % (PARB, PAR))], '( ( _i ^ %s ) x. %s ) = %s' % (PARB, sm, Q))], '%s = %s' % (EPSB, EPSB2))
    TAU, TAUB = '( M DChrGS Y )', '( M DChrGS %s )' % YB
    tc = D(w, A, 'syl', [ch, w.inst('dchrgscl')], '%s e. CC' % TAU)
    tbc = D(w, A, 'syl', [D(w, A, 'jca', [mn, ybd], '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % YB), w.inst('dchrgscl')], '%s e. CC' % TAUB)
    m1a = '( -u 1 ^ %s )' % PAR
    qq = chain(w, A, ['( %s x. %s )' % (Q, Q), '( ( ( _i ^ %s ) x. ( _i ^ %s ) ) x. ( %s x. %s ) )' % (PAR, PAR, sm, sm), '( %s x. M )' % m1a],
               [D(w, A, 'mul4d', [ia, smc, ia, smc], '( %s x. %s ) = ( ( ( _i ^ %s ) x. ( _i ^ %s ) ) x. ( %s x. %s ) )' % (Q, Q, PAR, PAR, sm, sm)),
                D(w, A, 'oveq12d', [D(w, A, 'eqtr3d', [D(w, A, 'mulexpd', [ic, ic, pn], '( ( _i x. _i ) ^ %s ) = ( ( _i ^ %s ) x. ( _i ^ %s ) )' % (PAR, PAR, PAR)),
                                                        D(w, A, 'oveq1d', [cst(w, A, 'ixi', '( _i x. _i ) = -u 1')], '( ( _i x. _i ) ^ %s ) = %s' % (PAR, m1a))],
                                      '( ( _i ^ %s ) x. ( _i ^ %s ) ) = %s' % (PAR, PAR, m1a)),
                                    D(w, A, 'eqtr3d', [D(w, A, 'cxpaddd', [mc, mne, hc, hc], '( M ^c ( ( 1 / 2 ) + ( 1 / 2 ) ) ) = ( %s x. %s )' % (sm, sm)),
                                                       D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [cst(w, A, '2halves', '( ( 1 / 2 ) + ( 1 / 2 ) ) = 1') if False else
                                                                                           w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('2halves')], 'ax-mp', '( ( 1 / 2 ) + ( 1 / 2 ) ) = 1')], 'a1i', '( %s -> ( ( 1 / 2 ) + ( 1 / 2 ) ) = 1 )' % A)],
                                                                                '( M ^c ( ( 1 / 2 ) + ( 1 / 2 ) ) ) = ( M ^c 1 )'), D(w, A, 'cxp1d', [mc], '( M ^c 1 ) = M')],
                                                         '( M ^c ( ( 1 / 2 ) + ( 1 / 2 ) ) ) = M')], '( %s x. %s ) = M' % (sm, sm))],
                  '( ( ( _i ^ %s ) x. ( _i ^ %s ) ) x. ( %s x. %s ) ) = ( %s x. M )' % (PAR, PAR, sm, sm, m1a))])
    gsp = D(w, A, 'syl', [pr, w.inst('zl3gsp')], '( %s x. %s ) = ( %s x. M )' % (TAU, TAUB, y1))
    num = D(w, A, 'eqtrd', [gsp, D(w, A, 'oveq1d', [ye], '( %s x. M ) = ( %s x. M )' % (y1, m1a))], '( %s x. %s ) = ( %s x. M )' % (TAU, TAUB, m1a))
    m1c = D(w, A, 'expcld', [cst(w, A, 'neg1cn', '-u 1 e. CC'), pn], '%s e. CC' % m1a)
    m1n = D(w, A, 'expne0d', [cst(w, A, 'neg1cn', '-u 1 e. CC'), cst(w, A, 'neg1ne0', '-u 1 =/= 0'), D(w, A, 'nn0zd', [pn], '%s e. ZZ' % PAR)], '%s =/= 0' % m1a)
    prodE = chain(w, A, ['( %s x. %s )' % (EPS, EPSB2), '( ( %s x. %s ) / ( %s x. %s ) )' % (TAU, TAUB, Q, Q), '( ( %s x. M ) / ( %s x. M ) )' % (m1a, m1a), '1'],
                  [D(w, A, 'divmuldivd', [tc, qc, tbc, qc, qne, qne], '( %s x. %s ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (EPS, EPSB2, TAU, TAUB, Q, Q)),
                   D(w, A, 'oveq12d', [num, qq], '( ( %s x. %s ) / ( %s x. %s ) ) = ( ( %s x. M ) / ( %s x. M ) )' % (TAU, TAUB, Q, Q, m1a, m1a)),
                   D(w, A, 'dividd', [D(w, A, 'mulcld', [m1c, mc], '( %s x. M ) e. CC' % m1a), D(w, A, 'mulne0d', [m1c, m1n, mc, mne], '( %s x. M ) =/= 0' % m1a)], '( ( %s x. M ) / ( %s x. M ) ) = 1' % (m1a, m1a))])
    ep = D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [eb], '( %s x. %s ) = ( %s x. %s )' % (EPS, EPSB, EPS, EPSB2)), prodE], '( %s x. %s ) = 1' % (EPS, EPSB))
    w.qed([D(w, A, 'jca', [D(w, A, 'jca', [prb, pe], '( %s /\\ %s = %s )' % (LE.PRB, PARB, PAR)), D(w, A, 'jca', [ii, ep], '( %s = Y /\\ ( %s x. %s ) = 1 )' % (LE.INVB, EPS, EPSB))], Cc)],
          'idi', SE['zl3yb'])
    goe(w)


# ---------------------------------------------------------------- zl3ilp
if wante('zl3ilp', MAIN):
    w = W('zl3ilp', 'Congruence of the theta integral ` IL ` in the parity and the coefficient function.')
    A, Cc = ante_e('zl3ilp')
    pq = D(w, A, 'simpl', [], 'P = Q'); cd = D(w, A, 'simpr', [], 'C = D')
    EXn = '( exp ` -u ( ( _pi x. ( n ^ 2 ) ) x. ( y / M ) ) )'
    T = lambda C, P: '( ( %s ` n ) x. ( ( n ^ %s ) x. %s ) )' % (C, P, EXn)
    Ay = '( ( %s /\\ t e. RR+ ) /\\ y e. ( 1 (,) t ) )' % A
    An = '( %s /\\ n e. NN )' % Ay
    pqn = ad(w, An, ad(w, Ay, ad(w, '( %s /\\ t e. RR+ )' % A, pq, 'P = Q'), 'P = Q'), 'P = Q')
    cdn = ad(w, An, ad(w, Ay, ad(w, '( %s /\\ t e. RR+ )' % A, cd, 'C = D'), 'C = D'), 'C = D')
    te = D(w, An, 'oveq12d', [D(w, An, 'fveq1d', [cdn], '( C ` n ) = ( D ` n )'), D(w, An, 'oveq1d', [D(w, An, 'oveq2d', [pqn], '( n ^ P ) = ( n ^ Q )')], '( ( n ^ P ) x. %s ) = ( ( n ^ Q ) x. %s )' % (EXn, EXn))],
           '%s = %s' % (T('C', 'P'), T('D', 'Q')))
    se = D(w, Ay, 'sumeq2dv', [te], '%s = %s' % (LE.THG('C', 'y', 'P'), LE.THG('D', 'y', 'Q')))
    pqy = ad(w, Ay, ad(w, '( %s /\\ t e. RR+ )' % A, pq, 'P = Q'), 'P = Q')
    ex = D(w, Ay, 'oveq2d', [D(w, Ay, 'oveq1d', [D(w, Ay, 'oveq1d', [D(w, Ay, 'oveq2d', [pqy], '( S + P ) = ( S + Q )')], '( ( S + P ) / 2 ) = ( ( S + Q ) / 2 )')],
                                         '( ( ( S + P ) / 2 ) - 1 ) = ( ( ( S + Q ) / 2 ) - 1 )')], '( y ^c ( ( ( S + P ) / 2 ) - 1 ) ) = ( y ^c ( ( ( S + Q ) / 2 ) - 1 ) )')
    ig = D(w, Ay, 'oveq12d', [se, ex], '( %s x. ( y ^c ( ( ( S + P ) / 2 ) - 1 ) ) ) = ( %s x. ( y ^c ( ( ( S + Q ) / 2 ) - 1 ) ) )' % (LE.THG('C', 'y', 'P'), LE.THG('D', 'y', 'Q')))
    It = lambda C, P, Q_: 'S. ( 1 (,) t ) ( %s x. ( y ^c ( ( ( S + %s ) / 2 ) - 1 ) ) ) _d y' % (LE.THG(C, 'y', P), Q_)
    iq = D(w, '( %s /\\ t e. RR+ )' % A, 'itgeq2dv', [ig], '%s = %s' % (It('C', 'P', 'P'), It('D', 'Q', 'Q')))
    mq = D(w, A, 'mpteq2dva', [iq], '( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s )' % (It('C', 'P', 'P'), It('D', 'Q', 'Q')))
    w.qed([D(w, A, 'fveq2d', [mq], Cc)], 'idi', SE['zl3ilp'])
    goe(w)


# ---------------------------------------------------------------- zl3mlb
if wante('zl3mlb', MAIN):
    w = W('zl3mlb', 'The Mellin identity ~ zl3mel for the inverse character ` YB ` , written with the parity and the coefficients of ` Y ` ( ~ zl3yb , ~ zl3ilp ).')
    A, Cc = ante_e('zl3mlb')
    pr = w.s([], 'id', '( %s -> %s )' % (A, A))
    PAR, PARB, EPSB = LE.PAR, LE.PARB, LE.EPSB
    CYM, CYBM = LE.CYM, LE.CYBM
    CYBB = LE.tsub(CYBM, {'Y': YB})
    yb = D(w, A, 'syl', [pr, w.inst('zl3yb')], L.split_imp(SE['zl3yb'])[1])
    prb = D(w, A, 'simpld', [D(w, A, 'simpld', [yb], '( %s /\\ %s = %s )' % (LE.PRB, PARB, PAR))], LE.PRB)
    pe = D(w, A, 'simprd', [D(w, A, 'simpld', [yb], '( %s /\\ %s = %s )' % (LE.PRB, PARB, PAR))], '%s = %s' % (PARB, PAR))
    ii = D(w, A, 'simpld', [D(w, A, 'simprd', [yb], '( %s = Y /\\ ( %s x. %s ) = 1 )' % (LE.INVB, LE.EPS, EPSB))], '%s = Y' % LE.INVB)
    MELB = LE.tsub(L.split_imp(Z3S := LE.Z3.STATEMENTS['zl3mel'])[1], {'Y': YB})
    melb = D(w, A, 'syl', [prb, w.inst('zl3mel')], MELB)
    As = '( %s /\\ s e. CC )' % A
    L1 = lambda st, f: ad(w, As, st, f)
    pes = L1(pe, '%s = %s' % (PARB, PAR))
    GB, G0 = LE.GAMFG('s', PARB), LE.GAMFG('s', PAR)
    ge = D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [pes], '( s + %s ) = ( s + %s )' % (PARB, PAR))], '( ( s + %s ) / 2 ) = ( ( s + %s ) / 2 )' % (PARB, PAR))],
                                               '( ( M / _pi ) ^c ( ( s + %s ) / 2 ) ) = ( ( M / _pi ) ^c ( ( s + %s ) / 2 ) )' % (PARB, PAR)),
                              D(w, As, 'fveq2d', [D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [pes], '( s + %s ) = ( s + %s )' % (PARB, PAR))], '( ( s + %s ) / 2 ) = ( ( s + %s ) / 2 )' % (PARB, PAR))],
                                '( _G ` ( ( s + %s ) / 2 ) ) = ( _G ` ( ( s + %s ) / 2 ) )' % (PARB, PAR))], '%s = %s' % (GB, G0))
    LSB = LE.Z3.LS(CYBM, 's')
    lhs = D(w, As, 'oveq1d', [ge], '( %s x. %s ) = ( %s x. %s )' % (GB, LSB, G0, LSB))
    ILP = lambda C, S, P, D_, Q: '( ( %s = %s /\\ %s = %s ) -> %s = %s )' % (P, Q, C, D_, LE.ILG(C, S, P), LE.ILG(D_, S, Q))
    i1 = D(w, As, 'syl', [D(w, As, 'jca', [pes, D(w, As, 'eqidd', [], '%s = %s' % (CYBM, CYBM))], '( %s = %s /\\ %s = %s )' % (PARB, PAR, CYBM, CYBM)),
                          w.s([], 'zl3ilp', ILP(CYBM, 's', PARB, CYBM, PAR))], '%s = %s' % (LE.ILG(CYBM, 's', PARB), LE.ILG(CYBM, 's', PAR)))
    cbe = D(w, As, 'mpteq2dv', [D(w, As, 'fveq1d', [L1(ii, '%s = Y' % LE.INVB)], '( %s ` ( %s ` a ) ) = ( Y ` ( %s ` a ) )' % (LE.INVB, LM, LM))], '%s = %s' % (CYBB, CYM))
    i2 = D(w, As, 'syl', [D(w, As, 'jca', [pes, cbe], '( %s = %s /\\ %s = %s )' % (PARB, PAR, CYBB, CYM)), w.s([], 'zl3ilp', ILP(CYBB, '( 1 - s )', PARB, CYM, PAR))],
           '%s = %s' % (LE.ILG(CYBB, '( 1 - s )', PARB), LE.ILG(CYM, '( 1 - s )', PAR)))
    PT = '( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) )' % LE.RM
    RB = '( ( %s + ( %s x. %s ) ) - %s )' % (LE.ILG(CYBM, 's', PARB), EPSB, LE.ILG(CYBB, '( 1 - s )', PARB), PT)
    R0 = '( ( %s + ( %s x. %s ) ) - %s )' % (LE.ILG(CYBM, 's', PAR), EPSB, LE.ILG(CYM, '( 1 - s )', PAR), PT)
    rhs = D(w, As, 'oveq1d', [D(w, As, 'oveq12d', [i1, D(w, As, 'oveq2d', [i2], '( %s x. %s ) = ( %s x. %s )' % (EPSB, LE.ILG(CYBB, '( 1 - s )', PARB), EPSB, LE.ILG(CYM, '( 1 - s )', PAR)))],
                                           '( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) )' % (LE.ILG(CYBM, 's', PARB), EPSB, LE.ILG(CYBB, '( 1 - s )', PARB), LE.ILG(CYBM, 's', PAR), EPSB, LE.ILG(CYM, '( 1 - s )', PAR)))],
              '%s = %s' % (RB, R0))
    EQB, EQ0 = '( %s x. %s ) = %s' % (GB, LSB, RB), '( %s x. %s ) = %s' % (G0, LSB, R0)
    bi = D(w, As, 'imbi2d', [D(w, As, 'eqeq12d', [lhs, rhs], '( %s <-> %s )' % (EQB, EQ0))], '( ( 1 < ( Re ` s ) -> %s ) <-> ( 1 < ( Re ` s ) -> %s ) )' % (EQB, EQ0))
    assert MELB == 'A. s e. CC ( 1 < ( Re ` s ) -> %s )' % EQB, MELB[:300]
    ra = D(w, A, 'ralbidva', [bi], '( A. s e. CC ( 1 < ( Re ` s ) -> %s ) <-> A. s e. CC ( 1 < ( Re ` s ) -> %s ) )' % (EQB, EQ0))
    fin = D(w, A, 'mpbid', [melb, ra], 'A. s e. CC ( 1 < ( Re ` s ) -> %s )' % EQ0)
    w.qed([fin], 'idi', SE['zl3mlb'])
    goe(w)
