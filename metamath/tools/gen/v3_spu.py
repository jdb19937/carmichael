"""Sortie v3: a sum over a set that injects into a product of two index sets.

sumprodub  ( ( ( S e. Fin /\\ T e. Fin /\\ U e. Fin ) /\\
               ( G : S --> ( 0 [,) +oo ) /\\ H : T --> ( 0 [,) +oo ) ) /\\
               F : U -1-1-> ( S X. T ) ) ->
             sum_ m e. U ( ( G ` ( 1st ` ( F ` m ) ) ) x. ( H ` ( 2nd ` ( F ` m ) ) ) )
               <_ ( sum_ i e. S ( G ` i ) x. sum_ j e. T ( H ` j ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst
from cl import lift

A = ('( ( S e. Fin /\\ T e. Fin /\\ U e. Fin ) /\\ '
     '( G : S --> ( 0 [,) +oo ) /\\ H : T --> ( 0 [,) +oo ) ) /\\ '
     'F : U -1-1-> ( S X. T ) )')
XT = '( S X. T )'


def BODY(u):
    return '( ( G ` ( 1st ` %s ) ) x. ( H ` ( 2nd ` %s ) ) )' % (u, u)


BU = BODY('u')
BFM = BODY('( F ` m )')
SUMU = 'sum_ m e. U %s' % BFM
SUMR = 'sum_ u e. ran F %s' % BU
SUMX = 'sum_ u e. %s %s' % (XT, BU)
SUMD = 'sum_ i e. S sum_ j e. T ( ( G ` i ) x. ( H ` j ) )'
SG = 'sum_ i e. S ( G ` i )'
SH = 'sum_ j e. T ( H ` j )'


def nnegfacts(w, ante, expr, mem):
    """( ante -> expr e. RR ) and ( ante -> 0 <_ expr ) from ( ante -> expr e. ( 0 [,) +oo ) )"""
    f = mkst(w, ante)
    b = f([f([w.s([], 'elrege0',
                  '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
             'a1i', '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr)),
           mem], 'mpbid', '( %s e. RR /\\ 0 <_ %s )' % (expr, expr))
    return f([b], 'simpld', '%s e. RR' % expr), f([b], 'simprd', '0 <_ %s' % expr)


def sumprodub():
    w = WS('sumprodub', 'A sum of a product-shaped nonnegative term over a set that injects '
                        'into a product of two index sets is at most the product of the two sums.')
    st = mkst(w, A)
    fins = st([], 'simp1', '( S e. Fin /\\ T e. Fin /\\ U e. Fin )')
    sfin = st([fins], 'simp1d', 'S e. Fin')
    tfin = st([fins], 'simp2d', 'T e. Fin')
    ufin = st([fins], 'simp3d', 'U e. Fin')
    ghs = st([], 'simp2', '( G : S --> ( 0 [,) +oo ) /\\ H : T --> ( 0 [,) +oo ) )')
    gf = st([ghs], 'simpld', 'G : S --> ( 0 [,) +oo )')
    hf = st([ghs], 'simprd', 'H : T --> ( 0 [,) +oo )')
    f1 = st([], 'simp3', 'F : U -1-1-> %s' % XT)
    f1o = st([f1, w.inst('f1f1orn')], 'syl', 'F : U -1-1-onto-> ran F')
    ff = st([f1, w.inst('f1f')], 'syl', 'F : U --> %s' % XT)
    rnss = st([ff, w.inst('frn')], 'syl', 'ran F C_ %s' % XT)
    xfin = st([sfin, tfin, w.inst('xpfi')], 'syl2anc', '%s e. Fin' % XT)
    # closures of the body on ( S X. T )
    AU = '( %s /\\ u e. %s )' % (A, XT)
    su = mkst(w, AU)
    u1 = su([su([], 'simpr', 'u e. %s' % XT), w.inst('xp1st')], 'syl', '( 1st ` u ) e. S')
    u2 = su([su([], 'simpr', 'u e. %s' % XT), w.inst('xp2nd')], 'syl', '( 2nd ` u ) e. T')
    gu = su([lift(w, gf, AU), u1, w.inst('ffvelcdm')], 'syl2anc',
            '( G ` ( 1st ` u ) ) e. ( 0 [,) +oo )')
    hu = su([lift(w, hf, AU), u2, w.inst('ffvelcdm')], 'syl2anc',
            '( H ` ( 2nd ` u ) ) e. ( 0 [,) +oo )')
    gur, gu0 = nnegfacts(w, AU, '( G ` ( 1st ` u ) )', gu)
    hur, hu0 = nnegfacts(w, AU, '( H ` ( 2nd ` u ) )', hu)
    bur = su([gur, hur], 'remulcld', '%s e. RR' % BU)
    bu0 = su([gur, hur, gu0, hu0], 'mulge0d', '0 <_ %s' % BU)
    buc = su([bur], 'recnd', '%s e. CC' % BU)
    # the body on ran F is the same expression restricted
    AR = '( %s /\\ u e. ran F )' % A
    sr = mkst(w, AR)
    urx = sr([lift(w, rnss, AR), sr([], 'simpr', 'u e. ran F')], 'sseldd', 'u e. %s' % XT)
    r1 = sr([urx, w.inst('xp1st')], 'syl', '( 1st ` u ) e. S')
    r2 = sr([urx, w.inst('xp2nd')], 'syl', '( 2nd ` u ) e. T')
    gr = sr([lift(w, gf, AR), r1, w.inst('ffvelcdm')], 'syl2anc',
            '( G ` ( 1st ` u ) ) e. ( 0 [,) +oo )')
    hr = sr([lift(w, hf, AR), r2, w.inst('ffvelcdm')], 'syl2anc',
            '( H ` ( 2nd ` u ) ) e. ( 0 [,) +oo )')
    grr, _ = nnegfacts(w, AR, '( G ` ( 1st ` u ) )', gr)
    hrr, _ = nnegfacts(w, AR, '( H ` ( 2nd ` u ) )', hr)
    brc = sr([sr([grr, hrr], 'remulcld', '%s e. RR' % BU)], 'recnd', '%s e. CC' % BU)
    # step 1: fsumf1o from ran F to U
    sb1 = w.s([w.s([], 'fveq2', '( u = ( F ` m ) -> ( 1st ` u ) = ( 1st ` ( F ` m ) ) )')],
              'fveq2d', '( u = ( F ` m ) -> ( G ` ( 1st ` u ) ) = ( G ` ( 1st ` ( F ` m ) ) ) )')
    sb2 = w.s([w.s([], 'fveq2', '( u = ( F ` m ) -> ( 2nd ` u ) = ( 2nd ` ( F ` m ) ) )')],
              'fveq2d', '( u = ( F ` m ) -> ( H ` ( 2nd ` u ) ) = ( H ` ( 2nd ` ( F ` m ) ) ) )')
    sb = w.s([sb1, sb2], 'oveq12d', '( u = ( F ` m ) -> %s = %s )' % (BU, BFM))
    AM = '( %s /\\ m e. U )' % A
    sm = mkst(w, AM)
    eqi = sm([], 'eqidd', '( F ` m ) = ( F ` m )')
    e1 = st([sb, ufin, f1o, eqi, brc], 'fsumf1o', '%s = %s' % (SUMR, SUMU))
    # step 2: fsumless up to the whole product set
    le1 = st([xfin, bur, bu0, rnss], 'fsumless', '%s <_ %s' % (SUMR, SUMX))
    # step 3: fsumxp
    iv = w.s([], 'vex', 'i e. _V')
    jv = w.s([], 'vex', 'j e. _V')
    o1 = w.s([iv, jv], 'op1st', '( 1st ` <. i , j >. ) = i')
    o2 = w.s([iv, jv], 'op2nd', '( 2nd ` <. i , j >. ) = j')
    x1 = w.s([w.s([], 'fveq2', '( u = <. i , j >. -> ( 1st ` u ) = ( 1st ` <. i , j >. ) )'),
              w.s([o1], 'a1i', '( u = <. i , j >. -> ( 1st ` <. i , j >. ) = i )')],
             'eqtrd', '( u = <. i , j >. -> ( 1st ` u ) = i )')
    x2 = w.s([w.s([], 'fveq2', '( u = <. i , j >. -> ( 2nd ` u ) = ( 2nd ` <. i , j >. ) )'),
              w.s([o2], 'a1i', '( u = <. i , j >. -> ( 2nd ` <. i , j >. ) = j )')],
             'eqtrd', '( u = <. i , j >. -> ( 2nd ` u ) = j )')
    x3 = w.s([w.s([x1], 'fveq2d', '( u = <. i , j >. -> ( G ` ( 1st ` u ) ) = ( G ` i ) )'),
              w.s([x2], 'fveq2d', '( u = <. i , j >. -> ( H ` ( 2nd ` u ) ) = ( H ` j ) )')],
             'oveq12d', '( u = <. i , j >. -> %s = ( ( G ` i ) x. ( H ` j ) ) )' % BU)
    AIJ = '( %s /\\ ( i e. S /\\ j e. T ) )' % A
    sij = mkst(w, AIJ)
    gi = sij([lift(w, gf, AIJ), sij([sij([], 'simpr', '( i e. S /\\ j e. T )')], 'simpld',
                                    'i e. S'), w.inst('ffvelcdm')], 'syl2anc',
             '( G ` i ) e. ( 0 [,) +oo )')
    hj = sij([lift(w, hf, AIJ), sij([sij([], 'simpr', '( i e. S /\\ j e. T )')], 'simprd',
                                    'j e. T'), w.inst('ffvelcdm')], 'syl2anc',
             '( H ` j ) e. ( 0 [,) +oo )')
    gir, _ = nnegfacts(w, AIJ, '( G ` i )', gi)
    hjr, _ = nnegfacts(w, AIJ, '( H ` j )', hj)
    ijc = sij([sij([gir, hjr], 'remulcld', '( ( G ` i ) x. ( H ` j ) ) e. RR')], 'recnd',
              '( ( G ` i ) x. ( H ` j ) ) e. CC')
    e2 = st([x3, sfin, tfin, ijc], 'fsumxp', '%s = %s' % (SUMD, SUMX))
    # step 4: the double sum is the product of the two sums
    AI = '( %s /\\ i e. S )' % A
    si = mkst(w, AI)
    gi2 = si([lift(w, gf, AI), si([], 'simpr', 'i e. S'), w.inst('ffvelcdm')], 'syl2anc',
             '( G ` i ) e. ( 0 [,) +oo )')
    gi2r, _ = nnegfacts(w, AI, '( G ` i )', gi2)
    gi2c = si([gi2r], 'recnd', '( G ` i ) e. CC')
    AJ = '( %s /\\ j e. T )' % A
    sj = mkst(w, AJ)
    hj2 = sj([lift(w, hf, AJ), sj([], 'simpr', 'j e. T'), w.inst('ffvelcdm')], 'syl2anc',
             '( H ` j ) e. ( 0 [,) +oo )')
    hj2r, _ = nnegfacts(w, AJ, '( H ` j )', hj2)
    hj2c = sj([hj2r], 'recnd', '( H ` j ) e. CC')
    shre = st([tfin, hj2r], 'fsumrecl', '%s e. RR' % SH)
    shc = st([shre], 'recnd', '%s e. CC' % SH)
    # ( ( G ` i ) x. sum_ j ) = sum_ j ( ( G ` i ) x. ( H ` j ) )   per i
    AIJ2 = '( ( %s /\\ i e. S ) /\\ j e. T )' % A
    sij2 = mkst(w, AIJ2)
    hj3 = sij2([lift(w, hf, AIJ2), sij2([], 'simpr', 'j e. T'), w.inst('ffvelcdm')], 'syl2anc',
               '( H ` j ) e. ( 0 [,) +oo )')
    hj3r, _ = nnegfacts(w, AIJ2, '( H ` j )', hj3)
    hj3c = sij2([hj3r], 'recnd', '( H ` j ) e. CC')
    mul2 = si([lift(w, tfin, AI), gi2c, hj3c], 'fsummulc2',
              '( ( G ` i ) x. %s ) = sum_ j e. T ( ( G ` i ) x. ( H ` j ) )' % SH)
    se = st([mul2], 'sumeq2dv',
            'sum_ i e. S ( ( G ` i ) x. %s ) = %s' % (SH, SUMD))
    mul1 = st([sfin, gi2c, shc], 'fsummulc1',
              '( %s x. %s ) = sum_ i e. S ( ( G ` i ) x. %s )' % (SG, SH, SH))
    prd = st([mul1, se], 'eqtrd', '( %s x. %s ) = %s' % (SG, SH, SUMD))
    # assemble
    sgre = st([sfin, gi2r], 'fsumrecl', '%s e. RR' % SG)
    sxre = st([xfin, bur], 'fsumrecl', '%s e. RR' % SUMX)
    sum1 = st([e1, le1], 'eqbrtrrd', '%s <_ %s' % (SUMU, SUMX))
    prd2 = st([prd, e2], 'eqtrd', '( %s x. %s ) = %s' % (SG, SH, SUMX))
    w.qed([sum1, prd2], 'breqtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (A, SUMU, SG, SH))
    return w


if __name__ == '__main__':
    sumprodub().run()
