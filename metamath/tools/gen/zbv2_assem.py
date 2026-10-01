"""Sortie ZBV2, section 4 part C2: the assembled diagonal bound, bvA over ( 1 ... |_ B ), the Rankin steps and
the endgame (Lean tsum_rpow_bvA_sq_le, bvA_eq_sum_Icc, sum_bvA_sq_div_le_tsum, rankin_alpha, bvHarm_uncond,
bvL2_star_uncond), ZBV2-blueprint.md section 3.3.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbv2lib import *
import num
import lin
lin.MAXDEG = 5
from zbv2_diag2 import phsre

PH = 'ph'
SEQ = lambda F: 'seq 1 ( + , %s )' % F
NNUZ_ = 'NN = ( ZZ>= ` 1 )'


def alsr(w, ante, jnn, j, N, h3):
    """( ante -> ALs(j,N) e. RR ) from jnn: ( ante -> j e. NN ) and h3: ( ( ph /\\ d e. ( 1 ... N ) ) -> ( L ` d ) e. RR ),
    ante = ( ph /\\ ... ) (ph the first conjunct)"""
    AD = '( %s /\\ d e. ( 1 ... %s ) )' % (ante, N)
    sd = mkst(w, AD)
    ld = hyp2(w, AD, lift(w, w.s([], 'id', '( ph -> ph )'), AD), sd([], 'simpr', 'd e. ( 1 ... %s )' % N), h3, '( L ` d ) e. RR')
    ifr = sd([ld, sd([], '0red', '0 e. RR')], 'ifcld', 'if ( d || %s , ( L ` d ) , 0 ) e. RR' % j)
    return w.s([w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (ante, N)), ifr], 'fsumrecl', '( %s -> %s e. RR )' % (ante, ALs(j, N)))


def bvdiagle():
    w = W('bvdiagle', 'The assembled diagonal bound for a generic weight L vanishing off the squarefree numbers, given '
                      '| S_m | <= m ^c -u S ( m / phi m ) K (Lean tsum_rpow_bvA_sq_le with the S_delta bound abstracted): '
                      'the series converges and its sum is at most zeta ( S ) K ^ 2 8 ( 1 + log N ) (bvtsum, bvdiag, bvwbnd).')
    h1, h2, h3, h4, h5, h6 = hyps_of(w, 'bvdiagle')
    st = mkst(w, PH)
    sr = st([h1], 'simpld', 'S e. RR'); s1 = st([h1], 'simprd', '1 < S')
    s1le = st([s1], 'ltled', '1 <_ S')
    nsr = st([sr], 'renegcld', '-u S e. RR')
    Ft = lambda v: '( ( %s ^c -u S ) x. ( %s ^ 2 ) )' % (v, ALs(v))
    MT = '( t e. NN |-> %s )' % Ft('t'); MN = '( n e. NN |-> %s )' % Ft('n')
    V = '( %s x. %s )' % (ZS(), DSUM())
    lim = w.s([h1, h2, h3], 'bvtsum', '( ph -> %s ~~> %s )' % (SEQ(MT), V))
    idtn = w.s([], 'id', '( t = n -> t = n )')
    cg, new = w.congr(Ft('t'), {'t': 'n'}, 't = n', {'t': idtn})
    assert new == Ft('n'), new
    cb = w.s([cg], 'cbvmptv', '%s = %s' % (MT, MN))
    sqe = st([st([cb], 'a1i', '%s = %s' % (MT, MN))], 'seqeq3d', '%s = %s' % (SEQ(MT), SEQ(MN)))
    limn = st([sqe, lim], 'eqbrtrrd', '%s ~~> %s' % (SEQ(MN), V))
    cvg = st([st([w.s([], 'climrel', 'Rel ~~>')], 'a1i', 'Rel ~~>'), limn, w.inst('releldm')], 'syl2anc', '%s e. dom ~~>' % SEQ(MN))
    AN = '( ph /\\ n e. NN )'; sn = mkst(w, AN)
    nnn = sn([], 'simpr', 'n e. NN')
    fr = sn([sn([sn([sn([nnn], 'nnrpd', 'n e. RR+'), lift(w, nsr, AN)], 'rpcxpcld', '( n ^c -u S ) e. RR+')], 'rpred', '( n ^c -u S ) e. RR'),
             sn([alsr(w, AN, nnn, 'n', 'N', h3)], 'resqcld', '( %s ^ 2 ) e. RR' % ALs('n'))], 'remulcld', '%s e. RR' % Ft('n'))
    vn, _ = mpv(w, AN, 't', 'NN', Ft('t'), 'n', nnn)
    z = clo(w, 'nnuz', NNUZ_)
    val = st([z, st([], '1zzd', '1 e. ZZ'), vn, sn([fr], 'recnd', '%s e. CC' % Ft('n')), lim], 'isumclim', 'sum_ n e. NN %s = %s' % (Ft('n'), V))
    # the diagonal sum
    SGm = SG('m')
    PT = lambda m: '( %s x. ( %s ^ 2 ) )' % (PHS('S', m), SG(m))
    dg = w.s([sr, h2, h3, h4], 'bvdiag', '( ph -> %s = sum_ m e. ( 1 ... N ) %s )' % (DSUM(), PT('m')))
    K2 = '( K ^ 2 )'
    RT = lambda m: '( %s x. %s )' % (WTERM(m), K2)
    AM = '( ph /\\ m e. ( 1 ... N ) )'; sm = mkst(w, AM)
    mel = sm([], 'simpr', 'm e. ( 1 ... N )'); mnn = sy(w, AM, mel, 'elfznn', 'm e. NN')
    mrp = sm([mnn], 'nnrpd', 'm e. RR+')
    phr = phsre(w, AM, mnn, lift(w, sr, AM), 'm')
    s0 = linarith(w, AM, [lift(w, s1le, AM)], '0 <_ S', leaves={'S': lift(w, sr, AM)})
    ph0 = sm([bind(w, AM, bind(w, AM, lift(w, sr, AM), s0, 'S e. RR', '0 <_ S'), mnn, '( S e. RR /\\ 0 <_ S )', 'm e. NN'), w.inst('bvphisg0')], 'syl',
             '0 <_ %s' % PHS('S', 'm'))
    # SG(m) real
    AMD = '( %s /\\ d e. ( 1 ... N ) )' % AM; smd = mkst(w, AMD)
    dnn = sy(w, AMD, smd([], 'simpr', 'd e. ( 1 ... N )'), 'elfznn', 'd e. NN')
    phmd = lift(w, w.s([], 'id', '( ph -> ph )'), AMD)
    ldr = hyp2(w, AMD, phmd, smd([], 'simpr', 'd e. ( 1 ... N )'), h3, '( L ` d ) e. RR')
    dsr = smd([smd([smd([dnn], 'nnrpd', 'd e. RR+'), lift(w, nsr, AMD)], 'rpcxpcld', '( d ^c -u S ) e. RR+')], 'rpred', '( d ^c -u S ) e. RR')
    TD = '( ( L ` d ) x. ( d ^c -u S ) )'
    IFD = 'if ( m || d , %s , 0 )' % TD
    ifdr = smd([smd([ldr, dsr], 'remulcld', '%s e. RR' % TD), smd([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFD)
    sgr = sm([sm([], 'fzfid', '( 1 ... N ) e. Fin'), ifdr], 'fsumrecl', '%s e. RR' % SGm)
    ptr = sm([phr, sm([sgr], 'resqcld', '( %s ^ 2 ) e. RR' % SGm)], 'remulcld', '%s e. RR' % PT('m'))
    cm = '( m ^c -u S )'; m2 = '( m ^c ( -u 2 x. S ) )'; RATm = '( m / ( phi ` m ) )'; R2 = '( %s ^ 2 )' % RATm
    cmr = sm([sm([mrp, lift(w, nsr, AM)], 'rpcxpcld', '%s e. RR+' % cm)], 'rpred', '%s e. RR' % cm)
    m2r = sm([sm([mrp, sm([lin_neg2(w, AM), lift(w, sr, AM)], 'remulcld', '( -u 2 x. S ) e. RR')],
                  'rpcxpcld', '%s e. RR+' % m2)], 'rpred', '%s e. RR' % m2)
    phinn = sy(w, AM, mnn, 'phicl', '( phi ` m ) e. NN')
    ratr = sm([sm([mnn], 'nnred', 'm e. RR'), sm([phinn], 'nnred', '( phi ` m ) e. RR'), sm([sm([phinn], 'nnrpd', '( phi ` m ) e. RR+')], 'rpne0d', '( phi ` m ) =/= 0')],
              'redivcld', '%s e. RR' % RATm)
    r2r = sm([ratr], 'resqcld', '%s e. RR' % R2)
    kr = lift(w, h5, AM); k2r = sm([kr], 'resqcld', '%s e. RR' % K2)
    WV = '( ( %s x. %s ) x. %s )' % (PHS('S', 'm'), m2, R2)
    wvr = sm([sm([phr, m2r], 'remulcld', '( %s x. %s ) e. RR' % (PHS('S', 'm'), m2)), r2r], 'remulcld', '%s e. RR' % WV)
    wtr = sm([wvr, sm([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % WTERM('m'))
    rtr = sm([wtr, k2r], 'remulcld', '%s e. RR' % RT('m'))
    # case ( mmu ` m ) =/= 0
    A1 = '( %s /\\ ( mmu ` m ) =/= 0 )' % AM; s_1 = mkst(w, A1)
    mu1 = s_1([], 'simpr', '( mmu ` m ) =/= 0')
    X = '( ( %s x. %s ) x. K )' % (cm, RATm)
    hb = hyp2(w, A1, lift(w, w.s([], 'id', '( ph -> ph )'), A1), s_1([lift(w, mel, A1), mu1], 'jca', '( m e. ( 1 ... N ) /\\ ( mmu ` m ) =/= 0 )'), h6,
              '( abs ` %s ) <_ %s' % (SGm, X))
    sgr1 = lift(w, sgr, A1)
    xr = s_1([s_1([lift(w, cmr, A1), lift(w, ratr, A1)], 'remulcld', '( %s x. %s ) e. RR' % (cm, RATm)), lift(w, kr, A1)], 'remulcld', '%s e. RR' % X)
    asr = s_1([s_1([sgr1], 'recnd', '%s e. CC' % SGm)], 'abscld', '( abs ` %s ) e. RR' % SGm)
    l2 = s_1([bind(w, A1, asr, s_1([s_1([sgr1], 'recnd', '%s e. CC' % SGm)], 'absge0d', '0 <_ ( abs ` %s )' % SGm), '( abs ` %s ) e. RR' % SGm, '0 <_ ( abs ` %s )' % SGm),
              bind(w, A1, xr, hb, '%s e. RR' % X, '( abs ` %s ) <_ %s' % (SGm, X)), w.inst('le2sq2')], 'syl2anc', '( ( abs ` %s ) ^ 2 ) <_ ( %s ^ 2 )' % (SGm, X))
    sq1 = s_1([sy(w, A1, sgr1, 'absresq', '( ( abs ` %s ) ^ 2 ) = ( %s ^ 2 )' % (SGm, SGm)), l2], 'eqbrtrrd', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (SGm, X))
    i1 = s_1([s_1([sgr1], 'resqcld', '( %s ^ 2 ) e. RR' % SGm), s_1([xr], 'resqcld', '( %s ^ 2 ) e. RR' % X), lift(w, phr, A1), lift(w, ph0, A1), sq1], 'lemul2ad',
             '%s <_ ( %s x. ( %s ^ 2 ) )' % (PT('m'), PHS('S', 'm'), X))
    CR = '( %s x. %s )' % (cm, RATm)
    cmc = s_1([lift(w, cmr, A1)], 'recnd', '%s e. CC' % cm); ratc = s_1([lift(w, ratr, A1)], 'recnd', '%s e. CC' % RATm)
    e1 = s_1([s_1([cmc, ratc], 'mulcld', '%s e. CC' % CR), s_1([lift(w, kr, A1)], 'recnd', 'K e. CC')], 'sqmuld',
             '( %s ^ 2 ) = ( ( %s ^ 2 ) x. %s )' % (X, CR, K2))
    e2 = s_1([s_1([cmc, ratc], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. %s )' % (CR, cm, R2))], 'oveq1d',
             '( ( %s ^ 2 ) x. %s ) = ( ( ( %s ^ 2 ) x. %s ) x. %s )' % (CR, K2, cm, R2, K2))
    mcc = s_1([lift(w, mnn, A1)], 'nncnd', 'm e. CC')
    nsc = s_1([lift(w, nsr, A1)], 'recnd', '-u S e. CC')
    cx = s_1([mcc, nsc, s_1([clo(w, '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0'), w.inst('cxpmul2')], 'syl3anc', '( m ^c ( -u S x. 2 ) ) = ( %s ^ 2 )' % cm)
    ex = lineq(w, A1, '( -u 2 x. S )', '( -u S x. 2 )', leaves={'S': lift(w, sr, A1)})
    m2e = s_1([s_1([ex], 'oveq2d', '%s = ( m ^c ( -u S x. 2 ) )' % m2), cx], 'eqtrd', '%s = ( %s ^ 2 )' % (m2, cm))
    e3 = s_1([s_1([s_1([m2e], 'eqcomd', '( %s ^ 2 ) = %s' % (cm, m2))], 'oveq1d', '( ( %s ^ 2 ) x. %s ) = ( %s x. %s )' % (cm, R2, m2, R2))], 'oveq1d',
             '( ( ( %s ^ 2 ) x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (cm, R2, K2, m2, R2, K2))
    xe = eqtr(w, A1, [e1, e2, e3], None)
    p1 = s_1([xe], 'oveq2d', '( %s x. ( %s ^ 2 ) ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (PHS('S', 'm'), X, PHS('S', 'm'), m2, R2, K2))
    p2 = lineq(w, A1, '( %s x. ( ( %s x. %s ) x. %s ) )' % (PHS('S', 'm'), m2, R2, K2), '( %s x. %s )' % (WV, K2), products=True,
               leaves={PHS('S', 'm'): lift(w, phr, A1), m2: lift(w, m2r, A1), R2: lift(w, r2r, A1), K2: lift(w, k2r, A1)}, atoms=[PHS('S', 'm'), m2, R2, K2])
    wt1 = s_1([mu1], 'iftrued', '%s = %s' % (WTERM('m'), WV))
    p3 = s_1([s_1([wt1], 'oveq1d', '%s = ( %s x. %s )' % (RT('m'), WV, K2))], 'eqcomd', '( %s x. %s ) = %s' % (WV, K2, RT('m')))
    c1 = s_1([i1, eqtr(w, A1, [p1, p2, p3], None)], 'breqtrd', '%s <_ %s' % (PT('m'), RT('m')))
    # case ( mmu ` m ) = 0
    A2 = '( %s /\\ -. ( mmu ` m ) =/= 0 )' % AM; s_2 = mkst(w, A2)
    nm = s_2([], 'simpr', '-. ( mmu ` m ) =/= 0')
    A2D = '( %s /\\ d e. ( 1 ... N ) )' % A2; s2d = mkst(w, A2D)
    del_ = s2d([], 'simpr', 'd e. ( 1 ... N )')
    dnn2 = sy(w, A2D, del_, 'elfznn', 'd e. NN')
    A2DV = '( %s /\\ m || d )' % A2D; s2v = mkst(w, A2DV)
    sq_ = s2v([lift(w, dnn2, A2DV), lift(w, lift(w, mnn, A2), A2DV), s2v([], 'simpr', 'm || d'), w.inst('dvdssqf')], 'syl3anc',
              '( ( mmu ` d ) =/= 0 -> ( mmu ` m ) =/= 0 )')
    nd = s2v([lift(w, nm, A2DV), sq_], 'mtod', '-. ( mmu ` d ) =/= 0')
    md0 = s2v([nd, w.inst('nne')], 'sylib', '( mmu ` d ) = 0')
    l0im = hyp2(w, A2DV, lift(w, w.s([], 'id', '( ph -> ph )'), A2DV), lift(w, del_, A2DV), h4, '( ( mmu ` d ) = 0 -> ( L ` d ) = 0 )')
    l0 = s2v([md0, l0im], 'mpd', '( L ` d ) = 0')
    dsc = s2v([s2v([s2v([lift(w, dnn2, A2DV)], 'nnrpd', 'd e. RR+'), lift(w, lift(w, nsr, A2), A2DV)], 'rpcxpcld', '( d ^c -u S ) e. RR+')], 'rpcnd', '( d ^c -u S ) e. CC')
    t0 = eqtr(w, A2DV, [s2v([s2v([], 'simpr', 'm || d')], 'iftrued', '%s = %s' % (IFD, TD)), s2v([l0], 'oveq1d', '%s = ( 0 x. ( d ^c -u S ) )' % TD),
                        s2v([dsc], 'mul02d', '( 0 x. ( d ^c -u S ) ) = 0')], None)
    A2DN = '( %s /\\ -. m || d )' % A2D
    t1 = w.s([w.s([], 'simpr', '( %s -> -. m || d )' % A2DN)], 'iffalsed', '( %s -> %s = 0 )' % (A2DN, IFD))
    tz = w.s([t0, t1], 'pm2.61dan', '( %s -> %s = 0 )' % (A2D, IFD))
    sgz = s_2([s_2([tz], 'sumeq2dv', '%s = sum_ d e. ( 1 ... N ) 0' % SGm),
               s_2([s_2([s_2([], 'fzfid', '( 1 ... N ) e. Fin')], 'olcd', '( ( 1 ... N ) C_ ( ZZ>= ` 1 ) \\/ ( 1 ... N ) e. Fin )'), w.inst('sumz')], 'syl',
                   'sum_ d e. ( 1 ... N ) 0 = 0')], 'eqtrd', '%s = 0' % SGm)
    phc2 = s_2([lift(w, phr, A2)], 'recnd', '%s e. CC' % PHS('S', 'm'))
    lz = eqtr(w, A2, [s_2([s_2([sgz], 'oveq1d', '( %s ^ 2 ) = ( 0 ^ 2 )' % SGm)], 'oveq2d', '%s = ( %s x. ( 0 ^ 2 ) )' % (PT('m'), PHS('S', 'm'))),
                      s_2([s_2([clo(w, 'sq0', '( 0 ^ 2 ) = 0')], 'a1i', '( 0 ^ 2 ) = 0')], 'oveq2d', '( %s x. ( 0 ^ 2 ) ) = ( %s x. 0 )' % (PHS('S', 'm'), PHS('S', 'm'))),
                      s_2([phc2], 'mul01d', '( %s x. 0 ) = 0' % PHS('S', 'm'))], None)
    rz = eqtr(w, A2, [s_2([s_2([nm], 'iffalsed', '%s = 0' % WTERM('m'))], 'oveq1d', '%s = ( 0 x. %s )' % (RT('m'), K2)),
                      s_2([s_2([lift(w, k2r, A2)], 'recnd', '%s e. CC' % K2)], 'mul02d', '( 0 x. %s ) = 0' % K2)], None)
    c2 = s_2([s_2([lz, rz], 'eqtr4d', '%s = %s' % (PT('m'), RT('m')))], 'eqled', '%s <_ %s' % (PT('m'), RT('m')))
    pt = w.s([c1, c2], 'pm2.61dan', '( %s -> %s <_ %s )' % (AM, PT('m'), RT('m')))
    fin = st([], 'fzfid', '( 1 ... N ) e. Fin')
    fle = st([fin, ptr, rtr, pt], 'fsumle', 'sum_ m e. ( 1 ... N ) %s <_ sum_ m e. ( 1 ... N ) %s' % (PT('m'), RT('m')))
    SW = 'sum_ m e. ( 1 ... N ) %s' % WTERM('m'); SWn = 'sum_ n e. ( 1 ... N ) %s' % WTERM('n')
    k2c = st([st([h5], 'resqcld', '%s e. RR' % K2)], 'recnd', '%s e. CC' % K2)
    fm = st([fin, k2c, sm([wtr], 'recnd', '%s e. CC' % WTERM('m'))], 'fsummulc1', '( %s x. %s ) = sum_ m e. ( 1 ... N ) %s' % (SW, K2, RT('m')))
    idmn = w.s([], 'id', '( m = n -> m = n )')
    cgw, nw = w.congr(WTERM('m'), {'m': 'n'}, 'm = n', {'m': idmn})
    assert nw == WTERM('n'), nw
    cbw = st([w.s([cgw], 'cbvsumv', '%s = %s' % (SW, SWn))], 'a1i', '%s = %s' % (SW, SWn))
    L8 = '( 8 x. ( 1 + ( log ` N ) ) )'
    wb = st([bind(w, PH, bind(w, PH, sr, s1le, 'S e. RR', '1 <_ S'), h2, '( S e. RR /\\ 1 <_ S )', 'N e. NN'), w.inst('bvwbnd')], 'syl', '%s <_ %s' % (SWn, L8))
    swr = st([fin, wtr], 'fsumrecl', '%s e. RR' % SW)
    l8r = st([st([clo(w, '8re', '8 e. RR')], 'a1i', '8 e. RR'),
              st([st([], '1red', '1 e. RR'), st([st([h2], 'nnrpd', 'N e. RR+')], 'relogcld', '( log ` N ) e. RR')], 'readdcld', '( 1 + ( log ` N ) ) e. RR')],
             'remulcld', '%s e. RR' % L8)
    wb2 = st([cbw, wb], 'eqbrtrd', '%s <_ %s' % (SW, L8))
    k2r0 = st([h5], 'resqcld', '%s e. RR' % K2)
    wb3 = st([swr, l8r, k2r0, st([h5], 'sqge0d', '0 <_ %s' % K2), wb2], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (SW, K2, L8, K2))
    dle = st([st([dg, fle], 'eqbrtrd', '%s <_ sum_ m e. ( 1 ... N ) %s' % (DSUM(), RT('m'))), st([fm], 'eqcomd', 'sum_ m e. ( 1 ... N ) %s = ( %s x. %s )' % (RT('m'), SW, K2))],
             'breqtrd', '%s <_ ( %s x. %s )' % (DSUM(), SW, K2))
    dsr = st([dg, st([fin, ptr], 'fsumrecl', 'sum_ m e. ( 1 ... N ) %s e. RR' % PT('m'))], 'eqeltrd', '%s e. RR' % DSUM())
    dle2 = st([dsr, st([swr, k2r0], 'remulcld', '( %s x. %s ) e. RR' % (SW, K2)), st([l8r, k2r0], 'remulcld', '( %s x. %s ) e. RR' % (L8, K2)), dle, wb3], 'letrd',
              '%s <_ ( %s x. %s )' % (DSUM(), L8, K2))
    dle3 = st([dle2, st([st([l8r], 'recnd', '%s e. CC' % L8), k2c], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (L8, K2, K2, L8))], 'breqtrd',
              '%s <_ ( %s x. %s )' % (DSUM(), K2, L8))
    # zeta ( S ) >= 0
    ZT = '( t e. NN |-> ( t ^c -u S ) )'
    AK = '( ph /\\ n e. NN )'; sk = mkst(w, AK)
    zv, _ = mpv(w, AK, 't', 'NN', '( t ^c -u S )', 'n', sk([], 'simpr', 'n e. NN'))
    nsrp = sk([sk([sk([], 'simpr', 'n e. NN')], 'nnrpd', 'n e. RR+'), lift(w, nsr, AK)], 'rpcxpcld', '( n ^c -u S ) e. RR+')
    z0 = st([z, st([], '1zzd', '1 e. ZZ'), zv, sk([nsrp], 'rpred', '( n ^c -u S ) e. RR'), st([h1, w.inst('zetacvg1')], 'syl', '%s e. dom ~~>' % SEQ(ZT)),
             sk([nsrp], 'rpge0d', '0 <_ ( n ^c -u S )')], 'isumge0', '0 <_ %s' % ZS())
    zr = st([h1, w.inst('zetasumcl')], 'syl', '%s e. RR' % ZS())
    rhsr = st([k2r0, l8r], 'remulcld', '( %s x. %s ) e. RR' % (K2, L8))
    fin_ = st([dsr, rhsr, zr, z0, dle3], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (ZS(), DSUM(), ZS(), K2, L8))
    tle = st([val, fin_], 'eqbrtrd', 'sum_ n e. NN %s <_ ( %s x. ( %s x. %s ) )' % (Ft('n'), ZS(), K2, L8))
    w.qed([cvg, tle], 'jca', STATEMENTS['bvdiagle'])
    return w


def lin_neg2(w, ante):
    """( ante -> -u 2 e. RR )"""
    return w.s([w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR')], 'a1i', '( %s -> -u 2 e. RR )' % ante)



from zbv2_ssum import habfacts, lvfacts, plfacts


def lzero(w, ante, h1, hf, dnn, dgt, d):
    """( ante -> ( L ` d ) = 0 ) from dgt: ( ante -> B < d ), d e. NN (the weight vanishes beyond z2)"""
    st = mkst(w, ante)
    lv = lvfacts(w, ante, h1, hf, dnn, d)
    drp = st([dnn], 'nnrpd', '%s e. RR+' % d); dre = st([drp], 'rpred', '%s e. RR' % d)
    def pl0(X, xlt):
        xd = '( %s / %s )' % (X, d)
        xr = st([hf['ar' if X == 'A' else 'br'], drp], 'rerpdivcld', '%s e. RR' % xd)
        q1 = st([xlt, sy2(w, ante, hf['ar' if X == 'A' else 'br'], drp, 'divlt1lt', '( %s < 1 <-> %s < %s )' % (xd, X, d))], 'mpbird', '%s < 1' % xd)
        n1 = st([q1, st([st([], '1red', '1 e. RR'), xr], 'ltnled', '( %s < 1 <-> -. 1 <_ %s )' % (xd, xd))], 'mpbid', '-. 1 <_ %s' % xd)
        return st([n1], 'iffalsed', '%s = 0' % PL(xd))
    alt = st([hf['ar'], hf['br'], dre, hf['ab'], dgt], 'lttrd', 'A < %s' % d)
    pb = pl0('B', dgt); pa = pl0('A', alt)
    PB = PL('( B / %s )' % d); PA = PL('( A / %s )' % d)
    mf = mqfacts(w, ante, dnn, d)
    z = eqtr(w, ante, [st([pb, pa], 'oveq12d', '( %s - %s ) = ( 0 - 0 )' % (PB, PA)), st([clo(w, '0m0e0', '( 0 - 0 ) = 0')], 'a1i', '( 0 - 0 ) = 0')], None)
    n0 = eqtr(w, ante, [st([z], 'oveq2d', '( ( mmu ` %s ) x. ( %s - %s ) ) = ( ( mmu ` %s ) x. 0 )' % (d, PB, PA, d)), st([mf['muc']], 'mul01d', '( ( mmu ` %s ) x. 0 ) = 0' % d)], None)
    b0 = eqtr(w, ante, [st([n0], 'oveq1d', '%s = ( 0 / %s )' % (BVL(d), LGAB)), st([hf['gcc'], hf['gne']], 'div0d', '( 0 / %s ) = 0' % LGAB)], None)
    return st([lv['val'], b0], 'eqtrd', '( L ` %s ) = 0' % d)


def notin_gt(w, ante, dnn, nin, NBr, NBz, N):
    """( ante -> N < d ) from dnn: d e. NN, nin: -. d e. ( 1 ... N ) (N an integer with real/ZZ steps)"""
    st = mkst(w, ante)
    dz = st([dnn], 'nnzd', 'd e. ZZ'); dre = st([dnn], 'nnred', 'd e. RR')
    A3 = '( %s /\\ d <_ %s )' % (ante, N); s3 = mkst(w, A3)
    inr = s3([s3([], '1zzd', '1 e. ZZ'), lift(w, NBz, A3), lift(w, dz, A3), s3([lift(w, dnn, A3)], 'nnge1d', '1 <_ d'), s3([], 'simpr', 'd <_ %s' % N)], 'elfzd', 'd e. ( 1 ... %s )' % N)
    nle = st([nin, inr], 'mtand', '-. d <_ %s' % N)
    return st([nle, st([NBr, dre], 'ltnled', '( %s < d <-> -. d <_ %s )' % (N, N))], 'mpbird', '%s < d' % N)


def bvaicc():
    w = W('bvaicc', 'The divisor sum of the Barban-Vehov weight over ( 1 ... |_ B ) with the indicator d || K: the weights '
                    'beyond z2 vanish (Lean bvA_eq_sum_Icc).')
    h1, = hyps_of(w, 'bvaicc')
    A = '( %s /\\ K e. NN )' % HAB
    st = mkst(w, A)
    hf = habfacts(w, A, st([], 'simpl', HAB)); knn = st([], 'simpr', 'K e. NN')
    DVK = '{ x e. NN | x || K }'; R = '( 1 ... %s )' % NB; I = '( %s i^i %s )' % (DVK, R)
    nbz = sy(w, A, hf['br'], 'flcl', '%s e. ZZ' % NB); nbr = st([nbz], 'zred', '%s e. RR' % NB)
    elr = w.s([w.s([], 'breq1', '( x = d -> ( x || K <-> d || K ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || K ) )' % DVK)
    IFK = 'if ( d || K , ( L ` d ) , 0 )'
    # on I
    AI = '( %s /\\ d e. %s )' % (A, I); si = mkst(w, AI)
    di = si([si([], 'simpr', 'd e. %s' % I), w.inst('elin')], 'sylib', '( d e. %s /\\ d e. %s )' % (DVK, R))
    dd = si([si([di], 'simpld', 'd e. %s' % DVK), elr], 'sylib', '( d e. NN /\\ d || K )')
    dnni = si([dd], 'simpld', 'd e. NN')
    hfi = {k: lift(w, v, AI) for k, v in hf.items()}
    lvi = lvfacts(w, AI, h1, hfi, dnni, 'd')
    lci = si([lvi['lre']], 'recnd', '( L ` d ) e. CC')
    iti = si([si([dd], 'simprd', 'd || K')], 'iftrued', '%s = ( L ` d )' % IFK)
    ifci = si([iti, lci], 'eqeltrd', '%s e. CC' % IFK)
    # DV(K) \ I : L d = 0
    AD = '( %s /\\ d e. ( %s \\ %s ) )' % (A, DVK, I); sd = mkst(w, AD)
    dif = sd([], 'simpr', 'd e. ( %s \\ %s )' % (DVK, I))
    ddv = sy(w, AD, dif, 'eldifi', 'd e. %s' % DVK); dni = sy(w, AD, dif, 'eldifn', '-. d e. %s' % I)
    dnnd = sd([sd([ddv, elr], 'sylib', '( d e. NN /\\ d || K )')], 'simpld', 'd e. NN')
    AD3 = '( %s /\\ d e. %s )' % (AD, R); s3 = mkst(w, AD3)
    ini = s3([s3([lift(w, ddv, AD3), s3([], 'simpr', 'd e. %s' % R)], 'jca', '( d e. %s /\\ d e. %s )' % (DVK, R)), w.inst('elin')], 'sylibr', 'd e. %s' % I)
    ndr = sd([dni, ini], 'mtand', '-. d e. %s' % R)
    nbd = notin_gt(w, AD, dnnd, ndr, lift(w, nbr, AD), lift(w, nbz, AD), NB)
    bd = sd([nbd, sy2(w, AD, lift(w, hf['br'], AD), sd([dnnd], 'nnzd', 'd e. ZZ'), 'fllt', '( B < d <-> %s < d )' % NB)], 'mpbird', 'B < d')
    hfd = {k: lift(w, v, AD) for k, v in hf.items()}
    lz = lzero(w, AD, h1, hfd, dnnd, bd, 'd')
    s_a = st([st([clo(w, 'inss1', '%s C_ %s' % (I, DVK))], 'a1i', '%s C_ %s' % (I, DVK)), lci, lz, sy(w, A, knn, 'dvdsfi', '%s e. Fin' % DVK)], 'fsumss',
             'sum_ d e. %s ( L ` d ) = sum_ d e. %s ( L ` d )' % (I, DVK))
    s_b = st([iti], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s ( L ` d )' % (I, IFK, I))
    # R \ I : the indicator vanishes
    AR = '( %s /\\ d e. ( %s \\ %s ) )' % (A, R, I); sr_ = mkst(w, AR)
    difr = sr_([], 'simpr', 'd e. ( %s \\ %s )' % (R, I))
    drr = sy(w, AR, difr, 'eldifi', 'd e. %s' % R); dnir = sy(w, AR, difr, 'eldifn', '-. d e. %s' % I)
    dnnr = sy(w, AR, drr, 'elfznn', 'd e. NN')
    AR3 = '( %s /\\ d || K )' % AR; sr3 = mkst(w, AR3)
    indv = sr3([sr3([lift(w, dnnr, AR3), sr3([], 'simpr', 'd || K')], 'jca', '( d e. NN /\\ d || K )'), elr], 'sylibr', 'd e. %s' % DVK)
    ini2 = sr3([sr3([indv, lift(w, drr, AR3)], 'jca', '( d e. %s /\\ d e. %s )' % (DVK, R)), w.inst('elin')], 'sylibr', 'd e. %s' % I)
    ndk = sr_([dnir, ini2], 'mtand', '-. d || K')
    zr = sr_([ndk], 'iffalsed', '%s = 0' % IFK)
    s_c = st([st([clo(w, 'inss2', '%s C_ %s' % (I, R))], 'a1i', '%s C_ %s' % (I, R)), ifci, zr, st([], 'fzfid', '%s e. Fin' % R)], 'fsumss',
             'sum_ d e. %s %s = sum_ d e. %s %s' % (I, IFK, R, IFK))
    w.qed([eqtr(w, A, [st([s_a], 'eqcomd', 'sum_ d e. %s ( L ` d ) = sum_ d e. %s ( L ` d )' % (DVK, I)),
                       st([s_b], 'eqcomd', 'sum_ d e. %s ( L ` d ) = sum_ d e. %s %s' % (I, I, IFK)), s_c], None), w.inst('id')], 'syl', STATEMENTS['bvaicc'])
    return w


def bvtsumle():
    w = W('bvtsumle', 'The assembled diagonal bound for the Barban-Vehov weight (Lean tsum_rpow_bvA_sq_le): bvdiagle '
                      'with K = ( 22 / 3 ) ( 1 + ( S - 1 ) log z2 ) / log ( z2 / z1 ) from bvssumle.')
    h1, = hyps_of(w, 'bvtsumle')
    HS1_ = '( S e. RR /\\ 1 < S )'
    A = '( %s /\\ %s )' % (HAB, HS1_)
    st = mkst(w, A)
    hab = st([], 'simpl', HAB); hs = st([], 'simpr', HS1_)
    hf = habfacts(w, A, hab)
    sr = st([hs], 'simpld', 'S e. RR'); s1 = st([st([hs], 'simprd', '1 < S')], 'ltled', '1 <_ S')
    nbn = st([hf['br'], hf['b1'], w.inst('flge1nn')], 'syl2anc', '%s e. NN' % NB)
    AD = '( %s /\\ d e. ( 1 ... %s ) )' % (A, NB); sd = mkst(w, AD)
    dnn = sy(w, AD, sd([], 'simpr', 'd e. ( 1 ... %s )' % NB), 'elfznn', 'd e. NN')
    hfd = {k: lift(w, v, AD) for k, v in hf.items()}
    lv = lvfacts(w, AD, h1, hfd, dnn, 'd')
    AD0 = '( %s /\\ ( mmu ` d ) = 0 )' % AD; s0 = mkst(w, AD0)
    PB = PL('( B / d )'); PA = PL('( A / d )'); DP = '( %s - %s )' % (PB, PA)
    hf0 = {k: lift(w, v, AD0) for k, v in hf.items()}
    drp0 = s0([lift(w, dnn, AD0)], 'nnrpd', 'd e. RR+')
    dpc = s0([s0([plfacts(w, AD0, s0([hf0['brp'], drp0], 'rpdivcld', '( B / d ) e. RR+'), '( B / d )'),
                  plfacts(w, AD0, s0([hf0['arp'], drp0], 'rpdivcld', '( A / d ) e. RR+'), '( A / d )')], 'resubcld', '%s e. RR' % DP)], 'recnd', '%s e. CC' % DP)
    z = eqtr(w, AD0, [lift(w, lv['val'], AD0), s0([s0([s0([], 'simpr', '( mmu ` d ) = 0')], 'oveq1d', '( ( mmu ` d ) x. %s ) = ( 0 x. %s )' % (DP, DP))], 'oveq1d',
                                                 '%s = ( ( 0 x. %s ) / %s )' % (BVL('d'), DP, LGAB)),
                      s0([s0([dpc], 'mul02d', '( 0 x. %s ) = 0' % DP)], 'oveq1d', '( ( 0 x. %s ) / %s ) = ( 0 / %s )' % (DP, LGAB, LGAB)),
                      s0([hf0['gcc'], hf0['gne']], 'div0d', '( 0 / %s ) = 0' % LGAB)], None)
    h4 = w.s([z], 'ex', '( %s -> ( ( mmu ` d ) = 0 -> ( L ` d ) = 0 ) )' % AD)
    WB = '( 1 + ( ( S - 1 ) x. ( log ` B ) ) )'
    wr = st([st([], '1red', '1 e. RR'), st([st([sr, st([], '1red', '1 e. RR')], 'resubcld', '( S - 1 ) e. RR'), st([hf['brp']], 'relogcld', '( log ` B ) e. RR')],
                                            'remulcld', '( ( S - 1 ) x. ( log ` B ) ) e. RR')], 'readdcld', '%s e. RR' % WB)
    kbr = st([st([st([num.real(w, '( ; 2 2 / 3 )')], 'a1i', '( ; 2 2 / 3 ) e. RR'), wr], 'remulcld', '( ( ; 2 2 / 3 ) x. %s ) e. RR' % WB), hf['gre'], hf['gne']],
             'redivcld', '%s e. RR' % KB)
    AM = '( %s /\\ ( m e. ( 1 ... %s ) /\\ ( mmu ` m ) =/= 0 ) )' % (A, NB); sm = mkst(w, AM)
    ssl = w.s([h1], 'bvssumle', '( ( ( %s /\\ ( S e. RR /\\ 1 <_ S ) ) /\\ ( m e. ( 1 ... %s ) /\\ ( mmu ` m ) =/= 0 ) ) -> ( abs ` %s ) <_ ( ( ( m ^c -u S ) x. ( m / ( phi ` m ) ) ) x. %s ) )'
              % (HAB, NB, SGB('m'), KB))
    h6 = sm([bind(w, AM, bind(w, AM, lift(w, hab, AM), bind(w, AM, lift(w, sr, AM), lift(w, s1, AM), 'S e. RR', '1 <_ S'), HAB, '( S e. RR /\\ 1 <_ S )'),
                  sm([], 'simpr', '( m e. ( 1 ... %s ) /\\ ( mmu ` m ) =/= 0 )' % NB), '( %s /\\ ( S e. RR /\\ 1 <_ S ) )' % HAB, '( m e. ( 1 ... %s ) /\\ ( mmu ` m ) =/= 0 )' % NB), ssl],
            'syl', '( abs ` %s ) <_ ( ( ( m ^c -u S ) x. ( m / ( phi ` m ) ) ) x. %s )' % (SGB('m'), KB))
    w.qed([hs, nbn, lv['lre'], h4, kbr, h6], 'bvdiagle', STATEMENTS['bvtsumle'])
    return w



def ninv(w, ante, nrp, n='n'):
    """( ante -> ( n ^c -u 1 ) = ( 1 / n ) ) from n e. RR+"""
    st = mkst(w, ante)
    ncc = st([nrp], 'rpcnd', '%s e. CC' % n); nne = st([nrp], 'rpne0d', '%s =/= 0' % n)
    a = st([ncc, nne, st([], '1cnd', '1 e. CC'), w.inst('cxpneg')], 'syl3anc', '( %s ^c -u 1 ) = ( 1 / ( %s ^c 1 ) )' % (n, n))
    b = st([st([ncc], 'cxp1d', '( %s ^c 1 ) = %s' % (n, n))], 'oveq2d', '( 1 / ( %s ^c 1 ) ) = ( 1 / %s )' % (n, n))
    return st([a, b], 'eqtrd', '( %s ^c -u 1 ) = ( 1 / %s )' % (n, n))


def bvrankin():
    w = W('bvrankin', 'The Rankin step at S = 1 + 1 / log Y (Lean sum_bvA_sq_div_le_tsum, for any real summand C): '
                      'n <= Y gives 1 / n <= e n ^c -u S, since n ^c ( 1 / log Y ) <= Y ^c ( 1 / log Y ) = e (isumless).')
    h1, h2, h3, h4 = hyps_of(w, 'bvrankin')
    st = mkst(w, PH)
    yr = st([h1], 'simpld', 'Y e. RR'); y1 = st([h1], 'simprd', '1 < Y')
    yrp = st([yr, linarith(w, PH, [y1], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+')
    lyrp = st([yr, y1, w.inst('rplogcl')], 'syl2anc', '( log ` Y ) e. RR+')
    U = '( 1 / ( log ` Y ) )'
    urp = st([lyrp], 'rpreccld', '%s e. RR+' % U); ur = st([urp], 'rpred', '%s e. RR' % U)
    srr = st([st([], '1red', '1 e. RR'), ur], 'readdcld', '%s e. RR' % SR)
    nsr = st([srr], 'renegcld', '-u %s e. RR' % SR)
    E1 = '( exp ` 1 )'
    e1 = st([st([], '1red', '1 e. RR')], 'reefcld', '%s e. RR' % E1)
    yu = eqtr(w, PH, [st([st([yr], 'recnd', 'Y e. CC'), st([yrp], 'rpne0d', 'Y =/= 0'), st([ur], 'recnd', '%s e. CC' % U)], 'cxpefd',
                          '( Y ^c %s ) = ( exp ` ( %s x. ( log ` Y ) ) )' % (U, U)),
                      st([st([st([], '1cnd', '1 e. CC'), st([lyrp], 'rpcnd', '( log ` Y ) e. CC'), st([lyrp], 'rpne0d', '( log ` Y ) =/= 0')], 'divcan1d',
                             '( %s x. ( log ` Y ) ) = 1' % U)], 'fveq2d', '( exp ` ( %s x. ( log ` Y ) ) ) = %s' % (U, E1))], None)
    R = '( 1 ... ( |_ ` Y ) )'
    AN = '( ph /\\ n e. %s )' % R; sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % R); nnn = sy(w, AN, nel, 'elfznn', 'n e. NN')
    nrp = sn([nnn], 'nnrpd', 'n e. RR+'); nre = sn([nrp], 'rpred', 'n e. RR')
    cr = hyp2(w, AN, lift(w, w.s([], 'id', '( ph -> ph )'), AN), nnn, h2, 'C e. RR')
    c2r = sn([cr], 'resqcld', '( C ^ 2 ) e. RR'); c20 = sn([cr], 'sqge0d', '0 <_ ( C ^ 2 )')
    NS = '( n ^c -u %s )' % SR; NU = '( n ^c %s )' % U
    nsp = sn([nrp, lift(w, nsr, AN)], 'rpcxpcld', '%s e. RR+' % NS); nsre = sn([nsp], 'rpred', '%s e. RR' % NS)
    ex = lineq(w, AN, '( %s + -u %s )' % (U, SR), '-u 1', leaves={U: lift(w, ur, AN)})
    ncc = sn([nrp], 'rpcnd', 'n e. CC'); nne = sn([nrp], 'rpne0d', 'n =/= 0')
    k1 = eqtr(w, AN, [sn([ncc, nne, sn([lift(w, ur, AN)], 'recnd', '%s e. CC' % U), sn([lift(w, nsr, AN)], 'recnd', '-u %s e. CC' % SR)], 'cxpaddd',
                          '( n ^c ( %s + -u %s ) ) = ( %s x. %s )' % (U, SR, NU, NS))], None)
    k2 = sn([sn([ex], 'oveq2d', '( n ^c ( %s + -u %s ) ) = ( n ^c -u 1 )' % (U, SR)), ninv(w, AN, nrp)], 'eqtrd', '( n ^c ( %s + -u %s ) ) = ( 1 / n )' % (U, SR))
    inv = sn([k2, k1], 'eqtr3d', '( 1 / n ) = ( %s x. %s )' % (NU, NS))
    nfl = sy(w, AN, nel, 'elfzle2', 'n <_ ( |_ ` Y )')
    ny = sn([nre, sy(w, AN, lift(w, yr, AN), 'reflcl', '( |_ ` Y ) e. RR'), lift(w, yr, AN), nfl, sy(w, AN, lift(w, yr, AN), 'flle', '( |_ ` Y ) <_ Y')], 'letrd', 'n <_ Y')
    cle = sn([nre, lift(w, yr, AN), lift(w, ur, AN), sn([nrp], 'rpge0d', '0 <_ n'), lift(w, st([urp], 'rpge0d', '0 <_ %s' % U), AN), ny], 'cxple2ad',
             '%s <_ ( Y ^c %s )' % (NU, U))
    nur = sn([sn([nrp, lift(w, ur, AN)], 'rpcxpcld', '%s e. RR+' % NU)], 'rpred', '%s e. RR' % NU)
    yur = sn([sn([lift(w, yrp, AN), lift(w, ur, AN)], 'rpcxpcld', '( Y ^c %s ) e. RR+' % U)], 'rpred', '( Y ^c %s ) e. RR' % U)
    l1 = sn([nur, yur, nsre, sn([nsp], 'rpge0d', '0 <_ %s' % NS), cle], 'lemul1ad', '( %s x. %s ) <_ ( ( Y ^c %s ) x. %s )' % (NU, NS, U, NS))
    l2 = sn([sn([inv, l1], 'eqbrtrd', '( 1 / n ) <_ ( ( Y ^c %s ) x. %s )' % (U, NS)), sn([lift(w, yu, AN)], 'oveq1d', '( ( Y ^c %s ) x. %s ) = ( %s x. %s )' % (U, NS, E1, NS))],
            'breqtrd', '( 1 / n ) <_ ( %s x. %s )' % (E1, NS))
    invr = sn([nrp], 'rpreccld', '( 1 / n ) e. RR+')
    ens = sn([lift(w, e1, AN), nsre], 'remulcld', '( %s x. %s ) e. RR' % (E1, NS))
    l3 = sn([sn([invr], 'rpred', '( 1 / n ) e. RR'), ens, c2r, c20, l2], 'lemul1ad', '( ( 1 / n ) x. ( C ^ 2 ) ) <_ ( ( %s x. %s ) x. ( C ^ 2 ) )' % (E1, NS))
    dv = sn([sn([c2r], 'recnd', '( C ^ 2 ) e. CC'), ncc, nne], 'divrec2d', '( ( C ^ 2 ) / n ) = ( ( 1 / n ) x. ( C ^ 2 ) )')
    ma = sn([sn([lift(w, e1, AN)], 'recnd', '%s e. CC' % E1), sn([nsre], 'recnd', '%s e. CC' % NS), sn([c2r], 'recnd', '( C ^ 2 ) e. CC')], 'mulassd',
            '( ( %s x. %s ) x. ( C ^ 2 ) ) = ( %s x. ( %s x. ( C ^ 2 ) ) )' % (E1, NS, E1, NS))
    TN = '( %s x. ( C ^ 2 ) )' % NS
    pt = sn([sn([dv, l3], 'eqbrtrd', '( ( C ^ 2 ) / n ) <_ ( ( %s x. %s ) x. ( C ^ 2 ) )' % (E1, NS)), ma], 'breqtrd', '( ( C ^ 2 ) / n ) <_ ( %s x. %s )' % (E1, TN))
    fin = st([], 'fzfid', '%s e. Fin' % R)
    qr = sn([c2r, nrp], 'rerpdivcld', '( ( C ^ 2 ) / n ) e. RR')
    tnr = sn([nsre, c2r], 'remulcld', '%s e. RR' % TN)
    s1 = st([fin, qr, sn([lift(w, e1, AN), tnr], 'remulcld', '( %s x. %s ) e. RR' % (E1, TN)), pt], 'fsumle',
            'sum_ n e. %s ( ( C ^ 2 ) / n ) <_ sum_ n e. %s ( %s x. %s )' % (R, R, E1, TN))
    s2 = st([fin, st([e1], 'recnd', '%s e. CC' % E1), sn([tnr], 'recnd', '%s e. CC' % TN)], 'fsummulc2',
            '( %s x. sum_ n e. %s %s ) = sum_ n e. %s ( %s x. %s )' % (E1, R, TN, R, E1, TN))
    # the finite sum below the series
    MT = '( t e. NN |-> ( ( t ^c -u %s ) x. ( D ^ 2 ) ) )' % SR
    AK = '( ph /\\ n e. NN )'; sk = mkst(w, AK)
    knn = sk([], 'simpr', 'n e. NN'); krp = sk([knn], 'nnrpd', 'n e. RR+')
    ckr = hyp2(w, AK, lift(w, w.s([], 'id', '( ph -> ph )'), AK), knn, h2, 'C e. RR')
    c1 = w.s([h4], 'eqcoms', '( t = n -> C = D )')
    c2 = w.s([c1], 'eqcomd', '( t = n -> D = C )')
    c3a = w.s([w.s([], 'id', '( t = n -> t = n )')], 'oveq1d', '( t = n -> ( t ^c -u %s ) = ( n ^c -u %s ) )' % (SR, SR))
    c3b = w.s([c2], 'oveq1d', '( t = n -> ( D ^ 2 ) = ( C ^ 2 ) )')
    c3 = w.s([c3a, c3b], 'oveq12d', '( t = n -> ( ( t ^c -u %s ) x. ( D ^ 2 ) ) = ( ( n ^c -u %s ) x. ( C ^ 2 ) ) )' % (SR, SR))
    c4 = w.s([c3], 'adantl', '( ( %s /\\ t = n ) -> ( ( t ^c -u %s ) x. ( D ^ 2 ) ) = %s )' % (AK, SR, TN))
    tkr = sk([sk([sk([krp, lift(w, nsr, AK)], 'rpcxpcld', '%s e. RR+' % NS)], 'rpred', '%s e. RR' % NS), sk([ckr], 'resqcld', '( C ^ 2 ) e. RR')], 'remulcld', '%s e. RR' % TN)
    fv = sk([sk([], 'eqidd', '%s = %s' % (MT, MT)), c4, knn, tkr], 'fvmptd', '( %s ` n ) = %s' % (MT, TN))
    nsp_k = sk([krp, lift(w, nsr, AK)], 'rpcxpcld', '%s e. RR+' % NS)
    tk0 = sk([sk([nsp_k], 'rpred', '%s e. RR' % NS), sk([ckr], 'resqcld', '( C ^ 2 ) e. RR'), sk([nsp_k], 'rpge0d', '0 <_ %s' % NS), sk([ckr], 'sqge0d', '0 <_ ( C ^ 2 )')],
             'mulge0d', '0 <_ %s' % TN)
    sub = st([clo(w, 'fz1ssnn', '%s C_ NN' % R)], 'a1i', '%s C_ NN' % R)
    les = st([clo(w, 'nnuz', NNUZ_), st([], '1zzd', '1 e. ZZ'), fin, sub, fv, tkr, tk0, h3], 'isumless', 'sum_ n e. %s %s <_ sum_ n e. NN %s' % (R, TN, TN))
    fr = st([fin, sn([nsre, c2r], 'remulcld', '%s e. RR' % TN)], 'fsumrecl', 'sum_ n e. %s %s e. RR' % (R, TN))
    isr = st([clo(w, 'nnuz', NNUZ_), st([], '1zzd', '1 e. ZZ'), fv, tkr, h3], 'isumrecl', 'sum_ n e. NN %s e. RR' % TN)
    l4 = st([fr, isr, e1, st([st([st([], '1red', '1 e. RR')], 'rpefcld', '%s e. RR+' % E1)], 'rpge0d', '0 <_ %s' % E1), les],
            'lemul2ad', '( %s x. sum_ n e. %s %s ) <_ ( %s x. sum_ n e. NN %s )' % (E1, R, TN, E1, TN))
    w.qed([st([s1, st([s2], 'eqcomd', 'sum_ n e. %s ( %s x. %s ) = ( %s x. sum_ n e. %s %s )' % (R, E1, TN, E1, R, TN))], 'breqtrd',
              'sum_ n e. %s ( ( C ^ 2 ) / n ) <_ ( %s x. sum_ n e. %s %s )' % (R, E1, R, TN)), l4], 'letrd', STATEMENTS['bvrankin'])
    return w


def bvrankina():
    w = W('bvrankina', 'The alpha step (Lean rankin_alpha): for n <= Y and T <= 1, n ^c ( 1 - 2 T ) = n ^c ( 2 - 2 T ) / n '
                       '<= Y ^c ( 2 - 2 T ) / n.')
    h1, h2, h3 = hyps_of(w, 'bvrankina')
    st = mkst(w, PH)
    yr = st([h1], 'simpld', 'Y e. RR'); y1 = st([h1], 'simprd', '1 <_ Y')
    yrp = st([yr, linarith(w, PH, [y1], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+')
    tr = st([h2], 'simpld', 'T e. RR'); t1 = st([h2], 'simprd', 'T <_ 1')
    B2 = '( 2 - ( 2 x. T ) )'; B1 = '( 1 - ( 2 x. T ) )'
    b2r = st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'),
              st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B2)
    b20 = linarith(w, PH, [t1], '0 <_ %s' % B2, leaves={'T': tr})
    YB = '( Y ^c %s )' % B2
    ybr = st([st([yrp, b2r], 'rpcxpcld', '%s e. RR+' % YB)], 'rpred', '%s e. RR' % YB)
    R = '( 1 ... ( |_ ` Y ) )'
    AN = '( ph /\\ n e. %s )' % R; sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % R); nnn = sy(w, AN, nel, 'elfznn', 'n e. NN')
    nrp = sn([nnn], 'nnrpd', 'n e. RR+'); nre = sn([nrp], 'rpred', 'n e. RR')
    cr = h3
    c2r = sn([cr], 'resqcld', '( C ^ 2 ) e. RR'); c20 = sn([cr], 'sqge0d', '0 <_ ( C ^ 2 )')
    ncc = sn([nrp], 'rpcnd', 'n e. CC'); nne = sn([nrp], 'rpne0d', 'n =/= 0')
    ex = lineq(w, AN, B1, '( %s + -u 1 )' % B2, leaves={'T': lift(w, tr, AN)})
    NB2 = '( n ^c %s )' % B2
    k1 = sn([ncc, nne, sn([lift(w, b2r, AN)], 'recnd', '%s e. CC' % B2), sn([sn([sn([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR')], 'recnd', '-u 1 e. CC')], 'cxpaddd',
            '( n ^c ( %s + -u 1 ) ) = ( %s x. ( n ^c -u 1 ) )' % (B2, NB2))
    k2 = eqtr(w, AN, [sn([ex], 'oveq2d', '( n ^c %s ) = ( n ^c ( %s + -u 1 ) )' % (B1, B2)), k1, sn([ninv(w, AN, nrp)], 'oveq2d', '( %s x. ( n ^c -u 1 ) ) = ( %s x. ( 1 / n ) )' % (NB2, NB2))], None)
    nfl = sy(w, AN, nel, 'elfzle2', 'n <_ ( |_ ` Y )')
    ny = sn([nre, sy(w, AN, lift(w, yr, AN), 'reflcl', '( |_ ` Y ) e. RR'), lift(w, yr, AN), nfl, sy(w, AN, lift(w, yr, AN), 'flle', '( |_ ` Y ) <_ Y')], 'letrd', 'n <_ Y')
    cle = sn([nre, lift(w, yr, AN), lift(w, b2r, AN), sn([nrp], 'rpge0d', '0 <_ n'), lift(w, b20, AN), ny], 'cxple2ad', '%s <_ %s' % (NB2, YB))
    nb2r = sn([sn([nrp, lift(w, b2r, AN)], 'rpcxpcld', '%s e. RR+' % NB2)], 'rpred', '%s e. RR' % NB2)
    invr = sn([nrp], 'rpreccld', '( 1 / n ) e. RR+')
    l1 = sn([nb2r, lift(w, ybr, AN), sn([invr], 'rpred', '( 1 / n ) e. RR'), sn([invr], 'rpge0d', '0 <_ ( 1 / n )'), cle], 'lemul1ad',
            '( %s x. ( 1 / n ) ) <_ ( %s x. ( 1 / n ) )' % (NB2, YB))
    l2 = sn([k2, l1], 'eqbrtrd', '( n ^c %s ) <_ ( %s x. ( 1 / n ) )' % (B1, YB))
    n1r = sn([sn([nrp, sn([sn([], '1red', '1 e. RR'), sn([lift(w, st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), AN), lift(w, tr, AN)], 'remulcld', '( 2 x. T ) e. RR')],
                          'resubcld', '%s e. RR' % B1)], 'rpcxpcld', '( n ^c %s ) e. RR+' % B1)], 'rpred', '( n ^c %s ) e. RR' % B1)
    ybn = sn([lift(w, ybr, AN), sn([invr], 'rpred', '( 1 / n ) e. RR')], 'remulcld', '( %s x. ( 1 / n ) ) e. RR' % YB)
    l3 = sn([n1r, ybn, c2r, c20, l2], 'lemul1ad', '( ( n ^c %s ) x. ( C ^ 2 ) ) <_ ( ( %s x. ( 1 / n ) ) x. ( C ^ 2 ) )' % (B1, YB))
    e3 = eqtr(w, AN, [sn([lift(w, st([ybr], 'recnd', '%s e. CC' % YB), AN), sn([invr], 'rpcnd', '( 1 / n ) e. CC'), sn([c2r], 'recnd', '( C ^ 2 ) e. CC')], 'mulassd',
                         '( ( %s x. ( 1 / n ) ) x. ( C ^ 2 ) ) = ( %s x. ( ( 1 / n ) x. ( C ^ 2 ) ) )' % (YB, YB)),
                      sn([sn([sn([sn([c2r], 'recnd', '( C ^ 2 ) e. CC'), ncc, nne], 'divrec2d', '( ( C ^ 2 ) / n ) = ( ( 1 / n ) x. ( C ^ 2 ) )')], 'eqcomd',
                             '( ( 1 / n ) x. ( C ^ 2 ) ) = ( ( C ^ 2 ) / n )')], 'oveq2d', '( %s x. ( ( 1 / n ) x. ( C ^ 2 ) ) ) = ( %s x. ( ( C ^ 2 ) / n ) )' % (YB, YB))], None)
    pt = sn([l3, e3], 'breqtrd', '( ( n ^c %s ) x. ( C ^ 2 ) ) <_ ( %s x. ( ( C ^ 2 ) / n ) )' % (B1, YB))
    fin = st([], 'fzfid', '%s e. Fin' % R)
    qr = sn([c2r, nrp], 'rerpdivcld', '( ( C ^ 2 ) / n ) e. RR')
    s1 = st([fin, sn([n1r, c2r], 'remulcld', '( ( n ^c %s ) x. ( C ^ 2 ) ) e. RR' % B1), sn([lift(w, ybr, AN), qr], 'remulcld', '( %s x. ( ( C ^ 2 ) / n ) ) e. RR' % YB), pt],
            'fsumle', 'sum_ n e. %s ( ( n ^c %s ) x. ( C ^ 2 ) ) <_ sum_ n e. %s ( %s x. ( ( C ^ 2 ) / n ) )' % (R, B1, R, YB))
    s2 = st([fin, st([ybr], 'recnd', '%s e. CC' % YB), sn([qr], 'recnd', '( ( C ^ 2 ) / n ) e. CC')], 'fsummulc2',
            '( %s x. sum_ n e. %s ( ( C ^ 2 ) / n ) ) = sum_ n e. %s ( %s x. ( ( C ^ 2 ) / n ) )' % (YB, R, R, YB))
    w.qed([s1, s2], 'breqtrrd', STATEMENTS['bvrankina'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvdiagle']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
