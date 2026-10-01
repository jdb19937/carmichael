"""ZL2 section E: the end theorem zl2cvxe (CVXH at ( N DChrLF X ), LConvexityCorollaries 97-330 and 1569-1686)
and its helpers: holomorphy combinators (zl2hres zl2hadd zl2hsub), the character on NN (zl2chb zl2chs zl2chm),
the Euler-factor Dirichlet polynomial (zl2cfblav zl2afv zl2afb zl2musub zl2cxv2 zl2cxc zl2dsp zl2dpf zl2muabs zl2sqfc
zl2dpb zl2dpv zl2dph), the product identity on the strip (zl2lfe1 zl2lfh zl2lfe), the edges (zl2ergt zl2elft zl2ecvx).
`MM_DB=sorties/zl2.mm python3 tools/gen/zl2_e.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import *
from lin import linarith, nlinarith
from zl2_g import inst_ral_t, cbv_yz
from zl2_p import inst_ral, strip_mem, holeq_, mpteq_
from zl1lib import mptv
import num

only = sys.argv[1:]
TOP = TOPC
MP = lambda x, X, E: '( %s e. %s |-> %s )' % (x, X, E)


def subst(text, m):
    """token-level substitution of class variables"""
    return ' '.join(m.get(t, t) for t in text.split())


def split_imp(text):
    """split '( A -> B )' at the top level"""
    toks = text.split(); assert toks[0] == '(' and toks[-1] == ')'
    d = 0
    for i, t in enumerate(toks[1:-1], 1):
        if t == '(': d += 1
        elif t == ')': d -= 1
        elif t == '->' and d == 0:
            return ' '.join(toks[1:i]), ' '.join(toks[i + 1:-1])
    raise ValueError(text[:80])


def holctx(w, A0, hl, Fn, Dm='D'):
    """from hl: ( A0 -> HOL(Fn, Dm) ): (fcn, ff, fmpt, dvm, dvf)"""
    dv = '( CC _D %s )' % Fn
    fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, Fn, Dm))
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (A0, Fn, Dm))
    fmpt = w.s([ff], 'feqmptd', '( %s -> %s = %s )' % (A0, Fn, MP('z', Dm, '( %s ` z )' % Fn)))
    dvm = w.s([hl, w.inst('holdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', Dm, '( %s ` z )' % Fn), MP('z', Dm, '( %s ` z )' % dv)))
    dvf = w.s([hl, w.inst('holf')], 'syl', '( %s -> %s : %s --> CC )' % (A0, dv, Dm))
    return fcn, ff, fmpt, dvm, dvf


def dvdom(w, A0, mp, x, X, rhs, dveq, cls):
    """( A0 -> X C_ dom ( CC _D mp ) ) from dveq: ( A0 -> ( CC _D mp ) = ( x e. X |-> rhs ) ) and cls: ( ( A0 /\\ x e. X ) -> rhs e. CC )"""
    eqm = w.s([], 'eqid', '%s = %s' % (MP(x, X, rhs), MP(x, X, rhs)))
    ffn = w.s([cls, eqm], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, MP(x, X, rhs), X))
    dm = w.s([ffn, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A0, MP(x, X, rhs), X))
    d1 = w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, mp, MP(x, X, rhs)))
    d2 = w.s([d1, dm], 'eqtrd', '( %s -> dom ( CC _D %s ) = %s )' % (A0, mp, X))
    return w.s([w.s([d2], 'eqcomd', '( %s -> %s = dom ( CC _D %s ) )' % (A0, X, mp))], 'eqimssd', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, X, mp))


def cnel(w, A0):
    return w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)


def holbin(label, op, cnlab, dvlab, cllab, desc):
    w = W(label, desc)
    A0 = '( %s /\\ %s )' % (HOL('F', 'D'), HOL('G', 'D'))
    A1 = '( %s /\\ z e. D )' % A0
    FZ = '( F ` z )'; GZ = '( G ` z )'; DFZ = '( ( CC _D F ) ` z )'; DGZ = '( ( CC _D G ) ` z )'
    MPM = MP('z', 'D', '( %s %s %s )' % (FZ, op, GZ))
    hf = D(w, A0, 'simpl', [], HOL('F', 'D')); hg = D(w, A0, 'simpr', [], HOL('G', 'D'))
    fcn, ff, fmpt, dvmF, dvfF = holctx(w, A0, hf, 'F')
    gcn, gf, gmpt, dvmG, dvfG = holctx(w, A0, hg, 'G')
    fmp = w.s([fmpt, fcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', FZ)))
    gmp = w.s([gmpt, gcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', GZ)))
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ocn = w.s([w.s([ej], cnlab, '%s e. ( ( %s tX %s ) Cn %s )' % (op, TOP, TOP, TOP))], 'a1i', '( %s -> %s e. ( ( %s tX %s ) Cn %s ) )' % (A0, op, TOP, TOP, TOP))
    cnc = w.s([ej, ocn, fmp, gmp], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MPM))
    ce = cnel(w, A0)
    zD = D(w, A1, 'simpr', [], 'z e. D')
    fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, FZ))
    gzc = w.s([w.s([gf], 'adantr', '( %s -> G : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, GZ))
    dfzc = w.s([w.s([dvfF], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DFZ))
    dgzc = w.s([w.s([dvfG], 'adantr', '( %s -> ( CC _D G ) : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DGZ))
    RHS = '( %s %s %s )' % (DFZ, op, DGZ)
    dvc = w.s([ce, fzc, dfzc, dvmF, gzc, dgzc, dvmG], dvlab, '( %s -> ( CC _D %s ) = %s )' % (A0, MPM, MP('z', 'D', RHS)))
    rhsc = w.s([dfzc, dgzc], cllab, '( %s -> %s e. CC )' % (A1, RHS))
    ds = dvdom(w, A0, MPM, 'z', 'D', RHS, dvc, rhsc)
    w.qed([cnc, ds], 'jca', STATEMENTS[label])
    return w


# ---------------------------------------------------------------- zl2hadd, zl2hsub
if __name__ == '__main__' and (not only or 'zl2hadd' in only):
    go(holbin('zl2hadd', '+', 'addcn', 'dvmptadd', 'addcld', 'A pointwise sum of two functions holomorphic on a common domain is holomorphic there ( ~ holmul with ~ addcn , ~ dvmptadd ).'), only)
if __name__ == '__main__' and (not only or 'zl2hsub' in only):
    go(holbin('zl2hsub', '-', 'subcn', 'dvmptsub', 'subcld', 'A pointwise difference of two functions holomorphic on a common domain is holomorphic there ( ~ holmul with ~ subcn , ~ dvmptsub ).'), only)


# ---------------------------------------------------------------- zl2hres
if __name__ == '__main__' and (not only or 'zl2hres' in only):
    w = W('zl2hres', 'A function holomorphic on ` D ` restricted to an open ` U C_ D ` is holomorphic on ` U ` ( ~ zl2hent for a general domain: ~ feqresmpt , ~ rescncf , ~ dvres , ~ isopn3i ).')
    R = '( z e. U |-> ( F ` z ) )'
    A0 = '( %s /\\ ( U e. %s /\\ U C_ D ) )' % (HOL('F', 'D'), TOP)
    hf = D(w, A0, 'simpl', [], HOL('F', 'D'))
    fcn = D(w, A0, 'simpld', [hf], 'F e. ( D -cn-> CC )'); fd = D(w, A0, 'simprd', [hf], 'D C_ dom ( CC _D F )')
    uo = D(w, A0, 'simprl', [], 'U e. %s' % TOP); ud = D(w, A0, 'simprr', [], 'U C_ D')
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    rs = w.s([ff, ud], 'feqresmpt', '( %s -> ( F |` U ) = %s )' % (A0, R))
    rc = w.s([ud, fcn, w.inst('rescncf')], 'sylc', '( %s -> ( F |` U ) e. ( U -cn-> CC ) )' % A0)
    dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    uss = D(w, A0, 'sstrd', [ud, dss], 'U C_ CC')
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    tt = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    ssc = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    idv = w.s([e, tt], 'dvres', '( ( ( CC C_ CC /\\ F : D --> CC ) /\\ ( D C_ CC /\\ U C_ CC ) ) -> ( CC _D ( F |` U ) ) = ( ( CC _D F ) |` ( ( int ` %s ) ` U ) ) )' % TOP)
    dv = w.s([w.s([ssc, ff], 'jca', '( %s -> ( CC C_ CC /\\ F : D --> CC ) )' % A0), w.s([dss, uss], 'jca', '( %s -> ( D C_ CC /\\ U C_ CC ) )' % A0), idv], 'syl2anc',
             '( %s -> ( CC _D ( F |` U ) ) = ( ( CC _D F ) |` ( ( int ` %s ) ` U ) ) )' % (A0, TOP))
    ct = w.s([w.s([e], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
    io = w.s([ct, uo, w.inst('isopn3i')], 'syl2anc', '( %s -> ( ( int ` %s ) ` U ) = U )' % (A0, TOP))
    dv2 = w.s([dv, w.s([io], 'reseq2d', '( %s -> ( ( CC _D F ) |` ( ( int ` %s ) ` U ) ) = ( ( CC _D F ) |` U ) )' % (A0, TOP))], 'eqtrd',
              '( %s -> ( CC _D ( F |` U ) ) = ( ( CC _D F ) |` U ) )' % A0)
    dm1 = w.s([dv2], 'dmeqd', '( %s -> dom ( CC _D ( F |` U ) ) = dom ( ( CC _D F ) |` U ) )' % A0)
    dm2 = w.s([w.s([], 'dmres', 'dom ( ( CC _D F ) |` U ) = ( U i^i dom ( CC _D F ) )')], 'a1i', '( %s -> dom ( ( CC _D F ) |` U ) = ( U i^i dom ( CC _D F ) ) )' % A0)
    sdd = D(w, A0, 'sstrd', [ud, fd], 'U C_ dom ( CC _D F )')
    sin = w.s([w.s([w.s([], 'ssid', 'U C_ U')], 'a1i', '( %s -> U C_ U )' % A0), sdd], 'ssind', '( %s -> U C_ ( U i^i dom ( CC _D F ) ) )' % A0)
    dmq = w.s([dm1, dm2], 'eqtrd', '( %s -> dom ( CC _D ( F |` U ) ) = ( U i^i dom ( CC _D F ) ) )' % A0)
    sd2 = w.s([sin, dmq], 'sseqtrrd', '( %s -> U C_ dom ( CC _D ( F |` U ) ) )' % A0)
    c1 = w.s([rc, w.s([rs], 'eleq1d', '( %s -> ( ( F |` U ) e. ( U -cn-> CC ) <-> %s e. ( U -cn-> CC ) ) )' % (A0, R))], 'mpbid', '( %s -> %s e. ( U -cn-> CC ) )' % (A0, R))
    c2 = w.s([sd2, w.s([w.s([w.s([rs], 'oveq2d', '( %s -> ( CC _D ( F |` U ) ) = ( CC _D %s ) )' % (A0, R))], 'dmeqd', '( %s -> dom ( CC _D ( F |` U ) ) = dom ( CC _D %s ) )' % (A0, R))], 'sseq2d',
                       '( %s -> ( U C_ dom ( CC _D ( F |` U ) ) <-> U C_ dom ( CC _D %s ) ) )' % (A0, R))], 'mpbid', '( %s -> U C_ dom ( CC _D %s ) )' % (A0, R))
    w.qed([c1, c2], 'jca', STATEMENTS['zl2hres'])
    go(w, only)


# ---------------------------------------------------------------- zl2cfblav
if __name__ == '__main__' and (not only or 'zl2cfblav' in only):
    w = W('zl2cfblav', 'A sequence bounded by 1 satisfies the log-average bound of ~ dconvlim with ` K = 1 ` ( ~ lchmulav made generic; ~ harmonicubnd ).')
    A0 = '( A : NN --> CC /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ 1 )'
    Ay = '( %s /\\ y e. RR )' % A0
    A1 = '( %s /\\ 1 <_ y )' % Ay
    RG = '( 1 ... ( |_ ` y ) )'
    Ad = '( %s /\\ d e. %s )' % (A1, RG)
    dn = w.s([D(w, Ad, 'simpr', [], 'd e. %s' % RG), w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % Ad)
    a0d = D(w, Ad, 'ad3antrrr', [], A0)
    af = D(w, Ad, 'simpld', [a0d], 'A : NN --> CC'); ab_ = D(w, Ad, 'simprd', [a0d], 'A. m e. NN ( abs ` ( A ` m ) ) <_ 1')
    AA = '( abs ` ( A ` d ) )'
    ab, _ = inst_ral(w, Ad, ab_, 'm', 'NN', '( abs ` ( A ` m ) ) <_ 1', 'd', dn)
    drp = D(w, Ad, 'nnrpd', [dn], 'd e. RR+')
    aar = D(w, Ad, 'abscld', [D(w, Ad, 'ffvelcdmd', [af, dn], '( A ` d ) e. CC')], '%s e. RR' % AA)
    td = D(w, Ad, 'lediv1dd', [aar, a1(w, Ad, '1re', '1 e. RR'), drp, ab], '( %s / d ) <_ ( 1 / d )' % AA)
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A1, RG))
    adr = D(w, Ad, 'rerpdivcld', [aar, drp], '( %s / d ) e. RR' % AA)
    odr = D(w, Ad, 'rpred', [D(w, Ad, 'rpreccld', [drp], '( 1 / d ) e. RR+')], '( 1 / d ) e. RR')
    s1 = w.s([fin, adr, odr, td], 'fsumle', '( %s -> sum_ d e. %s ( %s / d ) <_ sum_ d e. %s ( 1 / d ) )' % (A1, RG, AA, RG))
    yr = D(w, A1, 'simplr', [], 'y e. RR'); y1 = D(w, A1, 'simpr', [], '1 <_ y')
    hb = w.s([yr, y1, w.inst('harmonicubnd')], 'syl2anc', '( %s -> sum_ m e. %s ( 1 / m ) <_ ( ( log ` y ) + 1 ) )' % (A1, RG))
    cbm = w.s([w.s([], 'oveq2', '( m = d -> ( 1 / m ) = ( 1 / d ) )')], 'cbvsumv', 'sum_ m e. %s ( 1 / m ) = sum_ d e. %s ( 1 / d )' % (RG, RG))
    hb2 = w.s([w.s([cbm], 'a1i', '( %s -> sum_ m e. %s ( 1 / m ) = sum_ d e. %s ( 1 / d ) )' % (A1, RG, RG)), hb], 'eqbrtrrd', '( %s -> sum_ d e. %s ( 1 / d ) <_ ( ( log ` y ) + 1 ) )' % (A1, RG))
    SA = 'sum_ d e. %s ( %s / d )' % (RG, AA)
    ypos = linarith(w, A1, [y1], '0 < y', leaves={'y': yr})
    yrp = D(w, A1, 'elrpd', [yr, ypos], 'y e. RR+')
    RHS = '( ( log ` y ) + 1 )'
    rr = D(w, A1, 'readdcld', [D(w, A1, 'relogcld', [yrp], '( log ` y ) e. RR'), a1(w, A1, '1re', '1 e. RR')], '%s e. RR' % RHS)
    s2 = D(w, A1, 'letrd', [w.s([fin, adr], 'fsumrecl', '( %s -> %s e. RR )' % (A1, SA)), w.s([fin, odr], 'fsumrecl', '( %s -> sum_ d e. %s ( 1 / d ) e. RR )' % (A1, RG)), rr, s1, hb2],
           '%s <_ %s' % (SA, RHS))
    im = w.s([s2], 'ex', '( %s -> ( 1 <_ y -> %s <_ %s ) )' % (Ay, SA, RHS))
    w.qed([im], 'ralrimiva', STATEMENTS['zl2cfblav'])
    go(w, only)


def nxm(w, ante, nx):
    """( ante -> ( MC e. NN /\\ YP e. ( Base ` ( DChr ` MC ) ) ) ) from nx: ( ante -> NX )"""
    mn = w.s([nx, w.inst('dchrcondnn')], 'syl', '( %s -> %s e. NN )' % (ante, MC))
    yb = w.s([nx, w.inst('dchrprimcl')], 'syl', '( %s -> %s e. ( Base ` ( DChr ` %s ) ) )' % (ante, YP, MC))
    return w.s([mn, yb], 'jca', '( %s -> ( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) ) )' % (ante, MC, YP, MC)), mn, yb


NXM = '( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) )' % (MC, YP, MC)


# ---------------------------------------------------------------- zl2chb
if __name__ == '__main__' and (not only or 'zl2chb' in only):
    w = W('zl2chb', 'The character on ` NN ` is a sequence bounded by 1, in the form of ~ dsercl ( ~ zl1chrb ).')
    A0 = NXL
    ch = w.s([], 'zl1chrb', '( %s -> %s )' % (NXL, ZL1.CHRBX))
    f3 = D(w, A0, 'simpld', [ch], ZL1.CHRBX.split(' /\\ A. j e. NN ( abs')[0][2:])
    ff = D(w, A0, 'simp1d', [f3], '%s : NN --> CC' % CXN)
    BJ = '( abs ` ( %s ` j ) ) <_ 1' % CXN
    bj = D(w, A0, 'simprd', [ch], 'A. j e. NN %s' % BJ)
    idx = w.s([], 'id', '( j = m -> j = m )')
    st, BM = w.wcongr(BJ, {'j': 'm'}, 'j = m', {'j': idx})
    cbv = w.s([st], 'cbvralvw', '( A. j e. NN %s <-> A. m e. NN %s )' % (BJ, BM))
    bm = w.s([bj, cbv], 'sylib', '( %s -> A. m e. NN %s )' % (A0, BM))
    w.qed([ff, a1(w, A0, '1re', '1 e. RR'), bm], '3jca', STATEMENTS['zl2chb'])
    go(w, only)


# ---------------------------------------------------------------- zl2chs
if __name__ == '__main__' and (not only or 'zl2chs' in only):
    w = W('zl2chs', 'The Dirichlet series of the character on ` NN ` converges to a complex number bounded by ` 1 + 1 / ( Re Z - 1 ) ` on ` 1 < Re Z ` ( ~ dsercl , ~ lchrbnd , ~ zl1cxv ).')
    A0 = '( %s /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % NXL
    nx = D(w, A0, 'simpl', [], NXL); zz = D(w, A0, 'simpr', [], '( Z e. CC /\\ 1 < ( Re ` Z ) )')
    cfb = w.s([nx, w.inst('zl2chb')], 'syl', '( %s -> %s )' % (A0, CFB1(CXN)))
    S1 = DS(CXN, 'Z')
    cl = w.s([cfb, zz, w.inst('dsercl')], 'syl2anc', '( %s -> %s e. CC )' % (A0, S1))
    bnd = w.s([nx, zz, w.inst('lchrbnd')], 'syl2anc', '( %s -> ( abs ` sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) ) <_ ( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) ) )' % (A0, LHN))
    Ak = '( %s /\\ k e. NN )' % A0
    v = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NXL)), D(w, Ak, 'simpr', [], 'k e. NN'), w.inst('zl1cxv')], 'syl2anc', '( %s -> ( %s ` k ) = ( X ` ( %s ` k ) ) )' % (Ak, CXN, LHN))
    v2 = E(w, Ak, 'oveq1d', [v], '( ( %s ` k ) x. ( k ^c -u Z ) )' % CXN, '( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) )' % LHN)
    se = w.s([v2], 'sumeq2dv', '( %s -> %s = sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) )' % (A0, S1, LHN))
    ab = w.s([E(w, A0, 'fveq2d', [se], '( abs ` %s )' % S1, '( abs ` sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) )' % LHN), bnd], 'eqbrtrd',
             '( %s -> ( abs ` %s ) <_ ( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) ) )' % (A0, S1))
    w.qed([cl, ab], 'jca', STATEMENTS['zl2chs'])
    go(w, only)


# ---------------------------------------------------------------- zl2chm
if __name__ == '__main__' and (not only or 'zl2chm' in only):
    w = W('zl2chm', 'Complete multiplicativity of the character on ` NN ` along a divisor: ` C ( D ) C ( K / D ) = C ( K ) ` ( ~ zl1chrb ).')
    A0 = '( %s /\\ ( K e. NN /\\ D e. %s ) )' % (NXL, DIV('K'))
    nx = D(w, A0, 'simpl', [], NXL); kn = D(w, A0, 'simprl', [], 'K e. NN'); dd = D(w, A0, 'simprr', [], 'D e. %s' % DIV('K'))
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DIV('K'))], 'a1i', '( %s -> %s C_ NN )' % (A0, DIV('K')))
    dn = D(w, A0, 'sseldd', [ss, dd], 'D e. NN')
    qn = D(w, A0, 'sseldd', [ss, w.s([kn, dd, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( K / D ) e. %s )' % (A0, DIV('K')))], '( K / D ) e. NN')
    ch = w.s([nx, w.inst('zl1chrb')], 'syl', '( %s -> %s )' % (A0, ZL1.CHRBX))
    f3 = D(w, A0, 'simpld', [ch], ZL1.CHRBX.split(' /\\ A. j e. NN ( abs')[0][2:])
    MULB = 'A. j e. NN ( %s ` ( i x. j ) ) = ( ( %s ` i ) x. ( %s ` j ) )' % (CXN, CXN, CXN)
    mul = D(w, A0, 'simp3d', [f3], 'A. i e. NN %s' % MULB)
    m1, b1 = inst_ral(w, A0, mul, 'i', 'NN', MULB, 'D', dn)
    m2, b2 = inst_ral(w, A0, m1, 'j', 'NN', b1[len('A. j e. NN '):], '( K / D )', qn)
    dc = D(w, A0, 'nncnd', [dn], 'D e. CC'); kc = D(w, A0, 'nncnd', [kn], 'K e. CC'); dne = D(w, A0, 'nnne0d', [dn], 'D =/= 0')
    cn = D(w, A0, 'divcan2d', [kc, dc, dne], '( D x. ( K / D ) ) = K')
    fe = E(w, A0, 'fveq2d', [cn], '( %s ` ( D x. ( K / D ) ) )' % CXN, '( %s ` K )' % CXN)
    w.qed([m2, fe], 'eqtr3d', STATEMENTS['zl2chm'])
    go(w, only)


# ---------------------------------------------------------------- zl2afv
if __name__ == '__main__' and (not only or 'zl2afv' in only):
    w = W('zl2afv', 'The value of the Euler-factor coefficient sequence ` mu ( q ) chi_1 ( q ) [ q || N ] ` ( ~ fvmptg ).')
    A0 = 'K e. NN'
    BODY = 'if ( q || N , ( ( mmu ` q ) x. ( %s ` q ) ) , 0 )' % CY
    VAL = 'if ( K || N , ( ( mmu ` K ) x. ( %s ` K ) ) , 0 )' % CY
    idx = w.s([], 'id', '( q = K -> q = K )')
    st, val = w.congr(BODY, {'q': 'K'}, 'q = K', {'q': idx})
    assert val == VAL, (val, VAL)
    em = w.s([], 'eqid', '%s = %s' % (AF, AF))
    fm = w.s([st, em], 'fvmptg', '( ( K e. NN /\\ %s e. _V ) -> ( %s ` K ) = %s )' % (VAL, AF, VAL))
    ex = w.s([w.s([w.s([], 'ovex', '( ( mmu ` K ) x. ( %s ` K ) ) e. _V' % CY)], 'a1i', '( %s -> ( ( mmu ` K ) x. ( %s ` K ) ) e. _V )' % (A0, CY)),
              w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A0)], 'ifexd', '( %s -> %s e. _V )' % (A0, VAL))
    w.qed([w.s([], 'id', '( %s -> %s )' % (A0, A0)), ex, fm], 'syl2anc', STATEMENTS['zl2afv'])
    go(w, only)


# ---------------------------------------------------------------- zl2afb
if __name__ == '__main__' and (not only or 'zl2afb' in only):
    w = W('zl2afb', 'The Euler-factor coefficient sequence is a sequence bounded by 1 ( ~ mule1 , ~ zl2chb at the conductor ).')
    A0 = NXL
    nxs, mn, yb = nxm(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    cy = w.s([nxs, w.inst('zl2chb')], 'syl', '( %s -> %s )' % (A0, CFB1(CY)))
    cyf = D(w, A0, 'simp1d', [cy], '%s : NN --> CC' % CY); cyb = D(w, A0, 'simp3d', [cy], 'A. m e. NN ( abs ` ( %s ` m ) ) <_ 1' % CY)
    Aq = '( %s /\\ q e. NN )' % A0
    qn = D(w, Aq, 'simpr', [], 'q e. NN')
    MQ = '( ( mmu ` q ) x. ( %s ` q ) )' % CY
    mqc = D(w, Aq, 'mulcld', [D(w, Aq, 'zcnd', [w.s([qn, w.inst('mucl')], 'syl', '( %s -> ( mmu ` q ) e. ZZ )' % Aq)], '( mmu ` q ) e. CC'),
                               D(w, Aq, 'ffvelcdmd', [w.s([cyf], 'adantr', '( %s -> %s : NN --> CC )' % (Aq, CY)), qn], '( %s ` q ) e. CC' % CY)], '%s e. CC' % MQ)
    BODY = 'if ( q || N , %s , 0 )' % MQ
    bc = D(w, Aq, 'ifcld', [mqc, a1(w, Aq, '0cn', '0 e. CC')], '%s e. CC' % BODY)
    ff = w.s([bc, w.s([], 'eqid', '%s = %s' % (AF, AF))], 'fmptd', '( %s -> %s : NN --> CC )' % (A0, AF))
    # the bound at m
    Am = '( %s /\\ m e. NN )' % A0
    mn_ = D(w, Am, 'simpr', [], 'm e. NN')
    v = w.s([mn_, w.inst('zl2afv')], 'syl', '( %s -> ( %s ` m ) = if ( m || N , ( ( mmu ` m ) x. ( %s ` m ) ) , 0 ) )' % (Am, AF, CY))
    MM = '( ( mmu ` m ) x. ( %s ` m ) )' % CY
    mu1 = w.s([mn_, w.inst('mule1')], 'syl', '( %s -> ( abs ` ( mmu ` m ) ) <_ 1 )' % Am)
    # ( abs ` ( CY ` m ) ) <_ 1 by rspcva-free route: the ral at m itself (rspa)
    cyb2 = w.s([cyb], 'r19.21bi', '( %s -> ( abs ` ( %s ` m ) ) <_ 1 )' % (Am, CY))
    muc = D(w, Am, 'zcnd', [w.s([mn_, w.inst('mucl')], 'syl', '( %s -> ( mmu ` m ) e. ZZ )' % Am)], '( mmu ` m ) e. CC')
    cyc = D(w, Am, 'ffvelcdmd', [w.s([cyf], 'adantr', '( %s -> %s : NN --> CC )' % (Am, CY)), mn_], '( %s ` m ) e. CC' % CY)
    am = D(w, Am, 'absmuld', [muc, cyc], '( abs ` %s ) = ( ( abs ` ( mmu ` m ) ) x. ( abs ` ( %s ` m ) ) )' % (MM, CY))
    amu = D(w, Am, 'abscld', [muc], '( abs ` ( mmu ` m ) ) e. RR'); acy = D(w, Am, 'abscld', [cyc], '( abs ` ( %s ` m ) ) e. RR' % CY)
    amu0 = D(w, Am, 'absge0d', [muc], '0 <_ ( abs ` ( mmu ` m ) )'); acy0 = D(w, Am, 'absge0d', [cyc], '0 <_ ( abs ` ( %s ` m ) )' % CY)
    pr = D(w, Am, 'lemul12ad', [amu, a1(w, Am, '1re', '1 e. RR'), acy, a1(w, Am, '1re', '1 e. RR'), amu0, acy0, mu1, cyb2], '( ( abs ` ( mmu ` m ) ) x. ( abs ` ( %s ` m ) ) ) <_ ( 1 x. 1 )' % CY)
    pr2 = w.s([pr, a1(w, Am, '1t1e1', '( 1 x. 1 ) = 1')], 'breqtrd', '( %s -> ( ( abs ` ( mmu ` m ) ) x. ( abs ` ( %s ` m ) ) ) <_ 1 )' % (Am, CY))
    b1 = w.s([am, pr2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ 1 )' % (Am, MM))
    b0 = w.s([w.s([w.s([], 'abs0', '( abs ` 0 ) = 0'), w.s([], '0le1', '0 <_ 1')], 'eqbrtri', '( abs ` 0 ) <_ 1')], 'a1i', '( %s -> ( abs ` 0 ) <_ 1 )' % Am)
    # abs of the if
    fi = w.s([], 'fvif', '( abs ` if ( m || N , %s , 0 ) ) = if ( m || N , ( abs ` %s ) , ( abs ` 0 ) )' % (MM, MM))
    A1 = '( %s /\\ m || N )' % Am; A2 = '( %s /\\ -. m || N )' % Am
    c1 = w.s([D(w, A1, 'iftrued', [D(w, A1, 'simpr', [], 'm || N')], 'if ( m || N , ( abs ` %s ) , ( abs ` 0 ) ) = ( abs ` %s )' % (MM, MM)), w.s([b1], 'adantr', '( %s -> ( abs ` %s ) <_ 1 )' % (A1, MM))], 'eqbrtrd',
             '( %s -> if ( m || N , ( abs ` %s ) , ( abs ` 0 ) ) <_ 1 )' % (A1, MM))
    c2 = w.s([D(w, A2, 'iffalsed', [D(w, A2, 'simpr', [], '-. m || N')], 'if ( m || N , ( abs ` %s ) , ( abs ` 0 ) ) = ( abs ` 0 )' % MM), w.s([b0], 'adantr', '( %s -> ( abs ` 0 ) <_ 1 )' % A2)], 'eqbrtrd',
             '( %s -> if ( m || N , ( abs ` %s ) , ( abs ` 0 ) ) <_ 1 )' % (A2, MM))
    cc = w.s([c1, c2], 'pm2.61dan', '( %s -> if ( m || N , ( abs ` %s ) , ( abs ` 0 ) ) <_ 1 )' % (Am, MM))
    cc2 = w.s([w.s([fi], 'a1i', '( %s -> ( abs ` if ( m || N , %s , 0 ) ) = if ( m || N , ( abs ` %s ) , ( abs ` 0 ) ) )' % (Am, MM, MM)), cc], 'eqbrtrd', '( %s -> ( abs ` if ( m || N , %s , 0 ) ) <_ 1 )' % (Am, MM))
    fin = w.s([E(w, Am, 'fveq2d', [v], '( abs ` ( %s ` m ) )' % AF, '( abs ` if ( m || N , %s , 0 ) )' % MM), cc2], 'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ 1 )' % (Am, AF))
    ral = w.s([fin], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (A0, AF))
    w.qed([ff, a1(w, A0, '1re', '1 e. RR'), ral], '3jca', STATEMENTS['zl2afb'])
    go(w, only)


def divfin(w, A0, kn, K='N'):
    """( A0 -> DIV(K) e. Fin ) from kn: ( A0 -> K e. NN ) ( ~ dvdsssfz1 , ~ ssfi )"""
    DK = DIV(K)
    fz = w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (A0, K))
    ss = w.s([kn, w.inst('dvdsssfz1')], 'syl', '( %s -> { p e. NN | p || %s } C_ ( 1 ... %s ) )' % (A0, K, K))
    cb = w.s([w.s([], 'breq1', '( p = x -> ( p || %s <-> x || %s ) )' % (K, K))], 'cbvrabv', '{ p e. NN | p || %s } = %s' % (K, DK))
    ss2 = w.s([w.s([cb], 'a1i', '( %s -> { p e. NN | p || %s } = %s )' % (A0, K, DK)), ss], 'eqsstrrd', '( %s -> %s C_ ( 1 ... %s ) )' % (A0, DK, K))
    return w.s([fz, ss2, w.inst('ssfi')], 'syl2anc', '( %s -> %s e. Fin )' % (A0, DK))


def eldiv(w, A, K, dd, v='d'):
    """from dd: ( A -> v e. DIV(K) ): steps v e. NN, v || K, and the closed elrab equivalence"""
    er = w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (v, K, v, K))], 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (v, DIV(K), v, v, K))
    m = w.s([dd, w.s([er], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. NN /\\ %s || %s ) ) )' % (A, v, DIV(K), v, v, K))], 'mpbid', '( %s -> ( %s e. NN /\\ %s || %s ) )' % (A, v, v, K))
    return D(w, A, 'simpld', [m], '%s e. NN' % v), D(w, A, 'simprd', [m], '%s || %s' % (v, K)), er


def cyfun(w, A, nxs):
    """( A -> CY : NN --> CC ) and the bound ral from zl2chb at the conductor"""
    cy = w.s([nxs, w.inst('zl2chb')], 'syl', '( %s -> %s )' % (A, CFB1(CY)))
    return D(w, A, 'simp1d', [cy], '%s : NN --> CC' % CY), D(w, A, 'simp3d', [cy], 'A. m e. NN ( abs ` ( %s ` m ) ) <_ 1' % CY), cy


def muc_(w, A, dn, v='d'):
    return D(w, A, 'zcnd', [w.s([dn, w.inst('mucl')], 'syl', '( %s -> ( mmu ` %s ) e. ZZ )' % (A, v))], '( mmu ` %s ) e. CC' % v)


# ---------------------------------------------------------------- zl2musub
if __name__ == '__main__' and (not only or 'zl2musub' in only):
    w = W('zl2musub', 'The Moebius sum over the common divisors of ` K ` and ` N ` is ` [ gcd ( K , N ) = 1 ] ` ( ~ bvmusum at the gcd, ~ sumss2 , ~ dvdsgcdb ).')
    A0 = '( N e. NN /\\ K e. NN )'
    nn = D(w, A0, 'simpl', [], 'N e. NN'); kn = D(w, A0, 'simpr', [], 'K e. NN')
    G = '( K gcd N )'; DG = DIV(G); DK = DIV('K')
    gn = w.s([kn, nn, w.inst('gcdnncl')], 'syl2anc', '( %s -> %s e. NN )' % (A0, G))
    mus = w.s([gn, w.inst('bvmusum')], 'syl', '( %s -> sum_ d e. %s ( mmu ` d ) = if ( %s = 1 , 1 , 0 ) )' % (A0, DG, G))
    # DG C_ DK
    Ad = '( %s /\\ d e. %s )' % (A0, DG)
    dn, dg, er1 = eldiv(w, Ad, G, D(w, Ad, 'simpr', [], 'd e. %s' % DG))
    kz = D(w, Ad, 'nnzd', [w.s([kn], 'adantr', '( %s -> K e. NN )' % Ad)], 'K e. ZZ'); nz = D(w, Ad, 'nnzd', [w.s([nn], 'adantr', '( %s -> N e. NN )' % Ad)], 'N e. ZZ')
    dz = D(w, Ad, 'nnzd', [dn], 'd e. ZZ'); gz = D(w, Ad, 'nnzd', [w.s([gn], 'adantr', '( %s -> %s e. NN )' % (Ad, G))], '%s e. ZZ' % G)
    gk = D(w, Ad, 'simpld', [w.s([kz, nz, w.inst('gcddvds')], 'syl2anc', '( %s -> ( %s || K /\\ %s || N ) )' % (Ad, G, G))], '%s || K' % G)
    tr = w.s([w.s([dz, gz, kz], '3jca', '( %s -> ( d e. ZZ /\\ %s e. ZZ /\\ K e. ZZ ) )' % (Ad, G)), w.inst('dvdstr')], 'syl', '( %s -> ( ( d || %s /\\ %s || K ) -> d || K ) )' % (Ad, G, G))
    dk = w.s([w.s([dg, gk], 'jca', '( %s -> ( d || %s /\\ %s || K ) )' % (Ad, G, G)), tr], 'mpd', '( %s -> d || K )' % Ad)
    er2 = w.s([w.s([], 'breq1', '( x = d -> ( x || K <-> d || K ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || K ) )' % DK)
    mdk = w.s([w.s([dn, dk], 'jca', '( %s -> ( d e. NN /\\ d || K ) )' % Ad), w.s([er2], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ d || K ) ) )' % (Ad, DK))], 'mpbird', '( %s -> d e. %s )' % (Ad, DK))
    ss = w.s([w.s([mdk], 'ex', '( %s -> ( d e. %s -> d e. %s ) )' % (A0, DG, DK))], 'ssrdv', '( %s -> %s C_ %s )' % (A0, DG, DK))
    cc = w.s([muc_(w, Ad, dn)], 'ralrimiva', '( %s -> A. d e. %s ( mmu ` d ) e. CC )' % (A0, DG))
    fin = divfin(w, A0, kn, 'K')
    fin2 = w.s([fin], 'olcd', '( %s -> ( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin ) )' % (A0, DK, DK))
    s2 = w.s([w.s([ss, cc], 'jca', '( %s -> ( %s C_ %s /\\ A. d e. %s ( mmu ` d ) e. CC ) )' % (A0, DG, DK, DG)), fin2, w.inst('sumss2')], 'syl2anc',
             '( %s -> sum_ d e. %s ( mmu ` d ) = sum_ d e. %s if ( d e. %s , ( mmu ` d ) , 0 ) )' % (A0, DG, DK, DG))
    # termwise on DK
    Ak = '( %s /\\ d e. %s )' % (A0, DK)
    dn2, dk2, _ = eldiv(w, Ak, 'K', D(w, Ak, 'simpr', [], 'd e. %s' % DK))
    dz2 = D(w, Ak, 'nnzd', [dn2], 'd e. ZZ'); kz2 = D(w, Ak, 'nnzd', [w.s([kn], 'adantr', '( %s -> K e. NN )' % Ak)], 'K e. ZZ'); nz2 = D(w, Ak, 'nnzd', [w.s([nn], 'adantr', '( %s -> N e. NN )' % Ak)], 'N e. ZZ')
    b1 = w.s([w.s([dz2, kz2, nz2], '3jca', '( %s -> ( d e. ZZ /\\ K e. ZZ /\\ N e. ZZ ) )' % Ak), w.inst('dvdsgcdb')], 'syl', '( %s -> ( ( d || K /\\ d || N ) <-> d || %s ) )' % (Ak, G))
    b2 = w.s([dk2], 'biantrurd', '( %s -> ( d || N <-> ( d || K /\\ d || N ) ) )' % Ak)
    b3 = w.s([b2, b1], 'bitrd', '( %s -> ( d || N <-> d || %s ) )' % (Ak, G))
    b4 = w.s([dn2], 'biantrurd', '( %s -> ( d || %s <-> ( d e. NN /\\ d || %s ) ) )' % (Ak, G, G))
    b5 = w.s([b3, b4], 'bitrd', '( %s -> ( d || N <-> ( d e. NN /\\ d || %s ) ) )' % (Ak, G))
    b6 = w.s([b5, w.s([er1], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ d || %s ) ) )' % (Ak, DG, G))], 'bitr4d', '( %s -> ( d || N <-> d e. %s ) )' % (Ak, DG))
    ifb = w.s([b6], 'ifbid', '( %s -> if ( d || N , ( mmu ` d ) , 0 ) = if ( d e. %s , ( mmu ` d ) , 0 ) )' % (Ak, DG))
    s3 = w.s([ifb], 'sumeq2dv', '( %s -> sum_ d e. %s if ( d || N , ( mmu ` d ) , 0 ) = sum_ d e. %s if ( d e. %s , ( mmu ` d ) , 0 ) )' % (A0, DK, DK, DG))
    s4 = w.s([s2, mus], 'eqtr3d', '( %s -> sum_ d e. %s if ( d e. %s , ( mmu ` d ) , 0 ) = if ( %s = 1 , 1 , 0 ) )' % (A0, DK, DG, G))
    w.qed([s3, s4], 'eqtrd', STATEMENTS['zl2musub'])
    go(w, only)


# ---------------------------------------------------------------- zl2cxv2
if __name__ == '__main__' and (not only or 'zl2cxv2' in only):
    w = W('zl2cxv2', 'The character on ` NN ` in terms of its primitive character: ` chi ( K ) = [ gcd ( K , N ) = 1 ] chi_1 ( K ) ` ( ~ dchrprimind , ~ dchrindval2 ; Mathlib ` changeLevel_primitiveCharacter ` ).')
    A0 = '( %s /\\ K e. NN )' % NXL
    nx = D(w, A0, 'simpl', [], NXL); kn = D(w, A0, 'simpr', [], 'K e. NN')
    nxs, mn, yb = nxm(w, A0, nx)
    nn = D(w, A0, 'simpld', [nx], 'N e. NN')
    dv = w.s([nx, w.inst('dchrconddvdn')], 'syl', '( %s -> %s || N )' % (A0, MC))
    kz = D(w, A0, 'nnzd', [kn], 'K e. ZZ')
    IND = '( ( %s DChrInd N ) ` %s )' % (MC, YP)
    G = '( K gcd N )'
    h = w.s([w.s([w.s([mn, nn, dv], '3jca', '( %s -> ( %s e. NN /\\ N e. NN /\\ %s || N ) )' % (A0, MC, MC)), yb], 'jca',
                  '( %s -> ( ( %s e. NN /\\ N e. NN /\\ %s || N ) /\\ %s e. ( Base ` ( DChr ` %s ) ) ) )' % (A0, MC, MC, YP, MC)), kz], 'jca',
             '( %s -> ( ( ( %s e. NN /\\ N e. NN /\\ %s || N ) /\\ %s e. ( Base ` ( DChr ` %s ) ) ) /\\ K e. ZZ ) )' % (A0, MC, MC, YP, MC))
    iv = w.s([h, w.inst('dchrindval2')], 'syl', '( %s -> ( %s ` ( %s ` K ) ) = if ( %s = 1 , ( %s ` ( %s ` K ) ) , 0 ) )' % (A0, IND, LHN, G, YP, LMC))
    pi = w.s([nx, w.inst('dchrprimind')], 'syl', '( %s -> %s = X )' % (A0, IND))
    e1 = w.s([pi], 'fveq1d', '( %s -> ( %s ` ( %s ` K ) ) = ( X ` ( %s ` K ) ) )' % (A0, IND, LHN, LHN))
    e2 = w.s([nx, kn, w.inst('zl1cxv')], 'syl2anc', '( %s -> ( %s ` K ) = ( X ` ( %s ` K ) ) )' % (A0, CXN, LHN))
    e3 = w.s([nxs, kn, w.inst('zl1cxv')], 'syl2anc', '( %s -> ( %s ` K ) = ( %s ` ( %s ` K ) ) )' % (A0, CY, YP, LMC))
    e4 = w.s([e3], 'ifeq1d', '( %s -> if ( %s = 1 , ( %s ` K ) , 0 ) = if ( %s = 1 , ( %s ` ( %s ` K ) ) , 0 ) )' % (A0, G, CY, G, YP, LMC))
    c1 = w.s([e2, w.s([e1], 'eqcomd', '( %s -> ( X ` ( %s ` K ) ) = ( %s ` ( %s ` K ) ) )' % (A0, LHN, IND, LHN))], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` ( %s ` K ) ) )' % (A0, CXN, IND, LHN))
    c2 = w.s([c1, iv], 'eqtrd', '( %s -> ( %s ` K ) = if ( %s = 1 , ( %s ` ( %s ` K ) ) , 0 ) )' % (A0, CXN, G, YP, LMC))
    w.qed([c2, e4], 'eqtr4d', STATEMENTS['zl2cxv2'])
    go(w, only)


# ---------------------------------------------------------------- zl2cxc
if __name__ == '__main__' and (not only or 'zl2cxc' in only):
    w = W('zl2cxc', 'The Dirichlet convolution of the Euler-factor coefficients with the primitive character is the character: '
          '` sum_ ( d || K ) mu ( d ) chi_1 ( d ) [ d || N ] chi_1 ( K / d ) = chi ( K ) ` ( ~ zl2chm , ~ zl2musub , ~ zl2cxv2 ).')
    A0 = '( %s /\\ K e. NN )' % NXL
    nx = D(w, A0, 'simpl', [], NXL); kn = D(w, A0, 'simpr', [], 'K e. NN')
    nxs, mn, yb = nxm(w, A0, nx)
    nn = D(w, A0, 'simpld', [nx], 'N e. NN')
    cyf, cyb, _ = cyfun(w, A0, nxs)
    DK = DIV('K'); G = '( K gcd N )'; CK = '( %s ` K )' % CY
    ckc = D(w, A0, 'ffvelcdmd', [cyf, kn], '%s e. CC' % CK)
    Ad = '( %s /\\ d e. %s )' % (A0, DK)
    dd = D(w, Ad, 'simpr', [], 'd e. %s' % DK)
    dn, dk, _ = eldiv(w, Ad, 'K', dd)
    CQ = '( %s ` ( K / d ) )' % CY; CD = '( %s ` d )' % CY; MQ = '( ( mmu ` d ) x. %s )' % CD
    afv = w.s([dn, w.inst('zl2afv')], 'syl', '( %s -> ( %s ` d ) = if ( d || N , %s , 0 ) )' % (Ad, AF, MQ))
    chm = w.s([w.s([w.s([nxs], 'adantr', '( %s -> %s )' % (Ad, NXM)), w.s([w.s([kn], 'adantr', '( %s -> K e. NN )' % Ad), dd], 'jca', '( %s -> ( K e. NN /\\ d e. %s ) )' % (Ad, DK))], 'jca',
                  '( %s -> ( %s /\\ ( K e. NN /\\ d e. %s ) ) )' % (Ad, NXM, DK)), w.inst('zl2chm')], 'syl', '( %s -> ( %s x. %s ) = %s )' % (Ad, CD, CQ, CK))
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DK)], 'a1i', '( %s -> %s C_ NN )' % (Ad, DK))
    qn = D(w, Ad, 'sseldd', [ss, w.s([w.s([kn], 'adantr', '( %s -> K e. NN )' % Ad), dd, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( K / d ) e. %s )' % (Ad, DK))], '( K / d ) e. NN')
    cyfa = w.s([cyf], 'adantr', '( %s -> %s : NN --> CC )' % (Ad, CY))
    cdc = D(w, Ad, 'ffvelcdmd', [cyfa, dn], '%s e. CC' % CD); cqc = D(w, Ad, 'ffvelcdmd', [cyfa, qn], '%s e. CC' % CQ); ckc2 = w.s([ckc], 'adantr', '( %s -> %s e. CC )' % (Ad, CK))
    muc = muc_(w, Ad, dn)
    T0 = '( ( %s ` d ) x. %s )' % (AF, CQ)
    t1 = E(w, Ad, 'oveq1d', [afv], T0, '( if ( d || N , %s , 0 ) x. %s )' % (MQ, CQ))
    t2 = w.s([w.s([], 'ovif', '( if ( d || N , %s , 0 ) x. %s ) = if ( d || N , ( %s x. %s ) , ( 0 x. %s ) )' % (MQ, CQ, MQ, CQ, CQ))], 'a1i',
             '( %s -> ( if ( d || N , %s , 0 ) x. %s ) = if ( d || N , ( %s x. %s ) , ( 0 x. %s ) ) )' % (Ad, MQ, CQ, MQ, CQ, CQ))
    t3a = D(w, Ad, 'mulassd', [muc, cdc, cqc], '( %s x. %s ) = ( ( mmu ` d ) x. ( %s x. %s ) )' % (MQ, CQ, CD, CQ))
    t3b = E(w, Ad, 'oveq2d', [chm], '( ( mmu ` d ) x. ( %s x. %s ) )' % (CD, CQ), '( ( mmu ` d ) x. %s )' % CK)
    t3 = w.s([t3a, t3b], 'eqtrd', '( %s -> ( %s x. %s ) = ( ( mmu ` d ) x. %s ) )' % (Ad, MQ, CQ, CK))
    t4 = D(w, Ad, 'mul02d', [cqc], '( 0 x. %s ) = 0' % CQ)
    t5 = w.s([t3, t4], 'ifeq12d', '( %s -> if ( d || N , ( %s x. %s ) , ( 0 x. %s ) ) = if ( d || N , ( ( mmu ` d ) x. %s ) , 0 ) )' % (Ad, MQ, CQ, CQ, CK))
    IFM = 'if ( d || N , ( mmu ` d ) , 0 )'
    t6 = w.s([w.s([], 'ovif', '( %s x. %s ) = if ( d || N , ( ( mmu ` d ) x. %s ) , ( 0 x. %s ) )' % (IFM, CK, CK, CK))], 'a1i',
             '( %s -> ( %s x. %s ) = if ( d || N , ( ( mmu ` d ) x. %s ) , ( 0 x. %s ) ) )' % (Ad, IFM, CK, CK, CK))
    t7 = w.s([D(w, Ad, 'mul02d', [ckc2], '( 0 x. %s ) = 0' % CK)], 'ifeq2d', '( %s -> if ( d || N , ( ( mmu ` d ) x. %s ) , ( 0 x. %s ) ) = if ( d || N , ( ( mmu ` d ) x. %s ) , 0 ) )' % (Ad, CK, CK, CK))
    t8 = w.s([t6, t7], 'eqtrd', '( %s -> ( %s x. %s ) = if ( d || N , ( ( mmu ` d ) x. %s ) , 0 ) )' % (Ad, IFM, CK, CK))
    tl = chain(w, Ad, [T0, '( if ( d || N , %s , 0 ) x. %s )' % (MQ, CQ), 'if ( d || N , ( %s x. %s ) , ( 0 x. %s ) )' % (MQ, CQ, CQ), 'if ( d || N , ( ( mmu ` d ) x. %s ) , 0 )' % CK], [t1, t2, t5])
    term = w.s([tl, t8], 'eqtr4d', '( %s -> %s = ( %s x. %s ) )' % (Ad, T0, IFM, CK))
    s1 = w.s([term], 'sumeq2dv', '( %s -> sum_ d e. %s %s = sum_ d e. %s ( %s x. %s ) )' % (A0, DK, T0, DK, IFM, CK))
    fin = divfin(w, A0, kn, 'K')
    ifc = D(w, Ad, 'ifcld', [muc, a1(w, Ad, '0cn', '0 e. CC')], '%s e. CC' % IFM)
    SI = 'sum_ d e. %s %s' % (DK, IFM)
    s2 = w.s([fin, ckc, ifc], 'fsummulc1', '( %s -> ( %s x. %s ) = sum_ d e. %s ( %s x. %s ) )' % (A0, SI, CK, DK, IFM, CK))
    mus = w.s([w.s([nn, kn], 'jca', '( %s -> ( N e. NN /\\ K e. NN ) )' % A0), w.inst('zl2musub')], 'syl', '( %s -> %s = if ( %s = 1 , 1 , 0 ) )' % (A0, SI, G))
    s3 = E(w, A0, 'oveq1d', [mus], '( %s x. %s )' % (SI, CK), '( if ( %s = 1 , 1 , 0 ) x. %s )' % (G, CK))
    s4 = w.s([w.s([], 'ovif', '( if ( %s = 1 , 1 , 0 ) x. %s ) = if ( %s = 1 , ( 1 x. %s ) , ( 0 x. %s ) )' % (G, CK, G, CK, CK))], 'a1i',
             '( %s -> ( if ( %s = 1 , 1 , 0 ) x. %s ) = if ( %s = 1 , ( 1 x. %s ) , ( 0 x. %s ) ) )' % (A0, G, CK, G, CK, CK))
    s5 = w.s([D(w, A0, 'mullidd', [ckc], '( 1 x. %s ) = %s' % (CK, CK)), D(w, A0, 'mul02d', [ckc], '( 0 x. %s ) = 0' % CK)], 'ifeq12d',
             '( %s -> if ( %s = 1 , ( 1 x. %s ) , ( 0 x. %s ) ) = if ( %s = 1 , %s , 0 ) )' % (A0, G, CK, CK, G, CK))
    cx = w.s([nx, kn, w.inst('zl2cxv2')], 'syl2anc', '( %s -> ( %s ` K ) = if ( %s = 1 , %s , 0 ) )' % (A0, CXN, G, CK))
    terms = ['sum_ d e. %s %s' % (DK, T0), 'sum_ d e. %s ( %s x. %s )' % (DK, IFM, CK), '( %s x. %s )' % (SI, CK), '( if ( %s = 1 , 1 , 0 ) x. %s )' % (G, CK),
             'if ( %s = 1 , ( 1 x. %s ) , ( 0 x. %s ) )' % (G, CK, CK), 'if ( %s = 1 , %s , 0 )' % (G, CK), '( %s ` K )' % CXN]
    fin_ = chain(w, A0, terms, [s1, ('r', s2), s3, s4, s5, ('r', cx)])
    w.lines[-1] = w.lines[-1].replace(fin_ + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2dsp
if __name__ == '__main__' and (not only or 'zl2dsp' in only):
    w = W('zl2dsp', 'The Dirichlet series of ` chi ` is the product of the Euler-factor polynomial and the series of the primitive character on ` 1 < Re Z ` '
          '( ~ dconvlim with ~ zl2cxc ; Mathlib ` LFunction_changeLevel ` on the series side ).')
    A0 = '( %s /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % NXL
    nx = D(w, A0, 'simpl', [], NXL); zz = D(w, A0, 'simpr', [], '( Z e. CC /\\ 1 < ( Re ` Z ) )')
    nxs, mn, yb = nxm(w, A0, nx)
    afb = w.s([nx, w.inst('zl2afb')], 'syl', '( %s -> %s )' % (A0, CFB1(AF)))
    aff = D(w, A0, 'simp1d', [afb], '%s : NN --> CC' % AF); afbnd = D(w, A0, 'simp3d', [afb], 'A. m e. NN ( abs ` ( %s ` m ) ) <_ 1' % AF)
    lav = w.s([w.s([aff, afbnd], 'jca', '( %s -> ( %s : NN --> CC /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) )' % (A0, AF, AF)), w.inst('zl2cfblav')], 'syl', '( %s -> %s )' % (A0, LAVB(AF)))
    LAV3 = '( %s : NN --> CC /\\ 1 e. RR /\\ %s )' % (AF, LAVB(AF))
    lav3 = w.s([aff, a1(w, A0, '1re', '1 e. RR'), lav], '3jca', '( %s -> %s )' % (A0, LAV3))
    cfy = w.s([nxs, w.inst('zl2chb')], 'syl', '( %s -> %s )' % (A0, CFB1(CY)))
    SEQ = 'seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) x. ( n ^c -u Z ) ) ) ) e. dom ~~>' % AF
    cvg = w.s([afb, zz, w.inst('dsercvg')], 'syl2anc', '( %s -> %s )' % (A0, SEQ))
    h = w.s([w.s([lav3, cfy], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, LAV3, CFB1(CY))), w.s([zz, cvg], 'jca', '( %s -> ( ( Z e. CC /\\ 1 < ( Re ` Z ) ) /\\ %s ) )' % (A0, SEQ))], 'jca',
             '( %s -> ( ( %s /\\ %s ) /\\ ( ( Z e. CC /\\ 1 < ( Re ` Z ) ) /\\ %s ) ) )' % (A0, LAV3, CFB1(CY), SEQ))
    INN = 'sum_ d e. %s ( ( %s ` d ) x. ( %s ` ( k / d ) ) )' % (DIV('k'), AF, CY)
    SEQ2 = 'seq 1 ( + , ( n e. NN |-> ( sum_ d e. %s ( ( %s ` d ) x. ( %s ` ( n / d ) ) ) x. ( n ^c -u Z ) ) ) ) e. dom ~~>' % (DIV('n'), AF, CY)
    PRD = '( %s x. %s )' % (DS(AF, 'Z'), DS(CY, 'Z'))
    dc = w.s([h, w.inst('dconvlim')], 'syl', '( %s -> ( %s /\\ sum_ k e. NN ( %s x. ( k ^c -u Z ) ) = %s ) )' % (A0, SEQ2, INN, PRD))
    dc2 = D(w, A0, 'simprd', [dc], 'sum_ k e. NN ( %s x. ( k ^c -u Z ) ) = %s' % (INN, PRD))
    Ak = '( %s /\\ k e. NN )' % A0
    cx = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NXL)), D(w, Ak, 'simpr', [], 'k e. NN'), w.inst('zl2cxc')], 'syl2anc', '( %s -> %s = ( %s ` k ) )' % (Ak, INN, CXN))
    t = E(w, Ak, 'oveq1d', [cx], '( %s x. ( k ^c -u Z ) )' % INN, '( ( %s ` k ) x. ( k ^c -u Z ) )' % CXN)
    se = w.s([t], 'sumeq2dv', '( %s -> sum_ k e. NN ( %s x. ( k ^c -u Z ) ) = %s )' % (A0, INN, DS(CXN, 'Z')))
    w.qed([se, dc2], 'eqtr3d', STATEMENTS['zl2dsp'])
    go(w, only)


# ---------------------------------------------------------------- zl2dpf
if __name__ == '__main__' and (not only or 'zl2dpf' in only):
    w = W('zl2dpf', 'The Dirichlet series of the Euler-factor coefficients is the finite Dirichlet polynomial over the divisors of ` N ` ( ~ sumss2 ).')
    A0 = '( %s /\\ Z e. CC )' % NXL
    nx = D(w, A0, 'simpl', [], NXL); zc = D(w, A0, 'simpr', [], 'Z e. CC')
    nxs, mn, yb = nxm(w, A0, nx)
    nn = D(w, A0, 'simpld', [nx], 'N e. NN')
    cyf, cyb, _ = cyfun(w, A0, nxs)
    DN = DIV('N')
    C = lambda v: '( ( ( mmu ` %s ) x. ( %s ` %s ) ) x. ( %s ^c -u %s ) )' % (v, CY, v, v, 'Z')
    Ak = '( %s /\\ k e. %s )' % (A0, DN)
    kn, kdv, er = eldiv(w, Ak, 'N', D(w, Ak, 'simpr', [], 'k e. %s' % DN), 'k')
    ckc = D(w, Ak, 'ffvelcdmd', [w.s([cyf], 'adantr', '( %s -> %s : NN --> CC )' % (Ak, CY)), kn], '( %s ` k ) e. CC' % CY)
    muc = muc_(w, Ak, kn, 'k')
    pc = D(w, Ak, 'cxpcld', [D(w, Ak, 'nncnd', [kn], 'k e. CC'), D(w, Ak, 'negcld', [w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)], '-u Z e. CC')], '( k ^c -u Z ) e. CC')
    cc = D(w, Ak, 'mulcld', [D(w, Ak, 'mulcld', [muc, ckc], '( ( mmu ` k ) x. ( %s ` k ) ) e. CC' % CY), pc], '%s e. CC' % C('k'))
    ral = w.s([cc], 'ralrimiva', '( %s -> A. k e. %s %s e. CC )' % (A0, DN, C('k')))
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DN)], 'a1i', '( %s -> %s C_ NN )' % (A0, DN))
    nnu = w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqimssi', 'NN C_ ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN C_ ( ZZ>= ` 1 ) )' % A0)
    nnu2 = w.s([nnu], 'orcd', '( %s -> ( NN C_ ( ZZ>= ` 1 ) \\/ NN e. Fin ) )' % A0)
    s2 = w.s([w.s([ss, ral], 'jca', '( %s -> ( %s C_ NN /\\ A. k e. %s %s e. CC ) )' % (A0, DN, DN, C('k'))), nnu2, w.inst('sumss2')], 'syl2anc',
             '( %s -> sum_ k e. %s %s = sum_ k e. NN if ( k e. %s , %s , 0 ) )' % (A0, DN, C('k'), DN, C('k')))
    idx = w.s([], 'id', '( d = k -> d = k )')
    st, val = w.congr(C('d'), {'d': 'k'}, 'd = k', {'d': idx})
    assert val == C('k'), (val, C('k'))
    cb = w.s([st], 'cbvsumv', 'sum_ d e. %s %s = sum_ k e. %s %s' % (DN, C('d'), DN, C('k')))
    # termwise on NN
    An = '( %s /\\ k e. NN )' % A0
    kn2 = D(w, An, 'simpr', [], 'k e. NN')
    MQ = '( ( mmu ` k ) x. ( %s ` k ) )' % CY
    afv = w.s([kn2, w.inst('zl2afv')], 'syl', '( %s -> ( %s ` k ) = if ( k || N , %s , 0 ) )' % (An, AF, MQ))
    PK = '( k ^c -u Z )'
    pc2 = D(w, An, 'cxpcld', [D(w, An, 'nncnd', [kn2], 'k e. CC'), D(w, An, 'negcld', [w.s([zc], 'adantr', '( %s -> Z e. CC )' % An)], '-u Z e. CC')], '%s e. CC' % PK)
    u1 = E(w, An, 'oveq1d', [afv], '( ( %s ` k ) x. %s )' % (AF, PK), '( if ( k || N , %s , 0 ) x. %s )' % (MQ, PK))
    u2 = w.s([w.s([], 'ovif', '( if ( k || N , %s , 0 ) x. %s ) = if ( k || N , ( %s x. %s ) , ( 0 x. %s ) )' % (MQ, PK, MQ, PK, PK))], 'a1i',
             '( %s -> ( if ( k || N , %s , 0 ) x. %s ) = if ( k || N , ( %s x. %s ) , ( 0 x. %s ) ) )' % (An, MQ, PK, MQ, PK, PK))
    assert '( %s x. %s )' % (MQ, PK) == C('k')
    u3 = w.s([D(w, An, 'mul02d', [pc2], '( 0 x. %s ) = 0' % PK)], 'ifeq2d', '( %s -> if ( k || N , %s , ( 0 x. %s ) ) = if ( k || N , %s , 0 ) )' % (An, C('k'), PK, C('k')))
    bt = w.s([kn2], 'biantrurd', '( %s -> ( k || N <-> ( k e. NN /\\ k || N ) ) )' % An)
    bk = w.s([bt, w.s([er], 'a1i', '( %s -> ( k e. %s <-> ( k e. NN /\\ k || N ) ) )' % (An, DN))], 'bitr4d', '( %s -> ( k || N <-> k e. %s ) )' % (An, DN))
    u4 = w.s([bk], 'ifbid', '( %s -> if ( k || N , %s , 0 ) = if ( k e. %s , %s , 0 ) )' % (An, C('k'), DN, C('k')))
    term = chain(w, An, ['( ( %s ` k ) x. %s )' % (AF, PK), '( if ( k || N , %s , 0 ) x. %s )' % (MQ, PK), 'if ( k || N , %s , ( 0 x. %s ) )' % (C('k'), PK),
                         'if ( k || N , %s , 0 )' % C('k'), 'if ( k e. %s , %s , 0 )' % (DN, C('k'))], [u1, u2, u3, u4])
    s3 = w.s([term], 'sumeq2dv', '( %s -> %s = sum_ k e. NN if ( k e. %s , %s , 0 ) )' % (A0, DS(AF, 'Z'), DN, C('k')))
    r = chain(w, A0, [DS(AF, 'Z'), 'sum_ k e. NN if ( k e. %s , %s , 0 )' % (DN, C('k')), 'sum_ k e. %s %s' % (DN, C('k')), PFS('Z')],
              [s3, ('r', s2), w.s([w.s([cb], 'eqcomi', 'sum_ k e. %s %s = sum_ d e. %s %s' % (DN, C('k'), DN, C('d')))], 'a1i', '( %s -> sum_ k e. %s %s = %s )' % (A0, DN, C('k'), PFS('Z')))])
    w.lines[-1] = w.lines[-1].replace(r + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2muabs
if __name__ == '__main__' and (not only or 'zl2muabs' in only):
    w = W('zl2muabs', 'The modulus of the Moebius function is the squarefree indicator ( ~ muval2 , ~ absexp ).')
    A1 = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    ne = D(w, A1, 'simpr', [], '( mmu ` D ) =/= 0'); dn = D(w, A1, 'simpl', [], 'D e. NN')
    PD = '{ p e. Prime | p || D }'; H = '( # ` %s )' % PD
    mv = w.s([], 'muval2', '( %s -> ( mmu ` D ) = ( -u 1 ^ %s ) )' % (A1, H))
    hn0 = w.s([w.s([dn, w.inst('prmdvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A1, PD)), w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A1, H))
    ab1 = w.s([a1(w, A1, 'neg1cn', '-u 1 e. CC'), hn0, w.inst('absexp')], 'syl2anc', '( %s -> ( abs ` ( -u 1 ^ %s ) ) = ( ( abs ` -u 1 ) ^ %s ) )' % (A1, H, H))
    sa = w.s([], 'ax-1cn', '1 e. CC')
    sb = w.s([sa, w.s([], 'absneg', '( 1 e. CC -> ( abs ` -u 1 ) = ( abs ` 1 ) )')], 'ax-mp', '( abs ` -u 1 ) = ( abs ` 1 )')
    sc_ = w.s([sb, w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtri', '( abs ` -u 1 ) = 1')
    ab2 = E(w, A1, 'oveq1d', [w.s([sc_], 'a1i', '( %s -> ( abs ` -u 1 ) = 1 )' % A1)], '( ( abs ` -u 1 ) ^ %s )' % H, '( 1 ^ %s )' % H)
    ab3 = w.s([D(w, A1, 'nn0zd', [hn0], '%s e. ZZ' % H), w.inst('1exp')], 'syl', '( %s -> ( 1 ^ %s ) = 1 )' % (A1, H))
    ab = chain(w, A1, ['( abs ` ( mmu ` D ) )', '( abs ` ( -u 1 ^ %s ) )' % H, '( ( abs ` -u 1 ) ^ %s )' % H, '( 1 ^ %s )' % H, '1'], [E(w, A1, 'fveq2d', [mv], '( abs ` ( mmu ` D ) )', '( abs ` ( -u 1 ^ %s ) )' % H), ab1, ab2, ab3])
    IF = 'if ( ( mmu ` D ) =/= 0 , 1 , 0 )'
    c1 = w.s([ab, D(w, A1, 'iftrued', [ne], '%s = 1' % IF)], 'eqtr4d', '( %s -> ( abs ` ( mmu ` D ) ) = %s )' % (A1, IF))
    A2 = '( D e. NN /\\ -. ( mmu ` D ) =/= 0 )'
    nn2 = D(w, A2, 'simpr', [], '-. ( mmu ` D ) =/= 0')
    eq0 = w.s([nn2, w.s([], 'nne', '( -. ( mmu ` D ) =/= 0 <-> ( mmu ` D ) = 0 )')], 'sylib', '( %s -> ( mmu ` D ) = 0 )' % A2)
    a0 = w.s([E(w, A2, 'fveq2d', [eq0], '( abs ` ( mmu ` D ) )', '( abs ` 0 )'), a1(w, A2, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> ( abs ` ( mmu ` D ) ) = 0 )' % A2)
    c2 = w.s([a0, D(w, A2, 'iffalsed', [nn2], '%s = 0' % IF)], 'eqtr4d', '( %s -> ( abs ` ( mmu ` D ) ) = %s )' % (A2, IF))
    w.qed([c1, c2], 'pm2.61dan', STATEMENTS['zl2muabs'])
    go(w, only)


# ---------------------------------------------------------------- zl2sqfc
if __name__ == '__main__' and (not only or 'zl2sqfc' in only):
    w = W('zl2sqfc', 'The number of squarefree divisors of ` N ` is ` 2 ^ omega ( N ) ` : ` sum_ ( d || N ) | mu ( d ) | = 2 ^ omega ( N ) ` ( ~ sqff1o , ~ hashpw , ~ fsumconst ).')
    A0 = 'N e. NN'
    nn = w.s([], 'id', '( %s -> N e. NN )' % A0)
    PN = '{ p e. Prime | p || N }'; SQ = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || N ) }'; DN = DIV('N')
    FM = '( n e. %s |-> { p e. Prime | p || n } )' % SQ; GM = '( m e. NN |-> ( q e. Prime |-> ( q pCnt m ) ) )'; GMP = '( m e. NN |-> ( p e. Prime |-> ( p pCnt m ) ) )'; GMN = '( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )'
    h1 = w.s([], 'eqid', '%s = %s' % (SQ, SQ)); h2 = w.s([], 'eqid', '%s = %s' % (FM, FM))
    # sqff1o carries $d n G and $d p G: name G with the binders m, q and identify it with the n, p form by cbvmptv
    ha = w.s([w.s([], 'oveq1', '( q = p -> ( q pCnt m ) = ( p pCnt m ) )')], 'cbvmptv', '( q e. Prime |-> ( q pCnt m ) ) = ( p e. Prime |-> ( p pCnt m ) )')
    hb = w.s([ha], 'mpteq2i', '%s = %s' % (GM, GMP))
    hc = w.s([w.s([w.s([], 'oveq2', '( m = n -> ( p pCnt m ) = ( p pCnt n ) )')], 'mpteq2dv', '( m = n -> ( p e. Prime |-> ( p pCnt m ) ) = ( p e. Prime |-> ( p pCnt n ) ) )')], 'cbvmptv', '%s = %s' % (GMP, GMN))
    h3 = w.s([hb, hc], 'eqtri', '%s = %s' % (GM, GMN))
    f1o = w.s([h1, h2, h3], 'sqff1o', '( %s -> %s : %s -1-1-onto-> ~P %s )' % (A0, FM, SQ, PN))
    Ad = '( %s /\\ d e. %s )' % (A0, SQ)
    idx = w.s([], 'id', '( x = d -> x = d )')
    st, bd = w.wcongr('( ( mmu ` x ) =/= 0 /\\ x || N )', {'x': 'd'}, 'x = d', {'x': idx})
    ers = w.s([st], 'elrab', '( d e. %s <-> ( d e. NN /\\ %s ) )' % (SQ, bd))
    ms = w.s([D(w, Ad, 'simpr', [], 'd e. %s' % SQ), w.s([ers], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ %s ) ) )' % (Ad, SQ, bd))], 'mpbid', '( %s -> ( d e. NN /\\ %s ) )' % (Ad, bd))
    dn = D(w, Ad, 'simpld', [ms], 'd e. NN'); pr = D(w, Ad, 'simprd', [ms], bd)
    ddv = D(w, Ad, 'simprd', [pr], 'd || N')
    erd = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || N ) )' % DN)
    mdk = w.s([w.s([dn, ddv], 'jca', '( %s -> ( d e. NN /\\ d || N ) )' % Ad), w.s([erd], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ d || N ) ) )' % (Ad, DN))], 'mpbird', '( %s -> d e. %s )' % (Ad, DN))
    ss = w.s([w.s([mdk], 'ex', '( %s -> ( d e. %s -> d e. %s ) )' % (A0, SQ, DN))], 'ssrdv', '( %s -> %s C_ %s )' % (A0, SQ, DN))
    finD = divfin(w, A0, nn, 'N')
    finS = w.s([finD, ss, w.inst('ssfi')], 'syl2anc', '( %s -> %s e. Fin )' % (A0, SQ))
    # step 1
    Ak = '( %s /\\ d e. %s )' % (A0, DN)
    dn2, ddv2, _ = eldiv(w, Ak, 'N', D(w, Ak, 'simpr', [], 'd e. %s' % DN))
    ma = w.s([dn2, w.inst('zl2muabs')], 'syl', '( %s -> ( abs ` ( mmu ` d ) ) = if ( ( mmu ` d ) =/= 0 , 1 , 0 ) )' % Ak)
    bt1 = w.s([ddv2], 'biantrud', '( %s -> ( ( mmu ` d ) =/= 0 <-> %s ) )' % (Ak, bd))
    bt2 = w.s([dn2], 'biantrurd', '( %s -> ( %s <-> ( d e. NN /\\ %s ) ) )' % (Ak, bd, bd))
    bt = w.s([w.s([bt1, bt2], 'bitrd', '( %s -> ( ( mmu ` d ) =/= 0 <-> ( d e. NN /\\ %s ) ) )' % (Ak, bd)), w.s([ers], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ %s ) ) )' % (Ak, SQ, bd))], 'bitr4d',
             '( %s -> ( ( mmu ` d ) =/= 0 <-> d e. %s ) )' % (Ak, SQ))
    ifb = w.s([bt], 'ifbid', '( %s -> if ( ( mmu ` d ) =/= 0 , 1 , 0 ) = if ( d e. %s , 1 , 0 ) )' % (Ak, SQ))
    t1 = w.s([ma, ifb], 'eqtrd', '( %s -> ( abs ` ( mmu ` d ) ) = if ( d e. %s , 1 , 0 ) )' % (Ak, SQ))
    s1 = w.s([t1], 'sumeq2dv', '( %s -> sum_ d e. %s ( abs ` ( mmu ` d ) ) = sum_ d e. %s if ( d e. %s , 1 , 0 ) )' % (A0, DN, DN, SQ))
    # step 2
    ral1 = w.s([a1(w, Ad, 'ax-1cn', '1 e. CC')], 'ralrimiva', '( %s -> A. d e. %s 1 e. CC )' % (A0, SQ))
    s2 = w.s([w.s([ss, ral1], 'jca', '( %s -> ( %s C_ %s /\\ A. d e. %s 1 e. CC ) )' % (A0, SQ, DN, SQ)), w.s([finD], 'olcd', '( %s -> ( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin ) )' % (A0, DN, DN)), w.inst('sumss2')], 'syl2anc',
             '( %s -> sum_ d e. %s 1 = sum_ d e. %s if ( d e. %s , 1 , 0 ) )' % (A0, SQ, DN, SQ))
    # step 3
    s3 = w.s([finS, a1(w, A0, 'ax-1cn', '1 e. CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ d e. %s 1 = ( ( # ` %s ) x. 1 ) )' % (A0, SQ, SQ))
    s3b = D(w, A0, 'mulridd', [D(w, A0, 'nn0cnd', [w.s([finS, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A0, SQ))], '( # ` %s ) e. CC' % SQ)], '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (SQ, SQ))
    # step 4
    s4 = w.s([finS, f1o], 'hasheqf1od', '( %s -> ( # ` %s ) = ( # ` ~P %s ) )' % (A0, SQ, PN))
    s5 = w.s([w.s([nn, w.inst('prmdvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A0, PN)), w.inst('hashpw')], 'syl', '( %s -> ( # ` ~P %s ) = ( 2 ^ ( # ` %s ) ) )' % (A0, PN, PN))
    r = chain(w, A0, ['sum_ d e. %s ( abs ` ( mmu ` d ) )' % DN, 'sum_ d e. %s if ( d e. %s , 1 , 0 )' % (DN, SQ), 'sum_ d e. %s 1' % SQ, '( ( # ` %s ) x. 1 )' % SQ, '( # ` %s )' % SQ, '( # ` ~P %s )' % PN, OMGN],
              [s1, ('r', s2), s3, s3b, s4, s5])
    w.lines[-1] = w.lines[-1].replace(r + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2dpb
if __name__ == '__main__' and (not only or 'zl2dpb' in only):
    w = W('zl2dpb', 'The Euler-factor polynomial is bounded by ` 2 ^ omega ( N ) ` on ` 0 <_ Re S ` ( ~ fsumabs , ~ zl2sqfc ; Lean ` norm_prod_euler_factors_le ` ).')
    A0 = '( %s /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) )' % NXL
    nx = D(w, A0, 'simpl', [], NXL); ss = D(w, A0, 'simpr', [], '( S e. CC /\\ 0 <_ ( Re ` S ) )')
    sc = D(w, A0, 'simpld', [ss], 'S e. CC'); s0 = D(w, A0, 'simprd', [ss], '0 <_ ( Re ` S )')
    nn = D(w, A0, 'simpld', [nx], 'N e. NN')
    nxs, mn, yb = nxm(w, A0, nx)
    cyf, cyb, _ = cyfun(w, A0, nxs)
    DN = DIV('N')
    finD = divfin(w, A0, nn, 'N')
    Ad = '( %s /\\ d e. %s )' % (A0, DN)
    dn, ddv, _ = eldiv(w, Ad, 'N', D(w, Ad, 'simpr', [], 'd e. %s' % DN))
    CD = '( %s ` d )' % CY; MQ = '( ( mmu ` d ) x. %s )' % CD; PD = '( d ^c -u S )'; TERM = '( %s x. %s )' % (MQ, PD)
    assert PFS('S') == 'sum_ d e. %s %s' % (DN, TERM)
    cdc = D(w, Ad, 'ffvelcdmd', [w.s([cyf], 'adantr', '( %s -> %s : NN --> CC )' % (Ad, CY)), dn], '%s e. CC' % CD)
    muc = muc_(w, Ad, dn)
    sca = w.s([sc], 'adantr', '( %s -> S e. CC )' % Ad); nsc = D(w, Ad, 'negcld', [sca], '-u S e. CC')
    drp = D(w, Ad, 'nnrpd', [dn], 'd e. RR+'); dr = D(w, Ad, 'nnred', [dn], 'd e. RR'); d1 = D(w, Ad, 'nnge1d', [dn], '1 <_ d')
    pc = D(w, Ad, 'cxpcld', [D(w, Ad, 'nncnd', [dn], 'd e. CC'), nsc], '%s e. CC' % PD)
    mqc = D(w, Ad, 'mulcld', [muc, cdc], '%s e. CC' % MQ)
    tc = D(w, Ad, 'mulcld', [mqc, pc], '%s e. CC' % TERM)
    fa = w.s([finD, tc], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ d e. %s ( abs ` %s ) )' % (A0, PFS('S'), DN, TERM))
    a1_ = D(w, Ad, 'absmuld', [mqc, pc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TERM, MQ, PD))
    a2 = D(w, Ad, 'absmuld', [muc, cdc], '( abs ` %s ) = ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) )' % (MQ, CD))
    cyb1, _ = inst_ral(w, Ad, w.s([cyb], 'adantr', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (Ad, CY)), 'm', 'NN', '( abs ` ( %s ` m ) ) <_ 1' % CY, 'd', dn)
    ax = w.s([drp, nsc, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( d ^c ( Re ` -u S ) ) )' % (Ad, PD))
    RS = '( Re ` S )'
    rsr = D(w, Ad, 'recld', [sca], '%s e. RR' % RS)
    ax2 = w.s([ax, E(w, Ad, 'oveq2d', [D(w, Ad, 'renegd', [sca], '( Re ` -u S ) = -u %s' % RS)], '( d ^c ( Re ` -u S ) )', '( d ^c -u %s )' % RS)], 'eqtrd', '( %s -> ( abs ` %s ) = ( d ^c -u %s ) )' % (Ad, PD, RS))
    nrs = D(w, Ad, 'renegcld', [rsr], '-u %s e. RR' % RS)
    le0 = linarith(w, Ad, [w.s([s0], 'adantr', '( %s -> 0 <_ %s )' % (Ad, RS))], '-u %s <_ 0' % RS, leaves={RS: rsr})
    le1 = D(w, Ad, 'cxplead', [dr, d1, nrs, a1(w, Ad, '0re', '0 e. RR'), le0], '( d ^c -u %s ) <_ ( d ^c 0 )' % RS)
    pl1 = w.s([le1, D(w, Ad, 'cxp0d', [D(w, Ad, 'nncnd', [dn], 'd e. CC')], '( d ^c 0 ) = 1')], 'breqtrd', '( %s -> ( d ^c -u %s ) <_ 1 )' % (Ad, RS))
    apl1 = w.s([ax2, pl1], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ 1 )' % (Ad, PD))
    amu = D(w, Ad, 'abscld', [muc], '( abs ` ( mmu ` d ) ) e. RR'); acy = D(w, Ad, 'abscld', [cdc], '( abs ` %s ) e. RR' % CD); apc = D(w, Ad, 'abscld', [pc], '( abs ` %s ) e. RR' % PD)
    amu0 = D(w, Ad, 'absge0d', [muc], '0 <_ ( abs ` ( mmu ` d ) )'); acy0 = D(w, Ad, 'absge0d', [cdc], '0 <_ ( abs ` %s )' % CD); apc0 = D(w, Ad, 'absge0d', [pc], '0 <_ ( abs ` %s )' % PD)
    one = a1(w, Ad, '1re', '1 e. RR')
    mA = D(w, Ad, 'lemul2ad', [acy, one, amu, amu0, cyb1], '( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) <_ ( ( abs ` ( mmu ` d ) ) x. 1 )' % CD)
    mA2 = w.s([mA, D(w, Ad, 'mulridd', [D(w, Ad, 'recnd', [amu], '( abs ` ( mmu ` d ) ) e. CC')], '( ( abs ` ( mmu ` d ) ) x. 1 ) = ( abs ` ( mmu ` d ) )')], 'breqtrd',
              '( %s -> ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) <_ ( abs ` ( mmu ` d ) ) )' % (Ad, CD))
    pr = D(w, Ad, 'remulcld', [amu, acy], '( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) e. RR' % CD)
    pr0 = D(w, Ad, 'mulge0d', [amu, acy, amu0, acy0], '0 <_ ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) )' % CD)
    mB = D(w, Ad, 'lemul12ad', [pr, amu, apc, one, pr0, apc0, mA2, apl1], '( ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) ) <_ ( ( abs ` ( mmu ` d ) ) x. 1 )' % (CD, PD))
    mB2 = w.s([mB, D(w, Ad, 'mulridd', [D(w, Ad, 'recnd', [amu], '( abs ` ( mmu ` d ) ) e. CC')], '( ( abs ` ( mmu ` d ) ) x. 1 ) = ( abs ` ( mmu ` d ) )')], 'breqtrd',
              '( %s -> ( ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) ) <_ ( abs ` ( mmu ` d ) ) )' % (Ad, CD, PD))
    tb0 = w.s([a1_, E(w, Ad, 'oveq1d', [a2], '( ( abs ` %s ) x. ( abs ` %s ) )' % (MQ, PD), '( ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) )' % (CD, PD))], 'eqtrd',
              '( %s -> ( abs ` %s ) = ( ( ( abs ` ( mmu ` d ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) ) )' % (Ad, TERM, CD, PD))
    tb = w.s([tb0, mB2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( abs ` ( mmu ` d ) ) )' % (Ad, TERM))
    atr = D(w, Ad, 'abscld', [tc], '( abs ` %s ) e. RR' % TERM)
    s2 = w.s([finD, atr, amu, tb], 'fsumle', '( %s -> sum_ d e. %s ( abs ` %s ) <_ sum_ d e. %s ( abs ` ( mmu ` d ) ) )' % (A0, DN, TERM, DN))
    s3 = w.s([nn, w.inst('zl2sqfc')], 'syl', '( %s -> sum_ d e. %s ( abs ` ( mmu ` d ) ) = %s )' % (A0, DN, OMGN))
    absr = D(w, A0, 'abscld', [w.s([finD, tc], 'fsumcl', '( %s -> %s e. CC )' % (A0, PFS('S')))], '( abs ` %s ) e. RR' % PFS('S'))
    r1 = D(w, A0, 'letrd', [absr, w.s([finD, atr], 'fsumrecl', '( %s -> sum_ d e. %s ( abs ` %s ) e. RR )' % (A0, DN, TERM)), w.s([finD, amu], 'fsumrecl', '( %s -> sum_ d e. %s ( abs ` ( mmu ` d ) ) e. RR )' % (A0, DN)), fa, s2],
           '( abs ` %s ) <_ sum_ d e. %s ( abs ` ( mmu ` d ) )' % (PFS('S'), DN))
    w.qed([r1, s3], 'breqtrd', STATEMENTS['zl2dpb'])
    go(w, only)


# ---------------------------------------------------------------- zl2dpv
if __name__ == '__main__' and (not only or 'zl2dpv' in only):
    w = W('zl2dpv', 'The value of the Euler-factor polynomial as a function ( ~ fvmptg ).')
    A0 = 'Z e. CC'
    e1 = w.s([], 'negeq', '( w = Z -> -u w = -u Z )')
    e2 = w.s([e1], 'oveq2d', '( w = Z -> ( d ^c -u w ) = ( d ^c -u Z ) )')
    B = lambda z: '( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u %s ) )' % (CY, z)
    e3 = w.s([e2], 'oveq2d', '( w = Z -> %s = %s )' % (B('w'), B('Z')))
    st = w.s([e3], 'sumeq2sdv', '( w = Z -> %s = %s )' % (PFS('w'), PFS('Z')))
    em = w.s([], 'eqid', '%s = %s' % (PF, PF))
    fm = w.s([st, em], 'fvmptg', '( ( Z e. CC /\\ %s e. _V ) -> ( %s ` Z ) = %s )' % (PFS('Z'), PF, PFS('Z')))
    ex = w.s([w.s([], 'sumex', '%s e. _V' % PFS('Z'))], 'a1i', '( %s -> %s e. _V )' % (A0, PFS('Z')))
    w.qed([w.s([], 'id', '( %s -> %s )' % (A0, A0)), ex, fm], 'syl2anc', STATEMENTS['zl2dpv'])
    go(w, only)


# ---------------------------------------------------------------- zl2dph
if __name__ == '__main__' and (not only or 'zl2dph' in only):
    w = W('zl2dph', 'The Euler-factor polynomial is entire ( ~ z6ehfs , ~ z6ehmulc , ~ z6ehx ).')
    A0 = NXL
    nx = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    nn = D(w, A0, 'simpld', [nx], 'N e. NN')
    nxs, mn, yb = nxm(w, A0, nx)
    cyf, cyb, _ = cyfun(w, A0, nxs)
    DN = DIV('N')
    finD = divfin(w, A0, nn, 'N')
    Ad = '( %s /\\ d e. %s )' % (A0, DN)
    dn, ddv, _ = eldiv(w, Ad, 'N', D(w, Ad, 'simpr', [], 'd e. %s' % DN))
    CD = '( %s ` d )' % CY; B = '( ( mmu ` d ) x. %s )' % CD
    cdc = D(w, Ad, 'ffvelcdmd', [w.s([cyf], 'adantr', '( %s -> %s : NN --> CC )' % (Ad, CY)), dn], '%s e. CC' % CD)
    bc = D(w, Ad, 'mulcld', [muc_(w, Ad, dn), cdc], '%s e. CC' % B)
    M1 = '( w e. CC |-> %s )' % B; M2 = '( w e. CC |-> ( d ^c -u w ) )'; M3 = '( w e. CC |-> ( %s x. ( d ^c -u w ) ) )' % B
    h1 = w.s([bc], 'z6ehc', '( %s -> %s )' % (Ad, HOL(M1, 'CC')))
    h2 = w.s([D(w, Ad, 'nnrpd', [dn], 'd e. RR+'), w.inst('z6ehx')], 'syl', '( %s -> %s )' % (Ad, HOL(M2, 'CC')))
    h3 = w.s([h1, h2, w.inst('z6ehmulc')], 'syl2anc', '( %s -> %s )' % (Ad, HOL(M3, 'CC')))
    w.qed([finD, h3], 'z6ehfs', STATEMENTS['zl2dph'])
    go(w, only)


# ================================================================== the L-function identity on the strip
HOL3 = '( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U )' % STR
GRW = GRWB('F', STR)
TQ1 = '( T e. CC /\\ ( abs ` T ) = 1 )'


def pcparts(w, A, pc):
    """the parts of PCONT from pc: ( A -> PCONT )"""
    r = {}
    p1 = D(w, A, 'simpld', [pc], '( %s /\\ %s )' % (HOL3, GRW)); p2 = D(w, A, 'simprd', [pc], '( %s /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (SERY, TQ1, FEY, QBND))
    r['hol3'] = D(w, A, 'simpld', [p1], HOL3); r['grw'] = D(w, A, 'simprd', [p1], GRW)
    r['fcn'] = D(w, A, 'simp1d', [r['hol3']], 'F e. ( U -cn-> CC )'); r['fdm'] = D(w, A, 'simp2d', [r['hol3']], 'U C_ dom ( CC _D F )'); r['stru'] = D(w, A, 'simp3d', [r['hol3']], '%s C_ U' % STR)
    r['sery'] = D(w, A, 'simpld', [p2], SERY)
    p3 = D(w, A, 'simprd', [p2], '( %s /\\ ( %s /\\ %s ) )' % (TQ1, FEY, QBND))
    r['tq'] = D(w, A, 'simpld', [p3], TQ1)
    p4 = D(w, A, 'simprd', [p3], '( %s /\\ %s )' % (FEY, QBND))
    r['fey'] = D(w, A, 'simpld', [p4], FEY); r['qbnd'] = D(w, A, 'simprd', [p4], QBND)
    r['ff'] = w.s([r['fcn'], w.inst('cncff')], 'syl', '( %s -> F : U --> CC )' % A)
    r['holF'] = w.s([r['fcn'], r['fdm']], 'jca', '( %s -> %s )' % (A, HOL('F', 'U')))
    return r


def instr(w, A, S, sc, lo, hi, stru, ff):
    """( A -> ( F ` S ) e. CC ) from lo: -u ( 1 / 2 ) <_ Re S, hi: Re S <_ 2; also returns S e. STR, S e. U"""
    RS = '( Re ` %s )' % S
    rsr = D(w, A, 'recld', [sc], '%s e. RR' % RS)
    nh = w.s([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'renegcli', '-u ( 1 / 2 ) e. RR')], 'a1i', '( %s -> -u ( 1 / 2 ) e. RR )' % A)
    ric = w.s([w.s([rsr, lo, hi], '3jca', '( %s -> ( %s e. RR /\\ -u ( 1 / 2 ) <_ %s /\\ %s <_ 2 ) )' % (A, RS, RS, RS)),
               w.s([nh, a1(w, A, '2re', '2 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( -u ( 1 / 2 ) [,] 2 ) <-> ( %s e. RR /\\ -u ( 1 / 2 ) <_ %s /\\ %s <_ 2 ) ) )' % (A, RS, RS, RS, RS))],
              'mpbird', '( %s -> %s e. ( -u ( 1 / 2 ) [,] 2 ) )' % (A, RS))
    sst = w.s([w.s([sc, ric], 'jca', '( %s -> ( %s e. CC /\\ %s e. ( -u ( 1 / 2 ) [,] 2 ) ) )' % (A, S, RS)), w.s([], 'elstr', '( %s e. %s <-> ( %s e. CC /\\ %s e. ( -u ( 1 / 2 ) [,] 2 ) ) )' % (S, STR, S, RS))], 'sylibr',
              '( %s -> %s e. %s )' % (A, S, STR))
    su = D(w, A, 'sseldd', [stru, sst], '%s e. U' % S)
    return D(w, A, 'ffvelcdmd', [ff, su], '( F ` %s ) e. CC' % S), sst, su


def rpcl(w, A):
    """( A -> RP e. CC )"""
    return w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'ifcli', '%s e. CC' % RP)], 'a1i', '( %s -> %s e. CC )' % (A, RP))


def rpabs1(w, A):
    """( A -> ( abs ` RP ) <_ 1 )"""
    ONE = '( 0g ` ( DChr ` N ) )'
    t1 = w.s([], 'iftrue', '( X = %s -> %s = 1 )' % (ONE, RP))
    t2 = w.s([w.s([t1], 'fveq2d', '( X = %s -> ( abs ` %s ) = ( abs ` 1 ) )' % (ONE, RP)), w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtrdi', '( X = %s -> ( abs ` %s ) = 1 )' % (ONE, RP))
    t3 = w.s([t2, w.s([], '1le1', '1 <_ 1')], 'eqbrtrdi', '( X = %s -> ( abs ` %s ) <_ 1 )' % (ONE, RP))
    f1 = w.s([], 'iffalse', '( -. X = %s -> %s = 0 )' % (ONE, RP))
    f2 = w.s([w.s([f1], 'fveq2d', '( -. X = %s -> ( abs ` %s ) = ( abs ` 0 ) )' % (ONE, RP)), w.s([], 'abs0', '( abs ` 0 ) = 0')], 'eqtrdi', '( -. X = %s -> ( abs ` %s ) = 0 )' % (ONE, RP))
    f3 = w.s([f2, w.s([], '0le1', '0 <_ 1')], 'eqbrtrdi', '( -. X = %s -> ( abs ` %s ) <_ 1 )' % (ONE, RP))
    return w.s([w.s([t3, f3], 'pm2.61i', '( abs ` %s ) <_ 1' % RP)], 'a1i', '( %s -> ( abs ` %s ) <_ 1 )' % (A, RP))


def sne1(w, A, S, sc, rsne):
    """( A -> S =/= 1 ) from rsne: ( A -> ( Re ` S ) =/= 1 )"""
    st1 = w.s([], 'fveq2', '( %s = 1 -> ( Re ` %s ) = ( Re ` 1 ) )' % (S, S))
    st2 = w.s([st1], 'necon3i', '( ( Re ` %s ) =/= ( Re ` 1 ) -> %s =/= 1 )' % (S, S))
    r1 = w.s([rsne, a1(w, A, 're1', '( Re ` 1 ) = 1')], 'neeqtrrd', '( %s -> ( Re ` %s ) =/= ( Re ` 1 ) )' % (A, S))
    return w.s([r1, st2], 'syl', '( %s -> %s =/= 1 )' % (A, S))


def hpmem(w, A, S, sc, s0):
    """( A -> S e. HPZ ) from s0: ( A -> 0 < ( Re ` S ) )"""
    bi = w.s([a1(w, A, '0re', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (A, S, HPZ, S, S))
    return w.s([w.s([sc, s0], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (A, S, S)), bi], 'mpbird', '( %s -> %s e. %s )' % (A, S, HPZ))


# ---------------------------------------------------------------- zl2lfe1
if __name__ == '__main__' and (not only or 'zl2lfe1' in only):
    w = W('zl2lfe1', 'The L-function of ` chi ` is the product of the primitive continuation and the Euler-factor polynomial on ` 1 < Re S <_ 2 ` '
          '( ~ zl1dser , ~ zl2dsp , ~ zl2dpf , SERY; Lean ` LFunction_eq_primitive_mul_prod ` on the series ).')
    A0 = '( %s /\\ ( S e. CC /\\ ( 1 < ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) ) )' % NXP
    nxp = D(w, A0, 'simpl', [], NXP); ss = D(w, A0, 'simpr', [], '( S e. CC /\\ ( 1 < ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) )')
    nx = D(w, A0, 'simpld', [nxp], NXL); pc = D(w, A0, 'simprd', [nxp], PCONT)
    sc = D(w, A0, 'simpld', [ss], 'S e. CC'); sb = D(w, A0, 'simprd', [ss], '( 1 < ( Re ` S ) /\\ ( Re ` S ) <_ 2 )')
    s1 = D(w, A0, 'simpld', [sb], '1 < ( Re ` S )'); s2 = D(w, A0, 'simprd', [sb], '( Re ` S ) <_ 2')
    RS = '( Re ` S )'
    rsr = D(w, A0, 'recld', [sc], '%s e. RR' % RS)
    P = pcparts(w, A0, pc)
    s0 = linarith(w, A0, [s1], '0 < %s' % RS, leaves={RS: rsr})
    lo = linarith(w, A0, [s1], '-u ( 1 / 2 ) <_ %s' % RS, leaves={RS: rsr})
    shp = hpmem(w, A0, 'S', sc, s0)
    dser = w.s([nx, w.inst('zl1dser')], 'syl', '( %s -> %s )' % (A0, ZL1.DSERX))
    DB = ZL1.DSERX[len('A. s e. %s ' % HPZ):]
    d1, _ = inst_ral(w, A0, dser, 's', HPZ, DB, 'S', shp)
    S1 = DS(CXN, 'S'); DAF = DS(AF, 'S'); DCY = DS(CY, 'S')
    e1 = w.s([s1, d1], 'mpd', '( %s -> ( %s ` S ) = ( ( S - 1 ) x. %s ) )' % (A0, LF, S1))
    dsp = w.s([nx, w.s([sc, s1], 'jca', '( %s -> ( S e. CC /\\ 1 < ( Re ` S ) ) )' % A0), w.inst('zl2dsp')], 'syl2anc', '( %s -> %s = ( %s x. %s ) )' % (A0, S1, DAF, DCY))
    dpf = w.s([nx, sc, w.inst('zl2dpf')], 'syl2anc', '( %s -> %s = %s )' % (A0, DAF, PFS('S')))
    dpv = w.s([sc, w.inst('zl2dpv')], 'syl', '( %s -> ( %s ` S ) = %s )' % (A0, PF, PFS('S')))
    PS = '( %s ` S )' % PF; FS = '( F ` S )'; Sm = '( S - 1 )'; Q = '( %s / %s )' % (RP, Sm)
    e3a = w.s([dpf, dpv], 'eqtr4d', '( %s -> %s = %s )' % (A0, DAF, PS))
    sy, _ = inst_ral_t(w, A0, P['sery'], 'CC', SERY[len('A. z e. CC '):], 'S', sc)
    e3b = w.s([sb, sy], 'mpd', '( %s -> ( %s + %s ) = %s )' % (A0, FS, Q, DCY))
    e3 = w.s([e3a, w.s([e3b], 'eqcomd', '( %s -> %s = ( %s + %s ) )' % (A0, DCY, FS, Q))], 'oveq12d', '( %s -> ( %s x. %s ) = ( %s x. ( %s + %s ) ) )' % (A0, DAF, DCY, PS, FS, Q))
    smc = D(w, A0, 'subcld', [sc, a1(w, A0, 'ax-1cn', '1 e. CC')], '%s e. CC' % Sm)
    rsne = w.s([s1], 'gtned', '( %s -> %s =/= 1 )' % (A0, RS))
    sn1 = sne1(w, A0, 'S', sc, rsne)
    smne = D(w, A0, 'subne0d', [sc, a1(w, A0, 'ax-1cn', '1 e. CC'), sn1], '%s =/= 0' % Sm)
    rpc = rpcl(w, A0)
    qc = D(w, A0, 'divcld', [rpc, smc, smne], '%s e. CC' % Q)
    fsc, sst, su = instr(w, A0, 'S', sc, lo, s2, P['stru'], P['ff'])
    pff = w.s([D(w, A0, 'simpld', [w.s([nx, w.inst('zl2dph')], 'syl', '( %s -> %s )' % (A0, HOL(PF, 'CC')))], '%s e. ( CC -cn-> CC )' % PF), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (A0, PF))
    psc = D(w, A0, 'ffvelcdmd', [pff, sc], '%s e. CC' % PS)
    fqc = D(w, A0, 'addcld', [fsc, qc], '( %s + %s ) e. CC' % (FS, Q))
    e4a = D(w, A0, 'mul12d', [smc, psc, fqc], '( %s x. ( %s x. ( %s + %s ) ) ) = ( %s x. ( %s x. ( %s + %s ) ) )' % (Sm, PS, FS, Q, PS, Sm, FS, Q))
    e4b = D(w, A0, 'mulcomd', [psc, D(w, A0, 'mulcld', [smc, fqc], '( %s x. ( %s + %s ) ) e. CC' % (Sm, FS, Q))], '( %s x. ( %s x. ( %s + %s ) ) ) = ( ( %s x. ( %s + %s ) ) x. %s )' % (PS, Sm, FS, Q, Sm, FS, Q, PS))
    e5a = D(w, A0, 'adddid', [smc, fsc, qc], '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (Sm, FS, Q, Sm, FS, Sm, Q))
    e5b = D(w, A0, 'divcan2d', [rpc, smc, smne], '( %s x. %s ) = %s' % (Sm, Q, RP))
    e5 = w.s([e5a, E(w, A0, 'oveq2d', [e5b], '( ( %s x. %s ) + ( %s x. %s ) )' % (Sm, FS, Sm, Q), '( ( %s x. %s ) + %s )' % (Sm, FS, RP))], 'eqtrd', '( %s -> ( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + %s ) )' % (A0, Sm, FS, Q, Sm, FS, RP))
    e6 = E(w, A0, 'oveq1d', [e5], '( ( %s x. ( %s + %s ) ) x. %s )' % (Sm, FS, Q, PS), GPR('S'))
    terms = ['( %s ` S )' % LF, '( %s x. %s )' % (Sm, S1), '( %s x. ( %s x. %s ) )' % (Sm, DAF, DCY), '( %s x. ( %s x. ( %s + %s ) ) )' % (Sm, PS, FS, Q),
             '( %s x. ( %s x. ( %s + %s ) ) )' % (PS, Sm, FS, Q), '( ( %s x. ( %s + %s ) ) x. %s )' % (Sm, FS, Q, PS), GPR('S')]
    r = chain(w, A0, terms, [e1, E(w, A0, 'oveq2d', [dsp], terms[1], terms[2]), E(w, A0, 'oveq2d', [e3], terms[2], terms[3]), e4a, e4b, e6])
    w.lines[-1] = w.lines[-1].replace(r + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2lfh
if __name__ == '__main__' and (not only or 'zl2lfh' in only):
    w = W('zl2lfh', 'The difference ` L ( u , chi ) - ( ( u - 1 ) F ( u ) + R ) P ( u ) ` is holomorphic on ` U i^i HP 0 ` ( ~ zl2hres , ~ holmul , ~ zl2hadd , ~ zl2hsub , ~ zl1ehol , ~ zl2dph ).')
    A0 = NXP
    nx = D(w, A0, 'simpl', [], NXL); pc = D(w, A0, 'simpr', [], PCONT)
    P = pcparts(w, A0, pc)
    uo = w.s([P['holF'], w.inst('holopn')], 'syl', '( %s -> U e. %s )' % (A0, TOP))
    hpo = w.s([w.s([], 'hpopn', '%s e. %s' % (HPZ, TOP))], 'a1i', '( %s -> %s e. %s )' % (A0, HPZ, TOP))
    ct = w.s([w.s([w.s([], 'eqid', '%s = %s' % (TOP, TOP))], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
    ddo = w.s([ct, uo, hpo, w.inst('inopn')], 'syl3anc', '( %s -> %s e. %s )' % (A0, DD, TOP))
    ddu = w.s([w.s([], 'inss1', '%s C_ U' % DD)], 'a1i', '( %s -> %s C_ U )' % (A0, DD))
    ddh = w.s([w.s([], 'inss2', '%s C_ %s' % (DD, HPZ))], 'a1i', '( %s -> %s C_ %s )' % (A0, DD, HPZ))
    ddc = D(w, A0, 'sstrd', [ddh, w.s([w.s([], 'hpss', '%s C_ CC' % HPZ)], 'a1i', '( %s -> %s C_ CC )' % (A0, HPZ))], '%s C_ CC' % DD)
    ehol = w.s([nx, w.inst('zl1ehol')], 'syl', '( %s -> %s )' % (A0, HOL(LF, HPZ)))
    E1 = MP('z', DD, '( %s ` z )' % LF); F1 = MP('z', DD, '( F ` z )'); P1 = MP('z', DD, '( %s ` z )' % PF)
    hE1 = w.s([ehol, w.s([ddo, ddh], 'jca', '( %s -> ( %s e. %s /\\ %s C_ %s ) )' % (A0, DD, TOP, DD, HPZ)), w.inst('zl2hres')], 'syl2anc', '( %s -> %s )' % (A0, HOL(E1, DD)))
    hF1 = w.s([P['holF'], w.s([ddo, ddu], 'jca', '( %s -> ( %s e. %s /\\ %s C_ U ) )' % (A0, DD, TOP, DD)), w.inst('zl2hres')], 'syl2anc', '( %s -> %s )' % (A0, HOL(F1, DD)))
    pfh = w.s([nx, w.inst('zl2dph')], 'syl', '( %s -> %s )' % (A0, HOL(PF, 'CC')))
    hP1 = w.s([pfh, w.s([ddo, ddc], 'jca', '( %s -> ( %s e. %s /\\ %s C_ CC ) )' % (A0, DD, TOP, DD)), w.inst('zl2hres')], 'syl2anc', '( %s -> %s )' % (A0, HOL(P1, DD)))
    from zl2_p import ent_lin
    lin = ent_lin(w, A0, '1', a1(w, A0, 'ax-1cn', '1 e. CC'))
    cbv = w.s([w.s([], 'oveq1', '( t = z -> ( t - 1 ) = ( z - 1 ) )')], 'cbvmptv', '( t e. CC |-> ( t - 1 ) ) = ( z e. CC |-> ( z - 1 ) )')
    linz = holeq_(w, A0, '( t e. CC |-> ( t - 1 ) )', '( z e. CC |-> ( z - 1 ) )', 'CC', lin, w.s([cbv], 'a1i', '( %s -> ( t e. CC |-> ( t - 1 ) ) = ( z e. CC |-> ( z - 1 ) ) )' % A0))
    I1 = MP('z', DD, '( z - 1 )')
    hI1 = w.s([linz, ddo, w.inst('zl2hent')], 'syl2anc', '( %s -> %s )' % (A0, HOL(I1, DD)))
    rpc = rpcl(w, A0)
    C1 = MP('y', DD, RP)
    c1c = w.s([rpc], 'z6ehc', '( %s -> %s )' % (A0, HOL(MP('y', 'CC', RP), 'CC')))
    hC1 = w.s([c1c, ddo, w.inst('zl2hent')], 'syl2anc', '( %s -> %s )' % (A0, HOL(C1, DD)))
    # layer 2: M2 = ( y e. DD |-> ( ( y - 1 ) x. ( F ` y ) ) )
    Ay = '( %s /\\ y e. %s )' % (A0, DD); ym = D(w, Ay, 'simpr', [], 'y e. %s' % DD)
    M2o = MP('y', DD, '( ( %s ` y ) x. ( %s ` y ) )' % (I1, F1)); M2 = MP('y', DD, '( ( y - 1 ) x. ( F ` y ) )')
    m2a = w.s([hI1, hF1, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (A0, HOL(M2o, DD)))
    vI, _ = mptv(w, Ay, 'z', DD, '( z - 1 )', 'y', ym)
    vF, _ = mptv(w, Ay, 'z', DD, '( F ` z )', 'y', ym)
    eq2 = mpteq_(w, A0, 'y', DD, '( ( %s ` y ) x. ( %s ` y ) )' % (I1, F1), '( ( y - 1 ) x. ( F ` y ) )', w.s([vI, vF], 'oveq12d', '( %s -> ( ( %s ` y ) x. ( %s ` y ) ) = ( ( y - 1 ) x. ( F ` y ) ) )' % (Ay, I1, F1)))
    hM2 = holeq_(w, A0, M2o, M2, DD, m2a, eq2)
    # layer 3: A3 = ( v e. DD |-> ( ( ( v - 1 ) x. ( F ` v ) ) + RP ) ) (binder v: the antecedent binds z)
    Av = '( %s /\\ v e. %s )' % (A0, DD); vm = D(w, Av, 'simpr', [], 'v e. %s' % DD)
    A3o = MP('v', DD, '( ( %s ` v ) + ( %s ` v ) )' % (M2, C1)); A3 = MP('v', DD, '( ( ( v - 1 ) x. ( F ` v ) ) + %s )' % RP)
    a3a = w.s([hM2, hC1, w.inst('zl2hadd')], 'syl2anc', '( %s -> %s )' % (A0, HOL(A3o, DD)))
    vM, _ = mptv(w, Av, 'y', DD, '( ( y - 1 ) x. ( F ` y ) )', 'v', vm)
    rpv = w.s([w.s([rpc], 'adantr', '( %s -> %s e. CC )' % (Av, RP))], 'elexd', '( %s -> %s e. _V )' % (Av, RP))
    vC, _ = mptv(w, Av, 'y', DD, RP, 'v', vm, exs=rpv)
    eq3 = mpteq_(w, A0, 'v', DD, '( ( %s ` v ) + ( %s ` v ) )' % (M2, C1), '( ( ( v - 1 ) x. ( F ` v ) ) + %s )' % RP, w.s([vM, vC], 'oveq12d', '( %s -> ( ( %s ` v ) + ( %s ` v ) ) = ( ( ( v - 1 ) x. ( F ` v ) ) + %s ) )' % (Av, M2, C1, RP)))
    hA3 = holeq_(w, A0, A3o, A3, DD, a3a, eq3)
    # layer 4: G4 = ( y e. DD |-> GPR(y) )
    G4o = MP('y', DD, '( ( %s ` y ) x. ( %s ` y ) )' % (A3, P1)); G4 = MP('y', DD, GPR('y'))
    g4a = w.s([hA3, hP1, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (A0, HOL(G4o, DD)))
    vA, _ = mptv(w, Ay, 'v', DD, '( ( ( v - 1 ) x. ( F ` v ) ) + %s )' % RP, 'y', ym)
    vP, _ = mptv(w, Ay, 'z', DD, '( %s ` z )' % PF, 'y', ym)
    eq4 = mpteq_(w, A0, 'y', DD, '( ( %s ` y ) x. ( %s ` y ) )' % (A3, P1), GPR('y'), w.s([vA, vP], 'oveq12d', '( %s -> ( ( %s ` y ) x. ( %s ` y ) ) = %s )' % (Ay, A3, P1, GPR('y'))))
    hG4 = holeq_(w, A0, G4o, G4, DD, g4a, eq4)
    # layer 5: HH = ( u e. DD |-> ( ( LF ` u ) - GPR(u) ) )
    Au = '( %s /\\ u e. %s )' % (A0, DD); um = D(w, Au, 'simpr', [], 'u e. %s' % DD)
    H5o = MP('u', DD, '( ( %s ` u ) - ( %s ` u ) )' % (E1, G4))
    h5a = w.s([hE1, hG4, w.inst('zl2hsub')], 'syl2anc', '( %s -> %s )' % (A0, HOL(H5o, DD)))
    vE, _ = mptv(w, Au, 'z', DD, '( %s ` z )' % LF, 'u', um)
    vG, _ = mptv(w, Au, 'y', DD, GPR('y'), 'u', um)
    eq5 = mpteq_(w, A0, 'u', DD, '( ( %s ` u ) - ( %s ` u ) )' % (E1, G4), '( ( %s ` u ) - %s )' % (LF, GPR('u')), w.s([vE, vG], 'oveq12d', '( %s -> ( ( %s ` u ) - ( %s ` u ) ) = ( ( %s ` u ) - %s ) )' % (Au, E1, G4, LF, GPR('u'))))
    fin = holeq_(w, A0, H5o, HH, DD, h5a, eq5)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


def nnlit(w, digits):
    """closed step: the decimal numeral `digits` (no leading zero) e. NN"""
    if len(digits) == 1:
        return w.s([], '%snn' % digits, '%s e. NN' % digits)
    pre = digits[:-1]; last = digits[-1]
    txt = lambda d: (' '.join(['; '] * (len(d) - 1)) + ' '.join(d)).replace('  ', ' ').strip() if len(d) > 1 else d
    if last == '0':
        return w.s([nnlit(w, pre)], 'decnncl2', '%s e. NN' % num.nat_text(int(digits)))
    return w.s([nn0lit(w, pre), w.s([], '%snn' % last, '%s e. NN' % last)], 'decnncl', '%s e. NN' % num.nat_text(int(digits)))


def nn0lit(w, digits):
    if len(digits) == 1:
        return w.s([], '%snn0' % digits, '%s e. NN0' % digits)
    return w.s([nn0lit(w, digits[:-1]), w.s([], '%snn0' % digits[-1], '%s e. NN0' % digits[-1])], 'deccl', '%s e. NN0' % num.nat_text(int(digits)))


def rplit(w, A, digits):
    """( A -> NUM e. RR+ ) for a decimal numeral"""
    n = nnlit(w, digits)
    return w.s([w.s([n, w.s([], 'nnrp', '( %s e. NN -> %s e. RR+ )' % (num.nat_text(int(digits)), num.nat_text(int(digits))))], 'ax-mp', '%s e. RR+' % num.nat_text(int(digits)))], 'a1i',
               '( %s -> %s e. RR+ )' % (A, num.nat_text(int(digits))))


def recip(w, A, digits):
    """( A -> ( 1 / NUM ) e. RR+ ) and ( A -> ( 1 / NUM ) e. RR )"""
    rp = D(w, A, 'rpreccld', [rplit(w, A, digits)], '( 1 / %s ) e. RR+' % num.nat_text(int(digits)))
    return rp, D(w, A, 'rpred', [rp], '( 1 / %s ) e. RR' % num.nat_text(int(digits)))


def frac(w, A, p_, q_):
    """( A -> ( p / q ) e. RR ) for one-digit p, q"""
    return w.s([w.s([w.s([], '%sre' % p_, '%s e. RR' % p_), w.s([], '%sre' % q_, '%s e. RR' % q_), w.s([], '%sne0' % q_, '%s =/= 0' % q_)], 'redivcli', '( %s / %s ) e. RR' % (p_, q_))], 'a1i',
               '( %s -> ( %s / %s ) e. RR )' % (A, p_, q_))


def cxpt(w, A, X, Y, xr, yr):
    """the point ( X + ( _i x. Y ) ): (e. CC, Re = X, Im = Y)"""
    PT = '( %s + ( _i x. %s ) )' % (X, Y)
    c = D(w, A, 'addcld', [D(w, A, 'recnd', [xr], '%s e. CC' % X), D(w, A, 'mulcld', [a1(w, A, 'ax-icn', '_i e. CC'), D(w, A, 'recnd', [yr], '%s e. CC' % Y)], '( _i x. %s ) e. CC' % Y)], '%s e. CC' % PT)
    re = w.s([xr, yr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A, PT, X))
    im = w.s([xr, yr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A, PT, Y))
    return c, re, im


HHB = lambda u: '( ( %s ` %s ) - %s )' % (LF, u, GPR(u))


# ---------------------------------------------------------------- zl2lfrc
if __name__ == '__main__' and (not only or 'zl2lfrc' in only):
    w = W('zl2lfrc', 'The identity-theorem rectangle ` [ 1/200 , 3/2 ] x [ -( V + 1 ) , V + 1 ] ` fattened by ` 1/400 ` lies in ` U i^i HP 0 ` ( ~ crectss2 , ~ crectstr ).')
    A0 = '( %s /\\ ( V e. RR /\\ 0 <_ V ) )' % NXP
    nxp = D(w, A0, 'simpl', [], NXP); vv = D(w, A0, 'simpr', [], '( V e. RR /\\ 0 <_ V )')
    vr = D(w, A0, 'simpld', [vv], 'V e. RR'); v0 = D(w, A0, 'simprd', [vv], '0 <_ V')
    pc = D(w, A0, 'simprd', [nxp], PCONT); P = pcparts(w, A0, pc)
    A_ = RCA('V'); B_ = RCB('V'); RIQ = '( %s + ( _i x. %s ) )' % (RQ, RQ)
    CA = '( %s - %s )' % (A_, RIQ); CB = '( %s + %s )' % (B_, RIQ)
    X1 = RQ; Y1 = '( ( 3 / 2 ) + %s )' % RQ; T1 = '( V + 2 )'
    A2 = '( %s + ( _i x. -u %s ) )' % (X1, T1); B2 = '( %s + ( _i x. %s ) )' % (Y1, T1)
    rqrp, rqr = recip(w, A0, '400'); r2rp, r2r = recip(w, A0, '200')
    r32 = frac(w, A0, '3', '2')
    v1r = D(w, A0, 'readdcld', [vr, a1(w, A0, '1re', '1 e. RR')], '( V + 1 ) e. RR'); nv1r = D(w, A0, 'renegcld', [v1r], '-u ( V + 1 ) e. RR')
    t1r = D(w, A0, 'readdcld', [vr, a1(w, A0, '2re', '2 e. RR')], '%s e. RR' % T1); nt1r = D(w, A0, 'renegcld', [t1r], '-u %s e. RR' % T1)
    y1r = D(w, A0, 'readdcld', [r32, rqr], '%s e. RR' % Y1)
    ac, rea, ima = cxpt(w, A0, '( 1 / ; ; 2 0 0 )', '-u ( V + 1 )', r2r, nv1r)
    bc, reb, imb = cxpt(w, A0, '( 3 / 2 )', '( V + 1 )', r32, v1r)
    qc, req, imq = cxpt(w, A0, RQ, RQ, rqr, rqr)
    a2c, rea2, ima2 = cxpt(w, A0, X1, '-u %s' % T1, rqr, nt1r)
    b2c, reb2, imb2 = cxpt(w, A0, Y1, T1, y1r, t1r)
    cac = D(w, A0, 'subcld', [ac, qc], '%s e. CC' % CA); cbc = D(w, A0, 'addcld', [bc, qc], '%s e. CC' % CB)
    reca = w.s([D(w, A0, 'resubd', [ac, qc], '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (CA, A_, RIQ)), w.s([rea, req], 'oveq12d', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) = ( ( 1 / ; ; 2 0 0 ) - %s ) )' % (A0, A_, RIQ, RQ))], 'eqtrd',
              '( %s -> ( Re ` %s ) = ( ( 1 / ; ; 2 0 0 ) - %s ) )' % (A0, CA, RQ))
    imca = w.s([D(w, A0, 'imsubd', [ac, qc], '( Im ` %s ) = ( ( Im ` %s ) - ( Im ` %s ) )' % (CA, A_, RIQ)), w.s([ima, imq], 'oveq12d', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) = ( -u ( V + 1 ) - %s ) )' % (A0, A_, RIQ, RQ))], 'eqtrd',
              '( %s -> ( Im ` %s ) = ( -u ( V + 1 ) - %s ) )' % (A0, CA, RQ))
    recb = w.s([D(w, A0, 'readdd', [bc, qc], '( Re ` %s ) = ( ( Re ` %s ) + ( Re ` %s ) )' % (CB, B_, RIQ)), w.s([reb, req], 'oveq12d', '( %s -> ( ( Re ` %s ) + ( Re ` %s ) ) = ( ( 3 / 2 ) + %s ) )' % (A0, B_, RIQ, RQ))], 'eqtrd',
              '( %s -> ( Re ` %s ) = ( ( 3 / 2 ) + %s ) )' % (A0, CB, RQ))
    imcb = w.s([D(w, A0, 'imaddd', [bc, qc], '( Im ` %s ) = ( ( Im ` %s ) + ( Im ` %s ) )' % (CB, B_, RIQ)), w.s([imb, imq], 'oveq12d', '( %s -> ( ( Im ` %s ) + ( Im ` %s ) ) = ( ( V + 1 ) + %s ) )' % (A0, B_, RIQ, RQ))], 'eqtrd',
              '( %s -> ( Im ` %s ) = ( ( V + 1 ) + %s ) )' % (A0, CB, RQ))
    cl = Closure(w, A0, {'V': ('RR', vr), RQ: ('RR', rqr), '( 1 / ; ; 2 0 0 )': ('RR', r2r)}); cl.atom(RQ); cl.atom('( 1 / ; ; 2 0 0 )')
    # numeric facts about the two reciprocals: 1/400 + 1/400 = 1/200 (2 x. 1/400 = 1/200)
    # ( 1 / 200 ) = ( 2 / 400 ) = 2 x. ( 1 / 400 ): via num.mul_lits: ( 2 x. ( 1 / 400 ) ) = ( 1 / 200 )
    ml = num.mul_lits(w, '2', '( 1 / ; ; 4 0 0 )')
    mle = w.s([ml], 'a1i', '( %s -> ( 2 x. ( 1 / ; ; 4 0 0 ) ) = ( 1 / ; ; 2 0 0 ) )' % A0)
    i1 = linarith(w, A0, [mle], '%s <_ ( ( 1 / ; ; 2 0 0 ) - %s )' % (X1, RQ), closure=cl)
    i2 = linarith(w, A0, [], '( ( 3 / 2 ) + %s ) <_ %s' % (RQ, Y1), closure=cl)
    rq0 = D(w, A0, 'rpge0d', [rqrp], '0 <_ %s' % RQ)
    rq1b = num.le_lit(w, RQ, '1')
    rq1c = w.s([rq1b], 'a1i', '( %s -> %s <_ 1 )' % (A0, RQ))
    i3 = linarith(w, A0, [rq0, rq1c], '-u %s <_ ( -u ( V + 1 ) - %s )' % (T1, RQ), closure=cl)
    i4 = linarith(w, A0, [rq0, rq1c], '( ( V + 1 ) + %s ) <_ %s' % (RQ, T1), closure=cl)
    j1 = w.s([w.s([rea2, i1], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ ( ( 1 / ; ; 2 0 0 ) - %s ) )' % (A0, A2, RQ)), reca], 'breqtrrd', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, A2, CA))
    j2 = w.s([w.s([recb, i2], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ %s )' % (A0, CB, Y1)), reb2], 'breqtrrd', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, CB, B2))
    j3 = w.s([w.s([ima2, i3], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ ( -u ( V + 1 ) - %s ) )' % (A0, A2, RQ)), imca], 'breqtrrd', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, A2, CA))
    j4 = w.s([w.s([imcb, i4], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ %s )' % (A0, CB, T1)), imb2], 'breqtrrd', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, CB, B2))
    ss1 = w.s([w.s([a2c, b2c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A2, B2)), w.s([cac, cbc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CA, CB)),
               w.s([w.s([j1, j2], 'jca', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) ) )' % (A0, A2, CA, CB, B2)), w.s([j3, j4], 'jca', '( %s -> ( ( Im ` %s ) <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, A2, CA, CB, B2))], 'jca',
                   '( %s -> ( ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) ) /\\ ( ( Im ` %s ) <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) ) )' % (A0, A2, CA, CB, B2, A2, CA, CB, B2)),
               w.inst('crectss2')], 'syl3anc', '( %s -> ( %s crect %s ) C_ ( %s crect %s ) )' % (A0, CA, CB, A2, B2))
    STQ = STRIP(X1, Y1)
    st_ = w.s([rqr, y1r, t1r, w.inst('crectstr')], 'syl3anc', '( %s -> ( %s crect %s ) C_ %s )' % (A0, A2, B2, STQ))
    ss2 = D(w, A0, 'sstrd', [ss1, st_], '( %s crect %s ) C_ %s' % (CA, CB, STQ))
    # the strip lies in U i^i HP 0
    Az = '( %s /\\ t e. %s )' % (A0, STQ)
    zs = D(w, Az, 'simpr', [], 't e. %s' % STQ)
    zc, zr, lo, hi = strip_mem(w, Az, 't', zs, w.s([rqr], 'adantr', '( %s -> %s e. RR )' % (Az, RQ)), w.s([y1r], 'adantr', '( %s -> %s e. RR )' % (Az, Y1)), X=X1, Y=Y1)
    clz = Closure(w, Az, {'( Re ` t )': ('RR', zr), RQ: ('RR', w.s([rqr], 'adantr', '( %s -> %s e. RR )' % (Az, RQ)))}); clz.atom(RQ)
    rq0z = w.s([rq0], 'adantr', '( %s -> 0 <_ %s )' % (Az, RQ)); rq1z = w.s([rq1c], 'adantr', '( %s -> %s <_ 1 )' % (Az, RQ))
    lo2 = linarith(w, Az, [lo, rq0z], '-u ( 1 / 2 ) <_ ( Re ` t )', closure=clz)
    hi2 = linarith(w, Az, [hi, rq1z], '( Re ` t ) <_ 2', closure=clz)
    z0 = linarith(w, Az, [lo, D(w, Az, 'rpgt0d', [w.s([rqrp], 'adantr', '( %s -> %s e. RR+ )' % (Az, RQ))], '0 < %s' % RQ)], '0 < ( Re ` t )', closure=clz)
    fzc, zstr, zu = instr(w, Az, 't', zc, lo2, hi2, w.s([P['stru']], 'adantr', '( %s -> %s C_ U )' % (Az, STR)), w.s([P['ff']], 'adantr', '( %s -> F : U --> CC )' % Az))
    zhp = hpmem(w, Az, 't', zc, z0)
    zdd = D(w, Az, 'elind', [zu, zhp], 't e. %s' % DD)
    ss3 = w.s([w.s([zdd], 'ex', '( %s -> ( t e. %s -> t e. %s ) )' % (A0, STQ, DD))], 'ssrdv', '( %s -> %s C_ %s )' % (A0, STQ, DD))
    w.qed([ss2, ss3], 'sstrd', STATEMENTS['zl2lfrc'])
    go(w, only)


# ---------------------------------------------------------------- zl2lfnb
if __name__ == '__main__' and (not only or 'zl2lfnb' in only):
    w = W('zl2lfnb', 'The difference ` L ( v , chi ) - ( ( v - 1 ) F ( v ) + R ) P ( v ) ` vanishes on the disc of radius ` 1/8 ` about ` 5/4 ` ( ~ zl2lfe1 ).')
    A0 = NXP
    nx = D(w, A0, 'simpl', [], NXL); pc = D(w, A0, 'simpr', [], PCONT); P = pcparts(w, A0, pc)
    E8 = '( 1 / 8 )'
    Av0 = '( %s /\\ v e. %s )' % (A0, DD); Av = '( %s /\\ ( abs ` ( v - %s ) ) < %s )' % (Av0, X54, E8)
    vdd = D(w, Av, 'simplr', [], 'v e. %s' % DD); nxp = D(w, Av, 'simpll', [], NXP); lt = D(w, Av, 'simpr', [], '( abs ` ( v - %s ) ) < %s' % (X54, E8))
    nxv = D(w, Av, 'simpld', [nxp], NXL); pcv = D(w, Av, 'simprd', [nxp], PCONT); Pv = pcparts(w, Av, pcv)
    vu = D(w, Av, 'sseldd', [w.s([w.s([], 'inss1', '%s C_ U' % DD)], 'a1i', '( %s -> %s C_ U )' % (Av, DD)), vdd], 'v e. U')
    vhp = D(w, Av, 'sseldd', [w.s([w.s([], 'inss2', '%s C_ %s' % (DD, HPZ))], 'a1i', '( %s -> %s C_ %s )' % (Av, DD, HPZ)), vdd], 'v e. %s' % HPZ)
    hb = w.s([vhp, w.s([a1(w, Av, '0re', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s -> ( v e. %s <-> ( v e. CC /\\ 0 < ( Re ` v ) ) ) )' % (Av, HPZ))], 'mpbid', '( %s -> ( v e. CC /\\ 0 < ( Re ` v ) ) )' % Av)
    vc = D(w, Av, 'simpld', [hb], 'v e. CC')
    x54r = frac(w, Av, '5', '4'); x54c = D(w, Av, 'recnd', [x54r], '%s e. CC' % X54)
    RV = '( Re ` v )'; rvr = D(w, Av, 'recld', [vc], '%s e. RR' % RV)
    DF = '( v - %s )' % X54; dc = D(w, Av, 'subcld', [vc, x54c], '%s e. CC' % DF)
    r1 = D(w, Av, 'resubd', [vc, x54c], '( Re ` %s ) = ( %s - ( Re ` %s ) )' % (DF, RV, X54))
    r2 = w.s([r1, E(w, Av, 'oveq2d', [D(w, Av, 'rered', [x54r], '( Re ` %s ) = %s' % (X54, X54))], '( %s - ( Re ` %s ) )' % (RV, X54), '( %s - %s )' % (RV, X54))], 'eqtrd', '( %s -> ( Re ` %s ) = ( %s - %s ) )' % (Av, DF, RV, X54))
    ab = w.s([dc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` %s ) ) <_ ( abs ` %s ) )' % (Av, DF, DF))
    RD = '( %s - %s )' % (RV, X54); rdr = D(w, Av, 'resubcld', [rvr, x54r], '%s e. RR' % RD)
    _, e8r = recip(w, Av, '8')
    ab2 = w.s([E(w, Av, 'fveq2d', [r2], '( abs ` ( Re ` %s ) )' % DF, '( abs ` %s )' % RD), ab], 'eqbrtrrd', '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (Av, RD, DF))
    lt2 = D(w, Av, 'lelttrd', [D(w, Av, 'abscld', [D(w, Av, 'recnd', [rdr], '%s e. CC' % RD)], '( abs ` %s ) e. RR' % RD), D(w, Av, 'abscld', [dc], '( abs ` %s ) e. RR' % DF), e8r, ab2, lt], '( abs ` %s ) < %s' % (RD, E8))
    bi = w.s([rdr, e8r, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` %s ) < %s <-> ( -u %s < %s /\\ %s < %s ) ) )' % (Av, RD, E8, E8, RD, RD, E8))
    both = w.s([lt2, bi], 'mpbid', '( %s -> ( -u %s < %s /\\ %s < %s ) )' % (Av, E8, RD, RD, E8))
    bl = D(w, Av, 'simpld', [both], '-u %s < %s' % (E8, RD)); bu = D(w, Av, 'simprd', [both], '%s < %s' % (RD, E8))
    cl = Closure(w, Av, {RV: ('RR', rvr)})
    s1 = linarith(w, Av, [bl], '1 < %s' % RV, closure=cl); s2 = linarith(w, Av, [bu], '%s <_ 2' % RV, closure=cl)
    lfe1 = w.s([nxp, w.s([vc, w.s([s1, s2], 'jca', '( %s -> ( 1 < %s /\\ %s <_ 2 ) )' % (Av, RV, RV))], 'jca', '( %s -> ( v e. CC /\\ ( 1 < %s /\\ %s <_ 2 ) ) )' % (Av, RV, RV)), w.inst('zl2lfe1')], 'syl2anc',
               '( %s -> ( %s ` v ) = %s )' % (Av, LF, GPR('v')))
    val, _ = mptv(w, Av, 'u', DD, HHB('u'), 'v', vdd)
    lff = w.s([D(w, Av, 'simpld', [w.s([nxv, w.inst('zl1ehol')], 'syl', '( %s -> %s )' % (Av, HOL(LF, HPZ)))], '%s e. ( %s -cn-> CC )' % (LF, HPZ)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Av, LF, HPZ))
    lfc = D(w, Av, 'ffvelcdmd', [lff, vhp], '( %s ` v ) e. CC' % LF)
    pff = w.s([D(w, Av, 'simpld', [w.s([nxv, w.inst('zl2dph')], 'syl', '( %s -> %s )' % (Av, HOL(PF, 'CC')))], '%s e. ( CC -cn-> CC )' % PF), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (Av, PF))
    psc = D(w, Av, 'ffvelcdmd', [pff, vc], '( %s ` v ) e. CC' % PF)
    fvc = D(w, Av, 'ffvelcdmd', [Pv['ff'], vu], '( F ` v ) e. CC')
    gc = D(w, Av, 'mulcld', [D(w, Av, 'addcld', [D(w, Av, 'mulcld', [D(w, Av, 'subcld', [vc, a1(w, Av, 'ax-1cn', '1 e. CC')], '( v - 1 ) e. CC'), fvc], '( ( v - 1 ) x. ( F ` v ) ) e. CC'), rpcl(w, Av)], '( ( ( v - 1 ) x. ( F ` v ) ) + %s ) e. CC' % RP), psc], '%s e. CC' % GPR('v'))
    sb = w.s([lfc, gc, w.inst('subeq0')], 'syl2anc', '( %s -> ( ( ( %s ` v ) - %s ) = 0 <-> ( %s ` v ) = %s ) )' % (Av, LF, GPR('v'), LF, GPR('v')))
    zero = w.s([lfe1, sb], 'mpbird', '( %s -> ( ( %s ` v ) - %s ) = 0 )' % (Av, LF, GPR('v')))
    hv0 = w.s([val, zero], 'eqtrd', '( %s -> ( %s ` v ) = 0 )' % (Av, HH))
    BODY = lambda s: 'A. v e. %s ( ( abs ` ( v - %s ) ) < %s -> ( %s ` v ) = 0 )' % (DD, X54, s, HH)
    ral = w.s([w.s([hv0], 'ex', '( %s -> ( ( abs ` ( v - %s ) ) < %s -> ( %s ` v ) = 0 ) )' % (Av0, X54, E8, HH))], 'ralrimiva', '( %s -> %s )' % (A0, BODY(E8)))
    idx = w.s([], 'id', '( s = %s -> s = %s )' % (E8, E8))
    st, val2 = w.wcongr(BODY('s'), {'s': E8}, 's = %s' % E8, {'s': idx})
    assert val2 == BODY(E8), (val2, BODY(E8))
    rs = w.s([st], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. s e. RR+ %s )' % (E8, BODY(E8), BODY('s')))
    e8rp, _ = recip(w, A0, '8')
    w.qed([e8rp, ral, rs], 'syl2anc', STATEMENTS['zl2lfnb'])
    go(w, only)


# ---------------------------------------------------------------- zl2lfz
if __name__ == '__main__' and (not only or 'zl2lfz' in only):
    w = W('zl2lfz', 'The identity theorem ~ holidrect on the rectangle ` [ 1/200 , 3/2 ] x [ -( V + 1 ) , V + 1 ] ` : the difference ` L ( y , chi ) - ( ( y - 1 ) F ( y ) + R ) P ( y ) ` vanishes on it ( ~ zl2lfh , ~ zl2lfrc , ~ zl2lfnb ).')
    A0 = '( %s /\\ ( V e. RR /\\ 0 <_ V ) )' % NXP
    nxp = D(w, A0, 'simpl', [], NXP); vv = D(w, A0, 'simpr', [], '( V e. RR /\\ 0 <_ V )')
    vr = D(w, A0, 'simpld', [vv], 'V e. RR'); v0 = D(w, A0, 'simprd', [vv], '0 <_ V')
    A_ = RCA('V'); B_ = RCB('V')
    h = w.s([nxp, w.inst('zl2lfh')], 'syl', '( %s -> %s )' % (A0, HOL(HH, DD)))
    r2rp, r2r = recip(w, A0, '200'); r32 = frac(w, A0, '3', '2')
    v1r = D(w, A0, 'readdcld', [vr, a1(w, A0, '1re', '1 e. RR')], '( V + 1 ) e. RR'); nv1r = D(w, A0, 'renegcld', [v1r], '-u ( V + 1 ) e. RR')
    ac, rea, ima = cxpt(w, A0, '( 1 / ; ; 2 0 0 )', '-u ( V + 1 )', r2r, nv1r)
    bc, reb, imb = cxpt(w, A0, '( 3 / 2 )', '( V + 1 )', r32, v1r)
    cl = Closure(w, A0, {'V': ('RR', vr), '( 1 / ; ; 2 0 0 )': ('RR', r2r)}); cl.atom('( 1 / ; ; 2 0 0 )')
    r2le = w.s([num.le_lit(w, '( 1 / ; ; 2 0 0 )', '1')], 'a1i', '( %s -> ( 1 / ; ; 2 0 0 ) <_ 1 )' % A0)
    i1 = linarith(w, A0, [r2le], '( 1 / ; ; 2 0 0 ) <_ ( 3 / 2 )', closure=cl)
    i2 = linarith(w, A0, [v0], '-u ( V + 1 ) <_ ( V + 1 )', closure=cl)
    j1 = w.s([w.s([rea, i1], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ ( 3 / 2 ) )' % (A0, A_)), reb], 'breqtrrd', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, A_, B_))
    j2 = w.s([w.s([ima, i2], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ ( V + 1 ) )' % (A0, A_)), imb], 'breqtrrd', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, A_, B_))
    rqrp, rqr = recip(w, A0, '400')
    rc = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('zl2lfrc')], 'syl', '( %s -> %s C_ %s )' % (A0, FAT('V'), DD))
    # 5 / 4 in the rectangle
    x54r = frac(w, A0, '5', '4')
    k1 = linarith(w, A0, [r2le], '( 1 / ; ; 2 0 0 ) <_ %s' % X54, closure=cl); k2 = linarith(w, A0, [], '%s <_ ( 3 / 2 )' % X54, closure=cl)
    xin = w.s([w.s([x54r, k1, k2], '3jca', '( %s -> ( %s e. RR /\\ ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ ( 3 / 2 ) ) )' % (A0, X54, X54, X54)),
               w.s([r2r, r32, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) <-> ( %s e. RR /\\ ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ ( 3 / 2 ) ) ) )' % (A0, X54, X54, X54, X54))], 'mpbird',
              '( %s -> %s e. ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) )' % (A0, X54))
    xin2 = w.s([xin, w.s([w.s([rea, reb], 'oveq12d', '( %s -> ( ( Re ` %s ) [,] ( Re ` %s ) ) = ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) )' % (A0, A_, B_))], 'eleq2d',
                          '( %s -> ( %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) <-> %s e. ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) ) )' % (A0, X54, A_, B_, X54))], 'mpbird', '( %s -> %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A0, X54, A_, B_))
    l1 = linarith(w, A0, [v0], '-u ( V + 1 ) <_ 0', closure=cl); l2 = linarith(w, A0, [v0], '0 <_ ( V + 1 )', closure=cl)
    yin = w.s([w.s([a1(w, A0, '0re', '0 e. RR'), l1, l2], '3jca', '( %s -> ( 0 e. RR /\\ -u ( V + 1 ) <_ 0 /\\ 0 <_ ( V + 1 ) ) )' % A0),
               w.s([nv1r, v1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( 0 e. ( -u ( V + 1 ) [,] ( V + 1 ) ) <-> ( 0 e. RR /\\ -u ( V + 1 ) <_ 0 /\\ 0 <_ ( V + 1 ) ) ) )' % A0)], 'mpbird',
              '( %s -> 0 e. ( -u ( V + 1 ) [,] ( V + 1 ) ) )' % A0)
    yin2 = w.s([yin, w.s([w.s([ima, imb], 'oveq12d', '( %s -> ( ( Im ` %s ) [,] ( Im ` %s ) ) = ( -u ( V + 1 ) [,] ( V + 1 ) ) )' % (A0, A_, B_))], 'eleq2d',
                          '( %s -> ( 0 e. ( ( Im ` %s ) [,] ( Im ` %s ) ) <-> 0 e. ( -u ( V + 1 ) [,] ( V + 1 ) ) ) )' % (A0, A_, B_))], 'mpbird', '( %s -> 0 e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A0, A_, B_))
    pt = w.s([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A_, B_)), w.s([xin2, yin2], 'jca', '( %s -> ( %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ 0 e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (A0, X54, A_, B_, A_, B_)), w.inst('crectpt')], 'syl2anc',
             '( %s -> ( %s + ( _i x. 0 ) ) e. ( %s crect %s ) )' % (A0, X54, A_, B_))
    pteq = w.s([E(w, A0, 'oveq2d', [D(w, A0, 'mul01d', [a1(w, A0, 'ax-icn', '_i e. CC')], '( _i x. 0 ) = 0')], '( %s + ( _i x. 0 ) )' % X54, '( %s + 0 )' % X54), D(w, A0, 'addridd', [D(w, A0, 'recnd', [x54r], '%s e. CC' % X54)], '( %s + 0 ) = %s' % (X54, X54))], 'eqtrd',
               '( %s -> ( %s + ( _i x. 0 ) ) = %s )' % (A0, X54, X54))
    xpt = w.s([pteq, pt], 'eqeltrrd', '( %s -> %s e. ( %s crect %s ) )' % (A0, X54, A_, B_))
    nb = w.s([nxp, w.inst('zl2lfnb')], 'syl', '( %s -> %s )' % (A0, split_imp(STATEMENTS['zl2lfnb'])[1]))
    ABC = '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A_, B_, A_, B_, A_, B_)
    RC = '( %s e. RR+ /\\ %s C_ %s )' % (RQ, FAT('V'), DD)
    XC = '( %s e. ( %s crect %s ) /\\ %s )' % (X54, A_, B_, split_imp(STATEMENTS['zl2lfnb'])[1])
    abc = w.s([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A_, B_)), w.s([j1, j2], 'jca', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, A_, B_, A_, B_))], 'jca', '( %s -> %s )' % (A0, ABC))
    rc_ = w.s([rqrp, rc], 'jca', '( %s -> %s )' % (A0, RC))
    xc = w.s([xpt, nb], 'jca', '( %s -> %s )' % (A0, XC))
    ante = w.s([w.s([h, abc, rc_], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, HOL(HH, DD), ABC, RC)), xc], 'jca', '( %s -> ( ( %s /\\ %s /\\ %s ) /\\ %s ) )' % (A0, HOL(HH, DD), ABC, RC, XC))
    w.qed([ante, w.inst('holidrect')], 'syl', STATEMENTS['zl2lfz'])
    go(w, only)


# ---------------------------------------------------------------- zl2lfe
if __name__ == '__main__' and (not only or 'zl2lfe' in only):
    w = W('zl2lfe', 'The L-function of ` chi ` is the product of the primitive continuation and the Euler-factor polynomial on the strip ` 1/200 <_ Re S <_ 2 ` '
          '( ~ zl2lfz at height ` | Im S | ` for ` Re S <_ 3/2 ` , ~ zl2lfe1 beyond ).')
    RS = '( Re ` S )'
    A0 = '( %s /\\ ( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 ) ) )' % (NXP, RS, RS)
    nxp = D(w, A0, 'simpl', [], NXP); ss = D(w, A0, 'simpr', [], '( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 ) )' % (RS, RS))
    sc = D(w, A0, 'simpld', [ss], 'S e. CC'); sb = D(w, A0, 'simprd', [ss], '( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 )' % (RS, RS))
    c1 = D(w, A0, 'simpld', [sb], '( 1 / ; ; 2 0 0 ) <_ %s' % RS); c2 = D(w, A0, 'simprd', [sb], '%s <_ 2' % RS)
    rsr = D(w, A0, 'recld', [sc], '%s e. RR' % RS)
    r32 = frac(w, A0, '3', '2')
    CON = '( %s ` S ) = %s' % (LF, GPR('S'))
    # case 1: Re S <_ 3 / 2
    A1 = '( %s /\\ %s <_ ( 3 / 2 ) )' % (A0, RS)
    L1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
    case = D(w, A1, 'simpr', [], '%s <_ ( 3 / 2 )' % RS)
    nxp1 = L1(nxp, NXP); sc1 = L1(sc, 'S e. CC'); c11 = L1(c1, '( 1 / ; ; 2 0 0 ) <_ %s' % RS); c21 = L1(c2, '%s <_ 2' % RS); rsr1 = L1(rsr, '%s e. RR' % RS)
    nx1 = D(w, A1, 'simpld', [nxp1], NXL); pc1 = D(w, A1, 'simprd', [nxp1], PCONT); P1 = pcparts(w, A1, pc1)
    isc = D(w, A1, 'recnd', [D(w, A1, 'imcld', [sc1], '( Im ` S ) e. RR')], '( Im ` S ) e. CC')
    T = '( abs ` ( Im ` S ) )'; tr = D(w, A1, 'abscld', [isc], '%s e. RR' % T); t0 = D(w, A1, 'absge0d', [isc], '0 <_ %s' % T)
    A_ = RCA(T); B_ = RCB(T)
    lfz = w.s([w.s([nxp1, w.s([tr, t0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A1, T, T))], 'jca', '( %s -> ( %s /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A1, NXP, T, T)), w.inst('zl2lfz')], 'syl',
              '( %s -> A. y e. ( %s crect %s ) ( %s ` y ) = 0 )' % (A1, A_, B_, HH))
    r2rp, r2r = recip(w, A1, '200'); r321 = frac(w, A1, '3', '2')
    t1r = D(w, A1, 'readdcld', [tr, a1(w, A1, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % T); nt1r = D(w, A1, 'renegcld', [t1r], '-u ( %s + 1 ) e. RR' % T)
    ac, rea, ima = cxpt(w, A1, '( 1 / ; ; 2 0 0 )', '-u ( %s + 1 )' % T, r2r, nt1r)
    bc, reb, imb = cxpt(w, A1, '( 3 / 2 )', '( %s + 1 )' % T, r321, t1r)
    xin = w.s([w.s([rsr1, c11, case], '3jca', '( %s -> ( %s e. RR /\\ ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ ( 3 / 2 ) ) )' % (A1, RS, RS, RS)),
               w.s([r2r, r321, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) <-> ( %s e. RR /\\ ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ ( 3 / 2 ) ) ) )' % (A1, RS, RS, RS, RS))], 'mpbird',
              '( %s -> %s e. ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) )' % (A1, RS))
    xin2 = w.s([xin, w.s([w.s([rea, reb], 'oveq12d', '( %s -> ( ( Re ` %s ) [,] ( Re ` %s ) ) = ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) )' % (A1, A_, B_))], 'eleq2d',
                          '( %s -> ( %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) <-> %s e. ( ( 1 / ; ; 2 0 0 ) [,] ( 3 / 2 ) ) ) )' % (A1, RS, A_, B_, RS))], 'mpbird', '( %s -> %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A1, RS, A_, B_))
    IS = '( Im ` S )'; isr = D(w, A1, 'imcld', [sc1], '%s e. RR' % IS)
    abi = w.s([D(w, A1, 'leidd', [tr], '%s <_ %s' % (T, T)), D(w, A1, 'absled', [isr, tr], '( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (IS, T, T, IS, IS, T))], 'mpbid', '( %s -> ( -u %s <_ %s /\\ %s <_ %s ) )' % (A1, T, IS, IS, T))
    cli = Closure(w, A1, {IS: ('RR', isr), T: ('RR', tr)}); cli.atom(T)
    l1 = linarith(w, A1, [D(w, A1, 'simpld', [abi], '-u %s <_ %s' % (T, IS))], '-u ( %s + 1 ) <_ %s' % (T, IS), closure=cli)
    l2 = linarith(w, A1, [D(w, A1, 'simprd', [abi], '%s <_ %s' % (IS, T))], '%s <_ ( %s + 1 )' % (IS, T), closure=cli)
    yin = w.s([w.s([isr, l1, l2], '3jca', '( %s -> ( %s e. RR /\\ -u ( %s + 1 ) <_ %s /\\ %s <_ ( %s + 1 ) ) )' % (A1, IS, T, IS, IS, T)),
               w.s([nt1r, t1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( -u ( %s + 1 ) [,] ( %s + 1 ) ) <-> ( %s e. RR /\\ -u ( %s + 1 ) <_ %s /\\ %s <_ ( %s + 1 ) ) ) )' % (A1, IS, T, T, IS, T, IS, IS, T))], 'mpbird',
              '( %s -> %s e. ( -u ( %s + 1 ) [,] ( %s + 1 ) ) )' % (A1, IS, T, T))
    yin2 = w.s([yin, w.s([w.s([ima, imb], 'oveq12d', '( %s -> ( ( Im ` %s ) [,] ( Im ` %s ) ) = ( -u ( %s + 1 ) [,] ( %s + 1 ) ) )' % (A1, A_, B_, T, T))], 'eleq2d',
                          '( %s -> ( %s e. ( ( Im ` %s ) [,] ( Im ` %s ) ) <-> %s e. ( -u ( %s + 1 ) [,] ( %s + 1 ) ) ) )' % (A1, IS, A_, B_, IS, T, T))], 'mpbird', '( %s -> %s e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A1, IS, A_, B_))
    mem = w.s([w.s([sc1, xin2, yin2], '3jca', '( %s -> ( S e. CC /\\ %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ %s e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (A1, RS, A_, B_, IS, A_, B_)),
               w.s([ac, bc, w.inst('elcrect')], 'syl2anc', '( %s -> ( S e. ( %s crect %s ) <-> ( S e. CC /\\ %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ %s e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A1, A_, B_, RS, A_, B_, IS, A_, B_))], 'mpbird',
              '( %s -> S e. ( %s crect %s ) )' % (A1, A_, B_))
    h0, _ = inst_ral(w, A1, lfz, 'y', '( %s crect %s )' % (A_, B_), '( %s ` y ) = 0' % HH, 'S', mem)
    cl1 = Closure(w, A1, {RS: ('RR', rsr1), '( 1 / ; ; 2 0 0 )': ('RR', r2r)}); cl1.atom('( 1 / ; ; 2 0 0 )')
    r2p = D(w, A1, 'rpgt0d', [r2rp], '0 < ( 1 / ; ; 2 0 0 )')
    lo = linarith(w, A1, [c11, r2p], '-u ( 1 / 2 ) <_ %s' % RS, closure=cl1); s0 = linarith(w, A1, [c11, r2p], '0 < %s' % RS, closure=cl1)
    fsc, sst, su = instr(w, A1, 'S', sc1, lo, c21, P1['stru'], P1['ff'])
    shp = hpmem(w, A1, 'S', sc1, s0)
    sdd = D(w, A1, 'elind', [su, shp], 'S e. %s' % DD)
    val, _ = mptv(w, A1, 'u', DD, HHB('u'), 'S', sdd)
    lff = w.s([D(w, A1, 'simpld', [w.s([nx1, w.inst('zl1ehol')], 'syl', '( %s -> %s )' % (A1, HOL(LF, HPZ)))], '%s e. ( %s -cn-> CC )' % (LF, HPZ)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (A1, LF, HPZ))
    lfc = D(w, A1, 'ffvelcdmd', [lff, shp], '( %s ` S ) e. CC' % LF)
    pff = w.s([D(w, A1, 'simpld', [w.s([nx1, w.inst('zl2dph')], 'syl', '( %s -> %s )' % (A1, HOL(PF, 'CC')))], '%s e. ( CC -cn-> CC )' % PF), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (A1, PF))
    psc = D(w, A1, 'ffvelcdmd', [pff, sc1], '( %s ` S ) e. CC' % PF)
    gc = D(w, A1, 'mulcld', [D(w, A1, 'addcld', [D(w, A1, 'mulcld', [D(w, A1, 'subcld', [sc1, a1(w, A1, 'ax-1cn', '1 e. CC')], '( S - 1 ) e. CC'), fsc], '( ( S - 1 ) x. ( F ` S ) ) e. CC'), rpcl(w, A1)], '( ( ( S - 1 ) x. ( F ` S ) ) + %s ) e. CC' % RP), psc], '%s e. CC' % GPR('S'))
    z0 = w.s([val, h0], 'eqtr3d', '( %s -> ( ( %s ` S ) - %s ) = 0 )' % (A1, LF, GPR('S')))
    r1 = D(w, A1, 'subeq0d', [lfc, gc, z0], CON)
    # case 2: 3 / 2 < Re S
    A2 = '( %s /\\ ( 3 / 2 ) < %s )' % (A0, RS)
    L2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    case2 = D(w, A2, 'simpr', [], '( 3 / 2 ) < %s' % RS)
    s1 = linarith(w, A2, [case2], '1 < %s' % RS, leaves={RS: L2(rsr, '%s e. RR' % RS)})
    r2 = w.s([L2(nxp, NXP), w.s([L2(sc, 'S e. CC'), w.s([s1, L2(c2, '%s <_ 2' % RS)], 'jca', '( %s -> ( 1 < %s /\\ %s <_ 2 ) )' % (A2, RS, RS))], 'jca', '( %s -> ( S e. CC /\\ ( 1 < %s /\\ %s <_ 2 ) ) )' % (A2, RS, RS)), w.inst('zl2lfe1')], 'syl2anc',
             '( %s -> %s )' % (A2, CON))
    tri = w.s([rsr, r32, w.inst('lelttric')], 'syl2anc', '( %s -> ( %s <_ ( 3 / 2 ) \\/ ( 3 / 2 ) < %s ) )' % (A0, RS, RS))
    w.qed([r1, r2, tri], 'mpjaodan', STATEMENTS['zl2lfe'])
    go(w, only)


# ================================================================== the edges of F at A = 2 and the end theorem
def relit(w, A, digits):
    n = nn0lit(w, digits); t = num.nat_text(int(digits))
    return w.s([w.s([n], 'nn0rei', '%s e. RR' % t)], 'a1i', '( %s -> %s e. RR )' % (A, t)), w.s([w.s([n], 'nn0ge0i', '0 <_ %s' % t)], 'a1i', '( %s -> 0 <_ %s )' % (A, t))


def qparts(w, A1, yc, y_ne1, RY, ryr):
    """the pole term Q = RP / ( y - 1 ): (ymc, ymne, rpc, qc, |Q| = |RP| / |y-1|, |RP| <_ 1, |y-1| e. RR+, ( |RP| / |y-1| ) <_ ( 1 / |y-1| ))"""
    YM = '( y - 1 )'; Q = '( %s / %s )' % (RP, YM)
    ymc = D(w, A1, 'subcld', [yc, a1(w, A1, 'ax-1cn', '1 e. CC')], '%s e. CC' % YM)
    ymne = D(w, A1, 'subne0d', [yc, a1(w, A1, 'ax-1cn', '1 e. CC'), y_ne1], '%s =/= 0' % YM)
    rpc = rpcl(w, A1)
    qc = D(w, A1, 'divcld', [rpc, ymc, ymne], '%s e. CC' % Q)
    aq = D(w, A1, 'absdivd', [rpc, ymc, ymne], '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (Q, RP, YM))
    ra1 = rpabs1(w, A1)
    aymrp = D(w, A1, 'absrpcld', [ymc, ymne], '( abs ` %s ) e. RR+' % YM)
    q1 = D(w, A1, 'lediv1dd', [D(w, A1, 'abscld', [rpc], '( abs ` %s ) e. RR' % RP), a1(w, A1, '1re', '1 e. RR'), aymrp, ra1], '( ( abs ` %s ) / ( abs ` %s ) ) <_ ( 1 / ( abs ` %s ) )' % (RP, YM, YM))
    return ymc, ymne, rpc, qc, aq, ra1, aymrp, q1


# ---------------------------------------------------------------- zl2ergt
if __name__ == '__main__' and (not only or 'zl2ergt' in only):
    w = W('zl2ergt', 'The right-edge bound of the primitive continuation with ` A = 2 ` : ` | F ( z ) | <_ 2 ( 1 + 1 / ( Re z - 1 ) ) ` on ` 1 < Re z <_ 2 ` ( SERY, ~ zl2chs , the pole term ` | R / ( z - 1 ) | <_ 1 / ( Re z - 1 ) ` ).')
    A0 = NXP
    Ay = '( %s /\\ y e. CC )' % A0; RY = '( Re ` y )'
    CND = '( 1 < %s /\\ %s <_ 2 )' % (RY, RY)
    A1 = '( %s /\\ %s )' % (Ay, CND)
    nxp = D(w, A1, 'simpll', [], NXP); yc = D(w, A1, 'simplr', [], 'y e. CC'); cnd = D(w, A1, 'simpr', [], CND)
    y1 = D(w, A1, 'simpld', [cnd], '1 < %s' % RY); y2 = D(w, A1, 'simprd', [cnd], '%s <_ 2' % RY)
    nx = D(w, A1, 'simpld', [nxp], NXL); pc = D(w, A1, 'simprd', [nxp], PCONT); P = pcparts(w, A1, pc)
    nxs, mn, yb = nxm(w, A1, nx)
    ryr = D(w, A1, 'recld', [yc], '%s e. RR' % RY)
    Q = '( %s / ( y - 1 ) )' % RP; DCY = DS(CY, 'y'); B1 = '( 1 + ( 1 / ( %s - 1 ) ) )' % RY
    sy, _ = inst_ral_t(w, A1, P['sery'], 'CC', SERY[len('A. z e. CC '):], 'y', yc)
    eq = w.s([cnd, sy], 'mpd', '( %s -> ( ( F ` y ) + %s ) = %s )' % (A1, Q, DCY))
    chs = w.s([nxs, w.s([yc, y1], 'jca', '( %s -> ( y e. CC /\\ 1 < %s ) )' % (A1, RY)), w.inst('zl2chs')], 'syl2anc', '( %s -> ( %s e. CC /\\ ( abs ` %s ) <_ %s ) )' % (A1, DCY, DCY, B1))
    dsc = D(w, A1, 'simpld', [chs], '%s e. CC' % DCY); dsb = D(w, A1, 'simprd', [chs], '( abs ` %s ) <_ %s' % (DCY, B1))
    lo = linarith(w, A1, [y1], '-u ( 1 / 2 ) <_ %s' % RY, leaves={RY: ryr})
    fyc, _, _ = instr(w, A1, 'y', yc, lo, y2, P['stru'], P['ff'])
    rsne = w.s([y1], 'gtned', '( %s -> %s =/= 1 )' % (A1, RY))
    yne1 = sne1(w, A1, 'y', yc, rsne)
    ymc, ymne, rpc, qc, aq, ra1, aymrp, q1 = qparts(w, A1, yc, yne1, RY, ryr)
    YM = '( y - 1 )'
    f1 = w.s([D(w, A1, 'pncand', [fyc, qc], '( ( ( F ` y ) + %s ) - %s ) = ( F ` y )' % (Q, Q))], 'eqcomd', '( %s -> ( F ` y ) = ( ( ( F ` y ) + %s ) - %s ) )' % (A1, Q, Q))
    f2 = E(w, A1, 'oveq1d', [eq], '( ( ( F ` y ) + %s ) - %s )' % (Q, Q), '( %s - %s )' % (DCY, Q))
    fq = w.s([f1, f2], 'eqtrd', '( %s -> ( F ` y ) = ( %s - %s ) )' % (A1, DCY, Q))
    ab = D(w, A1, 'abs2dif2d', [dsc, qc], '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (DCY, Q, DCY, Q))
    abf = w.s([E(w, A1, 'fveq2d', [fq], '( abs ` ( F ` y ) )', '( abs ` ( %s - %s ) )' % (DCY, Q)), ab], 'eqbrtrd', '( %s -> ( abs ` ( F ` y ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, DCY, Q))
    # ( Re y - 1 ) <_ | y - 1 |
    R1 = '( %s - 1 )' % RY; r1r = D(w, A1, 'resubcld', [ryr, a1(w, A1, '1re', '1 e. RR')], '%s e. RR' % R1)
    rey = w.s([D(w, A1, 'resubd', [yc, a1(w, A1, 'ax-1cn', '1 e. CC')], '( Re ` %s ) = ( %s - ( Re ` 1 ) )' % (YM, RY)), E(w, A1, 'oveq2d', [a1(w, A1, 're1', '( Re ` 1 ) = 1')], '( %s - ( Re ` 1 ) )' % RY, R1)], 'eqtrd',
              '( %s -> ( Re ` %s ) = %s )' % (A1, YM, R1))
    reymr = D(w, A1, 'recld', [ymc], '( Re ` %s ) e. RR' % YM)
    le1 = D(w, A1, 'leabsd', [reymr], '( Re ` %s ) <_ ( abs ` ( Re ` %s ) )' % (YM, YM))
    le2 = w.s([ymc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` %s ) ) <_ ( abs ` %s ) )' % (A1, YM, YM))
    aym = D(w, A1, 'abscld', [ymc], '( abs ` %s ) e. RR' % YM)
    le3 = D(w, A1, 'letrd', [reymr, D(w, A1, 'abscld', [D(w, A1, 'recnd', [reymr], '( Re ` %s ) e. CC' % YM)], '( abs ` ( Re ` %s ) ) e. RR' % YM), aym, le1, le2], '( Re ` %s ) <_ ( abs ` %s )' % (YM, YM))
    le4 = w.s([rey, le3], 'eqbrtrrd', '( %s -> %s <_ ( abs ` %s ) )' % (A1, R1, YM))
    r1p = linarith(w, A1, [y1], '0 < %s' % R1, leaves={RY: ryr})
    r1rp = D(w, A1, 'elrpd', [r1r, r1p], '%s e. RR+' % R1)
    bi = D(w, A1, 'lerecd', [r1rp, aymrp], '( %s <_ ( abs ` %s ) <-> ( 1 / ( abs ` %s ) ) <_ ( 1 / %s ) )' % (R1, YM, YM, R1))
    q2 = w.s([le4, bi], 'mpbid', '( %s -> ( 1 / ( abs ` %s ) ) <_ ( 1 / %s ) )' % (A1, YM, R1))
    RC = '( 1 / %s )' % R1; rcr = D(w, A1, 'rpred', [D(w, A1, 'rpreccld', [r1rp], '%s e. RR+' % RC)], '%s e. RR' % RC)
    q3 = D(w, A1, 'letrd', [D(w, A1, 'rerpdivcld', [D(w, A1, 'abscld', [rpc], '( abs ` %s ) e. RR' % RP), aymrp], '( ( abs ` %s ) / ( abs ` %s ) ) e. RR' % (RP, YM)), D(w, A1, 'rpred', [D(w, A1, 'rpreccld', [aymrp], '( 1 / ( abs ` %s ) ) e. RR+' % YM)], '( 1 / ( abs ` %s ) ) e. RR' % YM), rcr, q1, q2],
           '( ( abs ` %s ) / ( abs ` %s ) ) <_ %s' % (RP, YM, RC))
    qle = w.s([aq, q3], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A1, Q, RC))
    AFY = '( abs ` ( F ` y ) )'; ADS = '( abs ` %s )' % DCY; AQ = '( abs ` %s )' % Q
    cl = Closure(w, A1, {AFY: ('RR', D(w, A1, 'abscld', [fyc], '%s e. RR' % AFY)), ADS: ('RR', D(w, A1, 'abscld', [dsc], '%s e. RR' % ADS)), AQ: ('RR', D(w, A1, 'abscld', [qc], '%s e. RR' % AQ)), RC: ('RR', rcr)})
    cl.atom(ADS); cl.atom(AQ); cl.atom(RC)
    fin = linarith(w, A1, [abf, dsb, qle], '%s <_ ( 2 x. %s )' % (AFY, B1), closure=cl)
    BODY = '( %s -> %s <_ ( 2 x. %s ) )' % (CND, AFY, B1)
    raly = w.s([w.s([fin], 'ex', '( %s -> %s )' % (Ay, BODY))], 'ralrimiva', '( %s -> A. y e. CC %s )' % (A0, BODY))
    r, val = cbv_yz(w, A0, raly, 'CC', BODY)
    assert 'A. z e. CC %s' % val == RGT('F', '2'), (val, RGT('F', '2'))
    w.lines[-1] = w.lines[-1].replace(r + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2egr
if __name__ == '__main__' and (not only or 'zl2egr' in only):
    w = W('zl2egr', 'The Dirichlet series of the inverse primitive character satisfies GRGT with ` A = 1 ` ( ~ zl2chs at the inverse character, ~ grpinvcl ).')
    A0 = NXP
    Ay = '( %s /\\ y e. CC )' % A0; RY = '( Re ` y )'
    A1 = '( %s /\\ 1 < %s )' % (Ay, RY)
    nxp = D(w, A1, 'simpll', [], NXP); yc = D(w, A1, 'simplr', [], 'y e. CC'); y1 = D(w, A1, 'simpr', [], '1 < %s' % RY)
    nx = D(w, A1, 'simpld', [nxp], NXL)
    nxs, mn, yb = nxm(w, A1, nx)
    GM = '( DChr ` %s )' % MC; IY = '( ( invg ` %s ) ` %s )' % (GM, YP)
    abl = w.s([mn, w.s([w.s([], 'eqid', '%s = %s' % (GM, GM))], 'dchrabl', '( %s e. NN -> %s e. Abel )' % (MC, GM))], 'syl', '( %s -> %s e. Abel )' % (A1, GM))
    grp = w.s([abl, w.inst('ablgrp')], 'syl', '( %s -> %s e. Grp )' % (A1, GM))
    ginv = w.s([w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (GM, GM)), w.s([], 'eqid', '( invg ` %s ) = ( invg ` %s )' % (GM, GM))], 'grpinvcl',
               '( ( %s e. Grp /\\ %s e. ( Base ` %s ) ) -> %s e. ( Base ` %s ) )' % (GM, YP, GM, IY, GM))
    iyb = w.s([grp, yb, ginv], 'syl2anc', '( %s -> %s e. ( Base ` %s ) )' % (A1, IY, GM))
    nxi = w.s([mn, iyb], 'jca', '( %s -> ( %s e. NN /\\ %s e. ( Base ` %s ) ) )' % (A1, MC, IY, GM))
    DCB = DS(CYB, 'y'); B1 = '( 1 + ( 1 / ( %s - 1 ) ) )' % RY
    chs = w.s([nxi, w.s([yc, y1], 'jca', '( %s -> ( y e. CC /\\ 1 < %s ) )' % (A1, RY)), w.inst('zl2chs')], 'syl2anc', '( %s -> ( %s e. CC /\\ ( abs ` %s ) <_ %s ) )' % (A1, DCB, DCB, B1))
    exs = w.s([w.s([], 'sumex', '%s e. _V' % DCB)], 'a1i', '( %s -> %s e. _V )' % (A1, DCB))
    v, _ = mptv(w, A1, 'w', 'CC', DS(CYB, 'w'), 'y', yc, exs=exs)
    c1 = w.s([v, D(w, A1, 'simpld', [chs], '%s e. CC' % DCB)], 'eqeltrd', '( %s -> ( %s ` y ) e. CC )' % (A1, GYB))
    ryr = D(w, A1, 'recld', [yc], '%s e. RR' % RY)
    r1p = linarith(w, A1, [y1], '0 < ( %s - 1 )' % RY, leaves={RY: ryr})
    b1r = D(w, A1, 'readdcld', [a1(w, A1, '1re', '1 e. RR'), D(w, A1, 'rpred', [D(w, A1, 'rpreccld', [D(w, A1, 'elrpd', [D(w, A1, 'resubcld', [ryr, a1(w, A1, '1re', '1 e. RR')], '( %s - 1 ) e. RR' % RY), r1p], '( %s - 1 ) e. RR+' % RY)], '( 1 / ( %s - 1 ) ) e. RR+' % RY)], '( 1 / ( %s - 1 ) ) e. RR' % RY)], '%s e. RR' % B1)
    c2a = w.s([E(w, A1, 'fveq2d', [v], '( abs ` ( %s ` y ) )' % GYB, '( abs ` %s )' % DCB), D(w, A1, 'simprd', [chs], '( abs ` %s ) <_ %s' % (DCB, B1))], 'eqbrtrd', '( %s -> ( abs ` ( %s ` y ) ) <_ %s )' % (A1, GYB, B1))
    c2 = w.s([c2a, D(w, A1, 'mullidd', [D(w, A1, 'recnd', [b1r], '%s e. CC' % B1)], '( 1 x. %s ) = %s' % (B1, B1))], 'breqtrrd', '( %s -> ( abs ` ( %s ` y ) ) <_ ( 1 x. %s ) )' % (A1, GYB, B1))
    BODY = '( 1 < %s -> ( ( %s ` y ) e. CC /\\ ( abs ` ( %s ` y ) ) <_ ( 1 x. %s ) ) )' % (RY, GYB, GYB, B1)
    w.qed([w.s([w.s([c1, c2], 'jca', '( %s -> ( ( %s ` y ) e. CC /\\ ( abs ` ( %s ` y ) ) <_ ( 1 x. %s ) ) )' % (A1, GYB, GYB, B1))], 'ex', '( %s -> %s )' % (Ay, BODY))], 'ralrimiva', STATEMENTS['zl2egr'])
    go(w, only)


# ---------------------------------------------------------------- zl2efe
if __name__ == '__main__' and (not only or 'zl2efe' in only):
    w = W('zl2efe', 'The functional equation FEY in the form FEQ of ~ zl2left , for the primitive L-function ` F + R / ( w - 1 ) ` and the series of the inverse character.')
    A0 = NXP
    Ay = '( %s /\\ y e. CC )' % A0; RY = '( Re ` y )'
    CND = '( -u ( 1 / 2 ) <_ %s /\\ %s < 0 )' % (RY, RY)
    A1 = '( %s /\\ %s )' % (Ay, CND)
    nxp = D(w, A1, 'simpll', [], NXP); yc = D(w, A1, 'simplr', [], 'y e. CC'); cnd = D(w, A1, 'simpr', [], CND)
    pc = D(w, A1, 'simprd', [nxp], PCONT); P = pcparts(w, A1, pc)
    fy, _ = inst_ral_t(w, A1, P['fey'], 'CC', FEY[len('A. z e. CC '):], 'y', yc)
    Q = '( %s / ( y - 1 ) )' % RP
    RHS = '( ( ( %s ^c ( ( 1 / 2 ) - y ) ) x. T ) x. ( ( Q ` y ) x. %s ) )' % (MC, DS(CYB, '( 1 - y )'))
    eq = w.s([cnd, fy], 'mpd', '( %s -> ( ( F ` y ) + %s ) = %s )' % (A1, Q, RHS))
    vF, _ = mptv(w, A1, 'w', 'CC', '( ( F ` w ) + ( %s / ( w - 1 ) ) )' % RP, 'y', yc)
    omy = D(w, A1, 'subcld', [a1(w, A1, 'ax-1cn', '1 e. CC'), yc], '( 1 - y ) e. CC')
    exg = w.s([w.s([], 'sumex', '%s e. _V' % DS(CYB, '( 1 - y )'))], 'a1i', '( %s -> %s e. _V )' % (A1, DS(CYB, '( 1 - y )')))
    vG, _ = mptv(w, A1, 'w', 'CC', DS(CYB, 'w'), '( 1 - y )', omy, exs=exg)
    t1 = w.s([vF, eq], 'eqtrd', '( %s -> ( %s ` y ) = %s )' % (A1, FPM, RHS))
    RHS2 = '( ( ( %s ^c ( ( 1 / 2 ) - y ) ) x. T ) x. ( ( Q ` y ) x. ( %s ` ( 1 - y ) ) ) )' % (MC, GYB)
    t2 = E(w, A1, 'oveq2d', [E(w, A1, 'oveq2d', [w.s([vG], 'eqcomd', '( %s -> %s = ( %s ` ( 1 - y ) ) )' % (A1, DS(CYB, '( 1 - y )'), GYB))], '( ( Q ` y ) x. %s )' % DS(CYB, '( 1 - y )'), '( ( Q ` y ) x. ( %s ` ( 1 - y ) ) )' % GYB)], RHS, RHS2)
    BODY = '( %s -> ( %s ` y ) = %s )' % (CND, FPM, RHS2)
    w.qed([w.s([w.s([t1, t2], 'eqtrd', '( %s -> ( %s ` y ) = %s )' % (A1, FPM, RHS2))], 'ex', '( %s -> %s )' % (Ay, BODY))], 'ralrimiva', STATEMENTS['zl2efe'])
    go(w, only)


# ---------------------------------------------------------------- zl2elft1
if __name__ == '__main__' and (not only or 'zl2elft1' in only):
    w = W('zl2elft1', 'The left edge of the primitive L-function ` F + R / ( w - 1 ) ` at modulus ` M ` and ` A = 1 ` ( ~ zl2left with ~ zl2efe , ~ zl2egr , QBND ).')
    A0 = NXP
    nx = D(w, A0, 'simpl', [], NXL); pc = D(w, A0, 'simpr', [], PCONT); P = pcparts(w, A0, pc)
    nxs, mn, yb = nxm(w, A0, nx)
    idx = w.s([], 'id', '( z = y -> z = y )')
    st, QBY = w.wcongr(QBND[len('A. z e. CC '):], {'z': 'y'}, 'z = y', {'z': idx})
    cbv = w.s([st], 'cbvralvw', '( %s <-> A. y e. CC %s )' % (QBND, QBY))
    qby = w.s([P['qbnd'], cbv], 'sylib', '( %s -> A. y e. CC %s )' % (A0, QBY))
    efe = w.s([], 'zl2efe', STATEMENTS['zl2efe']); egr = w.s([], 'zl2egr', STATEMENTS['zl2egr'])
    INST = subst(STATEMENTS['zl2left'], {'F': FPM, 'N': MC, 'A': '1', 'E': 'T', 'G': GYB, 'z': 'y'})
    ANT, CON = split_imp(INST)
    FEQy = split_imp(STATEMENTS['zl2efe'])[1]; GRy = split_imp(STATEMENTS['zl2egr'])[1]
    want = '( ( ( %s e. NN /\\ 1 e. RR ) /\\ %s ) /\\ ( %s /\\ ( A. y e. CC %s /\\ %s ) ) )' % (MC, TQ1, FEQy, QBY, GRy)
    assert ANT == want, '\n'.join([ANT, want])
    ante = w.s([w.s([w.s([mn, a1(w, A0, '1re', '1 e. RR')], 'jca', '( %s -> ( %s e. NN /\\ 1 e. RR ) )' % (A0, MC)), P['tq']], 'jca', '( %s -> ( ( %s e. NN /\\ 1 e. RR ) /\\ %s ) )' % (A0, MC, TQ1)),
                w.s([efe, w.s([qby, egr], 'jca', '( %s -> ( A. y e. CC %s /\\ %s ) )' % (A0, QBY, GRy))], 'jca', '( %s -> ( %s /\\ ( A. y e. CC %s /\\ %s ) ) )' % (A0, FEQy, QBY, GRy))], 'jca', '( %s -> %s )' % (A0, ANT))
    lfty = w.s([ante, w.inst('zl2left')], 'syl', '( %s -> %s )' % (A0, CON))
    r, val = cbv_yz(w, A0, lfty, 'CC', CON[len('A. y e. CC '):])
    assert 'A. z e. CC %s' % val == LFT(FPM, '1', MC), (val, LFT(FPM, '1', MC))
    w.lines[-1] = w.lines[-1].replace(r + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2elft
if __name__ == '__main__' and (not only or 'zl2elft' in only):
    w = W('zl2elft', 'The left-edge bound of the primitive continuation with ` A = 2 ` at modulus ` M ` ( ~ zl2elft1 , the pole term ` | R / ( z - 1 ) | <_ 1 ` and ` 1 <_ ` the edge bound ).')
    A0 = NXP
    Ay = '( %s /\\ y e. CC )' % A0; RY = '( Re ` y )'
    CND = '( -u ( 1 / 2 ) <_ %s /\\ %s < 0 )' % (RY, RY)
    A1 = '( %s /\\ %s )' % (Ay, CND)
    nxp = D(w, A1, 'simpll', [], NXP); yc = D(w, A1, 'simplr', [], 'y e. CC'); cnd = D(w, A1, 'simpr', [], CND)
    lo = D(w, A1, 'simpld', [cnd], '-u ( 1 / 2 ) <_ %s' % RY); ylt0 = D(w, A1, 'simprd', [cnd], '%s < 0' % RY)
    pc = D(w, A1, 'simprd', [nxp], PCONT); P = pcparts(w, A1, pc)
    nx = D(w, A1, 'simpld', [nxp], NXL); nxs, mn, yb = nxm(w, A1, nx)
    ryr = D(w, A1, 'recld', [yc], '%s e. RR' % RY)
    lft1 = w.s([w.s([], 'zl2elft1', STATEMENTS['zl2elft1'])], 'ad2antrr', '( %s -> %s )' % (A1, LFT(FPM, '1', MC)))
    b0, _ = inst_ral_t(w, A1, lft1, 'CC', LFT(FPM, '1', MC)[len('A. z e. CC '):], 'y', yc)
    LB1 = LFTB('y', '1', MC); LB2 = LFTB('y', '2', MC)
    b1 = w.s([cnd, b0], 'mpd', '( %s -> ( abs ` ( %s ` y ) ) <_ %s )' % (A1, FPM, LB1))
    hi = linarith(w, A1, [ylt0], '%s <_ 2' % RY, leaves={RY: ryr})
    fyc, _, _ = instr(w, A1, 'y', yc, lo, hi, P['stru'], P['ff'])
    Q = '( %s / ( y - 1 ) )' % RP
    vF, _ = mptv(w, A1, 'w', 'CC', '( ( F ` w ) + ( %s / ( w - 1 ) ) )' % RP, 'y', yc)
    rlt1 = linarith(w, A1, [ylt0], '%s < 1' % RY, leaves={RY: ryr})
    rsne = D(w, A1, 'ltned', [rlt1], '%s =/= 1' % RY)
    yne1 = sne1(w, A1, 'y', yc, rsne)
    ymc, ymne, rpc, qc, aq, ra1, aymrp, q1 = qparts(w, A1, yc, yne1, RY, ryr)
    YM = '( y - 1 )'
    fpc = w.s([vF, D(w, A1, 'addcld', [fyc, qc], '( ( F ` y ) + %s ) e. CC' % Q)], 'eqeltrd', '( %s -> ( %s ` y ) e. CC )' % (A1, FPM))
    f1 = w.s([D(w, A1, 'pncand', [fyc, qc], '( ( ( F ` y ) + %s ) - %s ) = ( F ` y )' % (Q, Q))], 'eqcomd', '( %s -> ( F ` y ) = ( ( ( F ` y ) + %s ) - %s ) )' % (A1, Q, Q))
    f2 = E(w, A1, 'oveq1d', [w.s([vF], 'eqcomd', '( %s -> ( ( F ` y ) + %s ) = ( %s ` y ) )' % (A1, Q, FPM))], '( ( ( F ` y ) + %s ) - %s )' % (Q, Q), '( ( %s ` y ) - %s )' % (FPM, Q))
    fq = w.s([f1, f2], 'eqtrd', '( %s -> ( F ` y ) = ( ( %s ` y ) - %s ) )' % (A1, FPM, Q))
    ab = D(w, A1, 'abs2dif2d', [fpc, qc], '( abs ` ( ( %s ` y ) - %s ) ) <_ ( ( abs ` ( %s ` y ) ) + ( abs ` %s ) )' % (FPM, Q, FPM, Q))
    abf = w.s([E(w, A1, 'fveq2d', [fq], '( abs ` ( F ` y ) )', '( abs ` ( ( %s ` y ) - %s ) )' % (FPM, Q)), ab], 'eqbrtrd', '( %s -> ( abs ` ( F ` y ) ) <_ ( ( abs ` ( %s ` y ) ) + ( abs ` %s ) ) )' % (A1, FPM, Q))
    # 1 <_ | y - 1 | : 1 - Re y <_ | y - 1 |
    R1 = '( %s - 1 )' % RY
    rey = w.s([D(w, A1, 'resubd', [yc, a1(w, A1, 'ax-1cn', '1 e. CC')], '( Re ` %s ) = ( %s - ( Re ` 1 ) )' % (YM, RY)), E(w, A1, 'oveq2d', [a1(w, A1, 're1', '( Re ` 1 ) = 1')], '( %s - ( Re ` 1 ) )' % RY, R1)], 'eqtrd',
              '( %s -> ( Re ` %s ) = %s )' % (A1, YM, R1))
    r1r = D(w, A1, 'resubcld', [ryr, a1(w, A1, '1re', '1 e. RR')], '%s e. RR' % R1)
    nr1 = D(w, A1, 'leabsd', [D(w, A1, 'renegcld', [r1r], '-u %s e. RR' % R1)], '-u %s <_ ( abs ` -u %s )' % (R1, R1))
    an = D(w, A1, 'absnegd', [D(w, A1, 'recnd', [r1r], '%s e. CC' % R1)], '( abs ` -u %s ) = ( abs ` %s )' % (R1, R1))
    nr2 = w.s([nr1, an], 'breqtrd', '( %s -> -u %s <_ ( abs ` %s ) )' % (A1, R1, R1))
    ar1 = w.s([E(w, A1, 'fveq2d', [rey], '( abs ` ( Re ` %s ) )' % YM, '( abs ` %s )' % R1), w.s([ymc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` %s ) ) <_ ( abs ` %s ) )' % (A1, YM, YM))], 'eqbrtrrd',
              '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (A1, R1, YM))
    aym = D(w, A1, 'abscld', [ymc], '( abs ` %s ) e. RR' % YM)
    nr3 = D(w, A1, 'letrd', [D(w, A1, 'renegcld', [r1r], '-u %s e. RR' % R1), D(w, A1, 'abscld', [D(w, A1, 'recnd', [r1r], '%s e. CC' % R1)], '( abs ` %s ) e. RR' % R1), aym, nr2, ar1], '-u %s <_ ( abs ` %s )' % (R1, YM))
    one_le = linarith(w, A1, [ylt0], '1 <_ -u %s' % R1, leaves={RY: ryr})
    ym1 = D(w, A1, 'letrd', [a1(w, A1, '1re', '1 e. RR'), D(w, A1, 'renegcld', [r1r], '-u %s e. RR' % R1), aym, one_le, nr3], '1 <_ ( abs ` %s )' % YM)
    bi = D(w, A1, 'lerecd', [a1(w, A1, '1rp', '1 e. RR+'), aymrp], '( 1 <_ ( abs ` %s ) <-> ( 1 / ( abs ` %s ) ) <_ ( 1 / 1 ) )' % (YM, YM))
    q2 = w.s([w.s([ym1, bi], 'mpbid', '( %s -> ( 1 / ( abs ` %s ) ) <_ ( 1 / 1 ) )' % (A1, YM)), a1(w, A1, '1div1e1', '( 1 / 1 ) = 1')], 'breqtrd', '( %s -> ( 1 / ( abs ` %s ) ) <_ 1 )' % (A1, YM))
    q3 = D(w, A1, 'letrd', [D(w, A1, 'rerpdivcld', [D(w, A1, 'abscld', [rpc], '( abs ` %s ) e. RR' % RP), aymrp], '( ( abs ` %s ) / ( abs ` %s ) ) e. RR' % (RP, YM)), D(w, A1, 'rpred', [D(w, A1, 'rpreccld', [aymrp], '( 1 / ( abs ` %s ) ) e. RR+' % YM)], '( 1 / ( abs ` %s ) ) e. RR' % YM), a1(w, A1, '1re', '1 e. RR'), q1, q2],
           '( ( abs ` %s ) / ( abs ` %s ) ) <_ 1' % (RP, YM))
    qle = w.s([aq, q3], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ 1 )' % (A1, Q))
    # 1 <_ LB1
    P1 = '( 1 + ( 1 / -u %s ) )' % RY; QTM = QT('y', MC); EXY = '( ( 1 / 2 ) - %s )' % RY; P2 = '( %s ^c %s )' % (QTM, EXY)
    assert LB1 == '( ( ( ; 1 2 x. 1 ) x. %s ) x. %s )' % (P1, P2), LB1
    nry = D(w, A1, 'renegcld', [ryr], '-u %s e. RR' % RY)
    nryp = linarith(w, A1, [ylt0], '0 < -u %s' % RY, leaves={RY: ryr})
    nryrp = D(w, A1, 'elrpd', [nry, nryp], '-u %s e. RR+' % RY)
    rcp = D(w, A1, 'rpreccld', [nryrp], '( 1 / -u %s ) e. RR+' % RY); rcr = D(w, A1, 'rpred', [rcp], '( 1 / -u %s ) e. RR' % RY)
    p1r = D(w, A1, 'readdcld', [a1(w, A1, '1re', '1 e. RR'), rcr], '%s e. RR' % P1)
    p1ge1 = linarith(w, A1, [D(w, A1, 'rpge0d', [rcp], '0 <_ ( 1 / -u %s )' % RY)], '1 <_ %s' % P1, leaves={'( 1 / -u %s )' % RY: rcr})
    iyc = D(w, A1, 'recnd', [D(w, A1, 'imcld', [yc], '( Im ` y ) e. RR')], '( Im ` y ) e. CC')
    aiy = D(w, A1, 'abscld', [iyc], '( abs ` ( Im ` y ) ) e. RR'); aiy0 = D(w, A1, 'absge0d', [iyc], '0 <_ ( abs ` ( Im ` y ) )')
    I2 = '( ( abs ` ( Im ` y ) ) + 2 )'
    i2r = D(w, A1, 'readdcld', [aiy, a1(w, A1, '2re', '2 e. RR')], '%s e. RR' % I2)
    i21 = linarith(w, A1, [aiy0], '1 <_ %s' % I2, leaves={'( abs ` ( Im ` y ) )': aiy})
    mr = D(w, A1, 'nnred', [mn], '%s e. RR' % MC); m1 = D(w, A1, 'nnge1d', [mn], '1 <_ %s' % MC)
    qtmr = D(w, A1, 'remulcld', [mr, i2r], '%s e. RR' % QTM)
    qtm1a = D(w, A1, 'lemul12ad', [a1(w, A1, '1re', '1 e. RR'), mr, a1(w, A1, '1re', '1 e. RR'), i2r, a1(w, A1, '0le1', '0 <_ 1'), a1(w, A1, '0le1', '0 <_ 1'), m1, i21], '( 1 x. 1 ) <_ %s' % QTM)
    qtm1 = w.s([a1(w, A1, '1t1e1', '( 1 x. 1 ) = 1'), qtm1a], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (A1, QTM))
    exr = D(w, A1, 'resubcld', [a1(w, A1, 'halfre', '( 1 / 2 ) e. RR'), ryr], '%s e. RR' % EXY)
    ex0 = linarith(w, A1, [ylt0], '0 <_ %s' % EXY, leaves={RY: ryr})
    p2ge1 = w.s([D(w, A1, 'cxp0d', [D(w, A1, 'recnd', [qtmr], '%s e. CC' % QTM)], '( %s ^c 0 ) = 1' % QTM), D(w, A1, 'cxplead', [qtmr, qtm1, a1(w, A1, '0re', '0 e. RR'), exr, ex0], '( %s ^c 0 ) <_ %s' % (QTM, P2))], 'eqbrtrrd',
               '( %s -> 1 <_ %s )' % (A1, P2))
    qtm0 = linarith(w, A1, [qtm1], '0 <_ %s' % QTM, leaves={QTM: qtmr})
    p2r = D(w, A1, 'recxpcld', [qtmr, qtm0, exr], '%s e. RR' % P2)
    p12 = w.s([a1(w, A1, '1t1e1', '( 1 x. 1 ) = 1'), D(w, A1, 'lemul12ad', [a1(w, A1, '1re', '1 e. RR'), p1r, a1(w, A1, '1re', '1 e. RR'), p2r, a1(w, A1, '0le1', '0 <_ 1'), a1(w, A1, '0le1', '0 <_ 1'), p1ge1, p2ge1], '( 1 x. 1 ) <_ ( %s x. %s )' % (P1, P2))], 'eqbrtrrd',
              '( %s -> 1 <_ ( %s x. %s ) )' % (A1, P1, P2))
    n12r, n120 = relit(w, A1, '12')
    n12c = D(w, A1, 'recnd', [n12r], '; 1 2 e. CC')
    e1 = E(w, A1, 'oveq1d', [E(w, A1, 'oveq1d', [D(w, A1, 'mulridd', [n12c], '( ; 1 2 x. 1 ) = ; 1 2')], '( ( ; 1 2 x. 1 ) x. %s )' % P1, '( ; 1 2 x. %s )' % P1)], LB1, '( ( ; 1 2 x. %s ) x. %s )' % (P1, P2))
    e2 = D(w, A1, 'mulassd', [n12c, D(w, A1, 'recnd', [p1r], '%s e. CC' % P1), D(w, A1, 'recnd', [p2r], '%s e. CC' % P2)], '( ( ; 1 2 x. %s ) x. %s ) = ( ; 1 2 x. ( %s x. %s ) )' % (P1, P2, P1, P2))
    lb1e = w.s([e1, e2], 'eqtrd', '( %s -> %s = ( ; 1 2 x. ( %s x. %s ) ) )' % (A1, LB1, P1, P2))
    p12r = D(w, A1, 'remulcld', [p1r, p2r], '( %s x. %s ) e. RR' % (P1, P2))
    big0 = D(w, A1, 'lemul2ad', [a1(w, A1, '1re', '1 e. RR'), p12r, n12r, n120, p12], '( ; 1 2 x. 1 ) <_ ( ; 1 2 x. ( %s x. %s ) )' % (P1, P2))
    big1 = w.s([D(w, A1, 'mulridd', [n12c], '( ; 1 2 x. 1 ) = ; 1 2'), big0], 'eqbrtrrd', '( %s -> ; 1 2 <_ ( ; 1 2 x. ( %s x. %s ) ) )' % (A1, P1, P2))
    one12 = linarith(w, A1, [], '1 <_ ; 1 2', leaves={})
    big2 = D(w, A1, 'letrd', [a1(w, A1, '1re', '1 e. RR'), n12r, D(w, A1, 'remulcld', [n12r, p12r], '( ; 1 2 x. ( %s x. %s ) ) e. RR' % (P1, P2)), one12, big1], '1 <_ ( ; 1 2 x. ( %s x. %s ) )' % (P1, P2))
    big = w.s([big2, lb1e], 'breqtrrd', '( %s -> 1 <_ %s )' % (A1, LB1))
    AFY = '( abs ` ( F ` y ) )'; AFP = '( abs ` ( %s ` y ) )' % FPM; AQ = '( abs ` %s )' % Q
    cl = Closure(w, A1, {AFY: ('RR', D(w, A1, 'abscld', [fyc], '%s e. RR' % AFY)), AFP: ('RR', D(w, A1, 'abscld', [fpc], '%s e. RR' % AFP)), AQ: ('RR', D(w, A1, 'abscld', [qc], '%s e. RR' % AQ)), P1: ('RR', p1r), P2: ('RR', p2r)})
    cl.atom(AFP); cl.atom(AQ); cl.atom(P1); cl.atom(P2)
    fin = linarith(w, A1, [abf, b1, qle, big], '%s <_ %s' % (AFY, LB2), closure=cl, products=True)
    BODY = '( %s -> %s <_ %s )' % (CND, AFY, LB2)
    raly = w.s([w.s([fin], 'ex', '( %s -> %s )' % (Ay, BODY))], 'ralrimiva', '( %s -> A. y e. CC %s )' % (A0, BODY))
    r, val = cbv_yz(w, A0, raly, 'CC', BODY)
    assert 'A. z e. CC %s' % val == LFT('F', '2', MC), (val, LFT('F', '2', MC))
    w.lines[-1] = w.lines[-1].replace(r + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2ecvx
if __name__ == '__main__' and (not only or 'zl2ecvx' in only):
    w = W('zl2ecvx', 'The convexity bound ~ zl2cvx for the primitive continuation ` F ` at modulus ` M ` with ` A = 2 ` ( ~ zl2ergt , ~ zl2elft ).')
    A0 = '( %s /\\ %s )' % (NXP, SRNG2())
    nxp = D(w, A0, 'simpl', [], NXP); sr = D(w, A0, 'simpr', [], SRNG2())
    nx = D(w, A0, 'simpld', [nxp], NXL); pc = D(w, A0, 'simprd', [nxp], PCONT); P = pcparts(w, A0, pc)
    mn = w.s([nx, w.inst('dchrcondnn')], 'syl', '( %s -> %s e. NN )' % (A0, MC))
    two = a1(w, A0, '2rp', '2 e. RR+')
    rgt2 = w.s([nxp, w.inst('zl2ergt')], 'syl', '( %s -> %s )' % (A0, RGT('F', '2')))
    lft2 = w.s([nxp, w.inst('zl2elft')], 'syl', '( %s -> %s )' % (A0, LFT('F', '2', MC)))
    HC2 = subst(HCVX, {'N': MC, 'A': '2'})
    hc = w.s([w.s([w.s([mn, two], 'jca', '( %s -> ( %s e. NN /\\ 2 e. RR+ ) )' % (A0, MC)), P['hol3']], 'jca', '( %s -> ( ( %s e. NN /\\ 2 e. RR+ ) /\\ %s ) )' % (A0, MC, HOL3)),
              w.s([P['grw'], w.s([rgt2, lft2], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, RGT('F', '2'), LFT('F', '2', MC)))], 'jca', '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (A0, GRW, RGT('F', '2'), LFT('F', '2', MC)))], 'jca',
             '( %s -> %s )' % (A0, HC2))
    CX2 = subst(STATEMENTS['zl2cvx'], {'N': MC, 'A': '2'})
    ANT, CON = split_imp(CX2)
    assert ANT == '( %s /\\ %s )' % (HC2, SRNG2()), ANT
    assert CON == split_imp(STATEMENTS['zl2ecvx'])[1], (CON, split_imp(STATEMENTS['zl2ecvx'])[1])
    w.qed([w.s([hc, sr], 'jca', '( %s -> %s )' % (A0, ANT)), w.inst('zl2cvx')], 'syl', STATEMENTS['zl2ecvx'])
    go(w, only)


# ---------------------------------------------------------------- zl2cvxe
if __name__ == '__main__' and (not only or 'zl2cvxe' in only):
    w = W('zl2cvxe', 'The convexity bound CVXH for ` ( N DChrLF X ) ` from a primitive continuation ` F ` at the conductor ( PCONT ): '
          '` | E ( s ) / ( s - 1 ) | <_ 200000 2 ^ omega ( N ) ( ( N ( | Im s | + 2 ) ) ^ max ( ( 1 - Re s ) / 2 , 0 ) log ( N ( | Im s | + 3 ) ) + 1 / | s - 1 | ) ` '
          'on ` 1 / 200 <_ Re s <_ 2 ` , ` s =/= 1 ` ( ~ zl2lfe , ~ zl2ecvx , ~ zl2dpb ; Lean ` norm_LFunction_le_convexity_all ` , its ` LFunction_eq_primitive_mul_prod ` and '
          '` norm_prod_euler_factors_le ` ).')
    A0 = NXP
    As = '( %s /\\ s e. %s )' % (A0, HPZ); RS = '( Re ` s )'
    CND3 = '( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 /\\ s =/= 1 )' % (RS, RS)
    A1 = '( %s /\\ %s )' % (As, CND3)
    nxp = D(w, A1, 'simpll', [], NXP); shp = D(w, A1, 'simplr', [], 's e. %s' % HPZ); cnd = D(w, A1, 'simpr', [], CND3)
    c1 = D(w, A1, 'simp1d', [cnd], '( 1 / ; ; 2 0 0 ) <_ %s' % RS); c2 = D(w, A1, 'simp2d', [cnd], '%s <_ 2' % RS); sne = D(w, A1, 'simp3d', [cnd], 's =/= 1')
    nx = D(w, A1, 'simpld', [nxp], NXL); pc = D(w, A1, 'simprd', [nxp], PCONT); P = pcparts(w, A1, pc)
    nn = D(w, A1, 'simpld', [nx], 'N e. NN')
    hb = w.s([shp, w.s([a1(w, A1, '0re', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s -> ( s e. %s <-> ( s e. CC /\\ 0 < %s ) ) )' % (A1, HPZ, RS))], 'mpbid', '( %s -> ( s e. CC /\\ 0 < %s ) )' % (A1, RS))
    sc = D(w, A1, 'simpld', [hb], 's e. CC'); s0 = D(w, A1, 'simprd', [hb], '0 < %s' % RS)
    rsr = D(w, A1, 'recld', [sc], '%s e. RR' % RS)
    mn = w.s([nx, w.inst('dchrcondnn')], 'syl', '( %s -> %s e. NN )' % (A1, MC))
    rng = w.s([sc, w.s([c1, c2], 'jca', '( %s -> ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 ) )' % (A1, RS, RS))], 'jca', '( %s -> ( s e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 ) ) )' % (A1, RS, RS))
    LFS = '( %s ` s )' % LF
    lfe = w.s([nxp, rng, w.inst('zl2lfe')], 'syl2anc', '( %s -> %s = %s )' % (A1, LFS, GPR('s')))
    Cm = CXB('s', MC); Cn = CXB('s', 'N')
    ecv = w.s([nxp, rng, w.inst('zl2ecvx')], 'syl2anc', '( %s -> ( abs ` ( F ` s ) ) <_ ( ( %s x. 2 ) x. %s ) )' % (A1, C5E, Cm))
    s0le = D(w, A1, 'ltled', [a1(w, A1, '0re', '0 e. RR'), rsr, s0], '0 <_ %s' % RS)
    dpb = w.s([nx, w.s([sc, s0le], 'jca', '( %s -> ( s e. CC /\\ 0 <_ %s ) )' % (A1, RS)), w.inst('zl2dpb')], 'syl2anc', '( %s -> ( abs ` %s ) <_ %s )' % (A1, PFS('s'), OMGN))
    dpv = w.s([sc, w.inst('zl2dpv')], 'syl', '( %s -> ( %s ` s ) = %s )' % (A1, PF, PFS('s')))
    PS = '( %s ` s )' % PF
    apb = w.s([E(w, A1, 'fveq2d', [dpv], '( abs ` %s )' % PS, '( abs ` %s )' % PFS('s')), dpb], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A1, PS, OMGN))
    Sm = '( s - 1 )'; FS = '( F ` s )'; Q = '( %s / %s )' % (RP, Sm)
    smc = D(w, A1, 'subcld', [sc, a1(w, A1, 'ax-1cn', '1 e. CC')], '%s e. CC' % Sm)
    smne = D(w, A1, 'subne0d', [sc, a1(w, A1, 'ax-1cn', '1 e. CC'), sne], '%s =/= 0' % Sm)
    r2rp, r2r = recip(w, A1, '200')
    lo = linarith(w, A1, [c1, D(w, A1, 'rpgt0d', [r2rp], '0 < ( 1 / ; ; 2 0 0 )')], '-u ( 1 / 2 ) <_ %s' % RS, leaves={RS: rsr, '( 1 / ; ; 2 0 0 )': r2r})
    fsc, sst, su = instr(w, A1, 's', sc, lo, c2, P['stru'], P['ff'])
    pff = w.s([D(w, A1, 'simpld', [w.s([nx, w.inst('zl2dph')], 'syl', '( %s -> %s )' % (A1, HOL(PF, 'CC')))], '%s e. ( CC -cn-> CC )' % PF), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (A1, PF))
    psc = D(w, A1, 'ffvelcdmd', [pff, sc], '%s e. CC' % PS)
    rpc = rpcl(w, A1); qc = D(w, A1, 'divcld', [rpc, smc, smne], '%s e. CC' % Q); fqc = D(w, A1, 'addcld', [fsc, qc], '( %s + %s ) e. CC' % (FS, Q))
    NUM = '( ( %s x. %s ) + %s )' % (Sm, FS, RP)
    smf = D(w, A1, 'mulcld', [smc, fsc], '( %s x. %s ) e. CC' % (Sm, FS)); numc = D(w, A1, 'addcld', [smf, rpc], '%s e. CC' % NUM)
    d1 = E(w, A1, 'oveq1d', [lfe], '( %s / %s )' % (LFS, Sm), '( %s / %s )' % (GPR('s'), Sm))
    d2 = D(w, A1, 'div23d', [numc, psc, smc, smne], '( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s )' % (NUM, PS, Sm, NUM, Sm, PS))
    d3 = D(w, A1, 'divdird', [smf, rpc, smc, smne], '( %s / %s ) = ( ( ( %s x. %s ) / %s ) + %s )' % (NUM, Sm, Sm, FS, Sm, Q))
    d4 = D(w, A1, 'divcan3d', [fsc, smc, smne], '( ( %s x. %s ) / %s ) = %s' % (Sm, FS, Sm, FS))
    d6 = w.s([d3, E(w, A1, 'oveq1d', [d4], '( ( ( %s x. %s ) / %s ) + %s )' % (Sm, FS, Sm, Q), '( %s + %s )' % (FS, Q))], 'eqtrd', '( %s -> ( %s / %s ) = ( %s + %s ) )' % (A1, NUM, Sm, FS, Q))
    d7 = E(w, A1, 'oveq1d', [d6], '( ( %s / %s ) x. %s )' % (NUM, Sm, PS), '( ( %s + %s ) x. %s )' % (FS, Q, PS))
    dv = chain(w, A1, ['( %s / %s )' % (LFS, Sm), '( %s / %s )' % (GPR('s'), Sm), '( ( %s / %s ) x. %s )' % (NUM, Sm, PS), '( ( %s + %s ) x. %s )' % (FS, Q, PS)], [d1, d2, d7])
    Wm = '( abs ` ( %s + %s ) )' % (FS, Q); APS = '( abs ` %s )' % PS; AFS = '( abs ` %s )' % FS; AQ = '( abs ` %s )' % Q
    ab1 = D(w, A1, 'absmuld', [fqc, psc], '( abs ` ( ( %s + %s ) x. %s ) ) = ( %s x. %s )' % (FS, Q, PS, Wm, APS))
    abe = w.s([E(w, A1, 'fveq2d', [dv], '( abs ` ( %s / %s ) )' % (LFS, Sm), '( abs ` ( ( %s + %s ) x. %s ) )' % (FS, Q, PS)), ab1], 'eqtrd', '( %s -> ( abs ` ( %s / %s ) ) = ( %s x. %s ) )' % (A1, LFS, Sm, Wm, APS))
    tri = D(w, A1, 'abstrid', [fsc, qc], '%s <_ ( %s + %s )' % (Wm, AFS, AQ))
    aq = D(w, A1, 'absdivd', [rpc, smc, smne], '%s = ( ( abs ` %s ) / ( abs ` %s ) )' % (AQ, RP, Sm))
    asmrp = D(w, A1, 'absrpcld', [smc, smne], '( abs ` %s ) e. RR+' % Sm)
    ra1 = rpabs1(w, A1)
    R1 = '( 1 / ( abs ` %s ) )' % Sm
    q1 = D(w, A1, 'lediv1dd', [D(w, A1, 'abscld', [rpc], '( abs ` %s ) e. RR' % RP), a1(w, A1, '1re', '1 e. RR'), asmrp, ra1], '( ( abs ` %s ) / ( abs ` %s ) ) <_ %s' % (RP, Sm, R1))
    qle = w.s([aq, q1], 'eqbrtrd', '( %s -> %s <_ %s )' % (A1, AQ, R1))
    r1rp = D(w, A1, 'rpreccld', [asmrp], '%s e. RR+' % R1); r1r = D(w, A1, 'rpred', [r1rp], '%s e. RR' % R1); r10 = D(w, A1, 'rpge0d', [r1rp], '0 <_ %s' % R1)
    # CXB monotone in the modulus
    mz = D(w, A1, 'nnzd', [mn], '%s e. ZZ' % MC)
    mle = w.s([w.s([nx, w.inst('dchrconddvdn')], 'syl', '( %s -> %s || N )' % (A1, MC)), w.s([mz, nn, w.inst('dvdsle')], 'syl2anc', '( %s -> ( %s || N -> %s <_ N ) )' % (A1, MC, MC))], 'mpd', '( %s -> %s <_ N )' % (A1, MC))
    mr = D(w, A1, 'nnred', [mn], '%s e. RR' % MC); nr = D(w, A1, 'nnred', [nn], 'N e. RR'); m1_ = D(w, A1, 'nnge1d', [mn], '1 <_ %s' % MC); m0 = D(w, A1, 'nnnn0d', [mn], '%s e. NN0' % MC)
    m0 = D(w, A1, 'nn0ge0d', [m0], '0 <_ %s' % MC)
    isc = D(w, A1, 'recnd', [D(w, A1, 'imcld', [sc], '( Im ` s ) e. RR')], '( Im ` s ) e. CC')
    ais = D(w, A1, 'abscld', [isc], '( abs ` ( Im ` s ) ) e. RR'); ais0 = D(w, A1, 'absge0d', [isc], '0 <_ ( abs ` ( Im ` s ) )')
    I2 = '( ( abs ` ( Im ` s ) ) + 2 )'; I3 = '( ( abs ` ( Im ` s ) ) + 3 )'
    i2r = D(w, A1, 'readdcld', [ais, a1(w, A1, '2re', '2 e. RR')], '%s e. RR' % I2); i3r = D(w, A1, 'readdcld', [ais, a1(w, A1, '3re', '3 e. RR')], '%s e. RR' % I3)
    i20 = linarith(w, A1, [ais0], '0 <_ %s' % I2, leaves={'( abs ` ( Im ` s ) )': ais}); i30 = linarith(w, A1, [ais0], '0 < %s' % I3, leaves={'( abs ` ( Im ` s ) )': ais})
    i31 = linarith(w, A1, [ais0], '1 <_ %s' % I3, leaves={'( abs ` ( Im ` s ) )': ais})
    QTM = QT('s', MC); QTN = QT('s', 'N'); QLM = QL('s', MC); QLN = QL('s', 'N'); EXP = EXPO('s')
    base = D(w, A1, 'lemul1ad', [mr, nr, i2r, i20, mle], '%s <_ %s' % (QTM, QTN))
    qtmr = D(w, A1, 'remulcld', [mr, i2r], '%s e. RR' % QTM); qtnr = D(w, A1, 'remulcld', [nr, i2r], '%s e. RR' % QTN)
    qtm0 = D(w, A1, 'mulge0d', [mr, i2r, m0, i20], '0 <_ %s' % QTM); qtn0 = D(w, A1, 'mulge0d', [nr, i2r, D(w, A1, 'nn0ge0d', [D(w, A1, 'nnnn0d', [nn], 'N e. NN0')], '0 <_ N'), i20], '0 <_ %s' % QTN)
    OMR = '( 1 - %s )' % RS; omr = D(w, A1, 'resubcld', [a1(w, A1, '1re', '1 e. RR'), rsr], '%s e. RR' % OMR)
    HL = '( %s / 2 )' % OMR; hlr = D(w, A1, 'redivcld', [omr, a1(w, A1, '2re', '2 e. RR'), a1(w, A1, '2ne0', '2 =/= 0')], '%s e. RR' % HL)
    expor = D(w, A1, 'ifcld', [a1(w, A1, '0re', '0 e. RR'), hlr], '%s e. RR' % EXP)
    At = '( %s /\\ 1 <_ %s )' % (A1, RS); Af = '( %s /\\ -. 1 <_ %s )' % (A1, RS)
    et0 = D(w, At, 'iftrued', [D(w, At, 'simpr', [], '1 <_ %s' % RS)], '%s = 0' % EXP)
    et = w.s([a1(w, At, '0le0', '0 <_ 0'), et0], 'breqtrrd', '( %s -> 0 <_ %s )' % (At, EXP))
    ef0 = D(w, Af, 'iffalsed', [D(w, Af, 'simpr', [], '-. 1 <_ %s' % RS)], '%s = %s' % (EXP, HL))
    rlt = w.s([D(w, Af, 'simpr', [], '-. 1 <_ %s' % RS), D(w, Af, 'ltnled', [w.s([rsr], 'adantr', '( %s -> %s e. RR )' % (Af, RS)), a1(w, Af, '1re', '1 e. RR')], '( %s < 1 <-> -. 1 <_ %s )' % (RS, RS))], 'mpbird', '( %s -> %s < 1 )' % (Af, RS))
    om0 = linarith(w, Af, [rlt], '0 <_ %s' % OMR, leaves={RS: w.s([rsr], 'adantr', '( %s -> %s e. RR )' % (Af, RS))})
    hl0 = D(w, Af, 'divge0d', [w.s([omr], 'adantr', '( %s -> %s e. RR )' % (Af, OMR)), a1(w, Af, '2rp', '2 e. RR+'), om0], '0 <_ %s' % HL)
    ef = w.s([hl0, ef0], 'breqtrrd', '( %s -> 0 <_ %s )' % (Af, EXP))
    e0 = w.s([et, ef], 'pm2.61dan', '( %s -> 0 <_ %s )' % (A1, EXP))
    PM = '( %s ^c %s )' % (QTM, EXP); PN = '( %s ^c %s )' % (QTN, EXP); LM = '( log ` %s )' % QLM; LN = '( log ` %s )' % QLN
    p1 = D(w, A1, 'cxple2ad', [qtmr, qtm0, qtnr, expor, e0, base], '%s <_ %s' % (PM, PN))
    lb = D(w, A1, 'lemul1ad', [mr, nr, i3r, D(w, A1, 'ltled', [a1(w, A1, '0re', '0 e. RR'), i3r, i30], '0 <_ %s' % I3), mle], '%s <_ %s' % (QLM, QLN))
    i3rp = D(w, A1, 'elrpd', [i3r, i30], '%s e. RR+' % I3)
    qlmrp = D(w, A1, 'rpmulcld', [D(w, A1, 'nnrpd', [mn], '%s e. RR+' % MC), i3rp], '%s e. RR+' % QLM); qlnrp = D(w, A1, 'rpmulcld', [D(w, A1, 'nnrpd', [nn], 'N e. RR+'), i3rp], '%s e. RR+' % QLN)
    l1 = w.s([lb, D(w, A1, 'logled', [qlmrp, qlnrp], '( %s <_ %s <-> %s <_ %s )' % (QLM, QLN, LM, LN))], 'mpbid', '( %s -> %s <_ %s )' % (A1, LM, LN))
    qlm1 = w.s([a1(w, A1, '1t1e1', '( 1 x. 1 ) = 1'), D(w, A1, 'lemul12ad', [a1(w, A1, '1re', '1 e. RR'), mr, a1(w, A1, '1re', '1 e. RR'), i3r, a1(w, A1, '0le1', '0 <_ 1'), a1(w, A1, '0le1', '0 <_ 1'), m1_, i31], '( 1 x. 1 ) <_ %s' % QLM)], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (A1, QLM))
    qlmr = D(w, A1, 'rpred', [qlmrp], '%s e. RR' % QLM)
    lm0 = D(w, A1, 'logge0d', [qlmr, qlm1], '0 <_ %s' % LM)
    pmr = D(w, A1, 'recxpcld', [qtmr, qtm0, expor], '%s e. RR' % PM); pm0 = D(w, A1, 'cxpge0d', [qtmr, qtm0, expor], '0 <_ %s' % PM)
    pnr = D(w, A1, 'recxpcld', [qtnr, qtn0, expor], '%s e. RR' % PN); pn0 = D(w, A1, 'cxpge0d', [qtnr, qtn0, expor], '0 <_ %s' % PN)
    lmr = D(w, A1, 'relogcld', [qlmrp], '%s e. RR' % LM); lnr = D(w, A1, 'relogcld', [qlnrp], '%s e. RR' % LN)
    ln0 = D(w, A1, 'letrd', [a1(w, A1, '0re', '0 e. RR'), lmr, lnr, lm0, l1], '0 <_ %s' % LN)
    cmn = D(w, A1, 'lemul12ad', [pmr, pnr, lmr, lnr, pm0, lm0, p1, l1], '%s <_ %s' % (Cm, Cn))
    assert Cm == '( %s x. %s )' % (PM, LM) and Cn == '( %s x. %s )' % (PN, LN)
    cmr = D(w, A1, 'remulcld', [pmr, lmr], '%s e. RR' % Cm); cnr = D(w, A1, 'remulcld', [pnr, lnr], '%s e. RR' % Cn)
    # the constant 100000 x. 2 = 200000
    K2 = '; ; ; ; ; 2 0 0 0 0 0'
    ml = num.mul_lits(w, C5E, '2')
    mle_ = w.s([ml], 'a1i', '( %s -> ( %s x. 2 ) = %s )' % (A1, C5E, K2))
    ecv2 = w.s([ecv, E(w, A1, 'oveq1d', [mle_], '( ( %s x. 2 ) x. %s )' % (C5E, Cm), '( %s x. %s )' % (K2, Cm))], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A1, AFS, K2, Cm))
    # assemble
    afs = D(w, A1, 'abscld', [fsc], '%s e. RR' % AFS); aqr = D(w, A1, 'abscld', [qc], '%s e. RR' % AQ)
    wr = D(w, A1, 'abscld', [fqc], '%s e. RR' % Wm); w0 = D(w, A1, 'absge0d', [fqc], '0 <_ %s' % Wm)
    apsr = D(w, A1, 'abscld', [psc], '%s e. RR' % APS); aps0 = D(w, A1, 'absge0d', [psc], '0 <_ %s' % APS)
    PRM = '{ p e. Prime | p || N }'
    hn0 = w.s([w.s([nn, w.inst('prmdvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A1, PRM)), w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A1, PRM))
    omn0 = D(w, A1, 'nn0expcld', [a1(w, A1, '2nn0', '2 e. NN0'), hn0], '%s e. NN0' % OMGN)
    omgr = D(w, A1, 'nn0red', [omn0], '%s e. RR' % OMGN); omg0 = D(w, A1, 'nn0ge0d', [omn0], '0 <_ %s' % OMGN)
    sumr = D(w, A1, 'readdcld', [afs, aqr], '( %s + %s ) e. RR' % (AFS, AQ))
    m1 = D(w, A1, 'lemul12ad', [wr, sumr, apsr, omgr, w0, aps0, tri, apb], '( %s x. %s ) <_ ( ( %s + %s ) x. %s )' % (Wm, APS, AFS, AQ, OMGN))
    k2r, k20 = relit(w, A1, '200000')
    cl = Closure(w, A1, {AFS: ('RR', afs), AQ: ('RR', aqr), Cm: ('RR', cmr), Cn: ('RR', cnr), R1: ('RR', r1r)}); cl.atom(Cm); cl.atom(Cn); cl.atom(R1); cl.atom(AQ)
    BND = '( ( %s x. %s ) + %s )' % (K2, Cn, R1)
    lin1 = linarith(w, A1, [ecv2, cmn, qle], '( %s + %s ) <_ %s' % (AFS, AQ, BND), closure=cl)
    bndr = D(w, A1, 'readdcld', [D(w, A1, 'remulcld', [k2r, cnr], '( %s x. %s ) e. RR' % (K2, Cn)), r1r], '%s e. RR' % BND)
    m2 = D(w, A1, 'lemul1ad', [sumr, bndr, omgr, omg0, lin1], '( ( %s + %s ) x. %s ) <_ ( %s x. %s )' % (AFS, AQ, OMGN, BND, OMGN))
    pos = D(w, A1, 'mulge0d', [r1r, omgr, r10, omg0], '0 <_ ( %s x. %s )' % (R1, OMGN))
    clf = Closure(w, A1, {Cn: ('RR', cnr), R1: ('RR', r1r), OMGN: ('RR', omgr)}); clf.atom(Cn); clf.atom(R1); clf.atom(OMGN)
    FINAL = '( ( %s x. %s ) x. ( %s + %s ) )' % (K2, OMGN, Cn, R1)
    assert FINAL == Z6A.CVXB('s'), (FINAL, Z6A.CVXB('s'))
    m3 = linarith(w, A1, [pos], '( %s x. %s ) <_ %s' % (BND, OMGN, FINAL), closure=clf, products=True)
    wp = D(w, A1, 'remulcld', [wr, apsr], '( %s x. %s ) e. RR' % (Wm, APS)); sp = D(w, A1, 'remulcld', [sumr, omgr], '( ( %s + %s ) x. %s ) e. RR' % (AFS, AQ, OMGN)); bp = D(w, A1, 'remulcld', [bndr, omgr], '( %s x. %s ) e. RR' % (BND, OMGN))
    finr = D(w, A1, 'remulcld', [D(w, A1, 'remulcld', [k2r, omgr], '( %s x. %s ) e. RR' % (K2, OMGN)), D(w, A1, 'readdcld', [cnr, r1r], '( %s + %s ) e. RR' % (Cn, R1))], '%s e. RR' % FINAL)
    t1 = D(w, A1, 'letrd', [wp, sp, bp, m1, m2], '( %s x. %s ) <_ ( %s x. %s )' % (Wm, APS, BND, OMGN))
    t2 = D(w, A1, 'letrd', [wp, bp, finr, t1, m3], '( %s x. %s ) <_ %s' % (Wm, APS, FINAL))
    fin = w.s([abe, t2], 'eqbrtrd', '( %s -> ( abs ` ( %s / %s ) ) <_ %s )' % (A1, LFS, Sm, FINAL))
    BODY = '( %s -> ( abs ` ( %s / %s ) ) <_ %s )' % (CND3, LFS, Sm, FINAL)
    assert 'A. s e. %s %s' % (HPZ, BODY) == CVXHX, (BODY, CVXHX)
    w.qed([w.s([fin], 'ex', '( %s -> %s )' % (As, BODY))], 'ralrimiva', STATEMENTS['zl2cvxe'])
    go(w, only)
