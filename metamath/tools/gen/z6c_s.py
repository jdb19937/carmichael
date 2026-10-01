"""Sortie Z6c, section 6: the detector sum split (Lean summable_Sterm, ofReal_Pfun, sum_Rset_Sterm, tsum_detector_split).
z6stcv   the per-modulus series converges (majorant R n q ^ n, z6geo)
z6fdvcl  the detector value is a complex number
z6hval   sum_r ( 1 / r ) STERM ( r , M ) = XM ( M )
z6xcut   the cut z1 < M is invisible for M >_ 2
z6x1     XM ( 1 ) = e ^ ( -1 / X ) P ( 1 ), the detector's first term is 0
z6split  FDV + e ^ ( -1 / X ) P ( 1 ) = sum_r ( 1 / r ) sum_n STERM ( r , n )
Run: MM_DB=sorties/z6c.mm LIN_FAST=1 python3 tools/gen/z6c_s.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6clib import *
from tm import sub
from cl import split_imp, lift, formula_of
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import mpval, toqed
import lin
from lin import linarith
import num

only = sys.argv[1:]
NNUZ = 'NN = ( ZZ>= ` 1 )'
HAB = sub(HAB0, {'A': Z1D, 'B': Z2D})
X = XPD
PSI_ = lambda r, m: '( ( mmu ` ( %s gcd %s ) ) x. ( phi ` ( %s gcd %s ) ) )' % (r, m, r, m)
BV = lambda m: '( ( %s bvA %s ) ` %s )' % (Z1D, Z2D, m)
EX = lambda m: '( exp ` ( -u %s / %s ) )' % (m, X)
PW = lambda m: '( %s ^c -u S )' % m
IFT = lambda m: 'if ( %s < %s , %s , 0 )' % (Z1D, m, XM(m))
IFF = '( n e. NN |-> %s )' % IFT('n')
GM = sub(GEOM, {'X': X})
Q = E1


def want(lab):
    return not only or lab in only


def cl1(w, a, ref, f):
    return c_(w, a, w.s([], ref, f), f)


def dfx(w, a, f):
    """record in f: D e. RR+, X e. RR+, z1 z2 e. RR+, z1 < z2, HAB, 1 <_ z1, RPD e. RR+"""
    st = mkst(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']
    drp = st([dr, linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    f['D e. RR+'] = drp
    f['%s e. RR+' % X] = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % X)
    f['%s e. RR+' % RPD] = st([drp, c_(w, a, num.real(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % RPD)
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D); z12 = st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))
    z1r = st([z1rp], 'rpred', '%s e. RR' % Z1D); z2r = st([z2rp], 'rpred', '%s e. RR' % Z2D)
    f['%s e. RR' % Z1D] = z1r; f['%s e. RR' % Z2D] = z2r; f['%s < %s' % (Z1D, Z2D)] = z12
    f[HAB] = st([st([z1r, st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
                 st([z2r, z12], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca', HAB)
    c3150 = '( ; 3 1 / ; 5 0 )'
    f['1 <_ %s' % Z1D] = st([dr, st([dr, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), d1], 'ltled', '1 <_ D') if False else
                              linarith(w, a, [d1], '1 <_ D', leaves={'D': dr}),
                              c_(w, a, num.real(w, c3150), '%s e. RR' % c3150), c_(w, a, num.le_lit(w, '0', c3150), '0 <_ %s' % c3150)], 'a5ge1cxp', '1 <_ %s' % Z1D)
    return f


def xrp(w, ctx, fl):
    return fl['%s e. RR+' % X]


def xmcc(w, ctx, fl, m, mn):
    """( ctx -> XM(m) e. CC ) and the closures of its factors; mn: ( ctx -> m e. NN )"""
    t = mkst(w, ctx)
    c = {}
    c['bv'] = t([t([t([fl[HAB], mn], 'jca', '( %s /\\ %s e. NN )' % (HAB, m)), w.inst('z5bvaabs')], 'syl', '( abs ` %s ) <_ %s' % (BV(m), m)), w.inst('z6absle')],
                'syl', '%s e. CC' % BV(m))
    nv = t([fl['N e. NN']], 'elexd', 'N e. _V') if False else t([t([fl['N e. NN']], 'nnred', 'N e. RR')], 'elexd', 'N e. _V')
    rv = t([t([fl['%s e. RR+' % RPD]], 'rpred', '%s e. RR' % RPD)], 'elexd', '%s e. _V' % RPD)
    c['pf'] = t([t([t([nv, rv], 'jca', '( N e. _V /\\ %s e. _V )' % RPD), mn], 'jca', '( ( N e. _V /\\ %s e. _V ) /\\ %s e. NN )' % (RPD, m)), w.inst('z5pfunre')], 'syl',
                '( %s ` %s ) e. RR' % (PFD, m))
    c['pfc'] = t([c['pf']], 'recnd', '( %s ` %s ) e. CC' % (PFD, m))
    xr = xrp(w, ctx, fl)
    mc = t([mn], 'nncnd', '%s e. CC' % m)
    c['emr'] = t([t([t([t([mn], 'nnred', '%s e. RR' % m)], 'renegcld', '-u %s e. RR' % m), xr], 'rerpdivcld', '( -u %s / %s ) e. RR' % (m, X))], 'rpefcld', '%s e. RR+' % EX(m))
    c['em'] = t([c['emr']], 'rpcnd', '%s e. CC' % EX(m))
    c['cm'] = t([fl['C : NN --> CC'], mn], 'ffvelcdmd', '( C ` %s ) e. CC' % m)
    c['pw'] = t([mc, t([fl['S e. CC']], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % PW(m))
    A1 = '( %s x. ( %s ` %s ) )' % (BV(m), PFD, m)
    A2 = '( %s x. %s )' % (A1, EX(m))
    A3 = '( %s x. ( C ` %s ) )' % (A2, m)
    s1 = t([c['bv'], c['pfc']], 'mulcld', '%s e. CC' % A1)
    s2 = t([s1, c['em']], 'mulcld', '%s e. CC' % A2)
    s3 = t([s2, c['cm']], 'mulcld', '%s e. CC' % A3)
    c['xm'] = t([s3, c['pw']], 'mulcld', '%s e. CC' % XM(m))
    return c


def stcc(w, ctx, fl, R, m, mn, rn):
    """( ctx -> STERM(R,m) e. CC ) with the factor closures"""
    t = mkst(w, ctx)
    c = {}
    c['bv'] = t([t([t([fl[HAB], mn], 'jca', '( %s /\\ %s e. NN )' % (HAB, m)), w.inst('z5bvaabs')], 'syl', '( abs ` %s ) <_ %s' % (BV(m), m)), w.inst('z6absle')],
                'syl', '%s e. CC' % BV(m))
    c['ps'] = t([t([rn, mn, w.inst('z5psiabs')], 'syl2anc', '( abs ` %s ) <_ %s' % (PSI_(R, m), R)), w.inst('z6absle')], 'syl', '%s e. CC' % PSI_(R, m))
    c['cm'] = t([fl['C : NN --> CC'], mn], 'ffvelcdmd', '( C ` %s ) e. CC' % m)
    CO = COEFG(Z1D, Z2D, R, m)
    c['bp'] = t([c['bv'], c['ps']], 'mulcld', '( %s x. %s ) e. CC' % (BV(m), PSI_(R, m)))
    c['co'] = t([c['bp'], c['cm']], 'mulcld', '%s e. CC' % CO)
    xr = xrp(w, ctx, fl)
    c['emr'] = t([t([t([t([mn], 'nnred', '%s e. RR' % m)], 'renegcld', '-u %s e. RR' % m), xr], 'rerpdivcld', '( -u %s / %s ) e. RR' % (m, X))], 'rpefcld', '%s e. RR+' % EX(m))
    c['em'] = t([c['emr']], 'rpcnd', '%s e. CC' % EX(m))
    c['pw'] = t([t([mn], 'nncnd', '%s e. CC' % m), t([fl['S e. CC']], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % PW(m))
    c['ep'] = t([c['em'], c['pw']], 'mulcld', '( %s x. %s ) e. CC' % (EX(m), PW(m)))
    c['st'] = t([c['co'], c['ep']], 'mulcld', '%s e. CC' % STERM(R, m))
    return c


def uz1(w, a, ak_step_fn, G, C):
    """from ( ( a /\\ k e. NN ) -> P(k) ) to ( ( a /\\ k e. ( ZZ>= ` 1 ) ) -> P(k) ); ak_step: the step under ( a /\\ k e. NN )"""
    raise NotImplementedError


def to_uz1(w, a, step, P):
    """step: ( ( a /\\ k e. NN ) -> P ); returns ( ( a /\\ k e. ( ZZ>= ` 1 ) ) -> P )"""
    am1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    kn1 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % am1), w.s([w.s([w.s([], 'nnuz', NNUZ)], 'eleq2i', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                   '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'syl', '( %s -> k e. NN )' % am1)
    ex = w.s([step], 'ex', '( %s -> ( k e. NN -> %s ) )' % (a, P))
    return w.s([w.s([ex], 'adantr', '( %s -> ( k e. NN -> %s ) )' % (am1, P)), kn1], 'mpd', '( %s -> %s )' % (am1, P))


# ================================================================== z6stcv
def z6stcv():
    w = W('z6stcv', 'The detector series at one modulus ` R ` converges (Lean ` summable_Sterm ` ): its terms are at most '
          '` R n q ^ n ` , ` q = e ^ ( -1 / X ) ` (~ z6acoef , ~ z6geo , ~ cvgcmpce ); no multiplicativity of ` C ` is used.')
    a = ante('z6stcv'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    geo = st([f['%s e. RR+' % X], w.inst('z6geo')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % GM)
    ak = '( %s /\\ k e. NN )' % a; t = mkst(w, ak); fl = LZ(w, f, ak)
    kn = t([], 'simpr', 'k e. NN'); fl['k e. NN'] = kn
    gv, _ = mpval(w, ak, 'm', 'NN0', '( m x. ( %s ^ m ) )' % Q, 'k', t([kn], 'nnnn0d', 'k e. NN0'))
    xr = fl['%s e. RR+' % X]
    m1x = t([cl1(w, ak, 'neg1rr', '-u 1 e. RR'), xr], 'rerpdivcld', '( -u 1 / %s ) e. RR' % X)
    qrp = t([m1x], 'rpefcld', '%s e. RR+' % Q)
    kr = t([kn], 'nnred', 'k e. RR')
    qk = t([t([qrp], 'rpred', '%s e. RR' % Q), t([kn], 'nnnn0d', 'k e. NN0')], 'reexpcld', '( %s ^ k ) e. RR' % Q)
    kqk = t([kr, qk], 'remulcld', '( k x. ( %s ^ k ) ) e. RR' % Q)
    greal = t([gv, kqk], 'eqeltrd', '( %s ` k ) e. RR' % GM)
    STF = STFR('R')
    sv, _ = mpval(w, ak, 'n', 'NN', STERM('R', 'n'), 'k', kn)
    c = stcc(w, ak, fl, 'R', 'k', kn, fl['R e. NN'])
    gcc = t([sv, c['st']], 'eqeltrd', '( %s ` k ) e. CC' % STF)
    CO = COEFG(Z1D, Z2D, 'R', 'k'); EK = EX('k'); PK = PW('k'); ST = STERM('R', 'k')
    CP = '( %s x. %s )' % (CO, PK)
    cpc = t([c['co'], c['pw']], 'mulcld', '%s e. CC' % CP)
    r1 = t([c['co'], c['em'], c['pw']], 'mul12d', '%s = ( %s x. %s )' % (ST, EK, CP))
    r2 = t([c['em'], cpc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (EK, CP, CP, EK))
    e = t([r1, r2], 'eqtrd', '%s = ( %s x. %s )' % (ST, CP, EK))
    ab1 = t([t([sv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (STF, ST)), t([e], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. %s ) )' % (ST, CP, EK))], 'eqtrd',
            '( abs ` ( %s ` k ) ) = ( abs ` ( %s x. %s ) )' % (STF, CP, EK))
    ab2 = t([cpc, c['em']], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CP, EK, CP, EK))
    ekr = t([c['emr']], 'rpred', '%s e. RR' % EK)
    ab3 = t([ekr, t([c['emr']], 'rpge0d', '0 <_ %s' % EK)], 'absidd', '( abs ` %s ) = %s' % (EK, EK))
    ab4 = t([ab3], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (CP, EK, CP, EK))
    abt = t([t([ab1, ab2], 'eqtrd', '( abs ` ( %s ` k ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (STF, CP, EK)), ab4], 'eqtrd',
            '( abs ` ( %s ` k ) ) = ( ( abs ` %s ) x. %s )' % (STF, CP, EK))
    ac, _ = applyn(w, ak, 'z6acoef', {'A': Z1D, 'B': Z2D, 'K': 'k'}, fl)
    rr = t([fl['R e. NN']], 'nnred', 'R e. RR')
    kR = t([kr, rr], 'remulcld', '( k x. R ) e. RR')
    m1 = t([t([cpc], 'abscld', '( abs ` %s ) e. RR' % CP), kR, ekr, t([c['emr']], 'rpge0d', '0 <_ %s' % EK), ac], 'lemul1ad',
           '( ( abs ` %s ) x. %s ) <_ ( ( k x. R ) x. %s )' % (CP, EK, EK))
    kc = t([kn], 'nncnd', 'k e. CC'); rc = t([rr], 'recnd', 'R e. CC')
    q1 = t([kc, rc, c['em']], 'mul32d', '( ( k x. R ) x. %s ) = ( ( k x. %s ) x. R )' % (EK, EK))
    q2 = t([t([kc, c['em']], 'mulcld', '( k x. %s ) e. CC' % EK), rc], 'mulcomd', '( ( k x. %s ) x. R ) = ( R x. ( k x. %s ) )' % (EK, EK))
    # EK = Q ^ k
    m1c = cl1(w, ak, 'neg1cn', '-u 1 e. CC')
    xc = t([xr], 'rpcnd', '%s e. CC' % X); xn = t([xr], 'rpne0d', '%s =/= 0' % X)
    d1 = t([kc, m1c, xc, xn], 'divassd', '( ( k x. -u 1 ) / %s ) = ( k x. ( -u 1 / %s ) )' % (X, X))
    d2 = t([t([kc, m1c], 'mulcomd', '( k x. -u 1 ) = ( -u 1 x. k )'), t([kc], 'mulm1d', '( -u 1 x. k ) = -u k')], 'eqtrd', '( k x. -u 1 ) = -u k')
    d3 = t([d2], 'oveq1d', '( ( k x. -u 1 ) / %s ) = ( -u k / %s )' % (X, X))
    d4 = t([d3, d1], 'eqtr3d', '( -u k / %s ) = ( k x. ( -u 1 / %s ) )' % (X, X))
    d5 = t([d4], 'fveq2d', '%s = ( exp ` ( k x. ( -u 1 / %s ) ) )' % (EK, X))
    d6 = t([t([m1x], 'recnd', '( -u 1 / %s ) e. CC' % X), t([kn], 'nnzd', 'k e. ZZ'), w.inst('efexp')], 'syl2anc',
           '( exp ` ( k x. ( -u 1 / %s ) ) ) = ( %s ^ k )' % (X, Q))
    ek = t([d5, d6], 'eqtrd', '%s = ( %s ^ k )' % (EK, Q))
    q3 = t([t([ek], 'oveq2d', '( k x. %s ) = ( k x. ( %s ^ k ) )' % (EK, Q))], 'oveq2d', '( R x. ( k x. %s ) ) = ( R x. ( k x. ( %s ^ k ) ) )' % (EK, Q))
    q4 = t([t([gv], 'eqcomd', '( k x. ( %s ^ k ) ) = ( %s ` k )' % (Q, GM))], 'oveq2d', '( R x. ( k x. ( %s ^ k ) ) ) = ( R x. ( %s ` k ) )' % (Q, GM))
    qq = t([t([t([q1, q2], 'eqtrd', '( ( k x. R ) x. %s ) = ( R x. ( k x. %s ) )' % (EK, EK)), q3], 'eqtrd',
              '( ( k x. R ) x. %s ) = ( R x. ( k x. ( %s ^ k ) ) )' % (EK, Q)), q4], 'eqtrd', '( ( k x. R ) x. %s ) = ( R x. ( %s ` k ) )' % (EK, GM))
    b0 = t([t([abt, m1], 'eqbrtrd', '( abs ` ( %s ` k ) ) <_ ( ( k x. R ) x. %s )' % (STF, EK)), qq], 'breqtrd', '( abs ` ( %s ` k ) ) <_ ( R x. ( %s ` k ) )' % (STF, GM))
    b2 = to_uz1(w, a, b0, '( abs ` ( %s ` k ) ) <_ ( R x. ( %s ` k ) )' % (STF, GM))
    rra = st([f['R e. NN']], 'nnred', 'R e. RR')
    w.qed([w.s([], 'nnuz', NNUZ), cl1(w, a, '1nn', '1 e. NN'), greal, gcc, geo, rra, b2], 'cvgcmpce', STATEMENTS['z6stcv'])
    return w


# ================================================================== z6fdvcl
def fdval(w, a, f):
    """( a -> FDV = sum_ n e. NN IFT(n) ) (z5fdetval)"""
    st = mkst(w, a)
    ov = lambda T: cl1(w, a, 'ovex', '%s e. _V' % T)
    cv = st([f['C : NN --> CC'], cl1(w, a, 'nnex', 'NN e. _V')], 'fexd', 'C e. _V')
    h = st([st([st([ov(Z1D), ov(Z2D)], 'jca', '( %s e. _V /\\ %s e. _V )' % (Z1D, Z2D)), st([ov(PFD), ov(X), cv], '3jca', '( %s e. _V /\\ %s e. _V /\\ C e. _V )' % (PFD, X))],
               'jca', '( ( %s e. _V /\\ %s e. _V ) /\\ ( %s e. _V /\\ %s e. _V /\\ C e. _V ) )' % (Z1D, Z2D, PFD, X)), f['S e. CC']], 'jca',
           '( ( ( %s e. _V /\\ %s e. _V ) /\\ ( %s e. _V /\\ %s e. _V /\\ C e. _V ) ) /\\ S e. CC )' % (Z1D, Z2D, PFD, X))
    return st([h, w.inst('z5fdetval')], 'syl', '%s = sum_ n e. NN %s' % (FDV, IFT('n')))


def ifcc(w, ctx, fl, m, mn):
    t = mkst(w, ctx)
    c = xmcc(w, ctx, fl, m, mn)
    return t([c['xm'], cl1(w, ctx, '0cn', '0 e. CC')], 'ifcld', '%s e. CC' % IFT(m)), c


def fdcvg(w, a, f):
    """( a -> seq 1 ( + , IFF ) e. dom ~~> ) (z5fdetcvg)"""
    st = mkst(w, a)
    g = dict(f)
    rp = f['%s e. RR+' % RPD]
    g['%s e. RR' % RPD] = st([rp], 'rpred', '%s e. RR' % RPD)
    g['0 <_ %s' % RPD] = st([rp], 'rpge0d', '0 <_ %s' % RPD)
    cv, co = applyn(w, a, 'z5fdetcvg', {'A': Z1D, 'B': Z2D, 'X': X, 'R': RPD, 'V': 'NN'}, g)
    from z6a_e3 import _split
    return st([cv], 'simprd', 'seq 1 ( + , %s ) e. dom ~~>' % IFF)


def z6fdvcl():
    w = W('z6fdvcl', 'The detector value ` F ( S ) ` is a complex number: its series converges (~ z5fdetval , ~ z5fdetcvg , ~ isumcl ).')
    a = ante('z6fdvcl'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    fv = fdval(w, a, f)
    cvg = fdcvg(w, a, f)
    am = '( %s /\\ m e. NN )' % a; t = mkst(w, am); fl = LZ(w, f, am)
    mn = t([], 'simpr', 'm e. NN')
    iv, _ = mpval(w, am, 'n', 'NN', IFT('n'), 'm', mn, exs=t([], 'ifexd' if False else 'fvexd', 'x') if False else None) if False else (None, None)
    ic, _ = ifcc(w, am, fl, 'm', mn)
    iv = ifval(w, am, 'm', mn, ic)
    s = st([w.s([], 'nnuz', NNUZ), cl1(w, a, '1z', '1 e. ZZ'), iv, ic, cvg], 'isumcl', 'sum_ m e. NN %s e. CC' % IFT('m'))
    cb = cbvsum_nm(w)
    w.qed([t_eq(w, a, fv, cb), s], 'eqeltrd' if False else 'eqeltrd', STATEMENTS['z6fdvcl']) if False else None
    e = st([fv, c_(w, a, cb, 'sum_ n e. NN %s = sum_ m e. NN %s' % (IFT('n'), IFT('m')))], 'eqtrd', '%s = sum_ m e. NN %s' % (FDV, IFT('m')))
    w.qed([e, s], 'eqeltrd', STATEMENTS['z6fdvcl'])
    return w


def ifval(w, ctx, m, mn, ic):
    """( ctx -> ( IFF ` m ) = IFT(m) ) by fvmptd3 (the value is an if: its set-hood from ic)"""
    t = mkst(w, ctx)
    exs = t([ic], 'elexd', '%s e. _V' % IFT(m))
    v, _ = mpval(w, ctx, 'n', 'NN', IFT('n'), m, mn, exs=exs)
    return v


def cbvsum_nm(w, frm='n', to='m', body=None):
    """closed: sum_ n e. NN IFT(n) = sum_ m e. NN IFT(m)"""
    body = body or IFT
    idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
    stp, val = w.congr(body(frm), {frm: to}, '%s = %s' % (frm, to), {frm: idx})
    assert val == body(to), val
    return w.s([stp], 'cbvsumv', 'sum_ %s e. NN %s = sum_ %s e. NN %s' % (frm, body(frm), to, body(to)))


def t_eq(*a):
    raise NotImplementedError


# ================================================================== z6hval
def rsetnn(w, ctx, fl, rmem, r='r'):
    """( ctx -> r e. NN ) and ( ctx -> ( mmu ` r ) =/= 0 ) from rmem: ( ctx -> r e. RSD )"""
    t = mkst(w, ctx)
    nv = t([t([fl['N e. NN']], 'nnred', 'N e. RR')], 'elexd', 'N e. _V')
    rv = t([t([fl['%s e. RR+' % RPD]], 'rpred', '%s e. RR' % RPD)], 'elexd', '%s e. _V' % RPD)
    EL = '( %s e. ( 1 ... ( |_ ` %s ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) )' % (r, RPD, r, r)
    bi = t([nv, rv, w.inst('z5elrset')], 'syl2anc', '( %s e. %s <-> %s )' % (r, RSD, EL))
    el = t([rmem, bi], 'mpbid', EL)
    rn = t([t([el], 'simpld', '%s e. ( 1 ... ( |_ ` %s ) )' % (r, RPD)), w.inst('elfznn')], 'syl', '%s e. NN' % r)
    mu = t([t([el], 'simprd', '( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 )' % (r, r))], 'simpld', '( mmu ` %s ) =/= 0' % r)
    return rn, mu, nv, rv


def z6hval():
    w = W('z6hval', 'The weighted ` r ` -sum of the per-modulus summands is the detector summand ` a ( M ) P ( M ) e ^ ( - M / X ) C ( M ) M ^ -S ` '
          '(Lean ` sum_Rset_Sterm ` , ` ofReal_Pfun ` ; ~ z5pfunval , ~ fsummulc1 ).')
    a = ante('z6hval'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    mn = f['M e. NN']
    cx = xmcc(w, a, f, 'M', mn)
    WW = '( %s x. ( ( C ` M ) x. ( %s x. %s ) ) )' % (BV('M'), EX('M'), PW('M'))
    ep = st([cx['em'], cx['pw']], 'mulcld', '( %s x. %s ) e. CC' % (EX('M'), PW('M')))
    cep = st([cx['cm'], ep], 'mulcld', '( ( C ` M ) x. ( %s x. %s ) ) e. CC' % (EX('M'), PW('M')))
    wc = st([cx['bv'], cep], 'mulcld', '%s e. CC' % WW)
    ar = '( %s /\\ r e. %s )' % (a, RSD); t = mkst(w, ar); fl = LZ(w, f, ar)
    rm = t([], 'simpr', 'r e. %s' % RSD)
    rn, mu, nv, rv = rsetnn(w, ar, fl, rm)
    PS = PSI_('r', 'M')
    ps = t([t([rn, fl['M e. NN'], w.inst('z5psiabs')], 'syl2anc', '( abs ` %s ) <_ r' % PS), w.inst('z6absle')], 'syl', '%s e. CC' % PS)
    bvl = lift(w, cx['bv'], ar); cml = lift(w, cx['cm'], ar); epl = lift(w, ep, ar); cepl = lift(w, cep, ar)
    ST = STERM('r', 'M')
    Y = '( %s x. %s )' % (EX('M'), PW('M'))
    # STERM = PS x. WW
    e1 = t([t([bvl, ps], 'mulcld', '( %s x. %s ) e. CC' % (BV('M'), PS)), cml, epl], 'mulassd',
           '%s = ( ( %s x. %s ) x. ( ( C ` M ) x. %s ) )' % (ST, BV('M'), PS, Y))
    e2 = t([t([bvl, ps], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (BV('M'), PS, PS, BV('M')))], 'oveq1d',
           '( ( %s x. %s ) x. ( ( C ` M ) x. %s ) ) = ( ( %s x. %s ) x. ( ( C ` M ) x. %s ) )' % (BV('M'), PS, Y, PS, BV('M'), Y))
    e3 = t([ps, bvl, cepl], 'mulassd', '( ( %s x. %s ) x. ( ( C ` M ) x. %s ) ) = ( %s x. %s )' % (PS, BV('M'), Y, PS, WW))
    se = t([t([e1, e2], 'eqtrd', '%s = ( ( %s x. %s ) x. ( ( C ` M ) x. %s ) )' % (ST, PS, BV('M'), Y)), e3], 'eqtrd', '%s = ( %s x. %s )' % (ST, PS, WW))
    rc = t([rn], 'nncnd', 'r e. CC'); r0 = t([rn], 'nnne0d', 'r =/= 0')
    ir = t([rc, r0], 'reccld', '( 1 / r ) e. CC')
    wcl = lift(w, wc, ar)
    f1 = t([se], 'oveq2d', '( ( 1 / r ) x. %s ) = ( ( 1 / r ) x. ( %s x. %s ) )' % (ST, PS, WW))
    f2 = t([t([ir, ps, wcl], 'mulassd', '( ( ( 1 / r ) x. %s ) x. %s ) = ( ( 1 / r ) x. ( %s x. %s ) )' % (PS, WW, PS, WW))], 'eqcomd',
           '( ( 1 / r ) x. ( %s x. %s ) ) = ( ( ( 1 / r ) x. %s ) x. %s )' % (PS, WW, PS, WW))
    f3 = t([t([ir, ps], 'mulcomd', '( ( 1 / r ) x. %s ) = ( %s x. ( 1 / r ) )' % (PS, PS)), t([ps, rc, r0], 'divrecd', '( %s / r ) = ( %s x. ( 1 / r ) )' % (PS, PS))],
           'eqtr4d', '( ( 1 / r ) x. %s ) = ( %s / r )' % (PS, PS))
    f4 = t([f3], 'oveq1d', '( ( ( 1 / r ) x. %s ) x. %s ) = ( ( %s / r ) x. %s )' % (PS, WW, PS, WW))
    per = t([t([f1, f2], 'eqtrd', '( ( 1 / r ) x. %s ) = ( ( ( 1 / r ) x. %s ) x. %s )' % (ST, PS, WW)), f4], 'eqtrd', '( ( 1 / r ) x. %s ) = ( ( %s / r ) x. %s )' % (ST, PS, WW))
    psr = t([ps, rc, r0], 'divcld', '( %s / r ) e. CC' % PS)
    s1 = st([per], 'sumeq2dv', 'sum_ r e. %s ( ( 1 / r ) x. %s ) = sum_ r e. %s ( ( %s / r ) x. %s )' % (RSD, ST, RSD, PS, WW))
    nv0 = st([st([f['N e. NN']], 'nnred', 'N e. RR')], 'elexd', 'N e. _V')
    rv0 = st([st([f['%s e. RR+' % RPD]], 'rpred', '%s e. RR' % RPD)], 'elexd', '%s e. _V' % RPD)
    fin = st([st([nv0, rv0, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RSD, RPD, RSD))], 'simprd', '%s e. Fin' % RSD)
    s2 = st([fin, wc, psr], 'fsummulc1', '( sum_ r e. %s ( %s / r ) x. %s ) = sum_ r e. %s ( ( %s / r ) x. %s )' % (RSD, PS, WW, RSD, PS, WW))
    pv = st([st([st([nv0, rv0], 'jca', '( N e. _V /\\ %s e. _V )' % RPD), mn], 'jca', '( ( N e. _V /\\ %s e. _V ) /\\ M e. NN )' % RPD), w.inst('z5pfunval')], 'syl',
            '( %s ` M ) = sum_ r e. %s ( %s / r )' % (PFD, RSD, PS))
    s3 = st([pv], 'oveq1d', '( ( %s ` M ) x. %s ) = ( sum_ r e. %s ( %s / r ) x. %s )' % (PFD, WW, RSD, PS, WW))
    sA = st([s1, st([s3, s2], 'eqtr2d' if False else 'eqtrd', '( ( %s ` M ) x. %s ) = sum_ r e. %s ( ( %s / r ) x. %s )' % (PFD, WW, RSD, PS, WW))], 'eqtr4d',
            'sum_ r e. %s ( ( 1 / r ) x. %s ) = ( ( %s ` M ) x. %s )' % (RSD, ST, PFD, WW))
    # ( PF x. WW ) = XM(M)
    P = '( %s ` M )' % PFD; B = BV('M'); CM = '( C ` M )'; E_ = EX('M'); PM = PW('M')
    U = '( %s x. %s )' % (B, P)
    g1 = st([cx['pfc'], cx['bv'], cep], 'mulassd', '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. %s )' % (P, B, CM, Y, P, WW))
    g2 = st([st([cx['pfc'], cx['bv']], 'mulcomd', '( %s x. %s ) = %s' % (P, B, U))], 'oveq1d', '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (P, B, CM, Y, U, CM, Y))
    uc = st([cx['bv'], cx['pfc']], 'mulcld', '%s e. CC' % U)
    g3 = st([st([cx['cm'], cx['em'], cx['pw']], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (CM, E_, PM, CM, Y))], 'eqcomd',
            '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (CM, Y, CM, E_, PM))
    g4 = st([g3], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (U, CM, Y, U, CM, E_, PM))
    ce = st([cx['cm'], cx['em']], 'mulcld', '( %s x. %s ) e. CC' % (CM, E_))
    g5 = st([st([uc, ce, cx['pw']], 'mulassd', '( ( %s x. ( %s x. %s ) ) x. %s ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (U, CM, E_, PM, U, CM, E_, PM))], 'eqcomd',
            '( %s x. ( ( %s x. %s ) x. %s ) ) = ( ( %s x. ( %s x. %s ) ) x. %s )' % (U, CM, E_, PM, U, CM, E_, PM))
    g6 = st([st([cx['cm'], cx['em']], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (CM, E_, E_, CM))], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (U, CM, E_, U, E_, CM))
    g7 = st([st([uc, cx['em'], cx['cm']], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (U, E_, CM, U, E_, CM))], 'eqcomd',
            '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (U, E_, CM, U, E_, CM))
    g67 = st([g6, g7], 'eqtrd', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (U, CM, E_, U, E_, CM))
    g8 = st([g67], 'oveq1d', '( ( %s x. ( %s x. %s ) ) x. %s ) = %s' % (U, CM, E_, PM, XM('M')))
    ch = st([g1], 'eqcomd', '( %s x. %s ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (P, WW, P, B, CM, Y))
    for s_, rhs in [(g2, '( %s x. ( %s x. %s ) )' % (U, CM, Y)), (g4, '( %s x. ( ( %s x. %s ) x. %s ) )' % (U, CM, E_, PM)),
                    (g5, '( ( %s x. ( %s x. %s ) ) x. %s )' % (U, CM, E_, PM)), (g8, XM('M'))]:
        ch = st([ch, s_], 'eqtrd', '( %s x. %s ) = %s' % (P, WW, rhs))
    w.qed([sA, ch], 'eqtrd', STATEMENTS['z6hval'])
    return w


# ================================================================== z6xcut
def z6xcut():
    w = W('z6xcut', 'For ` M >_ 2 ` the cut ` z1 < M ` of the detector does not change the summand: below ` z1 ` the coefficient ` a ( M ) ` vanishes '
          '(~ z5bva0 ; the ` k + 2 ` branch of Lean ` tsum_detector_split ` ).')
    a = ante('z6xcut'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    m2 = f['M e. ( ZZ>= ` 2 )']
    mn = st([m2, w.inst('eluz2nn')], 'syl', 'M e. NN')
    m1 = st([m2, w.inst('eluz2gt1')], 'syl', '1 < M')
    cx = xmcc(w, a, f, 'M', mn)
    an = '( %s /\\ -. %s < M )' % (a, Z1D); t = mkst(w, an); fl = LZ(w, f, an)
    le = t([t([], 'simpr', '-. %s < M' % Z1D), t([t([lift(w, mn, an)], 'nnred', 'M e. RR'), fl['%s e. RR' % Z1D]], 'lenltd', '( M <_ %s <-> -. %s < M )' % (Z1D, Z1D))],
           'mpbird', 'M <_ %s' % Z1D)
    h = t([t([t([fl['%s e. RR' % Z1D], fl['1 <_ %s' % Z1D]], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (Z1D, Z1D)),
              t([fl['%s e. RR' % Z2D], fl['%s < %s' % (Z1D, Z2D)]], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca',
             '( ( %s e. RR /\\ 1 <_ %s ) /\\ ( %s e. RR /\\ %s < %s ) )' % (Z1D, Z1D, Z2D, Z1D, Z2D)),
           t([lift(w, mn, an), t([lift(w, m1, an), le], 'jca', '( 1 < M /\\ M <_ %s )' % Z1D)], 'jca', '( M e. NN /\\ ( 1 < M /\\ M <_ %s ) )' % Z1D)], 'jca',
          '( ( ( %s e. RR /\\ 1 <_ %s ) /\\ ( %s e. RR /\\ %s < %s ) ) /\\ ( M e. NN /\\ ( 1 < M /\\ M <_ %s ) ) )' % (Z1D, Z1D, Z2D, Z1D, Z2D, Z1D))
    b0 = t([h, w.inst('z5bva0')], 'syl', '%s = 0' % BV('M'))
    P = '( %s ` M )' % PFD
    z1 = t([t([b0], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (BV('M'), P, P)), t([lift(w, cx['pfc'], an)], 'mul02d', '( 0 x. %s ) = 0' % P)], 'eqtrd', '( %s x. %s ) = 0' % (BV('M'), P))
    A1 = '( %s x. %s )' % (BV('M'), P)
    z2 = t([t([z1], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (A1, EX('M'), EX('M'))), t([lift(w, cx['em'], an)], 'mul02d', '( 0 x. %s ) = 0' % EX('M'))], 'eqtrd',
           '( %s x. %s ) = 0' % (A1, EX('M')))
    A2 = '( %s x. %s )' % (A1, EX('M'))
    z3 = t([t([z2], 'oveq1d', '( %s x. ( C ` M ) ) = ( 0 x. ( C ` M ) )' % A2), t([lift(w, cx['cm'], an)], 'mul02d', '( 0 x. ( C ` M ) ) = 0')], 'eqtrd',
           '( %s x. ( C ` M ) ) = 0' % A2)
    A3 = '( %s x. ( C ` M ) )' % A2
    z4 = t([t([z3], 'oveq1d', '%s = ( 0 x. %s )' % (XM('M'), PW('M'))), t([lift(w, cx['pw'], an)], 'mul02d', '( 0 x. %s ) = 0' % PW('M'))], 'eqtrd', '%s = 0' % XM('M'))
    z5 = t([z4], 'eqcomd', '0 = %s' % XM('M'))
    e = st([z5], 'ifeq2da', 'if ( %s < M , %s , 0 ) = if ( %s < M , %s , %s )' % (Z1D, XM('M'), Z1D, XM('M'), XM('M')))
    w.qed([e, cl1(w, a, 'ifid', 'if ( %s < M , %s , %s ) = %s' % (Z1D, XM('M'), XM('M'), XM('M')))], 'eqtrd', STATEMENTS['z6xcut'])
    return w


# ================================================================== z6x1
def p1dcc(w, a, f):
    """( a -> P1D e. CC )"""
    st = mkst(w, a)
    nv = st([st([f['N e. NN']], 'nnred', 'N e. RR')], 'elexd', 'N e. _V')
    rv = st([st([f['%s e. RR+' % RPD]], 'rpred', '%s e. RR' % RPD)], 'elexd', '%s e. _V' % RPD)
    fin = st([st([nv, rv, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RSD, RPD, RSD))], 'simprd', '%s e. Fin' % RSD)
    ar = '( %s /\\ r e. %s )' % (a, RSD); t = mkst(w, ar); fl = LZ(w, f, ar)
    rn, mu, _, _ = rsetnn(w, ar, fl, t([], 'simpr', 'r e. %s' % RSD))
    ir = t([t([rn], 'nncnd', 'r e. CC'), t([rn], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    return st([fin, ir], 'fsumcl', '%s e. CC' % P1D), fin, nv, rv


def z6x1():
    w = W('z6x1', 'The ` m = 1 ` summand is ` e ^ ( -1 / X ) P ( 1 ) ` (~ z5bva1 , ~ z5pfun1 , ` C ( 1 ) = 1 ` , ~ 1cxp ) and the detector\'s cut ` z1 < 1 ` removes it '
          '(the ` 1 ` branch of Lean ` tsum_detector_split ` ).')
    a = ante('z6x1'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    p1c, fin, nv, rv = p1dcc(w, a, f)
    bva1 = st([st([st([f['%s e. RR' % Z1D], f['1 <_ %s' % Z1D]], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (Z1D, Z1D)),
                   st([f['%s e. RR' % Z2D], f['%s < %s' % (Z1D, Z2D)]], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca',
                  '( ( %s e. RR /\\ 1 <_ %s ) /\\ ( %s e. RR /\\ %s < %s ) )' % (Z1D, Z1D, Z2D, Z1D, Z2D)), w.inst('z5bva1')], 'syl', '%s = 1' % BV('1'))
    pf1 = st([nv, rv, w.inst('z5pfun1')], 'syl2anc', '( %s ` 1 ) = %s' % (PFD, P1D))
    c1 = f['( C ` 1 ) = 1']
    cx1 = st([st([f['S e. CC']], 'negcld', '-u S e. CC'), w.inst('1cxp')], 'syl', '( 1 ^c -u S ) = 1')
    rules = {BV('1'): ('1', bva1), '( %s ` 1 )' % PFD: (P1D, pf1), '( C ` 1 )': ('1', c1), '( 1 ^c -u S )': ('1', cx1)}
    r0, new = w.rewrite(XM('1'), rules, a)
    V1 = '( ( ( ( 1 x. %s ) x. %s ) x. 1 ) x. 1 )' % (P1D, E1)
    assert new == V1, new
    xr = f['%s e. RR+' % X]
    e1c = st([st([st([cl1(w, a, 'neg1rr', '-u 1 e. RR'), xr], 'rerpdivcld', '( -u 1 / %s ) e. RR' % X)], 'rpefcld', '%s e. RR+' % E1)], 'rpcnd', '%s e. CC' % E1)
    pe = st([p1c, e1c], 'mulcld', '( %s x. %s ) e. CC' % (P1D, E1))
    h1 = st([p1c], 'mullidd', '( 1 x. %s ) = %s' % (P1D, P1D))
    h2 = st([h1], 'oveq1d', '( ( 1 x. %s ) x. %s ) = ( %s x. %s )' % (P1D, E1, P1D, E1))
    h3 = st([h2], 'oveq1d', '( ( ( 1 x. %s ) x. %s ) x. 1 ) = ( ( %s x. %s ) x. 1 )' % (P1D, E1, P1D, E1))
    h4 = st([h3, st([pe], 'mulridd', '( ( %s x. %s ) x. 1 ) = ( %s x. %s )' % (P1D, E1, P1D, E1))], 'eqtrd', '( ( ( 1 x. %s ) x. %s ) x. 1 ) = ( %s x. %s )' % (P1D, E1, P1D, E1))
    h5 = st([h4], 'oveq1d', '%s = ( ( %s x. %s ) x. 1 )' % (V1, P1D, E1))
    h6 = st([h5, st([pe], 'mulridd', '( ( %s x. %s ) x. 1 ) = ( %s x. %s )' % (P1D, E1, P1D, E1))], 'eqtrd', '%s = ( %s x. %s )' % (V1, P1D, E1))
    h7 = st([h6, st([p1c, e1c], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (P1D, E1, E1, P1D))], 'eqtrd', '%s = ( %s x. %s )' % (V1, E1, P1D))
    x1 = st([r0, h7], 'eqtrd', '%s = ( %s x. %s )' % (XM('1'), E1, P1D))
    nl = st([f['1 <_ %s' % Z1D], st([f['%s e. RR' % Z1D], cl1(w, a, '1re', '1 e. RR')], 'lenltd', '( 1 <_ %s <-> -. %s < 1 )' % (Z1D, Z1D))], 'mpbid', '-. %s < 1' % Z1D)
    i0 = st([nl], 'iffalsed', '%s = 0' % IFT('1'))
    w.qed([x1, i0], 'jca', STATEMENTS['z6x1'])
    return w


# ================================================================== z6split
HF = '( m e. NN |-> sum_ r e. %s ( ( 1 / r ) x. ( %s ` m ) ) )' % (RSD, STFR('r'))
RHS = 'sum_ r e. %s ( ( 1 / r ) x. %s )' % (RSD, SSUM('r'))


def hfval(w, ctx, fl, T, Tn):
    """( ctx -> ( HF ` T ) = XM(T) ): fvmpt, the inner values, z6hval"""
    t = mkst(w, ctx)
    INNER = 'sum_ r e. %s ( ( 1 / r ) x. ( %s ` %s ) )' % (RSD, STFR('r'), T)
    idx = w.s([], 'id', '( m = %s -> m = %s )' % (T, T))
    v, val = mpval(w, ctx, 'm', 'NN', 'sum_ r e. %s ( ( 1 / r ) x. ( %s ` m ) )' % (RSD, STFR('r')), T, Tn,
                   exs=t([], 'sumex' if False else 'fvexd', 'x') if False else None) if False else (None, None)
    exs = cl1(w, ctx, 'sumex', '%s e. _V' % INNER)
    v, val = mpval(w, ctx, 'm', 'NN', 'sum_ r e. %s ( ( 1 / r ) x. ( %s ` m ) )' % (RSD, STFR('r')), T, Tn, exs=exs)
    assert val == INNER, val
    cr = '( %s /\\ r e. %s )' % (ctx, RSD); u = mkst(w, cr)
    Tl = lift(w, Tn, cr)
    fl2 = LZ(w, fl, cr)
    rn, mu, _, _ = rsetnn(w, cr, fl2, u([], 'simpr', 'r e. %s' % RSD))
    c = stcc(w, cr, fl2, 'r', T, Tl, rn)
    sv, _ = mpval(w, cr, 'n', 'NN', STERM('r', 'n'), T, Tl)
    iv = u([sv], 'oveq2d', '( ( 1 / r ) x. ( %s ` %s ) ) = ( ( 1 / r ) x. %s )' % (STFR('r'), T, STERM('r', T)))
    s1 = t([iv], 'sumeq2dv', '%s = sum_ r e. %s ( ( 1 / r ) x. %s )' % (INNER, RSD, STERM('r', T)))
    fl['%s e. NN' % T] = Tn
    hv, _ = applyn(w, ctx, 'z6hval', {'M': T}, fl)
    return t([t([v, s1], 'eqtrd', '( %s ` %s ) = sum_ r e. %s ( ( 1 / r ) x. %s )' % (HF, T, RSD, STERM('r', T))), hv], 'eqtrd', '( %s ` %s ) = %s' % (HF, T, XM(T)))


def z6split():
    w = W('z6split', 'The detector plus its ` n = 1 ` term is the weighted sum over the moduli of the per-modulus series (Lean ` tsum_detector_split ` , '
          '` sum_Rset_Sterm ` and the ` hpre ` block of ` detection_identity_all ` ): the finite ` r ` -sum is exchanged with the limit (~ z5finser ), '
          'the ` m ` -th exchanged term is the detector summand (~ z6hval ), and ` m = 1 ` is split off both series (~ isum1p , ~ z6xcut , ~ z6x1 ).')
    a = ante('z6split'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    p1c, fin, nv, rv = p1dcc(w, a, f)
    # (1) each per-modulus series converges to its sum
    ar = '( %s /\\ r e. %s )' % (a, RSD); t = mkst(w, ar); fl = LZ(w, f, ar)
    rm = t([], 'simpr', 'r e. %s' % RSD)
    rn, mu, _, _ = rsetnn(w, ar, fl, rm)
    fl['r e. NN'] = rn
    cv, _ = applyn(w, ar, 'z6stcv', {'R': 'r'}, fl)
    arm_ = '( %s /\\ m e. NN )' % ar; u = mkst(w, arm_); fl2 = LZ(w, fl, arm_)
    mm_ = u([], 'simpr', 'm e. NN')
    cm_ = stcc(w, arm_, fl2, 'r', 'm', mm_, lift(w, rn, arm_))
    nv_, _ = mpval(w, arm_, 'n', 'NN', STERM('r', 'n'), 'm', mm_)
    lim0 = t([w.s([], 'nnuz', NNUZ), cl1(w, ar, '1z', '1 e. ZZ'), nv_, cm_['st'], cv], 'isumclim2', 'seq 1 ( + , %s ) ~~> sum_ m e. NN %s' % (STFR('r'), STERM('r', 'm')))
    cbs = cbvsum_nm(w, 'm', 'n', body=lambda v: STERM('r', v))
    lim = t([lim0, c_(w, ar, cbs, 'sum_ m e. NN %s = %s' % (STERM('r', 'm'), SSUM('r')))], 'breqtrd', 'seq 1 ( + , %s ) ~~> %s' % (STFR('r'), SSUM('r')))
    ir = t([t([rn], 'nncnd', 'r e. CC'), t([rn], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    # G ` m e. CC under ( a /\ ( r e. RSD /\ m e. NN ) )
    arm = '( %s /\\ ( r e. %s /\\ m e. NN ) )' % (a, RSD); v = mkst(w, arm); fl3 = LZ(w, f, arm)
    rn3, _, _, _ = rsetnn(w, arm, fl3, v([], 'simprl', 'r e. %s' % RSD))
    mm = v([], 'simprr', 'm e. NN')
    c3 = stcc(w, arm, fl3, 'r', 'm', mm, rn3)
    sv3, _ = mpval(w, arm, 'n', 'NN', STERM('r', 'n'), 'm', mm)
    gm = v([sv3, c3['st']], 'eqeltrd', '( %s ` m ) e. CC' % STFR('r'))
    # (2) the exchange
    ex = st([fin, gm, lim, ir], 'z5finser', 'seq 1 ( + , %s ) ~~> %s' % (HF, RHS))
    # (3) HF ` k = XM(k)
    ak = '( %s /\\ k e. NN )' % a; ta = mkst(w, ak); fk = LZ(w, f, ak)
    kn = ta([], 'simpr', 'k e. NN')
    hvk = hfval(w, ak, fk, 'k', kn)
    ck = xmcc(w, ak, fk, 'k', kn)
    # (4) sum_ k XM(k) = RHS
    sx = st([w.s([], 'nnuz', NNUZ), cl1(w, a, '1z', '1 e. ZZ'), hvk, ck['xm'], ex], 'isumclim', 'sum_ k e. NN %s = %s' % (XM('k'), RHS))
    # (5) split off k = 1
    dm = st([ex, w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> %s -> seq 1 ( + , %s ) e. dom ~~> )' % (HF, RHS, HF))], 'syl' if False else 'x', 'x') if False else None
    dm = st([ex, w.s([], 'climrel', 'Rel ~~>')], 'releldmd' if False else 'x', 'x') if False else None
    rel = w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> %s -> seq 1 ( + , %s ) e. dom ~~> )' % (HF, RHS, HF))
    dm = st([ex, rel], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % HF)
    U2 = '( ZZ>= ` ( 1 + 1 ) )'
    sp1 = st([w.s([], 'nnuz', NNUZ), cl1(w, a, '1z', '1 e. ZZ'), hvk, ck['xm'], dm], 'isum1p',
             'sum_ k e. NN %s = ( ( %s ` 1 ) + sum_ k e. %s %s )' % (XM('k'), HF, U2, XM('k')))
    one = cl1(w, a, '1nn', '1 e. NN')
    hv1 = hfval(w, a, f, '1', one)
    x1, _ = applyn(w, a, 'z6x1', {}, f)
    x1a = st([x1], 'simpld', '%s = ( %s x. %s )' % (XM('1'), E1, P1D))
    x1b = st([x1], 'simprd', '%s = 0' % IFT('1'))
    # (6) the detector: FDV = sum_ k IFT(k) = ( IFF ` 1 ) + sum_ ( k >_ 2 ) IFT(k)
    fv = fdval(w, a, f)
    cb = cbvsum_nm(w, 'n', 'k')
    fvk = st([fv, c_(w, a, cb, 'sum_ n e. NN %s = sum_ k e. NN %s' % (IFT('n'), IFT('k')))], 'eqtrd', '%s = sum_ k e. NN %s' % (FDV, IFT('k')))
    ick, _ = ifcc(w, ak, fk, 'k', kn)
    ivk = ifval(w, ak, 'k', kn, ick)
    fcv = fdcvg(w, a, f)
    sp2 = st([w.s([], 'nnuz', NNUZ), cl1(w, a, '1z', '1 e. ZZ'), ivk, ick, fcv], 'isum1p',
             'sum_ k e. NN %s = ( ( %s ` 1 ) + sum_ k e. %s %s )' % (IFT('k'), IFF, U2, IFT('k')))
    ic1, _ = ifcc(w, a, f, '1', one)
    iv1 = ifval(w, a, '1', one, ic1)
    # (7) the tails agree
    au = '( %s /\\ k e. %s )' % (a, U2); tu = mkst(w, au); fu = LZ(w, f, au)
    k2 = tu([tu([], 'simpr', 'k e. %s' % U2), w.s([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'fveq2i', '%s = ( ZZ>= ` 2 )' % U2)], 'eleqtrdi', 'k e. ( ZZ>= ` 2 )')
    fu['k e. ( ZZ>= ` 2 )'] = k2
    xc, _ = applyn(w, au, 'z6xcut', {'M': 'k'}, fu)
    tail = st([tu([xc], 'eqcomd', '%s = %s' % (XM('k'), IFT('k')))], 'sumeq2dv', 'sum_ k e. %s %s = sum_ k e. %s %s' % (U2, XM('k'), U2, IFT('k')))
    # the tail is a complex number
    T2 = 'sum_ k e. %s %s' % (U2, IFT('k'))
    two = st([cl1(w, a, '1nn', '1 e. NN'), w.inst('peano2nn')], 'syl', '( 1 + 1 ) e. NN')
    ifk = ta([ivk, ick], 'eqeltrd', '( %s ` k ) e. CC' % IFF)
    ie = st([w.s([], 'nnuz', NNUZ), two, ifk], 'iserex', '( seq 1 ( + , %s ) e. dom ~~> <-> seq ( 1 + 1 ) ( + , %s ) e. dom ~~> )' % (IFF, IFF))
    fcv2 = st([fcv, ie], 'mpbid', 'seq ( 1 + 1 ) ( + , %s ) e. dom ~~>' % IFF)
    kn2 = tu([lift(w, two, au), tu([], 'simpr', 'k e. %s' % U2), w.inst('eluznn')], 'syl2anc', 'k e. NN')
    ic2, _ = ifcc(w, au, fu, 'k', kn2)
    iv2 = ifval(w, au, 'k', kn2, ic2)
    t2c = st([w.s([], 'eqid', '%s = %s' % (U2, U2)), st([cl1(w, a, '1z', '1 e. ZZ'), w.inst('peano2z')], 'syl', '( 1 + 1 ) e. ZZ'), iv2, ic2, fcv2], 'isumcl', '%s e. CC' % T2)
    # (8) assembly
    EP = '( %s x. %s )' % (E1, P1D)
    L1 = st([fvk, sp2], 'eqtrd', '%s = ( ( %s ` 1 ) + %s )' % (FDV, IFF, T2))
    L2 = st([st([iv1, x1b], 'eqtrd', '( %s ` 1 ) = 0' % IFF)], 'oveq1d', '( ( %s ` 1 ) + %s ) = ( 0 + %s )' % (IFF, T2, T2))
    L3 = st([t2c], 'addlidd', '( 0 + %s ) = %s' % (T2, T2))
    fd = st([st([L1, L2], 'eqtrd', '%s = ( 0 + %s )' % (FDV, T2)), L3], 'eqtrd', '%s = %s' % (FDV, T2))
    R1 = st([sx], 'eqcomd', '%s = sum_ k e. NN %s' % (RHS, XM('k')))
    R2 = st([R1, sp1], 'eqtrd', '%s = ( ( %s ` 1 ) + sum_ k e. %s %s )' % (RHS, HF, U2, XM('k')))
    R3 = st([st([hv1, x1a], 'eqtrd', '( %s ` 1 ) = %s' % (HF, EP)), tail], 'oveq12d', '( ( %s ` 1 ) + sum_ k e. %s %s ) = ( %s + %s )' % (HF, U2, XM('k'), EP, T2))
    rh = st([R2, R3], 'eqtrd', '%s = ( %s + %s )' % (RHS, EP, T2))
    epc = st([p1c, st([st([st([cl1(w, a, 'neg1rr', '-u 1 e. RR'), f['%s e. RR+' % X]], 'rerpdivcld', '( -u 1 / %s ) e. RR' % X)], 'rpefcld', '%s e. RR+' % E1)],
                      'rpcnd', '%s e. CC' % E1)], 'mulcld' if False else 'x', 'x') if False else None
    e1c = st([st([st([cl1(w, a, 'neg1rr', '-u 1 e. RR'), f['%s e. RR+' % X]], 'rerpdivcld', '( -u 1 / %s ) e. RR' % X)], 'rpefcld', '%s e. RR+' % E1)], 'rpcnd', '%s e. CC' % E1)
    epc = st([e1c, p1c], 'mulcld', '%s e. CC' % EP)
    lhs = st([fd], 'oveq1d', '( %s + %s ) = ( %s + %s )' % (FDV, EP, T2, EP))
    lhs2 = st([lhs, st([t2c, epc], 'addcomd', '( %s + %s ) = ( %s + %s )' % (T2, EP, EP, T2))], 'eqtrd', '( %s + %s ) = ( %s + %s )' % (FDV, EP, EP, T2))
    w.qed([lhs2, rh], 'eqtr4d', STATEMENTS['z6split'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6stcv, z6fdvcl, z6hval, z6xcut, z6x1, z6split]:
        if want(fn.__name__):
            if not run(fn()):
                break
