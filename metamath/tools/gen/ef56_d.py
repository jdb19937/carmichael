"""Sortie EF56: generic line-integral difference (ef6ldf)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from cl import lift, Closure
import congr as _cg
from c8_o import numst
import lin
lin.FASTPATH = True


def gen_ldf():
    w = W('ef6ldf', 'The difference ` u |-> F ( u ) - G ( u ) ` of two continuous functions on the common domain is continuous, and its line integral along a segment inside both domains is the difference of the line integrals ( ~ lintval , ~ itgsub ).')
    A0 = ante_of(S['ef6ldf'])[0]
    c = Ctx(w, A0)
    ac = c.g('A e. CC'); bc = c.g('B e. CC'); fcn = c.g('F e. ( D -cn-> CC )'); gcn = c.g('G e. ( E -cn-> CC )'); seg = c.g('( A cseg B ) C_ ( D i^i E )')
    DE = '( D i^i E )'
    s1 = c.a1(w.s([], 'inss1', '%s C_ D' % DE), '%s C_ D' % DE)
    s2 = c.a1(w.s([], 'inss2', '%s C_ E' % DE), '%s C_ E' % DE)
    ff = c([fcn, w.inst('cncff')], 'syl', 'F : D --> CC')
    gf = c([gcn, w.inst('cncff')], 'syl', 'G : E --> CC')
    def resmp(M, Dm, sst, mcn, mf):
        rc = c([mcn, c([sst, w.inst('rescncf')], 'syl', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (M, Dm, M, DE, DE))], 'mpd', '( %s |` %s ) e. ( %s -cn-> CC )' % (M, DE, DE))
        eq = c([mf, sst], 'feqresmpt', '( %s |` %s ) = ( b e. %s |-> ( %s ` b ) )' % (M, DE, DE, M))
        return c([eq, rc], 'eqeltrrd', '( b e. %s |-> ( %s ` b ) ) e. ( %s -cn-> CC )' % (DE, M, DE))
    fr = resmp('F', 'D', s1, fcn, ff); gr = resmp('G', 'E', s2, gcn, gf)
    hcn = c([fr, gr], 'subcncf', '%s e. ( %s -cn-> CC )' % (HDG, DE))
    P = '( A + ( t x. ( B - A ) ) )'
    DF = '( B - A )'
    X = '( 0 (,) 1 )'
    Ao = '( %s /\\ t e. %s )' % (A0, X)
    co = Ctx(w, Ao)
    L = lambda st: lift(w, st, Ao)
    tio = co([], 'simpr', 't e. %s' % X)
    t01 = co([co.a1(w.s([], 'ioossicc', '%s C_ ( 0 [,] 1 )' % X), '%s C_ ( 0 [,] 1 )' % X), tio], 'sseldd', 't e. ( 0 [,] 1 )')
    pin = co([L(ac), L(bc), t01, w.inst('cseglin')], 'syl3anc', '%s e. ( A cseg B )' % P)
    pde = co([L(seg), pin], 'sseldd', '%s e. %s' % (P, DE))
    pd = co([L(s1), pde], 'sseldd', '%s e. D' % P)
    pe = co([L(s2), pde], 'sseldd', '%s e. E' % P)
    fp = co([L(ff), pd], 'ffvelcdmd', '( F ` %s ) e. CC' % P)
    gp = co([L(gf), pe], 'ffvelcdmd', '( G ` %s ) e. CC' % P)
    dfc = co([L(bc), L(ac)], 'subcld', '%s e. CC' % DF)
    VAL = '( ( F ` %s ) - ( G ` %s ) )' % (P, P)
    hv, _ = _cg.mptval(w, Ao, 'b', DE, '( ( F ` b ) - ( G ` b ) )', P, pde, exs=co.a1(w.s([], 'ovex', '%s e. _V' % VAL), '%s e. _V' % VAL), gen=w.g)
    FI = '( ( F ` %s ) x. %s )' % (P, DF)
    GI = '( ( G ` %s ) x. %s )' % (P, DF)
    HI = '( ( %s ` %s ) x. %s )' % (HDG, P, DF)
    pw = co([co([hv], 'oveq1d', '%s = ( %s x. %s )' % (HI, VAL, DF)), co([fp, gp, dfc], 'subdird', '( %s x. %s ) = ( %s - %s )' % (VAL, DF, FI, GI))], 'eqtrd', '%s = ( %s - %s )' % (HI, FI, GI))
    ieq = c([pw], 'itgeq2dv', 'S. %s %s _d t = S. %s ( %s - %s ) _d t' % (X, HI, X, FI, GI))
    def ibl(M, Dm, mcn, sst):
        segm = c([seg, sst], 'sstrd', '( A cseg B ) C_ %s' % Dm)
        return c([c([c([ac, bc], 'jca', '( A e. CC /\\ B e. CC )'), c([mcn, segm], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( A cseg B ) C_ %s )' % (M, Dm, Dm))], 'jca',
                    '( ( A e. CC /\\ B e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( A cseg B ) C_ %s ) )' % (M, Dm, Dm)), w.inst('lintibl')], 'syl',
                 '( t e. %s |-> ( ( %s ` %s ) x. %s ) ) e. L^1' % (X, M, P, DF))
    fib = ibl('F', 'D', fcn, s1); gib = ibl('G', 'E', gcn, s2)
    fic = co([fp, dfc], 'mulcld', '%s e. CC' % FI); gic = co([gp, dfc], 'mulcld', '%s e. CC' % GI)
    isub = c([fic, fib, gic, gib], 'itgsub', 'S. %s ( %s - %s ) _d t = ( S. %s %s _d t - S. %s %s _d t )' % (X, FI, GI, X, FI, X, GI))
    def lv(M, st):
        return c([c([st], 'elexd', '%s e. _V' % M), ac, bc, w.inst('lintval')], 'syl3anc', '( %s lint <. A , B >. ) = S. %s ( ( %s ` %s ) x. %s ) _d t' % (M, X, M, P, DF))
    lh = lv(HDG, hcn); lf = lv('F', fcn); lg = lv('G', gcn)
    e1 = c([c([lh, ieq], 'eqtrd', '( %s lint <. A , B >. ) = S. %s ( %s - %s ) _d t' % (HDG, X, FI, GI)), isub], 'eqtrd', '( %s lint <. A , B >. ) = ( S. %s %s _d t - S. %s %s _d t )' % (HDG, X, FI, X, GI))
    e2 = c([e1, c([c([lf, lg], 'oveq12d', '( ( F lint <. A , B >. ) - ( G lint <. A , B >. ) ) = ( S. %s %s _d t - S. %s %s _d t )' % (X, FI, X, GI))], 'eqcomd',
                  '( S. %s %s _d t - S. %s %s _d t ) = ( ( F lint <. A , B >. ) - ( G lint <. A , B >. ) )' % (X, FI, X, GI))], 'eqtrd',
           '( %s lint <. A , B >. ) = ( ( F lint <. A , B >. ) - ( G lint <. A , B >. ) )' % HDG)
    w.qed([hcn, e2], 'jca', S['ef6ldf'])
    return run8(w)


def dd_eta(w, A0):
    return w.s([w.s([], 'ef2dde', DD(ETA, '1'))], 'a1i', '( %s -> %s )' % (A0, DD(ETA, '1')))


def dd_gf(w, A0):
    return w.s([w.s([], 'ef2ddg', DD(GF, '1'))], 'a1i', '( %s -> %s )' % (A0, DD(GF, '1')))


def lam_conv(w, A0, zc, z):
    """( A0 -> DLAM ( z ) = DLVZ ( z ) ) and ( A0 -> DLVZ ( z ) e. CC ) for 1 < Re z (zc: z e. CC, z1: 1 < Re z)"""
    Ak = '( %s /\\ k e. NN )' % A0
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    kn = sk([], 'simpr', 'k e. NN')
    CH = '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) )' % U1
    nx = nx1(w, Ak)
    x1 = sk([sk([sk([nx, w.inst('simpr')], 'syl', '%s e. ( Base ` ( DChr ` 1 ) )' % U1), sk([kn], 'nnzd', 'k e. ZZ')], 'jca', '( %s e. ( Base ` ( DChr ` 1 ) ) /\\ k e. ZZ )' % U1), w.inst('zc1x1')], 'syl', '%s = 1' % CH)
    lk = sk([sk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    e1 = sk([sk([sk([x1], 'oveq1d', '( %s x. ( Lam ` k ) ) = ( 1 x. ( Lam ` k ) )' % CH), sk([lk], 'mullidd', '( 1 x. ( Lam ` k ) ) = ( Lam ` k )')], 'eqtrd', '( %s x. ( Lam ` k ) ) = ( Lam ` k )' % CH)],
            'oveq1d', '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u %s ) ) = ( ( Lam ` k ) x. ( k ^c -u %s ) )' % (CH, z, z))
    return w.s([e1], 'sumeq2dv', '( %s -> %s = %s )' % (A0, DLVZ(z), DLAM(z)))


def gen_pt():
    from ef4_b import ld0_mem, ldi_val, LD0F
    w = W('ef6pt', 'On ` Re z > 1 ` the difference of the strip integrands of ` eta ` and ` g ` is ` - ( sum Lam ( k ) k ^ - z ) y ^ z / z ` , the zeta integrand (Lean ` hdiffz ` ; ~ ef5lds ).')
    A0 = ante_of(S['ef6pt'])[0]
    c = Ctx(w, A0)
    yp = c.g('Y e. RR+'); zc = c.g('Z e. CC'); z1 = c.g('1 < ( Re ` Z )')
    rzr = c([zc], 'recld', '( Re ` Z ) e. RR')
    z0 = lin8(w, A0, [z1], '0 < ( Re ` Z )', {'( Re ` Z )': rzr})
    zh = c([c([zc, z0], 'jca', '( Z e. CC /\\ 0 < ( Re ` Z ) )'), c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( Z e. %s <-> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % HP0)], 'mpbird', 'Z e. %s' % HP0)
    _, _, _, _, nzE = dd_parts(w, A0, dd_eta(w, A0), ETA, '1')
    nzb, _ = ral_at(w, A0, nzE, 'w', 'Z', '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % ETA, zh)
    en = c([z1, nzb], 'mpd', '( %s ` Z ) =/= 0' % ETA)
    _, _, _, _, nzG = dd_parts(w, A0, dd_gf(w, A0), GF, '1')
    nzg, _ = ral_at(w, A0, nzG, 'w', 'Z', '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % GF, zh)
    gn = c([z1, nzg], 'mpd', '( %s ` Z ) =/= 0' % GF)
    ze = ld0_mem(w, A0, ETA, 'Z', zh, en)
    zg = ld0_mem(w, A0, GF, 'Z', zh, gn)
    z2 = c([c([ze, zg], 'jca', '( Z e. %s /\\ Z e. %s )' % (LD0E, LD0G)), c.a1(w.s([], 'elin', '( Z e. %s <-> ( Z e. %s /\\ Z e. %s ) )' % (D2, LD0E, LD0G)), '( Z e. %s <-> ( Z e. %s /\\ Z e. %s ) )' % (D2, LD0E, LD0G))],
           'mpbird', 'Z e. %s' % D2)
    he = ldi_val(w, A0, ETA, 'Z', ze)
    hg = ldi_val(w, A0, GF, 'Z', zg)
    YQ = '( ( Y ^c Z ) / Z )'
    QE, QG = LDF(ETA, 'Z'), LDF(GF, 'Z')
    VAL = '( ( %s ` Z ) - ( %s ` Z ) )' % (HE, HG)
    hv, _ = _cg.mptval(w, A0, 'b', D2, '( ( %s ` b ) - ( %s ` b ) )' % (HE, HG), 'Z', z2, exs=c.a1(w.s([], 'ovex', '%s e. _V' % VAL), '%s e. _V' % VAL), gen=w.g)
    e1 = c([hv, c([he, hg], 'oveq12d', '%s = ( ( %s x. %s ) - ( %s x. %s ) )' % (VAL, QE, YQ, QG, YQ))], 'eqtrd', '( %s ` Z ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (HD, QE, YQ, QG, YQ))
    # closures
    def qcc(F, fn, holst):
        dom = c([holst, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (HP0, F))
        dz = c([c.a1(w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (F, F)), '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (F, F)), c([dom, zh], 'sseldd', 'Z e. dom ( CC _D %s )' % F)], 'ffvelcdmd', '( ( CC _D %s ) ` Z ) e. CC' % F)
        fz = fcc(w, A0, holst, F, HP0, 'Z', zh)
        return c([dz, fz, fn], 'divcld', '%s e. CC' % LDF(F, 'Z'))
    qe = qcc(ETA, en, hol_eta(w, A0)); qg = qcc(GF, gn, hol_gf(w, A0))
    yqc = c([c([c([yp], 'rpcnd', 'Y e. CC'), zc], 'cxpcld', '( Y ^c Z ) e. CC'), zc, ne0_re(c, 'Z', zc, z0)], 'divcld', '%s e. CC' % YQ)
    e2 = c([qe, qg, yqc], 'subdird', '( ( %s - %s ) x. %s ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (QE, QG, YQ, QE, YQ, QG, YQ))
    ld = c([c([zc, z1], 'jca', '( Z e. CC /\\ 1 < ( Re ` Z ) )'), w.inst('ef5lds')], 'syl', '%s = ( %s - %s )' % (QE, QG, DLAM('Z')))
    lc = lam_conv(w, A0, zc, 'Z')
    DL = DLAM('Z')
    DZ = DLVZ('Z')
    dzc = dlvz_cc(w, A0, 'Z', zc, z1)
    dlc = c([lc, dzc], 'eqeltrrd' if False else 'x', 'x') if False else c([c([lc], 'eqcomd', '%s = %s' % (DL, DZ)), dzc], 'eqeltrd', '%s e. CC' % DL)
    cl = Closure(w, A0, {QG: ('CC', qg), DL: ('CC', dlc)})
    cl.atom(QG); cl.atom(DL)
    r1 = ringeq(w, A0, '( ( %s - %s ) - %s )' % (QG, DL, QG), '-u %s' % DL, cl)
    d1 = c([c([ld], 'oveq1d', '( %s - %s ) = ( ( %s - %s ) - %s )' % (QE, QG, QG, DL, QG)), r1], 'eqtrd', '( %s - %s ) = -u %s' % (QE, QG, DL))
    e3 = c([c([e1, c([e2], 'eqcomd', '( ( %s x. %s ) - ( %s x. %s ) ) = ( ( %s - %s ) x. %s )' % (QE, YQ, QG, YQ, QE, QG, YQ))], 'eqtrd', '( %s ` Z ) = ( ( %s - %s ) x. %s )' % (HD, QE, QG, YQ)),
            c([d1], 'oveq1d', '( ( %s - %s ) x. %s ) = ( -u %s x. %s )' % (QE, QG, YQ, DL, YQ))], 'eqtrd', '( %s ` Z ) = ( -u %s x. %s )' % (HD, DL, YQ))
    e4 = c([e3, c([dlc, yqc], 'mulneg1d', '( -u %s x. %s ) = -u ( %s x. %s )' % (DL, YQ, DL, YQ))], 'eqtrd', '( %s ` Z ) = -u ( %s x. %s )' % (HD, DL, YQ))
    e5 = c([e4, c([c([c([lc], 'eqcomd', '%s = %s' % (DL, DZ))], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (DL, YQ, DZ, YQ))], 'negeqd', '-u ( %s x. %s ) = -u ( %s x. %s )' % (DL, YQ, DZ, YQ))],
           'eqtrd', '( %s ` Z ) = -u ( %s x. %s )' % (HD, DZ, YQ))
    w.qed([z2, e5], 'jca', S['ef6pt'])
    return run8(w)

GENS = {'ef6ldf': gen_ldf, 'ef6pt': gen_pt}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
