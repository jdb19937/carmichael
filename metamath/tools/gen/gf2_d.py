"""Sortie GF2, section D: the Dirichlet identity sum_n P ( n ) ^ 2 C ( n ) n ^ -z = MH ( z ) L ( z )
(Lean Pfun_sq_term_eq, tsum_Pfun_sq_eq_Mh_mul_LFunction) and the principal value MH ( 1 ) = PHI (Mh_one_principal).
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_d.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
import gf1lib as G1L
from gf1lib import tsub, proj
from mvlib import ringeq, ringeqp

S_ = L.S
RSN = '( N RSet R )'
PS = lambda r, n: '( ( mmu ` ( %s gcd %s ) ) x. ( phi ` ( %s gcd %s ) ) )' % (r, n, r, n)
DV = lambda K: '{ x e. NN | x || %s }' % K
HB = lambda r, t, d: '( ( %s hBV %s ) ` %s )' % (r, t, d)
IS = lambda r, t, M: 'sum_ d e. %s ( ( %s x. ( C ` d ) ) x. ( C ` ( %s / d ) ) )' % (DV(M), HB(r, t, 'd'), M)
MULT = 'A. i e. NN A. j e. NN ( C ` ( i x. j ) ) = ( ( C ` i ) x. ( C ` j ) )'
DH = '( ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) /\\ ( C : NN --> CC /\\ %s ) )' % MULT
PM = lambda M: '( ( N PFun R ) ` %s )' % M
S_['gf2dir1'] = ('( ( %s /\\ M e. NN ) -> sum_ r e. %s sum_ t e. %s ( ( 1 / ( r x. t ) ) x. %s ) = ( ( %s ^ 2 ) x. ( C ` M ) ) )'
                 % (DH, RSN, RSN, IS('r', 't', 'M'), PM('M')))


def rsetf(w, a, nv, rr, k):
    """k e. RS -> ( k e. NN /\\ ( mmu ` k ) =/= 0 ) under a ( k free in a as a member )"""
    st = mkst(w, a)
    km = proj(w, a, '%s e. %s' % (k, RSN))
    el = st([nv, rr, w.inst('z5elrset')], 'syl2anc', '( %s e. %s <-> ( %s e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) ) )' % (k, RSN, k, k, k))
    e2 = st([km, el], 'mpbid', '( %s e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) )' % (k, k, k))
    kn = st([st([e2], 'simpld', '%s e. ( 1 ... ( |_ ` R ) )' % k), w.inst('elfznn')], 'syl', '%s e. NN' % k)
    mu = st([e2], 'simprld', '( mmu ` %s ) =/= 0' % k)
    return kn, mu


def gf2dir1():
    w = W('gf2dir1', 'The coefficient of the Dirichlet identity (Lean ` Pfun_sq_term_eq ` ): for ` C ` completely multiplicative, '
          '` sum_r sum_t ( 1 / r t ) sum_ d | M h ( d ; r , t ) C ( d ) C ( M / d ) = P ( M ) ^ 2 C ( M ) ` (~ z5psipsi , ~ z5pfunval ).')
    a = split_imp(S_['gf2dir1'])[0]; st = mkst(w, a)
    nv = proj(w, a, 'N e. V'); rr = proj(w, a, 'R e. RR'); mn = proj(w, a, 'M e. NN')
    cf = proj(w, a, 'C : NN --> CC'); mult = proj(w, a, MULT)
    cm = st([cf, mn], 'ffvelcdmd', '( C ` M ) e. CC')
    rsf = st([st([nv, rr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RSN, RSN))], 'simprd', '%s e. Fin' % RSN)
    ar = '( %s /\\ r e. %s )' % (a, RSN); sr = mkst(w, ar)
    rn, rmu = rsetf(w, ar, lift(w, nv, ar), lift(w, rr, ar), 'r')
    art = '( %s /\\ t e. %s )' % (ar, RSN); s2 = mkst(w, art)
    tn, tmu = rsetf(w, art, lift(w, nv, art), lift(w, rr, art), 't')
    rn2 = lift(w, rn, art); rmu2 = lift(w, rmu, art); mn2 = lift(w, mn, art); cm2 = lift(w, cm, art)
    ps = s2([s2([rn2, rmu2], 'jca', '( r e. NN /\\ ( mmu ` r ) =/= 0 )'), s2([tn, tmu], 'jca', '( t e. NN /\\ ( mmu ` t ) =/= 0 )'), mn2, w.inst('z5psipsi')], 'syl3anc',
             '( %s x. %s ) = sum_ d e. %s %s' % (PS('r', 'M'), PS('t', 'M'), DV('M'), HB('r', 't', 'd')))
    # per d
    ad = '( %s /\\ d e. %s )' % (art, DV('M')); sd = mkst(w, ad)
    dm = sd([], 'simpr', 'd e. %s' % DV('M'))
    er = w.s([w.s([], 'breq1', '( x = d -> ( x || M <-> d || M ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DV('M'))
    dd = sd([dm, a1(w, ad, er, '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DV('M'))], 'mpbid', '( d e. NN /\\ d || M )')
    dn = sd([dd], 'simpld', 'd e. NN'); ddv = sd([dd], 'simprd', 'd || M')
    md = sd([ddv, sd([lift(w, mn, ad), dn, w.inst('nndivdvds')], 'syl2anc', '( d || M <-> ( M / d ) e. NN )')], 'mpbid', '( M / d ) e. NN')
    b1 = w.s([w.s([w.s([], 'oveq1', '( i = d -> ( i x. j ) = ( d x. j ) )')], 'fveq2d', '( i = d -> ( C ` ( i x. j ) ) = ( C ` ( d x. j ) ) )'),
              w.s([w.s([], 'fveq2', '( i = d -> ( C ` i ) = ( C ` d ) )')], 'oveq1d', '( i = d -> ( ( C ` i ) x. ( C ` j ) ) = ( ( C ` d ) x. ( C ` j ) ) )')], 'eqeq12d',
             '( i = d -> ( ( C ` ( i x. j ) ) = ( ( C ` i ) x. ( C ` j ) ) <-> ( C ` ( d x. j ) ) = ( ( C ` d ) x. ( C ` j ) ) ) )')
    b2 = w.s([w.s([w.s([], 'oveq2', '( j = ( M / d ) -> ( d x. j ) = ( d x. ( M / d ) ) )')], 'fveq2d',
                  '( j = ( M / d ) -> ( C ` ( d x. j ) ) = ( C ` ( d x. ( M / d ) ) ) )'),
              w.s([w.s([], 'fveq2', '( j = ( M / d ) -> ( C ` j ) = ( C ` ( M / d ) ) )')], 'oveq2d',
                  '( j = ( M / d ) -> ( ( C ` d ) x. ( C ` j ) ) = ( ( C ` d ) x. ( C ` ( M / d ) ) ) )')], 'eqeq12d',
             '( j = ( M / d ) -> ( ( C ` ( d x. j ) ) = ( ( C ` d ) x. ( C ` j ) ) <-> ( C ` ( d x. ( M / d ) ) ) = ( ( C ` d ) x. ( C ` ( M / d ) ) ) ) )')
    mu_ = sd([b1, b2, lift(w, mult, ad), dn, md], 'rspc2dv', '( C ` ( d x. ( M / d ) ) ) = ( ( C ` d ) x. ( C ` ( M / d ) ) )')
    dc = sd([dn], 'nncnd', 'd e. CC'); mc = sd([lift(w, mn, ad)], 'nncnd', 'M e. CC')
    dcan = sd([mc, dc, sd([dn], 'nnne0d', 'd =/= 0')], 'divcan2d', '( d x. ( M / d ) ) = M')
    cmm = sd([sd([mu_], 'eqcomd', '( ( C ` d ) x. ( C ` ( M / d ) ) ) = ( C ` ( d x. ( M / d ) ) )'), sd([dcan], 'fveq2d', '( C ` ( d x. ( M / d ) ) ) = ( C ` M )')],
             'eqtrd', '( ( C ` d ) x. ( C ` ( M / d ) ) ) = ( C ` M )')
    hcr = sd([sd([lift(w, rn, ad), lift(w, tn, ad)], 'jca', '( r e. NN /\\ t e. NN )'), dn, w.inst('z5hbvre')], 'syl2anc', '%s e. RR' % HB('r', 't', 'd'))
    hc = sd([hcr], 'recnd', '%s e. CC' % HB('r', 't', 'd'))
    cdc = sd([lift(w, cf, ad), dn], 'ffvelcdmd', '( C ` d ) e. CC')
    cmdc = sd([lift(w, cf, ad), md], 'ffvelcdmd', '( C ` ( M / d ) ) e. CC')
    H_ = HB('r', 't', 'd')
    tq = sd([sd([hc, cdc, cmdc], 'mulassd', '( ( %s x. ( C ` d ) ) x. ( C ` ( M / d ) ) ) = ( %s x. ( ( C ` d ) x. ( C ` ( M / d ) ) ) )' % (H_, H_)),
             sd([sd([cmm], 'oveq2d', '( %s x. ( ( C ` d ) x. ( C ` ( M / d ) ) ) ) = ( %s x. ( C ` M ) )' % (H_, H_)),
                 sd([hc, lift(w, cm, ad)], 'mulcomd', '( %s x. ( C ` M ) ) = ( ( C ` M ) x. %s )' % (H_, H_))], 'eqtrd',
                '( %s x. ( ( C ` d ) x. ( C ` ( M / d ) ) ) ) = ( ( C ` M ) x. %s )' % (H_, H_))], 'eqtrd',
            '( ( %s x. ( C ` d ) ) x. ( C ` ( M / d ) ) ) = ( ( C ` M ) x. %s )' % (H_, H_))
    se = s2([tq], 'sumeq2dv', '%s = sum_ d e. %s ( ( C ` M ) x. %s )' % (IS('r', 't', 'M'), DV('M'), H_))
    dvf = s2([mn2, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV('M'))
    fm = w.s([dvf, cm2, hc], 'fsummulc2', '( %s -> ( ( C ` M ) x. sum_ d e. %s %s ) = sum_ d e. %s ( ( C ` M ) x. %s ) )' % (art, DV('M'), H_, DV('M'), H_))
    PP = '( %s x. %s )' % (PS('r', 'M'), PS('t', 'M'))
    isv = s2([s2([se, s2([fm], 'eqcomd', 'sum_ d e. %s ( ( C ` M ) x. %s ) = ( ( C ` M ) x. sum_ d e. %s %s )' % (DV('M'), H_, DV('M'), H_))], 'eqtrd',
                 '%s = ( ( C ` M ) x. sum_ d e. %s %s )' % (IS('r', 't', 'M'), DV('M'), H_)),
              s2([s2([ps], 'eqcomd', 'sum_ d e. %s %s = %s' % (DV('M'), H_, PP))], 'oveq2d', '( ( C ` M ) x. sum_ d e. %s %s ) = ( ( C ` M ) x. %s )' % (DV('M'), H_, PP))],
             'eqtrd', '%s = ( ( C ` M ) x. %s )' % (IS('r', 't', 'M'), PP))
    # psi values are complex
    def psc(ctx, k, kn):
        t_ = mkst(w, ctx)
        return t_([t_([kn, lift(w, mn, ctx), w.inst('z5psiabs')], 'syl2anc', '( abs ` %s ) <_ %s' % (PS(k, 'M'), k)), w.inst('z6absle')], 'syl', '%s e. CC' % PS(k, 'M'))
    psr = psc(art, 'r', rn2); pst = psc(art, 't', tn)
    rc = s2([rn2], 'nncnd', 'r e. CC'); r0 = s2([rn2], 'nnne0d', 'r =/= 0')
    tc = s2([tn], 'nncnd', 't e. CC'); t0 = s2([tn], 'nnne0d', 't =/= 0')
    U = '( 1 / ( r x. t ) )'
    rtc = s2([rc, tc], 'mulcld', '( r x. t ) e. CC'); rt0 = s2([rc, tc, r0, t0], 'mulne0d', '( r x. t ) =/= 0')
    uc = s2([rtc, rt0], 'reccld', '%s e. CC' % U)
    ppc = s2([psr, pst], 'mulcld', '%s e. CC' % PP)
    PR = '( %s / r )' % PS('r', 'M'); PT = '( %s / t )' % PS('t', 'M')
    dmd = s2([psr, rc, pst, tc, r0, t0], 'divmuldivd', '( %s x. %s ) = ( %s / ( r x. t ) )' % (PR, PT, PP))
    drec = s2([ppc, rtc, rt0], 'divrecd', '( %s / ( r x. t ) ) = ( %s x. %s )' % (PP, PP, U))
    cl = Closure(w, art, {U: uc, '( C ` M )': cm2, PS('r', 'M'): psr, PS('t', 'M'): pst})
    rq = ringeq(w, art, '( %s x. ( ( C ` M ) x. %s ) )' % (U, PP), '( ( %s x. %s ) x. ( C ` M ) )' % (PP, U), cl)
    e1 = s2([s2([dmd, drec], 'eqtrd', '( %s x. %s ) = ( %s x. %s )' % (PR, PT, PP, U))], 'oveq1d', '( ( %s x. %s ) x. ( C ` M ) ) = ( ( %s x. %s ) x. ( C ` M ) )' % (PR, PT, PP, U))
    prc = s2([psr, rc, r0], 'divcld', '%s e. CC' % PR); ptc = s2([pst, tc, t0], 'divcld', '%s e. CC' % PT)
    e2 = s2([prc, ptc, cm2], 'mulassd', '( ( %s x. %s ) x. ( C ` M ) ) = ( %s x. ( %s x. ( C ` M ) ) )' % (PR, PT, PR, PT))
    pt_ = s2([s2([s2([isv], 'oveq2d', '( %s x. %s ) = ( %s x. ( ( C ` M ) x. %s ) )' % (U, IS('r', 't', 'M'), U, PP)), rq], 'eqtrd',
                 '( %s x. %s ) = ( ( %s x. %s ) x. ( C ` M ) )' % (U, IS('r', 't', 'M'), PP, U)),
              s2([e1, e2], 'eqtr3d', '( ( %s x. %s ) x. ( C ` M ) ) = ( %s x. ( %s x. ( C ` M ) ) )' % (PP, U, PR, PT))], 'eqtrd',
             '( %s x. %s ) = ( %s x. ( %s x. ( C ` M ) ) )' % (U, IS('r', 't', 'M'), PR, PT))
    # the t-sum
    st1 = sr([pt_], 'sumeq2dv', 'sum_ t e. %s ( %s x. %s ) = sum_ t e. %s ( %s x. ( %s x. ( C ` M ) ) )' % (RSN, U, IS('r', 't', 'M'), RSN, PR, PT))
    prc_r = sr([psc(ar, 'r', rn), sr([rn], 'nncnd', 'r e. CC'), sr([rn], 'nnne0d', 'r =/= 0')], 'divcld', '%s e. CC' % PR)
    ptcm = s2([ptc, cm2], 'mulcld', '( %s x. ( C ` M ) ) e. CC' % PT)
    f2 = w.s([lift(w, rsf, ar), prc_r, ptcm], 'fsummulc2', '( %s -> ( %s x. sum_ t e. %s ( %s x. ( C ` M ) ) ) = sum_ t e. %s ( %s x. ( %s x. ( C ` M ) ) ) )'
             % (ar, PR, RSN, PT, RSN, PR, PT))
    f1 = w.s([lift(w, rsf, ar), lift(w, cm, ar), ptc], 'fsummulc1', '( %s -> ( sum_ t e. %s %s x. ( C ` M ) ) = sum_ t e. %s ( %s x. ( C ` M ) ) )' % (ar, RSN, PT, RSN, PT))
    pfv = st([st([nv, rr], 'jca', '( N e. V /\\ R e. RR )'), mn, w.inst('z5pfunval')], 'syl2anc', '%s = sum_ r e. %s %s' % (PM('M'), RSN, PR))
    idr = w.s([], 'id', '( r = t -> r = t )')
    cst, _ = w.congr(PR, {'r': 't'}, 'r = t', {'r': idr})
    cbt = a1(w, a, w.s([cst], 'cbvsumv', 'sum_ r e. %s %s = sum_ t e. %s %s' % (RSN, PR, RSN, PT)), 'sum_ r e. %s %s = sum_ t e. %s %s' % (RSN, PR, RSN, PT))
    pft = st([pfv, cbt], 'eqtrd', '%s = sum_ t e. %s %s' % (PM('M'), RSN, PT))
    PC = '( %s x. ( C ` M ) )' % PM('M')
    ta = sr([st1, sr([f2], 'eqcomd', 'sum_ t e. %s ( %s x. ( %s x. ( C ` M ) ) ) = ( %s x. sum_ t e. %s ( %s x. ( C ` M ) ) )' % (RSN, PR, PT, PR, RSN, PT))], 'eqtrd',
            'sum_ t e. %s ( %s x. %s ) = ( %s x. sum_ t e. %s ( %s x. ( C ` M ) ) )' % (RSN, U, IS('r', 't', 'M'), PR, RSN, PT))
    tb1 = sr([f1], 'eqcomd', 'sum_ t e. %s ( %s x. ( C ` M ) ) = ( sum_ t e. %s %s x. ( C ` M ) )' % (RSN, PT, RSN, PT))
    tb2 = sr([sr([lift(w, pft, ar)], 'eqcomd', 'sum_ t e. %s %s = %s' % (RSN, PT, PM('M')))], 'oveq1d', '( sum_ t e. %s %s x. ( C ` M ) ) = %s' % (RSN, PT, PC))
    tb = sr([tb1, tb2], 'eqtrd', 'sum_ t e. %s ( %s x. ( C ` M ) ) = %s' % (RSN, PT, PC))
    tc_ = sr([tb], 'oveq2d', '( %s x. sum_ t e. %s ( %s x. ( C ` M ) ) ) = ( %s x. %s )' % (PR, RSN, PT, PR, PC))
    tsum = sr([ta, tc_], 'eqtrd', 'sum_ t e. %s ( %s x. %s ) = ( %s x. %s )' % (RSN, U, IS('r', 't', 'M'), PR, PC))
    # the r-sum
    rsum = st([tsum], 'sumeq2dv', 'sum_ r e. %s sum_ t e. %s ( %s x. %s ) = sum_ r e. %s ( %s x. %s )' % (RSN, RSN, U, IS('r', 't', 'M'), RSN, PR, PC))
    pmc = st([st([st([nv, st([rr, proj(w, a, '0 <_ R')], 'jca', '( R e. RR /\\ 0 <_ R )')], 'jca', '( N e. V /\\ ( R e. RR /\\ 0 <_ R ) )'), mn, w.inst('z5pfunabs')],
                 'syl2anc', '( abs ` %s ) <_ ( |_ ` R )' % PM('M')), w.inst('z6absle')], 'syl', '%s e. CC' % PM('M'))
    pcc = st([pmc, cm], 'mulcld', '%s e. CC' % PC)
    f3 = w.s([rsf, pcc, prc_r], 'fsummulc1', '( %s -> ( sum_ r e. %s %s x. %s ) = sum_ r e. %s ( %s x. %s ) )' % (a, RSN, PR, PC, RSN, PR, PC))
    r2 = st([st([f3], 'eqcomd', 'sum_ r e. %s ( %s x. %s ) = ( sum_ r e. %s %s x. %s )' % (RSN, PR, PC, RSN, PR, PC)),
             st([st([pfv], 'eqcomd', 'sum_ r e. %s %s = %s' % (RSN, PR, PM('M')))], 'oveq1d', '( sum_ r e. %s %s x. %s ) = ( %s x. %s )' % (RSN, PR, PC, PM('M'), PC))], 'eqtrd',
            'sum_ r e. %s ( %s x. %s ) = ( %s x. %s )' % (RSN, PR, PC, PM('M'), PC))
    fin_alg = ringeqp(w, a, '( %s x. %s )' % (PM('M'), PC), '( ( %s ^ 2 ) x. ( C ` M ) )' % PM('M'), Closure(w, a, {PM('M'): pmc, '( C ` M )': cm}))
    fin = st([st([rsum, r2], 'eqtrd', 'sum_ r e. %s sum_ t e. %s ( %s x. %s ) = ( %s x. %s )' % (RSN, RSN, U, IS('r', 't', 'M'), PM('M'), PC)), fin_alg], 'eqtrd',
             split_imp(S_['gf2dir1'])[1])
    w.qed([fin], 'idi', S_['gf2dir1'])
    return w


LSZ = 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u Z ) )'
XRT = lambda r, t: 'sum_ d e. %s ( ( %s x. ( C ` d ) ) x. ( d ^c -u Z ) )' % (DV('( %s x. %s )' % (r, t)), HB(r, t, 'd'))
GRT = lambda r, t: '( n e. NN |-> ( %s x. ( n ^c -u Z ) ) )' % IS(r, t, 'n')
CBm = 'A. m e. NN ( abs ` ( C ` m ) ) <_ 1'
D2H = '( ( ( r e. NN /\\ t e. NN ) /\\ ( C : NN --> CC /\\ %s ) ) /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % CBm
S_['gf2dir2'] = '( %s -> seq 1 ( + , %s ) ~~> ( %s x. %s ) )' % (D2H, GRT('r', 't'), XRT('r', 't'), LSZ)


def gf2dir2():
    w = W('gf2dir2', 'One pair ` r , t ` of the Dirichlet identity: ` sum_n ( sum_ d | n h ( d ; r , t ) C ( d ) C ( n / d ) ) n ^ -u Z ` '
          'converges to ` ( sum_ d | r t h ( d ; r , t ) C ( d ) d ^ -u Z ) L ( Z ) ` (~ z5fconv with the finitely supported ` h C ` , ~ gf1hbv0 ).')
    a = D2H; st = mkst(w, a)
    rn = proj(w, a, 'r e. NN'); tn = proj(w, a, 't e. NN'); cf = proj(w, a, 'C : NN --> CC')
    RT = '( r x. t )'
    rtn = st([rn, tn], 'nnmulcld', '%s e. NN' % RT)
    AF = '( e e. NN |-> ( %s x. ( C ` e ) ) )' % HB('r', 't', 'e')
    ae = '( %s /\\ e e. NN )' % a; se = mkst(w, ae)
    en = se([], 'simpr', 'e e. NN')
    hce = se([se([se([lift(w, rn, ae), lift(w, tn, ae)], 'jca', '( r e. NN /\\ t e. NN )'), en, w.inst('z5hbvre')], 'syl2anc', '%s e. RR' % HB('r', 't', 'e'))], 'recnd',
             '%s e. CC' % HB('r', 't', 'e'))
    afc = se([hce, se([lift(w, cf, ae), en], 'ffvelcdmd', '( C ` e ) e. CC')], 'mulcld', '( %s x. ( C ` e ) ) e. CC' % HB('r', 't', 'e'))
    aff = st([afc, w.s([], 'eqid', '%s = %s' % (AF, AF))], 'fmptd', '%s : NN --> CC' % AF)
    F = DV(RT)
    ff = st([rtn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % F)
    fs = a1(w, a, w.s([], 'ssrab2', '%s C_ NN' % F), '%s C_ NN' % F)
    al = '( %s /\\ l e. ( NN \\ %s ) )' % (a, F); sl = mkst(w, al)
    lm = sl([], 'simpr', 'l e. ( NN \\ %s )' % F)
    ln = sl([lm, w.inst('eldifi')], 'syl', 'l e. NN')
    lnf = sl([lm, w.inst('eldifn')], 'syl', '-. l e. %s' % F)
    erl = w.s([w.s([], 'breq1', '( x = l -> ( x || %s <-> l || %s ) )' % (RT, RT))], 'elrab', '( l e. %s <-> ( l e. NN /\\ l || %s ) )' % (F, RT))
    ald = '( %s /\\ l || %s )' % (al, RT); sld = mkst(w, ald)
    lin_ = sld([sld([lift(w, ln, ald), sld([], 'simpr', 'l || %s' % RT)], 'jca', '( l e. NN /\\ l || %s )' % RT), a1(w, ald, erl, '( l e. %s <-> ( l e. NN /\\ l || %s ) )' % (F, RT))],
               'mpbird', 'l e. %s' % F)
    nd = sl([lnf, w.s([lin_], 'ex', '( %s -> ( l || %s -> l e. %s ) )' % (al, RT, F))], 'mtod', '-. l || %s' % RT)
    h0 = sl([sl([sl([lift(w, rn, al), lift(w, tn, al)], 'jca', '( r e. NN /\\ t e. NN )'), ln], 'jca', '( ( r e. NN /\\ t e. NN ) /\\ l e. NN )'), nd, w.inst('gf1hbv0')], 'syl2anc',
            '%s = 0' % HB('r', 't', 'l'))
    alv, _ = mpv(w, al, 'e', 'NN', '( %s x. ( C ` e ) )' % HB('r', 't', 'e'), 'l', ln)
    al0 = sl([alv, sl([sl([h0], 'oveq1d', '( %s x. ( C ` l ) ) = ( 0 x. ( C ` l ) )' % HB('r', 't', 'l')), sl([sl([lift(w, cf, al), ln], 'ffvelcdmd', '( C ` l ) e. CC')], 'mul02d',
                                                                                                                      '( 0 x. ( C ` l ) ) = 0')], 'eqtrd', '( %s x. ( C ` l ) ) = 0' % HB('r', 't', 'l'))],
             'eqtrd', '( %s ` l ) = 0' % AF)
    z0 = st([al0], 'ralrimiva', 'A. l e. ( NN \\ %s ) ( %s ` l ) = 0' % (F, AF))
    H1 = '( ( %s : NN --> CC /\\ %s e. Fin /\\ %s C_ NN ) /\\ A. l e. ( NN \\ %s ) ( %s ` l ) = 0 )' % (AF, F, F, F, AF)
    h1 = st([st([aff, ff, fs], '3jca', '( %s : NN --> CC /\\ %s e. Fin /\\ %s C_ NN )' % (AF, F, F)), z0], 'jca', H1)
    H2 = '( ( C : NN --> CC /\\ 1 e. RR /\\ %s ) /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % CBm
    h2 = st([st([cf, a1(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), proj(w, a, CBm)], '3jca', '( C : NN --> CC /\\ 1 e. RR /\\ %s )' % CBm),
             st([proj(w, a, 'Z e. CC'), proj(w, a, '1 < ( Re ` Z )')], 'jca', '( Z e. CC /\\ 1 < ( Re ` Z ) )')], 'jca', H2)
    G0B = lambda n: '( sum_ d e. %s ( ( %s ` d ) x. ( C ` ( %s / d ) ) ) x. ( %s ^c -u Z ) )' % (DV(n), AF, n, n)
    G0 = '( n e. NN |-> %s )' % G0B('n')
    X0 = 'sum_ d e. %s ( ( %s ` d ) x. ( d ^c -u Z ) )' % (F, AF)
    fc = st([h1, h2, w.inst('z5fconv')], 'syl2anc', 'seq 1 ( + , %s ) ~~> ( %s x. %s )' % (G0, X0, LSZ))
    # rewrite A ` d
    an = '( %s /\\ n e. NN )' % a
    adn = '( %s /\\ d e. %s )' % (an, DV('n')); sdn = mkst(w, adn)
    ern = w.s([w.s([], 'breq1', '( x = d -> ( x || n <-> d || n ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || n ) )' % DV('n'))
    dnn = sdn([sdn([sdn([], 'simpr', 'd e. %s' % DV('n')), a1(w, adn, ern, '( d e. %s <-> ( d e. NN /\\ d || n ) )' % DV('n'))], 'mpbid', '( d e. NN /\\ d || n )')], 'simpld', 'd e. NN')
    adv, _ = mpv(w, adn, 'e', 'NN', '( %s x. ( C ` e ) )' % HB('r', 't', 'e'), 'd', dnn)
    t1 = sdn([adv], 'oveq1d', '( ( %s ` d ) x. ( C ` ( n / d ) ) ) = ( ( %s x. ( C ` d ) ) x. ( C ` ( n / d ) ) )' % (AF, HB('r', 't', 'd')))
    s1 = w.s([t1], 'sumeq2dv', '( %s -> sum_ d e. %s ( ( %s ` d ) x. ( C ` ( n / d ) ) ) = %s )' % (an, DV('n'), AF, IS('r', 't', 'n')))
    s1b = w.s([s1], 'oveq1d', '( %s -> %s = ( %s x. ( n ^c -u Z ) ) )' % (an, G0B('n'), IS('r', 't', 'n')))
    geq = st([s1b], 'mpteq2dva', '%s = %s' % (G0, GRT('r', 't')))
    sq = st([geq, w.inst('seqeq3')], 'syl', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (G0, GRT('r', 't')))
    adf = '( %s /\\ d e. %s )' % (a, F); sdf = mkst(w, adf)
    erf = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (RT, RT))], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (F, RT))
    dfn = sdf([sdf([sdf([], 'simpr', 'd e. %s' % F), a1(w, adf, erf, '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (F, RT))], 'mpbid', '( d e. NN /\\ d || %s )' % RT)], 'simpld', 'd e. NN')
    afv, _ = mpv(w, adf, 'e', 'NN', '( %s x. ( C ` e ) )' % HB('r', 't', 'e'), 'd', dfn)
    xe = st([sdf([afv], 'oveq1d', '( ( %s ` d ) x. ( d ^c -u Z ) ) = ( ( %s x. ( C ` d ) ) x. ( d ^c -u Z ) )' % (AF, HB('r', 't', 'd')))], 'sumeq2dv', '%s = %s' % (X0, XRT('r', 't')))
    fin = st([fc, st([sq, st([xe], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (X0, LSZ, XRT('r', 't'), LSZ))], 'breq12d',
                     '( seq 1 ( + , %s ) ~~> ( %s x. %s ) <-> seq 1 ( + , %s ) ~~> ( %s x. %s ) )' % (G0, X0, LSZ, GRT('r', 't'), XRT('r', 't'), LSZ))], 'mpbid',
             split_imp(S_['gf2dir2'])[1])
    w.qed([fin], 'idi', S_['gf2dir2'])
    return w


LSF = '( n e. NN |-> ( ( C ` n ) x. ( n ^c -u Z ) ) )'


def lscv(w, a, cf, cbj, zc, z1):
    """( a -> LSZ e. CC ) by cvgcmpce against k ^c -u ( Re ` Z ) (zetacvg); cbj: ( a -> A. j e. NN ( abs ` ( C ` j ) ) <_ 1 )"""
    st = mkst(w, a)
    RZ = '( Re ` Z )'
    rzr = st([zc], 'recld', '%s e. RR' % RZ)
    ZR = '( n e. NN |-> ( n ^c -u %s ) )' % RZ
    ak = '( %s /\\ k e. NN )' % a; sk = mkst(w, ak)
    kn = sk([], 'simpr', 'k e. NN')
    zv, _ = mpv(w, ak, 'n', 'NN', '( n ^c -u %s )' % RZ, 'k', kn)
    rre = st([rzr, w.inst('rere')], 'syl', '( Re ` %s ) = %s' % (RZ, RZ))
    zcv = st([st([rzr], 'recnd', '%s e. CC' % RZ), st([z1, rre], 'breqtrrd', '1 < ( Re ` %s )' % RZ), zv], 'zetacvg', 'seq 1 ( + , %s ) e. dom ~~>' % ZR)
    kr = sk([kn], 'nnrpd', 'k e. RR+')
    KZ = '( k ^c -u %s )' % RZ
    kz = sk([kr, sk([lift(w, rzr, ak)], 'renegcld', '-u %s e. RR' % RZ)], 'rpcxpcld', '%s e. RR+' % KZ)
    zre = sk([zv, sk([kz], 'rpred', '%s e. RR' % KZ)], 'eqeltrd', '( %s ` k ) e. RR' % ZR)
    T_ = '( ( C ` k ) x. ( k ^c -u Z ) )'
    lv, _ = mpv(w, ak, 'n', 'NN', '( ( C ` n ) x. ( n ^c -u Z ) )', 'k', kn)
    ckc = sk([lift(w, cf, ak), kn], 'ffvelcdmd', '( C ` k ) e. CC')
    nzc = sk([lift(w, zc, ak)], 'negcld', '-u Z e. CC')
    kzc = sk([sk([kn], 'nncnd', 'k e. CC'), nzc], 'cxpcld', '( k ^c -u Z ) e. CC')
    tc = sk([ckc, kzc], 'mulcld', '%s e. CC' % T_)
    rsp = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( C ` j ) = ( C ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` k ) ) )')], 'breq1d',
              '( j = k -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` k ) ) <_ 1 ) )')
    cb = sk([rsp, lift(w, cbj, ak), kn], 'rspcdva', '( abs ` ( C ` k ) ) <_ 1')
    ab = sk([sk([kr, nzc, w.inst('abscxp')], 'syl2anc', '( abs ` ( k ^c -u Z ) ) = ( k ^c ( Re ` -u Z ) )'),
             sk([sk([lift(w, zc, ak)], 'renegd', '( Re ` -u Z ) = -u %s' % RZ)], 'oveq2d', '( k ^c ( Re ` -u Z ) ) = %s' % KZ)], 'eqtrd', '( abs ` ( k ^c -u Z ) ) = %s' % KZ)
    b1 = sk([sk([ckc], 'abscld', '( abs ` ( C ` k ) ) e. RR'), sk([], '1red', '1 e. RR'), sk([kzc], 'abscld', '( abs ` ( k ^c -u Z ) ) e. RR'), sk([kz], 'rpred', '%s e. RR' % KZ),
             sk([ckc], 'absge0d', '0 <_ ( abs ` ( C ` k ) )'), sk([kzc], 'absge0d', '0 <_ ( abs ` ( k ^c -u Z ) )'), cb, sk([sk([kzc], 'abscld', '( abs ` ( k ^c -u Z ) ) e. RR'), ab], 'eqled',
                                                                                                                                   '( abs ` ( k ^c -u Z ) ) <_ %s' % KZ)],
            'lemul12ad', '( ( abs ` ( C ` k ) ) x. ( abs ` ( k ^c -u Z ) ) ) <_ ( 1 x. %s )' % KZ)
    b2 = sk([sk([ckc, kzc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( C ` k ) ) x. ( abs ` ( k ^c -u Z ) ) )' % T_), b1], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. %s )' % (T_, KZ))
    b3 = sk([sk([sk([lv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (LSF, T_)), b2], 'eqbrtrd', '( abs ` ( %s ` k ) ) <_ ( 1 x. %s )' % (LSF, KZ)),
             sk([sk([zv], 'eqcomd', '%s = ( %s ` k )' % (KZ, ZR))], 'oveq2d', '( 1 x. %s ) = ( 1 x. ( %s ` k ) )' % (KZ, ZR))], 'breqtrd',
            '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (LSF, ZR))
    ak1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    kn1 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % ak1), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                   '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'syl', '( %s -> k e. NN )' % ak1)
    b4 = w.s([w.s([w.s([b3], 'ex', '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) ) )' % (a, LSF, ZR))], 'adantr',
                  '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) ) )' % (ak1, LSF, ZR)), kn1], 'mpd', '( %s -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) )' % (ak1, LSF, ZR))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    lcv = st([nnuz, a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'), zre, sk([lv, tc], 'eqeltrd', '( %s ` k ) e. CC' % LSF), zcv, st([], '1red', '1 e. RR'), b4], 'cvgcmpce',
             'seq 1 ( + , %s ) e. dom ~~>' % LSF)
    return w.s([nnuz, a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), lv, tc, lcv], 'isumcl', '( %s -> %s e. CC )' % (a, LSZ))


CBj = 'A. j e. NN ( abs ` ( C ` j ) ) <_ 1'
DIRH = '( %s /\\ ( %s /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) )' % (DH, CBj)
TGT = lambda n: '( ( ( %s ^ 2 ) x. ( C ` %s ) ) x. ( %s ^c -u Z ) )' % (PM(n), n, n)
MHZ = G1L.MH('N', 'R', 'C', 'Z')
S_['gf2dir'] = '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s ) )' % (DIRH, TGT('n'), MHZ, LSZ)
U_ = '( 1 / ( r x. t ) )'


def iscc(w, ctx, cf, rn, tn, qn, q):
    """( ctx -> IS ( r , t , q ) e. CC )"""
    sx = mkst(w, ctx)
    cd = '( %s /\\ d e. %s )' % (ctx, DV(q)); sd = mkst(w, cd)
    erq = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (q, q))], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DV(q), q))
    dd = sd([sd([], 'simpr', 'd e. %s' % DV(q)), a1(w, cd, erq, '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DV(q), q))], 'mpbid', '( d e. NN /\\ d || %s )' % q)
    dn = sd([dd], 'simpld', 'd e. NN')
    qd = sd([sd([dd], 'simprd', 'd || %s' % q), sd([lift(w, qn, cd), dn, w.inst('nndivdvds')], 'syl2anc', '( d || %s <-> ( %s / d ) e. NN )' % (q, q))], 'mpbid', '( %s / d ) e. NN' % q)
    hc = sd([sd([sd([lift(w, rn, cd), lift(w, tn, cd)], 'jca', '( r e. NN /\\ t e. NN )'), dn, w.inst('z5hbvre')], 'syl2anc', '%s e. RR' % HB('r', 't', 'd'))], 'recnd',
            '%s e. CC' % HB('r', 't', 'd'))
    tc = sd([sd([hc, sd([lift(w, cf, cd), dn], 'ffvelcdmd', '( C ` d ) e. CC')], 'mulcld', '( %s x. ( C ` d ) ) e. CC' % HB('r', 't', 'd')),
             sd([lift(w, cf, cd), qd], 'ffvelcdmd', '( C ` ( %s / d ) ) e. CC' % q)], 'mulcld', '( ( %s x. ( C ` d ) ) x. ( C ` ( %s / d ) ) ) e. CC' % (HB('r', 't', 'd'), q))
    return w.s([sx([qn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV(q)), tc], 'fsumcl', '( %s -> %s e. CC )' % (ctx, IS('r', 't', q)))


def xrtcc(w, ctx, cf, rn, tn, zc):
    """( ctx -> XRT ( r , t ) e. CC )"""
    sx = mkst(w, ctx)
    RT = '( r x. t )'
    cd = '( %s /\\ d e. %s )' % (ctx, DV(RT)); sd = mkst(w, cd)
    erq = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (RT, RT))], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DV(RT), RT))
    dn = sd([sd([sd([], 'simpr', 'd e. %s' % DV(RT)), a1(w, cd, erq, '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DV(RT), RT))], 'mpbid', '( d e. NN /\\ d || %s )' % RT)],
            'simpld', 'd e. NN')
    hc = sd([sd([sd([lift(w, rn, cd), lift(w, tn, cd)], 'jca', '( r e. NN /\\ t e. NN )'), dn, w.inst('z5hbvre')], 'syl2anc', '%s e. RR' % HB('r', 't', 'd'))], 'recnd',
            '%s e. CC' % HB('r', 't', 'd'))
    tc = sd([sd([hc, sd([lift(w, cf, cd), dn], 'ffvelcdmd', '( C ` d ) e. CC')], 'mulcld', '( %s x. ( C ` d ) ) e. CC' % HB('r', 't', 'd')),
             sd([sd([dn], 'nncnd', 'd e. CC'), sd([lift(w, zc, cd)], 'negcld', '-u Z e. CC')], 'cxpcld', '( d ^c -u Z ) e. CC')], 'mulcld',
            '( ( %s x. ( C ` d ) ) x. ( d ^c -u Z ) ) e. CC' % HB('r', 't', 'd'))
    rtn = sx([rn, tn], 'nnmulcld', '%s e. NN' % RT)
    return w.s([sx([rtn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV(RT)), tc], 'fsumcl', '( %s -> %s e. CC )' % (ctx, XRT('r', 't')))


def gf2dir():
    w = W('gf2dir', 'The Dirichlet identity (Lean ` tsum_Pfun_sq_eq_Mh_mul_LFunction ` ): for ` C ` completely multiplicative with ` | C | <_ 1 ` and '
          '` Re Z > 1 ` , ` sum_n P ( n ) ^ 2 C ( n ) n ^ -u Z ` converges to ` M_h ( Z ) sum_k C ( k ) k ^ -u Z ` (~ gf2dir2 per pair, ~ z5finser twice, '
          '~ gf2dir1 for the coefficients).')
    a = DIRH; st = mkst(w, a)
    nv = proj(w, a, 'N e. V'); rr = proj(w, a, 'R e. RR'); cf = proj(w, a, 'C : NN --> CC')
    zc = proj(w, a, 'Z e. CC'); z1 = proj(w, a, '1 < ( Re ` Z )')
    cbj = proj(w, a, CBj)
    idjm = w.s([w.s([w.s([], 'fveq2', '( j = m -> ( C ` j ) = ( C ` m ) )')], 'fveq2d', '( j = m -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` m ) ) )')], 'breq1d',
               '( j = m -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` m ) ) <_ 1 ) )')
    cbm = st([cbj, w.s([idjm], 'cbvralvw', '( %s <-> %s )' % (CBj, CBm))], 'sylib', CBm)
    rsf = st([st([nv, rr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RSN, RSN))], 'simprd', '%s e. Fin' % RSN)
    lsc = lscv(w, a, cf, cbj, zc, z1)
    # inner: index t
    ar = '( %s /\\ r e. %s )' % (a, RSN); sr = mkst(w, ar)
    rn, _ = rsetf(w, ar, lift(w, nv, ar), lift(w, rr, ar), 'r')
    art = '( %s /\\ t e. %s )' % (ar, RSN); s2 = mkst(w, art)
    tn, _ = rsetf(w, art, lift(w, nv, art), lift(w, rr, art), 't')
    rn2 = lift(w, rn, art)
    d2 = s2([s2([s2([s2([rn2, tn], 'jca', '( r e. NN /\\ t e. NN )'), s2([lift(w, cf, art), lift(w, cbm, art)], 'jca', '( C : NN --> CC /\\ %s )' % CBm)], 'jca',
                    '( ( r e. NN /\\ t e. NN ) /\\ ( C : NN --> CC /\\ %s ) )' % CBm), s2([lift(w, zc, art), lift(w, z1, art)], 'jca', '( Z e. CC /\\ 1 < ( Re ` Z ) )')], 'jca',
                D2H), w.inst('gf2dir2')], 'syl', split_imp(S_['gf2dir2'])[1])
    def ucc(ctx, rn_, tn_):
        t_ = mkst(w, ctx)
        rtc = t_([t_([rn_], 'nncnd', 'r e. CC'), t_([tn_], 'nncnd', 't e. CC')], 'mulcld', '( r x. t ) e. CC')
        rt0 = t_([t_([rn_], 'nncnd', 'r e. CC'), t_([tn_], 'nncnd', 't e. CC'), t_([rn_], 'nnne0d', 'r =/= 0'), t_([tn_], 'nnne0d', 't =/= 0')], 'mulne0d', '( r x. t ) =/= 0')
        return t_([rtc, rt0], 'reccld', '%s e. CC' % U_)
    uc = ucc(art, rn2, tn)
    # GRT ` q e. CC
    GR_ = GRT('r', 't')
    aq = '( %s /\\ ( t e. %s /\\ q e. NN ) )' % (ar, RSN); sq = mkst(w, aq)
    qn = sq([], 'simprr', 'q e. NN')
    tnq, _ = rsetf(w, aq, lift(w, nv, aq), lift(w, rr, aq), 't')
    rnq = lift(w, rn, aq)
    grv, _ = mpv(w, aq, 'n', 'NN', '( %s x. ( n ^c -u Z ) )' % IS('r', 't', 'n'), 'q', qn)
    grc = sq([grv, sq([iscc(w, aq, lift(w, cf, aq), rnq, tnq, qn, 'q'), sq([sq([qn], 'nncnd', 'q e. CC'), sq([lift(w, zc, aq)], 'negcld', '-u Z e. CC')], 'cxpcld', '( q ^c -u Z ) e. CC')],
                 'mulcld', '( %s x. ( q ^c -u Z ) ) e. CC' % IS('r', 't', 'q'))], 'eqeltrd', '( %s ` q ) e. CC' % GR_)
    GRr = '( q e. NN |-> sum_ t e. %s ( %s x. ( %s ` q ) ) )' % (RSN, U_, GR_)
    LTr = 'sum_ t e. %s ( %s x. ( %s x. %s ) )' % (RSN, U_, XRT('r', 't'), LSZ)
    inner = w.s([lift(w, rsf, ar), grc, d2, uc], 'z5finser', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (ar, GRr, LTr))
    # outer: index r
    am2 = '( %s /\\ ( r e. %s /\\ m e. NN ) )' % (a, RSN); sm = mkst(w, am2)
    mn2 = sm([], 'simprr', 'm e. NN')
    rnm, _ = rsetf(w, am2, lift(w, nv, am2), lift(w, rr, am2), 'r')
    grm, _ = mpv(w, am2, 'q', 'NN', 'sum_ t e. %s ( %s x. ( %s ` q ) )' % (RSN, U_, GR_), 'm', mn2,
                 exs=w.s([w.s([], 'sumex', 'sum_ t e. %s ( %s x. ( %s ` m ) ) e. _V' % (RSN, U_, GR_))], 'a1i', '( %s -> sum_ t e. %s ( %s x. ( %s ` m ) ) e. _V )' % (am2, RSN, U_, GR_)))
    amt = '( %s /\\ t e. %s )' % (am2, RSN); smt = mkst(w, amt)
    tnm, _ = rsetf(w, amt, lift(w, nv, amt), lift(w, rr, amt), 't')
    rnmt = lift(w, rnm, amt); mnt = lift(w, mn2, amt)
    grvm, _ = mpv(w, amt, 'n', 'NN', '( %s x. ( n ^c -u Z ) )' % IS('r', 't', 'n'), 'm', mnt)
    ismc = iscc(w, amt, lift(w, cf, amt), rnmt, tnm, mnt, 'm')
    mzc = smt([smt([mnt], 'nncnd', 'm e. CC'), smt([lift(w, zc, amt)], 'negcld', '-u Z e. CC')], 'cxpcld', '( m ^c -u Z ) e. CC')
    grcm = smt([grvm, smt([ismc, mzc], 'mulcld', '( %s x. ( m ^c -u Z ) ) e. CC' % IS('r', 't', 'm'))], 'eqeltrd', '( %s ` m ) e. CC' % GR_)
    ucm = ucc(amt, rnmt, tnm)
    tcm = smt([ucm, grcm], 'mulcld', '( %s x. ( %s ` m ) ) e. CC' % (U_, GR_))
    grrc = sm([grm, w.s([sm([lift(w, rsf, am2)], 'idi', '%s e. Fin' % RSN), tcm], 'fsumcl', '( %s -> sum_ t e. %s ( %s x. ( %s ` m ) ) e. CC )' % (am2, RSN, U_, GR_))], 'eqeltrd',
              '( %s ` m ) e. CC' % GRr)
    outer = w.s([rsf, grrc, inner, sr([], '1cnd', '1 e. CC')], 'z5finser',
                '( %s -> seq 1 ( + , ( m e. NN |-> sum_ r e. %s ( 1 x. ( %s ` m ) ) ) ) ~~> sum_ r e. %s ( 1 x. %s ) )' % (a, RSN, GRr, RSN, LTr))
    # the function: sum_r 1 ( GR_r ` m ) = TGT ( m )
    am = '( %s /\\ m e. NN )' % a; ta = mkst(w, am)
    mn = ta([], 'simpr', 'm e. NN')
    amr = '( %s /\\ r e. %s )' % (am, RSN); tr_ = mkst(w, amr)
    rnr, _ = rsetf(w, amr, lift(w, nv, amr), lift(w, rr, amr), 'r')
    mnr = lift(w, mn, amr)
    grmr, _ = mpv(w, amr, 'q', 'NN', 'sum_ t e. %s ( %s x. ( %s ` q ) )' % (RSN, U_, GR_), 'm', mnr,
                  exs=w.s([w.s([], 'sumex', 'sum_ t e. %s ( %s x. ( %s ` m ) ) e. _V' % (RSN, U_, GR_))], 'a1i', '( %s -> sum_ t e. %s ( %s x. ( %s ` m ) ) e. _V )' % (amr, RSN, U_, GR_)))
    amrt = '( %s /\\ t e. %s )' % (amr, RSN); t3 = mkst(w, amrt)
    tn3, _ = rsetf(w, amrt, lift(w, nv, amrt), lift(w, rr, amrt), 't')
    rn3 = lift(w, rnr, amrt); mn3 = lift(w, mn, amrt)
    gv3, _ = mpv(w, amrt, 'n', 'NN', '( %s x. ( n ^c -u Z ) )' % IS('r', 't', 'n'), 'm', mn3)
    is3 = iscc(w, amrt, lift(w, cf, amrt), rn3, tn3, mn3, 'm')
    mz3 = t3([t3([mn3], 'nncnd', 'm e. CC'), t3([lift(w, zc, amrt)], 'negcld', '-u Z e. CC')], 'cxpcld', '( m ^c -u Z ) e. CC')
    u3 = ucc(amrt, rn3, tn3)
    MZ = '( m ^c -u Z )'; ISm = IS('r', 't', 'm')
    pt3 = t3([t3([gv3], 'oveq2d', '( %s x. ( %s ` m ) ) = ( %s x. ( %s x. %s ) )' % (U_, GR_, U_, ISm, MZ)),
              t3([t3([u3, is3, mz3], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (U_, ISm, MZ, U_, ISm, MZ))], 'eqcomd',
                 '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (U_, ISm, MZ, U_, ISm, MZ))], 'eqtrd', '( %s x. ( %s ` m ) ) = ( ( %s x. %s ) x. %s )' % (U_, GR_, U_, ISm, MZ))
    s3_ = tr_([pt3], 'sumeq2dv', 'sum_ t e. %s ( %s x. ( %s ` m ) ) = sum_ t e. %s ( ( %s x. %s ) x. %s )' % (RSN, U_, GR_, RSN, U_, ISm, MZ))
    uisc = t3([u3, is3], 'mulcld', '( %s x. %s ) e. CC' % (U_, ISm))
    mzr = tr_([tr_([mnr], 'nncnd', 'm e. CC'), tr_([lift(w, zc, amr)], 'negcld', '-u Z e. CC')], 'cxpcld', '%s e. CC' % MZ)
    f1_ = w.s([lift(w, rsf, amr), mzr, uisc], 'fsummulc1', '( %s -> ( sum_ t e. %s ( %s x. %s ) x. %s ) = sum_ t e. %s ( ( %s x. %s ) x. %s ) )' % (amr, RSN, U_, ISm, MZ, RSN, U_, ISm, MZ))
    TS = 'sum_ t e. %s ( %s x. %s )' % (RSN, U_, ISm)
    grc_r = tr_([grmr, s3_], 'eqtrd', '( %s ` m ) = sum_ t e. %s ( ( %s x. %s ) x. %s )' % (GRr, RSN, U_, ISm, MZ))
    one_r = tr_([tr_([grc_r, tr_([f1_], 'eqcomd', 'sum_ t e. %s ( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (RSN, U_, ISm, MZ, TS, MZ))], 'eqtrd',
                     '( %s ` m ) = ( %s x. %s )' % (GRr, TS, MZ))], 'oveq2d', '( 1 x. ( %s ` m ) ) = ( 1 x. ( %s x. %s ) )' % (GRr, TS, MZ))
    tsc = w.s([lift(w, rsf, amr), uisc], 'fsumcl', '( %s -> %s e. CC )' % (amr, TS))
    one_r2 = tr_([one_r, tr_([tr_([tsc, mzr], 'mulcld', '( %s x. %s ) e. CC' % (TS, MZ))], 'mullidd', '( 1 x. ( %s x. %s ) ) = ( %s x. %s )' % (TS, MZ, TS, MZ))], 'eqtrd',
                 '( 1 x. ( %s ` m ) ) = ( %s x. %s )' % (GRr, TS, MZ))
    sr_ = ta([one_r2], 'sumeq2dv', 'sum_ r e. %s ( 1 x. ( %s ` m ) ) = sum_ r e. %s ( %s x. %s )' % (RSN, GRr, RSN, TS, MZ))
    mza = ta([ta([mn], 'nncnd', 'm e. CC'), ta([lift(w, zc, am)], 'negcld', '-u Z e. CC')], 'cxpcld', '%s e. CC' % MZ)
    f2_ = w.s([lift(w, rsf, am), mza, tsc], 'fsummulc1', '( %s -> ( sum_ r e. %s %s x. %s ) = sum_ r e. %s ( %s x. %s ) )' % (am, RSN, TS, MZ, RSN, TS, MZ))
    d1 = ta([ta([proj(w, am, DH), mn], 'jca', '( %s /\\ m e. NN )' % DH), w.inst('gf2dir1')], 'syl', tsub(split_imp(S_['gf2dir1'])[1], {'M': 'm'}))
    fe = ta([ta([sr_, ta([f2_], 'eqcomd', 'sum_ r e. %s ( %s x. %s ) = ( sum_ r e. %s %s x. %s )' % (RSN, TS, MZ, RSN, TS, MZ))], 'eqtrd',
                'sum_ r e. %s ( 1 x. ( %s ` m ) ) = ( sum_ r e. %s %s x. %s )' % (RSN, GRr, RSN, TS, MZ)),
             ta([d1], 'oveq1d', '( sum_ r e. %s %s x. %s ) = %s' % (RSN, TS, MZ, TGT('m')))], 'eqtrd', 'sum_ r e. %s ( 1 x. ( %s ` m ) ) = %s' % (RSN, GRr, TGT('m')))
    F1 = '( m e. NN |-> sum_ r e. %s ( 1 x. ( %s ` m ) ) )' % (RSN, GRr)
    fq1 = st([fe], 'mpteq2dva', '%s = ( m e. NN |-> %s )' % (F1, TGT('m')))
    idmn = w.s([], 'id', '( m = n -> m = n )')
    cst, _ = w.congr(TGT('m'), {'m': 'n'}, 'm = n', {'m': idmn})
    fq2 = a1(w, a, w.s([cst], 'cbvmptv', '( m e. NN |-> %s ) = ( n e. NN |-> %s )' % (TGT('m'), TGT('n'))), '( m e. NN |-> %s ) = ( n e. NN |-> %s )' % (TGT('m'), TGT('n')))
    FT = '( n e. NN |-> %s )' % TGT('n')
    fq = st([fq1, fq2], 'eqtrd', '%s = %s' % (F1, FT))
    sq_ = st([fq, w.inst('seqeq3')], 'syl', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (F1, FT))
    # the limit: sum_r 1 LT_r = MH L
    XR = XRT('r', 't')
    xr2 = xrtcc(w, art, lift(w, cf, art), rn2, tn, lift(w, zc, art))
    ls2 = lift(w, lsc, art)
    lta = s2([s2([uc, xr2, ls2], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (U_, XR, LSZ, U_, XR, LSZ))], 'eqcomd',
             '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (U_, XR, LSZ, U_, XR, LSZ))
    lt1 = sr([lta], 'sumeq2dv', '%s = sum_ t e. %s ( ( %s x. %s ) x. %s )' % (LTr, RSN, U_, XR, LSZ))
    uxc = s2([uc, xr2], 'mulcld', '( %s x. %s ) e. CC' % (U_, XR))
    TX = 'sum_ t e. %s ( %s x. %s )' % (RSN, U_, XR)
    fl1 = w.s([lift(w, rsf, ar), lift(w, lsc, ar), uxc], 'fsummulc1', '( %s -> ( %s x. %s ) = sum_ t e. %s ( ( %s x. %s ) x. %s ) )' % (ar, TX, LSZ, RSN, U_, XR, LSZ))
    lt2 = sr([lt1, sr([fl1], 'eqcomd', 'sum_ t e. %s ( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (RSN, U_, XR, LSZ, TX, LSZ))], 'eqtrd', '%s = ( %s x. %s )' % (LTr, TX, LSZ))
    txc = w.s([lift(w, rsf, ar), uxc], 'fsumcl', '( %s -> %s e. CC )' % (ar, TX))
    lt3 = sr([sr([lt2], 'oveq2d', '( 1 x. %s ) = ( 1 x. ( %s x. %s ) )' % (LTr, TX, LSZ)), sr([sr([txc, lift(w, lsc, ar)], 'mulcld', '( %s x. %s ) e. CC' % (TX, LSZ))], 'mullidd',
                                                                                                  '( 1 x. ( %s x. %s ) ) = ( %s x. %s )' % (TX, LSZ, TX, LSZ))], 'eqtrd',
             '( 1 x. %s ) = ( %s x. %s )' % (LTr, TX, LSZ))
    lt4 = st([lt3], 'sumeq2dv', 'sum_ r e. %s ( 1 x. %s ) = sum_ r e. %s ( %s x. %s )' % (RSN, LTr, RSN, TX, LSZ))
    fl2 = w.s([rsf, lsc, txc], 'fsummulc1', '( %s -> ( sum_ r e. %s %s x. %s ) = sum_ r e. %s ( %s x. %s ) )' % (a, RSN, TX, LSZ, RSN, TX, LSZ))
    assert 'sum_ r e. %s %s' % (RSN, TX) == MHZ, (MHZ,)
    lim = st([lt4, st([fl2], 'eqcomd', 'sum_ r e. %s ( %s x. %s ) = ( %s x. %s )' % (RSN, TX, LSZ, MHZ, LSZ))], 'eqtrd', 'sum_ r e. %s ( 1 x. %s ) = ( %s x. %s )' % (RSN, LTr, MHZ, LSZ))
    fin = st([outer, st([sq_, lim], 'breq12d', '( seq 1 ( + , %s ) ~~> sum_ r e. %s ( 1 x. %s ) <-> seq 1 ( + , %s ) ~~> ( %s x. %s ) )' % (F1, RSN, LTr, FT, MHZ, LSZ))],
             'mpbid', split_imp(S_['gf2dir'])[1])
    w.qed([fin], 'idi', S_['gf2dir'])
    return w


PRNn = '( n e. NN |-> if ( ( n gcd N ) = 1 , 1 , 0 ) )'
MH1 = G1L.MH('N', 'R', PRNn, '1')
S_['gf2mh1'] = '( ( N e. NN /\\ R e. RR ) -> %s = %s )' % (MH1, L.PHI('N', 'R'))


def rsetg(w, a, nv, rr, k):
    """k e. RS -> k e. NN , ( mmu ` k ) =/= 0 , ( k gcd N ) = 1"""
    st = mkst(w, a)
    km = proj(w, a, '%s e. %s' % (k, RSN))
    el = st([nv, rr, w.inst('z5elrset')], 'syl2anc', '( %s e. %s <-> ( %s e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) ) )' % (k, RSN, k, k, k))
    e2 = st([km, el], 'mpbid', '( %s e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) )' % (k, k, k))
    kn = st([st([e2], 'simpld', '%s e. ( 1 ... ( |_ ` R ) )' % k), w.inst('elfznn')], 'syl', '%s e. NN' % k)
    return kn, st([e2], 'simprld', '( mmu ` %s ) =/= 0' % k), st([e2], 'simprrd', '( %s gcd N ) = 1' % k)


def gf2mh1():
    w = W('gf2mh1', 'The principal value (Lean ` Mh_one_principal ` ): ` M_h ( 1 , chi_0 ) = sum_ r ( phi ( r ) / r ^ 2 ) ` : every divisor of ` r t ` is '
          'coprime to ` N ` , and ` sum_ d | r t h ( d ; r , t ) / d = [ r = t ] phi ( r ) ` (~ z5hbvorth , ~ sumite ).')
    a = split_imp(S_['gf2mh1'])[0]; st = mkst(w, a)
    nn_ = proj(w, a, 'N e. NN'); rr = proj(w, a, 'R e. RR')
    nv = nn_
    rsf = st([st([nv, rr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RSN, RSN))], 'simprd', '%s e. Fin' % RSN)
    ar = '( %s /\\ r e. %s )' % (a, RSN); sr = mkst(w, ar)
    rn, rmu, rg = rsetg(w, ar, lift(w, nv, ar), lift(w, rr, ar), 'r')
    art = '( %s /\\ t e. %s )' % (ar, RSN); s2 = mkst(w, art)
    tn, tmu, tg = rsetg(w, art, lift(w, nv, art), lift(w, rr, art), 't')
    rn2 = lift(w, rn, art); rmu2 = lift(w, rmu, art); rg2 = lift(w, rg, art)
    nz = s2([lift(w, nn_, art)], 'nnzd', 'N e. ZZ'); rz = s2([rn2], 'nnzd', 'r e. ZZ'); tz = s2([tn], 'nnzd', 't e. ZZ')
    RT = '( r x. t )'
    ng1 = s2([s2([nz, rz], 'gcdcomd', '( N gcd r ) = ( r gcd N )'), rg2], 'eqtrd', '( N gcd r ) = 1')
    ng2 = s2([s2([nz, tz], 'gcdcomd', '( N gcd t ) = ( t gcd N )'), tg], 'eqtrd', '( N gcd t ) = 1')
    nrt = s2([s2([ng1, ng2], 'jca', '( ( N gcd r ) = 1 /\\ ( N gcd t ) = 1 )'), s2([nz, rz, tz, w.inst('rpmul')], 'syl3anc',
                                                                                   '( ( ( N gcd r ) = 1 /\\ ( N gcd t ) = 1 ) -> ( N gcd %s ) = 1 )' % RT)], 'mpd', '( N gcd %s ) = 1' % RT)
    ad = '( %s /\\ d e. %s )' % (art, DV(RT)); sd = mkst(w, ad)
    erq = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (RT, RT))], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DV(RT), RT))
    dd = sd([sd([], 'simpr', 'd e. %s' % DV(RT)), a1(w, ad, erq, '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DV(RT), RT))], 'mpbid', '( d e. NN /\\ d || %s )' % RT)
    dn = sd([dd], 'simpld', 'd e. NN'); ddv = sd([dd], 'simprd', 'd || %s' % RT)
    dz = sd([dn], 'nnzd', 'd e. ZZ')
    rtz = sd([lift(w, rz, ad), lift(w, tz, ad)], 'zmulcld', '%s e. ZZ' % RT)
    nd = sd([sd([lift(w, nz, ad), dz, rtz], '3jca', '( N e. ZZ /\\ d e. ZZ /\\ %s e. ZZ )' % RT), sd([lift(w, nrt, ad), ddv], 'jca', '( ( N gcd %s ) = 1 /\\ d || %s )' % (RT, RT)),
             w.inst('rpdvds')], 'syl2anc', '( N gcd d ) = 1')
    dg = sd([sd([dz, lift(w, nz, ad)], 'gcdcomd', '( d gcd N ) = ( N gcd d )'), nd], 'eqtrd', '( d gcd N ) = 1')
    pv, _ = mpv(w, ad, 'n', 'NN', 'if ( ( n gcd N ) = 1 , 1 , 0 )', 'd', dn)
    p1 = sd([pv, sd([dg, w.s([], 'iftrue', '( ( d gcd N ) = 1 -> if ( ( d gcd N ) = 1 , 1 , 0 ) = 1 )')], 'syl', 'if ( ( d gcd N ) = 1 , 1 , 0 ) = 1')], 'eqtrd',
            '( %s ` d ) = 1' % PRNn)
    dc = sd([dn], 'nncnd', 'd e. CC'); d0 = sd([dn], 'nnne0d', 'd =/= 0')
    dm1 = sd([sd([dc, d0, sd([], '1cnd', '1 e. CC')], 'cxpnegd', '( d ^c -u 1 ) = ( 1 / ( d ^c 1 ) )'), sd([sd([dc], 'cxp1d', '( d ^c 1 ) = d')], 'oveq2d',
                                                                                                         '( 1 / ( d ^c 1 ) ) = ( 1 / d )')], 'eqtrd', '( d ^c -u 1 ) = ( 1 / d )')
    H_ = HB('r', 't', 'd')
    hc = sd([sd([sd([lift(w, rn2, ad), lift(w, tn, ad)], 'jca', '( r e. NN /\\ t e. NN )'), dn, w.inst('z5hbvre')], 'syl2anc', '%s e. RR' % H_)], 'recnd', '%s e. CC' % H_)
    tq = sd([sd([sd([p1], 'oveq2d', '( %s x. ( %s ` d ) ) = ( %s x. 1 )' % (H_, PRNn, H_)), dm1], 'oveq12d',
                '( ( %s x. ( %s ` d ) ) x. ( d ^c -u 1 ) ) = ( ( %s x. 1 ) x. ( 1 / d ) )' % (H_, PRNn, H_)),
             sd([sd([sd([hc], 'mulridd', '( %s x. 1 ) = %s' % (H_, H_))], 'oveq1d', '( ( %s x. 1 ) x. ( 1 / d ) ) = ( %s x. ( 1 / d ) )' % (H_, H_)),
                 sd([sd([hc, dc, d0], 'divrecd', '( %s / d ) = ( %s x. ( 1 / d ) )' % (H_, H_))], 'eqcomd', '( %s x. ( 1 / d ) ) = ( %s / d )' % (H_, H_))], 'eqtrd',
                '( ( %s x. 1 ) x. ( 1 / d ) ) = ( %s / d )' % (H_, H_))], 'eqtrd', '( ( %s x. ( %s ` d ) ) x. ( d ^c -u 1 ) ) = ( %s / d )' % (H_, PRNn, H_))
    INN = 'sum_ d e. %s ( ( %s x. ( %s ` d ) ) x. ( d ^c -u 1 ) )' % (DV(RT), H_, PRNn)
    se = s2([tq], 'sumeq2dv', '%s = sum_ d e. %s ( %s / d )' % (INN, DV(RT), H_))
    ho = s2([s2([rn2, rmu2], 'jca', '( r e. NN /\\ ( mmu ` r ) =/= 0 )'), s2([tn, tmu], 'jca', '( t e. NN /\\ ( mmu ` t ) =/= 0 )'), w.inst('z5hbvorth')], 'syl2anc',
            'sum_ d e. %s ( %s / d ) = if ( r = t , ( phi ` r ) , 0 )' % (DV(RT), H_))
    U = '( 1 / ( r x. t ) )'
    rc = s2([rn2], 'nncnd', 'r e. CC'); tc = s2([tn], 'nncnd', 't e. CC')
    uc = s2([s2([rc, tc], 'mulcld', '( r x. t ) e. CC'), s2([rc, tc, s2([rn2], 'nnne0d', 'r =/= 0'), s2([tn], 'nnne0d', 't =/= 0')], 'mulne0d', '( r x. t ) =/= 0')], 'reccld',
            '%s e. CC' % U)
    PH = '( phi ` r )'
    o2 = a1(w, art, w.s([], 'ovif2', '( %s x. if ( r = t , %s , 0 ) ) = if ( r = t , ( %s x. %s ) , ( %s x. 0 ) )' % (U, PH, U, PH, U)),
            '( %s x. if ( r = t , %s , 0 ) ) = if ( r = t , ( %s x. %s ) , ( %s x. 0 ) )' % (U, PH, U, PH, U))
    ib = s2([a1(w, art, w.s([], 'eqcom', '( r = t <-> t = r )'), '( r = t <-> t = r )'), s2([], 'eqidd', '( %s x. %s ) = ( %s x. %s )' % (U, PH, U, PH)),
             s2([uc], 'mul01d', '( %s x. 0 ) = 0' % U)], 'ifbieq12d', 'if ( r = t , ( %s x. %s ) , ( %s x. 0 ) ) = if ( t = r , ( %s x. %s ) , 0 )' % (U, PH, U, U, PH))
    pt = s2([s2([s2([se, ho], 'eqtrd', '%s = if ( r = t , %s , 0 )' % (INN, PH))], 'oveq2d', '( %s x. %s ) = ( %s x. if ( r = t , %s , 0 ) )' % (U, INN, U, PH)),
             s2([o2, ib], 'eqtrd', '( %s x. if ( r = t , %s , 0 ) ) = if ( t = r , ( %s x. %s ) , 0 )' % (U, PH, U, PH))], 'eqtrd',
            '( %s x. %s ) = if ( t = r , ( %s x. %s ) , 0 )' % (U, INN, U, PH))
    st1 = sr([pt], 'sumeq2dv', 'sum_ t e. %s ( %s x. %s ) = sum_ t e. %s if ( t = r , ( %s x. %s ) , 0 )' % (RSN, U, INN, RSN, U, PH))
    U2 = '( 1 / ( r x. r ) )'
    cg = w.s([w.s([w.s([w.s([], 'oveq2', '( t = r -> ( r x. t ) = ( r x. r ) )')], 'oveq2d', '( t = r -> %s = %s )' % (U, U2))], 'oveq1d',
                  '( t = r -> ( %s x. %s ) = ( %s x. %s ) )' % (U, PH, U2, PH))], 'idi', '( t = r -> ( %s x. %s ) = ( %s x. %s ) )' % (U, PH, U2, PH))
    rcr = sr([rn], 'nncnd', 'r e. CC'); r0r = sr([rn], 'nnne0d', 'r =/= 0')
    phc = sr([sr([sr([rn, w.inst('phicl')], 'syl', '%s e. NN' % PH)], 'nncnd', '%s e. CC' % PH)], 'idi', '%s e. CC' % PH)
    u2c = sr([sr([rcr, rcr], 'mulcld', '( r x. r ) e. CC'), sr([rcr, rcr, r0r, r0r], 'mulne0d', '( r x. r ) =/= 0')], 'reccld', '%s e. CC' % U2)
    si = sr([cg, lift(w, rsf, ar), sr([], 'simpr', 'r e. %s' % RSN), sr([u2c, phc], 'mulcld', '( %s x. %s ) e. CC' % (U2, PH))], 'sumite',
            'sum_ t e. %s if ( t = r , ( %s x. %s ) , 0 ) = ( %s x. %s )' % (RSN, U, PH, U2, PH))
    # ( 1 / ( r x. r ) ) phi r = phi r / r ^ 2
    sqv = sr([rcr], 'sqvald', '( r ^ 2 ) = ( r x. r )')
    fr = sr([sr([sr([sqv], 'oveq2d', '( %s / ( r ^ 2 ) ) = ( %s / ( r x. r ) )' % (PH, PH)),
                 sr([phc, sr([rcr, rcr], 'mulcld', '( r x. r ) e. CC'), sr([rcr, rcr, r0r, r0r], 'mulne0d', '( r x. r ) =/= 0')], 'divrecd',
                    '( %s / ( r x. r ) ) = ( %s x. %s )' % (PH, PH, U2))], 'eqtrd', '( %s / ( r ^ 2 ) ) = ( %s x. %s )' % (PH, PH, U2)),
             sr([phc, u2c], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (PH, U2, U2, PH))], 'eqtrd', '( %s / ( r ^ 2 ) ) = ( %s x. %s )' % (PH, U2, PH))
    pr = sr([sr([st1, si], 'eqtrd', 'sum_ t e. %s ( %s x. %s ) = ( %s x. %s )' % (RSN, U, INN, U2, PH)), fr], 'eqtr4d',
            'sum_ t e. %s ( %s x. %s ) = ( %s / ( r ^ 2 ) )' % (RSN, U, INN, PH))
    fin = st([pr], 'sumeq2dv', split_imp(S_['gf2mh1'])[1])
    w.qed([fin], 'idi', S_['gf2mh1'])
    return w


S_['gf2lsc'] = '( ( ( C : NN --> CC /\\ %s ) /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) -> %s e. CC )' % (CBj, LSZ)


def gf2lsc():
    w = W('gf2lsc', 'The Dirichlet series of a bounded ` C ` converges absolutely on ` Re Z > 1 ` (~ zetacvg , ~ cvgcmpce ).')
    a = split_imp(S_['gf2lsc'])[0]
    fin = lscv(w, a, proj(w, a, 'C : NN --> CC'), proj(w, a, CBj), proj(w, a, 'Z e. CC'), proj(w, a, '1 < ( Re ` Z )'))
    w.qed([fin], 'idi', S_['gf2lsc'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
