"""Sortie KD1: Cauchy's estimate for the Taylor coefficient integrals on a square (kdcest)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from kd1_c import sqctx
from mvlib import ringeq
from lin import linarith, lineq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def reim(w, ante, pc, rr):
    """Re/Im of the two corners of SQ(P,R)"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
    A, B = QLO('P', 'R'), QHI('P', 'R')
    RI_ = '( R + ( _i x. R ) )'
    rc = s([rr], 'recnd', 'R e. CC')
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante)
    ric = s([rc, s([ic, rc], 'mulcld', '( _i x. R ) e. CC')], 'addcld', '%s e. CC' % RI_)
    crr = s([rr, rr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = R' % RI_)
    cri = s([rr, rr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = R' % RI_)
    out = {}
    for nm, op, lab, part, cr in (('ReA', '-', 'resub', 'Re', crr), ('ReB', '+', 'readd', 'Re', crr),
                                  ('ImA', '-', 'imsub', 'Im', cri), ('ImB', '+', 'imadd', 'Im', cri)):
        X = A if op == '-' else B
        e1 = s([pc, ric, w.inst(lab)], 'syl2anc', '( %s ` %s ) = ( ( %s ` P ) %s ( %s ` %s ) )' % (part, X, part, op, part, RI_))
        e2 = s([cr], 'oveq2d', '( ( %s ` P ) %s ( %s ` %s ) ) = ( ( %s ` P ) %s R )' % (part, op, part, RI_, part, op))
        out[nm] = s([e1, e2], 'eqtrd', '( %s ` %s ) = ( ( %s ` P ) %s R )' % (part, X, part, op))
    return out


def gen_cest():
    w = W('kdcest', 'Cauchy\'s estimate on a square: a bound ` M ` for ` abs F ` on the frame of ` SQ ( P , R ) ` gives ` abs TC ( F , P , R , K ) <_ 2 M / R ^ K ` ( ML bound ` rectintabse ` , ` crectdis ` , ` 4 / pi <_ 2 ` ).')
    A0 = S['kdcest'].split(' -> ( abs ` ( (')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    fcn = s([], 'simpll', 'F e. ( D -cn-> CC )')
    sqh = s([], 'simplr', '( P e. CC /\\ R e. RR+ /\\ %s C_ D )' % SQ('P', 'R'))
    pc = s([sqh], 'simp1d', 'P e. CC'); rp = s([sqh], 'simp2d', 'R e. RR+'); sqd = s([sqh], 'simp3d', '%s C_ D' % SQ('P', 'R'))
    kk = s([], 'simpr1', 'K e. NN0'); mm = s([], 'simpr2', 'M e. RR')
    FR = FSQ('P', 'R')
    bnd = s([], 'simpr3', 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR)
    q = sqctx(w, A0, pc, rp)
    A, B = q['A'], q['B']
    rr = q['rr']
    SQD = '( %s \\ { P } )' % SQ('P', 'R')
    # continuity of the integrand
    sqcc = s([q['ab'], w.inst('crectss')], 'syl', '%s C_ CC' % SQ('P', 'R'))
    eD = s([w.s([w.s([], 'difss', '%s C_ %s' % (SQD, SQ('P', 'R')))], 'a1i', '( %s -> %s C_ %s )' % (A0, SQD, SQ('P', 'R'))), sqd], 'sstrd', '%s C_ D' % SQD)
    eP = s([sqcc, w.inst('ssdif')], 'syl', '%s C_ ( CC \\ { P } )' % SQD)
    k1 = s([kk, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')
    Gy = '( y e. %s |-> ( ( F ` y ) / ( ( y - P ) ^ ( K + 1 ) ) ) )' % SQD
    G = TCI('F', 'P', 'R', 'K')
    gcy = s([s([fcn, eD], 'jca', '( F e. ( D -cn-> CC ) /\\ %s C_ D )' % SQD), s([pc, eP], 'jca', '( P e. CC /\\ %s C_ ( CC \\ { P } ) )' % SQD), k1, w.inst('cfcn')],
            'syl3anc', '%s e. ( %s -cn-> CC )' % (Gy, SQD))
    cbe = w.s([w.s([w.s([], 'fveq2', '( y = z -> ( F ` y ) = ( F ` z ) )'),
                    w.s([w.s([], 'oveq1', '( y = z -> ( y - P ) = ( z - P ) )')], 'oveq1d', '( y = z -> ( ( y - P ) ^ ( K + 1 ) ) = ( ( z - P ) ^ ( K + 1 ) ) )')],
                   'oveq12d', '( y = z -> ( ( F ` y ) / ( ( y - P ) ^ ( K + 1 ) ) ) = ( ( F ` z ) / ( ( z - P ) ^ ( K + 1 ) ) ) )')], 'cbvmptv', '%s = %s' % (Gy, G))
    gc = s([w.s([cbe], 'a1i', '( %s -> %s = %s )' % (A0, Gy, G)), gcy], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (G, SQD))
    # distance to the frame
    pp = s([q['ab'] and s([pc, pc], 'jca', '( P e. CC /\\ P e. CC )'), rp], 'jca', '( ( P e. CC /\\ P e. CC ) /\\ R e. RR+ )')
    rpl = s([rpr := s([pc], 'recld', '( Re ` P ) e. RR')], 'leidd', '( Re ` P ) <_ ( Re ` P )')
    ipl = s([s([pc], 'imcld', '( Im ` P ) e. RR')], 'leidd', '( Im ` P ) <_ ( Im ` P )')
    pin = s([s([pc, pc], 'jca', '( P e. CC /\\ P e. CC )'), s([rpl, ipl], 'jca', '( ( Re ` P ) <_ ( Re ` P ) /\\ ( Im ` P ) <_ ( Im ` P ) )'), w.inst('crectcnr1')],
            'syl2anc', 'P e. ( P crect P )')
    nest = s([pp, pin, w.inst('holnest')], 'syl2anc', 'T.') if False else None
    NF = formula_of(w, q['inn']).split(' -> ', 1)[1][:-2]
    RBD = ('( ( R <_ ( ( Re ` P ) - ( Re ` %s ) ) /\\ R <_ ( ( Re ` %s ) - ( Re ` P ) ) ) /\\ '
           '( R <_ ( ( Im ` P ) - ( Im ` %s ) ) /\\ R <_ ( ( Im ` %s ) - ( Im ` P ) ) ) )') % (A, B, A, B)
    nest = s([pp, pin, w.inst('holnest')], 'syl2anc', '( %s /\\ ( R e. RR /\\ %s ) )' % (NF, RBD))
    rb = s([nest], 'simprd', '( R e. RR /\\ %s )' % RBD)
    dis = s([q['ab'], q['inn'], rb, w.inst('crectdis')], 'syl3anc', 'A. u e. %s R <_ ( abs ` ( u - P ) )' % FR)
    # pointwise bound on the frame
    Q = '( M / ( R ^ ( K + 1 ) ) )'
    Au = '( %s /\\ v e. %s )' % (A0, FR)
    v = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    ad = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Au, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    uF = v([], 'simpr', 'v e. %s' % FR)
    uS = v([ad(q['fr']), uF], 'sseldd', 'v e. %s' % SQD)
    uc = v([ad(s([w.s([w.s([], 'difss', '%s C_ %s' % (SQD, SQ('P', 'R')))], 'a1i', '( %s -> %s C_ %s )' % (A0, SQD, SQ('P', 'R'))), sqcc], 'sstrd', '%s C_ CC' % SQD)), uS], 'sseldd', 'v e. CC')
    une = v([v([ad(eP), uS], 'sseldd', 'v e. ( CC \\ { P } )'), w.inst('eldifsni')], 'syl', 'v =/= P')
    pcu = ad(pc)
    W_ = '( v - P )'
    wc = v([uc, pcu], 'subcld', '%s e. CC' % W_)
    wn = v([uc, pcu, une], 'subne0d', '%s =/= 0' % W_)
    k1u = ad(k1)
    uD = v([ad(eD), uS], 'sseldd', 'v e. D')
    fu = v([ad(s([fcn, w.inst('cncff')], 'syl', 'F : D --> CC')), uD], 'ffvelcdmd', '( F ` v ) e. CC')
    p1 = '( %s ^ ( K + 1 ) )' % W_
    p1c = v([wc, k1u], 'expcld', '%s e. CC' % p1)
    p1n = v([wc, wn, v([k1u], 'nn0zd', '( K + 1 ) e. ZZ')], 'expne0d', '%s =/= 0' % p1)
    GV = '( ( F ` v ) / %s )' % p1
    gvc = v([fu, p1c, p1n], 'divcld', '%s e. CC' % GV)
    e_g = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )'),
               w.s([w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')], 'oveq1d', '( z = v -> ( ( z - P ) ^ ( K + 1 ) ) = %s )' % p1)],
              'oveq12d', '( z = v -> ( ( F ` z ) / ( ( z - P ) ^ ( K + 1 ) ) ) = %s )' % GV)
    gv = fvmd(w, Au, G, 'v', GV, uS, gvc, e_g)
    AW = '( abs ` %s )' % W_
    a1 = v([gv], 'fveq2d', '( abs ` ( %s ` v ) ) = ( abs ` %s )' % (G, GV))
    a2 = v([fu, p1c, p1n], 'absdivd', '( abs ` %s ) = ( ( abs ` ( F ` v ) ) / ( abs ` %s ) )' % (GV, p1))
    a3 = v([wc, k1u], 'absexpd', '( abs ` %s ) = ( %s ^ ( K + 1 ) )' % (p1, AW))
    a4 = v([a3], 'oveq2d', '( ( abs ` ( F ` v ) ) / ( abs ` %s ) ) = ( ( abs ` ( F ` v ) ) / ( %s ^ ( K + 1 ) ) )' % (p1, AW))
    a5 = v([a1, a2, a4], '3eqtrd', '( abs ` ( %s ` v ) ) = ( ( abs ` ( F ` v ) ) / ( %s ^ ( K + 1 ) ) )' % (G, AW))
    cF = w.s([w.s([w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')], 'breq1d',
             '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )')
    fb = v([uF, ad(bnd), w.s([cF], 'rspcv', '( v e. %s -> ( A. u e. %s ( abs ` ( F ` u ) ) <_ M -> ( abs ` ( F ` v ) ) <_ M ) )' % (FR, FR))], 'sylc', '( abs ` ( F ` v ) ) <_ M')
    cD = w.s([w.s([w.s([], 'oveq1', '( u = v -> ( u - P ) = ( v - P ) )')], 'fveq2d', '( u = v -> ( abs ` ( u - P ) ) = %s )' % AW)], 'breq2d', '( u = v -> ( R <_ ( abs ` ( u - P ) ) <-> R <_ %s ) )' % AW)
    rdu = v([uF, ad(dis), w.s([cD], 'rspcv', '( v e. %s -> ( A. u e. %s R <_ ( abs ` ( u - P ) ) -> R <_ %s ) )' % (FR, FR, AW))], 'sylc', 'R <_ %s' % AW)
    afu = v([fu], 'abscld', '( abs ` ( F ` v ) ) e. RR')
    af0 = v([fu], 'absge0d', '0 <_ ( abs ` ( F ` v ) )')
    mmu = ad(mm)
    m0 = v([af0, fb], 'letrd' if False else 'letrd', '0 <_ M') if False else v([v([], '0red' if False else 'c0ex', 'T.')], 'id', 'T.') if False else \
        w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Au), afu, mmu, af0, fb], 'letrd', '( %s -> 0 <_ M )' % Au)
    awr = v([wc], 'abscld', '%s e. RR' % AW)
    awp = v([wc, wn], 'absrpcld', '%s e. RR+' % AW)
    rpu = ad(rp)
    rru = v([rpu], 'rpred', 'R e. RR')
    pw_r = v([rpu, v([k1u], 'nn0zd', '( K + 1 ) e. ZZ')], 'rpexpcld', '( R ^ ( K + 1 ) ) e. RR+')
    pw_w = v([awp, v([k1u], 'nn0zd', '( K + 1 ) e. ZZ')], 'rpexpcld', '( %s ^ ( K + 1 ) ) e. RR+' % AW)
    lexp = v([rru, awr, k1u, v([rpu], 'rpge0d', '0 <_ R'), rdu], 'leexp1ad', '( R ^ ( K + 1 ) ) <_ ( %s ^ ( K + 1 ) )' % AW)
    b1 = v([afu, mmu, pw_w, fb], 'lediv1dd', '( ( abs ` ( F ` v ) ) / ( %s ^ ( K + 1 ) ) ) <_ ( M / ( %s ^ ( K + 1 ) ) )' % (AW, AW))
    b2 = v([pw_r, pw_w, mmu, m0, lexp], 'lediv2ad', '( M / ( %s ^ ( K + 1 ) ) ) <_ %s' % (AW, Q))
    b3 = v([v([afu, pw_w], 'rerpdivcld', '( ( abs ` ( F ` v ) ) / ( %s ^ ( K + 1 ) ) ) e. RR' % AW), v([mmu, pw_w], 'rerpdivcld', '( M / ( %s ^ ( K + 1 ) ) ) e. RR' % AW),
            v([mmu, pw_r], 'rerpdivcld', '%s e. RR' % Q), b1, b2], 'letrd', '( ( abs ` ( F ` v ) ) / ( %s ^ ( K + 1 ) ) ) <_ %s' % (AW, Q))
    b4 = v([a5, b3], 'eqbrtrd', '( abs ` ( %s ` v ) ) <_ %s' % (G, Q))
    ballv = w.s([b4], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ %s )' % (A0, FR, G, Q))
    cG = w.s([w.s([w.s([], 'fveq2', '( u = v -> ( %s ` u ) = ( %s ` v ) )' % (G, G))], 'fveq2d', '( u = v -> ( abs ` ( %s ` u ) ) = ( abs ` ( %s ` v ) ) )' % (G, G))], 'breq1d',
             '( u = v -> ( ( abs ` ( %s ` u ) ) <_ %s <-> ( abs ` ( %s ` v ) ) <_ %s ) )' % (G, Q, G, Q))
    ball = s([ballv, w.s([cG], 'cbvralvw', '( A. u e. %s ( abs ` ( %s ` u ) ) <_ %s <-> A. v e. %s ( abs ` ( %s ` v ) ) <_ %s )' % (FR, G, Q, FR, G, Q))], 'sylibr' if False else 'sylibr',
             'A. u e. %s ( abs ` ( %s ` u ) ) <_ %s' % (FR, G, Q)) if False else w.s([ballv, w.s([cG], 'cbvralvw', '( A. u e. %s ( abs ` ( %s ` u ) ) <_ %s <-> A. v e. %s ( abs ` ( %s ` v ) ) <_ %s )' % (FR, G, Q, FR, G, Q))], 'sylibr',
             '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ %s )' % (A0, FR, G, Q))
    RI = '( %s rectint <. %s , %s >. )' % (G, A, B)
    qr = s([mm, s([rp, s([k1], 'nn0zd', '( K + 1 ) e. ZZ')], 'rpexpcld', '( R ^ ( K + 1 ) ) e. RR+')], 'rerpdivcld', '%s e. RR' % Q)
    frss = w.s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '( %s -> %s C_ %s )' % (A0, FR, FR))
    h3 = s([gc, frss, q['fr']], '3jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s )' % (G, SQD, FR, FR, FR, SQD))
    h1 = s([q['ab'], q['ordr'], h3], '3jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) )' % (
        A, B, A, B, A, B, G, SQD, FR, FR, FR, SQD))
    DL = '( ( ( Re ` %s ) - ( Re ` %s ) ) + ( ( Im ` %s ) - ( Im ` %s ) ) )' % (B, A, B, A)
    abse = s([h1, qr, ball, w.inst('rectintabse')], 'syl3anc', '( abs ` %s ) <_ ( ( 2 x. %s ) x. %s )' % (RI, Q, DL))
    ri = reim(w, A0, pc, rr)
    c = Closure(w, A0, {'R': ('RR', rr), 'M': ('RR', mm), '( Re ` P )': ('RR', s([pc], 'recld', '( Re ` P ) e. RR')),
                        '( Im ` P )': ('RR', s([pc], 'imcld', '( Im ` P ) e. RR')),
                        '( Re ` %s )' % A: ('RR', s([q['ac']], 'recld', '( Re ` %s ) e. RR' % A)), '( Re ` %s )' % B: ('RR', s([q['bc']], 'recld', '( Re ` %s ) e. RR' % B)),
                        '( Im ` %s )' % A: ('RR', s([q['ac']], 'imcld', '( Im ` %s ) e. RR' % A)), '( Im ` %s )' % B: ('RR', s([q['bc']], 'imcld', '( Im ` %s ) e. RR' % B)),
                        Q: ('RR', qr)})
    for e in ('( Re ` %s )' % A, '( Re ` %s )' % B, '( Im ` %s )' % A, '( Im ` %s )' % B, Q, '( Re ` P )', '( Im ` P )'):
        c.atom(e)
    dl = lineq(w, A0, DL, '( 4 x. R )', hyps=[ri['ReA'], ri['ReB'], ri['ImA'], ri['ImB']], closure=c)
    m1 = s([dl], 'oveq2d', '( ( 2 x. %s ) x. %s ) = ( ( 2 x. %s ) x. ( 4 x. R ) )' % (Q, DL, Q))
    m2 = ringeq(w, A0, '( ( 2 x. %s ) x. ( 4 x. R ) )' % Q, '( 8 x. ( %s x. R ) )' % Q, c)
    X = '( M / ( R ^ K ) )'
    rk = s([rp, s([kk], 'nn0zd', 'K e. ZZ')], 'rpexpcld', '( R ^ K ) e. RR+')
    rkc = s([rk], 'rpcnd', '( R ^ K ) e. CC'); rkn = s([rk], 'rpne0d', '( R ^ K ) =/= 0')
    rc = s([rr], 'recnd', 'R e. CC'); rn = s([rp], 'rpne0d', 'R =/= 0')
    mc = s([mm], 'recnd', 'M e. CC')
    e1 = s([rc, kk], 'expp1d', '( R ^ ( K + 1 ) ) = ( ( R ^ K ) x. R )')
    e2 = s([e1], 'oveq2d', '%s = ( M / ( ( R ^ K ) x. R ) )' % Q)
    e3 = s([mc, rkc, rc, rkn, rn], 'divdiv1d', '( %s / R ) = ( M / ( ( R ^ K ) x. R ) )' % X)
    e4 = s([e2, e3], 'eqtr4d', '%s = ( %s / R )' % (Q, X))
    xc = s([mc, rkc, rkn], 'divcld', '%s e. CC' % X)
    e5 = s([e4], 'oveq1d', '( %s x. R ) = ( ( %s / R ) x. R )' % (Q, X))
    e6 = s([xc, rc, rn], 'divcan1d', '( ( %s / R ) x. R ) = %s' % (X, X))
    e7 = s([e5, e6], 'eqtrd', '( %s x. R ) = %s' % (Q, X))
    m3 = s([e7], 'oveq2d', '( 8 x. ( %s x. R ) ) = ( 8 x. %s )' % (Q, X))
    up1 = s([abse, s([m1, m2, m3], '3eqtrd', '( ( 2 x. %s ) x. %s ) = ( 8 x. %s )' % (Q, DL, X))], 'breqtrd', '( abs ` %s ) <_ ( 8 x. %s )' % (RI, X))
    xr = s([mm, rk], 'rerpdivcld', '%s e. RR' % X)
    aF = s([q['ab'], q['ordr'], w.inst('crectfra')], 'syl2anc', '%s e. %s' % (A, FR))
    cA = w.s([w.s([w.s([], 'fveq2', '( u = %s -> ( F ` u ) = ( F ` %s ) )' % (A, A))], 'fveq2d', '( u = %s -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` %s ) ) )' % (A, A))],
             'breq1d', '( u = %s -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` %s ) ) <_ M ) )' % (A, A))
    rsA = w.s([cA], 'rspcv', '( %s e. %s -> ( A. u e. %s ( abs ` ( F ` u ) ) <_ M -> ( abs ` ( F ` %s ) ) <_ M ) )' % (A, FR, FR, A))
    fA = s([aF, bnd, rsA], 'sylc', '( abs ` ( F ` %s ) ) <_ M' % A)
    aD = s([s([q['fr'], eD], 'sstrd', '%s C_ D' % FR), aF], 'sseldd', '%s e. D' % A)
    fAc = s([s([fcn, w.inst('cncff')], 'syl', 'F : D --> CC'), aD], 'ffvelcdmd', '( F ` %s ) e. CC' % A)
    m0 = s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), s([fAc], 'abscld', '( abs ` ( F ` %s ) ) e. RR' % A), mm, s([fAc], 'absge0d', '0 <_ ( abs ` ( F ` %s ) )' % A), fA],
           'letrd', '0 <_ M')
    x0 = s([mm, rk, m0], 'divge0d' if False else 'divge0d', '0 <_ %s' % X)
    TPI = '( 2 x. ( _i x. _pi ) )'
    c.leaf(X, 'RR', xr); c.have(X, 'ge0', x0)
    c.leaf('_pi', 'RR', w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0))
    p3 = w.s([w.s([], 'pige3', '3 <_ _pi')], 'a1i', '( %s -> 3 <_ _pi )' % A0)
    l84 = linarith(w, A0, [p3], '8 <_ ( 4 x. _pi )', closure=c)
    l8x = s([s([], '8re', '8 e. RR') if False else w.s([w.s([], '8re', '8 e. RR')], 'a1i', '( %s -> 8 e. RR )' % A0), c.mem('( 4 x. _pi )', 'RR'), xr, x0, l84], 'lemul1ad',
            '( 8 x. %s ) <_ ( ( 4 x. _pi ) x. %s )' % (X, X))
    r4 = ringeq(w, A0, '( ( 4 x. _pi ) x. %s )' % X, '( ( 2 x. _pi ) x. ( 2 x. %s ) )' % X, c)
    ric = s([q['ab'], s([gc, q['fr']], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (G, SQD, FR, SQD)), w.inst('rectintcle')], 'syl2anc', '%s e. CC' % RI)
    c.leaf('( abs ` %s )' % RI, 'RR', s([ric], 'abscld', '( abs ` %s ) e. RR' % RI))
    up2 = s([c.mem('( abs ` %s )' % RI, 'RR'), c.mem('( 8 x. %s )' % X, 'RR'), c.mem('( ( 2 x. _pi ) x. ( 2 x. %s ) )' % X, 'RR'), up1, s([l8x, r4], 'breqtrd', '( 8 x. %s ) <_ ( ( 2 x. _pi ) x. ( 2 x. %s ) )' % (X, X))], 'letrd', '( abs ` %s ) <_ ( ( 2 x. _pi ) x. ( 2 x. %s ) )' % (RI, X))
    ric = s([q['ab'], s([gc, q['fr']], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (G, SQD, FR, SQD)), w.inst('rectintcle')], 'syl2anc', '%s e. CC' % RI)
    tpc = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI)],
              'a1i', '( %s -> %s e. CC )' % (A0, TPI))
    tpn = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'),
                    w.s([], '2ne0', '2 =/= 0'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( _i x. _pi ) =/= 0')],
                   'mulne0i', '%s =/= 0' % TPI)], 'a1i', '( %s -> %s =/= 0 )' % (A0, TPI))
    ab1 = s([ric, tpc, tpn], 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (RI, TPI, RI, TPI))
    ab2 = s([w.s([w.s([], 'abstpi', '( abs ` %s ) = ( 2 x. _pi )' % TPI)], 'a1i', '( %s -> ( abs ` %s ) = ( 2 x. _pi ) )' % (A0, TPI))], 'oveq2d',
            '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / ( 2 x. _pi ) )' % (RI, TPI, RI))
    tp2 = s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % A0)], 'rpmulcld', '( 2 x. _pi ) e. RR+')
    lm = s([c.mem('( abs ` %s )' % RI, 'RR'), c.mem('( 2 x. %s )' % X, 'RR'), tp2], 'ledivmuld',
           '( ( ( abs ` %s ) / ( 2 x. _pi ) ) <_ ( 2 x. %s ) <-> ( abs ` %s ) <_ ( ( 2 x. _pi ) x. ( 2 x. %s ) ) )' % (RI, X, RI, X))
    fin1 = s([up2, lm], 'mpbird', '( ( abs ` %s ) / ( 2 x. _pi ) ) <_ ( 2 x. %s )' % (RI, X))
    fin2 = s([s([ab1, ab2], 'eqtrd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( 2 x. _pi ) )' % (RI, TPI, RI)), fin1], 'eqbrtrd', '( abs ` ( %s / %s ) ) <_ ( 2 x. %s )' % (RI, TPI, X))
    dv = s([s([], '2cnd', '2 e. CC') if False else w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), mc, rkc, rkn], 'divassd', '( ( 2 x. M ) / ( R ^ K ) ) = ( 2 x. %s )' % X)
    w.qed([fin2, dv], 'breqtrrd', S['kdcest'])
    return run(w)




if __name__ == '__main__':
    gen_cest()
