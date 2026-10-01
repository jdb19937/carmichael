"""Sortie ZBV2, section 3 part A: products of powers, products over subsets, the
phiSig facts and sum_squarefree_prod_le (ZBV2-blueprint.md section 3.2).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *

PH = 'ph'


def prfacts(w, ante, pel, d):
    """under ante with pel: ( ante -> p e. PRF(d) ): p e. Prime, p || d, p e. NN, RR, RR+, CC, 1 < p, 1 <_ p, 2 <_ p"""
    st = mkst(w, ante)
    pp = sy(w, ante, pel, 'elrabi', 'p e. Prime')
    sub = w.s([], 'breq1', '( q = p -> ( q || %s <-> p || %s ) )' % (d, d))
    el = w.s([sub], 'elrab', '( p e. %s <-> ( p e. Prime /\\ p || %s ) )' % (PRF(d), d))
    pdd = st([st([pel, el], 'sylib', '( p e. Prime /\\ p || %s )' % d)], 'simprd', 'p || %s' % d)
    pnn = sy(w, ante, pp, 'prmnn', 'p e. NN')
    pre = st([pnn], 'nnred', 'p e. RR'); prp = st([pnn], 'nnrpd', 'p e. RR+')
    p1 = sy(w, ante, pp, 'prmgt1', '1 < p')
    return dict(pp=pp, pdd=pdd, nn=pnn, re=pre, rp=prp, cc=st([pnn], 'nncnd', 'p e. CC'), ne=st([prp], 'rpne0d', 'p =/= 0'), gt1=p1,
                ge1=st([st([], '1red', '1 e. RR'), pre, p1], 'ltled', '1 <_ p'), ge2=sy(w, ante, sy(w, ante, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), 'eluzle', '2 <_ p'))


def cxpfacts(w, ante, pf, sr, s0):
    """( p ^c S ) e. RR+, RR, 1 <_ ( p ^c S ), ( ( p ^c S ) - 1 ) e. RR, 0 <_ it, <_ ( p ^c S )"""
    st = mkst(w, ante)
    PS = '( p ^c S )'
    rp = st([pf['rp'], sr], 'rpcxpcld', '%s e. RR+' % PS); re = st([rp], 'rpred', '%s e. RR' % PS)
    le = st([pf['re'], pf['ge1'], st([], '0red', '0 e. RR'), sr, s0], 'cxplead', '( p ^c 0 ) <_ %s' % PS)
    ge1 = st([st([st([pf['cc']], 'cxp0d', '( p ^c 0 ) = 1')], 'eqcomd', '1 = ( p ^c 0 )'), le], 'eqbrtrd', '1 <_ %s' % PS)
    m1re = st([re, st([], '1red', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % PS)
    m10 = linarith(w, ante, [ge1], '0 <_ ( %s - 1 )' % PS, leaves={PS: re})
    return dict(rp=rp, re=re, ge1=ge1, m1re=m1re, m10=m10, m1le=st([re], 'lem1d', '( %s - 1 ) <_ %s' % (PS, PS)))


def bvfprodcxp():
    w = W('bvfprodcxp', 'A finite product of real powers is the power of the product: prod_ k e. A ( ( F ` k ) ^c S ) '
                        '= ( prod_ k e. A ( F ` k ) ) ^c S (through exp and log; Mathlib finsetProd_rpow).')
    h1, h2, h3 = hyps_of(w, 'bvfprodcxp')
    st = mkst(w, PH)
    AK = '( ph /\\ k e. A )'
    sk = mkst(w, AK)
    kel = sk([], 'simpr', 'k e. A')
    FK = '( F ` k )'
    fkc = sk([h3], 'rpcnd', '%s e. CC' % FK); fkne = sk([h3], 'rpne0d', '%s =/= 0' % FK)
    lg = sk([h3], 'relogcld', '( log ` %s ) e. RR' % FK); lgc = sk([lg], 'recnd', '( log ` %s ) e. CC' % FK)
    sc = st([h2], 'recnd', 'S e. CC')
    c1 = sk([fkc, fkne, lift(w, sc, AK)], 'cxpefd', '( %s ^c S ) = ( exp ` ( S x. ( log ` %s ) ) )' % (FK, FK))
    e1 = st([c1], 'prodeq2dv', 'prod_ k e. A ( %s ^c S ) = prod_ k e. A ( exp ` ( S x. ( log ` %s ) ) )' % (FK, FK))
    # F1 = ( t e. A |-> ( S x. ( log ` ( F ` t ) ) ) )
    F1 = '( t e. A |-> ( S x. ( log ` ( F ` t ) ) ) )'
    v1, _ = mpv(w, AK, 't', 'A', '( S x. ( log ` ( F ` t ) ) )', 'k', kel)
    slc = sk([lift(w, sc, AK), lgc], 'mulcld', '( S x. ( log ` %s ) ) e. CC' % FK)
    f1c = sk([v1, slc], 'eqeltrd', '( %s ` k ) e. CC' % F1)
    pe = w.s([h1, f1c], 'fprodefsumfi', '( ph -> prod_ k e. A ( exp ` ( %s ` k ) ) = ( exp ` sum_ k e. A ( %s ` k ) ) )' % (F1, F1))
    e2 = st([sk([sk([v1], 'eqcomd', '( S x. ( log ` %s ) ) = ( %s ` k )' % (FK, F1))], 'fveq2d', '( exp ` ( S x. ( log ` %s ) ) ) = ( exp ` ( %s ` k ) )' % (FK, F1))], 'prodeq2dv',
            'prod_ k e. A ( exp ` ( S x. ( log ` %s ) ) ) = prod_ k e. A ( exp ` ( %s ` k ) )' % (FK, F1))
    SL = 'sum_ k e. A ( log ` %s )' % FK
    e3 = st([st([v1], 'sumeq2dv', 'sum_ k e. A ( %s ` k ) = sum_ k e. A ( S x. ( log ` %s ) )' % (F1, FK)), st([st([h1, sc, lgc], 'fsummulc2', '( S x. %s ) = sum_ k e. A ( S x. ( log ` %s ) )' % (SL, FK))], 'eqcomd', 'sum_ k e. A ( S x. ( log ` %s ) ) = ( S x. %s )' % (FK, SL))], 'eqtrd',
            'sum_ k e. A ( %s ` k ) = ( S x. %s )' % (F1, SL))
    lhs = eqtr(w, PH, [e1, e2, pe, st([e3], 'fveq2d', '( exp ` sum_ k e. A ( %s ` k ) ) = ( exp ` ( S x. %s ) )' % (F1, SL))], None)
    # prod_ F = exp ( sum_ log F )
    F2 = '( t e. A |-> ( log ` ( F ` t ) ) )'
    v2, _ = mpv(w, AK, 't', 'A', '( log ` ( F ` t ) )', 'k', kel)
    f2c = sk([v2, lgc], 'eqeltrd', '( %s ` k ) e. CC' % F2)
    pe2 = w.s([h1, f2c], 'fprodefsumfi', '( ph -> prod_ k e. A ( exp ` ( %s ` k ) ) = ( exp ` sum_ k e. A ( %s ` k ) ) )' % (F2, F2))
    ef = sk([sk([v2], 'fveq2d', '( exp ` ( %s ` k ) ) = ( exp ` ( log ` %s ) )' % (F2, FK)), sy(w, AK, h3, 'reeflog', '( exp ` ( log ` %s ) ) = %s' % (FK, FK))], 'eqtrd', '( exp ` ( %s ` k ) ) = %s' % (F2, FK))
    PF = 'prod_ k e. A %s' % FK
    pfeq = st([st([st([ef], 'prodeq2dv', 'prod_ k e. A ( exp ` ( %s ` k ) ) = %s' % (F2, PF))], 'eqcomd', '%s = prod_ k e. A ( exp ` ( %s ` k ) )' % (PF, F2)), pe2], 'eqtrd', '%s = ( exp ` sum_ k e. A ( %s ` k ) )' % (PF, F2))
    pfeq2 = st([pfeq, st([st([v2], 'sumeq2dv', 'sum_ k e. A ( %s ` k ) = %s' % (F2, SL))], 'fveq2d', '( exp ` sum_ k e. A ( %s ` k ) ) = ( exp ` %s )' % (F2, SL))], 'eqtrd', '%s = ( exp ` %s )' % (PF, SL))
    slr = st([h1, lg], 'fsumrecl', '%s e. RR' % SL)
    lgpf = st([st([pfeq2], 'fveq2d', '( log ` %s ) = ( log ` ( exp ` %s ) )' % (PF, SL)), sy(w, PH, slr, 'relogef', '( log ` ( exp ` %s ) ) = %s' % (SL, SL))], 'eqtrd', '( log ` %s ) = %s' % (PF, SL))
    pfrp = st([h1, h3], 'fprodrpcl', '%s e. RR+' % PF)
    rhs = st([st([st([pfrp], 'rpcnd', '%s e. CC' % PF), st([pfrp], 'rpne0d', '%s =/= 0' % PF), sc], 'cxpefd', '( %s ^c S ) = ( exp ` ( S x. ( log ` %s ) ) )' % (PF, PF)),
              st([st([lgpf], 'oveq2d', '( S x. ( log ` %s ) ) = ( S x. %s )' % (PF, SL))], 'fveq2d', '( exp ` ( S x. ( log ` %s ) ) ) = ( exp ` ( S x. %s ) )' % (PF, SL))], 'eqtrd',
             '( %s ^c S ) = ( exp ` ( S x. %s ) )' % (PF, SL))
    w.qed([lhs, rhs], 'eqtr4d', STATEMENTS['bvfprodcxp'])
    return w


def bvprodle1():
    w = W('bvprodle1', 'A product of factors >= 1 grows with the index set (Lean prod_le_prod_subset_one_le).')
    h1, h2, h3, h4 = hyps_of(w, 'bvprodle1')
    st = mkst(w, PH)
    DIFF = '( B \\ A )'
    un = st([st([h2, w.inst('undif')], 'sylib', '( A u. %s ) = B' % DIFF)], 'eqcomd', 'B = ( A u. %s )' % DIFF)
    dj = st([clo(w, 'disjdif', '( A i^i %s ) = (/)' % DIFF)], 'a1i', '( A i^i %s ) = (/)' % DIFF)
    AB = '( ph /\\ k e. B )'
    sb = mkst(w, AB)
    cc = sb([h3], 'recnd', 'C e. CC')
    split = st([dj, un, h1, cc], 'fprodsplit', 'prod_ k e. B C = ( prod_ k e. A C x. prod_ k e. %s C )' % DIFF)
    nf = w.s([], 'nfv', 'F/ k ph')
    afin = st([h1, h2], 'ssfid', 'A e. Fin')
    AA = '( ph /\\ k e. A )'
    sa = mkst(w, AA)
    kb = sa([lift(w, h2, AA), sa([], 'simpr', 'k e. A')], 'sseldd', 'k e. B')
    cra = hyp2(w, AA, sa([], 'simpl', 'ph'), kb, h3, 'C e. RR'); c1a = hyp2(w, AA, sa([], 'simpl', 'ph'), kb, h4, '1 <_ C')
    c0a = linarith(w, AA, [c1a], '0 <_ C', leaves={'C': cra})
    pa0 = st([nf, afin, cra, c0a], 'fprodge0', '0 <_ prod_ k e. A C')
    dfin = sy(w, PH, h1, 'diffi', '%s e. Fin' % DIFF)
    AD = '( ph /\\ k e. %s )' % DIFF
    sd = mkst(w, AD)
    kbd = sy(w, AD, sd([], 'simpr', 'k e. %s' % DIFF), 'eldifi', 'k e. B')
    crd = hyp2(w, AD, sd([], 'simpl', 'ph'), kbd, h3, 'C e. RR'); c1d = hyp2(w, AD, sd([], 'simpl', 'ph'), kbd, h4, '1 <_ C')
    pd1 = st([nf, dfin, crd, c1d], 'fprodge1', '1 <_ prod_ k e. %s C' % DIFF)
    par = st([afin, cra], 'fprodrecl', 'prod_ k e. A C e. RR'); pdr = st([dfin, crd], 'fprodrecl', 'prod_ k e. %s C e. RR' % DIFF)
    le = st([par, pdr, pa0, pd1], 'lemulge11d', 'prod_ k e. A C <_ ( prod_ k e. A C x. prod_ k e. %s C )' % DIFF)
    w.qed([le, split], 'breqtrrd', STATEMENTS['bvprodle1'])
    return w


def bvphisg0():
    w = W('bvphisg0', 'phiSig is nonnegative (Lean phiSig_nonneg).')
    A = '( %s /\\ Q e. NN )' % HS0
    st = mkst(w, A)
    hs = st([], 'simpl', HS0); sr = st([hs], 'simpld', 'S e. RR'); s0 = st([hs], 'simprd', '0 <_ S'); qnn = st([], 'simpr', 'Q e. NN')
    AP = '( %s /\\ p e. %s )' % (A, PRF('Q'))
    sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF('Q')), 'Q')
    cf = cxpfacts(w, AP, pf, lift(w, sr, AP), lift(w, s0, AP))
    w.qed([w.s([], 'nfv', 'F/ p %s' % A), sy(w, A, qnn, 'pffinq', '%s e. Fin' % PRF('Q')), cf['m1re'], cf['m10']], 'fprodge0', STATEMENTS['bvphisg0'])
    return w


def bvsqdv():
    w = W('bvsqdv', 'The squarefree divisors of a squarefree number are all its divisors (dvdssqf).')
    A = SQF('N')
    st = mkst(w, A)
    nnn = st([], 'simpl', 'N e. NN'); mu = st([], 'simpr', '( mmu ` N ) =/= 0')
    AX = '( %s /\\ x e. NN )' % A
    sx = mkst(w, AX)
    AX2 = '( %s /\\ x || N )' % AX
    s2 = mkst(w, AX2)
    ds = w.s([bind3(w, AX2, lift(w, nnn, AX2), lift(w, sx([], 'simpr', 'x e. NN'), AX2), s2([], 'simpr', 'x || N'), 'N e. NN', 'x e. NN', 'x || N'), w.inst('dvdssqf')], 'syl',
             '( %s -> ( ( mmu ` N ) =/= 0 -> ( mmu ` x ) =/= 0 ) )' % AX2)
    mx = s2([lift(w, mu, AX2), ds], 'mpd', '( mmu ` x ) =/= 0')
    imp = w.s([mx], 'ex', '( %s -> ( x || N -> ( mmu ` x ) =/= 0 ) )' % AX)
    bi = sx([sx([imp], 'pm4.71rd', '( x || N <-> ( ( mmu ` x ) =/= 0 /\\ x || N ) )')], 'bicomd', '( ( ( mmu ` x ) =/= 0 /\\ x || N ) <-> x || N )')
    w.qed([bi], 'rabbidva', STATEMENTS['bvsqdv'])
    return w


def prodcxp_prf(w, A, Q, qnn, sr):
    """( A -> prod_ p e. PRF(Q) ( p ^c S ) = ( prod_ p e. PRF(Q) p ^c S ) ) by bvfprodcxp with F = ( t e. NN |-> t )"""
    st = mkst(w, A)
    F = '( t e. NN |-> t )'
    AP = '( %s /\\ p e. %s )' % (A, PRF(Q))
    sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF(Q)), Q)
    v, _ = mpv(w, AP, 't', 'NN', 't', 'p', pf['nn'], exs=sp([pf['nn']], 'elexd', 'p e. _V'))
    frp = sp([v, pf['rp']], 'eqeltrd', '( %s ` p ) e. RR+' % F)
    fin = sy(w, A, qnn, 'pffinq', '%s e. Fin' % PRF(Q))
    pc = w.s([fin, sr, frp], 'bvfprodcxp', '( %s -> prod_ p e. %s ( ( %s ` p ) ^c S ) = ( prod_ p e. %s ( %s ` p ) ^c S ) )' % (A, PRF(Q), F, PRF(Q), F))
    l = st([st([sp([v], 'oveq1d', '( ( %s ` p ) ^c S ) = ( p ^c S )' % F)], 'prodeq2dv', 'prod_ p e. %s ( ( %s ` p ) ^c S ) = prod_ p e. %s ( p ^c S )' % (PRF(Q), F, PRF(Q)))], 'eqcomd',
           'prod_ p e. %s ( p ^c S ) = prod_ p e. %s ( ( %s ` p ) ^c S )' % (PRF(Q), PRF(Q), F))
    r = st([st([st([v], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = prod_ p e. %s p' % (PRF(Q), F, PRF(Q)))], 'oveq1d', '( prod_ p e. %s ( %s ` p ) ^c S ) = ( prod_ p e. %s p ^c S )' % (PRF(Q), F, PRF(Q)))], 'id',
           '( prod_ p e. %s ( %s ` p ) ^c S ) = ( prod_ p e. %s p ^c S )' % (PRF(Q), F, PRF(Q))) if False else st([st([v], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = prod_ p e. %s p' % (PRF(Q), F, PRF(Q)))], 'oveq1d', '( prod_ p e. %s ( %s ` p ) ^c S ) = ( prod_ p e. %s p ^c S )' % (PRF(Q), F, PRF(Q)))
    return eqtr(w, A, [l, pc, r], None), pf


def bvphisgle():
    w = W('bvphisgle', 'phiSig ( Q ) <= Q ^c S for squarefree Q (Lean phiSig_le_rpow).')
    A = '( %s /\\ %s )' % (HS0, SQF('Q'))
    st = mkst(w, A)
    hs = st([], 'simpl', HS0); sr = st([hs], 'simpld', 'S e. RR'); s0 = st([hs], 'simprd', '0 <_ S')
    sq = st([], 'simpr', SQF('Q')); qnn = st([sq], 'simpld', 'Q e. NN')
    AP = '( %s /\\ p e. %s )' % (A, PRF('Q'))
    sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF('Q')), 'Q')
    cf = cxpfacts(w, AP, pf, lift(w, sr, AP), lift(w, s0, AP))
    fin = sy(w, A, qnn, 'pffinq', '%s e. Fin' % PRF('Q'))
    le = st([w.s([], 'nfv', 'F/ p %s' % A), fin, cf['m1re'], cf['m10'], cf['re'], cf['m1le']], 'fprodle', '%s <_ prod_ p e. %s ( p ^c S )' % (PHS('S', 'Q'), PRF('Q')))
    pc, _ = prodcxp_prf(w, A, 'Q', qnn, sr)
    sp_id = sy(w, A, sq, 'sqfprodid', 'prod_ p e. %s p = Q' % PRF('Q'))
    eq = st([pc, st([sp_id], 'oveq1d', '( prod_ p e. %s p ^c S ) = ( Q ^c S )' % PRF('Q'))], 'eqtrd', 'prod_ p e. %s ( p ^c S ) = ( Q ^c S )' % PRF('Q'))
    w.qed([le, eq], 'breqtrd', STATEMENTS['bvphisgle'])
    return w


def bvphisgsum():
    w = W('bvphisgsum', 'Identity (9): for squarefree N, sum_ d || N phiSig ( d ) = N ^c S (sqfdvdsum at G = ( t ^c S ) - 1).')
    A = '( S e. RR /\\ %s )' % SQF('N')
    st = mkst(w, A)
    sr = st([], 'simpl', 'S e. RR'); sq = st([], 'simpr', SQF('N')); nnn = st([sq], 'simpld', 'N e. NN')
    G = '( t e. Prime |-> ( ( t ^c S ) - 1 ) )'
    AT = '( %s /\\ t e. Prime )' % A
    stt = mkst(w, AT)
    tnn = sy(w, AT, stt([], 'simpr', 't e. Prime'), 'prmnn', 't e. NN')
    tc = stt([stt([stt([tnn], 'nnrpd', 't e. RR+'), lift(w, sr, AT)], 'rpcxpcld', '( t ^c S ) e. RR+')], 'rpcnd', '( t ^c S ) e. CC')
    gc = stt([tc, stt([], '1cnd', '1 e. CC')], 'subcld', '( ( t ^c S ) - 1 ) e. CC')
    gf = st([gc], 'fmpttd', '%s : Prime --> CC' % G)
    sd = st([nnn, gf, w.inst('sqfdvdsum')], 'syl2anc', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )' % (SQDV('N'), PRF('d'), G, PRF('N'), G))
    # values of G
    AD = '( %s /\\ d e. %s )' % (A, SQDV('N')); sdd = mkst(w, AD)
    ADP = '( %s /\\ p e. %s )' % (AD, PRF('d')); sdp = mkst(w, ADP)
    pfd = prfacts(w, ADP, sdp([], 'simpr', 'p e. %s' % PRF('d')), 'd')
    vd, _ = mpv(w, ADP, 't', 'Prime', '( ( t ^c S ) - 1 )', 'p', pfd['pp'])
    lhs = st([st([sdd([vd], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( ( p ^c S ) - 1 )' % (PRF('d'), G, PRF('d')))], 'sumeq2dv',
                 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s %s' % (SQDV('N'), PRF('d'), G, SQDV('N'), PHS('S', 'd'))),
              st([sy(w, A, sq, 'bvsqdv', '%s = %s' % (SQDV('N'), DV('N')))], 'sumeq1d', 'sum_ d e. %s %s = sum_ d e. %s %s' % (SQDV('N'), PHS('S', 'd'), DV('N'), PHS('S', 'd')))], 'eqtrd',
             'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s %s' % (SQDV('N'), PRF('d'), G, DV('N'), PHS('S', 'd')))
    AN = '( %s /\\ p e. %s )' % (A, PRF('N')); snp = mkst(w, AN)
    pfn = prfacts(w, AN, snp([], 'simpr', 'p e. %s' % PRF('N')), 'N')
    vn, _ = mpv(w, AN, 't', 'Prime', '( ( t ^c S ) - 1 )', 'p', pfn['pp'])
    psc = snp([snp([pfn['rp'], lift(w, sr, AN)], 'rpcxpcld', '( p ^c S ) e. RR+')], 'rpcnd', '( p ^c S ) e. CC')
    one = snp([snp([vn], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + ( ( p ^c S ) - 1 ) )' % G), snp([snp([], '1cnd', '1 e. CC'), psc], 'pncan3d', '( 1 + ( ( p ^c S ) - 1 ) ) = ( p ^c S )')], 'eqtrd', '( 1 + ( %s ` p ) ) = ( p ^c S )' % G)
    pc, _ = prodcxp_prf(w, A, 'N', nnn, sr)
    rhs = eqtr(w, A, [st([one], 'prodeq2dv', 'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s ( p ^c S )' % (PRF('N'), G, PRF('N'))), pc,
                      st([sy(w, A, sq, 'sqfprodid', 'prod_ p e. %s p = N' % PRF('N'))], 'oveq1d', '( prod_ p e. %s p ^c S ) = ( N ^c S )' % PRF('N'))], None)
    w.qed([st([lhs], 'eqcomd', 'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s ( %s ` p )' % (DV('N'), PHS('S', 'd'), SQDV('N'), PRF('d'), G)), st([sd, rhs], 'eqtrd', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = ( N ^c S )' % (SQDV('N'), PRF('d'), G))], 'eqtrd', STATEMENTS['bvphisgsum'])
    return w


def bvsqfsumlem1():
    w = W('bvsqfsumlem1', 'A squarefree D <= M is a squarefree divisor of the radical prod_ p e. PR(M) p (sqfdvdprod).')
    A = '( M e. NN /\\ ( D e. ( 1 ... M ) /\\ ( mmu ` D ) =/= 0 ) )'
    st = mkst(w, A)
    mnn = st([], 'simpl', 'M e. NN'); dfz = st([], 'simprl', 'D e. ( 1 ... M )'); mu = st([], 'simprr', '( mmu ` D ) =/= 0')
    dvp = st([bind(w, A, mnn, dfz, 'M e. NN', 'D e. ( 1 ... M )'), mu, w.inst('sqfdvdprod')], 'syl2anc', 'D || %s' % RADP('M'))
    dv = st([dvp, radeq(w, A)], 'breqtrd', 'D || %s' % RAD('M'))
    dnn = sy(w, A, dfz, 'elfznn', 'D e. NN')
    idx = w.s([], 'id', '( x = D -> x = D )')
    sub, new = w.wcongr('( ( mmu ` x ) =/= 0 /\\ x || %s )' % RAD('M'), {'x': 'D'}, 'x = D', {'x': idx})
    el = w.s([sub], 'elrab', '( D e. %s <-> ( D e. NN /\\ %s ) )' % (SQDV(RAD('M')), new))
    w.qed([bind(w, A, dnn, bind(w, A, mu, dv, '( mmu ` D ) =/= 0', 'D || %s' % RAD('M')), 'D e. NN', new), st([el], 'a1i', '( D e. %s <-> ( D e. NN /\\ %s ) )' % (SQDV(RAD('M')), new))], 'mpbird', STATEMENTS['bvsqfsumlem1'])
    return w


def radeq(w, A, m='M'):
    """( A -> RADP(m) = RAD(m) ) by cbvprodv"""
    cb = w.s([w.s([], 'id', '( p = r -> p = r )')], 'cbvprodv', '%s = %s' % (RADP(m), RAD(m)))
    return w.s([cb], 'a1i', '( %s -> %s = %s )' % (A, RADP(m), RAD(m)))


def ifvex(w, ante, val):
    """( ante -> if ( c , ( W ` t ) , 0 ) e. _V )"""
    inner = val[len('if ( '):-2]
    from cl import split_sep
    cond, A_, B_ = split_sep(inner.split(), (',',))
    ea = w.s([], 'fvexd', '( %s -> %s e. _V )' % (ante, A_))
    eb = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ante)
    return w.s([ea, eb], 'ifexd', '( %s -> %s e. _V )' % (ante, val))


def radfacts(w, A, mnn):
    """PR(M) e. Fin, PR(M) C_ Prime, RAD(M) e. NN, PRF(RAD(M)) = PR(M) (sqfprod)"""
    st = mkst(w, A)
    fin = st([st([clo(w, 'fzfi', '( 1 ... M ) e. Fin')], 'a1i', '( 1 ... M ) e. Fin'), st([clo(w, 'inss1', '%s C_ ( 1 ... M )' % PR('M'))], 'a1i', '%s C_ ( 1 ... M )' % PR('M'))], 'ssfid', '%s e. Fin' % PR('M'))
    ss = st([clo(w, 'inss2', '%s C_ Prime' % PR('M'))], 'a1i', '%s C_ Prime' % PR('M'))
    sp = sy2(w, A, fin, ss, 'sqfprod', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )' % (RADP('M'), RADP('M'), PRF(RADP('M')), PR('M')))
    both = st([sp], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (RADP('M'), RADP('M')))
    eq = radeq(w, A)
    radnn = st([eq, st([both], 'simpld', '%s e. NN' % RADP('M'))], 'eqeltrrd', '%s e. NN' % RAD('M'))
    prfeq, _ = w.rewrite(PRF(RADP('M')), {RADP('M'): (RAD('M'), eq)}, A)
    prf = st([st([prfeq], 'eqcomd', '%s = %s' % (PRF(RAD('M')), PRF(RADP('M')))), st([sp], 'simprd', '%s = %s' % (PRF(RADP('M')), PR('M')))], 'eqtrd', '%s = %s' % (PRF(RAD('M')), PR('M')))
    return dict(fin=fin, ss=ss, radnn=radnn, prf=prf, eq=eq)


def bvsqfsumlem2():
    w = W('bvsqfsumlem2', 'The prime factors of a squarefree divisor of the radical lie in ( 2 ... M ) (sqfprod, zdmprss).')
    A = '( M e. NN /\\ D e. %s )' % SQDV(RAD('M'))
    st = mkst(w, A)
    mnn = st([], 'simpl', 'M e. NN'); del_ = st([], 'simpr', 'D e. %s' % SQDV(RAD('M')))
    r = radfacts(w, A, mnn)
    idx = w.s([], 'id', '( x = D -> x = D )')
    sub, new = w.wcongr('( ( mmu ` x ) =/= 0 /\\ x || %s )' % RAD('M'), {'x': 'D'}, 'x = D', {'x': idx})
    el = w.s([sub], 'elrab', '( D e. %s <-> ( D e. NN /\\ %s ) )' % (SQDV(RAD('M')), new))
    parts = st([del_, st([el], 'a1i', '( D e. %s <-> ( D e. NN /\\ %s ) )' % (SQDV(RAD('M')), new))], 'mpbid', '( D e. NN /\\ %s )' % new)
    dnn = st([parts], 'simpld', 'D e. NN'); ddv = st([st([parts], 'simprd', new)], 'simprd', 'D || %s' % RAD('M'))
    AQ = '( %s /\\ y e. %s )' % (A, PRF('D'))
    sq = mkst(w, AQ)
    qel = sq([], 'simpr', 'y e. %s' % PRF('D'))
    subd = w.s([], 'breq1', '( q = y -> ( q || D <-> y || D ) )')
    elq = w.s([subd], 'elrab', '( y e. %s <-> ( y e. Prime /\\ y || D ) )' % PRF('D'))
    qpd = sq([qel, elq], 'sylib', '( y e. Prime /\\ y || D )')
    qp = sq([qpd], 'simpld', 'y e. Prime'); qdd = sq([qpd], 'simprd', 'y || D')
    qz = sy(w, AQ, qp, 'prmz', 'y e. ZZ')
    tr = w.s([bind3(w, AQ, qz, sq([lift(w, dnn, AQ)], 'nnzd', 'D e. ZZ'), sq([lift(w, r['radnn'], AQ)], 'nnzd', '%s e. ZZ' % RAD('M')), 'y e. ZZ', 'D e. ZZ', '%s e. ZZ' % RAD('M')), w.inst('dvdstr')], 'syl',
             '( %s -> ( ( y || D /\\ D || %s ) -> y || %s ) )' % (AQ, RAD('M'), RAD('M')))
    qdr = sq([bind(w, AQ, qdd, lift(w, ddv, AQ), 'y || D', 'D || %s' % RAD('M')), tr], 'mpd', 'y || %s' % RAD('M'))
    subr = w.s([], 'breq1', '( q = y -> ( q || %s <-> y || %s ) )' % (RAD('M'), RAD('M')))
    elr = w.s([subr], 'elrab', '( y e. %s <-> ( y e. Prime /\\ y || %s ) )' % (PRF(RAD('M')), RAD('M')))
    qin = sq([bind(w, AQ, qp, qdr, 'y e. Prime', 'y || %s' % RAD('M')), sq([elr], 'a1i', '( y e. %s <-> ( y e. Prime /\\ y || %s ) )' % (PRF(RAD('M')), RAD('M')))], 'mpbird', 'y e. %s' % PRF(RAD('M')))
    qpr = sq([qin, lift(w, r['prf'], AQ)], 'eleqtrd', 'y e. %s' % PR('M'))
    q2m = sq([sq([clo(w, 'zdmprss', '%s C_ ( 2 ... M )' % PR('M'))], 'a1i', '%s C_ ( 2 ... M )' % PR('M')), qpr], 'sseldd', 'y e. ( 2 ... M )')
    q2m = w.s([q2m], 'ex', '( %s -> ( y e. %s -> y e. ( 2 ... M ) ) )' % (A, PRF('D')))
    w.qed([q2m], 'ssrdv', STATEMENTS['bvsqfsumlem2'])
    return w


def bvsqfsum():
    w = W('bvsqfsum', 'Squarefree sum <= Euler product (Lean sum_squarefree_prod_le): sum_ a <= M mmu^2 ( a ) prod_ p || a W ( p ) '
                      '<= prod_ 2 <= n <= M ( 1 + W ( n ) ), by sqfdvdsum at the radical of ( 1 ... M ).')
    h1, h2, h3 = hyps_of(w, 'bvsqfsum')
    st = mkst(w, PH)
    r = radfacts(w, PH, h1)
    R1 = '( 1 ... M )'; SQ = '{ x e. %s | ( mmu ` x ) =/= 0 }' % R1; SDR = SQDV(RAD('M'))
    TERM = lambda a: 'prod_ p e. %s ( W ` p )' % PRF(a)
    IFT = lambda a: 'if ( ( mmu ` %s ) =/= 0 , %s , 0 )' % (a, TERM(a))
    fin1 = st([], 'fzfid', '%s e. Fin' % R1)
    # W ( p ) real and nonnegative for p e. PRF(d), d e. SDR (through lem2)
    def wfacts(ante, dstep, d):
        """under ante with dstep: ( ante -> d e. SDR ): ( ( ante /\\ p e. PRF(d) ) -> ( W ` p ) e. RR ), 0 <_ ( W ` p ); returns (re, ge0, cc)"""
        AP = '( %s /\\ p e. %s )' % (ante, PRF(d)); sp = mkst(w, AP)
        ss = w.s([bind(w, ante, lift(w, h1, ante), dstep, 'M e. NN', '%s e. %s' % (d, SDR)), w.inst('bvsqfsumlem2')], 'syl', '( %s -> %s C_ ( 2 ... M ) )' % (ante, PRF(d)))
        p2m = sp([lift(w, ss, AP), sp([], 'simpr', 'p e. %s' % PRF(d))], 'sseldd', 'p e. ( 2 ... M )')
        h2p, _ = rename(w, PH, '( 2 ... M )', 'n', 'p', h2, '( W ` n ) e. RR'); h3p, _ = rename(w, PH, '( 2 ... M )', 'n', 'p', h3, '0 <_ ( W ` n )')
        re = hyp2(w, AP, lift(w, w.s([], 'id', '( ph -> ph )'), AP), p2m, h2p, '( W ` p ) e. RR')
        ge = hyp2(w, AP, lift(w, w.s([], 'id', '( ph -> ph )'), AP), p2m, h3p, '0 <_ ( W ` p )')
        return re, ge, sp([re], 'recnd', '( W ` p ) e. CC'), AP
    # step A: the if-sum is the sum over SQ
    AD1 = '( ph /\\ a e. ( %s \\ %s ) )' % (R1, SQ); sd1 = mkst(w, AD1)
    eld = sd1([sd1([], 'simpr', 'a e. ( %s \\ %s )' % (R1, SQ)), w.inst('eldif')], 'sylib', '( a e. %s /\\ -. a e. %s )' % (R1, SQ))
    idxa = w.s([], 'id', '( x = a -> x = a )'); suba, _ = w.wcongr('( mmu ` x ) =/= 0', {'x': 'a'}, 'x = a', {'x': idxa})
    ela = w.s([suba], 'elrab', '( a e. %s <-> ( a e. %s /\\ ( mmu ` a ) =/= 0 ) )' % (SQ, R1))
    nmu = sd1([sd1([sd1([eld], 'simprd', '-. a e. %s' % SQ), ela], 'sylnib', '-. ( a e. %s /\\ ( mmu ` a ) =/= 0 )' % R1), w.inst('imnan')], 'sylibr', '( a e. %s -> -. ( mmu ` a ) =/= 0 )' % R1)
    nmu2 = sd1([sd1([eld], 'simpld', 'a e. %s' % R1), nmu], 'mpd', '-. ( mmu ` a ) =/= 0')
    zero = sd1([nmu2], 'iffalsed', '%s = 0' % IFT('a'))
    ASQ = '( ph /\\ a e. %s )' % SQ; ssq = mkst(w, ASQ)
    asq = ssq([ssq([], 'simpr', 'a e. %s' % SQ), ela], 'sylib', '( a e. %s /\\ ( mmu ` a ) =/= 0 )' % R1)
    ar1 = ssq([asq], 'simpld', 'a e. %s' % R1); amu = ssq([asq], 'simprd', '( mmu ` a ) =/= 0')
    ain = w.s([bind(w, ASQ, lift(w, h1, ASQ), bind(w, ASQ, ar1, amu, 'a e. %s' % R1, '( mmu ` a ) =/= 0'), 'M e. NN', '( a e. %s /\\ ( mmu ` a ) =/= 0 )' % R1), w.inst('bvsqfsumlem1')], 'syl', '( %s -> a e. %s )' % (ASQ, SDR))
    wre, wge, wcc, APa = wfacts(ASQ, ain, 'a')
    ann = sy(w, ASQ, ar1, 'elfznn', 'a e. NN')
    tc = ssq([sy(w, ASQ, ann, 'pffinq', '%s e. Fin' % PRF('a')), wcc], 'fprodcl', '%s e. CC' % TERM('a'))
    ifc = ssq([tc, ssq([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFT('a'))
    sub = st([clo(w, 'ssrab2', '%s C_ %s' % (SQ, R1))], 'a1i', '%s C_ %s' % (SQ, R1))
    S0 = 'sum_ a e. %s %s' % (R1, IFT('a')); S1 = 'sum_ a e. %s %s' % (SQ, IFT('a')); S2 = 'sum_ a e. %s %s' % (SQ, TERM('a'))
    fss = st([sub, ifc, zero, fin1], 'fsumss', '%s = %s' % (S1, S0))
    sA = st([st([fss], 'eqcomd', '%s = %s' % (S0, S1)), st([ssq([amu], 'iftrued', '%s = %s' % (IFT('a'), TERM('a')))], 'sumeq2dv', '%s = %s' % (S1, S2))], 'eqtrd', '%s = %s' % (S0, S2))
    # step B: SQ C_ SDR and the sum grows
    AS2 = '( ph /\\ a e. %s )' % SQ
    ssb = w.s([w.s([ain], 'ex', '( ph -> ( a e. %s -> a e. %s ) )' % (SQ, SDR))], 'ssrdv', '( ph -> %s C_ %s )' % (SQ, SDR))
    ADR = '( ph /\\ d e. %s )' % SDR; sdr = mkst(w, ADR)
    dels = sdr([], 'simpr', 'd e. %s' % SDR)
    wred, wged, wccd, APd = wfacts(ADR, dels, 'd')
    dnn = sy(w, ADR, dels, 'elrabi', 'd e. NN')
    fpd = sdr([sy(w, ADR, dnn, 'pffinq', '%s e. Fin' % PRF('d')), wred], 'fprodrecl', '%s e. RR' % TERM('d'))
    fpd0 = sdr([w.s([], 'nfv', 'F/ p %s' % ADR), sy(w, ADR, dnn, 'pffinq', '%s e. Fin' % PRF('d')), wred, wged], 'fprodge0', '0 <_ %s' % TERM('d'))
    S3 = 'sum_ d e. %s %s' % (SDR, TERM('d'))
    dvss = sy(w, PH, r['radnn'], 'dvdsssfz1', '%s C_ ( 1 ... %s )' % (DV(RAD('M')), RAD('M')))
    # SDR C_ DV(RAD): rabss-style: every element of SDR satisfies x || RAD
    AX = '( ph /\\ y e. %s )' % SDR; sx = mkst(w, AX)
    idy = w.s([], 'id', '( x = y -> x = y )')
    suby, newy = w.wcongr('( ( mmu ` x ) =/= 0 /\\ x || %s )' % RAD('M'), {'x': 'y'}, 'x = y', {'x': idy})
    ely = w.s([suby], 'elrab', '( y e. %s <-> ( y e. NN /\\ %s ) )' % (SDR, newy))
    xin = sx([sx([], 'simpr', 'y e. %s' % SDR), ely], 'sylib', '( y e. NN /\\ %s )' % newy)
    subdv = w.s([], 'breq1', '( x = y -> ( x || %s <-> y || %s ) )' % (RAD('M'), RAD('M')))
    eldv = w.s([subdv], 'elrab', '( y e. %s <-> ( y e. NN /\\ y || %s ) )' % (DV(RAD('M')), RAD('M')))
    xdv = sx([bind(w, AX, sx([xin], 'simpld', 'y e. NN'), sx([sx([xin], 'simprd', newy)], 'simprd', 'y || %s' % RAD('M')), 'y e. NN', 'y || %s' % RAD('M')), eldv], 'sylibr', 'y e. %s' % DV(RAD('M')))
    sdrss = w.s([w.s([xdv], 'ex', '( ph -> ( y e. %s -> y e. %s ) )' % (SDR, DV(RAD('M'))))], 'ssrdv', '( ph -> %s C_ %s )' % (SDR, DV(RAD('M'))))
    sdrfin = st([st([st([clo(w, 'fzfi', '( 1 ... %s ) e. Fin' % RAD('M'))], 'a1i', '( 1 ... %s ) e. Fin' % RAD('M')), dvss], 'ssfid', '%s e. Fin' % DV(RAD('M'))), sdrss], 'ssfid', '%s e. Fin' % SDR)
    S2d = 'sum_ d e. %s %s' % (SQ, TERM('d'))
    lessd = st([sdrfin, fpd, fpd0, ssb], 'fsumless', '%s <_ %s' % (S2d, S3))
    ida = w.s([], 'id', '( a = d -> a = d )'); cba, _ = w.congr(TERM('a'), {'a': 'd'}, 'a = d', {'a': ida})
    cbs2 = st([w.s([cba], 'cbvsumv', '%s = %s' % (S2, S2d))], 'a1i', '%s = %s' % (S2, S2d))
    less = st([cbs2, lessd], 'eqbrtrd', '%s <_ %s' % (S2, S3))
    # step C: sqfdvdsum at RAD(M) with G = ( t e. Prime |-> if ( t <_ M , ( W ` t ) , 0 ) )
    GB = 'if ( t <_ M , ( W ` t ) , 0 )'; G = '( t e. Prime |-> %s )' % GB
    AT = '( ph /\\ t e. Prime )'; stt = mkst(w, AT)
    AT1 = '( %s /\\ t <_ M )' % AT; st1 = mkst(w, AT1)
    tuz = sy(w, AT1, lift(w, stt([], 'simpr', 't e. Prime'), AT1), 'prmuz2', 't e. ( ZZ>= ` 2 )')
    muz = st1([lift(w, h1, AT1)], 'nnzd', 'M e. ZZ')
    tz = sy(w, AT1, tuz, 'eluzelz', 't e. ZZ')
    muz2 = st1([st1([], 'simpr', 't <_ M'), sy2(w, AT1, tz, muz, 'eluz', '( M e. ( ZZ>= ` t ) <-> t <_ M )')], 'mpbird', 'M e. ( ZZ>= ` t )')
    t2m = st1([bind(w, AT1, tuz, muz2, 't e. ( ZZ>= ` 2 )', 'M e. ( ZZ>= ` t )'), st1([clo(w, 'elfzuzb', '( t e. ( 2 ... M ) <-> ( t e. ( ZZ>= ` 2 ) /\\ M e. ( ZZ>= ` t ) ) )')], 'a1i', '( t e. ( 2 ... M ) <-> ( t e. ( ZZ>= ` 2 ) /\\ M e. ( ZZ>= ` t ) ) )')], 'mpbird', 't e. ( 2 ... M )')
    h2t, _ = rename(w, PH, '( 2 ... M )', 'n', 't', h2, '( W ` n ) e. RR')
    wtc = st1([hyp2(w, AT1, lift(w, w.s([], 'id', '( ph -> ph )'), AT1), t2m, h2t, '( W ` t ) e. RR')], 'recnd', '( W ` t ) e. CC')
    gbc = stt([wtc, w.s([], '0cnd', '( ( %s /\\ -. t <_ M ) -> 0 e. CC )' % AT)], 'ifclda', '%s e. CC' % GB)
    gf = st([gbc], 'fmpttd', '%s : Prime --> CC' % G)
    sd = st([r['radnn'], gf, w.inst('sqfdvdsum')], 'syl2anc', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )' % (SDR, PRF('d'), G, PRF(RAD('M')), G))
    # values of G at p e. PRF(d), d e. SDR
    spd = mkst(w, APd)
    pfd = prfacts(w, APd, spd([], 'simpr', 'p e. %s' % PRF('d')), 'd')
    ssd = w.s([bind(w, ADR, lift(w, h1, ADR), dels, 'M e. NN', 'd e. %s' % SDR), w.inst('bvsqfsumlem2')], 'syl', '( %s -> %s C_ ( 2 ... M ) )' % (ADR, PRF('d')))
    p2md = spd([lift(w, ssd, APd), spd([], 'simpr', 'p e. %s' % PRF('d'))], 'sseldd', 'p e. ( 2 ... M )')
    plem = sy(w, APd, p2md, 'elfzle2', 'p <_ M')
    vg, _ = mpv(w, APd, 't', 'Prime', GB, 'p', pfd['pp'], exs=ifvex(w, APd, GB.replace('t', 'p')))
    gv = spd([vg, spd([plem], 'iftrued', 'if ( p <_ M , ( W ` p ) , 0 ) = ( W ` p )')], 'eqtrd', '( %s ` p ) = ( W ` p )' % G)
    lhsC = st([sdr([gv], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = %s' % (PRF('d'), G, TERM('d')))], 'sumeq2dv', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = %s' % (SDR, PRF('d'), G, S3))
    # values at p e. PR(M)
    APR = '( ph /\\ p e. %s )' % PR('M'); spr = mkst(w, APR)
    pel = spr([], 'simpr', 'p e. %s' % PR('M'))
    pp = sy(w, APR, pel, 'elinel2', 'p e. Prime')
    p2m = spr([spr([clo(w, 'zdmprss', '%s C_ ( 2 ... M )' % PR('M'))], 'a1i', '%s C_ ( 2 ... M )' % PR('M')), pel], 'sseldd', 'p e. ( 2 ... M )')
    vg2, _ = mpv(w, APR, 't', 'Prime', GB, 'p', pp, exs=ifvex(w, APR, GB.replace('t', 'p')))
    gv2 = spr([vg2, spr([sy(w, APR, p2m, 'elfzle2', 'p <_ M')], 'iftrued', 'if ( p <_ M , ( W ` p ) , 0 ) = ( W ` p )')], 'eqtrd', '( %s ` p ) = ( W ` p )' % G)
    PRW = 'prod_ p e. %s ( 1 + ( W ` p ) )' % PR('M')
    rhsC = st([st([r['prf']], 'prodeq1d', 'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s ( 1 + ( %s ` p ) )' % (PRF(RAD('M')), G, PR('M'), G)),
               st([spr([gv2], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + ( W ` p ) )' % G)], 'prodeq2dv', 'prod_ p e. %s ( 1 + ( %s ` p ) ) = %s' % (PR('M'), G, PRW))], 'eqtrd',
              'prod_ p e. %s ( 1 + ( %s ` p ) ) = %s' % (PRF(RAD('M')), G, PRW))
    sC = st([st([lhsC], 'eqcomd', '%s = sum_ d e. %s prod_ p e. %s ( %s ` p )' % (S3, SDR, PRF('d'), G)), st([sd, rhsC], 'eqtrd', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = %s' % (SDR, PRF('d'), G, PRW))], 'eqtrd', '%s = %s' % (S3, PRW))
    # step D: bvprodle1 from PR(M) to ( 2 ... M ), then n
    A2M = '( ph /\\ p e. ( 2 ... M ) )'; s2m = mkst(w, A2M)
    h2p, _ = rename(w, PH, '( 2 ... M )', 'n', 'p', h2, '( W ` n ) e. RR'); h3p, _ = rename(w, PH, '( 2 ... M )', 'n', 'p', h3, '0 <_ ( W ` n )')
    c1r = s2m([s2m([], '1red', '1 e. RR'), h2p], 'readdcld', '( 1 + ( W ` p ) ) e. RR')
    c11 = linarith(w, A2M, [h3p], '1 <_ ( 1 + ( W ` p ) )', leaves={'( W ` p )': h2p})
    P2M = 'prod_ p e. ( 2 ... M ) ( 1 + ( W ` p ) )'
    le = w.s([st([], 'fzfid', '( 2 ... M ) e. Fin'), st([clo(w, 'zdmprss', '%s C_ ( 2 ... M )' % PR('M'))], 'a1i', '%s C_ ( 2 ... M )' % PR('M')), c1r, c11], 'bvprodle1', '( ph -> %s <_ %s )' % (PRW, P2M))
    idpn = w.s([], 'id', '( p = n -> p = n )'); cbs, _ = w.congr('( 1 + ( W ` p ) )', {'p': 'n'}, 'p = n', {'p': idpn})
    cbv = w.s([cbs], 'cbvprodv', '%s = prod_ n e. ( 2 ... M ) ( 1 + ( W ` n ) )' % P2M)
    s2r = st([sdrfin, fpd], 'fsumrecl', '%s e. RR' % S3)
    s1r = st([st([st([clo(w, 'fzfi', '%s e. Fin' % R1)], 'a1i', '%s e. Fin' % R1), sub], 'ssfid', '%s e. Fin' % SQ), ssq([sy(w, ASQ, ann, 'pffinq', '%s e. Fin' % PRF('a')), wre], 'fprodrecl', '%s e. RR' % TERM('a'))], 'fsumrecl', '%s e. RR' % S2)
    prwr = st([sC, s2r], 'eqeltrrd', '%s e. RR' % PRW)
    p2mr = st([st([], 'fzfid', '( 2 ... M ) e. Fin'), c1r], 'fprodrecl', '%s e. RR' % P2M)
    t1 = st([s1r, s2r, prwr, less, st([s2r, sC], 'eqled', '%s <_ %s' % (S3, PRW))], 'letrd', '%s <_ %s' % (S2, PRW))
    t2 = st([s1r, prwr, p2mr, t1, le], 'letrd', '%s <_ %s' % (S2, P2M))
    t3 = st([sA, t2], 'eqbrtrd', '%s <_ %s' % (S0, P2M))
    w.qed([t3, st([cbv], 'a1i', '%s = prod_ n e. ( 2 ... M ) ( 1 + ( W ` n ) )' % P2M)], 'breqtrd', STATEMENTS['bvsqfsum'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvfprodcxp', 'bvprodle1', 'bvphisg0', 'bvsqdv', 'bvphisgle', 'bvphisgsum', 'bvsqfsumlem1', 'bvsqfsumlem2', 'bvsqfsum']:
        runh(globals()[f]()) if f in ('bvfprodcxp', 'bvprodle1', 'bvsqfsum') else globals()[f]().run()
