"""Sortie CM: the prime sum (cmlsq) and the sieve at fixed u (cmsvu).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_e.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *
from lin import linarith, nlinarith, lineq

only = sys.argv[1:]


def gen_lsq():
    from mvlib import ringeqp
    w = W('cmlsq', 'The prime sum ` sum_ p ( log p ) ^ 2 / p <_ ( 15 / 4 ) e ^ 2 ( log Z ) ^ 2 ` over primes ` p <_ Z ` , ` exp 20 <_ Z ` , from the diagonal bound at ` k = 1 ` , ` U = 1 / log Z ` ( ~ kd2dgp ; Lean ` sum_log_sq_div_le ` , constant ` 3 e ^ 2 ` there, the factor ` 5 / 4 ` from ~ vmsharp ).')
    A0, C0 = split_imp(S['cmlsq'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    zr = F['Z e. RR']; ez = F['( exp ` ; 2 0 ) <_ Z']; af = F['A e. Fin']; apr = F['A C_ Prime']; az = F['A C_ ( 0 [,] Z )']
    c0 = Closure(w, A0, {'Z': ('RR', zr)})
    e20 = c0.mem('( exp ` ; 2 0 )', 'RR+')
    zp = d('elrpd', [zr, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), d('rpred', [e20], '( exp ` ; 2 0 ) e. RR'), zr, d('rpgt0d', [e20], '0 < ( exp ` ; 2 0 )'), ez], '0 < Z')], 'Z e. RR+')
    LZ = '( log ` Z )'
    l20 = d('eqbrtrrd', [d('relogefd' if False else 'syl', [c0.mem('; 2 0', 'RR'), w.inst('relogef')], '( log ` ( exp ` ; 2 0 ) ) = ; 2 0'),
                         d('mpbid', [ez, d('syl2anc', [e20, zp, w.inst('logleb')], '( ( exp ` ; 2 0 ) <_ Z <-> ( log ` ( exp ` ; 2 0 ) ) <_ %s )' % LZ)], '( log ` ( exp ` ; 2 0 ) ) <_ %s' % LZ)],
                '; 2 0 <_ %s' % LZ)
    lr = d('relogcld', [zp], '%s e. RR' % LZ)
    c0.have(LZ, 'RR', lr)
    lp = linarith(w, A0, [l20], '0 < %s' % LZ, closure=c0)
    c0.have(LZ, 'gt0', lp)
    U = '( 1 / %s )' % LZ
    up = c0.mem(U, 'RR+')
    u20 = d('mpbid', [l20, d('syl2anc', [d('jca', [c0.mem('; 2 0', 'RR'), c0.gt0('; 2 0')], '( ; 2 0 e. RR /\\ 0 < ; 2 0 )'), d('jca', [lr, lp], '( %s e. RR /\\ 0 < %s )' % (LZ, LZ)), w.inst('lerec')],
                                     '( ; 2 0 <_ %s <-> %s <_ ( 1 / ; 2 0 ) )' % (LZ, U))], '%s <_ ( 1 / ; 2 0 )' % U)
    ann = d('sstrd', [apr, a1(w, A0, 'prmssnn', 'Prime C_ NN')], 'A C_ NN')
    TK = lambda k: '( ( ( Lam ` %s ) x. ( ( log ` %s ) ^ 1 ) ) x. ( %s ^c -u ( 1 + %s ) ) )' % (k, k, k, U)
    NUM = '( ( ( ! ` 1 ) x. ( exp ` 1 ) ) x. ( ( 5 / 4 ) x. ( 1 + 2 ) ) )'
    B = '( %s / ( %s ^ ( 1 + 1 ) ) )' % (NUM, U)
    dgp = d('syl2anc', [d('jca', [d('jca', [up, u20], '( %s e. RR+ /\\ %s <_ ( 1 / ; 2 0 ) )' % (U, U)), a1(w, A0, '1nn0', '1 e. NN0')], '( ( %s e. RR+ /\\ %s <_ ( 1 / ; 2 0 ) ) /\\ 1 e. NN0 )' % (U, U)),
                        d('jca', [af, ann], '( A e. Fin /\\ A C_ NN )'), w.inst('kd2dgp')], 'sum_ k e. A %s <_ %s' % (TK('k'), B))
    eqk = 'k = p'
    idk = w.s([], 'id', '( %s -> %s )' % (eqk, eqk))
    stk, tp_ = w.congr(TK('k'), {'k': 'p'}, eqk, {'k': idk})
    cb = w.s([stk], 'cbvsumv', 'sum_ k e. A %s = sum_ p e. A %s' % (TK('k'), TK('p')))
    dgp2 = d('eqbrtrrd', [a1(w, A0, 'cbvsumv', 'sum_ k e. A %s = sum_ p e. A %s' % (TK('k'), TK('p')), [stk]), dgp], 'sum_ p e. A %s <_ %s' % (TK('p'), B))
    # termwise
    Cp = '( %s /\\ p e. A )' % A0
    cp = mk(w, Cp)
    L = lambda s_: lift(w, s_, Cp)
    pin = w.s([], 'simpr', '( %s -> p e. A )' % Cp)
    pprm = cp('sseldd', [L(apr), pin], 'p e. Prime')
    pnn = cp('syl', [pprm, w.inst('prmnn')], 'p e. NN')
    prp = cp('nnrpd', [pnn], 'p e. RR+'); pr = cp('rpred', [prp], 'p e. RR'); pc = cp('rpcnd', [prp], 'p e. CC'); pne = cp('rpne0d', [prp], 'p =/= 0')
    pic = cp('sseldd', [L(az), pin], 'p e. ( 0 [,] Z )')
    pz = cp('simp3d', [cp('mpbid', [pic, cp('syl2anc', [a1(w, Cp, '0re', '0 e. RR'), L(zr), w.inst('elicc2')], '( p e. ( 0 [,] Z ) <-> ( p e. RR /\\ 0 <_ p /\\ p <_ Z ) )')],
                                    '( p e. RR /\\ 0 <_ p /\\ p <_ Z )')], 'p <_ Z')
    LP = '( log ` p )'
    lpr = cp('relogcld', [prp], '%s e. RR' % LP); lpc = cp('recnd', [lpr], '%s e. CC' % LP)
    lam = cp('syl', [pprm, w.inst('vmaprm')], '( Lam ` p ) = %s' % LP)
    e1 = cp('exp1d', [lpc], '( %s ^ 1 ) = %s' % (LP, LP))
    ur = L(d('rpred', [up], '%s e. RR' % U)); uc = cp('recnd', [ur], '%s e. CC' % U)
    MU = '-u ( 1 + %s )' % U
    muc = cp('negcld', [cp('addcld', [a1(w, Cp, 'ax-1cn', '1 e. CC'), uc], '( 1 + %s ) e. CC' % U)], '%s e. CC' % MU)
    CPM = '( p ^c %s )' % MU; PU = '( p ^c %s )' % U
    ca = cp('cxpaddd', [pc, pne, muc, uc], '( p ^c ( %s + %s ) ) = ( %s x. %s )' % (MU, U, CPM, PU)) if False else None
    ca = cp('syl3anc', [cp('jca', [pc, pne], '( p e. CC /\\ p =/= 0 )'), muc, uc, w.inst('cxpadd')], '( p ^c ( %s + %s ) ) = ( %s x. %s )' % (MU, U, CPM, PU))
    cu = Closure(w, Cp, {U: ('RR', ur)})
    sm = lineq(w, Cp, '( %s + %s )' % (MU, U), '-u 1', closure=cu)
    cn1 = cp('eqtrd', [cp('syl3anc', [pc, pne, a1(w, Cp, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '( p ^c -u 1 ) = ( 1 / ( p ^c 1 ) )'),
                       cp('oveq2d', [cp('cxp1d', [pc], '( p ^c 1 ) = p')], '( 1 / ( p ^c 1 ) ) = ( 1 / p )')], '( p ^c -u 1 ) = ( 1 / p )')
    prod = chain(w, Cp, ['( %s x. %s )' % (CPM, PU), '( p ^c ( %s + %s ) )' % (MU, U), '( p ^c -u 1 )', '( 1 / p )'],
                 [('r', ca), cp('oveq2d', [sm], '( p ^c ( %s + %s ) ) = ( p ^c -u 1 )' % (MU, U)), cn1])
    Q = '( ( %s ^ 2 ) / p )' % LP
    T = TK('p')
    cpmc = cp('cxpcld', [pc, muc], '%s e. CC' % CPM); puc = cp('cxpcld', [pc, uc], '%s e. CC' % PU)
    lamc = cp('mulcld', [cp('eqeltrd', [lam, lpc], '( Lam ` p ) e. CC'), cp('eqeltrd', [e1, lpc], '( %s ^ 1 ) e. CC' % LP)], '( ( Lam ` p ) x. ( %s ^ 1 ) ) e. CC' % LP)
    LL = '( ( Lam ` p ) x. ( %s ^ 1 ) )' % LP
    tq = chain(w, Cp, ['( %s x. %s )' % (T, PU), '( %s x. ( %s x. %s ) )' % (LL, CPM, PU), '( ( %s x. %s ) x. ( 1 / p ) )' % (LP, LP), '( ( %s ^ 2 ) x. ( 1 / p ) )' % LP, Q],
               [cp('mulassd', [lamc, cpmc, puc], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (T, PU, LL, CPM, PU)),
                cp('oveq12d', [cp('oveq12d', [lam, e1], '%s = ( %s x. %s )' % (LL, LP, LP)), prod], '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( 1 / p ) )' % (LL, CPM, PU, LP, LP)),
                cp('oveq1d', [cp('eqcomd', [cp('sqvald', [lpc], '( %s ^ 2 ) = ( %s x. %s )' % (LP, LP, LP))], '( %s x. %s ) = ( %s ^ 2 )' % (LP, LP, LP))], '( ( %s x. %s ) x. ( 1 / p ) ) = ( ( %s ^ 2 ) x. ( 1 / p ) )' % (LP, LP, LP)),
                cp('eqcomd', [cp('divrecd', [cp('sqcld', [lpc], '( %s ^ 2 ) e. CC' % LP), pc, pne], '%s = ( ( %s ^ 2 ) x. ( 1 / p ) )' % (Q, LP))], '( ( %s ^ 2 ) x. ( 1 / p ) ) = %s' % (LP, Q))])
    # p ^ U <_ Z ^ U = e
    zc = L(d('rpcnd', [zp], 'Z e. CC')); zne = L(d('rpne0d', [zp], 'Z =/= 0'))
    ZU = '( Z ^c %s )' % U
    zu = chain(w, Cp, [ZU, '( exp ` ( %s x. %s ) )' % (U, LZ), '( exp ` 1 )'],
               [cp('syl3anc', [zc, zne, uc, w.inst('cxpef')], '%s = ( exp ` ( %s x. %s ) )' % (ZU, U, LZ)),
                cp('fveq2d', [cp('syl2anc', [L(d('recnd', [lr], '%s e. CC' % LZ)), L(d('gt0ne0d', [lp], '%s =/= 0' % LZ)), w.inst('recid2')], '( %s x. %s ) = 1' % (U, LZ))], '( exp ` ( %s x. %s ) ) = ( exp ` 1 )' % (U, LZ))])
    pzu = cp('syl3anc', [cp('3jca', [pr, L(zr), ur], '( p e. RR /\\ Z e. RR /\\ %s e. RR )' % U), cp('jca', [cp('rpge0d', [prp], '0 <_ p'), L(d('rpge0d', [up], '0 <_ %s' % U))], '( 0 <_ p /\\ 0 <_ %s )' % U), pz, w.inst('cxple2a')],
             '%s <_ %s' % (PU, ZU))
    pue = cp('breqtrd', [pzu, zu], '%s <_ ( exp ` 1 )' % PU)
    # T >_ 0
    cq = Closure(w, Cp, {'p': ('RR+', prp), U: ('RR', ur)})
    cq.have('( Lam ` p )', 'RR', cp('eqeltrd', [lam, lpr], '( Lam ` p ) e. RR'))
    cq.have('( Lam ` p )', 'ge0', cp('syl', [pnn, w.inst('vmage0')], '0 <_ ( Lam ` p )'))
    cq.have(LP, 'ge0', cp('syl', [pnn, w.inst('log1le' if False else 'nnge1d' if False else 'id')], 'x') if False else cp('syl2anc', [pr, cp('nnge1d', [pnn], '1 <_ p'), w.inst('logge0')], '0 <_ %s' % LP))
    cq.have(CPM, 'RR+', cp('rpcxpcld', [prp, cq.mem(MU, 'RR')], '%s e. RR+' % CPM))
    cq.have(PU, 'RR+', cp('rpcxpcld', [prp, ur], '%s e. RR+' % PU))
    t0 = cq.ge0(T); tr_ = cq.mem(T, 'RR')
    for at_ in (T, PU, Q, '( exp ` 1 )'):
        cq.atom(at_)
    cq.have(Q, 'RR', cp('redivcld', [cp('resqcld', [lpr], '( %s ^ 2 ) e. RR' % LP), pr, pne], '%s e. RR' % Q))
    cq.have('( exp ` 1 )', 'RR', ere(w, Cp))
    term = nlinarith(w, Cp, [t0, pue, tq], '%s <_ ( ( exp ` 1 ) x. %s )' % (Q, T), closure=cq)
    E_ = '( exp ` 1 )'
    s1 = d('fsumle', [af, cq.mem(Q, 'RR'), cp('remulcld', [ere(w, Cp), tr_], '( %s x. %s ) e. RR' % (E_, T)), term],
           'sum_ p e. A %s <_ sum_ p e. A ( %s x. %s )' % (Q, E_, T))
    s2 = d('fsummulc2', [af, d('recnd', [ere(w, A0)], '%s e. CC' % E_), cp('recnd', [tr_], '%s e. CC' % T)], '( %s x. sum_ p e. A %s ) = sum_ p e. A ( %s x. %s )' % (E_, T, E_, T))
    ST = 'sum_ p e. A %s' % T
    str_ = d('fsumrecl', [af, tr_], '%s e. RR' % ST)
    # B = NUM x. LZ ^ 2
    uc0 = d('recnd', [d('rpred', [up], '%s e. RR' % U)], '%s e. CC' % U)
    lzc = d('recnd', [lr], '%s e. CC' % LZ); lzne = d('gt0ne0d', [lp], '%s =/= 0' % LZ)
    u2 = chain(w, A0, ['( %s ^ ( 1 + 1 ) )' % U, '( %s ^ 2 )' % U, '( ( 1 ^ 2 ) / ( %s ^ 2 ) )' % LZ, '( 1 / ( %s ^ 2 ) )' % LZ],
               [a1(w, A0, 'oveq2i', '( %s ^ ( 1 + 1 ) ) = ( %s ^ 2 )' % (U, U), [w.s([], '1p1e2', '( 1 + 1 ) = 2')]),
                d('sqdivd', [a1(w, A0, 'ax-1cn', '1 e. CC'), lzc, lzne], '( %s ^ 2 ) = ( ( 1 ^ 2 ) / ( %s ^ 2 ) )' % (U, LZ)),
                d('oveq1d', [a1(w, A0, 'sq1', '( 1 ^ 2 ) = 1')], '( ( 1 ^ 2 ) / ( %s ^ 2 ) ) = ( 1 / ( %s ^ 2 ) )' % (LZ, LZ))])
    numc = c0.mem(NUM, 'CC') if False else None
    fac = a1(w, A0, 'fac1', '( ! ` 1 ) = 1')
    NUM2 = '( ( 1 x. ( exp ` 1 ) ) x. ( ( 5 / 4 ) x. 3 ) )'
    nq = d('oveq12d', [d('oveq1d', [fac], '( ( ! ` 1 ) x. ( exp ` 1 ) ) = ( 1 x. ( exp ` 1 ) )'), d('oveq2d', [a1(w, A0, '1p2e3', '( 1 + 2 ) = 3')], '( ( 5 / 4 ) x. ( 1 + 2 ) ) = ( ( 5 / 4 ) x. 3 )')],
           '%s = %s' % (NUM, NUM2))
    c2 = Closure(w, A0, {'( exp ` 1 )': ('RR', ere(w, A0)), LZ: ('RR', lr)})
    n2c = c2.mem(NUM2, 'CC')
    l2c = d('sqcld', [lzc], '( %s ^ 2 ) e. CC' % LZ); l2ne = d('sqne0d' if False else 'expne0d', [lzc, lzne, a1(w, A0, '2z', '2 e. ZZ')], '( %s ^ 2 ) =/= 0' % LZ)
    bq = chain(w, A0, [B, '( %s / ( 1 / ( %s ^ 2 ) ) )' % (NUM2, LZ), '( ( %s x. ( %s ^ 2 ) ) / 1 )' % (NUM2, LZ), '( %s x. ( %s ^ 2 ) )' % (NUM2, LZ)],
               [d('oveq12d', [nq, u2], '%s = ( %s / ( 1 / ( %s ^ 2 ) ) )' % (B, NUM2, LZ)),
                d('divdiv2d', [n2c, a1(w, A0, 'ax-1cn', '1 e. CC'), l2c, l2ne], '( %s / ( 1 / ( %s ^ 2 ) ) ) = ( ( %s x. ( %s ^ 2 ) ) / 1 )' % (NUM2, LZ, NUM2, LZ)),
                d('div1d', [d('mulcld', [n2c, l2c], '( %s x. ( %s ^ 2 ) ) e. CC' % (NUM2, LZ))], '( ( %s x. ( %s ^ 2 ) ) / 1 ) = ( %s x. ( %s ^ 2 ) )' % (NUM2, LZ, NUM2, LZ))])
    RHS = '( ( ( ; 1 5 / 4 ) x. %s ) x. ( %s ^ 2 ) )' % (EE2, LZ)
    rg = ringeqp(w, A0, '( %s x. ( %s x. ( %s ^ 2 ) ) )' % (E_, NUM2, LZ), RHS, c2)
    br = d('eqbrtrd', [bq, dgp2] if False else [d('eqcomd', [bq], '( %s x. ( %s ^ 2 ) ) = %s' % (NUM2, LZ, B)), dgp2], 'x') if False else None
    stB = d('breqtrd', [dgp2, bq], '%s <_ ( %s x. ( %s ^ 2 ) )' % (ST, NUM2, LZ))
    m = d('lemul2ad', [str_, c2.mem('( %s x. ( %s ^ 2 ) )' % (NUM2, LZ), 'RR'), ere(w, A0), d('ltled', [a1(w, A0, '0re', '0 e. RR'), ere(w, A0), epos(w, A0)], '0 <_ %s' % E_), stB],
          '( %s x. %s ) <_ ( %s x. ( %s x. ( %s ^ 2 ) ) )' % (E_, ST, E_, NUM2, LZ))
    SQS = 'sum_ p e. A %s' % Q
    f1 = d('breqtrrd', [s1, s2], '%s <_ ( %s x. %s )' % (SQS, E_, ST))
    f2 = d('letrd', [d('fsumrecl', [af, cq.mem(Q, 'RR')], '%s e. RR' % SQS), d('remulcld', [ere(w, A0), str_], '( %s x. %s ) e. RR' % (E_, ST)),
                     c2.mem('( %s x. ( %s x. ( %s ^ 2 ) ) )' % (E_, NUM2, LZ), 'RR'), f1, m], '%s <_ ( %s x. ( %s x. ( %s ^ 2 ) ) )' % (SQS, E_, NUM2, LZ))
    fin = d('breqtrd', [f2, rg], '%s <_ %s' % (SQS, RHS))
    w.qed([fin], 'idi', S['cmlsq'])
    return run(w, only)


def gen_sid():
    from mvlib import ringeq
    from congr import mptval
    import cm_c
    w = W('cmsid', 'The large-sieve polynomial with coefficients ` log n / n ` is the prime window sum: ` sum_ n ( log n / n ) x ( n ) n ^ ( -u T i ) = PWS ( T , Y , U ) ` ( ~ cxpadd ; Lean ` sieve_at_u ` ` hid ` ).')
    A0, C0 = split_imp(S['cmsid'])
    d = mk(w, A0)
    nx = d('simp1', [], NX); tr = d('simp3', [], 'T e. RR')
    PS = PSET('Y', 'U')
    Cn = '( %s /\\ n e. %s )' % (A0, PS)
    cn = mk(w, Cn)
    nn = cm_c.psmem(w, Cn, 'n', 'Y', 'U')[0]
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, PS))
    nc = cn('nncnd', [nn], 'n e. CC'); nne = cn('nnne0d', [nn], 'n =/= 0')
    LN = '( log ` n )'
    lnc = cn('recnd', [cn('relogcld', [cn('nnrpd', [nn], 'n e. RR+')], '%s e. RR' % LN)], '%s e. CC' % LN)
    fv, val = mptval(w, Cn, 'b', PS, '( ( log ` b ) / b )', 'n', nin, exs=cn('ovexd', [], '( %s / n ) e. _V' % LN), gen=w.g)
    assert val == '( %s / n )' % LN
    AM = AMAP('Y', 'U')
    CH = CHV('n')
    CPT = '( n ^c ( -u T x. _i ) )'
    L0 = '( ( ( %s ` n ) x. %s ) x. %s )' % (AM, CH, CPT)
    L1 = '( ( ( %s / n ) x. %s ) x. %s )' % (LN, CH, CPT)
    L2 = '( ( ( %s x. ( 1 / n ) ) x. %s ) x. %s )' % (LN, CH, CPT)
    R2 = '( ( %s x. %s ) x. ( ( 1 / n ) x. %s ) )' % (CH, LN, CPT)
    E1 = '( -u 1 - ( T x. _i ) )'; E2 = '( -u 1 + ( -u T x. _i ) )'
    R1 = '( ( %s x. %s ) x. ( n ^c %s ) )' % (CH, LN, E1)
    tc = lift(w, d('recnd', [tr], 'T e. CC'), Cn)
    ic = a1(w, Cn, 'ax-icn', '_i e. CC')
    cl1 = Closure(w, Cn, {'T': ('CC', tc), '_i': ('CC', ic)})
    ee = ringeq(w, Cn, E1, E2, cl1)
    m1c = cn('negcld', [a1(w, Cn, 'ax-1cn', '1 e. CC')], '-u 1 e. CC')
    mtc = cn('mulcld', [cn('negcld', [tc], '-u T e. CC'), ic], '( -u T x. _i ) e. CC')
    cadd = cn('syl3anc', [cn('jca', [nc, nne], '( n e. CC /\\ n =/= 0 )'), m1c, mtc, w.inst('cxpadd')], '( n ^c %s ) = ( ( n ^c -u 1 ) x. %s )' % (E2, CPT))
    cn1 = cn('eqtrd', [cn('syl3anc', [nc, nne, a1(w, Cn, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], '( n ^c -u 1 ) = ( 1 / ( n ^c 1 ) )'),
                       cn('oveq2d', [cn('cxp1d', [nc], '( n ^c 1 ) = n')], '( 1 / ( n ^c 1 ) ) = ( 1 / n )')], '( n ^c -u 1 ) = ( 1 / n )')
    pw = chain(w, Cn, ['( n ^c %s )' % E1, '( n ^c %s )' % E2, '( ( n ^c -u 1 ) x. %s )' % CPT, '( ( 1 / n ) x. %s )' % CPT],
               [cn('oveq2d', [ee], '( n ^c %s ) = ( n ^c %s )' % (E1, E2)), cadd, cn('oveq1d', [cn1], '( ( n ^c -u 1 ) x. %s ) = ( ( 1 / n ) x. %s )' % (CPT, CPT))])
    chc = cn('simpld', [cn('syl2anc', [lift(w, nx, Cn), cn('nnzd', [nn], 'n e. ZZ'), w.inst('cen2chv')], '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CH, CH))], '%s e. CC' % CH)
    cptc = cn('cxpcld', [nc, mtc if False else cn('mulcld', [cn('negcld', [tc], '-u T e. CC'), ic], '( -u T x. _i ) e. CC')], '%s e. CC' % CPT)
    rnc = cn('reccld', [nc, nne], '( 1 / n ) e. CC')
    cl2 = Closure(w, Cn, {LN: ('CC', lnc), '( 1 / n )': ('CC', rnc), CH: ('CC', chc), CPT: ('CC', cptc)})
    for at_ in (LN, '( 1 / n )', CH, CPT):
        cl2.atom(at_)
    rg = ringeq(w, Cn, L2, R2, cl2)
    tq = chain(w, Cn, [L0, L1, L2, R2, R1],
               [cn('oveq1d', [cn('oveq1d', [fv], '( ( %s ` n ) x. %s ) = ( ( %s / n ) x. %s )' % (AM, CH, LN, CH))], '%s = %s' % (L0, L1)),
                cn('oveq1d', [cn('oveq1d', [cn('divrecd', [lnc, nc, nne], '( %s / n ) = ( %s x. ( 1 / n ) )' % (LN, LN))], '( ( %s / n ) x. %s ) = ( ( %s x. ( 1 / n ) ) x. %s )' % (LN, CH, LN, CH))], '%s = %s' % (L1, L2)),
                rg, ('r', cn('oveq2d', [pw], '%s = %s' % (R1, R2)))])
    s1 = d('sumeq2dv', [tq], '%s = sum_ n e. %s %s' % (SIEVE_T('T', 'Y', 'U'), PS, R1))
    eqn = 'n = p'
    idn = w.s([], 'id', '( %s -> %s )' % (eqn, eqn))
    stn, rp = w.congr(R1, {'n': 'p'}, eqn, {'n': idn})
    assert rp == CP('p', 'T'), rp
    s2 = a1(w, A0, 'cbvsumv', 'sum_ n e. %s %s = %s' % (PS, R1, PWS('T', 'Y', 'U')), [stn])
    fin = d('eqtrd', [s1, s2], C0)
    w.qed([fin], 'idi', S['cmsid'])
    return run(w, only)


def gen_srh():
    from mvlib import ringeq
    from congr import mptval
    import cm_c
    w = W('cmsrh', 'The large-sieve right side at coefficients ` log n / n ` on primes ` n > Y >_ W ^ 5 ` : ` 100 sum ( n + ( W ^ 2 ) ^ 2 ( V + 1 ) ) abs ( log n / n ) ^ 2 <_ 750 e ^ 2 ( log Z ) ^ 2 ` ( ~ cmlsq ; Lean ` sieve_at_u ` ` hrhs ` , constant ` 600 e ^ 2 ` there).')
    A0, C0 = split_imp(S['cmsrh'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    vr = g('V e. RR'); wr = g('W e. RR'); v1 = g('1 <_ V'); w2 = g('2 <_ W'); v3 = g('( V + 3 ) <_ W'); yr = g('Y e. RR'); w5 = g('( W ^ 5 ) <_ Y')
    zr = g('Z e. RR'); ez = g('( exp ` ; 2 0 ) <_ Z'); ur = g('U e. RR'); uz = g('U <_ Z')
    c0 = Closure(w, A0, {'V': ('RR', vr), 'W': ('RR', wr), 'Y': ('RR', yr), 'Z': ('RR', zr), 'U': ('RR', ur)})
    wc = d('recnd', [wr], 'W e. CC')
    P4 = '( ( W ^ 2 ) ^ 2 )'; P5 = '( W ^ 5 )'
    p4 = chain(w, A0, ['( W ^ 4 )', '( W ^ ( 2 x. 2 ) )', P4],
               [d('oveq2d', [a1(w, A0, 'eqcomi', '4 = ( 2 x. 2 )', [w.s([], '2t2e4', '( 2 x. 2 ) = 4')])], '( W ^ 4 ) = ( W ^ ( 2 x. 2 ) )'),
                d('expmuld', [wc, a1(w, A0, '2nn0', '2 e. NN0'), a1(w, A0, '2nn0', '2 e. NN0')], '( W ^ ( 2 x. 2 ) ) = %s' % P4)])
    p5 = chain(w, A0, [P5, '( W ^ ( 4 + 1 ) )', '( ( W ^ 4 ) x. W )', '( %s x. W )' % P4],
               [d('oveq2d', [a1(w, A0, 'eqcomi', '5 = ( 4 + 1 )', [w.s([], '4p1e5', '( 4 + 1 ) = 5')])], '%s = ( W ^ ( 4 + 1 ) )' % P5),
                d('expp1d', [wc, a1(w, A0, '4nn0', '4 e. NN0')], '( W ^ ( 4 + 1 ) ) = ( ( W ^ 4 ) x. W )'), d('oveq1d', [p4], '( ( W ^ 4 ) x. W ) = ( %s x. W )' % P4)])
    p4r = c0.mem(P4, 'RR'); p40 = d('sqge0d', [c0.mem('( W ^ 2 )', 'RR')], '0 <_ %s' % P4)
    T2 = '( %s x. ( V + 1 ) )' % P4
    t2w = d('lemul2ad', [c0.mem('( V + 1 )', 'RR'), wr, p4r, p40, linarith(w, A0, [v3], '( V + 1 ) <_ W', closure=c0)], '%s <_ ( %s x. W )' % (T2, P4))
    for at_ in (P4, P5, '( %s x. W )' % P4, T2):
        c0.atom(at_)
    c0.have(P5, 'RR', c0.mem(P5, 'RR'))
    t2y = linarith(w, A0, [t2w, p5, w5], '%s <_ Y' % T2, closure=c0)
    PS = PSET('Y', 'U')
    pf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` U ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` U ) )' % PS)], '%s e. Fin' % PS)
    Cn = '( %s /\\ n e. %s )' % (A0, PS)
    cn = mk(w, Cn)
    nn, nprm, yn, nfl = cm_c.psmem(w, Cn, 'n', 'Y', 'U')
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, PS))
    nr = cn('nnred', [nn], 'n e. RR'); nc = cn('nncnd', [nn], 'n e. CC'); nne = cn('nnne0d', [nn], 'n =/= 0')
    LN = '( log ` n )'
    lnr = cn('relogcld', [cn('nnrpd', [nn], 'n e. RR+')], '%s e. RR' % LN); lnc = cn('recnd', [lnr], '%s e. CC' % LN)
    I = '( 1 / n )'
    ir = cn('nnrecred', [nn], '%s e. RR' % I)
    AM = AMAP('Y', 'U')
    fv, val = mptval(w, Cn, 'b', PS, '( ( log ` b ) / b )', 'n', nin, exs=cn('ovexd', [], '( %s / n ) e. _V' % LN), gen=w.g)
    ab = chain(w, Cn, ['( ( abs ` ( %s ` n ) ) ^ 2 )' % AM, '( ( abs ` ( %s / n ) ) ^ 2 )' % LN, '( ( %s / n ) ^ 2 )' % LN, '( ( %s x. %s ) ^ 2 )' % (LN, I)],
               [cn('oveq1d', [cn('fveq2d', [fv], '( abs ` ( %s ` n ) ) = ( abs ` ( %s / n ) )' % (AM, LN))], '( ( abs ` ( %s ` n ) ) ^ 2 ) = ( ( abs ` ( %s / n ) ) ^ 2 )' % (AM, LN)),
                cn('syl', [cn('redivcld', [lnr, nr, nne], '( %s / n ) e. RR' % LN), w.inst('absresq')], '( ( abs ` ( %s / n ) ) ^ 2 ) = ( ( %s / n ) ^ 2 )' % (LN, LN)),
                cn('oveq1d', [cn('divrecd', [lnc, nc, nne], '( %s / n ) = ( %s x. %s )' % (LN, LN, I))], '( ( %s / n ) ^ 2 ) = ( ( %s x. %s ) ^ 2 )' % (LN, LN, I))])
    cc = Closure(w, Cn, {'n': ('RR', nr), LN: ('RR', lnr), I: ('RR', ir), 'Y': ('RR', lift(w, yr, Cn)), T2: ('RR', lift(w, c0.mem(T2, 'RR'), Cn))})
    for at_ in (LN, I, T2):
        cc.atom(at_)
    sq = cc.mem('( ( %s x. %s ) ^ 2 )' % (LN, I), 'RR')
    sq0 = cn('sqge0d', [cc.mem('( %s x. %s )' % (LN, I), 'RR')], '0 <_ ( ( %s x. %s ) ^ 2 )' % (LN, I))
    le = linarith(w, Cn, [lift(w, t2y, Cn), yn], '( n + %s ) <_ ( 2 x. n )' % T2, closure=cc)
    SQ = '( ( %s x. %s ) ^ 2 )' % (LN, I)
    m = cn('lemul1ad', [cc.mem('( n + %s )' % T2, 'RR'), cc.mem('( 2 x. n )', 'RR'), sq, sq0, le], '( ( n + %s ) x. %s ) <_ ( ( 2 x. n ) x. %s )' % (T2, SQ, SQ))
    ccc = Closure(w, Cn, {'n': ('CC', nc), LN: ('CC', lnc), I: ('CC', cn('recnd', [ir], '%s e. CC' % I))})
    for at_ in (LN, I):
        ccc.atom(at_)
    QN = '( ( %s ^ 2 ) x. %s )' % (LN, I)
    from mvlib import ringeqp
    rg = ringeqp(w, Cn, '( ( 2 x. n ) x. %s )' % SQ, '( ( 2 x. %s ) x. ( n x. %s ) )' % (QN, I), ccc)
    ni = cn('recidd', [nc, nne], '( n x. %s ) = 1' % I)
    QD = '( ( %s ^ 2 ) / n )' % LN
    qc = cn('mulcld', [cn('sqcld', [lnc], '( %s ^ 2 ) e. CC' % LN), cn('recnd', [ir], '%s e. CC' % I)], '%s e. CC' % QN)
    r2 = chain(w, Cn, ['( ( 2 x. n ) x. %s )' % SQ, '( ( 2 x. %s ) x. ( n x. %s ) )' % (QN, I), '( ( 2 x. %s ) x. 1 )' % QN, '( 2 x. %s )' % QN, '( 2 x. %s )' % QD],
               [rg, cn('oveq2d', [ni], '( ( 2 x. %s ) x. ( n x. %s ) ) = ( ( 2 x. %s ) x. 1 )' % (QN, I, QN)),
                cn('mulridd', [cn('mulcld', [a1(w, Cn, '2cn', '2 e. CC'), qc], '( 2 x. %s ) e. CC' % QN)], '( ( 2 x. %s ) x. 1 ) = ( 2 x. %s )' % (QN, QN)),
                cn('oveq2d', [cn('eqcomd', [cn('divrecd', [cn('sqcld', [lnc], '( %s ^ 2 ) e. CC' % LN), nc, nne], '%s = %s' % (QD, QN))], '%s = %s' % (QN, QD))], '( 2 x. %s ) = ( 2 x. %s )' % (QN, QD))])
    TERM = '( ( n + %s ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) )' % (T2, AM)
    tm = cn('eqbrtrd', [cn('oveq2d', [ab], '%s = ( ( n + %s ) x. %s )' % (TERM, T2, SQ)), m], '%s <_ ( ( 2 x. n ) x. %s )' % (TERM, SQ))
    tm2 = cn('breqtrd', [tm, r2], '%s <_ ( 2 x. %s )' % (TERM, QD))
    termr = cn('eqeltrrd' if False else 'remulcld', [cc.mem('( n + %s )' % T2, 'RR'), cn('resqcld', [cn('abscld', [cn('eqeltrd', [fv, cn('recnd', [cn('redivcld', [lnr, nr, nne], '( %s / n ) e. RR' % LN)], '( %s / n ) e. CC' % LN)], '( %s ` n ) e. CC' % AM)], '( abs ` ( %s ` n ) ) e. RR' % AM)], '( ( abs ` ( %s ` n ) ) ^ 2 ) e. RR' % AM)], '%s e. RR' % TERM)
    qdr = cn('redivcld', [cn('resqcld', [lnr], '( %s ^ 2 ) e. RR' % LN), nr, nne], '%s e. RR' % QD)
    s1 = d('fsumle', [pf, termr, cn('remulcld', [a1(w, Cn, '2re', '2 e. RR'), qdr], '( 2 x. %s ) e. RR' % QD), tm2], 'sum_ n e. %s %s <_ sum_ n e. %s ( 2 x. %s )' % (PS, TERM, PS, QD))
    s2 = d('fsummulc2', [pf, a1(w, A0, '2cn', '2 e. CC'), cn('recnd', [qdr], '%s e. CC' % QD)], '( 2 x. sum_ n e. %s %s ) = sum_ n e. %s ( 2 x. %s )' % (PS, QD, PS, QD))
    # cmlsq at A := PS
    Cn2 = '( %s /\\ n e. %s )' % (A0, PS)
    nfz = cn('letrd', [nr, cn('zred', [cn('flcld', [lift(w, ur, Cn)], '( |_ ` U ) e. ZZ')], '( |_ ` U ) e. RR'), lift(w, zr, Cn), nfl,
                       cn('letrd', [cn('zred', [cn('flcld', [lift(w, ur, Cn)], '( |_ ` U ) e. ZZ')], '( |_ ` U ) e. RR'), lift(w, ur, Cn), lift(w, zr, Cn), cn('syl', [lift(w, ur, Cn), w.inst('flle')], '( |_ ` U ) <_ U'), lift(w, uz, Cn)], '( |_ ` U ) <_ Z')],
             'n <_ Z')
    nic = cn('mpbird', [cn('3jca', [nr, cn('nnge0d' if False else 'ltled', [a1(w, Cn, '0re', '0 e. RR'), nr, cn('nngt0d', [nn], '0 < n')], '0 <_ n'), nfz], '( n e. RR /\\ 0 <_ n /\\ n <_ Z )'),
                        cn('syl2anc', [a1(w, Cn, '0re', '0 e. RR'), lift(w, zr, Cn), w.inst('elicc2')], '( n e. ( 0 [,] Z ) <-> ( n e. RR /\\ 0 <_ n /\\ n <_ Z ) )')], 'n e. ( 0 [,] Z )')
    ssz = d('ssrdv', [w.s([nic], 'ex', '( %s -> ( n e. %s -> n e. ( 0 [,] Z ) ) )' % (A0, PS))], '%s C_ ( 0 [,] Z )' % PS)
    ssp = d('ssrdv', [w.s([nprm], 'ex', '( %s -> ( n e. %s -> n e. Prime ) )' % (A0, PS))], '%s C_ Prime' % PS)
    LSQ = inst('cmlsq', {'A': PS})
    ls = d('syl2anc', [d('jca', [zr, ez], '( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z )'), d('3jca', [pf, ssp, ssz], '( %s e. Fin /\\ %s C_ Prime /\\ %s C_ ( 0 [,] Z ) )' % (PS, PS, PS)), w.inst('cmlsq')], LSQ[1])
    eqp = 'p = n'
    idp = w.s([], 'id', '( %s -> %s )' % (eqp, eqp))
    stp, qn_ = w.congr('( ( ( log ` p ) ^ 2 ) / p )', {'p': 'n'}, eqp, {'p': idp})
    cbq = a1(w, A0, 'cbvsumv', 'sum_ p e. %s ( ( ( log ` p ) ^ 2 ) / p ) = sum_ n e. %s %s' % (PS, PS, QD), [stp])
    RB = '( ( ( ; 1 5 / 4 ) x. %s ) x. ( ( log ` Z ) ^ 2 ) )' % EE2
    ls2 = d('eqbrtrrd', [cbq, ls], 'sum_ n e. %s %s <_ %s' % (PS, QD, RB))
    ST = 'sum_ n e. %s %s' % (PS, TERM); SQD = 'sum_ n e. %s %s' % (PS, QD); S2Q = 'sum_ n e. %s ( 2 x. %s )' % (PS, QD)
    cf = Closure(w, A0, {'Z': ('RR', zr)})
    cf.have(ST, 'RR', d('fsumrecl', [pf, termr], '%s e. RR' % ST)); cf.have(SQD, 'RR', d('fsumrecl', [pf, qdr], '%s e. RR' % SQD))
    cf.have(S2Q, 'RR', d('fsumrecl', [pf, cn('remulcld', [a1(w, Cn, '2re', '2 e. RR'), qdr], '( 2 x. %s ) e. RR' % QD)], '%s e. RR' % S2Q))
    cf.have(EE2, 'RR', d('resqcld', [ere(w, A0)], '%s e. RR' % EE2))
    cf.have('( ( log ` Z ) ^ 2 )', 'RR', d('resqcld', [d('relogcld', [d('elrpd', [zr, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), cf.mem('( exp ` ; 2 0 )', 'RR'), zr, cf.gt0('( exp ` ; 2 0 )'), ez], '0 < Z')], 'Z e. RR+')], '( log ` Z ) e. RR')], '( ( log ` Z ) ^ 2 ) e. RR'))
    for at_ in (ST, SQD, S2Q, EE2, '( ( log ` Z ) ^ 2 )'):
        cf.atom(at_)
    fin = nlinarith(w, A0, [s1, s2, ls2], C0.split(' -> ')[-1] if False else C0, closure=cf)
    w.qed([fin], 'idi', S['cmsrh'])
    return run(w, only)


def gen_svu():
    import cm_c
    w = W('cmsvu', 'THE SIEVE AT FIXED ` U ` : the window sums of all bad characters of conductor ` d e. ( 2 ... K ) ` , ` K <_ W ` , weighted by ` L = log W <_ log ( W ^ 2 / d ) ` (the log-free cancellation), satisfy ` L sum_ d sum_ x S. abs ( PWS ) ^ 2 _d t <_ 750 e ^ 2 ( log Z ) ^ 2 ` ( ~ lspresift at ` Q = W ^ 2 ` , ` T = V + 1 ` , ~ cmsid , ~ cmsrh ; Lean ` sieve_at_u ` ).')
    A0, C0 = split_imp(S['cmsvu'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    sr = g('S e. RR'); vr = g('V e. RR'); wr = g('W e. RR'); v1 = g('1 <_ V'); w2 = g('2 <_ W'); kz = g('K e. ZZ'); kw = g('K <_ W'); v3 = g('( V + 3 ) <_ W')
    yr = g('Y e. RR'); w5 = g('( W ^ 5 ) <_ Y'); zr = g('Z e. RR'); ez = g('( exp ` ; 2 0 ) <_ Z'); ur = g('U e. RR'); yu = g('Y < U'); uz = g('U <_ Z')
    c0 = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'W': ('RR', wr), 'K': ('ZZ', kz), 'Y': ('RR', yr), 'Z': ('RR', zr), 'U': ('RR', ur)})
    wp = linarith(w, A0, [w2], '0 < W', closure=c0); c0.have('W', 'gt0', wp)
    w1 = linarith(w, A0, [w2], '1 <_ W', closure=c0)
    Q = '( W ^ 2 )'; T = V1
    qr = c0.mem(Q, 'RR')
    c0.atom(Q)
    wq = d('eqbrtrrd', [d('sqvald', [d('recnd', [wr], 'W e. CC')], '%s = ( W x. W )' % Q), d('lemul1ad', [a1(w, A0, '1re', '1 e. RR'), wr, wr, d('ltled', [a1(w, A0, '0re', '0 e. RR'), wr, wp], '0 <_ W'), w1], '( 1 x. W ) <_ ( W x. W )')], 'x') if False else None
    ww = d('sqvald', [d('recnd', [wr], 'W e. CC')], '%s = ( W x. W )' % Q)
    wmw = nlinarith(w, A0, [w2], '( 2 x. W ) <_ ( W x. W )', closure=c0)
    c0.atom('( W x. W )')
    q2 = linarith(w, A0, [ww, wmw, w2], '2 <_ %s' % Q, closure=c0)
    wleq = linarith(w, A0, [ww, wmw, w2], 'W <_ %s' % Q, closure=c0)
    tr = c0.mem(T, 'RR'); t1 = linarith(w, A0, [v1], '1 <_ %s' % T, closure=c0)
    PS = PSET('Y', 'U'); AM = AMAP('Y', 'U')
    pf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` U ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` U ) )' % PS)], '%s e. Fin' % PS)
    Cb = '( %s /\\ b e. %s )' % (A0, PS)
    bn = cm_c.psmem(w, Cb, 'b', 'Y', 'U')[0]
    cb_ = mk(w, Cb)
    bl = cb_('recnd', [cb_('redivcld', [cb_('relogcld', [cb_('nnrpd', [bn], 'b e. RR+')], '( log ` b ) e. RR'), cb_('nnred', [bn], 'b e. RR'), cb_('nnne0d', [bn], 'b =/= 0')], '( ( log ` b ) / b ) e. RR')], '( ( log ` b ) / b ) e. CC')
    amf = d('fmptd', [bl, w.s([], 'eqid', '%s = %s' % (AM, AM))], '%s : %s --> CC' % (AM, PS))
    Cn = '( %s /\\ n e. %s )' % (A0, PS)
    nn_ = cm_c.psmem(w, Cn, 'n', 'Y', 'U')[0]
    psn = d('ssrdv', [w.s([nn_], 'ex', '( %s -> ( n e. %s -> n e. NN ) )' % (A0, PS))], '%s C_ NN' % PS)
    # sifting
    Ck = '( ( %s /\\ k e. %s ) /\\ p e. Prime )' % (A0, PS)
    ck = mk(w, Ck)
    _, kprm, yk, _ = cm_c.psmem(w, Ck, 'k', 'Y', 'U')
    kr = ck('nnred', [ck('prmnnd' if False else 'syl', [kprm, w.inst('prmnn')], 'k e. NN')], 'k e. RR')
    pprm = w.s([], 'simpr', '( %s -> p e. Prime )' % Ck)
    dv = ck('syl2anc', [ck('syl', [pprm, w.inst('prmuz2')], 'p e. ( ZZ>= ` 2 )'), kprm, w.inst('dvdsprm')], '( p || k <-> p = k )')
    q5 = lift(w, d('leexp2ad', [wr, w1, a1(w, A0, 'eluzi' if False else 'mpbir', '5 e. ( ZZ>= ` 2 )', [w.s([w.s([], '2z', '2 e. ZZ'), w.s([w.s([], '5nn', '5 e. NN')], 'nnzi', '5 e. ZZ'), w.s([w.s([], '2re', '2 e. RR'), w.s([], '5re', '5 e. RR'), w.s([], '2lt5', '2 < 5')], 'ltleii', '2 <_ 5')], '3pm3.2i', '( 2 e. ZZ /\\ 5 e. ZZ /\\ 2 <_ 5 )'),
                                                                                                         w.s([], 'eluz2', '( 5 e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ 5 e. ZZ /\\ 2 <_ 5 ) )')])], '%s <_ ( W ^ 5 )' % Q), Ck)
    ck_cl = Closure(w, Ck, {'k': ('RR', kr), 'Y': ('RR', lift(w, yr, Ck)), Q: ('RR', lift(w, qr, Ck)), '( W ^ 5 )': ('RR', lift(w, c0.mem('( W ^ 5 )', 'RR'), Ck))})
    for at_ in (Q, '( W ^ 5 )'):
        ck_cl.atom(at_)
    qk = linarith(w, Ck, [q5, lift(w, w5, Ck), yk], '%s < k' % Q, closure=ck_cl)
    Ckp = '( %s /\\ p || k )' % Ck
    pk = D(w, Ckp, 'mpbid', [w.s([], 'simpr', '( %s -> p || k )' % Ckp), lift(w, dv, Ckp)], 'p = k')
    qp = D(w, Ckp, 'breqtrrd', [lift(w, qk, Ckp), pk], '%s < p' % Q)
    sift = d('ralrimiva', [w.s([w.s([qp], 'ex', '( %s -> ( p || k -> %s < p ) )' % (Ck, Q))], 'ralrimiva', '( ( %s /\\ k e. %s ) -> A. p e. Prime ( p || k -> %s < p ) )' % (A0, PS, Q))],
             'A. k e. %s A. p e. Prime ( p || k -> %s < p )' % (PS, Q))
    HPSf = '( ( ( %s e. RR /\\ 2 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s ) ) /\\ ( %s e. Fin /\\ %s C_ NN /\\ %s : %s --> CC ) /\\ A. k e. %s A. p e. Prime ( p || k -> %s < p ) )' % (
        Q, Q, T, T, PS, PS, AM, PS, PS, Q)
    hps = d('3jca', [d('jca', [d('jca', [qr, q2], '( %s e. RR /\\ 2 <_ %s )' % (Q, Q)), d('jca', [tr, t1], '( %s e. RR /\\ 1 <_ %s )' % (T, T))], '( ( %s e. RR /\\ 2 <_ %s ) /\\ ( %s e. RR /\\ 1 <_ %s ) )' % (Q, Q, T, T)),
                     d('3jca', [pf, psn, amf], '( %s e. Fin /\\ %s C_ NN /\\ %s : %s --> CC )' % (PS, PS, AM, PS)), sift], HPSf)
    LSP = inst('lspresift', {'Q': Q, 'T': T, 'S': PS, 'A': AM})
    assert LSP[0] == HPSf
    lsp = d('syl', [hps, w.inst('lspresift')], LSP[1])
    LHSS, RHSS = LSP[1].split(' <_ ( ; ; 1 0 0 x. ')
    RHSS = '( ; ; 1 0 0 x. ' + RHSS
    RH = inst('cmsrh', {})
    rh = d('syl', [d('jca', [d('jca', [d('jca', [vr, wr], '( V e. RR /\\ W e. RR )'), d('3jca', [v1, w2, v3], '( 1 <_ V /\\ 2 <_ W /\\ ( V + 3 ) <_ W )')], '( ( V e. RR /\\ W e. RR ) /\\ ( 1 <_ V /\\ 2 <_ W /\\ ( V + 3 ) <_ W ) )'),
                              d('3jca', [d('jca', [yr, w5], '( Y e. RR /\\ ( W ^ 5 ) <_ Y )'), d('jca', [zr, ez], '( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z )'), d('jca', [ur, uz], '( U e. RR /\\ U <_ Z )')],
                                     '( ( Y e. RR /\\ ( W ^ 5 ) <_ Y ) /\\ ( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z ) /\\ ( U e. RR /\\ U <_ Z ) )')], RH[0]), w.inst('cmsrh')], RH[1])
    assert RH[1].startswith(RHSS + ' <_ '), (RH[1][:200], RHSS[:200])
    # the sieve left side in PWS form
    PC = lambda f: '{ y e. %s | ( %s DChrCond y ) = %s }' % (BASE(f), f, f)
    JX = lambda f, x: JJ(V1, 'Y', 'U', f, x)
    GF = lambda f: 'sum_ x e. %s %s' % (PC(f), JX(f, 'x'))
    TT = '( -u %s (,) %s )' % (V1, V1)
    SIX = lambda f, x: 'S. %s ( ( abs ` %s ) ^ 2 ) _d t' % (TT, SIEVE_T('t', 'Y', 'U', f, x))
    FR = '( 1 ... ( |_ ` %s ) )' % Q
    Cf = '( %s /\\ f e. NN )' % A0
    Cfx = '( %s /\\ x e. %s )' % (Cf, PC('f'))
    xb = D(w, Cfx, 'sseldd', [a1(w, Cfx, 'ssrab2', '%s C_ %s' % (PC('f'), BASE('f'))), w.s([], 'simpr', '( %s -> x e. %s )' % (Cfx, PC('f')))], 'x e. %s' % BASE('f'))
    fnn = proj(w, Cfx, 'f e. NN')
    nxf = D(w, Cfx, 'jca', [fnn, xb], '( f e. NN /\\ x e. %s )' % BASE('f'))
    Cft = '( %s /\\ t e. %s )' % (Cfx, TT)
    tr_ = D(w, Cft, 'syl', [w.s([], 'simpr', '( %s -> t e. %s )' % (Cft, TT)), w.inst('elioore')], 't e. RR')
    SID = inst('cmsid', {'N': 'f', 'X': 'x', 'T': 't'})
    sid = D(w, Cft, 'syl3anc', [lift(w, nxf, Cft), lift(w, d('jca', [yr, ur], '( Y e. RR /\\ U e. RR )'), Cft), tr_, w.inst('cmsid')], SID[1])
    STx = SIEVE_T('t', 'Y', 'U', 'f', 'x'); PWx = PWS('t', 'Y', 'U', 'f', 'x')
    sq_ = D(w, Cft, 'oveq1d', [D(w, Cft, 'fveq2d', [sid], '( abs ` %s ) = ( abs ` %s )' % (STx, PWx))], '( ( abs ` %s ) ^ 2 ) = ( ( abs ` %s ) ^ 2 )' % (STx, PWx))
    ix = D(w, Cfx, 'itgeq2dv', [sq_], '%s = %s' % (SIX('f', 'x'), JX('f', 'x')))
    gq = D(w, Cf, 'sumeq2dv', [ix], 'sum_ x e. %s %s = %s' % (PC('f'), SIX('f', 'x'), GF('f')))
    # JJ nonneg / real for x a character mod f
    PWT = inst('cmpwt', {'N': 'f', 'X': 'x', 'H': V1})
    pwt = D(w, Cfx, 'syl3anc', [nxf, lift(w, tr, Cfx), lift(w, d('jca', [yr, ur], '( Y e. RR /\\ U e. RR )'), Cfx), w.inst('cmpwt')], PWT[1])
    jr = D(w, Cfx, 'simp2d', [pwt], '%s e. RR' % JX('f', 'x')); j0 = D(w, Cfx, 'simp3d', [pwt], '0 <_ %s' % JX('f', 'x'))
    dfi = D(w, Cf, 'syl', [w.s([], 'simpr', '( %s -> f e. NN )' % Cf), w.s([w.s([], 'eqid', '( DChr ` f ) = ( DChr ` f )'), w.s([], 'eqid', '%s = %s' % (BASE('f'), BASE('f')))], 'dchrfi', '( f e. NN -> %s e. Fin )' % BASE('f'))],
            '%s e. Fin' % BASE('f'))
    pcf = D(w, Cf, 'ssfid', [dfi, a1(w, Cf, 'ssrab2', '%s C_ %s' % (PC('f'), BASE('f')))], '%s e. Fin' % PC('f'))
    gr = D(w, Cf, 'fsumrecl', [pcf, jr], '%s e. RR' % GF('f'))
    g0 = D(w, Cf, 'fsumge0', [pcf, jr, j0], '0 <_ %s' % GF('f'))
    # LHSS = sum_f log ( Q / f ) G ( f )
    LG = lambda f: '( log ` ( %s / %s ) )' % (Q, f)
    Cf1 = '( %s /\\ f e. %s )' % (A0, FR)
    fnn1 = D(w, Cf1, 'syl', [w.s([], 'simpr', '( %s -> f e. %s )' % (Cf1, FR)), w.inst('elfznn')], 'f e. NN')
    gq1 = rean(w, D(w, Cf, 'oveq2d', [gq], '( %s x. sum_ x e. %s %s ) = ( %s x. %s )' % (LG('f'), PC('f'), SIX('f', 'x'), LG('f'), GF('f'))), '( %s /\\ f e. NN )' % A0)
    gq2 = D(w, Cf1, 'syl2anc', [w.s([], 'simpl', '( %s -> %s )' % (Cf1, A0)), fnn1, w.s([gq1], 'idi', '( ( %s /\\ f e. NN ) -> ( %s x. sum_ x e. %s %s ) = ( %s x. %s ) )' % (A0, LG('f'), PC('f'), SIX('f', 'x'), LG('f'), GF('f')))], 'x') if False else \
        D(w, Cf1, 'syl', [D(w, Cf1, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Cf1, A0)), fnn1], Cf), w.s([gq1], 'idi', '( %s -> ( %s x. sum_ x e. %s %s ) = ( %s x. %s ) )' % (Cf, LG('f'), PC('f'), SIX('f', 'x'), LG('f'), GF('f')))],
          '( %s x. sum_ x e. %s %s ) = ( %s x. %s )' % (LG('f'), PC('f'), SIX('f', 'x'), LG('f'), GF('f')))
    SUMF = 'sum_ f e. %s ( %s x. %s )' % (FR, LG('f'), GF('f'))
    assert LHSS == 'sum_ f e. %s ( %s x. sum_ x e. %s %s )' % (FR, LG('f'), PC('f'), SIX('f', 'x')), LHSS[:300]
    lq = d('sumeq2dv', [gq2], '%s = %s' % (LHSS, SUMF))
    # the d-sum is dominated
    DR = '( 2 ... K )'
    Cd = '( %s /\\ d e. %s )' % (A0, DR)
    cd = mk(w, Cd)
    din = w.s([], 'simpr', '( %s -> d e. %s )' % (Cd, DR))
    del_ = cd('mpbid', [din, cd('syl2anc' if False else 'syl', [lift(w, kz, Cd), w.inst('elfz1' if False else 'id')], 'x')], 'x') if False else None
    dz = cd('elfzelzd' if False else 'syl', [din, w.inst('elfzelz')], 'd e. ZZ')
    d2 = cd('syl', [din, w.inst('elfzle1')], '2 <_ d'); dk = cd('syl', [din, w.inst('elfzle2')], 'd <_ K')
    ccd = Closure(w, Cd, {'d': ('ZZ', dz), 'W': ('RR', lift(w, wr, Cd)), 'K': ('ZZ', lift(w, kz, Cd)), Q: ('RR', lift(w, qr, Cd))})
    ccd.atom(Q)
    dnn = cd('mpbird' if False else 'elnnz1d' if False else 'syl', [cd('jca', [dz, linarith(w, Cd, [d2], '0 < d', closure=ccd)], '( d e. ZZ /\\ 0 < d )'), w.inst('elnnz1') if False else w.inst('elnnz')], 'd e. NN') if False else None
    dnn = cd('mpbird', [cd('jca', [dz, linarith(w, Cd, [d2], '0 < d', closure=ccd)], '( d e. ZZ /\\ 0 < d )'), a1(w, Cd, 'elnnz', '( d e. NN <-> ( d e. ZZ /\\ 0 < d ) )')], 'd e. NN')
    dw = linarith(w, Cd, [dk, lift(w, kw, Cd)], 'd <_ W', closure=ccd)
    GD = GF('d')
    Cdf = '( %s /\\ f e. NN )' % A0
    grd = rean(w, D(w, Cd, 'syl', [cd('jca', [w.s([], 'simpl', '( %s -> %s )' % (Cd, A0)), dnn], '( %s /\\ d e. NN )' % A0), w.s([], 'id', 'x')], 'x'), Cd) if False else None
    # G ( d ), from the f-facts by substitution: prove directly at d
    Cdx = '( %s /\\ x e. %s )' % (Cd, PC('d'))
    xbd = D(w, Cdx, 'sseldd', [a1(w, Cdx, 'ssrab2', '%s C_ %s' % (PC('d'), BASE('d'))), w.s([], 'simpr', '( %s -> x e. %s )' % (Cdx, PC('d')))], 'x e. %s' % BASE('d'))
    nxd = D(w, Cdx, 'jca', [lift(w, dnn, Cdx), xbd], '( d e. NN /\\ x e. %s )' % BASE('d'))
    PWTd = inst('cmpwt', {'N': 'd', 'X': 'x', 'H': V1})
    pwtd = D(w, Cdx, 'syl3anc', [nxd, lift(w, tr, Cdx), lift(w, d('jca', [yr, ur], '( Y e. RR /\\ U e. RR )'), Cdx), w.inst('cmpwt')], PWTd[1])
    jrd = D(w, Cdx, 'simp2d', [pwtd], '%s e. RR' % JX('d', 'x')); j0d = D(w, Cdx, 'simp3d', [pwtd], '0 <_ %s' % JX('d', 'x'))
    dfid = cd('syl', [dnn, w.s([w.s([], 'eqid', '( DChr ` d ) = ( DChr ` d )'), w.s([], 'eqid', '%s = %s' % (BASE('d'), BASE('d')))], 'dchrfi', '( d e. NN -> %s e. Fin )' % BASE('d'))], '%s e. Fin' % BASE('d'))
    pcd = cd('ssfid', [dfid, a1(w, Cd, 'ssrab2', '%s C_ %s' % (PC('d'), BASE('d')))], '%s e. Fin' % PC('d'))
    BCd = BC('S', 'V', 'd')
    # BC ( d ) C_ PC ( d )
    Cdy = '( %s /\\ y e. %s )' % (Cd, BASE('d'))
    BCB = '( ( d DChrCond y ) = d /\\ %s =/= (/) )' % __import__('cen2lib').ZFB('S', 'V', 'd', 'y')
    ssb = cd('ss2rabdv', [w.s([w.s([], 'simpl', '( %s -> ( d DChrCond y ) = d )' % BCB)], 'a1i', '( %s -> ( %s -> ( d DChrCond y ) = d ) )' % (Cdy, BCB))], '%s C_ %s' % (BCd, PC('d')))
    SBC = 'sum_ x e. %s %s' % (BCd, JX('d', 'x'))
    le1 = cd('fsumless', [pcd, jrd, j0d, ssb], '%s <_ %s' % (SBC, GD))
    gdr = cd('fsumrecl', [pcd, jrd], '%s e. RR' % GD); gd0 = cd('fsumge0', [pcd, jrd, j0d], '0 <_ %s' % GD)
    Cdx2 = '( %s /\\ x e. %s )' % (Cd, BCd)
    xpc = D(w, Cdx2, 'sseldd', [lift(w, ssb, Cdx2), w.s([], 'simpr', '( %s -> x e. %s )' % (Cdx2, BCd))], 'x e. %s' % PC('d'))
    jrd2 = D(w, Cdx2, 'syl2anc' if False else 'syl', [D(w, Cdx2, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Cdx2, Cd)), xpc], Cdx), w.s([jrd], 'idi', '( %s -> %s e. RR )' % (Cdx, JX('d', 'x')))], '%s e. RR' % JX('d', 'x'))
    j0d2 = D(w, Cdx2, 'syl', [D(w, Cdx2, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Cdx2, Cd)), xpc], Cdx), w.s([j0d], 'idi', '( %s -> 0 <_ %s )' % (Cdx, JX('d', 'x')))], '0 <_ %s' % JX('d', 'x'))
    bcf = cd('ssfid', [pcd, ssb], '%s e. Fin' % BCd)
    sbr = cd('fsumrecl', [bcf, jrd2], '%s e. RR' % SBC); sb0 = cd('fsumge0', [bcf, jrd2, j0d2], '0 <_ %s' % SBC)
    # log W <_ log ( Q / d )
    dp = cd('nnrpd', [dnn], 'd e. RR+')
    wrp = lift(w, d('elrpd', [wr, wp], 'W e. RR+'), Cd)
    qd = cd('rpdivcld', [cd('rpexpcld' if False else 'rpmulcld' if False else 'syl', [wrp, w.inst('id')], 'x') if False else cd('rpexpcld', [wrp, a1(w, Cd, '2z', '2 e. ZZ')], '%s e. RR+' % Q), dp], '( %s / d ) e. RR+' % Q)
    wdq = cd('mpbid', [cd('eqbrtrd' if False else 'id', [], 'x') if False else linarith(w, Cd, [lift(w, ww, Cd), lift(w, d('lemul2ad' if False else 'id', [], 'x'), Cd)] if False else [], 'x', closure=ccd) if False else
                        nlinarith(w, Cd, [dw, lift(w, ww, Cd), lift(w, w2, Cd)], '( W x. d ) <_ %s' % Q, closure=ccd),
                        cd('syl3anc', [lift(w, wr, Cd), lift(w, qr, Cd), cd('jca', [cd('rpred', [dp], 'd e. RR'), cd('rpgt0d', [dp], '0 < d')], '( d e. RR /\\ 0 < d )'), w.inst('lemuldiv')], '( ( W x. d ) <_ %s <-> W <_ ( %s / d ) )' % (Q, Q))], 'W <_ ( %s / d )' % Q)
    lwq = cd('mpbid', [wdq, cd('syl2anc', [wrp, qd, w.inst('logleb')], '( W <_ ( %s / d ) <-> %s <_ %s )' % (Q, LW, LG('d')))], '%s <_ %s' % (LW, LG('d')))
    lw0 = lift(w, d('syl2anc', [wr, w1, w.inst('logge0')], '0 <_ %s' % LW), Cd)
    lwr = lift(w, d('relogcld', [d('elrpd', [wr, wp], 'W e. RR+')], '%s e. RR' % LW), Cd)
    lgr = cd('relogcld', [qd], '%s e. RR' % LG('d'))
    m1 = cd('lemul1ad', [lwr, lgr, sbr, sb0, lwq], '( %s x. %s ) <_ ( %s x. %s )' % (LW, SBC, LG('d'), SBC))
    m2 = cd('lemul2ad', [sbr, gdr, lgr, cd('letrd', [a1(w, Cd, '0re', '0 e. RR'), lwr, lgr, lw0, lwq], '0 <_ %s' % LG('d')), le1], '( %s x. %s ) <_ ( %s x. %s )' % (LG('d'), SBC, LG('d'), GD))
    tm = cd('letrd', [cd('remulcld', [lwr, sbr], '( %s x. %s ) e. RR' % (LW, SBC)), cd('remulcld', [lgr, sbr], '( %s x. %s ) e. RR' % (LG('d'), SBC)), cd('remulcld', [lgr, gdr], '( %s x. %s ) e. RR' % (LG('d'), GD)), m1, m2],
            '( %s x. %s ) <_ ( %s x. %s )' % (LW, SBC, LG('d'), GD))
    FAM = FAMJ('U', 'Y')
    dfin = d('fzfid', [], '%s e. Fin' % DR)
    s1 = d('fsummulc2', [dfin, d('recnd', [d('relogcld', [d('elrpd', [wr, wp], 'W e. RR+')], '%s e. RR' % LW)], '%s e. CC' % LW), cd('recnd', [sbr], '%s e. CC' % SBC)],
           '( %s x. %s ) = sum_ d e. %s ( %s x. %s )' % (LW, FAM, DR, LW, SBC))
    s2 = d('fsumle', [dfin, cd('remulcld', [lwr, sbr], '( %s x. %s ) e. RR' % (LW, SBC)), cd('remulcld', [lgr, gdr], '( %s x. %s ) e. RR' % (LG('d'), GD)), tm],
           'sum_ d e. %s ( %s x. %s ) <_ sum_ d e. %s ( %s x. %s )' % (DR, LW, SBC, DR, LG('d'), GD))
    # rename d to f and enlarge the range
    eqd = 'd = f'
    idd = w.s([], 'id', '( %s -> %s )' % (eqd, eqd))
    # manual congruence ( d = f -> LG(d) G(d) = LG(f) G(f) ) (congr.py has no S. node)
    At_ = '( %s /\\ t e. %s )' % (eqd, TT)
    fin_ = w.s([], 'simpl', '( %s -> %s )' % (At_, eqd))
    ABSd = '( ( abs ` %s ) ^ 2 )' % PWS('t', 'Y', 'U', 'd', 'x')
    sti, abf = w.congr(ABSd, {'d': 'f'}, At_, {'d': fin_})
    assert abf == '( ( abs ` %s ) ^ 2 )' % PWS('t', 'Y', 'U', 'f', 'x'), abf
    ijq = w.s([sti], 'itgeq2dv', '( %s -> %s = %s )' % (eqd, JX('d', 'x'), JX('f', 'x')))
    stpc, pcf_ = w.congr(PC('d'), {'d': 'f'}, eqd, {'d': idd})
    assert pcf_ == PC('f')
    Ax_ = '( %s /\\ x e. %s )' % (eqd, PC('d'))
    sq12 = w.s([stpc, w.s([ijq], 'adantr', '( %s -> %s = %s )' % (Ax_, JX('d', 'x'), JX('f', 'x')))], 'sumeq12dv', '( %s -> %s = %s )' % (eqd, GD, GF('f')))
    stl, lgf_ = w.congr(LG('d'), {'d': 'f'}, eqd, {'d': idd})
    std = w.s([stl, sq12], 'oveq12d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (eqd, LG('d'), GD, LG('f'), GF('f')))
    cbd = a1(w, A0, 'cbvsumv', 'sum_ d e. %s ( %s x. %s ) = sum_ f e. %s ( %s x. %s )' % (DR, LG('d'), GD, DR, LG('f'), GF('f')), [std])
    # 2 ... K C_ 1 ... |_ Q ; terms nonnegative on FR
    Cf2 = '( %s /\\ f e. %s )' % (A0, DR)
    cf2 = mk(w, Cf2)
    f2in = w.s([], 'simpr', '( %s -> f e. %s )' % (Cf2, DR))
    fz2 = cf2('syl', [f2in, w.inst('elfzelz')], 'f e. ZZ'); f2 = cf2('syl', [f2in, w.inst('elfzle1')], '2 <_ f'); fk = cf2('syl', [f2in, w.inst('elfzle2')], 'f <_ K')
    ccf = Closure(w, Cf2, {'f': ('ZZ', fz2), 'W': ('RR', lift(w, wr, Cf2)), 'K': ('ZZ', lift(w, kz, Cf2)), Q: ('RR', lift(w, qr, Cf2))})
    ccf.atom(Q)
    fq = linarith(w, Cf2, [fk, lift(w, kw, Cf2), lift(w, wleq, Cf2)], 'f <_ %s' % Q, closure=ccf)
    qz = lift(w, d('flcld', [qr], '( |_ ` %s ) e. ZZ' % Q), Cf2)
    ffl = cf2('mpbid', [fq, cf2('syl2anc', [lift(w, qr, Cf2), fz2, w.inst('flge')], '( f <_ %s <-> f <_ ( |_ ` %s ) )' % (Q, Q))], 'f <_ ( |_ ` %s )' % Q)
    ffr = cf2('mpbird', [cf2('jca', [linarith(w, Cf2, [f2], '1 <_ f', closure=ccf), ffl], '( 1 <_ f /\\ f <_ ( |_ ` %s ) )' % Q),
                         cf2('syl3anc', [fz2, a1(w, Cf2, '1z', '1 e. ZZ'), qz, w.inst('elfz')], '( f e. %s <-> ( 1 <_ f /\\ f <_ ( |_ ` %s ) ) )' % (FR, Q))], 'f e. %s' % FR)
    ssr = d('ssrdv', [w.s([ffr], 'ex', '( %s -> ( f e. %s -> f e. %s ) )' % (A0, DR, FR))], '%s C_ %s' % (DR, FR))
    # on FR: log ( Q / f ) >_ 0, G ( f ) >_ 0
    cf1 = mk(w, Cf1)
    f1in = w.s([], 'simpr', '( %s -> f e. %s )' % (Cf1, FR))
    fz1 = cf1('syl', [f1in, w.inst('elfzelz')], 'f e. ZZ'); ffl1 = cf1('syl', [f1in, w.inst('elfzle2')], 'f <_ ( |_ ` %s )' % Q)
    fq1 = cf1('letrd', [cf1('zred', [fz1], 'f e. RR'), cf1('zred', [lift(w, d('flcld', [qr], '( |_ ` %s ) e. ZZ' % Q), Cf1)], '( |_ ` %s ) e. RR' % Q), lift(w, qr, Cf1), ffl1,
                        cf1('syl', [lift(w, qr, Cf1), w.inst('flle')], '( |_ ` %s ) <_ %s' % (Q, Q))], 'f <_ %s' % Q)
    fp1 = cf1('nnrpd', [fnn1], 'f e. RR+')
    q1 = cf1('mpbid', [cf1('eqbrtrd', [cf1('mullidd', [cf1('rpcnd', [fp1], 'f e. CC')], '( 1 x. f ) = f'), fq1], '( 1 x. f ) <_ %s' % Q),
                        cf1('syl3anc', [a1(w, Cf1, '1re', '1 e. RR'), lift(w, qr, Cf1), cf1('jca', [cf1('rpred', [fp1], 'f e. RR'), cf1('rpgt0d', [fp1], '0 < f')], '( f e. RR /\\ 0 < f )'), w.inst('lemuldiv')],
                            '( ( 1 x. f ) <_ %s <-> 1 <_ ( %s / f ) )' % (Q, Q))], '1 <_ ( %s / f )' % Q)
    qf = cf1('redivcld', [lift(w, qr, Cf1), cf1('rpred', [fp1], 'f e. RR'), cf1('rpne0d', [fp1], 'f =/= 0')], '( %s / f ) e. RR' % Q)
    lg0 = cf1('syl2anc', [qf, q1, w.inst('logge0')], '0 <_ %s' % LG('f'))
    lgr1 = cf1('relogcld', [cf1('rpdivcld', [cf1('rpexpcld', [lift(w, d('elrpd', [wr, wp], 'W e. RR+'), Cf1), a1(w, Cf1, '2z', '2 e. ZZ')], '%s e. RR+' % Q), fp1], '( %s / f ) e. RR+' % Q)], '%s e. RR' % LG('f'))
    Cfnn = '( %s /\\ f e. NN )' % A0
    grf = D(w, Cf1, 'syl', [D(w, Cf1, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Cf1, A0)), fnn1], Cfnn), w.s([gr], 'idi', '( %s -> %s e. RR )' % (Cfnn, GF('f')))], '%s e. RR' % GF('f'))
    g0f = D(w, Cf1, 'syl', [D(w, Cf1, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Cf1, A0)), fnn1], Cfnn), w.s([g0], 'idi', '( %s -> 0 <_ %s )' % (Cfnn, GF('f')))], '0 <_ %s' % GF('f'))
    tr1 = cf1('remulcld', [lgr1, grf], '( %s x. %s ) e. RR' % (LG('f'), GF('f')))
    t01 = cf1('mulge0d', [lgr1, grf, lg0, g0f], '0 <_ ( %s x. %s )' % (LG('f'), GF('f')))
    s3 = d('fsumless', [d('fzfid', [], '%s e. Fin' % FR), tr1, t01, ssr], 'sum_ f e. %s ( %s x. %s ) <_ %s' % (DR, LG('f'), GF('f'), SUMF))
    # chain: LW FAM = s1 <_ s2 = cbd <_ s3 = lq^-1 <_ lsp <_ rh
    SDL = 'sum_ d e. %s ( %s x. %s )' % (DR, LW, SBC)
    SDG = 'sum_ d e. %s ( %s x. %s )' % (DR, LG('d'), GD)
    SFG = 'sum_ f e. %s ( %s x. %s )' % (DR, LG('f'), GF('f'))
    cfin = Closure(w, A0, {})
    rr = {}
    rr[SDL] = d('fsumrecl', [dfin, cd('remulcld', [lwr, sbr], '( %s x. %s ) e. RR' % (LW, SBC))], '%s e. RR' % SDL)
    rr[SDG] = d('fsumrecl', [dfin, cd('remulcld', [lgr, gdr], '( %s x. %s ) e. RR' % (LG('d'), GD))], '%s e. RR' % SDG)
    rr[SUMF] = d('fsumrecl', [d('fzfid', [], '%s e. Fin' % FR), tr1], '%s e. RR' % SUMF)
    rr[RHSS] = d('lerelxrd' if False else 'id', [], 'x') if False else None
    a = d('eqbrtrd', [s1, s2], '( %s x. %s ) <_ %s' % (LW, FAM, SDG))
    b = d('breqtrd', [a, cbd], '( %s x. %s ) <_ %s' % (LW, FAM, SFG))
    sfr = d('eqeltrrd', [cbd, rr[SDG]], '%s e. RR' % SFG)
    c = d('letrd', [d('eqeltrd', [s1, rr[SDL]], '( %s x. %s ) e. RR' % (LW, FAM)), sfr, rr[SUMF], b, s3], '( %s x. %s ) <_ %s' % (LW, FAM, SUMF))
    lhr = d('eqeltrd', [lq, rr[SUMF]], '%s e. RR' % LHSS)
    c2 = d('breqtrrd', [c, lq], '( %s x. %s ) <_ %s' % (LW, FAM, LHSS))
    RR_ = RH[1].split(' <_ ')[-1] if False else '( %s x. ( ( log ` Z ) ^ 2 ) )' % C750
    rhr = c0.mem(RHSS, 'RR') if False else None
    c3 = d('letrd', [d('eqeltrd', [s1, rr[SDL]], '( %s x. %s ) e. RR' % (LW, FAM)), lhr, d('id' if False else 'rexrd' if False else 'lelttrd' if False else 'id', [], 'x') if False else
                     d('remulcld', [a1(w, A0, 'nnrei' if False else 'id', 'x') if False else c0.mem('; ; 1 0 0', 'RR'), d('fsumrecl', [pf, D(w, Cn, 'remulcld', [D(w, Cn, 'readdcld', [D(w, Cn, 'nnred', [nn_], 'n e. RR'), lift(w, c0.mem('( ( %s ^ 2 ) x. %s )' % (Q, T), 'RR'), Cn)], '( n + ( ( %s ^ 2 ) x. %s ) ) e. RR' % (Q, T)),
                                                                                                                                                   D(w, Cn, 'resqcld', [D(w, Cn, 'abscld', [D(w, Cn, 'ffvelcdmd', [lift(w, amf, Cn), w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, PS))], '( %s ` n ) e. CC' % AM)], '( abs ` ( %s ` n ) ) e. RR' % AM)], '( ( abs ` ( %s ` n ) ) ^ 2 ) e. RR' % AM)],
                                                                                                                         '( ( n + ( ( %s ^ 2 ) x. %s ) ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) ) e. RR' % (Q, T, AM))],
                                                                                         'sum_ n e. %s ( ( n + ( ( %s ^ 2 ) x. %s ) ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) ) e. RR' % (PS, Q, T, AM))], '%s e. RR' % RHSS),
                     c2, lsp], '( %s x. %s ) <_ %s' % (LW, FAM, RHSS))
    fin = d('letrd', [d('eqeltrd', [s1, rr[SDL]], '( %s x. %s ) e. RR' % (LW, FAM)), d('id' if False else 'remulcld', [d('remulcld', [c0.mem('; ; 7 5 0', 'RR'), d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)], '%s e. RR' % C750) if False else c0.mem('; ; 7 5 0', 'RR') if False else d('remulcld', [c0.mem('; ; 7 5 0', 'RR'), d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)], '%s e. RR' % C750),
                                                                                        d('resqcld', [d('relogcld', [d('elrpd', [zr, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), c0.mem('( exp ` ; 2 0 )', 'RR'), zr, c0.gt0('( exp ` ; 2 0 )'), ez], '0 < Z')], 'Z e. RR+')], '( log ` Z ) e. RR')], '( ( log ` Z ) ^ 2 ) e. RR')],
                                                                                       '%s e. RR' % RR_),
                      c3 if False else d('id', [], 'x') if False else c3, rh] if False else [d('eqeltrd', [s1, rr[SDL]], '( %s x. %s ) e. RR' % (LW, FAM)), None, None, None, None], 'x') if False else None
    rhr = d('letrd' if False else 'id', [], 'x') if False else None
    SRr = inst('cmsrh', {})[1]
    rr_ = d('remulcld', [d('remulcld', [c0.mem('; ; 7 5 0', 'RR'), d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)], '%s e. RR' % C750),
                         d('resqcld', [d('relogcld', [d('elrpd', [zr, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), c0.mem('( exp ` ; 2 0 )', 'RR'), zr, c0.gt0('( exp ` ; 2 0 )'), ez], '0 < Z')], 'Z e. RR+')], '( log ` Z ) e. RR')], '( ( log ` Z ) ^ 2 ) e. RR')],
                '%s e. RR' % RR_)
    rhsr = [l for l in w.lines if l.endswith('-> %s e. RR )' % RHSS)][0].split(':')[0]
    fin = d('letrd', [d('eqeltrd', [s1, rr[SDL]], '( %s x. %s ) e. RR' % (LW, FAM)), rhsr, rr_, c3, rh], '( %s x. %s ) <_ %s' % (LW, FAM, RR_))
    w.qed([fin], 'idi', S['cmsvu'])
    return run(w, only)


if __name__ == '__main__':
    gen_lsq()
    gen_sid()
    gen_srh()
    gen_svu()
