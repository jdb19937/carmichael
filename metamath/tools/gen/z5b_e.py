"""Sortie Z5b, section E: the Euler-product engine (Detector.lean 139-192) and the
absolute value of a finite product."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5blib import *
from cl import Closure, lift


def pp(w, a, mem):
    """( a -> p e. Prime ) from mem: ( a -> p e. { q e. Prime | ... } )"""
    return w.s([mem, w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % a)


def z5fprodabs():
    w = W('z5fprodabs', "The absolute value of a finite product is the product of the absolute values (Lean Finset.abs_prod; "
                        "set.mm's fprodabs2 is a mathbox theorem, this is a main-body proof by findcard2d).")
    h1, h2 = hyps_of(w, 'z5fprodabs')
    PS = lambda X: '( abs ` prod_ k e. %s B ) = prod_ k e. %s ( abs ` B )' % (X, X)
    cgs = {}
    for X in ('(/)', 'y', '( y u. { z } )', 'A'):
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (X, X))
        st_, new = w.wcongr(PS('x'), {'x': X}, 'x = %s' % X, {'x': idx})
        cgs[X] = st_
    # base
    b1 = w.s([], 'prod0', 'prod_ k e. (/) B = 1')
    b2 = w.s([b1], 'fveq2i', '( abs ` prod_ k e. (/) B ) = ( abs ` 1 )')
    b3 = w.s([b2, w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtri', '( abs ` prod_ k e. (/) B ) = 1')
    b4 = w.s([], 'prod0', 'prod_ k e. (/) ( abs ` B ) = 1')
    b5 = w.s([b3, b4], 'eqtr4i', PS('(/)'))
    base = w.s([b5], 'a1i', '( ph -> %s )' % PS('(/)'))
    # step under c
    c = '( ph /\\ ( y C_ A /\\ z e. ( A \\ y ) ) )'
    sc = mkst(w, c)
    ya = sc([], 'simprl', 'y C_ A')
    zin = sc([], 'simprr', 'z e. ( A \\ y )')
    za = sc([zin], 'eldifad', 'z e. A'); zny = sc([zin], 'eldifbd', '-. z e. y')
    fa = lift(w, h1, c)
    yf = sc([fa, ya, w.inst('ssfi')], 'syl2anc', 'y e. Fin')
    zv = w.s([w.s([], 'vex', 'z e. _V')], 'a1i', '( %s -> z e. _V )' % c)
    ck = '( %s /\\ k e. y )' % c
    kA = w.s([lift(w, ya, ck), w.s([], 'simpr', '( %s -> k e. y )' % ck)], 'sseldd', '( %s -> k e. A )' % ck)
    php = w.s([], 'simpll', '( %s -> ph )' % ck)
    bc = w.s([php, kA, h2], 'syl2anc', '( %s -> B e. CC )' % ck)
    abc = w.s([bc], 'abscld', '( %s -> ( abs ` B ) e. RR )' % ck)
    abcc = w.s([abc], 'recnd', '( %s -> ( abs ` B ) e. CC )' % ck)
    D = '[_ z / k ]_ B'
    ral = w.s([h2], 'ralrimiva', '( ph -> A. k e. A B e. CC )')
    dcn = sc([za, lift(w, ral, c), w.inst('rspcsbela')], 'syl2anc', '%s e. CC' % D)
    nfc = w.s([], 'nfv', 'F/ k %s' % c)
    nfd = w.s([], 'nfcsb1v', 'F/_ k %s' % D)
    csb = w.s([], 'csbeq1a', '( k = z -> B = %s )' % D)
    sp1 = w.s([nfc, nfd, yf, zv, zny, bc, csb, dcn], 'fprodsplitsn', '( %s -> prod_ k e. ( y u. { z } ) B = ( prod_ k e. y B x. %s ) )' % (c, D))
    AD = '( abs ` %s )' % D
    nfa = w.s([w.s([], 'nfcv', 'F/_ k abs'), nfd], 'nffv', 'F/_ k %s' % AD)
    csba = w.s([csb], 'fveq2d', '( k = z -> ( abs ` B ) = %s )' % AD)
    adr = sc([dcn], 'abscld', '%s e. RR' % AD); adc = sc([adr], 'recnd', '%s e. CC' % AD)
    sp2 = w.s([nfc, nfa, yf, zv, zny, abcc, csba, adc], 'fprodsplitsn',
              '( %s -> prod_ k e. ( y u. { z } ) ( abs ` B ) = ( prod_ k e. y ( abs ` B ) x. %s ) )' % (c, AD))
    PY = 'prod_ k e. y B'
    pyc = sc([yf, bc], 'fprodcl', '%s e. CC' % PY)
    e1 = sc([sp1], 'fveq2d', '( abs ` prod_ k e. ( y u. { z } ) B ) = ( abs ` ( %s x. %s ) )' % (PY, D))
    e2 = sc([pyc, dcn], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. %s )' % (PY, D, PY, AD))
    e12 = sc([e1, e2], 'eqtrd', '( abs ` prod_ k e. ( y u. { z } ) B ) = ( ( abs ` %s ) x. %s )' % (PY, AD))
    ct = '( %s /\\ %s )' % (c, PS('y'))
    th = w.s([], 'simpr', '( %s -> %s )' % (ct, PS('y')))
    e3 = w.s([th], 'oveq1d', '( %s -> ( ( abs ` %s ) x. %s ) = ( prod_ k e. y ( abs ` B ) x. %s ) )' % (ct, PY, AD, AD))
    e4 = w.s([lift(w, e12, ct), e3], 'eqtrd', '( %s -> ( abs ` prod_ k e. ( y u. { z } ) B ) = ( prod_ k e. y ( abs ` B ) x. %s ) )' % (ct, AD))
    e5 = w.s([e4, lift(w, sp2, ct)], 'eqtr4d', '( %s -> %s )' % (ct, PS('( y u. { z } )')))
    stp = w.s([e5], 'ex', '( %s -> ( %s -> %s ) )' % (c, PS('y'), PS('( y u. { z } )')))
    w.qed([cgs['(/)'], cgs['y'], cgs['( y u. { z } )'], cgs['A'], base, stp, h1], 'findcard2d', STATEMENTS['z5fprodabs'])
    return w


def z5sfrad():
    w = W('z5sfrad', "Lean sf_dvd_radical: a squarefree divisor D of N divides the radical prod_ p | N p "
                     "(D = prod_ p | D p by sqfprodid, and the primes of D are among those of N).")
    ante = '( %s /\\ ( N e. NN /\\ D || N ) )' % SQF('D')
    st = mkst(w, ante)
    dnn = st([], 'simpll', 'D e. NN'); nnn = st([], 'simprl', 'N e. NN'); dvn = st([], 'simprr', 'D || N')
    A = PF('D'); U = PF('N'); B = '( %s \\ %s )' % (U, A)
    b = '( %s /\\ q e. Prime )' % ante
    sb = mkst(w, b)
    qz = sy(w, b, sb([], 'simpr', 'q e. Prime'), 'prmz', 'q e. ZZ')
    tr = sb([qz, sb([lift(w, dnn, b)], 'nnzd', 'D e. ZZ'), sb([lift(w, nnn, b)], 'nnzd', 'N e. ZZ'), w.inst('dvdstr')], 'syl3anc', '( ( q || D /\\ D || N ) -> q || N )')
    tr2 = sb([lift(w, dvn, b), tr], 'mpan2d', '( q || D -> q || N )')
    ss = st([tr2], 'ss2rabdv', '%s C_ %s' % (A, U))
    un = st([ss, w.s([], 'undif', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (A, U, A, B, U))], 'sylib', '( %s u. %s ) = %s' % (A, B, U))
    un2 = st([un], 'eqcomd', '%s = ( %s u. %s )' % (U, A, B))
    dj = w.s([w.s([], 'disjdif', '( %s i^i %s ) = (/)' % (A, B))], 'a1i', '( %s -> ( %s i^i %s ) = (/) )' % (ante, A, B))
    uf = sy(w, ante, nnn, 'pffinq', '%s e. Fin' % U)
    a = '( %s /\\ p e. %s )' % (ante, U)
    pc = w.s([sy(w, a, pp(w, a, w.s([], 'simpr', '( %s -> p e. %s )' % (a, U))), 'prmnn', 'p e. NN')], 'nncnd', '( %s -> p e. CC )' % a)
    spl = st([dj, un2, uf, pc], 'fprodsplit', 'prod_ p e. %s p = ( prod_ p e. %s p x. prod_ p e. %s p )' % (U, A, B))
    sid = st([st([], 'simpl', SQF('D')), w.inst('sqfprodid')], 'syl', 'prod_ p e. %s p = D' % A)
    K = 'prod_ p e. %s p' % B
    bf = sy(w, ante, uf, 'diffi', '%s e. Fin' % B)
    a2 = '( %s /\\ p e. %s )' % (ante, B)
    inu = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (a2, B))], 'eldifad', '( %s -> p e. %s )' % (a2, U))
    pn = sy(w, a2, pp(w, a2, inu), 'prmnn', 'p e. NN')
    kn = st([bf, pn], 'fprodnncl', '%s e. NN' % K)
    e1 = st([spl, st([sid], 'oveq1d', '( prod_ p e. %s p x. %s ) = ( D x. %s )' % (A, K, K))], 'eqtrd', 'prod_ p e. %s p = ( D x. %s )' % (U, K))
    dv = st([st([dnn], 'nnzd', 'D e. ZZ'), st([kn], 'nnzd', '%s e. ZZ' % K), w.inst('dvdsmul1')], 'syl2anc', 'D || ( D x. %s )' % K)
    w.qed([dv, e1], 'breqtrrd', STATEMENTS['z5sfrad'])
    return w


def z5sqfeul():
    w = W('z5sqfeul', "Lean sum_divisors_ite_squarefree_prod (the Euler-product engine of Lemmas 3.1-3.3): the divisor sum of "
                      "if ( d squarefree , prod_ p | d B ( p ) , 0 ) is prod_ p | N ( 1 + B ( p ) ), for any summand B complex at the "
                      "primes; from V2's sqfdvdsum.")
    h1, h2 = hyps_of(w, 'z5sqfeul')
    ante = 'ph'
    st = mkst(w, ante)
    G = '( p e. Prime |-> B )'
    SQDV = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || N ) }'
    gf = w.s([h2, w.s([], 'eqid', '%s = %s' % (G, G))], 'fmptd', '( ph -> %s : Prime --> CC )' % G)
    PT = lambda X: 'prod_ t e. %s ( %s ` t )' % (PF(X), G)
    sq = st([h1, gf, w.inst('sqfdvdsum')], 'syl2anc', 'sum_ d e. %s %s = prod_ t e. %s ( 1 + ( %s ` t ) )' % (SQDV, PT('d'), PF('N'), G))
    # fvmpt at p
    fvc = w.s([w.s([], 'eqid', '%s = %s' % (G, G))], 'fvmpt2', '( ( p e. Prime /\\ B e. CC ) -> ( %s ` p ) = B )' % G)
    b0 = '( ph /\\ p e. Prime )'
    fvp = w.s([w.s([], 'simpr', '( %s -> p e. Prime )' % b0), h2, fvc], 'syl2anc', '( %s -> ( %s ` p ) = B )' % (b0, G))
    # left side: sum over SQDV of prod_ t ( G ` t ) = sum over SQDV of prod_ p B
    nfpG = w.s([], 'nfmpt1', 'F/_ p %s' % G)
    nfpt = w.s([], 'nfcv', 'F/_ p t')
    nftG = w.s([], 'nfcv', 'F/_ t %s' % G)
    nftp = w.s([], 'nfcv', 'F/_ t p')
    nfpGt = w.s([nfpG, nfpt], 'nffv', 'F/_ p ( %s ` t )' % G)
    nftGp = w.s([nftG, nftp], 'nffv', 'F/_ t ( %s ` p )' % G)
    cb1 = w.s([w.s([], 'fveq2', '( t = p -> ( %s ` t ) = ( %s ` p ) )' % (G, G)), w.s([], 'nfcv', 'F/_ p %s' % PF('d')), w.s([], 'nfcv', 'F/_ t %s' % PF('d')),
               nfpGt, nftGp], 'cbvprod', '%s = prod_ p e. %s ( %s ` p )' % (PT('d'), PF('d'), G))
    a = '( ph /\\ d e. %s )' % SQDV
    ai = '( %s /\\ p e. %s )' % (a, PF('d'))
    ppi = pp(w, ai, w.s([], 'simpr', '( %s -> p e. %s )' % (ai, PF('d'))))
    # ( ( a /\ p e. PF(d) ) -> ( G ` p ) = B ): from fvp under ( ph /\ p e. Prime )
    phi_ = w.s([], 'simpll', '( %s -> ph )' % ai)
    fvi = w.s([phi_, ppi, w.s([fvp], 'ex', '( ph -> ( p e. Prime -> ( %s ` p ) = B ) )' % G)], 'sylc', '( %s -> ( %s ` p ) = B )' % (ai, G))
    pe = w.s([fvi], 'prodeq2dv', '( %s -> prod_ p e. %s ( %s ` p ) = prod_ p e. %s B )' % (a, PF('d'), G, PF('d')))
    pe2 = w.s([w.s([cb1], 'a1i', '( %s -> %s = prod_ p e. %s ( %s ` p ) )' % (a, PT('d'), PF('d'), G)), pe], 'eqtrd', '( %s -> %s = prod_ p e. %s B )' % (a, PT('d'), PF('d')))
    L1 = st([pe2], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s B' % (SQDV, PT('d'), SQDV, PF('d')))
    # right side
    nfp1 = w.s([w.s([], 'nfcv', 'F/_ p 1'), w.s([], 'nfcv', 'F/_ p +'), nfpGt], 'nfov', 'F/_ p ( 1 + ( %s ` t ) )' % G)
    nft1 = w.s([w.s([], 'nfcv', 'F/_ t 1'), w.s([], 'nfcv', 'F/_ t +'), nftGp], 'nfov', 'F/_ t ( 1 + ( %s ` p ) )' % G)
    cb2 = w.s([w.s([w.s([], 'fveq2', '( t = p -> ( %s ` t ) = ( %s ` p ) )' % (G, G))], 'oveq2d', '( t = p -> ( 1 + ( %s ` t ) ) = ( 1 + ( %s ` p ) ) )' % (G, G)),
               w.s([], 'nfcv', 'F/_ p %s' % PF('N')), w.s([], 'nfcv', 'F/_ t %s' % PF('N')), nfp1, nft1],
              'cbvprod', 'prod_ t e. %s ( 1 + ( %s ` t ) ) = prod_ p e. %s ( 1 + ( %s ` p ) )' % (PF('N'), G, PF('N'), G))
    bn = '( ph /\\ p e. %s )' % PF('N')
    ppn = pp(w, bn, w.s([], 'simpr', '( %s -> p e. %s )' % (bn, PF('N'))))
    fvn = w.s([w.s([], 'simpl', '( %s -> ph )' % bn), ppn, w.s([fvp], 'ex', '( ph -> ( p e. Prime -> ( %s ` p ) = B ) )' % G)], 'sylc', '( %s -> ( %s ` p ) = B )' % (bn, G))
    R1 = st([w.s([fvn], 'oveq2d', '( %s -> ( 1 + ( %s ` p ) ) = ( 1 + B ) )' % (bn, G))], 'prodeq2dv',
            'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s ( 1 + B )' % (PF('N'), G, PF('N')))
    R2 = st([w.s([cb2], 'a1i', '( ph -> prod_ t e. %s ( 1 + ( %s ` t ) ) = prod_ p e. %s ( 1 + ( %s ` p ) ) )' % (PF('N'), G, PF('N'), G)), R1], 'eqtrd',
            'prod_ t e. %s ( 1 + ( %s ` t ) ) = prod_ p e. %s ( 1 + B )' % (PF('N'), G, PF('N')))
    core = st([st([L1], 'eqcomd', 'sum_ d e. %s prod_ p e. %s B = sum_ d e. %s %s' % (SQDV, PF('d'), SQDV, PT('d'))), sq], 'eqtrd',
              'sum_ d e. %s prod_ p e. %s B = prod_ t e. %s ( 1 + ( %s ` t ) )' % (SQDV, PF('d'), PF('N'), G))
    core = st([core, R2], 'eqtrd', 'sum_ d e. %s prod_ p e. %s B = prod_ p e. %s ( 1 + B )' % (SQDV, PF('d'), PF('N')))
    # the if form over all divisors
    IF = 'if ( ( mmu ` d ) =/= 0 , prod_ p e. %s B , 0 )' % PF('d')
    DVN = DV('N')
    ssr = w.s([w.s([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N )')], 'a1i',
                   '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N ) )')], 'ss2rabi', '%s C_ %s' % (SQDV, DVN))
    ss = w.s([ssr], 'a1i', '( ph -> %s C_ %s )' % (SQDV, DVN))
    elsq = w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d', '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
                w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'anbi12d', '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) <-> ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )')
    elsq = w.s([elsq], 'elrab', '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )' % SQDV)
    eldv = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || N ) )' % DVN)
    # body in CC on SQDV
    sa = mkst(w, a)
    ma = sa([sa([], 'simpr', 'd e. %s' % SQDV), w.s([elsq], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) ) )' % (a, SQDV))], 'mpbid',
            '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) )')
    dn = sa([ma], 'simpld', 'd e. NN')
    mu0 = sa([ma], 'simprld', '( mmu ` d ) =/= 0')
    fd = sy(w, a, dn, 'pffinq', '%s e. Fin' % PF('d'))
    bci = w.s([w.s([], 'simpll', '( %s -> ph )' % ai), ppi, h2], 'syl2anc', '( %s -> B e. CC )' % ai)
    pc = sa([fd, bci], 'fprodcl', 'prod_ p e. %s B e. CC' % PF('d'))
    ifc = sa([pc, sa([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF)
    it = sa([mu0], 'iftrued', '%s = prod_ p e. %s B' % (IF, PF('d')))
    # zero off SQDV
    dd = '( ph /\\ d e. ( %s \\ %s ) )' % (DVN, SQDV)
    sd = mkst(w, dd)
    ind = sd([sd([], 'simpr', 'd e. ( %s \\ %s )' % (DVN, SQDV))], 'eldifad', 'd e. %s' % DVN)
    nsq = sd([sd([], 'simpr', 'd e. ( %s \\ %s )' % (DVN, SQDV))], 'eldifbd', '-. d e. %s' % SQDV)
    md = sd([ind, w.s([eldv], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ d || N ) ) )' % (dd, DVN))], 'mpbid', '( d e. NN /\\ d || N )')
    e_ = '( %s /\\ ( mmu ` d ) =/= 0 )' % dd
    se = mkst(w, e_)
    jn = se([lift(w, sd([md], 'simpld', 'd e. NN'), e_), se([se([], 'simpr', '( mmu ` d ) =/= 0'), lift(w, sd([md], 'simprd', 'd || N'), e_)], 'jca', '( ( mmu ` d ) =/= 0 /\\ d || N )')],
            'jca', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) )')
    imp = w.s([jn], 'ex', '( %s -> ( ( mmu ` d ) =/= 0 -> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) ) )' % dd)
    imp2 = sd([imp, w.s([elsq], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) ) )' % (dd, SQDV))], 'sylibrd', '( ( mmu ` d ) =/= 0 -> d e. %s )' % SQDV)
    nmu = sd([imp2, nsq], 'mtod', '-. ( mmu ` d ) =/= 0')
    z0 = sd([nmu], 'iffalsed', '%s = 0' % IF)
    dvf = sy(w, ante, h1, 'dvdsfi', '%s e. Fin' % DVN)
    fs = st([ss, ifc, z0, dvf], 'fsumss', 'sum_ d e. %s %s = sum_ d e. %s %s' % (SQDV, IF, DVN, IF))
    s2 = st([it], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s B' % (SQDV, IF, SQDV, PF('d')))
    ch = st([st([fs], 'eqcomd', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DVN, IF, SQDV, IF)), s2], 'eqtrd', 'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s B' % (DVN, IF, SQDV, PF('d')))
    w.qed([ch, core], 'eqtrd', STATEMENTS['z5sqfeul'])
    return w


if __name__ == '__main__':
    import z5blib
    for f in sys.argv[1:]:
        z5blib.run(globals()[f]())
