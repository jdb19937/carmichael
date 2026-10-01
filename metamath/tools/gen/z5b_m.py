"""Sortie Z5b, section M: multiplicativity of f = mu phi (Detector.lean 283-340) and
the prime-set product helper z5pfif."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5blib import *
from cl import Closure, lift
import lin


def _pp(w, a, mem, S):
    i = w.inst('elrabi')
    return w.s([mem, i], 'syl', '( %s -> p e. Prime )' % a)


def z5fmpprm():
    w = W('z5fmpprm', "Lean fmp_prime: f ( p ) = mmu ( p ) phi ( p ) = - ( p - 1 ) for a prime p.")
    ante = 'P e. Prime'
    st = mkst(w, ante)
    pr = st([], 'id', 'P e. Prime')
    mu = sy(w, ante, pr, 'bvmuprm', '( mmu ` P ) = -u 1')
    ph = sy(w, ante, pr, 'phiprm', '( phi ` P ) = ( P - 1 )')
    e1 = st([mu, ph], 'oveq12d', '%s = ( -u 1 x. ( P - 1 ) )' % FMP('P'))
    pc = st([sy(w, ante, pr, 'prmnn', 'P e. NN')], 'nncnd', 'P e. CC')
    pm = st([pc, st([], '1cnd', '1 e. CC')], 'subcld', '( P - 1 ) e. CC')
    e2 = st([pm], 'mulm1d', '( -u 1 x. ( P - 1 ) ) = -u ( P - 1 )')
    w.qed([e1, e2], 'eqtrd', STATEMENTS['z5fmpprm'])
    return w


def z5fmpmul():
    w = W('z5fmpmul', "Lean fmp_mul_coprime: f = mmu phi is multiplicative, f ( A B ) = f ( A ) f ( B ) for coprime A, B.")
    ante = '( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 )'
    st = mkst(w, ante)
    idd = st([], 'id', ante)
    mu = st([idd, w.inst('mumul')], 'syl', '( mmu ` ( A x. B ) ) = ( ( mmu ` A ) x. ( mmu ` B ) )')
    ph = st([idd, w.inst('phimul')], 'syl', '( phi ` ( A x. B ) ) = ( ( phi ` A ) x. ( phi ` B ) )')
    e1 = st([mu, ph], 'oveq12d', '%s = ( ( ( mmu ` A ) x. ( mmu ` B ) ) x. ( ( phi ` A ) x. ( phi ` B ) ) )' % FMP('( A x. B )'))
    an = st([], 'simp1', 'A e. NN'); bn = st([], 'simp2', 'B e. NN')
    c = {}
    for X, s in (('A', an), ('B', bn)):
        c['mu' + X] = st([sy(w, ante, s, 'mucl', '( mmu ` %s ) e. ZZ' % X)], 'zcnd', '( mmu ` %s ) e. CC' % X)
        c['phi' + X] = st([sy(w, ante, s, 'phicl', '( phi ` %s ) e. NN' % X)], 'nncnd', '( phi ` %s ) e. CC' % X)
    e2 = st([c['muA'], c['muB'], c['phiA'], c['phiB']], 'mul4d',
            '( ( ( mmu ` A ) x. ( mmu ` B ) ) x. ( ( phi ` A ) x. ( phi ` B ) ) ) = ( %s x. %s )' % (FMP('A'), FMP('B')))
    w.qed([e1, e2], 'eqtrd', STATEMENTS['z5fmpmul'])
    return w


def z5fmpprod():
    w = W('z5fmpprod', "Lean fmp_prod_primeFactors: for squarefree M, f ( M ) = prod_ p | M f ( p ) "
                       "(mmu ( M ) = ( -1 ) ^ omega ( M ), phi ( M ) = prod ( p - 1 ), f ( p ) = - ( p - 1 )).")
    ante = SQF('M')
    st = mkst(w, ante)
    mnn = st([], 'simpl', 'M e. NN')
    fin = sy(w, ante, mnn, 'pffinq', '%s e. Fin' % PF('M'))
    a = '( %s /\\ p e. %s )' % (ante, PF('M'))
    sa = mkst(w, a)
    pp = _pp(w, a, sa([], 'simpr', 'p e. %s' % PF('M')), PF('M'))
    fp = sy(w, a, pp, 'z5fmpprm', '%s = -u ( p - 1 )' % FMP('p'))
    pm = sa([sa([sy(w, a, pp, 'prmnn', 'p e. NN')], 'nncnd', 'p e. CC'), sa([], '1cnd', '1 e. CC')], 'subcld', '( p - 1 ) e. CC')
    m1 = sa([sa([pm], 'mulm1d', '( -u 1 x. ( p - 1 ) ) = -u ( p - 1 )')], 'eqcomd', '-u ( p - 1 ) = ( -u 1 x. ( p - 1 ) )')
    t = sa([fp, m1], 'eqtrd', '%s = ( -u 1 x. ( p - 1 ) )' % FMP('p'))
    P1 = 'prod_ p e. %s %s' % (PF('M'), FMP('p'))
    P2 = 'prod_ p e. %s ( -u 1 x. ( p - 1 ) )' % PF('M')
    PA = 'prod_ p e. %s -u 1' % PF('M'); PB = 'prod_ p e. %s ( p - 1 )' % PF('M')
    s1 = st([t], 'prodeq2dv', '%s = %s' % (P1, P2))
    n1 = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % a)
    s2 = st([fin, n1, pm], 'fprodmul', '%s = ( %s x. %s )' % (P2, PA, PB))
    HS = '( # ` %s )' % PF('M')
    n1c = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % ante)
    s3 = st([fin, n1c, w.inst('fprodconst')], 'syl2anc', '%s = ( -u 1 ^ %s )' % (PA, HS))
    # muval2 with its own letter p in the prime set
    PFp = '{ p e. Prime | p || M }'
    mv = st([st([], 'id', ante), w.inst('muval2')], 'syl', '( mmu ` M ) = ( -u 1 ^ ( # ` %s ) )' % PFp)
    cb = w.s([w.s([], 'breq1', '( p = q -> ( p || M <-> q || M ) )')], 'cbvrabv', '%s = %s' % (PFp, PF('M')))
    cb2 = w.s([cb], 'fveq2i', '( # ` %s ) = %s' % (PFp, HS))
    cb3 = w.s([cb2], 'oveq2i', '( -u 1 ^ ( # ` %s ) ) = ( -u 1 ^ %s )' % (PFp, HS))
    mv2 = st([mv, w.s([cb3], 'a1i', '( %s -> ( -u 1 ^ ( # ` %s ) ) = ( -u 1 ^ %s ) )' % (ante, PFp, HS))], 'eqtrd', '( mmu ` M ) = ( -u 1 ^ %s )' % HS)
    s3b = st([s3, st([mv2], 'eqcomd', '( -u 1 ^ %s ) = ( mmu ` M )' % HS)], 'eqtrd', '%s = ( mmu ` M )' % PA)
    s4 = st([st([], 'id', ante), w.inst('phisqf')], 'syl', '( phi ` M ) = %s' % PB)
    s4b = st([s4], 'eqcomd', '%s = ( phi ` M )' % PB)
    s5 = st([s3b, s4b], 'oveq12d', '( %s x. %s ) = %s' % (PA, PB, FMP('M')))
    ch = st([s1, s2], 'eqtrd', '%s = ( %s x. %s )' % (P1, PA, PB))
    ch = st([ch, s5], 'eqtrd', '%s = %s' % (P1, FMP('M')))
    w.qed([ch], 'eqcomd', STATEMENTS['z5fmpprod'])
    return w


def z5pfif():
    w = W('z5pfif', "Lean Finset.prod_filter in the form of psi_eq_prod and sum_abs_hBV_le: for R | M, the product over the primes of M "
                    "of if ( p | R , C , 1 ) is the product of C over the primes of R.")
    h1, h2, h3, h4 = hyps_of(w, 'z5pfif')
    ante = 'ph'
    st = mkst(w, ante)
    IF = 'if ( p || R , C , 1 )'
    A = PF('R'); B = PF('M')
    # A C_ B
    b = '( ph /\\ q e. Prime )'
    sb = mkst(w, b)
    qz = sy(w, b, sb([], 'simpr', 'q e. Prime'), 'prmz', 'q e. ZZ')
    rz = sb([lift(w, h2, b)], 'nnzd', 'R e. ZZ'); mz = sb([lift(w, h1, b)], 'nnzd', 'M e. ZZ')
    tr = sb([qz, rz, mz, w.inst('dvdstr')], 'syl3anc', '( ( q || R /\\ R || M ) -> q || M )')
    tr2 = sb([lift(w, h3, b), tr], 'mpan2d', '( q || R -> q || M )')
    ss = st([tr2], 'ss2rabdv', '%s C_ %s' % (A, B))
    # body in CC on A
    a = '( ph /\\ p e. %s )' % A
    sa = mkst(w, a)
    ppa = _pp(w, a, sa([], 'simpr', 'p e. %s' % A), A)
    cc = w.s([ppa, h4], 'syldan', '( %s -> C e. CC )' % a)
    ifc = sa([cc, sa([], '1cnd', '1 e. CC')], 'ifcld', '%s e. CC' % IF)
    # on B \ A the body is 1
    d = '( ph /\\ p e. ( %s \\ %s ) )' % (B, A)
    sd = mkst(w, d)
    inb = sd([sd([], 'simpr', 'p e. ( %s \\ %s )' % (B, A))], 'eldifad', 'p e. %s' % B)
    nina = sd([sd([], 'simpr', 'p e. ( %s \\ %s )' % (B, A))], 'eldifbd', '-. p e. %s' % A)
    ppd = _pp(w, d, inb, B)
    el = w.s([w.s([], 'breq1', '( q = p -> ( q || R <-> p || R ) )')], 'elrab', '( p e. %s <-> ( p e. Prime /\\ p || R ) )' % A)
    n2 = sd([nina, w.s([el], 'a1i', '( %s -> ( p e. %s <-> ( p e. Prime /\\ p || R ) ) )' % (d, A))], 'mtbid', '-. ( p e. Prime /\\ p || R )')
    n3 = sd([n2, w.s([], 'imnan', '( ( p e. Prime -> -. p || R ) <-> -. ( p e. Prime /\\ p || R ) )')], 'sylibr', '( p e. Prime -> -. p || R )')
    n4 = sd([ppd, n3], 'mpd', '-. p || R')
    one = sd([n4], 'iffalsed', '%s = 1' % IF)
    finb = sy(w, ante, h1, 'pffinq', '%s e. Fin' % B)
    e1 = st([ss, ifc, one, finb], 'fprodss', 'prod_ p e. %s %s = prod_ p e. %s %s' % (A, IF, B, IF))
    # on A the body is C
    pa = sa([sa([], 'simpr', 'p e. %s' % A), w.s([el], 'a1i', '( %s -> ( p e. %s <-> ( p e. Prime /\\ p || R ) ) )' % (a, A))], 'mpbid', '( p e. Prime /\\ p || R )')
    tc = sa([sa([pa], 'simprd', 'p || R')], 'iftrued', '%s = C' % IF)
    e2 = st([tc], 'prodeq2dv', 'prod_ p e. %s %s = prod_ p e. %s C' % (A, IF, A))
    e3 = st([e1], 'eqcomd', 'prod_ p e. %s %s = prod_ p e. %s %s' % (B, IF, A, IF))
    w.qed([e3, e2], 'eqtrd', STATEMENTS['z5pfif'])
    return w


if __name__ == '__main__':
    import z5blib
    for f in sys.argv[1:]:
        z5blib.run(globals()[f]())
