"""Sortie A4c, batch 10: the divisor set of a prime multiple (Lean:
AlgScan.divisors_prime_mul) and the divisor-set membership bridge."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

def DIVS(x): return '{ m e. ( 1 ... %s ) | m || %s }' % (x, x)

# ------------------------------------------------------------------ divsetel
if not only or 'divsetel' in only:
    w = W('divsetel', 'Membership in the set of divisors (Lean: Nat.mem_divisors).')
    A = '( M e. NN /\\ X e. ZZ )'
    mm = w.s([], 'simpl', '( %s -> M e. NN )' % A)
    xz = w.s([], 'simpr', '( %s -> X e. ZZ )' % A)
    sb = w.s([], 'breq1', '( m = X -> ( m || M <-> X || M ) )')
    er = w.s([sb], 'elrab', '( X e. %s <-> ( X e. ( 1 ... M ) /\\ X || M ) )' % DIVS('M'))
    erd = w.s([er], 'a1i', '( %s -> ( X e. %s <-> ( X e. ( 1 ... M ) /\\ X || M ) ) )' % (A, DIVS('M')))
    one = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A)
    mz = w.s([mm], 'nnzd', '( %s -> M e. ZZ )' % A)
    fzb = w.s([w.s([xz, one, mz], '3jca', '( %s -> ( X e. ZZ /\\ 1 e. ZZ /\\ M e. ZZ ) )' % A), w.inst('elfz')], 'syl',
              '( %s -> ( X e. ( 1 ... M ) <-> ( 1 <_ X /\\ X <_ M ) ) )' % A)
    nz1 = w.s([w.s([], 'elnnz1', '( X e. NN <-> ( X e. ZZ /\\ 1 <_ X ) )')], 'a1i',
              '( %s -> ( X e. NN <-> ( X e. ZZ /\\ 1 <_ X ) ) )' % A)
    F = '( %s /\\ ( X e. ( 1 ... M ) /\\ X || M ) )' % A
    f1 = w.s([w.s([w.s([xz], 'adantr', '( %s -> X e. ZZ )' % F),
                   w.s([w.s([w.s([], 'simprl', '( %s -> X e. ( 1 ... M ) )' % F),
                             w.s([fzb], 'adantr', '( %s -> ( X e. ( 1 ... M ) <-> ( 1 <_ X /\\ X <_ M ) ) )' % F)], 'mpbid',
                            '( %s -> ( 1 <_ X /\\ X <_ M ) )' % F)], 'simpld', '( %s -> 1 <_ X )' % F)], 'jca',
                  '( %s -> ( X e. ZZ /\\ 1 <_ X ) )' % F),
              w.s([nz1], 'adantr', '( %s -> ( X e. NN <-> ( X e. ZZ /\\ 1 <_ X ) ) )' % F)], 'mpbird',
             '( %s -> X e. NN )' % F)
    fwd = w.s([w.s([f1, w.s([], 'simprr', '( %s -> X || M )' % F)], 'jca', '( %s -> ( X e. NN /\\ X || M ) )' % F)], 'ex',
              '( %s -> ( ( X e. ( 1 ... M ) /\\ X || M ) -> ( X e. NN /\\ X || M ) ) )' % A)
    G = '( %s /\\ ( X e. NN /\\ X || M ) )' % A
    xn = w.s([], 'simprl', '( %s -> X e. NN )' % G)
    xd = w.s([], 'simprr', '( %s -> X || M )' % G)
    ge1 = w.s([xn], 'nnge1d', '( %s -> 1 <_ X )' % G)
    lem = w.s([w.s([w.s([w.s([xz], 'adantr', '( %s -> X e. ZZ )' % G), w.s([mm], 'adantr', '( %s -> M e. NN )' % G)], 'jca',
                    '( %s -> ( X e. ZZ /\\ M e. NN ) )' % G), w.inst('dvdsle')], 'syl',
                   '( %s -> ( X || M -> X <_ M ) )' % G), xd], 'mpd', '( %s -> X <_ M )' % G)
    g1 = w.s([w.s([ge1, lem], 'jca', '( %s -> ( 1 <_ X /\\ X <_ M ) )' % G),
              w.s([fzb], 'adantr', '( %s -> ( X e. ( 1 ... M ) <-> ( 1 <_ X /\\ X <_ M ) ) )' % G)], 'mpbird',
             '( %s -> X e. ( 1 ... M ) )' % G)
    bwd = w.s([w.s([g1, xd], 'jca', '( %s -> ( X e. ( 1 ... M ) /\\ X || M ) )' % G)], 'ex',
              '( %s -> ( ( X e. NN /\\ X || M ) -> ( X e. ( 1 ... M ) /\\ X || M ) ) )' % A)
    w.qed([erd, w.s([fwd, bwd], 'impbid', '( %s -> ( ( X e. ( 1 ... M ) /\\ X || M ) <-> ( X e. NN /\\ X || M ) ) )' % A)],
          'bitrd', '( %s -> ( X e. %s <-> ( X e. NN /\\ X || M ) ) )' % (A, DIVS('M')))
    run(w)

# ------------------------------------------------------------------ mulimel
if not only or 'mulimel' in only:
    w = W('mulimel', 'Membership in the image of a set under multiplication by a constant.')
    FMP = '( d e. S |-> ( d x. Q ) )'
    eq = w.s([], 'eqid', '%s = %s' % (FMP, FMP))
    w.qed([eq], 'elrnmpt', '( X e. V -> ( X e. ran %s <-> E. d e. S X = ( d x. Q ) ) )' % FMP)
    run(w)

# ------------------------------------------------------------------ divprmmul
QM = '( Q x. M )'
DM = DIVS('M')
DQM = DIVS(QM)
FMP = '( d e. %s |-> ( d x. Q ) )' % DM
RHS = '( %s u. ran %s )' % (DM, FMP)

def dsel(w, A, num, numst, x, xzst):
    """( A -> ( x e. DIVS( num ) <-> ( x e. NN /\\ x || num ) ) )"""
    return w.s([w.s([numst, xzst], 'jca', '( %s -> ( %s e. NN /\\ %s e. ZZ ) )' % (A, num, x)), w.inst('divsetel')], 'syl',
               '( %s -> ( %s e. %s <-> ( %s e. NN /\\ %s || %s ) ) )' % (A, x, DIVS(num), x, x, num))

if not only or 'divprmmul' in only:
    w = W('divprmmul', 'The divisors of a prime multiple (Lean: divisors_prime_mul).')
    A = '( Q e. Prime /\\ M e. NN )'
    qp = w.s([], 'simpl', '( %s -> Q e. Prime )' % A)
    mm = w.s([], 'simpr', '( %s -> M e. NN )' % A)
    qn = w.s([qp, w.inst('prmnn')], 'syl', '( %s -> Q e. NN )' % A)
    qz = w.s([qn], 'nnzd', '( %s -> Q e. ZZ )' % A)
    mz = w.s([mm], 'nnzd', '( %s -> M e. ZZ )' % A)
    qmn = w.s([qn, mm], 'nnmulcld', '( %s -> %s e. NN )' % (A, QM))
    qne = w.s([qn], 'nnne0d', '( %s -> Q =/= 0 )' % A)
    # ------------------------------------------------- LHS C_ RHS
    B = '( %s /\\ x e. %s )' % (A, DQM)
    b = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (B, f))
    sbx = w.s([], 'breq1', '( m = x -> ( m || %s <-> x || %s ) )' % (QM, QM))
    erx = w.s([w.s([sbx], 'elrab', '( x e. %s <-> ( x e. ( 1 ... %s ) /\\ x || %s ) )' % (DQM, QM, QM))], 'a1i',
              '( %s -> ( x e. %s <-> ( x e. ( 1 ... %s ) /\\ x || %s ) ) )' % (B, DQM, QM, QM))
    xfz = w.s([w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (B, DQM)), erx], 'mpbid',
                   '( %s -> ( x e. ( 1 ... %s ) /\\ x || %s ) )' % (B, QM, QM))], 'simpld',
              '( %s -> x e. ( 1 ... %s ) )' % (B, QM))
    xzb = w.s([xfz, w.inst('elfzelz')], 'syl', '( %s -> x e. ZZ )' % B)
    selq = dsel(w, B, QM, b(qmn, '%s e. NN' % QM), 'x', xzb)
    xnd = w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (B, DQM)), selq], 'mpbid',
              '( %s -> ( x e. NN /\\ x || %s ) )' % (B, QM))
    xn = w.s([xnd], 'simpld', '( %s -> x e. NN )' % B)
    xd = w.s([xnd], 'simprd', '( %s -> x || %s )' % (B, QM))
    #   case Q || x
    C1 = '( %s /\\ Q || x )' % B
    c1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C1, f))
    qdx = w.s([], 'simpr', '( %s -> Q || x )' % C1)
    DQ = '( x / Q )'
    dn = w.s([w.s([w.s([c1(xn, 'x e. NN'), c1(b(qn, 'Q e. NN'), 'Q e. NN')], 'jca',
                       '( %s -> ( x e. NN /\\ Q e. NN ) )' % C1), w.inst('nndivdvds')], 'syl',
                  '( %s -> ( Q || x <-> %s e. NN ) )' % (C1, DQ)), qdx], 'mpbid', '( %s -> %s e. NN )' % (C1, DQ))
    xeq = w.s([w.s([c1(xn, 'x e. NN')], 'nncnd', '( %s -> x e. CC )' % C1),
               w.s([c1(b(qn, 'Q e. NN'), 'Q e. NN')], 'nncnd', '( %s -> Q e. CC )' % C1),
               c1(b(qne, 'Q =/= 0'), 'Q =/= 0'), w.inst('divcan1')], 'syl3anc',
              '( %s -> ( %s x. Q ) = x )' % (C1, DQ))
    comm = w.s([w.s([c1(b(qn, 'Q e. NN'), 'Q e. NN')], 'nncnd', '( %s -> Q e. CC )' % C1),
                w.s([c1(b(mm, 'M e. NN'), 'M e. NN')], 'nncnd', '( %s -> M e. CC )' % C1)], 'mulcomd',
               '( %s -> %s = ( M x. Q ) )' % (C1, QM))
    dvd1 = w.s([w.s([xeq, c1(xd, 'x || %s' % QM)], 'eqbrtrd',
                    '( %s -> ( %s x. Q ) || %s )' % (C1, DQ, QM)), comm], 'breqtrd',
               '( %s -> ( %s x. Q ) || ( M x. Q ) )' % (C1, DQ))
    canc = w.s([w.s([w.s([dn], 'nnzd', '( %s -> %s e. ZZ )' % (C1, DQ)), c1(b(mz, 'M e. ZZ'), 'M e. ZZ'),
                     w.s([c1(b(qz, 'Q e. ZZ'), 'Q e. ZZ'), c1(b(qne, 'Q =/= 0'), 'Q =/= 0')], 'jca',
                         '( %s -> ( Q e. ZZ /\\ Q =/= 0 ) )' % C1)], '3jca',
                    '( %s -> ( %s e. ZZ /\\ M e. ZZ /\\ ( Q e. ZZ /\\ Q =/= 0 ) ) )' % (C1, DQ)), w.inst('dvdsmulcr')], 'syl',
               '( %s -> ( ( %s x. Q ) || ( M x. Q ) <-> %s || M ) )' % (C1, DQ, DQ))
    ddm = w.s([w.s([dn, w.s([dvd1, canc], 'mpbid', '( %s -> %s || M )' % (C1, DQ))], 'jca',
                   '( %s -> ( %s e. NN /\\ %s || M ) )' % (C1, DQ, DQ)),
               dsel(w, C1, 'M', c1(b(mm, 'M e. NN'), 'M e. NN'), DQ, w.s([dn], 'nnzd', '( %s -> %s e. ZZ )' % (C1, DQ)))],
              'mpbird', '( %s -> %s e. %s )' % (C1, DQ, DM))
    sbd = w.s([], 'oveq1', '( d = %s -> ( d x. Q ) = ( %s x. Q ) )' % (DQ, DQ))
    sbd2 = w.s([sbd], 'eqeq2d', '( d = %s -> ( x = ( d x. Q ) <-> x = ( %s x. Q ) ) )' % (DQ, DQ))
    rex = w.s([w.s([ddm, w.s([xeq], 'eqcomd', '( %s -> x = ( %s x. Q ) )' % (C1, DQ))], 'jca',
                   '( %s -> ( %s e. %s /\\ x = ( %s x. Q ) ) )' % (C1, DQ, DM, DQ)),
               w.s([sbd2], 'rspcev', '( ( %s e. %s /\\ x = ( %s x. Q ) ) -> E. d e. %s x = ( d x. Q ) )' % (DQ, DM, DQ, DM))], 'syl',
              '( %s -> E. d e. %s x = ( d x. Q ) )' % (C1, DM))
    xex = w.s([c1(xn, 'x e. NN')], 'elexd', '( %s -> x e. _V )' % C1)
    inrn = w.s([rex, w.s([xex, w.inst('mulimel')], 'syl',
                         '( %s -> ( x e. ran %s <-> E. d e. %s x = ( d x. Q ) ) )' % (C1, FMP, DM))], 'mpbird',
               '( %s -> x e. ran %s )' % (C1, FMP))
    g1 = w.s([inrn], 'olcd', '( %s -> ( x e. %s \\/ x e. ran %s ) )' % (C1, DM, FMP))
    g1b = w.s([g1, w.s([w.s([], 'elun', '( x e. %s <-> ( x e. %s \\/ x e. ran %s ) )' % (RHS, DM, FMP))], 'a1i',
                       '( %s -> ( x e. %s <-> ( x e. %s \\/ x e. ran %s ) ) )' % (C1, RHS, DM, FMP))], 'mpbird',
              '( %s -> x e. %s )' % (C1, RHS))
    #   case -. Q || x
    C2 = '( %s /\\ -. Q || x )' % B
    c2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C2, f))
    gcd1 = w.s([w.s([w.s([c2(b(qp, 'Q e. Prime'), 'Q e. Prime'), c2(xzb, 'x e. ZZ')], 'jca',
                         '( %s -> ( Q e. Prime /\\ x e. ZZ ) )' % C2), w.inst('coprm')], 'syl',
                    '( %s -> ( -. Q || x <-> ( Q gcd x ) = 1 ) )' % C2),
                w.s([], 'simpr', '( %s -> -. Q || x )' % C2)], 'mpbid', '( %s -> ( Q gcd x ) = 1 )' % C2)
    gcd2 = w.s([w.s([w.s([c2(xzb, 'x e. ZZ'), c2(b(qz, 'Q e. ZZ'), 'Q e. ZZ')], 'jca',
                         '( %s -> ( x e. ZZ /\\ Q e. ZZ ) )' % C2), w.inst('gcdcom')], 'syl',
                    '( %s -> ( x gcd Q ) = ( Q gcd x ) )' % C2), gcd1], 'eqtrd', '( %s -> ( x gcd Q ) = 1 )' % C2)
    cop = w.s([w.s([w.s([c2(xzb, 'x e. ZZ'), c2(b(qz, 'Q e. ZZ'), 'Q e. ZZ'), c2(b(mz, 'M e. ZZ'), 'M e. ZZ')], '3jca',
                        '( %s -> ( x e. ZZ /\\ Q e. ZZ /\\ M e. ZZ ) )' % C2), w.inst('coprmdvds')], 'syl',
                   '( %s -> ( ( x || %s /\\ ( x gcd Q ) = 1 ) -> x || M ) )' % (C2, QM)),
               w.s([c2(xd, 'x || %s' % QM), gcd2], 'jca', '( %s -> ( x || %s /\\ ( x gcd Q ) = 1 ) )' % (C2, QM))], 'mpd',
              '( %s -> x || M )' % C2)
    g2 = w.s([w.s([w.s([c2(xn, 'x e. NN'), cop], 'jca', '( %s -> ( x e. NN /\\ x || M ) )' % C2),
                   dsel(w, C2, 'M', c2(b(mm, 'M e. NN'), 'M e. NN'), 'x', c2(xzb, 'x e. ZZ'))], 'mpbird',
                  '( %s -> x e. %s )' % (C2, DM))], 'orcd', '( %s -> ( x e. %s \\/ x e. ran %s ) )' % (C2, DM, FMP))
    g2b = w.s([g2, w.s([w.s([], 'elun', '( x e. %s <-> ( x e. %s \\/ x e. ran %s ) )' % (RHS, DM, FMP))], 'a1i',
                       '( %s -> ( x e. %s <-> ( x e. %s \\/ x e. ran %s ) ) )' % (C2, RHS, DM, FMP))], 'mpbird',
              '( %s -> x e. %s )' % (C2, RHS))
    ss1 = w.s([w.s([w.s([g1b, g2b], 'pm2.61dan', '( %s -> x e. %s )' % (B, RHS))], 'ex',
                   '( %s -> ( x e. %s -> x e. %s ) )' % (A, DQM, RHS))], 'ssrdv', '( %s -> %s C_ %s )' % (A, DQM, RHS))
    # ------------------------------------------------- RHS C_ LHS
    D = '( %s /\\ x e. %s )' % (A, RHS)
    d = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D, f))
    dis = w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (D, RHS)),
               w.s([w.s([], 'elun', '( x e. %s <-> ( x e. %s \\/ x e. ran %s ) )' % (RHS, DM, FMP))], 'a1i',
                   '( %s -> ( x e. %s <-> ( x e. %s \\/ x e. ran %s ) ) )' % (D, RHS, DM, FMP))], 'mpbid',
              '( %s -> ( x e. %s \\/ x e. ran %s ) )' % (D, DM, FMP))
    #   left: x | M
    E1 = '( %s /\\ x e. %s )' % (D, DM)
    e1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E1, f))
    sbm = w.s([], 'breq1', '( m = x -> ( m || M <-> x || M ) )')
    erm = w.s([w.s([sbm], 'elrab', '( x e. %s <-> ( x e. ( 1 ... M ) /\\ x || M ) )' % DM)], 'a1i',
              '( %s -> ( x e. %s <-> ( x e. ( 1 ... M ) /\\ x || M ) ) )' % (E1, DM))
    xz1 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (E1, DM)), erm], 'mpbid',
                        '( %s -> ( x e. ( 1 ... M ) /\\ x || M ) )' % E1)], 'simpld', '( %s -> x e. ( 1 ... M ) )' % E1),
               w.inst('elfzelz')], 'syl', '( %s -> x e. ZZ )' % E1)
    selm = dsel(w, E1, 'M', e1(d(mm, 'M e. NN'), 'M e. NN'), 'x', xz1)
    xnd1 = w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (E1, DM)), selm], 'mpbid',
               '( %s -> ( x e. NN /\\ x || M ) )' % E1)
    mdq = w.s([w.s([e1(d(qz, 'Q e. ZZ'), 'Q e. ZZ'), e1(d(mz, 'M e. ZZ'), 'M e. ZZ')], 'jca',
                   '( %s -> ( Q e. ZZ /\\ M e. ZZ ) )' % E1), w.inst('dvdsmul2')], 'syl', '( %s -> M || %s )' % (E1, QM))
    xdq = w.s([w.s([w.s([xz1, e1(d(mz, 'M e. ZZ'), 'M e. ZZ'),
                         w.s([e1(d(qz, 'Q e. ZZ'), 'Q e. ZZ'), e1(d(mz, 'M e. ZZ'), 'M e. ZZ')], 'zmulcld',
                             '( %s -> %s e. ZZ )' % (E1, QM))], '3jca',
                        '( %s -> ( x e. ZZ /\\ M e. ZZ /\\ %s e. ZZ ) )' % (E1, QM)), w.inst('dvdstr')], 'syl',
                   '( %s -> ( ( x || M /\\ M || %s ) -> x || %s ) )' % (E1, QM, QM)),
               w.s([w.s([xnd1], 'simprd', '( %s -> x || M )' % E1), mdq], 'jca',
                   '( %s -> ( x || M /\\ M || %s ) )' % (E1, QM))], 'mpd', '( %s -> x || %s )' % (E1, QM))
    h1 = w.s([w.s([w.s([xnd1], 'simpld', '( %s -> x e. NN )' % E1), xdq], 'jca',
                  '( %s -> ( x e. NN /\\ x || %s ) )' % (E1, QM)),
              dsel(w, E1, QM, e1(d(qmn, '%s e. NN' % QM), '%s e. NN' % QM), 'x', xz1)], 'mpbird',
             '( %s -> x e. %s )' % (E1, DQM))
    #   right: x = ( y x. Q )
    idy = w.s([], 'oveq1', '( d = y -> ( d x. Q ) = ( y x. Q ) )')
    idy2 = w.s([idy], 'eqeq2d', '( d = y -> ( x = ( d x. Q ) <-> x = ( y x. Q ) ) )')
    cbv = w.s([idy2], 'cbvrexv', '( E. d e. %s x = ( d x. Q ) <-> E. y e. %s x = ( y x. Q ) )' % (DM, DM))
    E2 = '( %s /\\ x e. ran %s )' % (D, FMP)
    e2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E2, f))
    xex2 = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (E2, FMP))], 'elexd', '( %s -> x e. _V )' % E2)
    rex2 = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (E2, FMP)),
                w.s([xex2, w.inst('mulimel')], 'syl',
                    '( %s -> ( x e. ran %s <-> E. d e. %s x = ( d x. Q ) ) )' % (E2, FMP, DM))], 'mpbid',
               '( %s -> E. d e. %s x = ( d x. Q ) )' % (E2, DM))
    rex3 = w.s([rex2, w.s([cbv], 'a1i', '( %s -> ( E. d e. %s x = ( d x. Q ) <-> E. y e. %s x = ( y x. Q ) ) )' % (E2, DM, DM))],
               'mpbid', '( %s -> E. y e. %s x = ( y x. Q ) )' % (E2, DM))
    F2 = '( %s /\\ y e. %s )' % (E2, DM)
    f2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (F2, f))
    ery = w.s([w.s([], 'breq1', '( m = y -> ( m || M <-> y || M ) )')], 'elrab',
              '( y e. %s <-> ( y e. ( 1 ... M ) /\\ y || M ) )' % DM)
    yfz = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> y e. %s )' % (F2, DM)),
                         w.s([ery], 'a1i', '( %s -> ( y e. %s <-> ( y e. ( 1 ... M ) /\\ y || M ) ) )' % (F2, DM))], 'mpbid',
                        '( %s -> ( y e. ( 1 ... M ) /\\ y || M ) )' % F2)], 'simpld', '( %s -> y e. ( 1 ... M ) )' % F2),
               w.inst('elfzelz')], 'syl', '( %s -> y e. ZZ )' % F2)
    sely = dsel(w, F2, 'M', f2(e2(d(mm, 'M e. NN'), 'M e. NN'), 'M e. NN'), 'y', yfz)
    ynd = w.s([w.s([], 'simpr', '( %s -> y e. %s )' % (F2, DM)), sely], 'mpbid',
              '( %s -> ( y e. NN /\\ y || M ) )' % F2)
    G2 = '( %s /\\ x = ( y x. Q ) )' % F2
    g2f = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (G2, f))
    xyq = w.s([], 'simpr', '( %s -> x = ( y x. Q ) )' % G2)
    yqn = w.s([g2f(w.s([ynd], 'simpld', '( %s -> y e. NN )' % F2), 'y e. NN'),
               g2f(f2(e2(d(qn, 'Q e. NN'), 'Q e. NN'), 'Q e. NN'), 'Q e. NN')], 'nnmulcld',
              '( %s -> ( y x. Q ) e. NN )' % G2)
    xnn2 = w.s([xyq, yqn], 'eqeltrd', '( %s -> x e. NN )' % G2)
    dmc = w.s([w.s([w.s([g2f(yfz, 'y e. ZZ'), g2f(f2(e2(d(mz, 'M e. ZZ'), 'M e. ZZ'), 'M e. ZZ'), 'M e. ZZ'),
                         g2f(f2(e2(d(qz, 'Q e. ZZ'), 'Q e. ZZ'), 'Q e. ZZ'), 'Q e. ZZ')], '3jca',
                        '( %s -> ( y e. ZZ /\\ M e. ZZ /\\ Q e. ZZ ) )' % G2), w.inst('dvdsmulc')], 'syl',
                   '( %s -> ( y || M -> ( y x. Q ) || ( M x. Q ) ) )' % G2),
               g2f(w.s([ynd], 'simprd', '( %s -> y || M )' % F2), 'y || M')], 'mpd',
              '( %s -> ( y x. Q ) || ( M x. Q ) )' % G2)
    commg = w.s([w.s([g2f(f2(e2(d(mm, 'M e. NN'), 'M e. NN'), 'M e. NN'), 'M e. NN')], 'nncnd', '( %s -> M e. CC )' % G2),
                 w.s([g2f(f2(e2(d(qn, 'Q e. NN'), 'Q e. NN'), 'Q e. NN'), 'Q e. NN')], 'nncnd', '( %s -> Q e. CC )' % G2)],
                'mulcomd', '( %s -> ( M x. Q ) = %s )' % (G2, QM))
    xdq2 = w.s([w.s([xyq, dmc], 'eqbrtrd', '( %s -> x || ( M x. Q ) )' % G2), commg], 'breqtrd',
               '( %s -> x || %s )' % (G2, QM))
    h2 = w.s([w.s([xnn2, xdq2], 'jca', '( %s -> ( x e. NN /\\ x || %s ) )' % (G2, QM)),
              dsel(w, G2, QM, g2f(f2(e2(d(qmn, '%s e. NN' % QM), '%s e. NN' % QM), '%s e. NN' % QM), '%s e. NN' % QM),
                   'x', w.s([xnn2], 'nnzd', '( %s -> x e. ZZ )' % G2))], 'mpbird', '( %s -> x e. %s )' % (G2, DQM))
    h2b = w.s([rex3, w.s([w.s([h2], 'ex', '( %s -> ( x = ( y x. Q ) -> x e. %s ) )' % (F2, DQM))], 'rexlimdva',
                         '( %s -> ( E. y e. %s x = ( y x. Q ) -> x e. %s ) )' % (E2, DM, DQM))], 'mpd',
              '( %s -> x e. %s )' % (E2, DQM))
    ss2 = w.s([w.s([w.s([dis, w.s([h1], 'ex', '( %s -> ( x e. %s -> x e. %s ) )' % (D, DM, DQM)),
                         w.s([h2b], 'ex', '( %s -> ( x e. ran %s -> x e. %s ) )' % (D, FMP, DQM))], 'mpjaod',
                        '( %s -> x e. %s )' % (D, DQM))], 'ex', '( %s -> ( x e. %s -> x e. %s ) )' % (A, RHS, DQM))],
              'ssrdv', '( %s -> %s C_ %s )' % (A, RHS, DQM))
    w.qed([ss1, ss2], 'eqssd', '( %s -> %s = %s )' % (A, DQM, RHS))
    run(w)
