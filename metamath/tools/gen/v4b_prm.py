"""Sortie v4b block 1: the sifting primes.

progtfi  ( PH -> ( T e. Fin /\\ T C_ Prime ) )
progpnn  ( PH -> ( ( P e. NN /\\ ( mmu ` P ) =/= 0 ) /\\ { q e. Prime | q || P } = T ) )
progpel  ( ( PH /\\ Q e. Prime ) -> ( Q || P <-> ( Q <_ Z /\\ -. Q || M ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import T, P, PH, mkst

PH2 = '( %s /\\ Q e. Prime )' % PH
PRED = lambda v: '( %s e. Prime /\\ -. %s || M )' % (v, v)


def telrab(w, v):
    """the elrab biconditional ( v e. T <-> ( v e. ( 0 ... Z ) /\\ PRED( v ) ) )"""
    h1 = w.s([], 'eleq1', '( u = %s -> ( u e. Prime <-> %s e. Prime ) )' % (v, v))
    h2 = w.s([], 'breq1', '( u = %s -> ( u || M <-> %s || M ) )' % (v, v))
    h3 = w.s([h2], 'notbid', '( u = %s -> ( -. u || M <-> -. %s || M ) )' % (v, v))
    h4 = w.s([h1, h3], 'anbi12d', '( u = %s -> ( %s <-> %s ) )' % (v, PRED('u'), PRED(v)))
    return w.s([h4], 'elrab', '( %s e. %s <-> ( %s e. ( 0 ... Z ) /\\ %s ) )'
               % (v, T, v, PRED(v)))


def progtfi():
    w = W('progtfi', 'The sifting primes of the progression sieve form a finite set of '
                     'primes.')
    st = mkst(w, PH)
    fin = st([], 'fzfid', '( 0 ... Z ) e. Fin')
    ss = st([w.s([], 'ssrab2', '%s C_ ( 0 ... Z )' % T)], 'a1i', '%s C_ ( 0 ... Z )' % T)
    tf = st([fin, ss], 'ssfid', '%s e. Fin' % T)
    el = telrab(w, 'w')
    im = w.s([el], 'biimpi', '( w e. %s -> ( w e. ( 0 ... Z ) /\\ %s ) )' % (T, PRED('w')))
    pr = w.s([im], 'simprld', '( w e. %s -> w e. Prime )' % T)
    sp = w.s([pr], 'ssriv', '%s C_ Prime' % T)
    sp2 = st([sp], 'a1i', '%s C_ Prime' % T)
    w.qed([tf, sp2], 'jca', '( %s -> ( %s e. Fin /\\ %s C_ Prime ) )' % (PH, T, T))
    return w


def progpnn():
    w = W('progpnn', 'The sifting product of the progression sieve is a squarefree '
                     'positive integer whose prime divisors are the sifting primes.')
    st = mkst(w, PH)
    tf = st([], 'progtfi', '( %s e. Fin /\\ %s C_ Prime )' % (T, T))
    w.qed([tf, w.inst('sqfprod')], 'syl',
          '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s ) )'
          % (PH, P, P, P, T))
    return w


def progpel():
    w = W('progpel', 'A prime divides the sifting product exactly when it is at most the '
                     'sifting level and does not divide the modulus.')
    st = mkst(w, PH2)
    qp = st([], 'simpr', 'Q e. Prime')
    zn = st([], 'simpl2', 'Z e. NN')
    zn0 = st([zn], 'nnnn0d', 'Z e. NN0')
    qn = st([qp, w.inst('prmnn')], 'syl', 'Q e. NN')
    qn0 = st([qn], 'nnnn0d', 'Q e. NN0')
    # ( 1 )  Q || P <-> ( Q e. Prime /\\ Q || P )
    b1 = st([qp], 'biantrurd', '( Q || %s <-> ( Q e. Prime /\\ Q || %s ) )' % (P, P))
    # ( 2 )  ( Q e. Prime /\\ Q || P ) <-> Q e. { q e. Prime | q || P }
    hb = w.s([], 'breq1', '( q = Q -> ( q || %s <-> Q || %s ) )' % (P, P))
    e1 = w.s([hb], 'elrab', '( Q e. { q e. Prime | q || %s } <-> ( Q e. Prime /\\ Q || %s ) )'
             % (P, P))
    e1d = st([e1], 'a1i', '( Q e. { q e. Prime | q || %s } <-> ( Q e. Prime /\\ Q || %s ) )'
             % (P, P))
    b2 = st([e1d], 'bicomd', '( ( Q e. Prime /\\ Q || %s ) <-> Q e. { q e. Prime | q || %s } )'
            % (P, P))
    # ( 3 )  the set equality
    ph_ = st([], 'simpl', PH)
    pn = w.s([ph_, w.inst('progpnn')], 'syl',
             '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s ) )'
             % (PH2, P, P, P, T))
    eq = st([pn], 'simprd', '{ q e. Prime | q || %s } = %s' % (P, T))
    b3 = st([eq], 'eleq2d', '( Q e. { q e. Prime | q || %s } <-> Q e. %s )' % (P, T))
    # ( 4 )  Q e. T
    b4 = st([telrab(w, 'Q')], 'a1i',
            '( Q e. %s <-> ( Q e. ( 0 ... Z ) /\\ %s ) )' % (T, PRED('Q')))
    # ( 5 )  the range and the prime conjunct
    fz = w.s([], 'elfz2nn0', '( Q e. ( 0 ... Z ) <-> ( Q e. NN0 /\\ Z e. NN0 /\\ Q <_ Z ) )')
    fzi = w.s([fz], 'biimpi',
              '( Q e. ( 0 ... Z ) -> ( Q e. NN0 /\\ Z e. NN0 /\\ Q <_ Z ) )')
    fwd0 = w.s([fzi], 'simp3d', '( Q e. ( 0 ... Z ) -> Q <_ Z )')
    fwd = w.s([fwd0], 'adantl', '( ( %s /\\ Q e. ( 0 ... Z ) ) -> Q <_ Z )' % PH2)
    qn0a = w.s([qn0], 'adantr', '( ( %s /\\ Q <_ Z ) -> Q e. NN0 )' % PH2)
    zn0a = w.s([zn0], 'adantr', '( ( %s /\\ Q <_ Z ) -> Z e. NN0 )' % PH2)
    lea = w.s([], 'simpr', '( ( %s /\\ Q <_ Z ) -> Q <_ Z )' % PH2)
    j3 = w.s([qn0a, zn0a, lea], '3jca',
             '( ( %s /\\ Q <_ Z ) -> ( Q e. NN0 /\\ Z e. NN0 /\\ Q <_ Z ) )' % PH2)
    fzr = w.s([fz], 'biimpri',
              '( ( Q e. NN0 /\\ Z e. NN0 /\\ Q <_ Z ) -> Q e. ( 0 ... Z ) )')
    bwd = w.s([j3, fzr], 'syl', '( ( %s /\\ Q <_ Z ) -> Q e. ( 0 ... Z ) )' % PH2)
    fzb = w.s([fwd, bwd], 'impbida', '( %s -> ( Q e. ( 0 ... Z ) <-> Q <_ Z ) )' % PH2)
    pb0 = st([qp], 'biantrurd', '( -. Q || M <-> ( Q e. Prime /\\ -. Q || M ) )')
    pb = st([pb0], 'bicomd', '( ( Q e. Prime /\\ -. Q || M ) <-> -. Q || M )')
    b5 = st([fzb, pb], 'anbi12d',
            '( ( Q e. ( 0 ... Z ) /\\ %s ) <-> ( Q <_ Z /\\ -. Q || M ) )' % PRED('Q'))
    t1 = st([b1, b2, b3], '3bitrd', '( Q || %s <-> Q e. %s )' % (P, T))
    w.qed([t1, b4, b5], '3bitrd',
          '( %s -> ( Q || %s <-> ( Q <_ Z /\\ -. Q || M ) ) )' % (PH2, P))
    return w


def main(names=None):
    fns = {'progtfi': progtfi, 'progpnn': progpnn, 'progpel': progpel}
    order = ['progtfi', 'progpnn', 'progpel']
    ok = True
    for nm in (names or order):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
