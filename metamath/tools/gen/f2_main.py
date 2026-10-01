"""Sortie F2: the four theorems (f2alpha, f2cw, f2rex, f2lgd) and stage B's worksheet
worksheets/carmtm.mmp (written, not added: `loggedDensity` is LDEN's).

    MM_DB=sorties/f2.mm MM_ENGINE=mmatch python3 tools/gen/f2_main.py LABEL   # generate + add
    python3 tools/gen/f2_main.py -w LABEL                                     # write the worksheet only
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from tm import W
import f2lib
from f2lib import S, CARMTM, MATA, MAT, MATP, PH, DS, DZ, DA, ren
from bmlib import ANTE, CONS, BOUND, PSET, DIV, CNT, XB, X1B, XH, PF, PCOND, F3160
from zdilib import LOGGED, LOGFREE

only = [a for a in sys.argv[1:] if not a.startswith('-')]
WRITE_ONLY = '-w' in sys.argv


def go(w):
    if only and w.label not in only:
        return True
    if WRITE_ONLY:
        print('wrote', w.write()); return True
    return w.run()


def gen_alpha():
    w = W('f2alpha', 'The AGP 3.1 matrix of carmsw.3 (` D := s ` , ` F := r ` ) with its bound ` k m q ` renamed ` g j o ` is the matrix: the closed alpha-equivalence that lets the matrix enter ~ carmtmw \'s antecedent under its ` $d ph e i k m n q ` .')
    l, x = 'l', 'x'
    # ANTE' <-> ANTE (o -> q)
    a1 = w.s([], 'breq1', '( o = q -> ( o || l <-> q || l ) )')
    a2 = w.s([], 'breq1', '( o = q -> ( o <_ %s <-> q <_ %s ) )' % (XH(x), XH(x)))
    a3 = w.s([a1, a2], 'imbi12d', '( o = q -> ( ( o || l -> o <_ %s ) <-> ( q || l -> q <_ %s ) ) )' % (XH(x), XH(x)))
    RALO = 'A. o e. Prime ( o || l -> o <_ %s )' % XH(x); RALQ = 'A. q e. Prime ( q || l -> q <_ %s )' % XH(x)
    a4 = w.s([a3], 'cbvralvw', '( %s <-> %s )' % (RALO, RALQ))
    a5 = w.s([], 'oveq2', '( o = q -> ( 1 / o ) = ( 1 / q ) )')
    PFL = '{ p e. Prime | p || l }'
    SUMO = 'sum_ o e. %s ( 1 / o )' % PFL; SUMQ = 'sum_ q e. %s ( 1 / q )' % PFL
    a6 = w.s([a5], 'cbvsumv', '%s = %s' % (SUMO, SUMQ))
    a7 = w.s([a6], 'breq1i', '( %s <_ %s <-> %s <_ %s )' % (SUMO, F3160, SUMQ, F3160))
    a8 = w.s([a4, a7], 'anbi12i', '( ( %s /\\ %s <_ %s ) <-> ( %s /\\ %s <_ %s ) )' % (RALO, SUMO, F3160, RALQ, SUMQ, F3160))
    ANTEQ = ANTE(DZ, x, l, F3160); ANTEO = ren(ANTEQ)
    a9 = w.s([a8], 'anbi2i', '( %s <-> %s )' % (ANTEO, ANTEQ))
    # CONS' <-> CONS'' (j -> m, closed) then CONS'' <-> CONS (g -> k)
    DIVJ = ren(DIV(l)); DIVM = DIV(l)
    b1 = w.s([], 'breq1', '( j = m -> ( j || l <-> m || l ) )')
    b2 = w.s([b1], 'cbvrabv', '%s = %s' % (DIVJ, DIVM))
    C1J = '{ d e. %s | d <_ %s }' % (DIVJ, XB(x)); C1M = '{ d e. %s | d <_ %s }' % (DIVM, XB(x))
    b3 = w.s([b2], 'rabeqi', '%s = %s' % (C1J, C1M))
    b4 = w.s([b3], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (C1J, C1M))
    BJ = ren(BOUND(DS, x, l)); BM = BOUND(DS, x, l)
    b5 = w.s([b4], 'oveq2i', '%s = %s' % (BJ, BM))
    PJ = ren(PSET(l, 'k', x)); PMG = PSET(l, 'g', x); PMK = PSET(l, 'k', x)
    b6 = w.s([b2], 'rabeqi', '%s = %s' % (PJ, PMG))
    b7 = w.s([b6], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (PJ, PMG))
    b8 = w.s([b5, b7], 'breq12i', '( %s <_ ( # ` %s ) <-> %s <_ ( # ` %s ) )' % (BJ, PJ, BM, PMG))
    GC = '( g <_ %s /\\ ( g gcd l ) = 1 )' % X1B(x); KC = '( k <_ %s /\\ ( k gcd l ) = 1 )' % X1B(x)
    BODYJ = '( %s /\\ %s <_ ( # ` %s ) )' % (GC, BJ, PJ)
    BODYG = '( %s /\\ %s <_ ( # ` %s ) )' % (GC, BM, PMG)
    BODYK = '( %s /\\ %s <_ ( # ` %s ) )' % (KC, BM, PMK)
    b9 = w.s([b8], 'anbi2i', '( %s <-> %s )' % (BODYJ, BODYG))
    CONSJ = 'E. g e. NN %s' % BODYJ; CONSG = 'E. g e. NN %s' % BODYG; CONSK = 'E. k e. NN %s' % BODYK
    assert CONSJ == ren(CONS(DS, x, l)) and CONSK == CONS(DS, x, l)
    b10 = w.s([b9], 'rexbii', '( %s <-> %s )' % (CONSJ, CONSG))
    c1 = w.s([], 'breq1', '( g = k -> ( g <_ %s <-> k <_ %s ) )' % (X1B(x), X1B(x)))
    c2 = w.s([], 'oveq1', '( g = k -> ( g gcd l ) = ( k gcd l ) )')
    c3 = w.s([c2], 'eqeq1d', '( g = k -> ( ( g gcd l ) = 1 <-> ( k gcd l ) = 1 ) )')
    c4 = w.s([c1, c3], 'anbi12d', '( g = k -> ( %s <-> %s ) )' % (GC, KC))
    c5 = w.s([], 'oveq2', '( g = k -> ( d x. g ) = ( d x. k ) )')
    c6 = w.s([c5], 'oveq1d', '( g = k -> ( ( d x. g ) + 1 ) = ( ( d x. k ) + 1 ) )')
    c7 = w.s([c6], 'breq1d', '( g = k -> ( ( ( d x. g ) + 1 ) <_ x <-> ( ( d x. k ) + 1 ) <_ x ) )')
    c8 = w.s([c6], 'eleq1d', '( g = k -> ( ( ( d x. g ) + 1 ) e. Prime <-> ( ( d x. k ) + 1 ) e. Prime ) )')
    c9 = w.s([c7, c8], 'anbi12d', '( g = k -> ( %s <-> %s ) )' % (PCOND('d', 'g', x), PCOND('d', 'k', x)))
    c10 = w.s([c9], 'rabbidv', '( g = k -> %s = %s )' % (PMG, PMK))
    c11 = w.s([c10], 'fveq2d', '( g = k -> ( # ` %s ) = ( # ` %s ) )' % (PMG, PMK))
    c12 = w.s([c11], 'breq2d', '( g = k -> ( %s <_ ( # ` %s ) <-> %s <_ ( # ` %s ) ) )' % (BM, PMG, BM, PMK))
    c13 = w.s([c4, c12], 'anbi12d', '( g = k -> ( %s <-> %s ) )' % (BODYG, BODYK))
    c14 = w.s([c13], 'cbvrexvw', '( %s <-> %s )' % (CONSG, CONSK))
    c15 = w.s([b10, c14], 'bitri', '( %s <-> %s )' % (CONSJ, CONSK))
    d1 = w.s([a9, c15], 'imbi12i', '( ( %s -> %s ) <-> ( %s -> %s ) )' % (ANTEO, CONSJ, ANTEQ, CONSK))
    w.qed([d1], '2ralbii', S['f2alpha'])
    return go(w)


def gen_cw():
    w = W('f2cw', '~ carmtmw at ` D := s ` , ` F := r ` with its antecedent ` ph ` the two memberships and the AGP 3.1 matrix (carmsw.3\'s, bound ` k m q ` renamed ` g j o ` for ` $d ph e i k m n q ` ): carmsw.1 by ~ simp1 + ~ nn0red , carmsw.2 by ~ simp2 , carmsw.3 by ~ simp3 and ~ f2alpha .')
    s1 = w.s([], 'simp1', '( %s -> %s e. NN0 )' % (PH, DS))
    s2 = w.s([s1], 'nn0red', '( %s -> %s e. RR )' % (PH, DS))
    s3 = w.s([], 'simp2', '( %s -> %s e. NN0 )' % (PH, DZ))
    s4 = w.s([], 'simp3', '( %s -> %s )' % (PH, MATP))
    s5 = w.s([], 'f2alpha', S['f2alpha'])
    s6 = w.s([s4, s5], 'sylib', '( %s -> %s )' % (PH, MAT))
    w.qed([s2, s3, s6], 'carmtmw', S['f2cw'])
    return go(w)


def gen_rex():
    w = W('f2rex', 'The main theorem from the AGP 3.1 pigeonhole statement in ~ bmpig21 \'s form: ~ f2cw exported, ~ f2alpha , ~ rexlimivv over ` s r ` , and the outer existential renamed ` a -> s ` (` a ` is bound in the conclusion).')
    AR = '( %s e. NN0 /\\ %s e. NN0 )' % (DS, DZ)
    s1 = w.s([], 'f2cw', S['f2cw'])
    s2 = w.s([s1], '3expia', '( %s -> ( %s -> %s ) )' % (AR, MATP, CARMTM))
    s3 = w.s([], 'f2alpha', S['f2alpha'])
    s4 = w.s([s3, s2], 'biimtrrid', '( %s -> ( %s -> %s ) )' % (AR, MAT, CARMTM))
    EXS = 'E. %s e. NN0 E. %s e. NN0 %s' % (DS, DZ, MAT); EXA = 'E. %s e. NN0 E. %s e. NN0 %s' % (DA, DZ, MATA)
    s5 = w.s([s4], 'rexlimivv', '( %s -> %s )' % (EXS, CARMTM))
    E = '( %s = %s -> ' % (DA, DS)
    t1 = w.s([], 'negeq', E + '-u a = -u s )')
    t2 = w.s([t1], 'oveq1d', E + '( -u a - 2 ) = ( -u s - 2 ) )')
    t3 = w.s([t2], 'oveq2d', E + '( 2 ^c ( -u a - 2 ) ) = ( 2 ^c ( -u s - 2 ) ) )')
    t4 = w.s([t3], 'oveq1d', E + '( ( 2 ^c ( -u a - 2 ) ) / ( log ` x ) ) = ( ( 2 ^c ( -u s - 2 ) ) / ( log ` x ) ) )')
    BA = BOUND(DA, 'x', 'l'); BS = BOUND(DS, 'x', 'l'); PK = '( # ` %s )' % PSET('l', 'k', 'x')
    t5 = w.s([t4], 'oveq1d', E + '%s = %s )' % (BA, BS))
    t6 = w.s([t5], 'breq1d', E + '( %s <_ %s <-> %s <_ %s ) )' % (BA, PK, BS, PK))
    KC = '( k <_ %s /\\ ( k gcd l ) = 1 )' % X1B('x')
    t7 = w.s([t6], 'anbi2d', E + '( ( %s /\\ %s <_ %s ) <-> ( %s /\\ %s <_ %s ) ) )' % (KC, BA, PK, KC, BS, PK))
    t8 = w.s([t7], 'rexbidv', E + '( %s <-> %s ) )' % (CONS(DA, 'x', 'l'), CONS(DS, 'x', 'l')))
    AN = ANTE(DZ, 'x', 'l', F3160)
    t9 = w.s([t8], 'imbi2d', E + '( ( %s -> %s ) <-> ( %s -> %s ) ) )' % (AN, CONS(DA, 'x', 'l'), AN, CONS(DS, 'x', 'l')))
    t10 = w.s([t9], '2ralbidv', E + '( %s <-> %s ) )' % (MATA, MAT))
    t11 = w.s([t10], 'rexbidv', E + '( E. %s e. NN0 %s <-> E. %s e. NN0 %s ) )' % (DZ, MATA, DZ, MAT))
    t12 = w.s([t11], 'cbvrexvw', '( %s <-> %s )' % (EXA, EXS))
    w.qed([t12, s5], 'sylbi', S['f2rex'])
    return go(w)


def gen_lgd():
    w = W('f2lgd', 'THE MAIN THEOREM CONDITIONAL ON THE LOGGED DENSITY ` LoggedDensity ` alone (M-FINAL stage A): ~ zd2lfl gives the log-free density, ~ bmpig21 the AGP 3.1 pigeonhole statement, ~ f2rex the machine theorem ` carmtm ` (the frozen text of scratch/carmtm.mmp). Stage B is one ~ ax-mp with LDEN\'s ` loggedDensity ` .')
    s1 = w.s([], 'zd2lfl', '( %s -> %s )' % (LOGGED, LOGFREE))
    s2 = w.s([s1], 'ancri', '( %s -> ( %s /\\ %s ) )' % (LOGGED, LOGFREE, LOGGED))
    EXA = 'E. %s e. NN0 E. %s e. NN0 %s' % (DA, DZ, MATA)
    s3 = w.s([], 'bmpig21', '( ( %s /\\ %s ) -> %s )' % (LOGFREE, LOGGED, EXA))
    s4 = w.s([s2, s3], 'syl', '( %s -> %s )' % (LOGGED, EXA))
    s5 = w.s([], 'f2rex', S['f2rex'])
    w.qed([s4, s5], 'syl', S['f2lgd'])
    return go(w)


def gen_carmtm():
    """stage B's worksheet: written only (loggedDensity is LDEN's label, not in the database yet)"""
    w = W('carmtm', 'THE MAIN THEOREM of carmichael.tex in the machine model (Mickey\'s theorem, no hypotheses; the frozen statement of sortie S): a TM2 machine computes, from ` n ` , a Carmichael number in ` ( n , n ^ ( 1 + e ) ] ` with its prime factorization, in time ` exp ( c log n log log n ) ` . ~ loggedDensity (the logged zero-density statement, Route Z) and ~ f2lgd (the machine layer under it).')
    h1 = w.s([], 'loggedDensity', LOGGED)
    h2 = w.s([], 'f2lgd', S['f2lgd'])
    w.qed([h1, h2], 'ax-mp', CARMTM)
    if not only or 'carmtm' in only:
        print('wrote', w.write())
    return True


if __name__ == '__main__':
    ok = True
    for g in (gen_alpha, gen_cw, gen_rex, gen_lgd, gen_carmtm):
        ok = g() and ok
        if not ok:
            break
    sys.exit(0 if ok else 1)
