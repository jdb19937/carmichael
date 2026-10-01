"""Sortie V5, objective 2: carmsw, carmsalg's conclusion with its sieve-side
hypotheses .1-.10 discharged by smshw (the exponent, the density constant, the
threshold) and c1algex (C1), under carmsalg.11-.13 only.
MM_DB=sorties/v5.mm python3 tools/gen/v5_alg.py"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
import a5lib
import v5lib
from v5lib import mkst, lit, Proj, subst, HALF
import c0lib


def carmsw():
    w = W('carmsw', 'The algorithmic main theorem with the sieve side discharged: under the AGP hypotheses '
                    'carmsalg.11-.13 alone, there are C1 >= 1000 and a smoothness exponent t in ( 0 , 1 / 2 ] for '
                    'which carmsalg holds (Lean: carmichael_search_alg at Eweak, gammaWeak, x1Weak, C1weak).')
    hyps = v5lib.carmsalg_hyps()
    H = [None] + [w.s([], 'carmsw.%d' % i, hyps[10 + i - 1], name='h%d' % i) for i in (1, 2, 3)]
    H = [None, '1', '2', '3']
    DENS = v5lib.dens_text('t', 'g', 'w')
    DENSS = a5lib.subvars(DENS, {'q': 's'})
    PC = '( ; ; ; 1 0 0 0 <_ c /\\ ; 6 0 <_ ( c x. g ) )'
    A1 = '( ph /\\ t e. RR )'
    A2 = '( %s /\\ ( 0 < t /\\ t <_ %s ) )' % (A1, HALF)
    A3 = '( %s /\\ g e. RR )' % A2
    A4 = '( %s /\\ 0 < g )' % A3
    A5 = '( %s /\\ w e. NN0 )' % A4
    A6 = '( %s /\\ %s )' % (A5, DENSS)
    A7 = '( %s /\\ c e. RR )' % A6
    A8 = '( %s /\\ %s )' % (A7, PC)
    st = mkst(w, A8); pj = Proj(w, A8)
    # the closed renaming of the density statement's inner binder
    P = 'A. q e. Prime ( q || ( a - 1 ) -> q <_ ( x ^c ( 1 - t ) ) )'
    sl, _ = subst(w, 'q', 's', '( q || ( a - 1 ) -> q <_ ( x ^c ( 1 - t ) ) )')
    PS = a5lib.subvars(P, {'q': 's'})
    b1 = w.s([sl], 'cbvralvw', '( %s <-> %s )' % (P, PS))
    b2 = w.s([b1], 'anbi2i', '( ( a e. Prime /\\ %s ) <-> ( a e. Prime /\\ %s ) )' % (P, PS))
    SQ = '{ a e. ( 0 ... x ) | ( a e. Prime /\\ %s ) }' % P
    SS = '{ a e. ( 0 ... x ) | ( a e. Prime /\\ %s ) }' % PS
    b3 = w.s([b2], 'rabbii', '%s = %s' % (SQ, SS))
    b4 = w.s([b3], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (SQ, SS))
    b5 = w.s([b4], 'breq2i', '( ( g x. ( ppi ` x ) ) <_ ( # ` %s ) <-> ( g x. ( ppi ` x ) ) <_ ( # ` %s ) )' % (SQ, SS))
    b6 = w.s([b5], 'ralbii', '( %s <-> %s )' % (DENS, DENSS))
    assert DENS == 'A. x e. ( ZZ>= ` w ) ( g x. ( ppi ` x ) ) <_ ( # ` %s )' % SQ, DENS
    b7 = w.s([b6], 'rexbii', '( E. w e. NN0 %s <-> E. w e. NN0 %s )' % (DENS, DENSS))
    # carmsalg under A8
    c1 = pj('c e. RR'); c2 = pj('; ; ; 1 0 0 0 <_ c'); c3 = pj('t e. RR'); c4 = pj('0 < t'); c5 = pj('t <_ %s' % HALF)
    c6 = pj('g e. RR'); c7 = pj('0 < g'); c8 = pj('; 6 0 <_ ( c x. g )'); c9 = pj('w e. NN0')
    c10 = st([pj(DENSS), b6], 'sylibr', DENS)
    from cl import lift
    c11 = lift(w, H[1], A8); c12 = lift(w, H[2], A8); c13 = lift(w, H[3], A8)
    CONCL = a5lib.subvars(a5lib.split_imp(a5lib.dbstmt('carmsalg'))[1], {'C': 'c', 'E': 't'})
    alg = st([c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13], 'carmsalg', CONCL)
    BODY = '( ( ; ; ; 1 0 0 0 <_ c /\\ ( 0 < t /\\ t <_ %s ) ) /\\ %s )' % (HALF, CONCL)
    body = st([st([c2, st([c4, c5], 'jca', '( 0 < t /\\ t <_ %s )' % HALF)], 'jca', '( ; ; ; 1 0 0 0 <_ c /\\ ( 0 < t /\\ t <_ %s ) )' % HALF), alg], 'jca', BODY)
    ET = 'E. t e. RR %s' % BODY
    GOAL = 'E. c e. RR %s' % ET
    assert v5lib.carmsw_text() == '( ph -> %s )' % GOAL
    ext = st([c3, body, w.s([], 'rspe', '( ( t e. RR /\\ %s ) -> %s )' % (BODY, ET))], 'syl2anc', ET)
    exc = st([c1, ext, w.s([], 'rspe', '( ( c e. RR /\\ %s ) -> %s )' % (ET, GOAL))], 'syl2anc', GOAL)
    # eliminate c (bound in the goal: rexlimd with nfre1)
    i1 = w.s([exc], 'exp31', '( %s -> ( c e. RR -> ( %s -> %s ) ) )' % (A6, PC, GOAL))
    nfc1 = w.s([], 'nfv', 'F/ c %s' % A6)
    nfc2 = w.s([], 'nfre1', 'F/ c %s' % GOAL)
    r1 = w.s([nfc1, nfc2, i1], 'rexlimd', '( %s -> ( E. c e. RR %s -> %s ) )' % (A6, PC, GOAL))
    pj6 = Proj(w, A6)
    cex = w.s([w.s([pj6('g e. RR'), pj6('0 < g')], 'jca', '( %s -> ( g e. RR /\\ 0 < g ) )' % A6), w.inst('c1algex')], 'syl',
              '( %s -> E. c e. RR %s )' % (A6, PC))
    g6 = w.s([cex, r1], 'mpd', '( %s -> %s )' % (A6, GOAL))
    # eliminate the density statement and w
    i2 = w.s([g6], 'ex', '( %s -> ( %s -> %s ) )' % (A5, DENSS, GOAL))
    r2 = w.s([i2], 'rexlimdva', '( %s -> ( E. w e. NN0 %s -> %s ) )' % (A4, DENSS, GOAL))
    r2b = w.s([b7, r2], 'biimtrid', '( %s -> ( E. w e. NN0 %s -> %s ) )' % (A4, DENS, GOAL))
    # g
    i3 = w.s([r2b], 'ex', '( %s -> ( 0 < g -> ( E. w e. NN0 %s -> %s ) ) )' % (A3, DENS, GOAL))
    i3b = w.s([i3], 'impd', '( %s -> ( ( 0 < g /\\ E. w e. NN0 %s ) -> %s ) )' % (A3, DENS, GOAL))
    BG = '( 0 < g /\\ E. w e. NN0 %s )' % DENS
    r3 = w.s([i3b], 'rexlimdva', '( %s -> ( E. g e. RR %s -> %s ) )' % (A2, BG, GOAL))
    # t
    BT = '( ( 0 < t /\\ t <_ %s ) /\\ E. g e. RR %s )' % (HALF, BG)
    i4 = w.s([r3], 'ex', '( %s -> ( ( 0 < t /\\ t <_ %s ) -> ( E. g e. RR %s -> %s ) ) )' % (A1, HALF, BG, GOAL))
    i4b = w.s([i4], 'impd', '( %s -> ( %s -> %s ) )' % (A1, BT, GOAL))
    i4c = w.s([i4b], 'ex', '( ph -> ( t e. RR -> ( %s -> %s ) ) )' % (BT, GOAL))
    nft1 = w.s([], 'nfv', 'F/ t ph')
    nft2 = w.s([w.s([], 'nfcv', 'F/_ t RR'), w.s([], 'nfre1', 'F/ t %s' % ET)], 'nfrexw', 'F/ t %s' % GOAL)
    r4 = w.s([nft1, nft2, i4c], 'rexlimd', '( ph -> ( E. t e. RR %s -> %s ) )' % (BT, GOAL))
    assert v5lib.STATEMENTS['smshw'] == 'E. t e. RR %s' % BT
    w.qed([w.s([], 'smshw', 'E. t e. RR %s' % BT), r4], 'mpi', '( ph -> %s )' % GOAL)
    ok = c0lib.runh(w)
    assert ok, 'carmsw'


if __name__ == '__main__':
    carmsw()
