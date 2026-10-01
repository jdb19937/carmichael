"""Sortie bt: bruntitex (Lean BrunTitchmarsh as brunTitchmarsh_holds proves it)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
import num
from btlib import STATEMENTS as S, C2E8, EXPK, Y0, Z2, RPOW, CNT, BND, body


def bruntitex():
    w = W('bruntitex', 'Brun-Titchmarsh for the progression 1 mod m with an existential '
          'threshold (Lean BrunTitchmarsh, proved as brunTitchmarsh_holds): from some t on, '
          'the primes up to y congruent to 1 mod m number at most 3 y / ( phi ( m ) log ( y / m ) ) '
          'for every m >_ 2 with m <_ y ^ ( 19 / 20 ).')
    s = w.s
    # the witness t := ( |^ ` ( exp ` 200000000 ) )
    kre = num.re_nat(w, 200000000)
    ere = s([kre, w.inst('reefcl')], 'ax-mp', '%s e. RR' % EXPK)
    epos = s([kre, w.inst('efgt0')], 'ax-mp', '0 < %s' % EXPK)
    tz = s([ere, w.inst('ceilcl')], 'ax-mp', '%s e. ZZ' % Y0)
    tre = s([tz, w.inst('zre')], 'ax-mp', '%s e. RR' % Y0)
    ele = s([ere, w.inst('ceilge')], 'ax-mp', '%s <_ %s' % (EXPK, Y0))
    e0 = s([s([], '0re', '0 e. RR'), ere, epos], 'ltleii', '0 <_ %s' % EXPK)
    lt3 = s([s([], '0re', '0 e. RR'), ere, tre], 'letri',
            '( ( 0 <_ %s /\\ %s <_ %s ) -> 0 <_ %s )' % (EXPK, EXPK, Y0, Y0))
    t0 = s([e0, ele, lt3], 'mp2an', '0 <_ %s' % Y0)
    tnn0 = s([tz, t0, s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (Y0, Y0, Y0))],
             'mpbir2an', '%s e. NN0' % Y0)
    # the matrix at t
    HYP = '( %s <_ y /\\ m <_ %s )' % (Y0, RPOW)
    VAR = '( y e. NN0 /\\ m e. %s )' % Z2
    AA = '( %s /\\ %s )' % (VAR, HYP)
    st = lambda hyps, ref, g: s(hyps, ref, '( %s -> %s )' % (AA, g))
    yn = st([], 'simpll', 'y e. NN0')
    mz = st([], 'simplr', 'm e. %s' % Z2)
    mr = st([], 'simprr', 'm <_ %s' % RPOW)
    ty = st([], 'simprl', '%s <_ y' % Y0)
    ey = st([st([ere], 'a1i', '%s e. RR' % EXPK), st([tre], 'a1i', '%s e. RR' % Y0),
             st([yn], 'nn0red', 'y e. RR'), st([ele], 'a1i', '%s <_ %s' % (EXPK, Y0)), ty],
            'letrd', '%s <_ y' % EXPK)
    bt = st([yn, mz, mr, ey, w.inst('bruntit')], 'syl22anc', '%s <_ %s' % (CNT, BND))
    ex = s([bt], 'ex', '( %s -> ( %s -> %s <_ %s ) )' % (VAR, HYP, CNT, BND))
    rg = s([ex], 'rgen2', body(Y0))
    # the substitution t = Y0
    EQ = 't = %s' % Y0
    b1 = s([], 'breq1', '( %s -> ( t <_ y <-> %s <_ y ) )' % (EQ, Y0))
    b2 = s([b1], 'anbi1d', '( %s -> ( ( t <_ y /\\ m <_ %s ) <-> %s ) )' % (EQ, RPOW, HYP))
    b3 = s([b2], 'imbi1d', '( %s -> ( ( ( t <_ y /\\ m <_ %s ) -> %s <_ %s ) <-> ( %s -> %s <_ %s ) ) )'
           % (EQ, RPOW, CNT, BND, HYP, CNT, BND))
    IN_T = 'A. m e. %s ( ( t <_ y /\\ m <_ %s ) -> %s <_ %s )' % (Z2, RPOW, CNT, BND)
    IN_Y = 'A. m e. %s ( %s -> %s <_ %s )' % (Z2, HYP, CNT, BND)
    b4 = s([b3], 'ralbidv', '( %s -> ( %s <-> %s ) )' % (EQ, IN_T, IN_Y))
    b5 = s([b4], 'ralbidv', '( %s -> ( %s <-> %s ) )' % (EQ, body('t'), body(Y0)))
    rs = s([b5], 'rspcev', '( ( %s e. NN0 /\\ %s ) -> %s )' % (Y0, body(Y0), S['bruntitex']))
    w.qed([tnn0, rg, rs], 'mp2an', S['bruntitex'])
    return w


ALL = {'bruntitex': bruntitex}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
