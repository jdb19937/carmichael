"""T10: reservoirF at the machine (Lean ` reservoirF_runs ` ): ` predNum 3 6 ; pushNum 2 2 ; pushSym 5 bra ; resGoF ;
dropNum 2 ; dropNum 3 ` at width ` b + 1 ` (~ tmirgf , ~ reservoirval ).

    MM_DB=sorties/t10.mm python3 tools/gen/t10_o_rsv.py tmirsv
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t10_e_doa import ex_, lift_from
from t10_n_rgf import tmbn
import num

SEL = sys.argv[1:]
LM = FRAGS['rsv'].lmap()
B0_, B1_ = '<. 1 , (/) >.', '<. 1 , 1o >.'


def tmirsv():
    lab = 'tmirsv'
    T = numtree(TREE_RSV)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` reservoirF_runs ` at the machine: ` predNum 3 6 ` turns ` z ` into the fuel ` z - 1 ` , ` pushNum 2 2 ` and '
               '` pushSym 5 bra ` start ` resGoF ` (~ tmirgf at width ` b + 1 ` ), the two drops clean up; the reservoir '
               '` ( reservoir z z99 y ).1 ` (~ reservoirval ) is pushed on stack 4.')
    s = w.s
    c0 = Ctx(w, ph, T)
    znn, gn, ynn, bn = c0['Z e. NN'], c0['G e. NN0'], c0['Y e. NN'], c0['B e. NN0']
    yn = s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph)
    zn = s([znn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    eqs = {'0': (EWg('Y', 'X'), ewg_(w, ph, 'Y', yn, 'X', c0[WG('X')])), '1': (EWg('G', "X'"), ewg_(w, ph, 'G', gn, "X'", c0[WG("X'")])),
           '3': (EWg('Z', 'Z"'), ewg_(w, ph, 'Z', zn, 'Z"', c0[WG('Z"')]))}
    B = Base(w, ph, T, N8, 'rsv', eqs)
    c, mk = B.c, B.mk
    B.deep('rsv', 1)
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    Z1 = '( Z - 1 )'
    z1n = s([znn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, Z1))
    E3 = EWg(Z1, 'Z"')
    B.call(R, 'tmiprdbs', {'K': '3', 'J': '6', 'F': 'Z', 'N': 'B', 'X': 'Z"', 'P': PL('P', 4), 'E': LM['Z1']},
           {}, [('3', E3, B.g(E3, ewg_(w, ph, Z1, z1n, 'Z"', c0[WG('Z"')])))])
    # pushNum 2 2
    K2 = '( <" 4 "> ++ %s )' % DK(2)
    g2 = B.g(K2, wg4(w, ph, DK(2), g('2')))
    B.call(R, 'tm2fpshn', {'A': LM['Z1'], 'E': LM['Z2'], 'K': '2', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('2'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['2']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('2')))},
           [('2', K2, g2)])
    bg1 = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1_))
    bg0 = s([closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B0_))
    K21 = '( <" %s "> ++ %s )' % (B1_, K2)
    g21 = B.g(K21, wgcat(w, ph, '<" %s ">' % B1_, K2, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1_)), g2))
    B.call(R, 'tm2fpshn', {'A': LM['Z2'], 'E': LM['Z3'], 'K': '2', 'Z': B1_, 'N': S},
           {'%s e. %s' % (B1_, GX('2')): s([bg1, mk['k']['2']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1_, GX('2')))}, [('2', K21, g21)])
    K210 = '( <" %s "> ++ %s )' % (B0_, K21)
    g210 = B.g(K210, wgcat(w, ph, '<" %s ">' % B0_, K21, s([bg0], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B0_)), g21))
    B.call(R, 'tm2fpshn', {'A': LM['Z3'], 'E': LM['Z4'], 'K': '2', 'Z': B0_, 'N': S},
           {'%s e. %s' % (B0_, GX('2')): s([bg0, mk['k']['2']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B0_, GX('2')))}, [('2', K210, g210)])
    e2 = s([g('2'), w.inst('tmienc2')], 'syl', '( %s -> %s = %s )' % (ph, EWg('2', DK(2)), K210))
    # pushSym 5 bra
    K5 = '( <" 2 "> ++ %s )' % DK(5)
    g5 = B.g(K5, wgcat(w, ph, '<" 2 ">', DK(5), s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph), g('5')))
    B.call(R, 'tm2fpshn', {'A': LM['Z4'], 'E': LM['Y2'], 'K': '5', 'Z': '2', 'N': S},
           {'2 e. %s' % GX('5'): s([closed(w, ph, 'gamma2', "2 e. Gamma'"), mk['k']['5']['ge']], 'eleqtrrd', '( %s -> 2 e. %s )' % (ph, GX('5')))},
           [('5', K5, g5)])
    # resGoF at q = 2 , fuel = z - 1 , width b + 1
    B1 = '( B + 1 )'
    b1n = s([bn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, B1))
    p2, p21 = '( 2 ^ B )', '( 2 ^ %s )' % B1
    ex2 = s([closed(w, ph, '2cn', '2 e. CC'), bn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ph, p21, p2))
    cl = Closure(w, ph, {'Z': ('NN', znn), 'G': ('NN0', gn), 'Y': ('NN', ynn), 'B': ('NN0', bn)})
    cl.atom(p2)
    cl.atom(p21)
    b12 = linarith(w, ph, [c['2 <_ B']], '2 <_ %s' % B1, closure=cl)
    glt = linarith(w, ph, [c['G < ( 2 ^ B )'], ex2, cl.ge0('G')], 'G < %s' % p21, closure=cl)
    ylt = linarith(w, ph, [c['Y < ( 2 ^ B )'], ex2, cl.ge0('Y')], 'Y < %s' % p21, closure=cl)
    z1 = s([znn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ Z )' % ph)
    qlt = linarith(w, ph, [c['Z < ( 2 ^ B )'], ex2, z1], '( 2 + %s ) < %s' % (Z1, p21), closure=cl)
    RGZ = '( ( ( G ResGo Y ) ` 2 ) ` %s )' % Z1
    E4 = ENCL('( 1st ` %s )' % RGZ, DK(4))
    rgc = s([s([s([gn, ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), closed(w, ph, '2nn', '2 e. NN')], 'jca',
               '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ 2 e. NN ) )' % ph), z1n, w.inst('resgocl')], 'syl2anc', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, RGZ))
    lw = s([rgc, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` %s ) e. Word NN0 )' % (ph, RGZ))
    g4 = wgcat(w, ph, '( encList ` ( 1st ` %s ) )' % RGZ, DK(4), s([lw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` ( 1st ` %s ) ) e. Word Gamma' )" % (ph, RGZ)), g('4'))
    t2 = s([closed(w, ph, '2nn0', '2 e. NN0'), z1n, w.inst('nn0addcl')], 'syl2anc', '( %s -> ( 2 + %s ) e. NN0 )' % (ph, Z1))
    E2 = EWg('( 2 + %s )' % Z1, DK(2))
    E30 = EWg('0', 'Z"')
    B.call(R, 'tmirgf', {'Q': '2', 'H': Z1, 'B': B1, 'Z': DK(2), "Z'": 'Z"', 'R': DK(5), 'P': PL('P', 5), 'E': LM['Y3']},
           {'2 e. NN': closed(w, ph, '2nn', '2 e. NN'), '%s e. NN0' % Z1: z1n, '%s e. NN0' % B1: b1n, '2 <_ %s' % B1: b12,
            'G < %s' % p21: glt, 'Y < %s' % p21: ylt, '( 2 + %s ) < %s' % (Z1, p21): qlt,
            '( %s ` 2 ) = %s' % (R.S.D, EWg('2', DK(2))): s([R.S.vals['2'][1], s([e2], 'eqcomd', '( %s -> %s = %s )' % (ph, K210, EWg('2', DK(2))))],
                                                             'eqtrd', '( %s -> ( %s ` 2 ) = %s )' % (ph, R.S.D, EWg('2', DK(2)))),
            WG(DK(2)): g('2'), WG(DK(5)): g('5')},
           [('2', E2, B.g(E2, ewg_(w, ph, '( 2 + %s )' % Z1, t2, DK(2), g('2')))), ('3', E30, B.g(E30, ewg_(w, ph, '0', closed(w, ph, '0nn0', '0 e. NN0'), 'Z"', c0[WG('Z"')]))),
            ('4', E4, B.g(E4, g4)), ('5', DK(5), g('5'))])
    # dropNum 2 , dropNum 3
    cur, oa = R.normalize(['0', '1', '3', '4', '5', '6', '7', '2'])
    assert oa[-1][0] == '2', oa
    B.call(R, 'tmidropb', {'K': '2', 'F': '( 2 + %s )' % Z1, 'N': B1, 'X': DK(2), 'P': PL('P', 6), 'E': LM['Y4']},
           {'( 2 + %s ) e. NN0' % Z1: t2, '%s e. NN0' % B1: b1n, '( 2 + %s ) < %s' % (Z1, p21): qlt}, [('2', DK(2), g('2'))], on=(R.at(oa[:-1]), oa[:-1]))
    cur, ob = R.normalize(['0', '1', '2', '4', '5', '6', '7', '3'])
    assert ob[-1][0] == '3', ob
    zlt = linarith(w, ph, [c['Z < ( 2 ^ B )'], cl.ge0('Z')], '0 < %s' % p2, closure=cl)
    B.call(R, 'tmidropb', {'K': '3', 'F': '0', 'N': 'B', 'X': 'Z"', 'P': PL('P', 7), 'E': 'E'},
           {'0 e. NN0': closed(w, ph, '0nn0', '0 e. NN0'), '0 < %s' % p2: zlt}, [('3', 'Z"', c0[WG('Z"')])], on=(R.at(ob[:-1]), ob[:-1]))
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    RSV = '( ( Z Reservoir G ) ` Y )'
    rv = s([s([s([znn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), ynn], 'jca', '( %s -> ( ( Z e. NN /\\ G e. NN0 ) /\\ Y e. NN ) )' % ph),
            w.inst('reservoirval')], 'syl', '( %s -> %s = %s )' % (ph, RSV, RGZ))
    rve = s([rv], 'eqcomd', '( %s -> %s = %s )' % (ph, RGZ, RSV))
    Dc = triple_D(D)
    rf, xf = w.rewrite(Dc, {RGZ: (RSV, rve)}, ph)
    DF_ = UPS('D', ('3', 'Z"'), ('4', ENCL('( 1st ` %s )' % RSV, DK(4))))
    assert xf == DF_, (xf, DF_)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, rf, Dc, xf))
    # the bound
    TB, TB1 = '( TMB ` B )', '( TMB ` %s )' % B1
    X14 = '( TMB ` ( ( 4 x. B ) + ; 1 4 ) )'
    X10 = '( TMB ` ( ( 4 x. %s ) + ; 1 0 ) )' % B1
    e14 = lineq(w, ph, '( ( 4 x. %s ) + ; 1 0 )' % B1, '( ( 4 x. B ) + ; 1 4 )', closure=cl)
    ex14 = s([e14], 'fveq2d', '( %s -> %s = %s )' % (ph, X10, X14))
    b14 = s([s([closed(w, ph, '4nn0', '4 e. NN0'), bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % ph),
             s([num.nn0(w, 14)], 'a1i', '( %s -> ; 1 4 e. NN0 )' % ph), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 4 ) e. NN0 )' % ph)
    x14n = tmbn(w, ph, '( ( 4 x. B ) + ; 1 4 )', b14)
    tbn = tmbn(w, ph, 'B', bn)
    t1n = tmbn(w, ph, B1, b1n)
    for x_, st_ in ((TB, tbn), (TB1, t1n), (X14, x14n)):
        cl.leaf(x_, 'NN0', st_)
    m1 = s([bn, b14, linarith(w, ph, [cl.ge0('B')], 'B <_ ( ( 4 x. B ) + ; 1 4 )', closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, X14))
    m2 = s([b1n, b14, linarith(w, ph, [cl.ge0('B')], '%s <_ ( ( 4 x. B ) + ; 1 4 )' % B1, closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB1, X14))
    A2 = '( 2nd ` %s )' % RGZ
    A2R = '( 2nd ` %s )' % RSV
    a2 = s([rgc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, A2))
    cl.leaf(A2, 'NN0', a2)
    a2r = s([rv], 'fveq2d', '( %s -> %s = %s )' % (ph, A2R, A2))
    cl.leaf(A2R, 'NN0', s([a2r, a2], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, A2R)))
    BND = RSVB = '( ( ( %s + 1 ) x. ( ; 1 1 x. %s ) ) + ( ( 3 x. %s ) + 7 ) )' % (A2R, X14, X14)
    # the resGoF charge in n is ( ( A2 + 1 ) x. ( ; 1 1 x. X10 ) )
    PR = '( ( %s + 1 ) x. ( ; 1 1 x. %s ) )' % (A2, X10)
    pe = s([s([ex14], 'oveq2d', '( %s -> ( ; 1 1 x. %s ) = ( ; 1 1 x. %s ) )' % (ph, X10, X14))], 'oveq2d',
           '( %s -> %s = ( ( %s + 1 ) x. ( ; 1 1 x. %s ) ) )' % (ph, PR, A2, X14))
    pe2 = s([s([a2r], 'oveq1d', '( %s -> ( %s + 1 ) = ( %s + 1 ) )' % (ph, A2R, A2))], 'oveq1d',
            '( %s -> ( ( %s + 1 ) x. ( ; 1 1 x. %s ) ) = ( ( %s + 1 ) x. ( ; 1 1 x. %s ) ) )' % (ph, A2R, X14, A2, X14))
    PRX = '( ( %s + 1 ) x. ( ; 1 1 x. %s ) )' % (A2, X14)
    cl.leaf(PRX, 'NN0', s([s([a2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, A2)),
                           s([closed(w, ph, '11nn0', '; 1 1 e. NN0'), x14n, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( ; 1 1 x. %s ) e. NN0 )' % (ph, X14)),
                           w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, PRX)))
    cl.leaf(PR, 'NN0', s([pe, cl.mem(PRX, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, PR)))
    PRR = '( ( %s + 1 ) x. ( ; 1 1 x. %s ) )' % (A2R, X14)
    cl.leaf(PRR, 'NN0', s([pe2, cl.mem(PRX, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, PRR)))
    le = linarith(w, ph, [pe, pe2, m1, m2], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
