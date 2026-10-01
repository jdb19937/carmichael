"""T10: step2Pre at the machine (Lean ` step2Pre_runs ` ): the reservoir on stack 4, its length on 2, ` cmp := compare len T ` .

    MM_DB=sorties/t10.mm python3 tools/gen/t10_p_s2p.py tmis2p
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t10_e_doa import ex_, lift_from
from t10_n_rgf import tmbn
from t10_l_rga import RGX
import num

SEL = sys.argv[1:]
LM = FRAGS['s2p'].lmap()
RGZ = '( ( ( G ResGo Y ) ` 2 ) ` ( Z - 1 ) )'


def me_bound(w, ph, t, tn, tlt, bn, cl):
    """( ph -> ( ( 2 x. ( # ` ( encNatGam ` t ) ) ) + 4 ) <_ ( TMB ` B ) ) from t < 2 ^ B"""
    s = w.s
    WT = '( encNatGam ` %s )' % t
    LW = '( # ` %s )' % WT
    cl.leaf(LW, 'NN0', s([encw(w, ph, t, tn), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))
    lw = s([s([tn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` %s ) ) )' % (ph, LW, t)),
            s([tn, bn, tlt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` %s ) ) <_ B )' % (ph, t))],
           'eqbrtrd', '( %s -> %s <_ B )' % (ph, LW))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( B + 2 ) ^ 2 ) ) <_ ( TMB ` B ) )' % ph)
    return nlinarith(w, ph, [lw, qd, cl.ge0('B'), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ ( TMB ` B )' % LW, closure=cl,
                     atoms=['B', LW, '( TMB ` B )'])


def tmis2p():
    lab = 'tmis2p'
    T = numtree(TREE_S2P)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` step2Pre_runs ` at the machine: ` dup 0 3 5 ; moveEntry 0 1 5 ; moveEntry 0 1 5 ` set up ~ tmirsv , the '
               'drops leave ` T :: theta ` on stack 0 and ` z ` on 1, ` listLen 4 2 5 6 ` (~ tmillenb ) pushes the length and '
               '` cmpFrag 5 6 ` on copies compares it with ` T ` .')
    s = w.s
    c0 = Ctx(w, ph, T)
    znn, gn, ynn, un, on, bn = c0['Z e. NN'], c0['G e. NN0'], c0['Y e. NN'], c0['U e. NN0'], c0['O e. NN0'], c0['B e. NN0']
    zn = s([znn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    yn = s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph)
    rw_ = c0[WG('R')]
    EOR = EWg('O', 'R')
    gor = ewg_(w, ph, 'O', on, 'R', rw_)
    guo = ewg_(w, ph, 'U', un, EOR, gor)
    gyu = ewg_(w, ph, 'Y', yn, EWUO, guo)
    E1 = EWg('Y', EWUO)
    E2 = EWg('G', E1)
    ggy = ewg_(w, ph, 'G', gn, E1, gyu)
    E3 = EWg('Z', E2)
    eqs = {'0': (E3, ewg_(w, ph, 'Z', zn, E2, ggy))}
    B = Base(w, ph, T, N8, 's2p', eqs)
    c, mk = B.c, B.mk
    for t_, st_ in ((EOR, gor), (EWUO, guo), (E1, gyu), (E2, ggy)):
        B.g(t_, st_)
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    cl = Closure(w, ph, {'Z': ('NN', znn), 'G': ('NN0', gn), 'Y': ('NN', ynn), 'U': ('NN0', un), 'B': ('NN0', bn)})
    p2 = '( 2 ^ B )'
    # 1. dup 0 3 5
    EZ3 = EWg('Z', DK(3))
    B.call(R, 'tmidupb', {'K': '0', 'J': '3', 'I': '5', 'F': 'Z', 'N': 'B', 'X': E2, 'P': PL('P', 0), 'E': LM['Y2']},
           {'Z e. NN0': zn}, [('3', EZ3, B.g(EZ3, ewg_(w, ph, 'Z', zn, DK(3), g('3'))))])
    # 2. moveEntry 0 1 5 ; 3. moveEntry 0 1 5
    WZ, WG_ = '( encNatGam ` Z )', '( encNatGam ` G )'
    EZ1 = EWg('Z', DK(1))
    B.call(R, 'tmime', {'K': '0', 'J': '1', 'I': '5', 'W': WZ, 'X': E2, 'P': PL('P', 1), 'E': LM['Y3']},
           {WRD(WZ, BITS): engb(w, ph, 'Z', zn)}, [('0', E2, ggy), ('1', EZ1, B.g(EZ1, ewg_(w, ph, 'Z', zn, DK(1), g('1'))))])
    EG1 = EWg('G', EZ1)
    B.call(R, 'tmime', {'K': '0', 'J': '1', 'I': '5', 'W': WG_, 'X': E1, 'P': PL('P', 2), 'E': LM['Y4']},
           {WRD(WG_, BITS): engb(w, ph, 'G', gn)}, [('0', E1, gyu), ('1', EG1, B.g(EG1, ewg_(w, ph, 'G', gn, EZ1, B.gam[EZ1])))])
    # 4. reservoirF
    RSV = '( ( Z Reservoir G ) ` Y )'
    RL = '( 1st ` %s )' % RSV
    E4 = ENCL(RL, DK(4))
    rsc = s([s([s([znn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), ynn], 'jca', '( %s -> ( ( Z e. NN /\\ G e. NN0 ) /\\ Y e. NN ) )' % ph),
             w.inst('reservoircl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, RSV))
    rlw = s([rsc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RL))
    g4 = wgcat(w, ph, '( encList ` %s )' % RL, DK(4), s([rlw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, RL)), g('4'))
    B.call(R, 'tmirsv', {'X': EWUO, "X'": EZ1, 'Z"': DK(3), 'P': PL('P', 3), 'E': LM['Y5']},
           {WG(EWUO): guo, WG(EZ1): B.gam[EZ1], WG(DK(3)): g('3')}, [('3', DK(3), g('3')), ('4', E4, B.g(E4, g4))])
    # 5. dropNum 1 ; 6. dropNum 0
    cur, oa = R.normalize(['0', '2', '3', '4', '5', '6', '7', '1'])
    assert oa[-1][0] == '1', oa
    B.call(R, 'tmidropb', {'K': '1', 'F': 'G', 'N': 'B', 'X': EZ1, 'P': PL('P', 4), 'E': LM['Y6']}, {}, [('1', EZ1, B.gam[EZ1])],
           on=(R.at(oa[:-1]), oa[:-1]))
    cur, ob = R.normalize(['1', '2', '3', '4', '5', '6', '7', '0'])
    assert ob[-1][0] == '0', ob
    B.call(R, 'tmidropb', {'K': '0', 'F': 'Y', 'N': 'B', 'X': EWUO, 'P': PL('P', 5), 'E': LM['Y7']}, {'Y e. NN0': yn}, [('0', EWUO, guo)],
           on=(R.at(ob[:-1]), ob[:-1]))
    # 7. listLen 4 2 5 6
    LEN = '( # ` %s )' % RL
    rv = s([s([s([znn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), ynn], 'jca', '( %s -> ( ( Z e. NN /\\ G e. NN0 ) /\\ Y e. NN ) )' % ph),
            w.inst('reservoirval')], 'syl', '( %s -> %s = %s )' % (ph, RSV, RGZ))
    Z1 = '( Z - 1 )'
    z1n = s([znn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, Z1))
    rgl = s([s([s([gn, ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([closed(w, ph, '2nn', '2 e. NN'), z1n], 'jca',
                                                                                  '( %s -> ( 2 e. NN /\\ %s e. NN0 ) )' % (ph, Z1))],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( 2 e. NN /\\ %s e. NN0 ) ) )' % (ph, Z1)),
             w.inst('rgln')], 'syl', '( %s -> ( ( # ` ( 1st ` %s ) ) <_ %s /\\ %s <_ ( 2nd ` %s ) ) )' % (ph, RGZ, Z1, Z1, RGZ))
    l1 = s([s([s([rv], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, RL, RGZ))], 'fveq2d', '( %s -> %s = ( # ` ( 1st ` %s ) ) )' % (ph, LEN, RGZ)),
            s([rgl], 'simpld', '( %s -> ( # ` ( 1st ` %s ) ) <_ %s )' % (ph, RGZ, Z1))], 'eqbrtrd', '( %s -> %s <_ %s )' % (ph, LEN, Z1))
    RC = '( 2nd ` %s )' % RSV
    l2 = s([s([rgl], 'simprd', '( %s -> %s <_ ( 2nd ` %s ) )' % (ph, Z1, RGZ)), s([s([rv], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (ph, RC, RGZ))], 'eqcomd',
                                                                              '( %s -> ( 2nd ` %s ) = %s )' % (ph, RGZ, RC))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, Z1, RC))
    lenn = s([rlw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN))
    cl.leaf(LEN, 'NN0', lenn)
    rcn = s([rsc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, RC))
    cl.leaf(RC, 'NN0', rcn)
    cl.atom(p2)
    lenlt = linarith(w, ph, [l1, c['Z < ( 2 ^ B )']], '%s < %s' % (LEN, p2), closure=cl)
    # entries of the reservoir below 2 ^ B (~ resgomem at q = 2 , fuel = z - 1)
    pa = '( %s /\\ a e. ran %s )' % (ph, RL)
    ain0 = s([], 'simpr', '( %s -> a e. ran %s )' % (pa, RL))
    ain = s([ain0, s([lift_from(w, ph, pa, s([rv], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, RL, RGZ)))], 'rneqd',
                     '( %s -> ran %s = ran ( 1st ` %s ) )' % (pa, RL, RGZ))], 'eleqtrd', '( %s -> a e. ran ( 1st ` %s ) )' % (pa, RGZ))
    frn = s([s([lift_from(w, ph, pa, rlw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, RL, RL)), w.inst('frn')], 'syl',
            '( %s -> ran %s C_ NN0 )' % (pa, RL))
    ann = s([frn, ain0], 'sseldd', '( %s -> a e. NN0 )' % pa)
    gm = s([s([s([lift_from(w, ph, pa, gn), lift_from(w, ph, pa, ynn), closed(w, pa, '2nn', '2 e. NN')], '3jca',
                 '( %s -> ( G e. NN0 /\\ Y e. NN /\\ 2 e. NN ) )' % pa), s([lift_from(w, ph, pa, z1n), ann], 'jca', '( %s -> ( %s e. NN0 /\\ a e. NN0 ) )' % (pa, Z1))],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN /\\ 2 e. NN ) /\\ ( %s e. NN0 /\\ a e. NN0 ) ) )' % (pa, Z1)), w.inst('resgomem')], 'syl',
           '( %s -> ( a e. ran ( 1st ` %s ) <-> ( ( 2 <_ a /\\ a < ( 2 + %s ) ) /\\ ( G < a /\\ a e. Prime /\\ A. p e. Prime ( p || ( a - 1 ) -> p <_ Y ) ) ) ) )'
           % (pa, RGZ, Z1))
    gm2 = s([ain, gm], 'mpbid', '( %s -> ( ( 2 <_ a /\\ a < ( 2 + %s ) ) /\\ ( G < a /\\ a e. Prime /\\ A. p e. Prime ( p || ( a - 1 ) -> p <_ Y ) ) ) )' % (pa, Z1))
    alt = s([s([gm2], 'simpld', '( %s -> ( 2 <_ a /\\ a < ( 2 + %s ) ) )' % (pa, Z1))], 'simprd', '( %s -> a < ( 2 + %s ) )' % (pa, Z1))
    clp = Closure(w, pa, {'a': ('NN0', ann), 'Z': ('NN', lift_from(w, ph, pa, znn)), 'B': ('NN0', lift_from(w, ph, pa, bn))})
    e2z = lineq(w, pa, '( 2 + %s )' % Z1, '( Z + 1 )', closure=clp)
    alz = s([alt, e2z], 'breqtrd', '( %s -> a < ( Z + 1 ) )' % pa)
    alez = s([alz, s([ann, lift_from(w, ph, pa, zn), w.inst('nn0leltp1')], 'syl2anc', '( %s -> ( a <_ Z <-> a < ( Z + 1 ) ) )' % pa)], 'mpbird',
             '( %s -> a <_ Z )' % pa)
    a2 = linarith(w, pa, [alez, lift_from(w, ph, pa, c['Z < ( 2 ^ B )'])], 'a < %s' % p2, closure=clp)
    ral = s([a2], 'ralrimiva', '( %s -> A. a e. ran %s a < %s )' % (ph, RL, p2))
    EL2 = EWg(LEN, DK(2))
    B.call(R, 'tmillenb', {'K': '4', 'J': '2', 'I': '5', "I'": '6', 'L': RL, 'R': DK(4), 'P': PL('P', 6), 'E': LM['Y8']},
           {'%s e. Word NN0' % RL: rlw, 'A. a e. ran %s a < %s' % (RL, p2): ral, '%s < %s' % (LEN, p2): lenlt},
           [('2', EL2, B.g(EL2, ewg_(w, ph, LEN, lenn, DK(2), g('2'))))])
    # 8. dup 2 5 6 ; 9. dup 0 6 5 ; 10. cmpFrag 5 6
    EL5 = EWg(LEN, DK(5))
    B.call(R, 'tmidupb', {'K': '2', 'J': '5', 'I': '6', 'F': LEN, 'N': 'B', 'X': DK(2), 'P': PL('P', 7), 'E': LM['Y9']},
           {'%s e. NN0' % LEN: lenn, '%s < %s' % (LEN, p2): lenlt}, [('5', EL5, B.g(EL5, ewg_(w, ph, LEN, lenn, DK(5), g('5'))))])
    EU6 = EWg('U', DK(6))
    B.call(R, 'tmidupb', {'K': '0', 'J': '6', 'I': '5', 'F': 'U', 'N': 'B', 'X': EOR, 'P': PL('P', 8), 'E': LM['Y10']},
           {}, [('6', EU6, B.g(EU6, ewg_(w, ph, 'U', un, DK(6), g('6'))))])
    B.call(R, 'tmicmpb', {'K': '5', 'J': '6', 'F': LEN, 'G': 'U', 'N': 'B', 'X': DK(5), 'Y': DK(6), 'P': PL('P', 9), 'E': 'E'},
           {'%s e. NN0' % LEN: lenn, '%s < %s' % (LEN, p2): lenlt}, [('5', DK(5), g('5')), ('6', DK(6), g('6'))])
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the bound
    TB = '( TMB ` B )'
    X14 = '( TMB ` ( ( 4 x. B ) + ; 1 4 ) )'
    b14 = s([s([closed(w, ph, '4nn0', '4 e. NN0'), bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % ph),
             s([num.nn0(w, 14)], 'a1i', '( %s -> ; 1 4 e. NN0 )' % ph), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 4 ) e. NN0 )' % ph)
    tbn = tmbn(w, ph, 'B', bn)
    x14n = tmbn(w, ph, '( ( 4 x. B ) + ; 1 4 )', b14)
    cl.leaf(TB, 'NN0', tbn)
    mz = me_bound(w, ph, 'Z', zn, c['Z < ( 2 ^ B )'], bn, cl)
    mg = me_bound(w, ph, 'G', gn, c['G < ( 2 ^ B )'], bn, cl)
    cl.leaf(X14, 'NN0', x14n)
    m1 = s([bn, b14, linarith(w, ph, [cl.ge0('B')], 'B <_ ( ( 4 x. B ) + ; 1 4 )', closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, X14))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    q14 = s([b14, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
            '( %s -> ( 4 x. ( ( ( ( 4 x. B ) + ; 1 4 ) + 2 ) ^ 2 ) ) <_ %s )' % (ph, X14))
    x7 = nlinarith(w, ph, [q14, cl.ge0('B')], '7 <_ %s' % X14, closure=cl, atoms=['B', X14])
    lr = linarith(w, ph, [l1, l2], '%s <_ %s' % (LEN, RC), closure=cl)
    pr1 = s([cl.mem(LEN, 'RR'), cl.mem(RC, 'RR'), cl.mem(TB, 'RR'), cl.ge0(TB), lr], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, LEN, TB, RC, TB))
    pr2 = s([cl.mem(TB, 'RR'), cl.mem(X14, 'RR'), cl.mem(RC, 'RR'), cl.ge0(RC), m1], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, RC, TB, RC, X14))
    BND = '( ( %s + 2 ) x. ( ; 1 2 x. %s ) )' % (RC, X14)
    le = linarith(w, ph, [mz, mg, m1, x7, pr1, pr2], '%s <_ %s' % (n, BND), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
