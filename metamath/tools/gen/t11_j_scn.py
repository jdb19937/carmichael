"""T11: Lean's ` scanNext ` (Steps23.lean 1883) on TMIscn: ` incr 2 5 ; moveEntry 1 7 5 ; predNum 1 5 ; isZero 1 5 ;
moveEntry 7 1 5 ; load' ( carry := !flag , flag := false ) ` .

  tmiscn   scanNext_runs: ` k := k + 1 ` , ` fuel := fuel - 1 ` , ` carry := ( fuel - 1 =/= 0 ) ` , ` flag := false `

    MM_DB=sorties/t11.mm python3 tools/gen/t11_j_scn.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, lineq
from t10_e_doa import lift_from
from t10_u_s2s import expose, me_bound_n
import t8alib as A8
import t11_i_clso as CO

SEL = sys.argv[1:]
H1 = '( H + 1 )'
DATA_SCN = ((STKD('D'), ('Z e. NN0', 'G e. NN0', 'H e. NN0'), ('B e. NN0', LT2('Z'), (LT2('( G + 1 )'), LT2(H1)))),
            (WG("X'"), WG('Y')), (DEQ(1, EWg('Z', EWg(H1, "X'"))), DEQ(2, EWg('G', 'Y'))))
TREE_SCN = TREE0('scn', DATA_SCN)
VCAR = 'if ( H = 0 , (/) , 1o )'
NCF = '{ h e. TMSt | ( ( TMcar ` h ) = %s /\\ ( TMfl ` h ) = (/) ) }' % VCAR
CONCL_SCN = TRI(CS('scn'), CLN('E', NCF, UPS('D', ('1', EWg('Z', EWg('H', "X'"))), ('2', EWg('( G + 1 )', 'Y')))), '( ( 5 x. ( TMB ` B ) ) + 1 )')
add11('tmiscn', TREE_SCN, CONCL_SCN)
ORDER11.remove('tmiscn'); ORDER11.insert(ORDER11.index('tmisct'), 'tmiscn')
NO = lambda v: '{ h e. TMSt | ( TMfl ` h ) = %s }' % v


def tmiscn():
    lab = 'tmiscn'
    T = numtree11(TREE_SCN)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scanNext_runs ` at the machine: ` incr 2 5 ` (~ tmiincbs ), ` moveEntry 1 7 5 ` (~ tmime ), '
               '` predNum 1 5 ` (~ tmiprdbs ), ` isZero 1 5 ` (~ tmiizbs ), ` moveEntry 7 1 5 ` keeping the flag (~ tmimebo ) and '
               '` load\' ( carry := !flag , flag := false ) ` : ` k ` one up, the fuel one down, the carry ` fuel - 1 =/= 0 ` , '
               'the flag false, within ` 5 B b + 1 ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    zn, gn, hn = c0['Z e. NN0'], c0['G e. NN0'], c0['H e. NN0']
    xw, yw = c0[WG("X'")], c0[WG('Y')]
    h1n = s([hn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, H1))
    E1 = EWg('Z', EWg(H1, "X'"))
    e1g = ewg_(w, ph, 'Z', zn, EWg(H1, "X'"), ewg_(w, ph, H1, h1n, "X'", xw))
    B = Base(w, ph, T, N8, 'scn', {'1': (E1, e1g), '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', yw))})
    c, mk = B.c, B.mk
    bn = c['B e. NN0']
    cl = Closure(w, ph, {'Z': ('NN0', zn), 'G': ('NN0', gn), 'H': ('NN0', hn), 'B': ('NN0', bn)})
    TB_ = '( TMB ` B )'
    cl.leaf(TB_, 'NN0', s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB_)))
    lm = FRAGS['scn'].lmap()
    R = B.run()
    p2 = '( 2 ^ B )'
    glt = linarith(w, ph, [c[LT2('( G + 1 )')]], 'G < %s' % p2, closure=cl)
    G1 = '( G + 1 )'
    g1n = s([gn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, G1))
    E2 = EWg(G1, 'Y')
    B.call(R, 'tmiincbs', {'K': '2', 'J': '5', 'F': 'G', 'N': 'B', 'X': 'Y', 'P': PL('P', 1), 'E': lm['Y2']},
           {'G e. NN0': gn, 'B e. NN0': bn, 'G < %s' % p2: glt}, [('2', E2, B.g(E2, ewg_(w, ph, G1, g1n, 'Y', yw)))])
    WZ = '( encNatGam ` Z )'
    E7 = EWg('Z', DK(7))
    B.call(R, 'tmime', {'K': '1', 'J': '7', 'I': '5', 'W': WZ, 'X': EWg(H1, "X'"), 'P': PL('P', 2), 'E': lm['Y3']},
           {WRD(WZ, BITS): engb(w, ph, 'Z', zn)}, [('1', EWg(H1, "X'"), B.gam[EWg(H1, "X'")] if EWg(H1, "X'") in B.gam else
                                                    B.g(EWg(H1, "X'"), ewg_(w, ph, H1, h1n, "X'", xw))),
                                                   ('7', E7, B.g(E7, ewg_(w, ph, 'Z', zn, DK(7), B.S0.vals['7'][2])))])
    hnn = s([hn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (ph, H1))
    HM = '( %s - 1 )' % H1
    ex_ = s([s([hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('pncan1')], 'syl', '( %s -> %s = H )' % (ph, HM))
    B.call(R, 'tmiprdbs', {'K': '1', 'J': '5', 'F': H1, 'N': 'B', 'X': "X'", 'P': PL('P', 3), 'E': lm['Y4']},
           {'%s e. NN' % H1: hnn, 'B e. NN0': bn, '%s < %s' % (H1, p2): c[LT2(H1)]},
           [('1', EWg(HM, "X'"), B.g(EWg(HM, "X'"), ewg_(w, ph, HM, s([ex_, hn], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, HM)), "X'", xw)))],
           )
    # rewrite ( H + 1 ) - 1 = H in the current stacks
    Dc = triple_D(R.cur)
    rw_, Dn = w.rewrite(Dc, {HM: ('H', ex_)}, ph)
    head = R.cur[:-len(' X. { %s } ) )' % Dc)]
    lab0 = head.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
    ncls = head.split(' } X. ( ', 1)[1]
    R.tri, _, R.cur, _ = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, lab0, ncls, rw_, Dc, Dn))
    EH = EWg('H', "X'")
    R.chain[-1] = ('1', EH)
    hlt = linarith(w, ph, [c[LT2(H1)]], 'H < %s' % p2, closure=cl)
    V = 'if ( H = 0 , 1o , (/) )'
    B.g(EH, ewg_(w, ph, 'H', hn, "X'", xw))
    R.gam.update(B.gam)
    R.S = R.at(R.chain)
    B.call(R, 'tmiizbs', {'K': '1', 'I': '5', 'F': 'H', 'N': 'B', 'X': "X'", 'P': PL('P', 4), 'E': lm['Y5']},
           {'H e. NN0': hn, 'B e. NN0': bn, 'H < %s' % p2: hlt}, [])
    E1n = EWg('Z', EH)
    B.call(R, 'tmimebo', {'K': '7', 'J': '1', 'I': '5', 'F': 'Z', 'N': 'B', 'X': DK(7), 'O': V, 'P': PL('P', 5), 'E': lm['Z1']},
           {'Z e. NN0': zn, 'B e. NN0': bn, LT2('Z'): c[LT2('Z')]},
           [('7', DK(7), B.S0.vals['7'][2]), ('1', E1n, B.g(E1n, ewg_(w, ph, 'Z', zn, EH, B.gam[EH])))])
    # the load
    kw = lambda t: {'car': 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t, 'fl': '(/)'}
    LTX = LSET(car=NOTFL, fl='(/)')
    assert LTX == L_CNF
    pr = '( %s /\\ r e. %s )' % (ph, NO(V))
    rr, fr = A8.nfl_unpack(w, pr, V, 'r', s([], 'simpr', '( %s -> r e. %s )' % (pr, NO(V))))
    nv = lset_val2(w, pr, kw, 'r', rr)
    NR = '( %s ` r )' % L_CNF
    cif = s([s([s([fr], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (pr, V)),
                s([s([], 'tmcif1', '( %s = 1o <-> H = 0 )' % V)], 'a1i', '( %s -> ( %s = 1o <-> H = 0 ) )' % (pr, V))], 'bitrd',
               '( %s -> ( ( TMfl ` r ) = 1o <-> H = 0 ) )' % pr)], 'ifbid', '( %s -> if ( ( TMfl ` r ) = 1o , (/) , 1o ) = %s )' % (pr, VCAR))
    ca = s([nv['fields']['car'], cif], 'eqtrd', '( %s -> ( TMcar ` %s ) = %s )' % (pr, NR, VCAR))
    fl = nv['fields']['fl']
    cond = lambda t: '( ( TMcar ` %s ) = %s /\\ ( TMfl ` %s ) = (/) )' % (t, VCAR, t)
    from t7lib import rab_in
    inm = rab_in(w, pr, NCF, cond, NR, nv['mem'], s([ca, fl], 'jca', '( %s -> %s )' % (pr, cond(NR))))
    lin_ = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, NO(V), L_CNF, NCF))
    ex3 = {LTY(L_CNF): lset_ty2(w, ph, mk, L_CNF, kw), SSS(NO(V)): B.ss(NO(V)), SSS(NCF): B.ss(NCF),
           'A. r e. %s ( %s ` r ) e. %s' % (NO(V), L_CNF, NCF): lin_}
    B.call(R, 'tm2flg', {'A': lm['Z1'], 'E': 'E', 'F': L_CNF, 'N': NO(V), "N'": NCF}, ex3, [])
    cur, out = R.normalize(N8)
    assert out == [('1', E1n), ('2', E2)], out
    # the bound
    mb = me_bound_n(w, ph, 'Z', zn, c[LT2('Z')], 'B', bn, cl)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    BND = '( ( 5 x. %s ) + 1 )' % TB_
    LWZ = '( # ` %s )' % WZ
    le = linarith(w, ph, [mb], '%s <_ %s' % (n, BND), closure=cl, atoms=[TB_, LWZ])
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
