"""T9: Lean's ` extractF_le_B ` at the machine on TMIexf.

  tmiexfb   ` pushNum nm 1 ; pushSym nu bra ; dup nL t s ; emptyTbl t acc s ; extractGoF ... ` (~ tmidupb , ~ tmietbb ,
            ~ tmiexg at ` m = 1 ` , ` used = [] ` , the empty table bounded by ` 0 ` ), the budget
            ` ( ( extract ).2 + 1 ) 25 exY ` with ` X = exX # W b = 3 # W b + 5 b + 5 `

    MM_DB=sorties/t9.mm python3 tools/gen/t9_o_exf.py tmiexfb
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import num

SEL = sys.argv[1:]
LMF = FRAGS['exf'].lmap()
NW = '( # ` W )'
EGF = EGO('L', 'G', 'W', '1', '(/)', 'EmptyTbl')
OO = '( ( 1 + ( B x. %s ) ) + B )' % NW
EXYF = '( ( ( ( L + 1 ) ^ 2 ) x. ( %s + 2 ) ) x. ( TMB ` %s ) )' % (NW, EXX)


def tmiexfb():
    lab = 'tmiexfb'
    ph = cj(TREE_EXF)
    w = W(lab, 'Lean\'s ` extractF_le_B ` at the machine: wherever ` extractF np nL snap acc s t nm nu ` is installed, with '
               'the pool ` W ` on ` np ` (entries below ` 2 ^ b ` ), ` L ` on ` nL ` , ` n ` on ` nm ` and ` acc ` empty, the machine '
               'pushes ` m = 1 ` and ` used = [] ` , builds the empty table (~ tmidupb , ~ tmietbb ) and runs ` extractGoF ` '
               '(~ tmiexg at the table bound ` 0 ` , ` bm = 1 ` , ` bM = 1 + b # W + b ` , ` X = exX # W b ` ): the stacks hold '
               'the extraction state at its stop index, the flag says whether ` ( extract ).1 ` is ` some ` , within '
               '` ( ( extract ).2 + 1 ) 25 exY ` steps.')
    s = w.s
    c0 = Ctx(w, ph, TREE_EXF)
    ln, gn, ww, bn = c0['L e. NN'], c0['G e. NN0'], c0['W e. Word NN0'], c0['B e. NN0']
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    xw, x2w, yw = c0[WG('X')], c0[WG("X'")], c0[WG('Y')]
    egy = ewg_(w, ph, 'G', gn, 'Y', yw)
    eqs = {'K': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), 'J': (EWg('L', "X'"), ewg_(w, ph, 'L', l0, "X'", x2w)),
           "I'": ('(/)', closed(w, ph, 'wrd0', "(/) e. Word Gamma'"))}
    B = Base(w, ph, TREE_EXF, K8, 'exf', eqs)
    c, mk = B.c, B.mk
    R = B.run()
    # pushNum nm 1 ; pushSym nu bra
    K04 = '( <" 4 "> ++ ( D ` K0 ) )'
    g4 = B.g(K04, wg4(w, ph, '( D ` K0 )', B.S0.vals['K0'][2]))
    B.call(R, 'tm2fpshn', {'A': LMF['Q1'], 'E': LMF['Q2'], 'K': 'K0', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('K0'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['K0']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('K0')))},
           [('K0', K04, g4)])
    K041 = '( <" %s "> ++ %s )' % (B1, K04)
    bg = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1))
    g41 = B.g(K041, wgcat(w, ph, '<" %s ">' % B1, K04, s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1)), g4))
    B.call(R, 'tm2fpshn', {'A': LMF['Q2'], 'E': LMF['Q3'], 'K': 'K0', 'Z': B1, 'N': S},
           {'%s e. %s' % (B1, GX('K0')): s([bg, mk['k']['K0']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1, GX('K0')))},
           [('K0', K041, g41)])
    J02 = '( <" 2 "> ++ ( D ` J0 ) )'
    g2 = closed(w, ph, 'gamma2', "2 e. Gamma'")
    gj2 = B.g(J02, wgcat(w, ph, '<" 2 ">', '( D ` J0 )', s([g2], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph), B.S0.vals['J0'][2]))
    B.call(R, 'tm2fpshn', {'A': LMF['Q3'], 'E': LMF['X1'], 'K': 'J0', 'Z': '2', 'N': S},
           {"2 e. %s" % GX('J0'): s([g2, mk['k']['J0']['ge']], 'eleqtrrd', '( %s -> 2 e. %s )' % (ph, GX('J0')))},
           [('J0', J02, gj2)])
    # dup nL t s ; emptyTbl t acc s
    ELT = EWg('L', '( D ` I0 )')
    gl = B.g(ELT, ewg_(w, ph, 'L', l0, '( D ` I0 )', B.S0.vals['I0'][2]))
    B.call(R, 'tmidupb', {'K': 'J', 'J': 'I0', 'I': 'I"', 'F': 'L', 'N': 'B', 'X': "X'", 'P': PL('P', 3), 'E': LMF['X2']},
           {'L e. NN0': l0}, [('I0', ELT, gl)])
    ACE = CC('( L encTblAsc EmptyTbl )', '( <" 0 "> ++ (/) )')
    et = s([l0, w.inst('ttetb0')], 'syl', '( %s -> ( L encTblAsc EmptyTbl ) = ( 3 repeatS L ) )' % ph)
    g3 = closed(w, ph, 'gamma3', "3 e. Gamma'")
    rw_ = s([g3, l0, w.inst('repsw')], 'syl2anc', "( %s -> ( 3 repeatS L ) e. Word Gamma' )" % ph)
    etg = s([et, rw_], 'eqeltrd', "( %s -> ( L encTblAsc EmptyTbl ) e. Word Gamma' )" % ph)
    s0 = s([closed(w, ph, 'gamma0', "0 e. Gamma'")], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
    z0g = wgcat(w, ph, '<" 0 ">', '(/)', s0, closed(w, ph, 'wrd0', "(/) e. Word Gamma'"))
    gace = B.g(ACE, wgcat(w, ph, '( L encTblAsc EmptyTbl )', '( <" 0 "> ++ (/) )', etg, z0g))
    B.call(R, 'tmietbb', {'K': 'I0', 'J': "I'", 'I': 'I"', 'L': 'L', 'X': '( D ` I0 )', 'B': 'B', 'P': PL('P', 4), 'E': LMF['X3']},
           {'L e. NN0': l0}, [('I0', '( D ` I0 )', B.gam['( D ` I0 )']), ("I'", ACE, gace)])
    # extractGoF at m = 1 , used = [] , the empty table
    S1 = R.S
    DC = S1.D
    cr = s([s0, w.inst('ccatrid')], 'syl', '( %s -> ( <" 0 "> ++ (/) ) = <" 0 "> )' % ph)
    ae = s([cr], 'oveq2d', '( %s -> %s = %s )' % (ph, ACE, ACCW('EmptyTbl')))
    iv = s([S1.vals["I'"][1], ae], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ph, DC, ACCW('EmptyTbl')))
    e1 = s([s([B.S0.vals['K0'][2], w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (ph, EWg('1', '( D ` K0 )'), K041))], 'eqcomd',
           '( %s -> %s = %s )' % (ph, K041, EWg('1', '( D ` K0 )')))
    k0c = s([c['( D ` K0 ) = %s' % EWg('G', 'Y')]], 'oveq2d', '( %s -> ( <" 4 "> ++ ( D ` K0 ) ) = ( <" 4 "> ++ %s ) )' % (ph, EWg('G', 'Y')))
    e2 = s([k0c], 'oveq2d', '( %s -> %s = %s )' % (ph, EWg('1', '( D ` K0 )'), EWg('1', EWg('G', 'Y'))))
    kv0 = s([s([S1.vals['K0'][1], e1], 'eqtrd', '( %s -> ( %s ` K0 ) = %s )' % (ph, DC, EWg('1', '( D ` K0 )'))), e2], 'eqtrd',
            '( %s -> ( %s ` K0 ) = %s )' % (ph, DC, EWg('1', EWg('G', 'Y'))))
    el0 = s([closed(w, ph, 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'oveq1d', '( %s -> %s = %s )' % (ph, ENCL('(/)', '( D ` J0 )'), J02))
    jv0 = s([S1.vals['J0'][1], s([el0], 'eqcomd', '( %s -> %s = %s )' % (ph, J02, ENCL('(/)', '( D ` J0 )')))], 'eqtrd',
            '( %s -> ( %s ` J0 ) = %s )' % (ph, DC, ENCL('(/)', '( D ` J0 )')))
    cl = Closure(w, ph, {'B': ('NN0', bn)})
    cl.leaf(NW, 'NN0', s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW)))
    cl.leaf('L', 'NN0', l0)
    b2 = s([s([closed(w, ph, '2nn', '2 e. NN'), bn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ B ) e. NN )' % ph)], 'nnred', '( %s -> ( 2 ^ B ) e. RR )' % ph)
    def pmono(e1_, e2_, le_):
        ez = s([cl.mem(e1_, 'ZZ'), cl.mem(e2_, 'ZZ'), le_], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (ph, e1_, e2_, e1_, e2_))
        eu = s([ez, w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, e2_, e1_))
        return s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), eu, w.inst('leexp2a')], 'syl3anc',
                 '( %s -> ( 2 ^ %s ) <_ ( 2 ^ %s ) )' % (ph, e1_, e2_))
    BW0 = cl.ge0('( B x. %s )' % NW)
    bo = linarith(w, ph, [BW0, cl.ge0('B')], 'B <_ %s' % OO, closure=cl, products=True)
    oq = linarith(w, ph, [BW0, cl.ge0('B')], '%s <_ %s' % (OO, EXX), closure=cl, products=True)
    oo = cl.mem(OO, 'NN0')
    go = s([s([gn], 'nn0red', '( %s -> G e. RR )' % ph), b2,
            s([s([closed(w, ph, '2nn', '2 e. NN'), oo, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, OO))], 'nnred',
              '( %s -> ( 2 ^ %s ) e. RR )' % (ph, OO)), c['G < ( 2 ^ B )'], pmono('B', OO, bo)], 'ltletrd', '( %s -> G < ( 2 ^ %s ) )' % (ph, OO))
    one2 = s([closed(w, ph, '2cn', '2 e. CC'), w.inst('exp1')], 'syl', '( %s -> ( 2 ^ 1 ) = 2 )' % ph)
    f1 = s([closed(w, ph, '1lt2', '1 < 2'), s([one2], 'eqcomd', '( %s -> 2 = ( 2 ^ 1 ) )' % ph)], 'breqtrd', '( %s -> 1 < ( 2 ^ 1 ) )' % ph)
    tb0 = s([closed(w, ph, '0nn0', '0 e. NN0'), bn, w.inst('ttabtbb0')], 'syl2anc', '( %s -> %s )' % (ph, TBB('EmptyTbl', '0')))
    m = {'F': '1', 'U': '(/)', 'A': 'EmptyTbl', 'N': '0', 'H': NW, 'C': '1', 'O': OO, 'Q': EXX, 'D': DC, 'R': '( D ` J0 )',
         'P': PL('P', 5), 'E': 'E'}
    ex = {'1 e. NN0': closed(w, ph, '1nn0', '1 e. NN0'), '(/) e. Word NN0': closed(w, ph, 'wrd0', '(/) e. Word NN0'),
          'EmptyTbl e. Tbl': closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl'), WG('( D ` J0 )'): B.S0.vals['J0'][2],
          "( %s ` I' ) = %s" % (DC, ACCW('EmptyTbl')): iv, '( %s ` K0 ) = %s' % (DC, EWg('1', EWg('G', 'Y'))): kv0,
          '( %s ` J0 ) = %s' % (DC, ENCL('(/)', '( D ` J0 )')): jv0, '0 e. NN0': closed(w, ph, '0nn0', '0 e. NN0'),
          '%s e. NN0' % NW: cl.mem(NW, 'NN0'), '%s e. NN0' % OO: oo, '%s e. NN0' % EXX: cl.mem(EXX, 'NN0'), TBB('EmptyTbl', '0'): tb0,
          '( 0 + %s ) <_ %s' % (NW, NW): linarith(w, ph, [], '( 0 + %s ) <_ %s' % (NW, NW), closure=cl),
          'B <_ %s' % EXX: linarith(w, ph, [BW0, cl.ge0('B')], 'B <_ %s' % EXX, closure=cl, products=True),
          '1 < ( 2 ^ 1 )': f1, '1 <_ 1': linarith(w, ph, [], '1 <_ 1', closure=cl),
          '( 1 + ( B x. ( 0 + %s ) ) ) <_ %s' % (NW, OO): linarith(w, ph, [BW0, cl.ge0('B')], '( 1 + ( B x. ( 0 + %s ) ) ) <_ %s' % (NW, OO), closure=cl, products=True),
          'G < ( 2 ^ %s )' % OO: go, '%s <_ %s' % (OO, EXX): oq,
          '( ( ( 2 x. ( %s + 2 ) ) x. B ) + 4 ) <_ %s' % (NW, EXX): linarith(w, ph, [BW0, cl.ge0('B')], '( ( ( 2 x. ( %s + 2 ) ) x. B ) + 4 ) <_ %s' % (NW, EXX),
                                                                        closure=cl, products=True)}
    for k in ('K', 'J'):
        ex['( %s ` %s ) = %s' % (DC, k, S1.vals[k][0])] = S1.vals[k][1]
    ex['%s e. ( TM2Stk ` T )' % DC] = S1.memb
    ex.update(B.ex)
    t, cc = inst(w, ph, 'tmiexg', m, Bld(w, ph, c, ex))
    C, D, n = triple_parts(cc)
    t = hrseq(w, ph, mk['phm'], R.tri, t, R.C0, R.cur, D, R.n, n)
    NT = '( %s + %s )' % (R.n, n)
    # the post-state
    xv = s([s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), ww], 'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ W e. Word NN0 ) )' % ph),
            w.inst('extractval')], 'syl', '( %s -> %s = %s )' % (ph, EXT_, EGF))
    xe = s([xv], 'eqcomd', '( %s -> %s = %s )' % (ph, EGF, EXT_))
    Dpost = triple_D(D)
    Npost = D.split(' } X. ( ', 1)[1].rsplit(' X. { ', 1)[0]
    rn_, xn = w.rewrite(Npost, {EGF: (EXT_, xe)}, ph)
    # stacks: the chain on D
    chi = [('K0', K04), ('K0', K041), ('J0', J02), ('I0', ELT), ('I0', '( D ` I0 )'), ("I'", ACE)]
    PBC = chain_text('D', chi)
    assert DC == PBC, DC
    fin_chi = chi + [('K', ENCL('( W substr <. %s , %s >. )' % (RF, NW), 'X')), ("I'", ACCW(ZA(FINF))), ('K0', EWg(ZM(FINF), EWg('G', 'Y'))),
                     ('J0', ENCL(ZU(FINF), '( D ` J0 )'))]
    assert Dpost == chain_text('D', fin_chi), Dpost
    # typings of the final values
    e2o = s([s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % ph)
    q3 = s([closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl'), e2o], 'opelxpd', '( %s -> <. EmptyTbl , (/) >. e. ( Tbl X. 2o ) )' % ph)
    q2 = s([closed(w, ph, 'wrd0', '(/) e. Word NN0'), q3], 'opelxpd', '( %s -> <. (/) , <. EmptyTbl , (/) >. >. e. ( Word NN0 X. ( Tbl X. 2o ) ) )' % ph)
    q1 = s([closed(w, ph, '1nn0', '1 e. NN0'), q2], 'opelxpd', '( %s -> %s e. %s )' % (ph, Z0F, STY))
    sqs = s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), s([ww, q1], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0F, STY))],
            'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0F, STY))
    ps = sqs
    ip = s([ps, w.inst('exitp')], 'syl', '( %s -> ( %s e. ( 0 ... %s ) /\\ ( %s = %s \\/ %s = 1o ) /\\ A. i e. ( 0 ..^ %s ) ( i e. ( 0 ..^ %s ) /\\ -. %s = 1o ) ) )'
           % (ph, RF, NW, RF, NW, ZH(FINF), RF, NW, ZH('( %s ` i )' % SQF)))
    rz = s([ip], 'simp1d', '( %s -> %s e. ( 0 ... %s ) )' % (ph, RF, NW))
    st = s([s([ps, rz], 'jca', '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) /\\ %s e. ( 0 ... %s ) ) )' % (ph, Z0F, STY, RF, NW)),
            w.inst('exstcl')], 'syl', '( %s -> %s e. %s )' % (ph, FINF, STY))
    T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
    mz = s([st, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, ZM(FINF)))
    z2 = s([st, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. %s )' % (ph, FINF, T23))
    uz = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ZU(FINF)))
    z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` %s ) ) e. ( Tbl X. 2o ) )' % (ph, FINF))
    az = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, ZA(FINF)))
    dw = s([ww, w.inst('swrdcl')], 'syl', '( %s -> ( W substr <. %s , %s >. ) e. Word NN0 )' % (ph, RF, NW))
    B.g(fin_chi[6][1], enclg(w, ph, '( W substr <. %s , %s >. )' % (RF, NW), dw, 'X', xw))
    B.g(fin_chi[7][1], accw_g(w, ph, ZA(FINF), az, 'L', l0))
    B.g(fin_chi[8][1], ewg_(w, ph, ZM(FINF), mz, EWg('G', 'Y'), egy))
    B.g(fin_chi[9][1], enclg(w, ph, ZU(FINF), uz, '( D ` J0 )', B.S0.vals['J0'][2]))
    nst, out = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, fin_chi, B.gam, K8)
    assert chain_text('D', out) == DFIN_EXF, out
    ceq = s([clnneq(w, ph, 'E', rn_, Npost, xn, Dpost), clneq(w, ph, 'E', xn, nst, Dpost, DFIN_EXF)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN('E', xn, DFIN_EXF)))
    t, C, D, NT = hrrw(w, ph, t, R.C0, D, NT, deq=ceq)
    # the budget
    rb, NT2 = w.rewrite(NT, {EGF: (EXT_, xe)}, ph)
    EG2 = '( 2nd ` %s )' % EXT_
    a1 = s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph)
    A2 = '( ( L e. NN /\\ G e. NN0 ) /\\ W e. Word NN0 )'
    a2 = s([a1, ww], 'jca', '( %s -> %s )' % (ph, A2))
    A3 = '( %s /\\ 1 e. NN0 )' % A2
    a3 = s([a2, closed(w, ph, '1nn0', '1 e. NN0')], 'jca', '( %s -> %s )' % (ph, A3))
    A4 = '( %s /\\ (/) e. Word NN0 )' % A3
    a4 = s([a3, closed(w, ph, 'wrd0', '(/) e. Word NN0')], 'jca', '( %s -> %s )' % (ph, A4))
    A5 = '( %s /\\ EmptyTbl e. Tbl )' % A4
    a5 = s([a4, closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl')], 'jca', '( %s -> %s )' % (ph, A5))
    xc = s([a5, w.inst('extractgocl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, EGF))
    xcl = s([xv, xc], 'eqeltrd', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, EXT_))
    eg2 = s([xcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, EG2))
    TX = '( TMB ` %s )' % EXX
    TB = '( TMB ` B )'
    exn = cl.mem(EXX, 'NN0')
    tx = s([s([exn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TX))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TX))
    tb = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    KK = '( ( ( L + 1 ) ^ 2 ) x. ( %s + 2 ) )' % NW
    k1 = nlinarith(w, ph, [cl.ge0('L'), cl.ge0(NW)], '( L + 2 ) <_ %s' % KK, closure=cl)
    mono = s([bn, exn, linarith(w, ph, [BW0, cl.ge0('B')], 'B <_ %s' % EXX, closure=cl, products=True), w.inst('tmbmono')], 'syl3anc',
             '( %s -> %s <_ %s )' % (ph, TB, TX))
    cl.leaf(TX, 'NN0', tx)
    cl.leaf(TB, 'NN0', tb)
    f1_ = s([cl.mem('( L + 2 )', 'RR'), cl.mem(KK, 'RR'), cl.mem(TB, 'RR'), cl.mem(TX, 'RR'), cl.ge0('( L + 2 )'), cl.ge0(TB), k1, mono],
            'lemul12ad', '( %s -> ( ( L + 2 ) x. %s ) <_ ( %s x. %s ) )' % (ph, TB, KK, TX))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([exn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc', '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, EXX, TX))
    t16 = nlinarith(w, ph, [qd, cl.ge0(EXX)], '; 1 6 <_ %s' % TX, closure=cl, atoms=[EXX, TX])
    one = linarith(w, ph, [k1, cl.ge0('L')], '1 <_ %s' % KK, closure=cl, atoms=[KK])
    f2 = s([closed(w, ph, '1re', '1 e. RR'), cl.mem(KK, 'RR'), cl.mem(TX, 'RR'), cl.ge0(TX), one], 'lemul1ad',
           '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, TX, KK, TX))
    cl.leaf(EXYF, 'NN0', cl.mem(EXYF, 'NN0'))
    y16 = linarith(w, ph, [f2, t16], '; 1 6 <_ %s' % EXYF, closure=cl, atoms=[TX])
    cl.leaf(EG2, 'NN0', eg2)
    f3 = s([cl.mem('; 1 6', 'RR'), cl.mem(EXYF, 'RR'), cl.mem(EG2, 'RR'), cl.ge0(EG2), y16], 'lemul2ad',
           '( %s -> ( %s x. ; 1 6 ) <_ ( %s x. %s ) )' % (ph, EG2, EG2, EXYF))
    le = linarith(w, ph, [f1_, y16, f3, cl.ge0(EG2)], '%s <_ %s' % (NT2, EXFB), closure=cl, products=True, atoms=[EXYF, EG2, TB])
    le2 = s([s([rb], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, NT, EXFB, NT2, EXFB)), le], 'mpbird', '( %s -> %s <_ %s )' % (ph, NT, EXFB))
    hrle(w, ph, mk['phm'], t, C, D, NT, EXFB, cl.mem(EXFB, 'NN0'), le2, qed=True)
    return w.run()


STMTS = {}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
