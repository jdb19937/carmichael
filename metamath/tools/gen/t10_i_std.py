"""T10: smoothTDF at the machine (Lean ` smoothTDF_le_B ` ) at ` xy xr xd xf s t u = 0 6 4 7 1 2 3 ` .

  tmistdb   smoothTDF_le_B: the fuel ` y - 1 ` on top of ` y ` , ` d := 2 ` , ~ tmisgfb , the two drops, ` pushNum s 1 ` ,
            ` cmpFrag xr s ` , ` load' ( flag := decide ( cmp = .eq ) ) ` ; the flag is ` ( smoothTD y k ).1 ` (~ smoothtdval )

    MM_DB=sorties/t10.mm python3 tools/gen/t10_i_std.py tmistdb
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import mval
from t7_h_iz import lset_val, lset_ty
from cl import Closure
from t10_e_doa import ex_, lift_from
from t10_g_sga import SGX

SEL = sys.argv[1:]
LM = FRAGS['std'].lmap()
B0_, B1_ = '<. 1 , (/) >.', '<. 1 , 1o >.'


def tmistdb():
    lab = 'tmistdb'
    T = numtree(TREE_STD)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` smoothTDF_le_B ` at the machine ( ` xy xr xd xf s t u = 0 6 4 7 1 2 3 ` ): ` dup xy s t ; predNum s t ; '
               'moveEntry s xy t ` put the fuel ` y - 1 ` on top of ` y ` , ` pushNum xd 2 ` , ~ tmisgfb , ` dropNum xy ; dropNum xd ; '
               'pushNum s 1 ; cmpFrag xr s ` and ` load\' ( flag := decide ( cmp = .eq ) ) ` : the flag is ` ( smoothTD y k ).1 ` '
               '(~ smoothtdval ), ` k ` consumed, every other stack restored, in ` ( ( smoothTD y k ).2 + 1 ) B ( 4 b + 10 ) ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    ynn, fn, bn = c0['Y e. NN'], c0['F e. NN0'], c0['B e. NN0']
    yn = s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph)
    xw, x2w = c0[WG('X')], c0[WG("X'")]
    eqs = {'0': (EWg('Y', 'X'), ewg_(w, ph, 'Y', yn, 'X', xw)), '6': (EWg('F', "X'"), ewg_(w, ph, 'F', fn, "X'", x2w))}
    B = Base(w, ph, T, N8, 'std', eqs)
    c, mk = B.c, B.mk
    B.deep('std', 3)
    g = lambda k: B.S0.vals[k][2]
    Y1 = '( Y - 1 )'
    y1n = s([ynn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, Y1))
    p2 = '( 2 ^ B )'
    cl = Closure(w, ph, {'Y': ('NN', ynn), 'F': ('NN0', fn), 'B': ('NN0', bn)})
    cl.atom(p2)
    y1lt = linarith(w, ph, [c['Y < ( 2 ^ B )']], '%s < %s' % (Y1, p2), closure=cl)
    R = B.run()
    # 1. dup 0 1 2
    EY1 = EWg('Y', DK(1))
    B.call(R, 'tmidupb', {'K': '0', 'J': '1', 'I': '2', 'F': 'Y', 'N': 'B', 'X': 'X', 'P': PL('P', 6), 'E': LM['Y2']},
           {'Y e. NN0': yn}, [('1', EY1, B.g(EY1, ewg_(w, ph, 'Y', yn, DK(1), g('1'))))])
    # 2. predNum 1 2
    EY2 = EWg(Y1, DK(1))
    B.call(R, 'tmiprdbs', {'K': '1', 'J': '2', 'F': 'Y', 'N': 'B', 'X': DK(1), 'P': PL('P', 7), 'E': LM['Y3']},
           {}, [('1', EY2, B.g(EY2, ewg_(w, ph, Y1, y1n, DK(1), g('1'))))])
    # 3. moveEntry 1 0 2
    E0 = EWg(Y1, EWg('Y', 'X'))
    B.call(R, 'tmimeb', {'K': '1', 'J': '0', 'I': '2', 'F': Y1, 'N': 'B', 'X': DK(1), 'O': 'O', 'Q': 'Q', 'R': 'R',
                         'P': PL('P', 8), 'E': LM['Z1']},
           {'%s e. NN0' % Y1: y1n, '%s < %s' % (Y1, p2): y1lt}, [('1', DK(1), g('1')), ('0', E0, B.g(E0, ewg_(w, ph, Y1, y1n, EWg('Y', 'X'), g('0'))))],
           pre=None) if False else None
    # tmimeb runs at an NP class: use tmime (class S) with the bits word
    WY = '( encNatGam ` %s )' % Y1
    B.call(R, 'tmime', {'K': '1', 'J': '0', 'I': '2', 'W': WY, 'X': DK(1), 'P': PL('P', 8), 'E': LM['Z1']},
           {WRD(WY, BITS): engb(w, ph, Y1, y1n)}, [('1', DK(1), g('1')), ('0', E0, B.g(E0, ewg_(w, ph, Y1, y1n, EWg('Y', 'X'), g('0'))))])
    # 4. pushNum 4 2
    K4 = '( <" 4 "> ++ %s )' % DK(4)
    g4 = B.g(K4, wg4(w, ph, DK(4), g('4')))
    B.call(R, 'tm2fpshn', {'A': LM['Z1'], 'E': LM['Z2'], 'K': '4', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('4'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['4']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('4')))},
           [('4', K4, g4)])
    bg1 = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1_))
    bg0 = s([closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B0_))
    K41 = '( <" %s "> ++ %s )' % (B1_, K4)
    g41 = B.g(K41, wgcat(w, ph, '<" %s ">' % B1_, K4, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1_)), g4))
    B.call(R, 'tm2fpshn', {'A': LM['Z2'], 'E': LM['Z3'], 'K': '4', 'Z': B1_, 'N': S},
           {'%s e. %s' % (B1_, GX('4')): s([bg1, mk['k']['4']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1_, GX('4')))}, [('4', K41, g41)])
    K410 = '( <" %s "> ++ %s )' % (B0_, K41)
    g410 = B.g(K410, wgcat(w, ph, '<" %s ">' % B0_, K41, s([bg0], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B0_)), g41))
    B.call(R, 'tm2fpshn', {'A': LM['Z3'], 'E': LM['Y4'], 'K': '4', 'Z': B0_, 'N': S},
           {'%s e. %s' % (B0_, GX('4')): s([bg0, mk['k']['4']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B0_, GX('4')))}, [('4', K410, g410)])
    # the pushed word is EW( 2 , D ` 4 ) (~ tmienc2 )
    e2 = s([g('4'), w.inst('tmienc2')], 'syl', '( %s -> %s = %s )' % (ph, EWg('2', DK(4)), K410))
    # 5. smoothGoF at d = 2 , r = k , fuel = y - 1
    two = closed(w, ph, '2nn', '2 e. NN')
    b2 = c['2 <_ B']
    le4 = s([closed(w, ph, '2re', '2 e. RR'), s([closed(w, ph, '1le2', '1 <_ 2')], 'id', '( %s -> 1 <_ 2 )' % ph) if False else closed(w, ph, '1le2', '1 <_ 2'),
             s([s([closed(w, ph, '2z', '2 e. ZZ'), s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), b2], '3jca', '( %s -> ( 2 e. ZZ /\\ B e. ZZ /\\ 2 <_ B ) )' % ph),
                s([], 'eluz2', '( B e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ B e. ZZ /\\ 2 <_ B ) )')], 'sylibr', '( %s -> B e. ( ZZ>= ` 2 ) )' % ph),
             w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ 2 ) <_ %s )' % (ph, p2))
    two_lt = s([s([s([closed(w, ph, '2lt4', '2 < 4'), s([s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '( %s -> ( 2 ^ 2 ) = 4 )' % ph)], 'breqtrrd',
                     '( %s -> 2 < ( 2 ^ 2 ) )' % ph)], 'id', '') if False else
                s([closed(w, ph, '2lt4', '2 < 4'), s([s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '( %s -> ( 2 ^ 2 ) = 4 )' % ph)], 'breqtrrd',
                  '( %s -> 2 < ( 2 ^ 2 ) )' % ph), le4], 'id', '') if False else None
    lt22 = s([closed(w, ph, '2lt4', '2 < 4'), s([s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '( %s -> ( 2 ^ 2 ) = 4 )' % ph)], 'breqtrrd',
             '( %s -> 2 < ( 2 ^ 2 ) )' % ph)
    cl.leaf('( 2 ^ 2 )', 'RR', s([s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '') if False else
            s([s([s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '( %s -> ( 2 ^ 2 ) = 4 )' % ph), closed(w, ph, '4re', '4 e. RR')], 'eqeltrd',
              '( %s -> ( 2 ^ 2 ) e. RR )' % ph))
    t2lt = linarith(w, ph, [lt22, le4], '2 < %s' % p2, closure=cl)
    SGY = SGX('2', 'F', Y1)
    SG1 = '( 1st ` %s )' % SGY
    E4 = EWg('( 2 + %s )' % Y1, DK(4))
    E6 = EWg(SG1, "X'")
    E00 = EWg('0', EWg('Y', 'X'))
    sgc = s([s([two, fn], 'jca', '( %s -> ( 2 e. NN /\\ F e. NN0 ) )' % ph), y1n, w.inst('smoothgocl')], 'syl2anc',
            '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, SGY))
    sg1n = s([sgc, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, SG1))
    sg2n = s([sgc, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (ph, SGY))
    t2n = s([closed(w, ph, '2nn0', '2 e. NN0'), y1n, w.inst('nn0addcl')], 'syl2anc', '( %s -> ( 2 + %s ) e. NN0 )' % (ph, Y1))
    B.call(R, 'tmisgfb', {'G': '2', 'F': 'F', 'H': Y1, 'B': 'B', 'X': DK(4), "X'": "X'", 'Y': EWg('Y', 'X'), 'P': PL('P', 9), 'E': LM['Y5']},
           {'2 e. NN': two, '%s e. NN0' % Y1: y1n, '2 < %s' % p2: t2lt, '%s < %s' % (Y1, p2): y1lt,
            '( %s ` 4 ) = %s' % (R.S.D, EWg('2', DK(4))): s([R.S.vals['4'][1], s([e2], 'eqcomd', '( %s -> %s = %s )' % (ph, K410, EWg('2', DK(4))))],
                                                             'eqtrd', '( %s -> ( %s ` 4 ) = %s )' % (ph, R.S.D, EWg('2', DK(4)))),
            WG(EWg('Y', 'X')): g('0')},
           [('0', E00, B.g(E00, ewg_(w, ph, '0', closed(w, ph, '0nn0', '0 e. NN0'), EWg('Y', 'X'), g('0')))),
            ('4', E4, B.g(E4, ewg_(w, ph, '( 2 + %s )' % Y1, t2n, DK(4), g('4')))), ('6', E6, B.g(E6, ewg_(w, ph, SG1, sg1n, "X'", x2w)))])
    # 6. dropNum 0 , dropNum 4
    cur, oa = R.normalize(['1', '2', '3', '5', '6', '7', '4', '0'])
    assert oa[-1][0] == '0', oa
    z2 = s([closed(w, ph, '0nn0', '0 e. NN0'), s([closed(w, ph, '2nn0', '2 e. NN0'), bn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, p2)),
            w.inst('nn0ge0') if False else closed(w, ph, '0nn0', '0 e. NN0')], 'id', '') if False else None
    zlt = linarith(w, ph, [t2lt], '0 < %s' % p2, closure=cl)
    B.call(R, 'tmidropb', {'K': '0', 'F': '0', 'N': 'B', 'X': EWg('Y', 'X'), 'P': PL('P', 10), 'E': LM['Y6']},
           {'0 e. NN0': closed(w, ph, '0nn0', '0 e. NN0'), '0 < %s' % p2: zlt}, [('0', EWg('Y', 'X'), g('0'))], on=(R.at(oa[:-1]), oa[:-1]))
    cur, ob = R.normalize(['1', '2', '3', '5', '6', '7', '0', '4'])
    assert ob[-1][0] == '4', ob
    B1 = '( B + 1 )'
    b1n = s([bn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, B1))
    p21 = '( 2 ^ %s )' % B1
    ex2 = s([closed(w, ph, '2cn', '2 e. CC'), bn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ph, p21, p2))
    cl.atom(p21)
    t4lt = linarith(w, ph, [c['Y < ( 2 ^ B )'], ex2, t2lt], '( 2 + %s ) < %s' % (Y1, p21), closure=cl)
    B.call(R, 'tmidropb', {'K': '4', 'F': '( 2 + %s )' % Y1, 'N': B1, 'X': DK(4), 'P': PL('P', 11), 'E': LM['Z4']},
           {'( 2 + %s ) e. NN0' % Y1: t2n, '%s e. NN0' % B1: b1n, '( 2 + %s ) < %s' % (Y1, p21): t4lt}, [('4', DK(4), g('4'))],
           on=(R.at(ob[:-1]), ob[:-1]))
    # 7. pushNum 1 1
    K1 = '( <" 4 "> ++ %s )' % DK(1)
    g1 = B.g(K1, wg4(w, ph, DK(1), g('1')))
    B.call(R, 'tm2fpshn', {'A': LM['Z4'], 'E': LM['Z5'], 'K': '1', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('1'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['1']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('1')))},
           [('1', K1, g1)])
    K11 = '( <" %s "> ++ %s )' % (B1_, K1)
    g11 = B.g(K11, wgcat(w, ph, '<" %s ">' % B1_, K1, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1_)), g1))
    B.call(R, 'tm2fpshn', {'A': LM['Z5'], 'E': LM['Y7'], 'K': '1', 'Z': B1_, 'N': S},
           {'%s e. %s' % (B1_, GX('1')): s([bg1, mk['k']['1']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1_, GX('1')))}, [('1', K11, g11)])
    e1 = s([g('1'), w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (ph, EWg('1', DK(1)), K11))
    # 8. cmpFrag 6 1
    from t10_g_sga import ST_SGFLE
    sgle = inst(w, ph, 'sgfle', {'G': '2', 'I': Y1}, Bld(w, ph, c, {'2 e. NN': two, '%s e. NN0' % Y1: y1n}))[0]
    cl.leaf(SG1, 'NN0', sg1n)
    sglt = linarith(w, ph, [sgle, c['F < ( 2 ^ B )']], '%s < %s' % (SG1, p2), closure=cl)
    onelt = linarith(w, ph, [t2lt], '1 < %s' % p2, closure=cl)
    CMPN = '{ h e. TMSt | ( TMcmp ` h ) = ( %s Ncmp 1 ) }' % SG1
    B.call(R, 'tmicmpb', {'K': '6', 'J': '1', 'F': SG1, 'G': '1', 'N': 'B', 'X': "X'", 'Y': DK(1), 'P': PL('P', 12), 'E': LM['Z6']},
           {'%s e. NN0' % SG1: sg1n, '1 e. NN0': closed(w, ph, '1nn0', '1 e. NN0'), '%s < %s' % (SG1, p2): sglt, '1 < %s' % p2: onelt,
            '( %s ` 1 ) = %s' % (R.S.D, EWg('1', DK(1))): s([R.S.vals['1'][1], s([e1], 'eqcomd', '( %s -> %s = %s )' % (ph, K11, EWg('1', DK(1))))],
                                                             'eqtrd', '( %s -> ( %s ` 1 ) = %s )' % (ph, R.S.D, EWg('1', DK(1))))},
           [('6', "X'", x2w), ('1', DK(1), g('1'))])
    # 9. load ( flag := decide ( cmp = .eq ) )
    STD_ = '( Y SmoothTD F )'
    FL = '( 1st ` %s )' % STD_
    IFS = 'if ( %s = 1 , 1o , (/) )' % SG1
    sv = s([ynn, fn, w.inst('smoothtdval')], 'syl2anc', '( %s -> %s = <. %s , ( ( 2nd ` %s ) + 1 ) >. )' % (ph, STD_, IFS, SGY))
    from t10_e_doa import fst_of, snd_of
    ife = ifex_closed(w, ph, '%s = 1' % SG1, '1o', '(/)', s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V'))
    s2e = ex_(w, ph, '( ( 2nd ` %s ) + 1 )' % SGY, 'ovex')
    fv = fst_of(w, ph, STD_, IFS, '( ( 2nd ` %s ) + 1 )' % SGY, sv, ife, s2e)
    sd = snd_of(w, ph, STD_, IFS, '( ( 2nd ` %s ) + 1 )' % SGY, sv, ife, s2e)
    kw = lambda t: dict(fl='if ( ( TMcmp ` %s ) = 1o , 1o , (/) )' % t)
    pr = '( %s /\\ r e. %s )' % (ph, CMPN)
    rin = s([], 'simpr', '( %s -> r e. %s )' % (pr, CMPN))
    idh = s([], 'id', '( h = r -> h = r )')
    condc = lambda t: '( TMcmp ` %s ) = ( %s Ncmp 1 )' % (t, SG1)
    cg, new = w.wcongr(condc('h'), {'h': 'r'}, 'h = r', {'h': idh})
    both = s([rin, s([cg], 'elrab', '( r e. %s <-> ( r e. TMSt /\\ %s ) )' % (CMPN, condc('r')))], 'sylib', '( %s -> ( r e. TMSt /\\ %s ) )' % (pr, condc('r')))
    rr = s([both], 'simpld', '( %s -> r e. TMSt )' % pr)
    rc = s([both], 'simprd', '( %s -> %s )' % (pr, condc('r')))
    nv = lset_val(w, pr, kw, 'r', rr)
    NR = '( %s ` r )' % L_EQ
    ncq = s([s([lift_from(w, ph, pr, sg1n), closed(w, pr, '1nn0', '1 e. NN0'), w.inst('ncmpeq')], 'syl2anc',
               '( %s -> ( ( %s Ncmp 1 ) = 1o <-> %s = 1 ) )' % (pr, SG1, SG1))], 'id', '') if False else \
        s([lift_from(w, ph, pr, sg1n), closed(w, pr, '1nn0', '1 e. NN0'), w.inst('ncmpeq')], 'syl2anc',
          '( %s -> ( ( %s Ncmp 1 ) = 1o <-> %s = 1 ) )' % (pr, SG1, SG1))
    c1 = s([s([rc], 'eqeq1d', '( %s -> ( ( TMcmp ` r ) = 1o <-> ( %s Ncmp 1 ) = 1o ) )' % (pr, SG1)), ncq], 'bitrd',
           '( %s -> ( ( TMcmp ` r ) = 1o <-> %s = 1 ) )' % (pr, SG1))
    i1_ = s([c1], 'ifbid', '( %s -> if ( ( TMcmp ` r ) = 1o , 1o , (/) ) = %s )' % (pr, IFS))
    flr = s([s([nv['fields']['fl'], i1_], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pr, NR, IFS)),
             s([lift_from(w, ph, pr, fv)], 'eqcomd', '( %s -> %s = %s )' % (pr, IFS, FL))], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pr, NR, FL))
    inm = A8.nfl_pack(w, pr, FL, NR, nv['mem'], flr)
    hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, CMPN, L_EQ, NFL(FL)))
    B.call(R, 'tm2flg', {'A': LM['Z6'], 'E': 'E', 'F': L_EQ, 'N': CMPN, "N'": NFL(FL)},
           {LTY(L_EQ): lset_ty(w, ph, mk, L_EQ, kw), SSS(CMPN): B.ss(CMPN), SSS(NFL(FL)): B.ss(NFL(FL)),
            'A. r e. %s ( %s ` r ) e. %s' % (CMPN, L_EQ, NFL(FL)): hl}, [])
    cur, of = R.normalize(N8)
    assert of == [('0', EWg('Y', 'X')), ('6', "X'")], of
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    u0 = upidv(w, ph, 'D', '0', EWg('Y', 'X'), B.S0.vals['0'][1], mk['tv'], B.dd, mk['k']['0']['kd'])
    Dc = triple_D(D)
    ru, xu = w.rewrite(Dc, {UP('D', '0', EWg('Y', 'X')): ('D', u0)}, ph)
    assert xu == UP('D', '6', "X'"), xu
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', NFL(FL), ru, Dc, xu))
    # the bound
    TB = '( TMB ` B )'
    TB1 = '( TMB ` %s )' % B1
    KB = '( TMB ` ( ( 4 x. B ) + ; 1 0 ) )'
    k410 = s([bn, w.inst('tplb410')], 'syl', '( %s -> %s = ( ; 6 4 x. %s ) )' % (ph, KB, TB1))
    tbn = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    t1n = s([s([b1n, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB1))
    cl.leaf(TB, 'NN0', tbn)
    cl.leaf(TB1, 'NN0', t1n)
    kbn = s([k410, cl.mem('( ; 6 4 x. %s )' % TB1, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, KB))
    cl.leaf(KB, 'NN0', kbn)
    S2 = '( 2nd ` %s )' % SGY
    cl.leaf(S2, 'NN0', sg2n)
    tbm = s([bn, b1n, linarith(w, ph, [], 'B <_ %s' % B1, closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, TB1))
    t1p = s([s([b1n, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB1))
    BND = '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (STD_, TMBx('( ( 4 x. B ) + ; 1 0 )'))
    SB = '( ( ( %s + 1 ) + 1 ) x. %s )' % (S2, KB)
    bq = s([s([sd], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( ( %s + 1 ) + 1 ) )' % (ph, STD_, S2))], 'oveq1d',
           '( %s -> %s = %s )' % (ph, BND, SB))
    SK = '( %s x. %s )' % (S2, KB)
    ex_sb = lineq(w, ph, SB, '( %s + ( 2 x. %s ) )' % (SK, KB), closure=cl, products=True)
    ex_n = '( ( ( %s + 1 ) x. %s ) )' % (S2, KB)
    SK1 = '( ( %s + 1 ) x. %s )' % (S2, KB)
    e_sk1 = lineq(w, ph, SK1, '( %s + %s )' % (SK, KB), closure=cl, products=True) if False else None
    LW = '( # ` %s )' % WY
    cl.leaf(LW, 'NN0', s([encw(w, ph, Y1, y1n), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))
    lw = s([s([y1n, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` %s ) ) )' % (ph, LW, Y1)),
            s([y1n, bn, y1lt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` %s ) ) <_ B )' % (ph, Y1))],
           'eqbrtrd', '( %s -> %s <_ B )' % (ph, LW))
    import num
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( B + 2 ) ^ 2 ) ) <_ ( TMB ` B ) )' % ph)
    meb = nlinarith(w, ph, [lw, qd, cl.ge0('B'), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ %s' % (LW, TB), closure=cl, atoms=['B', LW, TB])
    sbn = s([s([s([sg2n, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, S2)), w.inst('peano2nn0')], 'syl',
               '( %s -> ( ( %s + 1 ) + 1 ) e. NN0 )' % (ph, S2)), kbn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, SB))
    cl.leaf(SB, 'NN0', sbn)
    cl.leaf(BND, 'NN0', s([bq, sbn], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, BND)))
    le = linarith(w, ph, [bq, ex_sb, k410, tbm, t1p, meb], '%s <_ %s' % (n, BND), closure=cl, atoms=[TB, TB1, KB, S2, BND, SB, LW], products=True)
    bn_ = s([bq, cl.mem(SB, 'NN0') if False else s([s([s([s([sg2n, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, S2)), w.inst('peano2nn0')],
                                                       'syl', '( %s -> ( ( %s + 1 ) + 1 ) e. NN0 )' % (ph, S2)), kbn, w.inst('nn0mulcl')], 'syl2anc',
                                                    '( %s -> %s e. NN0 )' % (ph, SB))], 'id', '') if False else
            s([s([s([sg2n, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, S2)), w.inst('peano2nn0')], 'syl',
                 '( %s -> ( ( %s + 1 ) + 1 ) e. NN0 )' % (ph, S2)), kbn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, SB))],
          'eqeltrd', '( %s -> %s e. NN0 )' % (ph, BND))
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, bn_, le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
