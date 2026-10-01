"""T7c: the three runs of Lean's ` primeGoBody ` at the machine (T7b-HANDOFF
item 2), wherever ` primeGoBody ` is installed ( TMIpgb ).

  tmipgt1   dup xd s t ; dup xd t s ; mulC s t u xf xm ; dup xm s t ; cmpFrag s u
  tmipgt2   dup xm s t ; dup xd t s ; modC s t u xd xf xm ; isZero s t ; dropNum s
  tmipgt3   incr xd s ; predNum xf s ; isZero xf s

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_c_pgt.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *
from cl import Closure
import lin
from lin import linarith, nlinarith
from t7_v_leb import tmb_lin
from t7b_h_dmq import ifmax_le

lin.FASTPATH = True
SEL = sys.argv[1:]

PGB = FRAGS['pgb']
LM = PGB.lmap()
TB = '( TMB ` N )'
NUM2 = (('F e. NN0', 'G e. NN0', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )'))
NUM2P = (('F e. NN0', 'G e. NN', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )'))
DKJ = ((WRD('X', GAM), WRD('Y', GAM), STKD('D')), ('( D ` K ) = %s' % EW('F', 'X'), '( D ` J ) = %s' % EW('G', 'Y')))
NCMP1 = '{ h e. TMSt | ( TMcmp ` h ) = ( F Ncmp ( G x. G ) ) }'
NFL2 = '{ h e. TMSt | ( TMfl ` h ) = if ( ( F mod G ) = 0 , 1o , (/) ) }'
NFL3 = '{ h e. TMSt | ( TMfl ` h ) = if ( ( H - 1 ) = 0 , 1o , (/) ) }'
NUM3 = (('G e. NN0', 'H e. NN', 'N e. NN0'), ('G < ( 2 ^ N )', 'H < ( 2 ^ N )'))
DJI = ((WRD('Y', GAM), WRD('Z', GAM), STKD('D')), ('( D ` J ) = %s' % EW('G', 'Y'), '( D ` I ) = %s' % EW('H', 'Z')))
POST3 = UP(UP('D', 'J', EW('( G + 1 )', 'Y')), 'I', EW('( H - 1 )', 'Z'))


def STMT(lab):
    head = ((T_PHM7, PGB.pred()), (idx_tree(K6), dist_tree(K6)))
    if lab == 'tmipgt1':
        return head + ((NUM2, DKJ),), TRI(CLN(LM['B0'], SS, 'D'), CLN(LM["B'"], NCMP1, 'D'), '( 5 x. %s )' % TB)
    if lab == 'tmipgt2':
        return head + ((NUM2P, DKJ),), TRI(CLN(LM['E0'], SS, 'D'), CLN(LM["E'"], NFL2, 'D'), '( 5 x. %s )' % TB)
    if lab == 'tmipgt3':
        return head + ((NUM3, DJI),), TRI(CLN(LM['A0'], SS, 'D'), CLN(LM["A'"], NFL3, POST3), '( 3 x. %s )' % TB)


def start(lab, desc):
    T, C = STMT(lab)
    ph = cj(T)
    w = W(lab, desc)
    c, mk, ne, base = setup(w, ph, T, K6, PGB.pred(), 'pgb')
    return T, C, ph, w, c, mk, ne, base


def stacks0(w, ph, c, mk, ne, known):
    """the base stacks with the known values (s -> (value text, eq leaf)) and the rest self"""
    dd = c[STKD('D')]
    vals = {}
    for s_ in K6:
        if s_ in known:
            txt, st, g = known[s_]
            vals[s_] = (txt, st, g)
        else:
            vals[s_] = selfval(w, ph, mk, 'D', dd, s_)
    return Stacks(w, ph, mk, 'D', dd, ne, vals)


def eqv(S, s_, val):
    """the leaf ( Dcur ` s ) = val and its step"""
    txt, st, g = S.vals[s_]
    assert txt == val, (txt, val)
    return {'( %s ` %s ) = %s' % (S.D, s_, val): st}


def tmipgt1():
    lab = 'tmipgt1'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The compare run of Lean\'s ` primeGoBody xm xd xf s t u ` , ` dup xd s t ; dup xd t s ; mulC s t u xf xm ; '
        'dup xm s t ; cmpFrag s u ` , wherever ` primeGoBody ` is installed: ` cmp ` compares ` m ` on ` xm ` with '
        '` d x. d ` ( ` d ` on ` xd ` ) and every stack is restored ( ` primeGoBody_runs ` , steps 1-5).')
    fn, gn, nn = c['F e. NN0'], c['G e. NN0'], c['N e. NN0']
    xg, yg = c[WRD('X', GAM)], c[WRD('Y', GAM)]
    kv = {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ph, 'F', fn, 'X', xg)),
          'J': (EW('G', 'Y'), c['( D ` J ) = %s' % EW('G', 'Y')], ewg(w, ph, 'G', gn, 'Y', yg))}
    S0 = stacks0(w, ph, c, mk, ne, kv)
    run = Run(w, ph, mk, S0, base, c)
    DV = lambda s_: '( D ` %s )' % s_
    dg = lambda s_: S0.vals[s_][2]
    # 1. dup xd s t
    run.call('tmidupb', {'K': 'J', 'J': "I'", 'I': 'I"', 'F': 'G', 'X': 'Y', 'P': PL('P', 5), 'E': LM['X1']},
             eqv(run.S, 'J', EW('G', 'Y')), [("I'", EW('G', DV("I'")), ewg(w, ph, 'G', gn, DV("I'"), dg("I'")))])
    # 2. dup xd t s
    run.call('tmidupb', {'K': 'J', 'J': 'I"', 'I': "I'", 'F': 'G', 'X': 'Y', 'P': PL('P', 6), 'E': LM['X2']},
             eqv(run.S, 'J', EW('G', 'Y')), [('I"', EW('G', DV('I"')), ewg(w, ph, 'G', gn, DV('I"'), dg('I"')))])
    # 3. mulC s t u xf xm
    GG = '( G x. G )'
    ggn = w.s([gn, gn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, GG))
    ex3 = eqv(run.S, "I'", EW('G', DV("I'")))
    ex3.update(eqv(run.S, 'I"', EW('G', DV('I"'))))
    ex3.update({WRD(DV("I'"), GAM): dg("I'"), WRD(DV('I"'), GAM): dg('I"')})
    run.call('tmimulb', {'K': "I'", 'J': 'I"', 'I': 'I0', "I'": 'I', 'I"': 'K', 'F': 'G', 'G': 'G',
                         'X': DV("I'"), 'Y': DV('I"'), 'P': PL('P', 7), 'E': LM['X3']},
             ex3, [('I0', EW(GG, DV('I0')), ewg(w, ph, GG, ggn, DV('I0'), dg('I0'))), ("I'", DV("I'"), dg("I'")),
                   ('I"', DV('I"'), dg('I"'))])
    # 4. dup xm s t
    run.call('tmidupb', {'K': 'K', 'J': "I'", 'I': 'I"', 'F': 'F', 'X': 'X', 'P': PL('P', 8), 'E': LM['X4']},
             eqv(run.S, 'K', EW('F', 'X')), [("I'", EW('F', DV("I'")), ewg(w, ph, 'F', fn, DV("I'"), dg("I'")))])
    # 5. cmpFrag s u : the length form
    EF, EGG = ENC('F'), ENC(GG)
    ef = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    egg = w.s([ggn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EGG))
    def ib(t, tn, X):
        gv = w.s([tn, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. %s ) )' % (ph, ENG(t), ENC(t)))
        return w.s([gv], 'oveq1d', '( %s -> %s = %s )' % (ph, EW(t, X), CC('( inclBool o. %s )' % ENC(t), YX(X))))
    S = run.S
    e1 = w.s([S.vals["I'"][1], ib('F', fn, DV("I'"))], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ph, S.D, CC('( inclBool o. %s )' % EF, YX(DV("I'")))))
    e2 = w.s([S.vals['I0'][1], ib(GG, ggn, DV('I0'))], 'eqtrd', "( %s -> ( %s ` I0 ) = %s )" % (ph, S.D, CC('( inclBool o. %s )' % EGG, YX(DV('I0')))))
    ex5 = {"( %s ` I' ) = %s" % (S.D, CC('( inclBool o. %s )' % EF, YX(DV("I'")))): e1,
           '( %s ` I0 ) = %s' % (S.D, CC('( inclBool o. %s )' % EGG, YX(DV('I0')))): e2,
           WRD(EF, '2o'): ef, WRD(EGG, '2o'): egg, WRD(DV("I'"), GAM): dg("I'"), WRD(DV('I0'), GAM): dg('I0')}
    tf = w.s([fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, EF))
    tg = w.s([ggn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = %s )' % (ph, EGG, GG))
    nc = w.s([tf, tg], 'oveq12d', '( %s -> ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) = ( F Ncmp %s ) )' % (ph, EF, EGG, GG))
    OLD = '{ h e. TMSt | ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) }' % (EF, EGG)
    ce = w.s([nc], 'eqeq2d', '( %s -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) <-> ( TMcmp ` h ) = ( F Ncmp %s ) ) )' % (ph, EF, EGG, GG))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) <-> ( TMcmp ` h ) = ( F Ncmp %s ) ) )'
                  % (ph, EF, EGG, GG))], 'rabbidva', '( %s -> %s = %s )' % (ph, OLD, NCMP1))
    t5, n5 = run.call('tmicmp', {'K': "I'", 'J': 'I0', 'L': EF, "L'": EGG, 'X': DV("I'"), 'Y': DV('I0'), 'P': PL('P', 9), 'E': LM["B'"]},
                      ex5, [("I'", DV("I'"), dg("I'")), ('I0', DV('I0'), dg('I0'))], cls_rw=(rb, NCMP1))
    cur, out = run.normalize(K6)
    assert out == [], out
    assert cur == CLN(LM["B'"], NCMP1, 'D'), cur
    # the bound
    LF, LG = '( # ` %s )' % EF, '( # ` %s )' % EGG
    lf = w.s([fn, nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, LF))
    NN = '( N + N )'
    nnn = w.s([nn, nn], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, NN))
    cl = Closure(w, ph, {'G': ('NN0', gn), 'N': ('NN0', nn), 'F': ('NN0', fn)})
    p2 = '( 2 ^ N )'
    cl.atom(p2)
    p2n = w.s([closed(w, ph, '2nn0', '2 e. NN0'), nn, w.inst('nn0expcld') if False else w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, p2))
    cl.leaf(p2, 'NN0', p2n)
    ggl = nlinarith(w, ph, [c['G < ( 2 ^ N )'], cl.ge0('G')], '%s < ( %s x. %s )' % (GG, p2, p2), closure=cl, atoms=[p2])
    ea = w.s([closed(w, ph, '2cn', '2 e. CC'), nn, nn, w.inst('expadd')], 'syl3anc', '( %s -> ( 2 ^ %s ) = ( %s x. %s ) )' % (ph, NN, p2, p2))
    gglt = w.s([ggl, ea], 'breqtrrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, GG, NN))
    lg = w.s([ggn, nnn, gglt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, LG, NN))
    lfn = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LF))
    lgn = w.s([egg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LG))
    cl.leaf(LF, 'NN0', lfn); cl.leaf(LG, 'NN0', lgn)
    lf2 = linarith(w, ph, [lf, cl.ge0('N')], '%s <_ %s' % (LF, NN), closure=cl)
    MX = 'if ( %s <_ %s , %s , %s )' % (LF, LG, LG, LF)
    mx = ifmax_le(w, ph, LF, LG, NN, cl.mem(LF, 'RR'), cl.mem(LG, 'RR'), cl.mem(NN, 'RR'), lf2, lg)
    mxn = w.s([lgn, lfn], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MX))
    cl.leaf(MX, 'NN0', mxn)
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    cl.leaf(TB, 'NN0', tbn)
    tl = tmb_lin(w, ph, nn, '2')
    B5 = '( 5 x. %s )' % TB
    le = linarith(w, ph, [mx, tl, cl.ge0('N'), cl.ge0(TB)], '%s <_ %s' % (run.n, B5), closure=cl)
    hrle(w, ph, mk['phm'], run.tri, run.C0, run.cur, run.n, B5, cl.mem(B5, 'NN0'), le, qed=True)
    return w.run()


def modle(w, ph, F, G, fn, gnn, cl):
    """( ph -> ( F mod G ) <_ F ) for F e. NN0 , G e. NN"""
    md, fq = '( %s mod %s )' % (F, G), '( |_ ` ( %s / %s ) )' % (F, G)
    fr = w.s([fn], 'nn0red', '( %s -> %s e. RR )' % (ph, F))
    gp = w.s([gnn], 'nnrpd', '( %s -> %s e. RR+ )' % (ph, G))
    mv = w.s([fr, gp, w.inst('modvalr')], 'syl2anc', '( %s -> %s = ( %s - ( %s x. %s ) ) )' % (ph, md, F, fq, G))
    fqn = w.s([fn, gnn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, fq))
    cl.leaf(fq, 'NN0', fqn)
    return nlinarith(w, ph, [mv, cl.ge0(fq), cl.ge0(G)], '%s <_ %s' % (md, F), closure=cl, atoms=[fq, md])


def tmb_facts(w, ph, nn):
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    return tbn


def tmipgt2():
    lab = 'tmipgt2'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The modulo run of Lean\'s ` primeGoBody xm xd xf s t u ` , ` dup xm s t ; dup xd t s ; modC s t u xd xf xm ; '
        'isZero s t ; dropNum s ` , wherever ` primeGoBody ` is installed: ` flag ` is ` [ m mod d = 0 ] ` and every '
        'stack is restored; the flag survives ` dropNum s ` by ~ tmidropnb ( ` primeGoBody_runs ` , steps 6a-6e).')
    fn, gnn, nn = c['F e. NN0'], c['G e. NN'], c['N e. NN0']
    gn = w.s([gnn], 'nnnn0d', '( %s -> G e. NN0 )' % ph)
    xg, yg = c[WRD('X', GAM)], c[WRD('Y', GAM)]
    kv = {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ph, 'F', fn, 'X', xg)),
          'J': (EW('G', 'Y'), c['( D ` J ) = %s' % EW('G', 'Y')], ewg(w, ph, 'G', gn, 'Y', yg))}
    S0 = stacks0(w, ph, c, mk, ne, kv)
    run = Run(w, ph, mk, S0, base, c)
    run.base['G e. NN0'] = gn
    DV = lambda s_: '( D ` %s )' % s_
    dg = lambda s_: S0.vals[s_][2]
    # 1. dup xm s t
    run.call('tmidupb', {'K': 'K', 'J': "I'", 'I': 'I"', 'F': 'F', 'X': 'X', 'P': PL('P', 10), 'E': LM['Y1']},
             eqv(run.S, 'K', EW('F', 'X')), [("I'", EW('F', DV("I'")), ewg(w, ph, 'F', fn, DV("I'"), dg("I'")))])
    # 2. dup xd t s
    run.call('tmidupb', {'K': 'J', 'J': 'I"', 'I': "I'", 'F': 'G', 'X': 'Y', 'P': PL('P', 11), 'E': LM['Y2']},
             eqv(run.S, 'J', EW('G', 'Y')), [('I"', EW('G', DV('I"')), ewg(w, ph, 'G', gn, DV('I"'), dg('I"')))])
    # 3. modC s t u xd xf xm
    FM = '( F mod G )'
    fmn = w.s([w.s([fn], 'nn0zd', '( %s -> F e. ZZ )' % ph), gnn, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FM))
    ex3 = eqv(run.S, "I'", EW('F', DV("I'")))
    ex3.update(eqv(run.S, 'I"', EW('G', DV('I"'))))
    ex3.update({WRD(DV("I'"), GAM): dg("I'"), WRD(DV('I"'), GAM): dg('I"')})
    run.call('tmimodcb', {'K': "I'", 'J': 'I"', 'I': 'I0', "I'": 'J', 'I"': 'I', 'I0': 'K', 'F': 'F', 'G': 'G',
                          'X': DV("I'"), 'Y': DV('I"'), 'P': PL('P', 12), 'E': LM['Y3']},
             ex3, [("I'", EW(FM, DV("I'")), ewg(w, ph, FM, fmn, DV("I'"), dg("I'"))), ('I"', DV('I"'), dg('I"'))])
    # 4. isZero s t
    cl = Closure(w, ph, {'F': ('NN0', fn), 'G': ('NN', gnn), 'N': ('NN0', nn)})
    cl.leaf(FM, 'NN0', fmn)
    p2 = '( 2 ^ N )'
    p2n = w.s([closed(w, ph, '2nn0', '2 e. NN0'), nn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, p2))
    cl.leaf(p2, 'NN0', p2n)
    mle = w.s([w.s([fn], 'nn0red', '( %s -> F e. RR )' % ph), w.s([gnn], 'nnrpd', '( %s -> G e. RR+ )' % ph), fn if False else
               w.s([fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ph), w.inst('modlelt' if False else 'modlt')], 'syl3anc', '') if False else None
    fr = w.s([fn], 'nn0red', '( %s -> F e. RR )' % ph)
    grp = w.s([gnn], 'nnrpd', '( %s -> G e. RR+ )' % ph)
    f0 = w.s([fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ph)
    mle = modle(w, ph, 'F', 'G', fn, gnn, cl)
    mlt = w.s([mle, c['F < ( 2 ^ N )']], 'lelttrd', '( %s -> %s < %s )' % (ph, FM, p2))
    S = run.S
    ex4 = eqv(S, "I'", EW(FM, DV("I'")))
    ex4.update({'%s e. NN0' % FM: fmn, '%s < %s' % (FM, p2): mlt, WRD(DV("I'"), GAM): dg("I'")})
    run.call('tmiizbs', {'K': "I'", 'I': 'I"', 'F': FM, 'X': DV("I'"), 'P': PL('P', 13), 'E': LM['Y4']}, ex4, [])
    # 5. dropNum s : stacks normalised to UPD( D , I' , .. ) first
    cur, out = run.normalize(['K', 'J', 'I', 'I"', 'I0', "I'"])
    assert out == [("I'", EW(FM, DV("I'")))], out
    IFM = 'if ( %s = 0 , 1o , (/) )' % FM
    ex5 = {'%s e. NN0' % FM: fmn, '%s < %s' % (FM, p2): mlt, WRD(DV("I'"), GAM): dg("I'")}
    run.call('tmidropnb', {'K': "I'", 'F': FM, 'X': DV("I'"), 'O': IFM, 'P': PL('P', 14), 'E': LM["E'"]}, ex5,
             [("I'", DV("I'"), dg("I'"))], on=(S0, []))
    cur, out = run.normalize(K6)
    assert out == [], out
    assert cur == CLN(LM["E'"], NFL2, 'D'), cur
    tbn = tmb_facts(w, ph, nn)
    cl.leaf(TB, 'NN0', tbn)
    B5 = '( 5 x. %s )' % TB
    le = linarith(w, ph, [cl.ge0(TB)], '%s <_ %s' % (run.n, B5), closure=cl)
    hrle(w, ph, mk['phm'], run.tri, run.C0, run.cur, run.n, B5, cl.mem(B5, 'NN0'), le, qed=True)
    return w.run()


def tmipgt3():
    lab = 'tmipgt3'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The step run of Lean\'s ` primeGoBody xm xd xf s t u ` , ` incr xd s ; predNum xf s ; isZero xf s ` , '
        'wherever ` primeGoBody ` is installed: the divisor on ` xd ` goes up by one, the fuel on ` xf ` down by one, '
        'and ` flag ` is ` [ fuel - 1 = 0 ] ` ( ` primeGoBody_runs ` , steps 7-9).')
    gn, hnn, nn = c['G e. NN0'], c['H e. NN'], c['N e. NN0']
    hn = w.s([hnn], 'nnnn0d', '( %s -> H e. NN0 )' % ph)
    yg, zg = c[WRD('Y', GAM)], c[WRD('Z', GAM)]
    kv = {'J': (EW('G', 'Y'), c['( D ` J ) = %s' % EW('G', 'Y')], ewg(w, ph, 'G', gn, 'Y', yg)),
          'I': (EW('H', 'Z'), c['( D ` I ) = %s' % EW('H', 'Z')], ewg(w, ph, 'H', hn, 'Z', zg))}
    S0 = stacks0(w, ph, c, mk, ne, kv)
    run = Run(w, ph, mk, S0, base, c)
    G1, H1 = '( G + 1 )', '( H - 1 )'
    g1n = w.s([gn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, G1))
    h1n = w.s([hnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, H1))
    run.call('tmiincbs', {'K': 'J', 'J': "I'", 'F': 'G', 'X': 'Y', 'P': PL('P', 15), 'E': LM['Z1']},
             eqv(run.S, 'J', EW('G', 'Y')), [('J', EW(G1, 'Y'), ewg(w, ph, G1, g1n, 'Y', yg))])
    run.call('tmiprdbs', {'K': 'I', 'J': "I'", 'F': 'H', 'X': 'Z', 'P': PL('P', 16), 'E': LM['Z2']},
             eqv(run.S, 'I', EW('H', 'Z')), [('I', EW(H1, 'Z'), ewg(w, ph, H1, h1n, 'Z', zg))])
    cl = Closure(w, ph, {'G': ('NN0', gn), 'H': ('NN', hnn), 'N': ('NN0', nn)})
    p2 = '( 2 ^ N )'
    cl.atom(p2)
    h1lt = linarith(w, ph, [c['H < ( 2 ^ N )']], '%s < %s' % (H1, p2), closure=cl)
    ex3 = eqv(run.S, 'I', EW(H1, 'Z'))
    ex3.update({'%s e. NN0' % H1: h1n, '%s < %s' % (H1, p2): h1lt})
    run.call('tmiizbs', {'K': 'I', 'I': "I'", 'F': H1, 'X': 'Z', 'P': PL('P', 17), 'E': LM["A'"]}, ex3, [])
    assert run.cur == CLN(LM["A'"], NFL3, POST3), run.cur
    tbn = tmb_facts(w, ph, nn)
    cl.leaf(TB, 'NN0', tbn)
    B3 = '( 3 x. %s )' % TB
    le = linarith(w, ph, [cl.ge0(TB)], '%s <_ %s' % (run.n, B3), closure=cl)
    hrle(w, ph, mk['phm'], run.tri, run.C0, run.cur, run.n, B3, cl.mem(B3, 'NN0'), le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
