"""T12: korseltTDF at the machine (Step5.lean ` koTest ` , ` koBody ` , ` korseltTDF ` ; blueprint D4, D6).

  tmikota  the prefix of ` koTest ` : ` dup 5 3 2 ; predNum 3 2 ; isZero 3 2 ` ( ` p - 1 ` on 3, flag ` p - 1 = 0 ` )
  tmikot   ` koTest_runs ` : flag ` if- ( p - 1 = 0 , m - 1 = 0 , ( m - 1 ) mod ( p - 1 ) = 0 ) ` , stacks restored
  t12kofl  the machine's korselt flag is ` ( 1st ( m KorseltTD S ) ) ` when every entry is at least 2
  tmikoai  one entry of the loop ( ` koBody_runs ` ) along the family ` P' `
  tmikoat  the frame: the family's typing, its column 5, its values at 0 and at the end
  tmikoal  ` accLoopF koBody ` at the family (~ tmiacl )
  tmiko    ` korseltTDF_runs ` : ~ tmilcpyb then ~ tmikoal

    MM_DB=sorties/t12.mm python3 tools/gen/t12_k_ko.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t7lib import mval
from t10_n_rgf import tmbn
from t10_d_dot import skip_ty, skip_in, cls_to, load_nfl, lift
from t10_e_doa import lift_from
from t10_u_s2s import expose
import t8alib as A8
import t7c_h_lst as LST
import t12_j_acc as ACC
from t12_j_acc import Plain
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
TB = lambda x: '( TMB ` %s )' % x
KTF = lambda p: ('( ( ( %s - 1 ) = 0 /\\ ( F - 1 ) = 0 ) \\/ ( -. ( %s - 1 ) = 0 /\\ ( ( F - 1 ) mod ( %s - 1 ) ) = 0 ) )'
                 % (p, p, p))   # the machine's test at p ( ` if- ` unfolded: the tools' parser has no ` if- ` )
KTIF = lambda p: 'if- ( ( %s - 1 ) = 0 , ( F - 1 ) = 0 , ( ( F - 1 ) mod ( %s - 1 ) ) = 0 )' % (p, p)


def ifp_bi(w, ph, p, cst, truth):
    """( ph -> ( KTF( p ) <-> branch ) ) from cst : ( ph -> ( p - 1 ) = 0 ) (truth) or ( ph -> -. ( p - 1 ) = 0 )"""
    s = w.s
    br = '( F - 1 ) = 0' if truth else '( ( F - 1 ) mod ( %s - 1 ) ) = 0' % p
    d = s([s([], 'df-ifp', '( %s <-> %s )' % (KTIF(p), KTF(p)))], 'a1i', '( %s -> ( %s <-> %s ) )' % (ph, KTIF(p), KTF(p)))
    i = s([cst, w.inst('ifptru' if truth else 'ifpfal')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, KTIF(p), br))
    return s([d, i], 'bitr3d', '( %s -> ( %s <-> %s ) )' % (ph, KTF(p), br))
KOFL = lambda p: 'if ( %s , 1o , (/) )' % KTF(p)
G1, F1 = '( G - 1 )', '( F - 1 )'

# ------------------------------------------------------------ koTest: p = G on 5, m = F on 7, bit bounds B <_ N
DATA_KOT = ((STKD('D'), ('G e. NN', 'F e. NN'), ('B e. NN0', 'N e. NN0')), ((LT2('G'), LT2('F', 'N'), 'B <_ N'), (WG('X'), WG('Y'))),
            (DEQ(5, EWg('G', 'X')), DEQ(7, EWg('F', 'Y'))))
TREE_KOT = TREE0('kot', DATA_KOT)
LMK = FRAGS['kot'].lmap()
NZ1 = NFL('if ( %s = 0 , 1o , (/) )' % G1)
CONCL_KOTA = TRI(CS('kot'), CLN(LMK['Z1'], NZ1, UP('D', '3', EWg(G1, DK(3)))), '( 3 x. %s )' % TB('B'))
CONCL_KOT = TRI(CS('kot'), CLN('E', NFL(KOFL('G')), 'D'), '( ( 8 x. %s ) + 1 )' % TB('N'))
add12('tmikota', TREE_KOT, CONCL_KOTA)
add12('tmikot', TREE_KOT, CONCL_KOT)


class Kot(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        gnn, fnn, bn, nn = c0['G e. NN'], c0['F e. NN'], c0['B e. NN0'], c0['N e. NN0']
        xg, yg = c0[WG('X')], c0[WG('Y')]
        gn = w.s([gnn], 'nnnn0d', '( %s -> G e. NN0 )' % ph)
        fn = w.s([fnn], 'nnnn0d', '( %s -> F e. NN0 )' % ph)
        Base.__init__(self, w, ph, T, N8, 'kot', {'5': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xg)), '7': (EWg('F', 'Y'), ewg_(w, ph, 'F', fn, 'Y', yg))})
        s = w.s
        self.gnn, self.fnn, self.gn, self.fn, self.bn, self.nn, self.xg, self.yg = gnn, fnn, gn, fn, bn, nn, xg, yg
        self.cl = Closure(w, ph, {'G': ('NN', gnn), 'F': ('NN', fnn), 'B': ('NN0', bn), 'N': ('NN0', nn)})
        self.cl.atom('( 2 ^ B )'); self.cl.atom('( 2 ^ N )')
        self.g1n = s([gnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, G1))
        self.f1n = s([fnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, F1))
        self.c1 = self.c
        c = self.c
        self.glt, self.flt, self.ble = c[LT2('G')], c[LT2('F', 'N')], c['B <_ N']
        self.g1lt = linarith(w, ph, [self.glt], '%s < ( 2 ^ B )' % G1, closure=self.cl)
        self.f1lt = linarith(w, ph, [self.flt], '%s < ( 2 ^ N )' % F1, closure=self.cl)
        # 2 ^ B <_ 2 ^ N
        u = s([s([s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), s([nn], 'nn0zd', '( %s -> N e. ZZ )' % ph), self.ble], '3jca',
                 '( %s -> ( B e. ZZ /\\ N e. ZZ /\\ B <_ N ) )' % ph), w.inst('eluz2')], 'sylibr', '( %s -> N e. ( ZZ>= ` B ) )' % ph)
        self.pble = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u, w.inst('leexp2a')], 'syl3anc',
                      '( %s -> ( 2 ^ B ) <_ ( 2 ^ N ) )' % ph)
        self.gltn = linarith(w, ph, [self.glt, self.pble], 'G < ( 2 ^ N )', closure=self.cl)
        self.g1ltn = linarith(w, ph, [self.glt, self.pble], '%s < ( 2 ^ N )' % G1, closure=self.cl)
        self.tbb = tmbn(w, ph, 'B', bn); self.tbn = tmbn(w, ph, 'N', nn)
        self.cl.leaf(TB('B'), 'NN0', self.tbb); self.cl.leaf(TB('N'), 'NN0', self.tbn)
        self.tbmono = s([bn, nn, self.ble, w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB('B'), TB('N')))
        self.tb1 = s([s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB('N'))), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB('N')))

    def cp(self, j):
        F_ = FRAGS['kot']
        fn_, cks, en, exn = F_.children[j]
        return PL('P', F_.slot(j)), LMK[exn]


def tmikota():
    lab = 'tmikota'
    T = numtree(TREE_KOT)
    ph = cj(T)
    w = W(lab, 'The prefix of Lean\'s ` koTest ` at the machine: ` dup 5 3 2 ; predNum 3 2 ; isZero 3 2 ` puts ` p - 1 ` on 3 '
               'and sets the flag to ` p - 1 = 0 ` (~ tmidupb , ~ tmiprdbs , ~ tmiizbs ), within ` 3 B b ` steps.')
    s = w.s
    B = Kot(w, ph, T)
    c, mk = B.c, B.mk
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    P, E = B.cp(0)
    V3 = EWg('G', DK(3))
    B.call(R, 'tmidupb', {'K': '5', 'J': '3', 'I': '2', 'F': 'G', 'N': 'B', 'X': 'X', 'P': P, 'E': E},
           {'G e. NN0': B.gn}, [('3', V3, B.g(V3, ewg_(w, ph, 'G', B.gn, DK(3), g('3'))))])
    P, E = B.cp(1)
    V31 = EWg(G1, DK(3))
    B.call(R, 'tmiprdbs', {'K': '3', 'J': '2', 'F': 'G', 'N': 'B', 'X': DK(3), 'P': P, 'E': E},
           {}, [('3', V31, B.g(V31, ewg_(w, ph, G1, B.g1n, DK(3), g('3'))))])
    P, E = B.cp(2)
    assert E == LMK['Z1'], E
    B.call(R, 'tmiizbs', {'K': '3', 'I': '2', 'F': G1, 'N': 'B', 'X': DK(3), 'P': P, 'E': E},
           {'%s e. NN0' % G1: B.g1n, '%s < ( 2 ^ B )' % G1: B.g1lt}, [])
    cur, out = R.normalize(N8)
    assert out == [('3', V31)], out
    BND = '( 3 x. %s )' % TB('B')
    le = linarith(w, ph, [], '%s <_ %s' % (R.n, BND), closure=B.cl)
    st = hrle(w, ph, mk['phm'], R.tri, R.C0, R.cur, R.n, BND, B.cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def tmikot():
    lab = 'tmikot'
    T0 = numtree(TREE_KOT)
    ph = cj(T0)
    w = W(lab, 'Lean\'s ` koTest_runs ` at the machine: after the prefix (~ tmikota ), by cases on ` p - 1 = 0 ` : '
               '` dropNum 3 ; dup 7 6 2 ; predNum 6 2 ; isZero 6 2 ; dropNum 6 ` (the test is ` m - 1 = 0 ` , Lean\'s '
               '` x % 0 = x ` ), or ` dup 7 6 2 ; predNum 6 2 ; modC 6 3 5 4 1 2 ; isZero 6 2 ; dropNum 6 ` (~ tmimodcb ); '
               'the flag is ` if- ( p - 1 = 0 , m - 1 = 0 , ( m - 1 ) mod ( p - 1 ) = 0 ) ` , every stack restored, '
               'within ` 8 B bM + 1 ` steps.')
    s = w.s
    pre0 = s([], 'tmikota', STMTS12['tmikota'])
    pre = s([pre0], 'adantr', '( %s -> %s )' % (ph, CONCL_KOTA))
    C0_, D0_, n0_ = triple_parts(CONCL_KOTA)
    Z1 = LMK['Z1']
    outs = []
    for z in (True, False):
        cc = '%s = 0' % G1 if z else '-. %s = 0' % G1
        T = (T0, cc)
        pc = cj(T)
        B = Kot(w, pc, T)
        c, mk, cl = B.c, B.mk, B.cl
        cst = c[cc]
        tp = s([pre], 'adantr', '( %s -> %s )' % (pc, CONCL_KOTA))
        V0 = '1o' if z else '(/)'
        e0 = s([cst], 'iftrued' if z else 'iffalsed', '( %s -> if ( %s = 0 , 1o , (/) ) = %s )' % (pc, G1, V0))
        t0, C0, D0, n0 = cls_to(w, pc, (tp, C0_, D0_, n0_), 'if ( %s = 0 , 1o , (/) )' % G1, V0, e0)
        N0 = NFL(V0)
        V31 = EWg(G1, DK(3))
        S3 = B.S0.upd('3', V31, B.g(V31, ewg_(w, pc, G1, B.g1n, DK(3), B.S0.vals['3'][2])))
        R = B.run()
        R.S = S3
        R.chain = [('3', V31)]
        R.gam[V31] = B.gam[V31]
        g = lambda k: B.S0.vals[k][2]
        THEN, ELSE = PL(PL('P', 4), 0), PL(PL('P', 9), 0)
        ex = {SSS(N0): B.ss(N0)}
        V6 = EWg('F', DK(6))
        V61 = EWg(F1, DK(6))
        if z:
            ex[STMT(GT(ELSE))] = gotocl(w, pc, mk['tv'], ELSE, B.ex[LAB(ELSE)])
            ex['A. m e. %s ( TMfl ` m ) = 1o' % N0] = A8.ht_nfl(w, pc, '1o')
            B.call(R, 'tm2lbrt', {'A': Z1, 'C': 'TMfl', 'E': THEN, 'Q': GT(ELSE), 'N': N0}, ex, [])
            # dropNum 3 at the class
            P, E = B.cp(3)
            B.call(R, 'tmidropnb', {'K': '3', 'F': G1, 'N': 'B', 'X': DK(3), 'O': V0, 'P': P, 'E': E},
                   {'%s e. NN0' % G1: B.g1n, '%s < ( 2 ^ B )' % G1: B.g1lt}, [('3', DK(3), g('3'))], on=(B.S0, []))
            P, E = B.cp(4)
            B.call(R, 'tmidupb', {'K': '7', 'J': '6', 'I': '2', 'F': 'F', 'N': 'N', 'X': 'Y', 'P': P, 'E': E},
                   {'F e. NN0': B.fn}, [('6', V6, B.g(V6, ewg_(w, pc, 'F', B.fn, DK(6), g('6'))))], pre=(N0, B.ss(N0)))
            Son6, old6 = R.S, list(R.chain)
            P, E = B.cp(5)
            B.call(R, 'tmiprdbs', {'K': '6', 'J': '2', 'F': 'F', 'N': 'N', 'X': DK(6), 'P': P, 'E': E},
                   {}, [('6', V61, B.g(V61, ewg_(w, pc, F1, B.f1n, DK(6), g('6'))))])
            P, E = B.cp(6)
            B.call(R, 'tmiizbs', {'K': '6', 'I': '2', 'F': F1, 'N': 'N', 'X': DK(6), 'P': P, 'E': E},
                   {'%s e. NN0' % F1: B.f1n, '%s < ( 2 ^ N )' % F1: B.f1lt}, [])
            VF = 'if ( %s = 0 , 1o , (/) )' % F1
            P, E = B.cp(7)
            assert E == 'E', E
            B.call(R, 'tmidropnb', {'K': '6', 'F': F1, 'N': 'N', 'X': DK(6), 'O': VF, 'P': P, 'E': E},
                   {'%s e. NN0' % F1: B.f1n, '%s < ( 2 ^ N )' % F1: B.f1lt}, [('6', DK(6), g('6'))], on=(Son6, old6))
            # the flag: if- ( G - 1 = 0 , F - 1 = 0 , .. ) <-> F - 1 = 0
            bi = ifp_bi(w, pc, 'G', cst, True)
            ef = s([bi], 'ifbid', '( %s -> %s = %s )' % (pc, KOFL('G'), VF))
        else:
            ex[STMT(GT(THEN))] = gotocl(w, pc, mk['tv'], THEN, B.ex[LAB(THEN)])
            ex['A. m e. %s -. ( TMfl ` m ) = 1o' % N0] = A8.ht_nfl(w, pc, '(/)')
            B.call(R, 'tm2fbrg', {'A': Z1, 'C': 'TMfl', 'E': ELSE, 'Q': GT(THEN), 'N': N0}, ex, [])
            P, E = B.cp(8)
            B.call(R, 'tmidupb', {'K': '7', 'J': '6', 'I': '2', 'F': 'F', 'N': 'N', 'X': 'Y', 'P': P, 'E': E},
                   {'F e. NN0': B.fn}, [('6', V6, B.g(V6, ewg_(w, pc, 'F', B.fn, DK(6), g('6'))))], pre=(N0, B.ss(N0)))
            P, E = B.cp(9)
            B.call(R, 'tmiprdbs', {'K': '6', 'J': '2', 'F': 'F', 'N': 'N', 'X': DK(6), 'P': P, 'E': E},
                   {}, [('6', V61, B.g(V61, ewg_(w, pc, F1, B.f1n, DK(6), g('6'))))])
            # modC 6 3 5 4 1 2 : ( F - 1 ) mod ( G - 1 ) , G - 1 e. NN
            g1nn = s([s([B.g1n, s([cst], 'neqned', '( %s -> %s =/= 0 )' % (pc, G1))], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (pc, G1, G1)),
                      w.inst('elnnne0')], 'sylibr', '( %s -> %s e. NN )' % (pc, G1))
            MD = '( %s mod %s )' % (F1, G1)
            mdn = s([s([B.f1n], 'nn0zd', '( %s -> %s e. ZZ )' % (pc, F1)), g1nn, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, MD))
            cl.leaf(MD, 'NN0', mdn)
            mdlt = s([s([B.f1n], 'nn0red', '( %s -> %s e. RR )' % (pc, F1)), s([g1nn, w.inst('nnrp')], 'syl', '( %s -> %s e. RR+ )' % (pc, G1)), w.inst('modlt')],
                     'syl2anc', '( %s -> %s < %s )' % (pc, MD, G1))
            mdltn = linarith(w, pc, [mdlt, B.g1ltn], '%s < ( 2 ^ N )' % MD, closure=cl)
            P, E = B.cp(10)
            V6M = EWg(MD, DK(6))
            B.call(R, 'tmimodcb', {'K': '6', 'J': '3', 'I': '5', "I'": '4', 'I"': '1', 'I0': '2', 'F': F1, 'G': G1, 'N': 'N', 'X': DK(6), 'Y': DK(3),
                                   'P': P, 'E': E},
                   {'%s e. NN0' % F1: B.f1n, '%s e. NN' % G1: g1nn, '%s < ( 2 ^ N )' % F1: B.f1lt, '%s < ( 2 ^ N )' % G1: B.g1ltn},
                   [('6', V6M, B.g(V6M, ewg_(w, pc, MD, mdn, DK(6), g('6')))), ('3', DK(3), g('3'))])
            P, E = B.cp(11)
            B.call(R, 'tmiizbs', {'K': '6', 'I': '2', 'F': MD, 'N': 'N', 'X': DK(6), 'P': P, 'E': E},
                   {'%s e. NN0' % MD: mdn, '%s < ( 2 ^ N )' % MD: mdltn}, [])
            VF = 'if ( %s = 0 , 1o , (/) )' % MD
            Son, old = expose(w, pc, B, R, '6')
            P, E = B.cp(12)
            assert E == 'E', E
            B.call(R, 'tmidropnb', {'K': '6', 'F': MD, 'N': 'N', 'X': DK(6), 'O': VF, 'P': P, 'E': E},
                   {'%s e. NN0' % MD: mdn, '%s < ( 2 ^ N )' % MD: mdltn}, [('6', DK(6), g('6'))], on=(Son, old))
            bi = ifp_bi(w, pc, 'G', cst, False)
            ef = s([bi], 'ifbid', '( %s -> %s = %s )' % (pc, KOFL('G'), VF))
        cur, out = R.normalize(N8)
        assert out == [], out
        t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
        assert C1 == D0, (C1, D0)
        t2 = hrseq(w, pc, mk['phm'], t0, t1, C0, D0, D1, n0, n1)
        n2 = '( %s + %s )' % (n0, n1)
        t2, C2, D2, n2 = cls_to(w, pc, (t2, C0, D1, n2), VF, KOFL('G'), s([ef], 'eqcomd', '( %s -> %s = %s )' % (pc, VF, KOFL('G'))))
        BND = '( ( 8 x. %s ) + 1 )' % TB('N')
        le = linarith(w, pc, [B.tbmono, B.tb1], '%s <_ %s' % (n2, BND), closure=cl)
        outs.append(hrle(w, pc, mk['phm'], t2, C2, D2, n2, BND, cl.mem(BND, 'NN0'), le))
    st = s(outs, 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_KOT))
    finish(w, st, lab)
    return w.run()


# ------------------------------------------------------------ the korselt flag lemma
ANDW = lambda tcond: 'A. i e. ( 0 ..^ ( # ` W ) ) %s' % tcond('i')
KT_I = lambda i: KTF('( W ` %s )' % i)
ST_KOFL = ('( ( ( F e. NN0 /\\ W e. Word NN0 ) /\\ A. a e. ran W 2 <_ a ) -> ( 1st ` ( F KorseltTD W ) ) = '
           'if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o ) )' % ANDW(KT_I))


def flag_if(w, ph, cond, X1, iff_st, x2o):
    """( ph -> X1 = if ( if ( cond , 1 , 0 ) = 0 , (/) , 1o ) ) from iff_st : ( ph -> ( X1 = 1o <-> cond ) ) and
    x2o : ( ph -> X1 e. 2o )"""
    s = w.s
    ACC = 'if ( %s , 1 , 0 )' % cond
    OUT = 'if ( %s = 0 , (/) , 1o )' % ACC
    pt = '( %s /\\ %s )' % (ph, cond)
    pn = '( %s /\\ -. %s )' % (ph, cond)
    # true
    a1 = s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = 1 )' % (pt, ACC))
    n1 = s([s([a1], 'eqeq1d', '( %s -> ( %s = 0 <-> 1 = 0 ) )' % (pt, ACC)), s([closed(w, pt, 'ax-1ne0', '1 =/= 0')], 'neneqd', '( %s -> -. 1 = 0 )' % pt)],
           'mtbird', '( %s -> -. %s = 0 )' % (pt, ACC))
    o1 = s([n1], 'iffalsed', '( %s -> %s = 1o )' % (pt, OUT))
    x1 = s([s([], 'simpr', '( %s -> %s )' % (pt, cond)), s([iff_st], 'adantr', '( %s -> ( X1 = 1o <-> %s ) )' % (pt, cond)).replace('X1', X1) if False else
            s([iff_st], 'adantr', '( %s -> ( %s = 1o <-> %s ) )' % (pt, X1, cond))], 'mpbird', '( %s -> %s = 1o )' % (pt, X1))
    t1 = s([x1, o1], 'eqtr4d', '( %s -> %s = %s )' % (pt, X1, OUT))
    # false
    a2 = s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = 0 )' % (pn, ACC))
    o2 = s([a2], 'iftrued', '( %s -> %s = (/) )' % (pn, OUT))
    nx = s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond)), s([iff_st], 'adantr', '( %s -> ( %s = 1o <-> %s ) )' % (pn, X1, cond))], 'mtbird',
           '( %s -> -. %s = 1o )' % (pn, X1))
    x2 = s([s([x2o], 'adantr', '( %s -> %s e. 2o )' % (pn, X1)), s([s([], 'df2o3', '2o = { (/) , 1o }')], 'a1i', '( %s -> 2o = { (/) , 1o } )' % pn)],
           'eleqtrd', '( %s -> %s e. { (/) , 1o } )' % (pn, X1))
    xo = s([x2, w.inst('elpri')], 'syl', '( %s -> ( %s = (/) \\/ %s = 1o ) )' % (pn, X1, X1))
    x0 = s([s([s([xo], 'orcomd', '( %s -> ( %s = 1o \\/ %s = (/) ) )' % (pn, X1, X1))], 'ord', '( %s -> ( -. %s = 1o -> %s = (/) ) )' % (pn, X1, X1)), nx],
           'mpd' if False else 'mpd', '( %s -> %s = (/) )' % (pn, X1)) if False else None
    x0 = s([nx, s([s([xo], 'orcomd', '( %s -> ( %s = 1o \\/ %s = (/) ) )' % (pn, X1, X1))], 'ord', '( %s -> ( -. %s = 1o -> %s = (/) ) )' % (pn, X1, X1))],
           'mpd', '( %s -> %s = (/) )' % (pn, X1))
    t2 = s([x0, o2], 'eqtr4d', '( %s -> %s = %s )' % (pn, X1, OUT))
    return s([t1, t2], 'pm2.61dan', '( %s -> %s = %s )' % (ph, X1, OUT))


def ral_ran(w, ph, tcond, var, ww):
    """( ph -> ( A. var e. ran W tcond(var) <-> A. i e. ( 0 ..^ ( # ` W ) ) tcond( ( W ` i ) ) ) ) (~ ralrn ; ww : W e. Word NN0)"""
    s = w.s
    cg, new = w.wcongr(tcond(var), {var: '( W ` i )'}, '%s = ( W ` i )' % var, {var: s([], 'id', '( %s = ( W ` i ) -> %s = ( W ` i ) )' % (var, var))})
    assert new == tcond('( W ` i )'), new
    fn = s([ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ ( # ` W ) ) )' % ph)
    rr = s([cg], 'ralrn', '( W Fn ( 0 ..^ ( # ` W ) ) -> ( A. %s e. ran W %s <-> A. i e. ( 0 ..^ ( # ` W ) ) %s ) )' % (var, tcond(var), tcond('( W ` i )')))
    return s([fn, rr], 'syl', '( %s -> ( A. %s e. ran W %s <-> A. i e. ( 0 ..^ ( # ` W ) ) %s ) )' % (ph, var, tcond(var), tcond('( W ` i )')))


def t12kofl():
    lab = 't12kofl'
    ph = '( ( F e. NN0 /\\ W e. Word NN0 ) /\\ A. a e. ran W 2 <_ a )'
    w = W(lab, 'The machine\'s korselt flag is Lean\'s and A1b\'s ` ( 1st ( m KorseltTD S ) ) ` when every entry is at least 2 '
               '(then ` p - 1 =/= 0 ` and the test is ` ( m - 1 ) mod ( p - 1 ) = 0 ` ; ~ korselttdfst , ~ ralrn ).')
    s = w.s
    fn = s([], 'simpll', '( %s -> F e. NN0 )' % ph)
    ww = s([], 'simplr', '( %s -> W e. Word NN0 )' % ph)
    r2 = s([], 'simpr', '( %s -> A. a e. ran W 2 <_ a )' % ph)
    KO = '( 1st ` ( F KorseltTD W ) )'
    MT = lambda p: '( ( F - 1 ) mod ( %s - 1 ) ) = 0' % p
    fst = s([fn, ww, w.inst('korselttdfst')], 'syl2anc', '( %s -> ( %s = 1o <-> A. p e. ran W %s ) )' % (ph, KO, MT('p')))
    # under 2 <_ p : KTF( p ) <-> MT( p )
    pp = '( %s /\\ p e. ran W )' % ph
    p2 = s([s([], 'breq2', '( a = p -> ( 2 <_ a <-> 2 <_ p ) )'), s([], 'simpr', '( %s -> p e. ran W )' % pp), s([r2], 'adantr', '( %s -> A. a e. ran W 2 <_ a )' % pp)],
           'rspcdva', '( %s -> 2 <_ p )' % pp)
    pn0 = s([s([s([ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % ph), w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % ph)],
            'adantr', '( %s -> ran W C_ NN0 )' % pp)
    pnn = s([pn0, s([], 'simpr', '( %s -> p e. ran W )' % pp)], 'sseldd', '( %s -> p e. NN0 )' % pp)
    cl = Closure(w, pp, {'p': ('NN0', pnn)})
    ne = linarith(w, pp, [p2], '0 < ( p - 1 )', closure=cl)
    nz = s([s([ne], 'gt0ne0d', '( %s -> ( p - 1 ) =/= 0 )' % pp)], 'neneqd', '( %s -> -. ( p - 1 ) = 0 )' % pp)
    bi = ifp_bi(w, pp, 'p', nz, False)
    rb = s([bi], 'ralbidva', '( %s -> ( A. p e. ran W %s <-> A. p e. ran W %s ) )' % (ph, KTF('p'), MT('p')))
    rr = ral_ran(w, ph, KTF, 'p', ww)
    iff = s([fst, s([s([rb], 'bicomd', '( %s -> ( A. p e. ran W %s <-> A. p e. ran W %s ) )' % (ph, MT('p'), KTF('p'))), rr], 'bitrd',
                     '( %s -> ( A. p e. ran W %s <-> %s ) )' % (ph, MT('p'), ANDW(KT_I)))], 'bitrd', '( %s -> ( %s = 1o <-> %s ) )' % (ph, KO, ANDW(KT_I)))
    k2 = s([s([fn, ww, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( F KorseltTD W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp1st')], 'syl',
           '( %s -> %s e. 2o )' % (ph, KO))
    w.qed([flag_if(w, ph, ANDW(KT_I), KO, iff, k2), w.inst('biid')], 'mpbi', ST_KOFL)
    return w.run()


# ------------------------------------------------------------ the loop: koa = accLoopF koBody at the family
LG = '( encNatGam o. W )'
NLG = '( # ` %s )' % LG
DOM = '( 0 ... %s )' % NLG
EB = lambda k: '( encListB ` ( %s substr <. %s , %s >. ) )' % (LG, k, NLG)
C5 = lambda k: '( %s ++ R )' % EB(k)
ACC = lambda k: 'if ( A. i e. ( 0 ..^ %s ) %s , 1 , 0 )' % (k, KT_I('i'))
E1 = lambda k: EWg(ACC(k), DK(1))
PB = lambda k: UPS('D', ('1', E1(k)), ('5', C5(k)))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
PV = "P'"
DATA_KOL = ((STKD('D'), ('W e. Word NN0', 'F e. NN0'), ('B e. NN0', 'N e. NN0')),
            ((RALB('W', 'B'), LT2('F', 'N'), 'B <_ N'), ('1 <_ F', 'A. a e. ran W 1 <_ a'), (WG('R'), WG('Y'))),
            (DEQ(5, ENCL('W', 'R')), DEQ(7, EWg('F', 'Y'))))
TREE_KOA = TREE0('koa', DATA_KOL)
PSI_T = (TREE_KOA, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
YC = '( ( ; 1 1 x. %s ) + 2 )' % TB('N')
YF = '( i e. NN0 |-> %s )' % YC
UC = '( %s x. ( %s + 2 ) )' % (NLG, YC)
LMA = FRAGS['koa'].lmap()
GM_KO = {'A0': LMA['Z1'], 'P0': LMA['Z2'], 'P1': LMA['Z3'], 'A': LMA['Z4'], "A'": LMA['Y1'], 'A"': LMA['Z5'], "E'": LMA['Z6'], 'E"': LMA['Z7'],
         'Q': PL('P', 8), 'Q1': PL('P', 9), 'E': 'E', 'L': LG, 'R': 'R', 'D': 'D', 'P': PV, 'Y': YF, 'U': UC, 'G': ACC(NLG), 'B': 'N'}
_GA, _GC = split_imp(STMTS12['tmiacl'])
GTREE = tsub(parse_conj(_GA), GM_KO)
GCONCL = tsub_text(_GC, GM_KO)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in _fl if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
P0EQ = [t for t in _fl if t.startswith('( %s ` 0 ) = ' % PV)][0]
PNEQ = [t for t in _fl if t.startswith('( %s ` %s ) = ' % (PV, NLG))][0]
SUMLE = [t for t in _fl if t.startswith('sum_ ')][0]
# the body statement: the triple with the literal cost YC
HOARE_YC = PERB.split(' /\\ ', 1)[1][:-2].rsplit(' , ', 1)[0] + ' , %s >.' % YC
add12('tmikoai', (PSI_T, 'j e. ( 0 ..^ %s )' % NLG), HOARE_YC)
add12('tmikoat', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FTY, FCOL, P0EQ, PNEQ))
KOAC = '( ( ( # ` W ) x. ( %s + 2 ) ) + ( ( 2 x. %s ) + 6 ) )' % (YC, TB('N'))
KOFLAG = 'if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o )' % ANDW(KT_I)
CONCL_KOAL = TRI(CS('koa'), CLN('E', NFL(KOFLAG), UP('D', '5', 'R')), KOAC)
add12('tmikoal', PSI_T, CONCL_KOAL)
# korseltTDF_runs (Lean, the flag the machine's; tmiverb identifies it under allPrime)
DATA_KO = ((STKD('D'), ('W e. Word NN0', 'F e. NN0'), ('B e. NN0', 'N e. NN0')),
           ((RALB('W', 'B'), LT2('F', 'N'), 'B <_ N'), ('1 <_ F', 'A. a e. ran W 1 <_ a'), (WG('X'), WG('Y'))),
           (DEQ(4, ENCL('W', 'X')), DEQ(7, EWg('F', 'Y'))))
TREE_KO = TREE0('ko', DATA_KO)
CONCL_KO = TRI(CS('ko'), CLN('E', NFL(KOFLAG), 'D'), '( ( ( 2nd ` ( F KorseltTD W ) ) + 1 ) x. ( ; 1 6 x. %s ) )' % TB('N'))
add12('tmiko', TREE_KO, CONCL_KO)


class Koa(Base):
    def __init__(self, w, ph, T, fname='koa'):
        c0 = Ctx(w, ph, T)
        ww, fn, bn, nn = c0['W e. Word NN0'], c0['F e. NN0'], c0['B e. NN0'], c0['N e. NN0']
        rw, yw = c0[WG('R')], c0[WG('Y')]
        eqs = {'5': (ENCL('W', 'R'), enclg(w, ph, 'W', ww, 'R', rw)), '7': (EWg('F', 'Y'), ewg_(w, ph, 'F', fn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, fname, eqs)
        s = w.s
        self.ww, self.fn, self.bn, self.nn, self.rw, self.yw = ww, fn, bn, nn, rw, yw
        c = self.c
        self.f1 = c['1 <_ F']
        self.fnn = s([s([fn, self.f1], 'jca', '( %s -> ( F e. NN0 /\\ 1 <_ F ) )' % ph), w.inst('elnnnn0c')], 'sylibr', '( %s -> F e. NN )' % ph)
        self.lgw = s([ww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([ww, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = ( # ` W ) )' % (ph, NLG))
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
        self.nlg = s([self.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
        self.cl = Closure(w, ph, {'F': ('NN0', fn), 'B': ('NN0', bn), 'N': ('NN0', nn)})
        self.cl.leaf('( # ` W )', 'NN0', self.nw)
        self.cl.leaf(NLG, 'NN0', self.nlg)
        self.cl.leaf(TB('N'), 'NN0', tmbn(w, ph, 'N', nn))
        self.cl.leaf(TB('B'), 'NN0', tmbn(w, ph, 'B', bn))
        self.d1 = self.S0.vals['1'][2]
        self.tb1 = s([s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB('N'))), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB('N')))
        self.tbmono = s([bn, nn, c['B <_ N'], w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB('B'), TB('N')))

    def accn(self, k):
        """( ph -> ACC( k ) e. NN0 ) and ( ph -> ACC( k ) <_ 1 )"""
        w, ph, s = self.w, self.ph, self.w.s
        a = s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ACC(k)))
        cond = 'A. i e. ( 0 ..^ %s ) %s' % (k, KT_I('i'))
        pt, pn = '( %s /\\ %s )' % (ph, cond), '( %s /\\ -. %s )' % (ph, cond)
        l1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = 1 )' % (pt, ACC(k))), closed(w, pt, '1le1', '1 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pt, ACC(k)))
        l2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = 0 )' % (pn, ACC(k))), closed(w, pn, '0le1', '0 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pn, ACC(k)))
        return a, s([l1, l2], 'pm2.61dan', '( %s -> %s <_ 1 )' % (ph, ACC(k)))

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        an, _ = self.accn(k)
        g1 = self.g(E1(k), ewg_(w, ph, ACC(k), an, DK(1), self.d1))
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g5 = self.g(C5(k), wgcat(w, ph, EB(k), 'R', eb, self.rw))
        return self.S0.upd('1', E1(k), g1).upd('5', C5(k), g5)


def ifo_bi(w, ph, tj):
    """( ph -> ( if ( tj , 1o , (/) ) = 1o <-> tj ) )"""
    s = w.s
    O = 'if ( %s , 1o , (/) )' % tj
    pt, pn = '( %s /\\ %s )' % (ph, tj), '( %s /\\ -. %s )' % (ph, tj)
    a = s([s([], 'simpr', '( %s -> %s )' % (pt, tj))], 'iftrued', '( %s -> %s = 1o )' % (pt, O))
    t1 = s([a, s([], 'simpr', '( %s -> %s )' % (pt, tj))], '2thd', '( %s -> ( %s = 1o <-> %s ) )' % (pt, O, tj))
    b = s([s([], 'simpr', '( %s -> -. %s )' % (pn, tj))], 'iffalsed', '( %s -> %s = (/) )' % (pn, O))
    n0 = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
    nb = s([s([n0], 'a1i', '( %s -> -. (/) = 1o )' % pn), s([b], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (pn, O))], 'mtbird',
           '( %s -> -. %s = 1o )' % (pn, O))
    t2 = s([nb, s([], 'simpr', '( %s -> -. %s )' % (pn, tj))], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (pn, O, tj))
    return s([t1, t2], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (ph, O, tj))


def acc_step(w, ph, jn, jn0, tcond, ocond, obi, j='j'):
    """( ph -> if ( ocond , ACC( j ) , 0 ) = ACC( j + 1 ) ) with ACC( k ) = if ( A. i e. ( 0 ..^ k ) tcond( i ) , 1 , 0 ) ,
    obi : ( ph -> ( ocond <-> tcond( j ) ) ) ; jn : ( ph -> j e. NN0 ) , jn0 : ( ph -> j e. ( ZZ>= ` 0 ) )"""
    s = w.s
    tj = tcond(j)
    AND = lambda k: 'A. i e. ( 0 ..^ %s ) %s' % (k, tcond('i'))
    ACCk = lambda k: 'if ( %s , 1 , 0 )' % AND(k)
    J1 = '( %s + 1 )' % j
    LHS = 'if ( %s , %s , 0 )' % (ocond, ACCk(j))
    sp = s([jn0, w.inst('fzosplitsn')], 'syl', '( %s -> ( 0 ..^ %s ) = ( ( 0 ..^ %s ) u. { %s } ) )' % (ph, J1, j, j))
    r1 = s([sp], 'raleqdv', '( %s -> ( %s <-> A. i e. ( ( 0 ..^ %s ) u. { %s } ) %s ) )' % (ph, AND(J1), j, j, tcond('i')))
    cg, new = w.wcongr(tcond('i'), {'i': j}, 'i = %s' % j, {'i': s([], 'id', '( i = %s -> i = %s )' % (j, j))})
    assert new == tj, new
    r2 = s([jn, s([cg], 'ralunsn', '( %s e. NN0 -> ( A. i e. ( ( 0 ..^ %s ) u. { %s } ) %s <-> ( %s /\\ %s ) ) )' % (j, j, j, tcond('i'), AND(j), tj))],
           'syl', '( %s -> ( A. i e. ( ( 0 ..^ %s ) u. { %s } ) %s <-> ( %s /\\ %s ) ) )' % (ph, j, j, tcond('i'), AND(j), tj))
    bi = s([r1, r2], 'bitrd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ph, AND(J1), AND(j), tj))
    pt, pn = '( %s /\\ %s )' % (ph, tj), '( %s /\\ -. %s )' % (ph, tj)
    o1 = s([s([], 'simpr', '( %s -> %s )' % (pt, tj)), s([obi], 'adantr', '( %s -> ( %s <-> %s ) )' % (pt, ocond, tj))], 'mpbird', '( %s -> %s )' % (pt, ocond))
    l1 = s([o1], 'iftrued', '( %s -> %s = %s )' % (pt, LHS, ACCk(j)))
    b1 = s([s([bi], 'adantr', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (pt, AND(J1), AND(j), tj)),
            s([s([], 'simpr', '( %s -> %s )' % (pt, tj))], 'biantrud', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (pt, AND(j), AND(j), tj))], 'bitr4d',
           '( %s -> ( %s <-> %s ) )' % (pt, AND(J1), AND(j)))
    a1 = s([b1], 'ifbid', '( %s -> %s = %s )' % (pt, ACCk(J1), ACCk(j)))
    t1 = s([l1, a1], 'eqtr4d', '( %s -> %s = %s )' % (pt, LHS, ACCk(J1)))
    o2 = s([s([], 'simpr', '( %s -> -. %s )' % (pn, tj)), s([obi], 'adantr', '( %s -> ( %s <-> %s ) )' % (pn, ocond, tj))], 'mtbird', '( %s -> -. %s )' % (pn, ocond))
    l2 = s([o2], 'iffalsed', '( %s -> %s = 0 )' % (pn, LHS))
    na = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, tj))], 'intnand', '( %s -> -. ( %s /\\ %s ) )' % (pn, AND(j), tj)),
            s([bi], 'adantr', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (pn, AND(J1), AND(j), tj))], 'mtbird', '( %s -> -. %s )' % (pn, AND(J1)))
    a2 = s([na], 'iffalsed', '( %s -> %s = 0 )' % (pn, ACCk(J1)))
    t2 = s([l2, a2], 'eqtr4d', '( %s -> %s = %s )' % (pn, LHS, ACCk(J1)))
    return s([t1, t2], 'pm2.61dan', '( %s -> %s = %s )' % (ph, LHS, ACCk(J1)))


def tmikoai():
    lab = 'tmikoai'
    T = numtree((PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    ph = cj(T)
    w = W(lab, 'One entry of Lean\'s ` korseltTDF ` loop at the machine ( ` koBody_runs ` ): along the family of the '
               'accumulator, ` koTest ` (~ tmikot ) on the entry ` p ` at the top of 5 and ` m ` on 7, ` accAnd ` (~ tmiaca ), '
               '` dropNum 5 ` (~ tmidropb ), within ` 11 B bM + 2 ` steps.')
    s = w.s
    B = Koa(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    jj = c['j e. ( 0 ..^ %s )' % NLG]
    jW = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` W ) ) )' % (ph, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` W ) ) )' % ph)
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    J1 = '( j + 1 )'
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (ph, J1, DOM))
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % ph)
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j'))
    PT = '( %s ` j )' % PV
    # ( PT ` 5 ) = EW( ( W ` j ) , C5( j + 1 ) )
    WJ = '( W ` j )'
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % ph), jW, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (ph, LG, WJ))
    wjn = s([B.ww, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WJ))
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = s([lgj, encw(w, ph, WJ, wjn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG))
    ca1 = s([egj, g4, B.rw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, B.rw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ R ) = ( <" 4 "> ++ %s ) )' % (ph, EB(J1), C5(J1)))
    r1 = s([s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) )' % (ph, C5('j'), LG, EB(J1))), ca1], 'eqtrd',
           '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ph, C5('j'), LG, EB(J1)))
    V5 = EWg(WJ, C5(J1))
    r2 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) = %s )' % (ph, LG, EB(J1), V5))
    iv = s([SJ.vals['5'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, C5('j'), V5))], 'eqtrd', '( %s -> ( %s ` 5 ) = %s )' % (ph, PT, V5))
    g51 = B.g(C5(J1), wgcat(w, ph, EB(J1), 'R', eb1, B.rw))
    # the entry's facts: 1 <_ ( W ` j ) , ( W ` j ) < 2 ^ B
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ ( # ` W ) ) )' % ph), jW, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran W )' % (ph, WJ))
    wjlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ B ) <-> %s < ( 2 ^ B ) ) )' % (WJ, WJ)), wr, c[RALB('W', 'B')]], 'rspcdva', '( %s -> %s < ( 2 ^ B ) )' % (ph, WJ))
    wj1 = s([s([], 'breq2', '( a = %s -> ( 1 <_ a <-> 1 <_ %s ) )' % (WJ, WJ)), wr, c['A. a e. ran W 1 <_ a']], 'rspcdva', '( %s -> 1 <_ %s )' % (ph, WJ))
    wjnn = s([s([wjn, wj1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (ph, WJ, WJ)), w.inst('elnnnn0c')], 'sylibr', '( %s -> %s e. NN )' % (ph, WJ))
    accj, accle = B.accn('j')
    cl.leaf(ACC('j'), 'NN0', accj)
    cl.atom('( 2 ^ B )'); cl.atom('( 2 ^ N )')
    # ACC( j ) < 2 ^ N : ACC <_ 1 <_ F < 2 ^ N
    acclt = linarith(w, ph, [accle, B.f1, c[LT2('F', 'N')]], '%s < ( 2 ^ N )' % ACC('j'), closure=cl)
    # the Run at the family's stacks with the 5 column exposed
    B.deep('koa', 0)
    v2 = dict(SJ.vals)
    v2['5'] = (V5, iv, B.g(V5, ewg_(w, ph, WJ, wjn, C5(J1), g51)))
    SJ2 = Stacks(w, ph, mk, SJ.D, SJ.memb, SJ.ne, v2)
    R = B.run(SJ2)
    lm_kob = FRAGS['kob'].lmap(PL('P', 7), LMA['Z5'])
    P7 = PL('P', 7)
    # 1. koTest
    B.call(R, 'tmikot', {'G': WJ, 'F': 'F', 'B': 'B', 'N': 'N', 'X': C5(J1), 'Y': 'Y', 'P': PL(P7, 0), 'E': lm_kob['Y2']},
           {'%s e. NN' % WJ: wjnn, 'F e. NN': B.fnn, '%s < ( 2 ^ B )' % WJ: wjlt, WG(C5(J1)): g51}, [])
    O = KOFL(WJ)
    # 2. accAnd
    IFO = 'if ( %s = 1o , %s , 0 )' % (O, ACC('j'))
    ifon = s([accj, closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, IFO))
    EI = EWg(IFO, DK(1))
    B.call(R, 'tmiaca', {'A': ACC('j'), 'B': 'N', 'X': DK(1), 'O': O, 'P': PL(P7, 1), 'E': lm_kob['Y3']},
           {'%s e. NN0' % ACC('j'): accj, '%s < ( 2 ^ N )' % ACC('j'): acclt, WG(DK(1)): B.d1}, [('1', EI, B.g(EI, ewg_(w, ph, IFO, ifon, DK(1), B.d1)))])
    # 3. dropNum 5
    Son, old = expose(w, ph, B, R, '5')
    B.call(R, 'tmidropb', {'K': '5', 'F': WJ, 'N': 'B', 'X': C5(J1), 'P': PL(P7, 2), 'E': LMA['Z5']},
           {'%s e. NN0' % WJ: wjn, '%s < ( 2 ^ B )' % WJ: wjlt, WG(C5(J1)): g51}, [('5', C5(J1), g51)], on=(Son, old))
    e, nrm, out2 = renorm(w, ph, B, R, [('1', E1('j')), ('5', C5('j'))], N8, PT=PT, pv=pvj)
    assert out2 == [('1', EI), ('5', C5(J1))], out2
    # the accumulator step
    jn0 = s([jn, w.inst('elnn0uz')], 'sylib', '( %s -> j e. ( ZZ>= ` 0 ) )' % ph)
    ast = acc_step(w, ph, jn, jn0, KT_I, '%s = 1o' % O, ifo_bi(w, ph, KT_I('j')))
    r_, nrm2 = w.rewrite(nrm, {IFO: (ACC(J1), ast)}, ph)
    assert nrm2 == PB(J1), '\n%s\n%s' % (nrm2, PB(J1))
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1))
    D0 = triple_D(R.cur)
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, D0, PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LMA['Z5'], S, deq, D0, '( %s ` %s )' % (PV, J1)))
    le = linarith(w, ph, [B.tbmono], '%s <_ %s' % (n, YC), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, YC, cl.mem(YC, 'NN0'), le)
    assert TRI(C, D, YC) == HOARE_YC, '\n%s\n%s' % (TRI(C, D, YC), HOARE_YC)
    finish(w, st, lab)
    return w.run()


def tmikoat():
    lab = 'tmikoat'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` korseltTDF ` loop at the machine: the family of the accumulator is a stack family '
               'whose 5 column is the rest of the copied list, at 0 it is the stacks with the accumulator ` 1 ` pushed, at the '
               'end the accumulator is the conjunction of the tests and the list\'s ` bra ` remains.')
    s = w.s
    B = Koa(w, ph, T)
    c, mk = B.c, B.mk
    fam = c['%s = %s' % (PV, PF)]
    ph0t = (TREE_KOA, NUMS)
    ph0 = cj(ph0t)
    # typing
    TK = (ph0t, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Koa(w, pk, TK)
    Sk = Bk.pbst('k')
    fm = s([Sk.memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    j0 = s([c[cj(TREE_KOA)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fm2 = s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)), fm2],
            'mpbird', '( %s -> %s )' % (ph, FTY))
    # the 5 column
    TJ = (T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Koa(w, pj, TJ)
    jz = Bj.c['j e. %s' % DOM]
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', jz, Bj.pbst('j'))
    col = s([SJ.vals['5'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    # the value at 0 : ACC( 0 ) = 1 , C5( 0 ) = ( D ` 5 )
    z0 = s([B.nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0'))
    a0 = s([s([s([], 'ral0', 'A. i e. (/) %s' % KT_I('i')), s([s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'raleqi',
                                                          '( A. i e. ( 0 ..^ 0 ) %s <-> A. i e. (/) %s )' % (KT_I('i'), KT_I('i')))], 'mpbir',
              'A. i e. ( 0 ..^ 0 ) %s' % KT_I('i'))], 'iftruei', '%s = 1' % ACC('0'))
    e1 = s([s([s([a0], 'a1i', '( %s -> %s = 1 )' % (ph, ACC('0')))], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` 1 ) )' % (ph, ACC('0')))], 'oveq1d',
           '( %s -> %s = %s )' % (ph, E1('0'), EWg('1', DK(1))))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le_ = s([B.ww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` W ) = ( encListB ` %s ) )' % (ph, LG))
    e5 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le_], 'eqtr4d', '( %s -> %s = ( encList ` W ) )' % (ph, EB('0')))],
           'oveq1d', '( %s -> %s = %s )' % (ph, C5('0'), ENCL('W', 'R')))
    e5b = s([e5, s([c[DEQ(5, ENCL('W', 'R'))]], 'eqcomd', '( %s -> %s = ( D ` 5 ) )' % (ph, ENCL('W', 'R')))], 'eqtrd', '( %s -> %s = ( D ` 5 ) )' % (ph, C5('0')))
    rr, xx = w.rewrite(PB('0'), {E1('0'): (EWg('1', DK(1)), e1), C5('0'): ('( D ` 5 )', e5b)}, ph)
    assert xx == UPS('D', ('1', EWg('1', DK(1))), ('5', DK(5))), xx
    B.g(EWg('1', DK(1)), ewg_(w, ph, '1', closed(w, ph, '1nn0', '1 e. NN0'), DK(1), B.d1))
    nst, outn = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, [('1', EWg('1', DK(1))), ('5', DK(5))], B.gam, N8)
    assert outn == [('1', EWg('1', DK(1)))], outn
    p0 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx)), nst], 'eqtrd', '( %s -> %s )' % (ph, P0EQ))
    # the value at the end
    nz = s([B.nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    pvN, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, NLG, nz, B.pbst(NLG))
    DR = '( %s substr <. %s , %s >. )' % (LG, NLG, NLG)
    e2 = s([s([closed(w, ph, 'swrd00', '%s = (/)' % DR)], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (ph, DR)),
            closed(w, ph, 'tm2lencb0', '( encListB ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encListB ` %s ) = <" 2 "> )' % (ph, DR))
    e5n = s([e2], 'oveq1d', '( %s -> %s = ( <" 2 "> ++ R ) )' % (ph, C5(NLG)))
    rN, xN = w.rewrite(PB(NLG), {C5(NLG): ('( <" 2 "> ++ R )', e5n)}, ph)
    pn = s([pvN, rN], 'eqtrd', '( %s -> %s )' % (ph, PNEQ))
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([p0, pn], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ph, FTY, FCOL, P0EQ, PNEQ))
    finish(w, st, lab)
    return w.run()


def tmikoal():
    lab = 'tmikoal'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` accLoopF koBody ` at the machine: ~ tmiacl at the family of the accumulator ( ` P\' ` a letter; the '
               'entries by ~ tmikoai , the frame by ~ tmikoat ); the flag is the conjunction of the machine\'s korselt tests over '
               'the list, the list\'s ` bra ` is gone from 5.')
    s = w.s
    B = Koa(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    ex = dict(B.ex)
    B.deep('koa', 0)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmikoat', STMTS12['tmikoat']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))
    ex[FTY] = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    ex[P0EQ] = s([a2], 'simpld', '( %s -> %s )' % (ph, P0EQ))
    ex[PNEQ] = s([a2], 'simprd', '( %s -> %s )' % (ph, PNEQ))
    # PER: the body theorem with the cost ( YF ` j ) = YC , under ( PSI /\ j e. ( 0 ..^ NLG ) )
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (PSI, NLG)
    bj = s([], 'tmikoai', STMTS12['tmikoai'])
    jn = s([s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NLG)), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
    cj_ = Ctx(w, pj, (PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    nnj = cj_['N e. NN0']
    clj = Closure(w, pj, {'N': ('NN0', nnj)})
    clj.leaf(TB('N'), 'NN0', tmbn(w, pj, 'N', nnj))
    ycn = clj.mem(YC, 'NN0')
    yj = s([jn, ycn, s([s([], 'eqidd', '( i = j -> %s = %s )' % (YC, YC)), s([], 'eqid', '%s = %s' % (YF, YF))], 'fvmptg',
                        '( ( j e. NN0 /\\ %s e. NN0 ) -> ( %s ` j ) = %s )' % (YC, YF, YC))], 'syl2anc', '( %s -> ( %s ` j ) = %s )' % (pj, YF, YC))
    Cb, Db, nb = triple_parts(HOARE_YC)
    tb, _, _, _ = hrrw(w, pj, bj, Cb, Db, nb, neq=s([yj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (pj, YC, YF)))
    yjn = s([yj, ycn], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (pj, YF))
    perb = s([yjn, tb], 'jca', '( %s -> %s )' % (pj, PERB))
    ex[PER] = lift_from(w, PSI, ph, s([perb], 'ralrimiva', '( %s -> %s )' % (PSI, PER)))
    # the sum: sum_ j ( ( YF ` j ) + 2 ) = NLG x. ( YC + 2 ) = UC
    pj2 = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLG)
    jn2 = s([s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj2, NLG)), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj2)
    yj2 = s([jn2, s([cl.mem(YC, 'NN0')], 'adantr', '( %s -> %s e. NN0 )' % (pj2, YC)),
             s([s([], 'eqidd', '( i = j -> %s = %s )' % (YC, YC)), s([], 'eqid', '%s = %s' % (YF, YF))], 'fvmptg',
               '( ( j e. NN0 /\\ %s e. NN0 ) -> ( %s ` j ) = %s )' % (YC, YF, YC))], 'syl2anc', '( %s -> ( %s ` j ) = %s )' % (pj2, YF, YC))
    yjc = s([yj2], 'oveq1d', '( %s -> ( ( %s ` j ) + 2 ) = ( %s + 2 ) )' % (pj2, YF, YC))
    SJ_ = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NLG, YF)
    se = s([yjc], 'sumeq2dv', '( %s -> %s = sum_ j e. ( 0 ..^ %s ) ( %s + 2 ) )' % (ph, SJ_, NLG, YC))
    fc = s([s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NLG)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NLG)), cl.mem('( %s + 2 )' % YC, 'CC'),
            w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ j e. ( 0 ..^ %s ) ( %s + 2 ) = ( ( # ` ( 0 ..^ %s ) ) x. ( %s + 2 ) ) )' % (ph, NLG, YC, NLG, YC))
    hf = s([s([B.nlg, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (ph, NLG, NLG))], 'oveq1d',
           '( %s -> ( ( # ` ( 0 ..^ %s ) ) x. ( %s + 2 ) ) = %s )' % (ph, NLG, YC, UC))
    seq_ = s([se, fc, hf], '3eqtrd', '( %s -> %s = %s )' % (ph, SJ_, UC))
    sumr = s([s([seq_, cl.mem(UC, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, SJ_))], 'nn0red', '( %s -> %s e. RR )' % (ph, SJ_))
    ex[SUMLE] = s([sumr, seq_], 'eqled', '( %s -> %s )' % (ph, SUMLE))
    # the remaining leaves: L , G , B := N , U
    accN, accleN = B.accn(NLG)
    cl.leaf(ACC(NLG), 'NN0', accN)
    ex['%s e. NN0' % ACC(NLG)] = accN
    ex['%s < ( 2 ^ N )' % ACC(NLG)] = linarith(w, ph, [accleN, B.f1, c[LT2('F', 'N')]], '%s < ( 2 ^ N )' % ACC(NLG), closure=cl)
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex['%s e. NN0' % UC] = cl.mem(UC, 'NN0')
    ex[WG('R')] = B.rw
    st = Bld(w, ph, c, ex)(GTREE)
    st2 = s([st, w.inst('tmiacl')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    C0, D0, n0 = triple_parts(GCONCL)
    rd, D1 = w.rewrite(D0, {NLG: ('( # ` W )', B.lg)}, ph)
    rn, n1 = w.rewrite(n0, {NLG: ('( # ` W )', B.lg)}, ph)
    t, C, D, n = hrrw(w, ph, st2, C0, D0, n0, deq=rd, neq=rn)
    assert TRI(C, D, n) == CONCL_KOAL, '\n%s\n%s' % (TRI(C, D, n), CONCL_KOAL)
    finish(w, t, lab)
    return w.run()


def tmiko():
    lab = 'tmiko'
    T = numtree(TREE_KO)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` korseltTDF_runs ` at the machine: ` copyList 4 5 2 3 ` (~ tmilcpyb ) then the accumulator loop '
               '(~ tmikoal ); every stack restored, the flag the conjunction of the machine\'s korselt tests (equal to '
               '` ( 1st ( m KorseltTD S ) ) ` on lists of numbers at least 2, ~ t12kofl ), within '
               '` ( ( korseltTD m S ).2 + 1 ) 16 B bM ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    ww, fn, bn, nn = c0['W e. Word NN0'], c0['F e. NN0'], c0['B e. NN0'], c0['N e. NN0']
    xw, yw = c0[WG('X')], c0[WG('Y')]
    B = Base(w, ph, T, N8, 'ko', {'4': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), '7': (EWg('F', 'Y'), ewg_(w, ph, 'F', fn, 'Y', yw))})
    c, mk = B.c, B.mk
    g = lambda k: B.S0.vals[k][2]
    LM = FRAGS['ko'].lmap()
    R = B.run()
    V5 = ENCL('W', DK(5))
    B.call(R, 'tmilcpyb', {'K': '4', 'J': '5', 'I': '2', "I'": '3', 'L': 'W', 'R': 'X', 'B': 'B', 'P': PL('P', 0), 'E': LM['Y2']},
           {}, [('5', V5, B.g(V5, enclg(w, ph, 'W', ww, DK(5), g('5'))))])
    PFi = tsub_text(PF, {'D': R.S.D, 'R': DK(5)})
    B.call(R, 'tmikoal', {'W': 'W', 'F': 'F', 'B': 'B', 'N': 'N', 'R': DK(5), 'Y': 'Y', PV: PFi, 'P': PL('P', 1), 'E': 'E'},
           {WG(DK(5)): g('5'), '%s = %s' % (PFi, PFi): s([s([], 'eqid', '%s = %s' % (PFi, PFi))], 'a1i', '( %s -> %s = %s )' % (ph, PFi, PFi))},
           [('5', DK(5), g('5'))])
    cur, out = R.normalize(N8)
    assert out == [], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    cl = Closure(w, ph, {'B': ('NN0', bn), 'N': ('NN0', nn)})
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl.leaf('( # ` W )', 'NN0', nw)
    cl.leaf(TB('B'), 'NN0', tmbn(w, ph, 'B', bn))
    cl.leaf(TB('N'), 'NN0', tmbn(w, ph, 'N', nn))
    mono = s([bn, nn, c['B <_ N'], w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB('B'), TB('N')))
    tb8 = s([nn, closed(w, ph, '8nn0', '8 e. NN0'), s([num.le_lit(w, '8', '; 6 4')], 'a1i', '( %s -> 8 <_ ; 6 4 )' % ph), w.inst('tmblin')], 'syl3anc',
            '( %s -> ( 8 x. ( N + 2 ) ) <_ %s )' % (ph, TB('N')))
    KC = '( 2nd ` ( F KorseltTD W ) )'
    kc = s([fn, ww, w.inst('korselttdcost')], 'syl2anc', '( %s -> %s = ( # ` W ) )' % (ph, KC))
    cl.leaf(KC, 'NN0', s([kc, nw], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, KC)))
    BND = triple_parts(CONCL_KO)[2]
    le = linarith(w, ph, [mono, tb8, kc, cl.ge0('N'), cl.ge0('( # ` W )')], '%s <_ %s' % (n, BND), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


import num

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
