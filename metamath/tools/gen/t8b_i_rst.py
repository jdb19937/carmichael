"""T8b: resStep at the machine (Lean ` resStep_runs ` ) on its installation predicate TMIrst.

  tmirsta   the prefix ` moveEntry nL np s ; dup np t s ; dup nL s t ; cmpFrag t s ` into the compare class
  tmirstb   the branch ` cmp = lt ` : ` dup ; sub ; moveEntry ; dup ; sub ; moveEntry ; moveEntry `
  tmirstc   the other branch ` dup nL t s ; sub np t s np `
  tmirst    resStep_runs: ~ tm2frst with the two branches by cases, the final ` moveEntry np nL s `

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_i_rst.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, nlinarith
from t7lib import mval, ifex_closed, not1o
from t7_e_cmp import lamty
from t8b_e_sin import L_

SEL = sys.argv[1:]
K4_ = ['K', 'J', 'I', "I'"]
IB = lambda l: '( inclBool o. %s )' % l
WBc = BW('L"', 'X')
WA = BW("L'", WBc)
S1 = "( ( L' subTrunc L ) ` (/) )"
S2 = '( ( L" subTrunc %s ) ` (/) )' % S1
S3 = "( ( L subTrunc L' ) ` (/) )"
DJ, DI, DIp = '( D ` J )', '( D ` I )', "( D ` I' )"
DP = UP(UP('D', 'K', WA), 'J', BW('L', DJ))
CMPC = "{ h e. TMSt | ( TMcmp ` h ) = ( ( toNat ` L ) Ncmp ( toNat ` L' ) ) }"
T1B = '( ( 7 x. H ) + ; 1 6 )'
T2B = '( ( ; 1 6 x. H ) + ; 3 2 )'
T0B = '( ( 5 x. H ) + ; 1 0 )'
TPB = '( ( 2 x. H ) + 4 )'
DB = lambda Sx: UP(UP('D', 'K', WA), 'J', BW(Sx, DJ))
ST_A = '( %s -> %s )' % (cj(TREE_RST), TRI(CEN('rst', 'D'), CLN('( P ` 0 )', CMPC, DP), T1B))
ST_B = '( %s -> %s )' % (cj(TREE_RST), TRI(CLN(PL(PL('P', 5), 0), S, DP), CLN(PL(PL('P', 14), 0), S, DB(S2)), T2B))
ST_C = '( %s -> %s )' % (cj(TREE_RST), TRI(CLN(PL(PL('P', 12), 0), S, DP), CLN(PL(PL('P', 14), 0), S, DB(S3)), T0B))


class Fx:
    """the facts shared by the pieces"""
    def __init__(self, w, ph):
        self.w, self.ph = w, ph
        c, mk, ne, ex = hsetup(w, ph, TREE_RST, K4_, 'rst')
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        s = w.s
        self.dd = c[STKD('D')]
        g = {}
        for l in ('L', "L'", 'L"'):
            g[l] = c['%s e. Word 2o' % l]
        z2 = closed(w, ph, '0el2o', '(/) e. 2o')
        g[S1] = s([g["L'"], g['L'], z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, S1))
        g[S2] = s([g['L"'], g[S1], z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, S2))
        g[S3] = s([g['L'], g["L'"], z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, S3))
        self.g2 = g
        self.gb = {l: s([g[l], w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IB(l), BITS)) for l in g}
        self.gw = {l: s([g[l], w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IB(l))) for l in g}
        vals = {k: selfval(w, ph, mk, 'D', self.dd, k) for k in K4_}
        self.S0 = Stacks(w, ph, mk, 'D', self.dd, ne, vals)
        self.gam = {v[0]: v[2] for v in vals.values()}
        xw = c[WRD('X', GAM)]
        self.gam['X'] = xw
        self.bw(WBc, 'L"', 'X')
        self.bw(WA, "L'", WBc)
        for l in ('L', "L'", 'L"', S1, S2, S3):
            for r in (DJ, DI, DIp):
                self.bw(BW(l, r), l, r)
        self.cl = Closure(w, ph, {'H': ('NN0', c['H e. NN0'])})
        for l in g:
            self.cl.leaf('( # ` %s )' % l, 'NN0', s([g[l], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, l)))
        self.lens = []

    def bw(self, txt, l, rest):
        w, ph = self.w, self.ph
        self.gam[txt] = wgcat(w, ph, IB(l), '( <" 4 "> ++ %s )' % rest, self.gw[l], wg4(w, ph, rest, self.gam[rest]))
        return self.gam[txt]

    def ex_for(self, l):
        return {WRD(IB(l), BITS): self.gb[l], '%s e. Word 2o' % l: self.g2[l]}

    def lenfacts(self, words):
        """( # ` ( inclBool o. w ) ) = ( # ` w ) and ( # ` w ) <_ H for the words; atoms for the closure"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        out = []
        c = self.c
        if not hasattr(self, '_le'):
            self._le = {'L': c['( # ` L ) <_ H'], "L'": c["( # ` L' ) <_ H"], 'L"': c['( # ` L" ) <_ H']}
        le = self._le
        hr = cl.mem('H', 'RR')
        def rr(x):
            return cl.mem(x, 'RR')
        mx = lambda a, b: 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (a, b, b, a)
        def maxle(a, b):
            j = s([rr('( # ` %s )' % a), rr('( # ` %s )' % b), hr], '3jca', '( %s -> ( ( # ` %s ) e. RR /\\ ( # ` %s ) e. RR /\\ H e. RR ) )' % (ph, a, b))
            e = s([j, w.inst('maxle')], 'syl', '( %s -> ( %s <_ H <-> ( ( # ` %s ) <_ H /\\ ( # ` %s ) <_ H ) ) )' % (ph, mx(a, b), a, b))
            return s([s([le[a], le[b]], 'jca', '( %s -> ( ( # ` %s ) <_ H /\\ ( # ` %s ) <_ H ) )' % (ph, a, b)), e], 'mpbird',
                     '( %s -> %s <_ H )' % (ph, mx(a, b)))
        z2 = closed(w, ph, '0el2o', '(/) e. 2o')
        def stle(x, a, b):
            reg_mx(self, a, b)
            sl = s([self.g2[a], self.g2[b], z2, w.inst('subtrunclen')], 'syl3anc', '( %s -> ( # ` %s ) <_ %s )' % (ph, x, mx(a, b)))
            le[x] = s([rr('( # ` %s )' % x), rr(mx(a, b)), hr, sl, maxle(a, b)], 'letrd', '( %s -> ( # ` %s ) <_ H )' % (ph, x))
        for a, b in (("L'", 'L'), ('L', "L'"), ('L"', "L'"), ('L', 'L"')):
            m = mx(a, b)
            if m not in cl.known if hasattr(cl, 'known') else True:
                pass
        for x in words:
            if x == S1 and x not in le:
                stle(S1, "L'", 'L')
            if x == S3 and x not in le:
                stle(S3, 'L', "L'")
            if x == S2 and x not in le:
                if S1 not in le:
                    stle(S1, "L'", 'L')
                stle(S2, 'L"', S1)
        for x in words:
            bl = s([self.g2[x], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, IB(x), x))
            cl.leaf('( # ` %s )' % IB(x), 'NN0', s([self.gb[x], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, IB(x))))
            out += [bl, le[x]]
        return out, maxle


def run_prefix(w, ph, fx, R, base_chain):
    """finish: normalize the Run relative to D (base chain + the Run's chain)"""
    cur, out = R.normalize(K4_)
    chi = list(base_chain) + out
    nst, out2 = stk_normalize(w, ph, fx.mk, 'D', fx.dd, fx.ne, chi, fx.gam, K4_)
    return chi, nst, out2


def tmirsta():
    ph = cj(TREE_RST)
    w = W('tmirsta', 'The prefix of Lean\'s ` resStep ` at the machine: ` moveEntry nL np s ` (~ tmime ) parks the residue '
                     'on ` np ` , ` dup np t s ` and ` dup nL s t ` (~ tmidup ) copy it and ` q ` , ` cmpFrag t s ` (~ tmicmp ) '
                     'compares them.')
    fx = Fx(w, ph)
    s, c = w.s, fx.c
    R = Run(w, ph, fx.mk, fx.S0, fx.ex, c)
    ex = fx.ex_for('L'); ex[WRD(WA, GAM)] = fx.gam[WA]
    ex['( D ` K ) = %s' % BW('L', WA)] = c['( D ` K ) = %s' % W3('L')]
    R.call('tmime', {'K': 'K', 'J': 'J', 'I': 'I', 'P': PL('P', 1), 'E': PL(PL('P', 2), 0), 'W': IB('L'), 'X': WA}, ex,
           [('K', WA, fx.gam[WA]), ('J', BW('L', DJ), fx.gam[BW('L', DJ)])])
    S1_ = R.S
    ex = fx.ex_for('L'); ex[WRD(DJ, GAM)] = fx.gam[DJ]
    ex['( %s ` J ) = %s' % (S1_.D, BW('L', DJ))] = S1_.vals['J'][1]
    R.call('tmidup', {'K': 'J', 'J': "I'", 'I': 'I', 'P': PL('P', 2), 'E': PL(PL('P', 3), 0), 'W': IB('L'), 'X': DJ}, ex,
           [("I'", BW('L', DIp), fx.gam[BW('L', DIp)])])
    S2_ = R.S
    ex = fx.ex_for("L'"); ex[WRD(WBc, GAM)] = fx.gam[WBc]
    ex['( %s ` K ) = %s' % (S2_.D, WA)] = S2_.vals['K'][1]
    R.call('tmidup', {'K': 'K', 'J': 'I', 'I': "I'", 'P': PL('P', 3), 'E': PL(PL('P', 4), 0), 'W': IB("L'"), 'X': WBc}, ex,
           [('I', BW("L'", DI), fx.gam[BW("L'", DI)])])
    S3_ = R.S
    ex = dict(fx.ex_for('L')); ex.update(fx.ex_for("L'"))
    ex[WRD(DIp, GAM)] = fx.gam[DIp]; ex[WRD(DI, GAM)] = fx.gam[DI]
    ex["( %s ` I' ) = %s" % (S3_.D, BW('L', DIp))] = S3_.vals["I'"][1]
    ex['( %s ` I ) = %s' % (S3_.D, BW("L'", DI))] = S3_.vals['I'][1]
    R.call('tmicmp', {'K': "I'", 'J': 'I', 'P': PL('P', 4), 'E': PL('P', 0), 'L': 'L', "L'": "L'", 'X': DIp, 'Y': DI}, ex,
           [("I'", DIp, fx.gam[DIp]), ('I', DI, fx.gam[DI])])
    chi, nst, out2 = run_prefix(w, ph, fx, R, [])
    assert chain_text('D', out2) == DP, chain_text('D', out2)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    lens, _ = fx.lenfacts(['L', "L'"])
    le = linarith(w, ph, lens + [fx.cl.ge0('H')] + [maxle_step(w, ph, fx, 'L', "L'")], '%s <_ %s' % (n, T1B), closure=fx.cl)
    hrle(w, ph, fx.mk['phm'], t, C, D, n, T1B, fx.cl.mem(T1B, 'NN0'), le, qed=True)
    return w.run()


def reg_mx(fx, a, b):
    key = ('mx', a, b)
    if getattr(fx, '_mx', None) is None:
        fx._mx = set()
    if key in fx._mx:
        return
    fx._mx.add(key)
    mx = 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (a, b, b, a)
    fx.cl.leaf(mx, 'NN0', ifnn0(fx.w, fx.ph, fx, a, b))


def maxle_step(w, ph, fx, a, b):
    _, maxle = fx.lenfacts([])
    reg_mx(fx, a, b)
    return maxle(a, b)


def ifnn0(w, ph, fx, a, b):
    mx = 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (a, b, b, a)
    return w.s([fx.cl.mem('( # ` %s )' % b, 'NN0'), fx.cl.mem('( # ` %s )' % a, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ph, mx))


def branch(lab, desc, calls_fn, tgt, bound, entry):
    ph = cj(TREE_RST)
    w = W(lab, desc)
    fx = Fx(w, ph)
    SP = fx.S0.upd('K', WA, fx.gam[WA]).upd('J', BW('L', DJ), fx.gam[BW('L', DJ)])
    R = Run(w, ph, fx.mk, SP, fx.ex, fx.c)
    words, mx = calls_fn(w, ph, fx, R)
    chi, nst, out2 = run_prefix(w, ph, fx, R, [('K', WA), ('J', BW('L', DJ))])
    assert chain_text('D', out2) == tgt, chain_text('D', out2)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, PL(PL('P', 14), 0), S, nst, chain_text(DP, chi[2:]) if False else chain_text('D', chi), tgt))
    lens, _ = fx.lenfacts(words)
    mxs = [maxle_step(w, ph, fx, a, b) for a, b in mx]
    le = linarith(w, ph, lens + mxs + [fx.cl.ge0('H')], '%s <_ %s' % (n, bound), closure=fx.cl)
    hrle(w, ph, fx.mk['phm'], t, C, D, n, bound, fx.cl.mem(bound, 'NN0'), le, qed=True)
    return w.run()


def calls_b(w, ph, fx, R):
    s = w.s
    S_ = R.S
    ex = fx.ex_for("L'"); ex[WRD(WBc, GAM)] = fx.gam[WBc]
    ex['( %s ` K ) = %s' % (S_.D, WA)] = S_.vals['K'][1]
    R.call('tmidup', {'K': 'K', 'J': "I'", 'I': 'I', 'P': PL('P', 5), 'E': PL(PL('P', 6), 0), 'W': IB("L'"), 'X': WBc}, ex,
           [("I'", BW("L'", DIp), fx.gam[BW("L'", DIp)])])
    S_ = R.S
    ex = dict(fx.ex_for('L')); ex.update(fx.ex_for("L'")); ex[WRD(DIp, GAM)] = fx.gam[DIp]; ex[WRD(DJ, GAM)] = fx.gam[DJ]
    ex["( %s ` I' ) = %s" % (S_.D, BW("L'", DIp))] = S_.vals["I'"][1]
    ex['( %s ` J ) = %s' % (S_.D, BW('L', DJ))] = S_.vals['J'][1]
    R.call('tmisub', {'K': "I'", 'J': 'J', 'I': 'I', 'P': PL('P', 6), 'E': PL(PL('P', 7), 0), 'L': "L'", "L'": 'L', 'X': DIp, 'Y': DJ}, ex,
           [("I'", BW(S1, DIp), fx.gam[BW(S1, DIp)]), ('J', DJ, fx.gam[DJ])])
    S_ = R.S
    ex = fx.ex_for("L'"); ex[WRD(WBc, GAM)] = fx.gam[WBc]
    ex['( %s ` K ) = %s' % (S_.D, WA)] = S_.vals['K'][1]
    R.call('tmime', {'K': 'K', 'J': 'J', 'I': 'I', 'P': PL('P', 7), 'E': PL(PL('P', 8), 0), 'W': IB("L'"), 'X': WBc}, ex,
           [('K', WBc, fx.gam[WBc]), ('J', BW("L'", DJ), fx.gam[BW("L'", DJ)])])
    S_ = R.S
    ex = fx.ex_for('L"'); ex[WRD('X', GAM)] = fx.gam['X']
    ex['( %s ` K ) = %s' % (S_.D, WBc)] = S_.vals['K'][1]
    R.call('tmidup', {'K': 'K', 'J': 'I', 'I': "I'", 'P': PL('P', 8), 'E': PL(PL('P', 9), 0), 'W': IB('L"'), 'X': 'X'}, ex,
           [('I', BW('L"', DI), fx.gam[BW('L"', DI)])])
    S_ = R.S
    ex = dict(fx.ex_for('L"')); ex.update(fx.ex_for(S1)); ex[WRD(DI, GAM)] = fx.gam[DI]; ex[WRD(DIp, GAM)] = fx.gam[DIp]
    ex['( %s ` I ) = %s' % (S_.D, BW('L"', DI))] = S_.vals['I'][1]
    ex["( %s ` I' ) = %s" % (S_.D, BW(S1, DIp))] = S_.vals["I'"][1]
    R.call('tmisub', {'K': 'I', 'J': "I'", 'I': 'J', 'P': PL('P', 9), 'E': PL(PL('P', 10), 0), 'L': 'L"', "L'": S1, 'X': DI, 'Y': DIp}, ex,
           [('I', BW(S2, DI), fx.gam[BW(S2, DI)]), ("I'", DIp, fx.gam[DIp])])
    S_ = R.S
    ex = fx.ex_for("L'"); ex[WRD(DJ, GAM)] = fx.gam[DJ]
    ex['( %s ` J ) = %s' % (S_.D, BW("L'", DJ))] = S_.vals['J'][1]
    R.call('tmime', {'K': 'J', 'J': 'K', 'I': "I'", 'P': PL('P', 10), 'E': PL(PL('P', 11), 0), 'W': IB("L'"), 'X': DJ}, ex,
           [('J', DJ, fx.gam[DJ]), ('K', WA, fx.gam[WA])])
    S_ = R.S
    ex = fx.ex_for(S2); ex[WRD(DI, GAM)] = fx.gam[DI]
    ex['( %s ` I ) = %s' % (S_.D, BW(S2, DI))] = S_.vals['I'][1]
    R.call('tmime', {'K': 'I', 'J': 'J', 'I': "I'", 'P': PL('P', 11), 'E': PL(PL('P', 14), 0), 'W': IB(S2), 'X': DI}, ex,
           [('I', DI, fx.gam[DI]), ('J', BW(S2, DJ), fx.gam[BW(S2, DJ)])])
    return ['L', "L'", 'L"', S1, S2], [("L'", 'L'), ('L"', S1)]


def calls_c(w, ph, fx, R):
    S_ = R.S
    ex = fx.ex_for("L'"); ex[WRD(WBc, GAM)] = fx.gam[WBc]
    ex['( %s ` K ) = %s' % (S_.D, WA)] = S_.vals['K'][1]
    R.call('tmidup', {'K': 'K', 'J': "I'", 'I': 'I', 'P': PL('P', 12), 'E': PL(PL('P', 13), 0), 'W': IB("L'"), 'X': WBc}, ex,
           [("I'", BW("L'", DIp), fx.gam[BW("L'", DIp)])])
    S_ = R.S
    ex = dict(fx.ex_for('L')); ex.update(fx.ex_for("L'")); ex[WRD(DIp, GAM)] = fx.gam[DIp]; ex[WRD(DJ, GAM)] = fx.gam[DJ]
    ex['( %s ` J ) = %s' % (S_.D, BW('L', DJ))] = S_.vals['J'][1]
    ex["( %s ` I' ) = %s" % (S_.D, BW("L'", DIp))] = S_.vals["I'"][1]
    R.call('tmisub', {'K': 'J', 'J': "I'", 'I': 'I', 'P': PL('P', 13), 'E': PL(PL('P', 14), 0), 'L': 'L', "L'": "L'", 'X': DJ, 'Y': DIp}, ex,
           [('J', BW(S3, DJ), fx.gam[BW(S3, DJ)]), ("I'", DIp, fx.gam[DIp])])
    return ['L', "L'"], [('L', "L'")]


def tmirstb():
    return branch('tmirstb', 'The branch ` cmp = lt ` of Lean\'s ` resStep ` at the machine: ` dup nL t s ; sub t np s t ; '
                  'moveEntry nL np s ; dup nL s t ; sub s t np s ; moveEntry np nL t ; moveEntry s np t ` (~ tmidup , '
                  '~ tmisub , ~ tmime ) leaves ` L - ( q - a ) ` on ` np ` .', calls_b, DB(S2), T2B, 5)


def tmirstc():
    return branch('tmirstc', 'The other branch of Lean\'s ` resStep ` at the machine: ` dup nL t s ; sub np t s np ` '
                  '(~ tmidup , ~ tmisub ) leaves ` a - q ` on ` np ` .', calls_c, DB(S3), T0B, 12)



def tmirst():
    lab = 'tmirst'
    ph = cj(TREE_RST)
    w = W(lab, 'Lean\'s ` resStep_runs ` at the machine: wherever ` resStep nL np s t ` is installed, with ` a ` above '
               '` q ` above ` L ` on ` nL ` (bit words of length at most ` m ` ), ` a ` is replaced by the word ` RW ` '
               'the machine computes ( ` a - q ` if ` q <_ a ` , else ` L - ( q - a ) ` ), every other stack restored, '
               'within ` 25 m + 53 ` steps (~ tm2frst ; the prefix ~ tmirsta , the branches ~ tmirstb , ~ tmirstc by '
               'cases on ` cmp = lt ` , the final ` moveEntry np nL s ` by ~ tmime ).')
    fx = Fx(w, ph)
    s, c, mk = w.s, fx.c, fx.mk
    tL, tL2 = '( toNat ` L )', "( toNat ` L' )"
    RWc = "( toNat ` L' ) <_ ( toNat ` L )"
    # RW typing and length
    rwg = s([fx.g2[S3], fx.g2[S2]], 'ifcld', '( %s -> %s e. Word 2o )' % (ph, RW))
    fx.g2[RW] = rwg
    fx.gb[RW] = s([rwg, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IB(RW), BITS))
    fx.gw[RW] = s([rwg, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IB(RW)))
    for r in (DJ, WA):
        fx.bw(BW(RW, r), RW, r)
    ex = dict(fx.ex)
    # the compare class and the test
    ssc = s([s([], 'ssrab2', '%s C_ TMSt' % CMPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, CMPC))
    ex[SSS(CMPC)] = s([ssc, mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, CMPC, S))
    b01 = s([s([], '0el2o', '(/) e. 2o'), s([], '1oel2o', '1o e. 2o')], 'ifcli', 'if ( ( TMcmp ` u ) = (/) , 1o , (/) ) e. 2o')
    XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    ex['%s e. ( 2o ^m %s )' % (CLT_, S)] = lamty(w, ph, mk, CLT_, XL, '2o', s([], '2oex', '2o e. _V'), b01)
    # the stacks
    SP = fx.S0.upd('K', WA, fx.gam[WA]).upd('J', BW('L', DJ), fx.gam[BW('L', DJ)])
    ex[STKD(DP)] = SP.memb
    cl = fx.cl
    for b in (T1B, T2B, T0B, TPB):
        ex['%s e. NN0' % b] = cl.mem(b, 'NN0')
    ex['%s <_ %s' % (T0B, T2B)] = linarith(w, ph, [cl.ge0('H')], '%s <_ %s' % (T0B, T2B), closure=cl)
    ex[TRI(CEN('rst', 'D'), CLN('( P ` 0 )', CMPC, DP), T1B)] = s([], 'tmirsta', ST_A)
    # the disjunction by cases
    tln = s([fx.g2['L'], w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, tL))
    tln2 = s([fx.g2["L'"], w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, tL2))
    nl = s([s([tln, tln2], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, tL, tL2)), w.inst('ncmplt')], 'syl',
           '( %s -> ( ( %s Ncmp %s ) = (/) <-> %s < %s ) )' % (ph, tL, tL2, tL, tL2))
    DBR = DB(RW)
    E14 = PL(PL('P', 14), 0)
    m = dict(FRAGS['rst'].lmap())
    m.update({'C': CLT_, "D'": DP, 'N1': CMPC, 'N': S, 'D': 'D', 'T1': T1B, 'T"': T2B, 'T0': T0B, "T'": TPB, 'N"': S, 'D"': DBR,
              "N'": S, 'D0': UP('D', 'K', W3(RW))})
    from t8a_e_slot import disj_leaf
    d, d1, d2 = disj_leaf('tm2frst', m)
    CND = '%s < %s' % (tL, tL2)

    def testv(pc, lift):
        """under pc: for m e. CMPC, ( CLT_ ` m ) = if ( ( TMcmp ` m ) = (/) , 1o , (/) ) and ( TMcmp ` m ) = ( tL Ncmp tL' )"""
        pm = '( %s /\\ m e. %s )' % (pc, CMPC)
        mi = s([], 'simpr', '( %s -> m e. %s )' % (pm, CMPC))
        cond = lambda t: '( TMcmp ` %s ) = ( %s Ncmp %s )' % (t, tL, tL2)
        idh = s([], 'id', '( h = m -> h = m )')
        cg, new = w.wcongr(cond('h'), {'h': 'm'}, 'h = m', {'h': idh})
        el = s([cg], 'elrab', '( m e. %s <-> ( m e. TMSt /\\ %s ) )' % (CMPC, cond('m')))
        both = s([mi, el], 'sylib', '( %s -> ( m e. TMSt /\\ %s ) )' % (pm, cond('m')))
        mm = s([both], 'simpld', '( %s -> m e. TMSt )' % pm)
        mc = s([both], 'simprd', '( %s -> %s )' % (pm, cond('m')))
        xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V'))
        cv = mval(w, pm, 'u', 'TMSt', XL, 'm', mm, xex)
        return pm, mc, cv

    # case lt
    pc = '( %s /\\ %s )' % (ph, CND)
    Lc = lambda st: L_(w, pc, ph, st)
    ltc = s([], 'simpr', '( %s -> %s )' % (pc, CND))
    pm, mc, cv = testv(pc, Lc)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pc, st)))
    nc0 = s([ltc, Lc(nl)], 'mpbird', '( %s -> ( %s Ncmp %s ) = (/) )' % (pc, tL, tL2))
    cm0 = s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = (/) )' % pm)
    ht = s([s([cv, s([cm0], 'iftrued', '( %s -> %s = 1o )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CLT_))],
           'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pc, CMPC, CLT_))
    tb = Lc(s([], 'tmirstb', ST_B))
    E5 = PL(PL('P', 5), 0)
    tb = hrssc(w, pc, Lc(mk['phm']), tb, CLN(E5, S, DP), CLN(E14, S, DB(S2)), T2B, CLN(E5, CMPC, DP), clnss(w, pc, E5, CMPC, S, DP, Lc(ex[SSS(CMPC)])))
    nle = s([s([Lc(tln), Lc(tln2)], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (pc, tL, tL2)), w.inst('nn0ltnle' if False else 'id'), ], 'id', '') if False else None
    lnl = s([s([Lc(tln)], 'nn0red', '( %s -> %s e. RR )' % (pc, tL)), s([Lc(tln2)], 'nn0red', '( %s -> %s e. RR )' % (pc, tL2))], 'ltnled',
            '( %s -> ( %s <-> -. %s ) )' % (pc, CND, RWc))
    lt2 = s([ltc, lnl], 'mpbid', '( %s -> -. %s )' % (pc, RWc))
    rwe = s([lt2], 'iffalsed', '( %s -> %s = %s )' % (pc, RW, S2))
    r1, x1 = w.rewrite(DB(S2), {S2: (RW, s([rwe], 'eqcomd', '( %s -> %s = %s )' % (pc, S2, RW)))}, pc)
    assert x1 == DBR
    tb, _, _, _ = hrrw(w, pc, tb, CLN(E5, CMPC, DP), CLN(E14, S, DB(S2)), T2B, deq=clneq(w, pc, E14, S, r1, DB(S2), DBR))
    o1 = s([s([ht, tb], 'jca', '( %s -> %s )' % (pc, d1))], 'orcd', '( %s -> %s )' % (pc, d))
    # case not lt
    pn = '( %s /\\ -. %s )' % (ph, CND)
    Ln = lambda st: L_(w, pn, ph, st)
    nlt = s([], 'simpr', '( %s -> -. %s )' % (pn, CND))
    pm, mc, cv = testv(pn, Ln)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pn, st)))
    nn0 = s([nlt, Ln(nl)], 'mtbird', '( %s -> -. ( %s Ncmp %s ) = (/) )' % (pn, tL, tL2))
    cm1 = s([Lm(nn0), s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = (/) <-> ( %s Ncmp %s ) = (/) ) )' % (pm, tL, tL2))], 'mtbird',
            '( %s -> -. ( TMcmp ` m ) = (/) )' % pm)
    c0 = s([cv, s([cm1], 'iffalsed', '( %s -> %s = (/) )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CLT_))
    htf = s([not1o(w, pm, c0, CLT_, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pn, CMPC, CLT_))
    tcc = Ln(s([], 'tmirstc', ST_C))
    E12 = PL(PL('P', 12), 0)
    tcc = hrssc(w, pn, Ln(mk['phm']), tcc, CLN(E12, S, DP), CLN(E14, S, DB(S3)), T0B, CLN(E12, CMPC, DP), clnss(w, pn, E12, CMPC, S, DP, Ln(ex[SSS(CMPC)])))
    ge = s([s([Ln(tln2)], 'nn0red', '( %s -> %s e. RR )' % (pn, tL2)), s([Ln(tln)], 'nn0red', '( %s -> %s e. RR )' % (pn, tL)), nlt], 'lenltd' if False else 'id', '') if False else None
    ge = s([s([s([Ln(tln2)], 'nn0red', '( %s -> %s e. RR )' % (pn, tL2)), s([Ln(tln)], 'nn0red', '( %s -> %s e. RR )' % (pn, tL)), w.inst('lenlt')], 'syl2anc',
              '( %s -> ( %s <-> -. %s ) )' % (pn, RWc, CND)), nlt], 'mpbird', '( %s -> %s )' % (pn, RWc))
    rwe = s([ge], 'iftrued', '( %s -> %s = %s )' % (pn, RW, S3))
    r2, x2 = w.rewrite(DB(S3), {S3: (RW, s([rwe], 'eqcomd', '( %s -> %s = %s )' % (pn, S3, RW)))}, pn)
    assert x2 == DBR
    tcc, _, _, _ = hrrw(w, pn, tcc, CLN(E12, CMPC, DP), CLN(E14, S, DB(S3)), T0B, deq=clneq(w, pn, E14, S, r2, DB(S3), DBR))
    o2 = s([s([htf, tcc], 'jca', '( %s -> %s )' % (pn, d2))], 'olcd', '( %s -> %s )' % (pn, d))
    ex[d] = s([o1, o2], 'pm2.61dan', '( %s -> %s )' % (ph, d))
    # the final moveEntry np nL s from DBR
    SB_ = fx.S0.upd('K', WA, fx.gam[WA]).upd('J', BW(RW, DJ), fx.gam[BW(RW, DJ)])
    assert SB_.D == DBR
    R = Run(w, ph, mk, SB_, fx.ex, c)
    exm = fx.ex_for(RW); exm[WRD(DJ, GAM)] = fx.gam[DJ]
    exm['( %s ` J ) = %s' % (DBR, BW(RW, DJ))] = SB_.vals['J'][1]
    R.call('tmime', {'K': 'J', 'J': 'K', 'I': 'I', 'P': PL('P', 14), 'E': 'E', 'W': IB(RW), 'X': DJ}, exm,
           [('J', DJ, fx.gam[DJ]), ('K', W3(RW), fx.gam[W3(RW)] if W3(RW) in fx.gam else fx.bw(W3(RW), RW, WA))])
    chi, nst, out2 = run_prefix(w, ph, fx, R, [('K', WA), ('J', BW(RW, DJ))])
    assert chain_text('D', out2) == UP('D', 'K', W3(RW)), chain_text('D', out2)
    t4, C4, D4, n4 = R.tri, R.C0, R.cur, R.n
    t4, C4, D4, n4 = hrrw(w, ph, t4, C4, D4, n4, deq=clneq(w, ph, 'E', S, nst, chain_text('D', chi), UP('D', 'K', W3(RW))))
    # # RW <_ H
    lens, maxle = fx.lenfacts([S3, S2])
    le = fx._le
    h = c['H e. NN0']
    f3 = s([s([fx.g2[S3], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, S3)), h, le[S3]], 'elfz2nn0d' if False else 'id', '') if False else None
    fz3 = s([s([s([fx.g2[S3], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, S3)), h, le[S3]], '3jca',
               '( %s -> ( ( # ` %s ) e. NN0 /\\ H e. NN0 /\\ ( # ` %s ) <_ H ) )' % (ph, S3, S3)), w.inst('elfz2nn0')], 'sylibr',
            '( %s -> ( # ` %s ) e. ( 0 ... H ) )' % (ph, S3))
    fz2 = s([s([s([fx.g2[S2], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, S2)), h, le[S2]], '3jca',
               '( %s -> ( ( # ` %s ) e. NN0 /\\ H e. NN0 /\\ ( # ` %s ) <_ H ) )' % (ph, S2, S2)), w.inst('elfz2nn0')], 'sylibr',
            '( %s -> ( # ` %s ) e. ( 0 ... H ) )' % (ph, S2))
    fvi = s([], 'fvif', '( # ` %s ) = if ( %s , ( # ` %s ) , ( # ` %s ) )' % (RW, RWc, S3, S2))
    ifz = s([fz3, fz2], 'ifcld', '( %s -> if ( %s , ( # ` %s ) , ( # ` %s ) ) e. ( 0 ... H ) )' % (ph, RWc, S3, S2))
    rfz = s([w.s([fvi], 'a1i', '( %s -> ( # ` %s ) = if ( %s , ( # ` %s ) , ( # ` %s ) ) )' % (ph, RW, RWc, S3, S2)), ifz], 'eqeltrd',
            '( %s -> ( # ` %s ) e. ( 0 ... H ) )' % (ph, RW))
    rle = s([rfz, w.inst('elfzle2')], 'syl', '( %s -> ( # ` %s ) <_ H )' % (ph, RW))
    bl = s([rwg, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, IB(RW), RW))
    cl.leaf('( # ` %s )' % IB(RW), 'NN0', s([fx.gb[RW], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, IB(RW))))
    cl.leaf('( # ` %s )' % RW, 'NN0', s([rwg, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, RW)))
    lef = linarith(w, ph, [bl, rle], '%s <_ %s' % (n4, TPB), closure=cl)
    t4 = hrle(w, ph, mk['phm'], t4, C4, D4, n4, TPB, cl.mem(TPB, 'NN0'), lef)
    ex[TRI(C4, D4, TPB)] = t4
    t, cc = inst(w, ph, 'tm2frst', m, Bld(w, ph, c, ex))
    C, D, n = triple_parts(cc)
    neq = linarith(w, ph, [], '%s = %s' % (n, '( ( ; 2 5 x. H ) + ; 5 3 )'), closure=cl) if False else None
    from lin import lineq
    neq = lineq(w, ph, n, '( ( ; 2 5 x. H ) + ; 5 3 )', closure=cl)
    hrrw(w, ph, t, C, D, n, neq=neq, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
