"""T8a: walkDown at the machine (Lean ` walkDown_runs ` ) on its installation predicate TMIwdn.

  tmiwdni   one iteration: ` moveSlot tbl scr s j ; predNum j s ; isZero j s ` (~ tmimvs , ~ tmiprds , ~ tmiizs )
  tmiwdnt   the frame: typings over ( 0 ... F ), the exit test, the prologue ` isZero j s ` and the epilogue
            ` dropNum j `
  tmiwdnl   ~ tm2fwdn assembled, the stack family a letter P'
  tmiwdn    walkDown_runs

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_g_wdn.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
from lin import linarith, lineq, nlinarith
from t7lib import famval, fam_unpack, fam_pack, mval
from t8a_e_slot import stkcl
from t8a_f_wup import find, cnfl_m

SEL = sys.argv[1:]
F = FG
RL = '( # ` L )'
DI = "( D ` I' )"
Z0D = '( <" 0 "> ++ %s )' % DI
Y4 = '( <" 4 "> ++ Y )'


def At(t):
    return CC(ES(DROP('L', t)), 'X')


def Bt(t):
    return CC('( inclBool o. %s )' % CW(t), Y4)


def Ct(t):
    return CC(ES(REV(PFX('L', t))), Z0D)


def PDB(t):
    return UP(UP(UP('D', 'K', At(t)), 'J', Bt(t)), "I'", Ct(t))


PDF = '( j e. NN0 |-> %s )' % PDB('j')
NCD = lambda h, t: '( TMfl ` %s ) = if ( ( %s - %s ) = 0 , 1o , (/) )' % (h, F, t)
NF = '( j e. NN0 |-> { h e. TMSt | %s } )' % NCD('h', 'j')
UB = '( ( 2 x. H ) + 5 )'
UB2 = '( H + 1 )'
TB = '( ( %s + ( ( 2 x. H ) + 3 ) ) + ( ( 2 x. H ) + 5 ) )' % SLOTC
FAMEQ = "P' = %s" % PDF
T_L = (TREE_WDN, FAMEQ)
PH = cj(T_L)
PSI = '( %s /\\ i e. ( 0 ..^ %s ) )' % (PH, F)

GM = dict(FRAGS['wdn'].lmap())
GM.update({'K': "I'", 'Y': BLANK, 'C0': CNFL, 'R': F, "T'": TB, 'O': S, 'N': NF, 'P': "P'", 'U': UB, "U'": UB2,
           "D'": DFIN_WDN, "N'": S})
_LA, _LC = split_imp(stmt('tm2fwdn'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LPER = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ..^ '))[0]
LBODY = LPER[len('A. i e. ( 0 ..^ %s ) ' % F):]
LTYP = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ... %s ) ' % F))[0]
LEXIT = 'A. m e. ( %s ` %s ) -. ( %s ` m ) = 1o' % (NF, F, CNFL)
P1_, A_, B0_, E0_ = GM['P1'], GM['A'], GM['B0'], GM['E']
LPRO = TRI(CLN(P1_, S, UP('D', "I'", Z0D)), CLN(A_, '( %s ` 0 )' % NF, "( P' ` 0 )"), UB)
LEPI = TRI(CLN(E0_, '( %s ` %s )' % (NF, F), "( P' ` %s )" % F), CLN('E', S, DFIN_WDN), UB2)
for _t in (LEXIT, LPRO, LEPI):
    assert find(LTREE, lambda t, _t=_t: t == _t), _t
FRAME = ((LTYP, LEXIT), (LPRO, LEPI))


class Wc:
    """facts under ph (the walkDown antecedent with the family equation, possibly extended)"""
    def __init__(self, w, ph, tree=None, root=None, pl="P'"):
        self.w, self.ph, self.pl = w, ph, pl
        tree = tree or T_L
        if root is None and ph != cj(tree):
            root = w.s([], 'simpl', '( %s -> %s )' % (ph, cj(tree)))
        self.c = c = Ctx(w, ph, tree, root=root)
        mk = self.mk = machine(w, ph, c, K4)
        ne = self.ne = ne_fn(w, ph, c, set(flat(dist_tree(K4))))
        base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        base.update(unfold_all(w, ph, c[FRAGS['wdn'].pred()], 'wdn', K4, 'P', 'E', rec=False))
        fr = FRAGS['wdn']; lm = fr.lmap()
        for j, (fn, cks, en, exn) in enumerate(fr.children):
            P_ = PL('P', fr.slot(j))
            pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
            base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
        for s_ in K4:
            base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K4):
            for b in K4[i_ + 1:]:
                base['%s =/= %s' % (a, b)] = ne(a, b)
                base['%s =/= %s' % (b, a)] = ne(b, a)
        ex = self.ex = dict(base)
        ex.update(H.handler_extra(w, ph, mk, H.IFACE))
        hi = w.s([mk['seq'], w.inst('tmctbhi')], 'syl', '( %s -> %s )' % (ph, cj(HI_TREE)))
        ex.update(parts(w, ph, hi, HI_TREE))
        ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
        self.lw, self.gw = c['L e. %s' % WSLOT], c['G e. Word 2o']
        self.xw, self.yw, self.dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
        self.fn = w.s([self.gw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, F))
        self.rn = w.s([self.lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, RL))
        self.flt = c['%s < %s' % (F, RL)]
        self.fle = w.s([w.s([self.fn], 'nn0red', '( %s -> %s e. RR )' % (ph, F)), w.s([self.rn], 'nn0red', '( %s -> %s e. RR )' % (ph, RL)), self.flt],
                       'ltled', '( %s -> %s <_ %s )' % (ph, F, RL))
        uz = w.s([w.s([self.fn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, F)), w.s([self.rn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, RL)), self.fle, w.inst('eluz2')],
                 'syl3anbrc', '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, RL, F))
        self.fzs = w.s([uz, w.inst('fzss2')], 'syl', '( %s -> ( 0 ... %s ) C_ ( 0 ... %s ) )' % (ph, F, RL))
        self.fzos = w.s([uz, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ %s ) C_ ( 0 ..^ %s ) )' % (ph, F, RL))
        dk = mk['k']["I'"]
        self.diw = w.s([stkfv(w, ph, 'D', "I'", mk['tv'], self.dd, dk['kd']), dk['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, DI))
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        self.s0 = w.s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        self.z0d = w.s([self.s0, self.diw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Z0D))
        self.y4 = wg4(w, ph, 'Y', self.yw)
        self.memo = {}

    def cw(self, t, tn, tle):
        """ttwcp at t : ( CW( t ) e. Word 2o , toNat = F - t , # <_ # G )"""
        key = ('cw', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        st = w.s([self.gw, tn, tle, w.inst('ttwcp')], 'syl3anc', '( %s -> ( %s e. Word 2o /\\ ( toNat ` %s ) = ( %s - %s ) /\\ ( # ` %s ) <_ ( # ` G ) ) )'
                 % (ph, CW(t), CW(t), F, t, CW(t)))
        r = (w.s([st, w.inst('simp1')], 'syl', '( %s -> %s e. Word 2o )' % (ph, CW(t))),
             w.s([st, w.inst('simp2')], 'syl', '( %s -> ( toNat ` %s ) = ( %s - %s ) )' % (ph, CW(t), F, t)),
             w.s([st, w.inst('simp3')], 'syl', '( %s -> ( # ` %s ) <_ ( # ` G ) )' % (ph, CW(t))))
        self.memo[key] = r
        return r

    def words(self, t, tfzF, tn, tle):
        """typings of A( t ), B( t ), C( t ) for t e. ( 0 ... F )"""
        key = ('w', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        dr = w.s([self.lw, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DROP('L', t), WSLOT))
        ed = w.s([dr, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(DROP('L', t))))
        aw = w.s([ed, self.xw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, At(t)))
        cwt = self.cw(t, tn, tle)[0]
        bw = w.s([wib(w, ph, CW(t), cwt), self.y4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Bt(t)))
        pf = w.s([self.lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, PFX('L', t), WSLOT))
        rp = w.s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REV(PFX('L', t)), WSLOT))
        er = w.s([rp, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(REV(PFX('L', t)))))
        cw_ = w.s([er, self.z0d, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Ct(t)))
        self.memo[key] = (aw, bw, cw_, ed, er)
        return self.memo[key]

    def stacks(self, t, tfzF, tn, tle):
        """the Stacks of PDB( t ) over D"""
        w, ph = self.w, self.ph
        aw, bw, cw_, ed, er = self.words(t, tfzF, tn, tle)
        vals = {s_: selfval(w, ph, self.mk, 'D', self.dd, s_) for s_ in K4}
        S0 = Stacks(w, ph, self.mk, 'D', self.dd, self.ne, vals)
        return S0, S0.upd('K', At(t), aw).upd('J', Bt(t), bw).upd("I'", Ct(t), cw_)

    def pdb(self, t, tfzF, tn, tle):
        """( ph -> ( P' ` t ) = PDB( t ) ) and the Stacks"""
        w, ph = self.w, self.ph
        S0, St = self.stacks(t, tfzF, tn, tle)
        v = mval(w, ph, 'j', 'NN0', PDB, t, tn, w.s([St.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PDB(t))))
        e = w.s([self.c['%s = %s' % (self.pl, PDF)]], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, self.pl, t, PDF, t))
        return w.s([e, v], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, self.pl, t, PDB(t))), S0, St

    def nfss(self, t, tn):
        w, ph = self.w, self.ph
        fv = famval(w, ph, NCD, t, tn)
        rab = '{ h e. TMSt | %s }' % NCD('h', t)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % rab)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, rab))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, rab, S))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ %s )' % (ph, NF, t, S))

    def ghb(self):
        """( ph -> ( # ` G ) <_ H ) and the closure with H, N, B"""
        return self.c['( # ` G ) <_ H']


def tmiwdni():
    lab = 'tmiwdni'
    w = W(lab, 'One iteration of Lean\'s ` walkDown ` loop at the machine ( ` walkBody_runs ` ): the test ` !flag ` holds '
               'while the counter is not zero, and ` moveSlot tbl scr s j ; predNum j s ; isZero j s ` moves slot ` i ` '
               'from ` tbl ` onto ` scr ` and counts down (~ tmimvs , ~ tmiprds , ~ tmiizs , ~ ttwcs ).')
    ps = PSI
    f = Wc(w, ps)
    c, mk = f.c, f.mk
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (ps, F))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ps, F))
    ir = w.s([inn], 'nn0red', '( %s -> i e. RR )' % ps)
    fr = w.s([f.fn], 'nn0red', '( %s -> %s e. RR )' % (ps, F))
    ile = w.s([ir, fr, ilt], 'ltled', '( %s -> i <_ %s )' % (ps, F))
    ifzF = w.s([ii, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (ps, F))
    I1 = '( i + 1 )'
    i1fzF = w.s([ii, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ps, I1, F))
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    i1le = w.s([i1fzF, w.inst('elfzle2')], 'syl', '( %s -> %s <_ %s )' % (ps, I1, F))
    iL = w.s([f.fzos, ii], 'sseldd', '( %s -> i e. ( 0 ..^ %s ) )' % (ps, RL))
    iz, fz = w.s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ps), w.s([f.fn], 'nn0zd', '( %s -> %s e. ZZ )' % (ps, F))
    fin = w.s([ilt, w.s([iz, fz, w.inst('znnsub')], 'syl2anc', '( %s -> ( i < %s <-> ( %s - i ) e. NN ) )' % (ps, F, F))], 'mpbid',
              '( %s -> ( %s - i ) e. NN )' % (ps, F))
    fn0 = w.s([w.s([fin], 'nnne0d', '( %s -> ( %s - i ) =/= 0 )' % (ps, F))], 'neneqd', '( %s -> -. ( %s - i ) = 0 )' % (ps, F))
    # the test
    NI = '( %s ` i )' % NF
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl0 = w.s([mc, w.s([Lm(fn0)], 'iffalsed', '( %s -> if ( ( %s - i ) = 0 , 1o , (/) ) = (/) )' % (pm, F))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ht = w.s([cnfl_m(w, pm, 'm', mm, '(/)', fl0)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNFL))
    # the run from the stacks PDB( i )
    pi, S0, Si = f.pdb('i', ifzF, inn, ile)
    aw1, bw1, cw1, ed1, er1 = f.words(I1, i1fzF, i1n, i1le)
    aw0, bw0, cw0, ed0, er0 = f.words('i', ifzF, inn, ile)
    Li = '( L ` i )'
    li = w.s([f.lw, iL, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (ps, Li, SLOT))
    eli = w.s([li, w.s([w.s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi', "( %s e. %s -> %s e. Word Gamma' )" % (Li, SLOT, ESL(Li)))],
              'syl', "( %s -> %s e. Word Gamma' )" % (ps, ESL(Li)))
    drp = w.s([f.lw, iL, w.inst('ttsesdrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(DROP('L', 'i')), ESL(Li), ES(DROP('L', I1))))
    ka = w.s([drp], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ X ) )' % (ps, At('i'), ESL(Li), ES(DROP('L', I1))))
    kb = w.s([eli, ed1, f.xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ X ) = ( %s ++ %s ) )' % (ps, ESL(Li), ES(DROP('L', I1)), ESL(Li), At(I1)))
    dki = w.s([Si.vals['K'][1], w.s([ka, kb], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ps, At('i'), ESL(Li), At(I1)))], 'eqtrd',
              '( %s -> ( %s ` K ) = ( %s ++ %s ) )' % (ps, Si.D, ESL(Li), At(I1)))
    lr = w.s([f.lw, iL, w.inst('algranfv')], 'syl2anc', '( %s -> %s e. ran L )' % (ps, Li))
    ido = w.s([], 'id', '( o = %s -> o = %s )' % (Li, Li))
    cg, new = w.wcongr(SB('o'), {'o': Li}, 'o = %s' % Li, {'o': ido})
    rsp = w.s([cg], 'rspcv', '( %s e. ran L -> ( %s -> %s ) )' % (Li, RSB, SB(Li)))
    sbi = w.s([lr, c[RSB], rsp], 'sylc', '( %s -> %s )' % (ps, SB(Li)))
    run = Run(w, ps, mk, Si, f.ex, c)
    ECI = CC(ESL(Li), Ct('i'))
    eci = w.s([eli, cw0, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, ECI))
    run.call('tmimvs', {'K': 'K', 'J': "I'", 'I': 'I', "I'": 'J', 'P': PL('P', 3), 'E': PL(PL('P', 4), 0), 'O': Li, 'R': At(I1)},
             {'%s e. %s' % (Li, SLOT): li, "%s e. Word Gamma'" % At(I1): aw1, '( %s ` K ) = ( %s ++ %s )' % (Si.D, ESL(Li), At(I1)): dki, SB(Li): sbi},
             [('K', At(I1), aw1), ("I'", ECI, eci)], pre=(NI, f.nfss('i', inn)))
    cwi, tni, lni = f.cw('i', inn, ile)
    PBW = '( predBits ` %s )' % CW('i')
    pbw = w.s([cwi, w.inst('predbitscl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, PBW))
    PBV = CC('( inclBool o. %s )' % PBW, Y4)
    pbv = w.s([wib(w, ps, PBW, pbw), f.y4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, PBV))
    S1 = run.S
    run.call('tmiprds', {'K': 'J', 'J': 'I', 'P': PL('P', 4), 'E': PL(PL('P', 5), 0), 'L': CW('i'), 'X': 'Y'},
             {'( %s ` J ) = %s' % (S1.D, Bt('i')): S1.vals['J'][1], '%s e. Word 2o' % CW('i'): cwi},
             [('J', PBV, pbv)])
    S2 = run.S
    # the class after isZero
    ws = w.s([f.gw, inn, ilt, w.inst('ttwcs')], 'syl3anc', '( %s -> %s = %s )' % (ps, PBW, CW(I1)))
    cw1_, tn1, ln1 = f.cw(I1, i1n, i1le)
    tpb = w.s([w.s([ws], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ps, PBW, CW(I1))), tn1], 'eqtrd',
              '( %s -> ( toNat ` %s ) = ( %s - %s ) )' % (ps, PBW, F, I1))
    OLD = '{ h e. TMSt | ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) }' % PBW
    ce = w.s([w.s([w.s([tpb], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( %s - %s ) = 0 ) )' % (ps, PBW, F, I1))], 'ifbid',
                  '( %s -> if ( ( toNat ` %s ) = 0 , 1o , (/) ) = if ( ( %s - %s ) = 0 , 1o , (/) ) )' % (ps, PBW, F, I1))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, PBW, NCD('h', I1)))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, PBW, NCD('h', I1)))],
             'rabbidva', '( %s -> %s = { h e. TMSt | %s } )' % (ps, OLD, NCD('h', I1)))
    fv1 = famval(w, ps, NCD, I1, i1n)
    rb2 = w.s([rb, w.s([fv1], 'eqcomd', '( %s -> { h e. TMSt | %s } = ( %s ` %s ) )' % (ps, NCD('h', I1), NF, I1))], 'eqtrd',
              '( %s -> %s = ( %s ` %s ) )' % (ps, OLD, NF, I1))
    run.call('tmiizs', {'K': 'J', 'I': 'I', 'P': PL('P', 5), 'E': PL('P', 1), 'L': PBW, 'X': 'Y'},
             {'( %s ` J ) = %s' % (S2.D, PBV): S2.vals['J'][1], '%s e. Word 2o' % PBW: pbw}, [], cls_rw=(rb2, '( %s ` %s )' % (NF, I1)))
    # normalize the stacks from D
    full = [('K', At('i')), ('J', Bt('i')), ("I'", Ct('i'))] + run.chain
    assert chain_text('D', full) == run.S.D, (chain_text('D', full), run.S.D)
    gam = dict(run.gam)
    gam.update({At('i'): aw0, Bt('i'): bw0, Ct('i'): cw0, At(I1): aw1, ECI: eci, PBV: pbv})
    nst, out = stk_normalize(w, ps, mk, 'D', f.dd, f.ne, full, gam, K4)
    assert out == [('K', At(I1)), ('J', PBV), ("I'", ECI)], out
    rv = w.s([f.lw, iL, w.inst('ttsesrev')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(REV(PFX('L', I1))), ESL(Li), ES(REV(PFX('L', 'i')))))
    ca = w.s([eli, er0, f.z0d, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = %s )' % (ps, ESL(Li), ES(REV(PFX('L', 'i'))), Z0D, ECI))
    cb = w.s([rv], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (ps, Ct(I1), ESL(Li), ES(REV(PFX('L', 'i'))), Z0D))
    ce2 = w.s([w.s([cb, ca], 'eqtrd', '( %s -> %s = %s )' % (ps, Ct(I1), ECI))], 'eqcomd', '( %s -> %s = %s )' % (ps, ECI, Ct(I1)))
    r2, x2 = w.rewrite(chain_text('D', out), {PBW: (CW(I1), ws), ECI: (Ct(I1), ce2)}, ps)
    assert x2 == PDB(I1), x2
    p1, _, _ = f.pdb(I1, i1fzF, i1n, i1le)
    fin_ = w.s([w.s([nst, r2], 'eqtrd', '( %s -> %s = %s )' % (ps, run.S.D, PDB(I1))), p1], 'eqtr4d', "( %s -> %s = ( P' ` %s ) )" % (ps, run.S.D, I1))
    head = run.cur[:-len(' X. { %s } ) )' % run.S.D)]
    ncls = head.split(' } X. ( ', 1)[1]
    deq = clneq(w, ps, A_, ncls, fin_, run.S.D, "( P' ` %s )" % I1)
    ceq = clneq(w, ps, B0_, NI, w.s([pi], 'eqcomd', "( %s -> %s = ( P' ` i ) )" % (ps, PDB('i'))), PDB('i'), "( P' ` i )")
    t2, C2, D2, n2 = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, ceq=ceq, deq=deq)
    # the bound
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'H': ('NN0', c['H e. NN0'])})
    for e_, st_ in [('( # ` %s )' % CW('i'), w.s([cwi, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, CW('i')))),
                    ('( # ` %s )' % PBW, w.s([pbw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, PBW))),
                    ('( # ` G )', w.s([f.gw, w.inst('lencl')], 'syl', '( %s -> ( # ` G ) e. NN0 )' % ps))]:
        cl.leaf(e_, 'NN0', st_)
    pbl = w.s([cwi, w.inst('predbitslen')], 'syl', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (ps, PBW, CW('i')))
    le = linarith(w, ps, [lni, pbl, f.ghb()], '%s <_ %s' % (n2, TB), closure=cl)
    t3 = hrle(w, ps, mk['phm'], t2, C2, D2, n2, TB, cl.mem(TB, 'NN0'), le)
    body = TRI(C2, D2, TB)
    got = '( %s /\\ %s )' % (HT(NI, CNFL), body)
    assert got == LBODY, '\nGOT  %s\nWANT %s' % (got, LBODY)
    w.qed([ht, t3], 'jca', '( %s -> %s )' % (ps, LBODY))
    return w.run()


ST_T = '( %s -> %s )' % (PH, cj(FRAME))


def tmiwdnt():
    lab = 'tmiwdnt'
    w = W(lab, 'The frame of Lean\'s ` walkDown ` loop at the machine: the invariant\'s classes and stacks over '
               '` 0 ... jn ` , the test ` !flag ` failing at ` jn ` , the prologue ` isZero j s ` (~ tmiizs ) entering the '
               'invariant at 0 after the marker push, and the epilogue ` dropNum j ` (~ tmidrop ).')
    ps = PH
    f = Wc(w, ps)
    c, mk = f.c, f.mk
    # typings
    pt = '( %s /\\ i e. ( 0 ... %s ) )' % (ps, F)
    g = Wc(w, pt)
    ifz = w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (pt, F))
    inn = w.s([ifz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = w.s([ifz, w.inst('elfzle2')], 'syl', '( %s -> i <_ %s )' % (pt, F))
    pi, S0i, Si = g.pdb('i', ifz, inn, ile)
    mem = w.s([pi, Si.memb], 'eqeltrd', "( %s -> ( P' ` i ) e. %s )" % (pt, STK_T))
    ty = w.s([g.nfss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYP[len('A. i e. ( 0 ... %s ) ' % F):]))
    typ = w.s([ty], 'ralrimiva', '( %s -> %s )' % (ps, LTYP))
    # exit
    NFF = '( %s ` %s )' % (NF, F)
    pm = '( %s /\\ m e. %s )' % (ps, NFF)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, F, Lm(f.fn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NFF)))
    ff = w.s([Lm(w.s([f.fn], 'nn0cnd', '( %s -> %s e. CC )' % (ps, F)))], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (pm, F, F))
    f1 = w.s([mc, w.s([ff], 'iftrued', '( %s -> if ( ( %s - %s ) = 0 , 1o , (/) ) = 1o )' % (pm, F, F))], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    exi = w.s([not1o(w, pm, cnfl_m(w, pm, 'm', mm, '1o', f1), CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXIT))
    # the prologue
    tv, dd = mk['tv'], f.dd
    D1 = UP('D', "I'", Z0D)
    kI, kJ, kK = mk['k']["I'"], mk['k']['J'], mk['k']['K']
    togk = lambda X, k, g_: w.s([g_, mk['k'][k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(k)))
    d1 = updcl(w, ps, 'D', "I'", Z0D, tv, dd, kI['kd'], togk(Z0D, "I'", f.z0d))
    dj = w.s([updnv(w, ps, 'D', "I'", Z0D, 'J', tv, dd, kI['kd'], w.s([f.z0d], 'elexd', '( %s -> %s e. _V )' % (ps, Z0D)), kJ['kd'], f.ne('J', "I'")),
              c['( D ` J ) = ( ( inclBool o. G ) ++ %s )' % Y4]], 'eqtrd', '( %s -> ( %s ` J ) = ( ( inclBool o. G ) ++ %s ) )' % (ps, D1, Y4))
    ex = dict(f.ex)
    ex.update({STKD(D1): d1, '( %s ` J ) = ( ( inclBool o. G ) ++ %s )' % (D1, Y4): dj})
    t, cc = inst(w, ps, 'tmiizs', {'K': 'J', 'I': 'I', 'P': PL('P', 2), 'E': PL('P', 1), 'L': 'G', 'X': 'Y', 'D': D1}, Bld(w, ps, c, ex))
    Ca, Da, na = triple_parts(cc)
    OLD = '{ h e. TMSt | ( TMfl ` h ) = if ( ( toNat ` G ) = 0 , 1o , (/) ) }'
    f0 = w.s([w.s([f.fn], 'nn0cnd', '( %s -> %s e. CC )' % (ps, F))], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (ps, F, F))
    ce = w.s([w.s([w.s([w.s([f0], 'eqcomd', '( %s -> %s = ( %s - 0 ) )' % (ps, F, F))], 'eqeq1d', '( %s -> ( %s = 0 <-> ( %s - 0 ) = 0 ) )' % (ps, F, F))],
                  'ifbid', '( %s -> if ( %s = 0 , 1o , (/) ) = if ( ( %s - 0 ) = 0 , 1o , (/) ) )' % (ps, F, F))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = if ( %s = 0 , 1o , (/) ) <-> %s ) )' % (ps, F, NCD('h', '0')))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = if ( %s = 0 , 1o , (/) ) <-> %s ) )' % (ps, F, NCD('h', '0')))],
             'rabbidva', '( %s -> %s = { h e. TMSt | %s } )' % (ps, OLD, NCD('h', '0')))
    z0 = closed(w, ps, '0nn0', '0 e. NN0')
    fv0 = famval(w, ps, NCD, '0', z0)
    rb2 = w.s([rb, w.s([fv0], 'eqcomd', '( %s -> { h e. TMSt | %s } = ( %s ` 0 ) )' % (ps, NCD('h', '0'), NF))], 'eqtrd', '( %s -> %s = ( %s ` 0 ) )' % (ps, OLD, NF))
    cn = clnneq(w, ps, A_, rb2, OLD, '( %s ` 0 )' % NF, D1)
    # PDB( 0 ) = UPD( D , I' , Z0D )
    z0F = w.s([f.fn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, F))
    z0le = w.s([f.fn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ps, F))
    p0, _, _ = f.pdb('0', z0F, z0, z0le)
    dk = c['( D ` K ) = ( %s ++ X )' % ES('L')]
    d0 = w.s([f.lw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = L )' % (ps, DROP('L', '0')))
    a0 = w.s([dk, w.s([w.s([d0], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP('L', '0')), ES('L')))], 'oveq1d',
                      '( %s -> %s = ( %s ++ X ) )' % (ps, At('0'), ES('L')))], 'eqtr4d', '( %s -> ( D ` K ) = %s )' % (ps, At('0')))
    c0 = w.s([f.gw, w.inst('ttwc0')], 'syl', '( %s -> %s = G )' % (ps, CW('0')))
    b0 = w.s([c['( D ` J ) = ( ( inclBool o. G ) ++ %s )' % Y4], w.s([w.s([c0], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. G ) )' % (ps, CW('0')))],
                                                                    'oveq1d', '( %s -> %s = ( ( inclBool o. G ) ++ %s ) )' % (ps, Bt('0'), Y4))],
             'eqtr4d', '( %s -> ( D ` J ) = %s )' % (ps, Bt('0')))
    pz = closed(w, ps, 'pfx00', '%s = (/)' % PFX('L', '0'))
    rz = w.s([w.s([pz], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ps, REV(PFX('L', '0')))), closed(w, ps, 'rev0', '( reverse ` (/) ) = (/)')], 'eqtrd',
             '( %s -> %s = (/) )' % (ps, REV(PFX('L', '0'))))
    ez = w.s([w.s([rz], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(REV(PFX('L', '0'))), ES('(/)'))), closed(w, ps, 'ttses0', ST_ES0)], 'eqtrd',
             '( %s -> %s = (/) )' % (ps, ES(REV(PFX('L', '0')))))
    c0e = w.s([w.s([ez], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, Ct('0'), Z0D)), w.s([f.z0d, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, Z0D, Z0D))],
              'eqtrd', '( %s -> %s = %s )' % (ps, Ct('0'), Z0D))
    u1 = upidv(w, ps, 'D', 'K', At('0'), a0, tv, dd, kK['kd'])
    u2 = upidv(w, ps, 'D', 'J', Bt('0'), b0, tv, dd, kJ['kd'])
    r1, x1 = w.rewrite(PDB('0'), {UP('D', 'K', At('0')): ('D', u1)}, ps)
    r2, x2 = w.rewrite(x1, {UP('D', 'J', Bt('0')): ('D', u2), Ct('0'): (Z0D, c0e)}, ps)
    assert x2 == D1, x2
    pe = w.s([w.s([w.s([p0, r1], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ps, x1)), r2], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ps, D1))], 'eqcomd',
             "( %s -> %s = ( P' ` 0 ) )" % (ps, D1))
    cs = clneq(w, ps, A_, '( %s ` 0 )' % NF, pe, D1, "( P' ` 0 )")
    deq = w.s([cn, cs], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, CLN(A_, '( %s ` 0 )' % NF, "( P' ` 0 )")))
    t1, C1, Dn1, n1 = hrrw(w, ps, t, Ca, Da, na, deq=deq)
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'H': ('NN0', c['H e. NN0'])})
    cl.leaf('( # ` G )', 'NN0', w.s([f.gw, w.inst('lencl')], 'syl', '( %s -> ( # ` G ) e. NN0 )' % ps))
    le = linarith(w, ps, [f.ghb()], '%s <_ %s' % (n1, UB), closure=cl)
    pro = hrle(w, ps, mk['phm'], t1, C1, Dn1, n1, UB, cl.mem(UB, 'NN0'), le)
    # the epilogue
    fF = w.s([f.fn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, F, F))
    fle = w.s([w.s([f.fn], 'nn0red', '( %s -> %s e. RR )' % (ps, F))], 'leidd', '( %s -> %s <_ %s )' % (ps, F, F))
    pF, S0F, SF = f.pdb(F, fF, f.fn, fle)
    awF, bwF, cwF, edF, erF = f.words(F, fF, f.fn, fle)
    XK = UP('D', 'K', At(F))
    xk = stkcl(w, ps, mk, 'D', dd, [('K', At(F))], {At(F): awF})
    sw1 = upc(w, ps, XK, 'J', Bt(F), "I'", Ct(F), tv, xk, f.ne('J', "I'"), kJ['kd'], togk(Bt(F), 'J', bwF), kI['kd'], togk(Ct(F), "I'", cwF))
    D0 = UP(XK, "I'", Ct(F))
    d0s = stkcl(w, ps, mk, 'D', dd, [('K', At(F)), ("I'", Ct(F))], {At(F): awF, Ct(F): cwF})
    cwFw, tnF, lnF = f.cw(F, f.fn, fle)
    WF = '( inclBool o. %s )' % CW(F)
    wfb = w.s([cwFw, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word ( { 1 } X. 2o ) )' % (ps, WF))
    ex2 = dict(f.ex)
    ex2.update({STKD(D0): d0s, '%s e. Word ( { 1 } X. 2o )' % WF: wfb})
    t, cc = inst(w, ps, 'tmidrop', {'K': 'J', 'P': PL('P', 6), 'E': 'E', 'W': WF, 'X': 'Y', 'D': D0}, Bld(w, ps, c, ex2))
    Ca, Da, na = triple_parts(cc)
    assert Ca == CLN(E0_, S, UP(D0, 'J', Bt(F))), Ca
    nssF = f.nfss(F, f.fn)
    tE = hrssc(w, ps, mk['phm'], t, Ca, Da, na, CLN(E0_, NFF, UP(D0, 'J', Bt(F))), clnss(w, ps, E0_, NFF, S, UP(D0, 'J', Bt(F)), nssF))
    pe2 = w.s([w.s([pF, sw1], 'eqtrd', "( %s -> ( P' ` %s ) = %s )" % (ps, F, UP(D0, 'J', Bt(F))))], 'eqcomd', "( %s -> %s = ( P' ` %s ) )" % (ps, UP(D0, 'J', Bt(F)), F))
    ceq = clneq(w, ps, E0_, NFF, pe2, UP(D0, 'J', Bt(F)), "( P' ` %s )" % F)
    sw2 = upc(w, ps, XK, "I'", Ct(F), 'J', 'Y', tv, xk, f.ne("I'", 'J'), kI['kd'], togk(Ct(F), "I'", cwF), kJ['kd'], togk('Y', 'J', f.yw))
    assert concl(w, ps, sw2) == '%s = %s' % (UP(D0, 'J', 'Y'), DFIN_WDN), concl(w, ps, sw2)
    deq2 = clneq(w, ps, 'E', S, sw2, UP(D0, 'J', 'Y'), DFIN_WDN)
    tE2, CE2, DE2, nE2 = hrrw(w, ps, tE, CLN(E0_, NFF, UP(D0, 'J', Bt(F))), Da, na, ceq=ceq, deq=deq2)
    lw_ = w.s([cwFw, w.s([w.s([], 'inclboolf', "inclBool : 2o --> Gamma'")], 'a1i', "( %s -> inclBool : 2o --> Gamma' )" % ps), w.inst('lenco')],
              'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ps, WF, CW(F)))
    cl.leaf('( # ` %s )' % WF, 'NN0', w.s([wfb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, WF)))
    cl.leaf('( # ` %s )' % CW(F), 'NN0', w.s([cwFw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, CW(F))))
    wl = w.s([lw_, lnF], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( # ` G ) )' % (ps, WF))
    le2 = linarith(w, ps, [wl, f.ghb()], '%s <_ %s' % (nE2, UB2), closure=cl)
    epi = hrle(w, ps, mk['phm'], tE2, CE2, DE2, nE2, UB2, cl.mem(UB2, 'NN0'), le2)
    a1 = w.s([typ, exi], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LTYP, LEXIT))
    a2 = w.s([pro, epi], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LPRO, LEPI))
    w.qed([a1, a2], 'jca', ST_T)
    return w.run()


ST_L = '( %s -> %s )' % (PH, LCONCL)


def tmiwdnl():
    lab = 'tmiwdnl'
    w = W(lab, 'Lean\'s ` walkDown ` at the machine with the invariant\'s stack family a letter: ~ tm2fwdn at the '
               'test ` !flag ` , the marker ` blank = 0 ` , the body ~ tmiwdni , the frame ~ tmiwdnt .')
    ps = PH
    f = Wc(w, ps)
    c, mk = f.c, f.mk
    ex = dict(f.ex)
    fr = w.s([], 'tmiwdnt', ST_T)
    ex.update(parts(w, ps, fr, FRAME))
    ex['%s e. NN0' % F] = f.fn
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'H': ('NN0', c['H e. NN0'])})
    for e_ in (TB, UB, UB2):
        ex['%s e. NN0' % e_] = cl.mem(e_, 'NN0')
    ex["0 e. %s" % GX("I'")] = w.s([closed(w, ps, 'gamma0', "0 e. Gamma'"), mk['k']["I'"]['ge']], 'eleqtrrd', '( %s -> 0 e. %s )' % (ps, GX("I'")))
    ex[SSS(S)] = closed(w, ps, 'ssid', '%s C_ %s' % (S, S))
    bi = w.s([], 'tmiwdni', '( %s -> %s )' % (PSI, LBODY))
    ex[LPER] = w.s([bi], 'ralrimiva', '( %s -> %s )' % (ps, LPER))
    st = Bld(w, ps, c, ex)(LTREE)
    w.qed([st, w.inst('tm2fwdn')], 'syl', ST_L)
    return w.run()


def tmiwdn():
    lab = 'tmiwdn'
    ps = cj(TREE_WDN)
    w = W(lab, 'Lean\'s ` walkDown_runs ` at the machine: wherever ` walkDown tbl j s scr ` is installed, the first '
               '` jn = toNat js ` slots of the table ` L ` on ` tbl ` move onto ` scr ` above a ` blank ` marker in '
               'reverse order, the counter on ` j ` is consumed, every other stack restored, within '
               '` jn ( slotC N b + 4 m + 9 ) + 3 m + 8 ` steps (~ tmiwdnl at the family of ` WalkInv ` ).')
    c = Ctx(w, ps, TREE_WDN)
    eqs = {'%s = %s' % (PDF, PDF): closed(w, ps, 'eqid', '%s = %s' % (PDF, PDF))}
    t, cc = inst(w, ps, 'tmiwdnl', {"P'": PDF}, Bld(w, ps, c, eqs))
    Ca, Da, na = triple_parts(cc)
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'H': ('NN0', c['H e. NN0'])})
    cl.leaf(F, 'NN0', w.s([c['G e. Word 2o'], w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ps, F)))
    neq = lineq(w, ps, na, WDNC, closure=cl, products=True)
    hrrw(w, ps, t, Ca, Da, na, neq=neq, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
