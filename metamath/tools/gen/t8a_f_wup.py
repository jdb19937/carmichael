"""T8a: walkUp at the machine (Lean ` walkUp_runs ` ) on its installation predicate TMIwup.

  tmiwupi   one iteration: the body ` moveSlot scr tbl s j ` (~ tmimvs ) and the peek of ` blank `
  tmiwupt   the frame: typings and peek data over ( 0 ... # L ), the exit test, the first peek, the pop
  tmiwupl   ~ tm2fwup assembled, the families as letters P' Z' X'
  tmiwup    walkUp_runs

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_f_wup.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
from lin import linarith, lineq, nlinarith
from t7lib import famval, fam_unpack, fam_pack, mval
from t8a_e_slot import stkcl

SEL = sys.argv[1:]
R_ = '( # ` L )'
Z0X = '( <" 0 "> ++ X )'
QW = '( %s ++ Y )' % ES('U')


def Vt(t):
    return CC(ES(DROP('L', t)), Z0X)


def Wt(t):
    return CC(ES(REV(PFX('L', t))), QW)


def PDB(t):
    return UP(UP('D', 'K', Wt(t)), "I'", Vt(t))


PDF = '( j e. NN0 |-> %s )' % PDB('j')
ZDF = '( j e. NN0 |-> %s )' % HD0(Vt('j'))
XDF = '( j e. NN0 |-> %s )' % TL1(Vt('j'))
NCD = lambda h, t: '( TMfl ` %s ) = if ( %s = %s , 1o , (/) )' % (h, t, R_)
NF = '( j e. NN0 |-> { h e. TMSt | %s } )' % NCD('h', 'j')
N1C = '( NN0 X. { %s } )' % S
FAMEQ = ("P' = %s" % PDF, "Z' = %s" % ZDF, "X' = %s" % XDF)
T_L = (TREE_WUP, FAMEQ)
PH = cj(T_L)
PSI = '( %s /\\ i e. ( 0 ..^ %s ) )' % (PH, R_)

GM = dict(FRAGS['wup'].lmap())
GM.update({'K': "I'", 'F': RDBL, 'C0': CNFL, 'F"': PID, 'R': R_, "T'": SLOTC, 'O': S, 'N': NF, 'N1': N1C, 'P': "P'",
           'Z': "Z'", 'X': "X'", "N'": S})
_LA, _LC = split_imp(stmt('tm2fwup'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)


def find(tree, pred):
    out = []
    def go(t):
        if isinstance(t, str):
            if pred(t):
                out.append(t)
            return
        if pred(cj(t)):
            out.append(cj(t))
        for x in t:
            go(x)
    go(tree)
    return out


LPER = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ..^ '))[0]
LBODY = LPER[len('A. i e. ( 0 ..^ %s ) ' % R_):]
LTYP = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ... %s ) ( ( ( j e. NN0' % R_))[0]
LPKD = find(LTREE, lambda t: t.startswith("A. i e. ( 0 ... %s ) ( ( ( P' ` i ) ` I' )" % R_))[0]
LEXIT = 'A. m e. ( %s ` %s ) -. ( %s ` m ) = 1o' % (NF, R_, CNFL)
LPK0 = "A. r e. %s ( %s ` <. r , ( inl ` ( Z' ` 0 ) ) >. ) e. ( %s ` 0 )" % (S, RDBL, NF)
LPOP = "A. r e. ( %s ` %s ) ( %s ` <. r , ( inl ` ( Z' ` %s ) ) >. ) e. %s" % (NF, R_, PID, R_, S)
for _t in (LEXIT, LPK0, LPOP):
    assert find(LTREE, lambda t, _t=_t: t == _t), _t
FRAME = ((LTYP, LPKD), (LEXIT, LPK0, LPOP))


class Fc:
    """facts under ph (the walkUp antecedent with the family equations, possibly extended)"""
    def __init__(self, w, ph, tree=None, root=None, lets=None):
        self.L = lets or {"P'": "P'", "Z'": "Z'", "X'": "X'"}
        self.w, self.ph = w, ph
        tree = tree or T_L
        if root is None and ph != cj(tree):
            root = w.s([], 'simpl', '( %s -> %s )' % (ph, cj(tree)))
        self.c, self.mk, self.ne, self.ex = hsetup(w, ph, tree, K4, 'wup') if root is None else self._rooted(tree, root)
        c = self.c
        self.lw = c['L e. %s' % WSLOT]
        self.uw = c['U e. %s' % WSLOT]
        self.xw, self.yw, self.dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
        w_ = w
        self.rn = w.s([self.lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, R_))
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        s0 = w.s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        self.zxw = w.s([s0, self.xw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Z0X))
        self.s0 = s0
        eu = w.s([self.uw, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES('U')))
        self.qw = w.s([eu, self.yw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, QW))
        self.memo = {}

    def _rooted(self, tree, root):
        w, ph = self.w, self.ph
        c = Ctx(w, ph, tree, root=root)
        import t8alib
        return t8alib.hsetup.__wrapped__(w, ph, c) if False else self._hs(tree, root)

    def _hs(self, tree, root):
        # hsetup over a rooted Ctx
        w, ph = self.w, self.ph
        c = Ctx(w, ph, tree, root=root)
        mk = machine(w, ph, c, K4)
        ne = ne_fn(w, ph, c, set(flat(dist_tree(K4))))
        base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        base.update(unfold_all(w, ph, c[FRAGS['wup'].pred()], 'wup', K4, 'P', 'E', rec=False))
        f = FRAGS['wup']; lm = f.lmap()
        for j, (fn, cks, en, exn) in enumerate(f.children):
            P_ = PL('P', f.slot(j))
            pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
            base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
        for s_ in K4:
            base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K4):
            for b in K4[i_ + 1:]:
                base['%s =/= %s' % (a, b)] = ne(a, b)
                base['%s =/= %s' % (b, a)] = ne(b, a)
        ex = dict(base)
        ex.update(H.handler_extra(w, ph, mk, H.IFACE))
        hi = w.s([mk['seq'], w.inst('tmctbhi')], 'syl', '( %s -> %s )' % (ph, cj(HI_TREE)))
        ex.update(parts(w, ph, hi, HI_TREE))
        ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
        return c, mk, ne, ex

    def ifz(self, t, tfz):
        """( ph -> t e. ( 0 ... # L ) ) given; returns t e. NN0"""
        return self.w.s([tfz, self.w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (self.ph, t))

    def words(self, t, tfz):
        """typings of the family words at t e. ( 0 ... # L ): V(t), W(t)"""
        key = ('w', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        dr = w.s([self.lw, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DROP('L', t), WSLOT))
        ed = w.s([dr, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(DROP('L', t))))
        vw = w.s([ed, self.zxw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Vt(t)))
        pf = w.s([self.lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, PFX('L', t), WSLOT))
        rp = w.s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REV(PFX('L', t)), WSLOT))
        er = w.s([rp, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(REV(PFX('L', t)))))
        ww = w.s([er, self.qw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Wt(t)))
        self.memo[key] = (vw, ww, ed)
        return self.memo[key]

    def vn0(self, t, tfz):
        """( ph -> V( t ) =/= (/) )"""
        w, ph = self.w, self.ph
        vw, ww, ed = self.words(t, tfz)
        c0 = w.s([ed, self.zxw, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( %s = (/) /\\ %s = (/) ) ) )' % (ph, Vt(t), ES(DROP('L', t)), Z0X))
        c1 = w.s([self.s0, self.xw, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( <" 0 "> = (/) /\\ X = (/) ) ) )' % (ph, Z0X))
        n0 = closed(w, ph, 's1nz', '<" 0 "> =/= (/)')
        n1 = w.s([w.s([n0], 'neneqd', '( %s -> -. <" 0 "> = (/) )' % ph)], 'intnanrd', '( %s -> -. ( <" 0 "> = (/) /\\ X = (/) ) )' % ph)
        n2 = w.s([c1, n1], 'mtbird', '( %s -> -. %s = (/) )' % (ph, Z0X))
        n3 = w.s([n2], 'intnand', '( %s -> -. ( %s = (/) /\\ %s = (/) ) )' % (ph, ES(DROP('L', t)), Z0X))
        n4 = w.s([c0, n3], 'mtbird', '( %s -> -. %s = (/) )' % (ph, Vt(t)))
        return w.s([n4], 'neqned', '( %s -> %s =/= (/) )' % (ph, Vt(t)))

    def pdb(self, t, tfz):
        """( ph -> ( P' ` t ) = PDB( t ) ), ( ph -> PDB( t ) e. Stk ), Stacks-like values"""
        key = ('p', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        vw, ww, ed = self.words(t, tfz)
        st = stkcl(w, ph, self.mk, 'D', self.dd, [('K', Wt(t)), ("I'", Vt(t))], {Wt(t): ww, Vt(t): vw})
        tn = self.ifz(t, tfz)
        v = mval(w, ph, 'j', 'NN0', PDB, t, tn, w.s([st], 'elexd', '( %s -> %s e. _V )' % (ph, PDB(t))))
        PL_ = self.L["P'"]
        e = w.s([self.c['%s = %s' % (PL_, PDF)]], 'fveq1d', "( %s -> ( %s ` %s ) = ( %s ` %s ) )" % (ph, PL_, t, PDF, t))
        r = w.s([e, v], 'eqtrd', "( %s -> ( %s ` %s ) = %s )" % (ph, PL_, t, PDB(t)))
        self.memo[key] = (r, st)
        return r, st

    def fam(self, letter, F, X_of, t, tfz, xex):
        """( ph -> ( letter ` t ) = X_of( t ) ) from the family equation letter = F"""
        w, ph = self.w, self.ph
        tn = self.ifz(t, tfz)
        v = mval(w, ph, 'j', 'NN0', X_of, t, tn, xex)
        letter = self.L[letter]
        e = w.s([self.c['%s = %s' % (letter, F)]], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, letter, t, F, t))
        return w.s([e, v], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, letter, t, X_of(t)))

    def zx(self, t, tfz):
        """( Z' ` t ) = ( V ` 0 ) , ( X' ` t ) = rest, the split of V( t ) and the typings"""
        w, ph = self.w, self.ph
        vw, ww, ed = self.words(t, tfz)
        eq, hg, tg = word_split(w, ph, Vt(t), vw, self.vn0(t, tfz))
        z = self.fam("Z'", ZDF, lambda s: HD0(Vt(s)), t, tfz, w.s([hg], 'elexd', '( %s -> %s e. _V )' % (ph, HD0(Vt(t)))))
        x = self.fam("X'", XDF, lambda s: TL1(Vt(s)), t, tfz, w.s([tg], 'elexd', '( %s -> %s e. _V )' % (ph, TL1(Vt(t)))))
        return z, x, eq, hg, tg

    def zflag(self, t, tfz):
        """( ph -> if ( ( Z' ` t ) = 0 , 1o , (/) ) = if ( t = # L , 1o , (/) ) ) and ( Z' ` t ) e. Gamma'"""
        w, ph = self.w, self.ph
        z, x, eq, hg, tg = self.zx(t, tfz)
        hd = w.s([self.lw, self.xw, tfz, w.inst('ttseshd')], 'syl3anc', '( %s -> ( %s = 0 <-> %s = %s ) )' % (ph, HD0(Vt(t)), t, R_))
        e1 = w.s([z], 'eqeq1d', "( %s -> ( ( Z' ` %s ) = 0 <-> %s = 0 ) )" % (ph, t, HD0(Vt(t))))
        e2 = w.s([e1, hd], 'bitrd', "( %s -> ( ( Z' ` %s ) = 0 <-> %s = %s ) )" % (ph, t, t, R_))
        ifq = w.s([e2], 'ifbid', "( %s -> if ( ( Z' ` %s ) = 0 , 1o , (/) ) = if ( %s = %s , 1o , (/) ) )" % (ph, t, t, R_))
        zg = w.s([z, hg], 'eqeltrd', "( %s -> ( Z' ` %s ) e. Gamma' )" % (ph, t))
        return ifq, zg

    def peek_to_nf(self, Z, zg, ifq, t, tn, DOM, dss):
        """( ph -> A. r e. DOM ( TMrdBlank ` <. r , ( inl ` Z ) >. ) e. ( NF ` t ) ) from
        ifq : ( ph -> if ( Z = 0 , 1o , (/) ) = if ( t = # L , 1o , (/) ) ), dss : ( ph -> DOM C_ S )"""
        w, ph, mk = self.w, self.ph, self.mk
        a = '( %s /\\ r e. %s )' % (ph, DOM)
        L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))
        rs = w.s([L(dss), w.s([], 'simpr', '( %s -> r e. %s )' % (a, DOM))], 'sseldd', '( %s -> r e. %s )' % (a, S))
        rr = w.s([rs, L(mk['seq'])], 'eleqtrd', '( %s -> r e. TMSt )' % a)
        N = '( %s ` <. r , ( inl ` %s ) >. )' % (RDBL, Z)
        m = w.s([rr, L(zg), w.inst('tmcrdblkc')], 'syl2anc', '( %s -> %s e. %s )' % (a, N, HCLS(Z, BLANK)))
        idh = w.s([], 'id', '( h = %s -> h = %s )' % (N, N))
        cond = lambda s: '( TMfl ` %s ) = if ( %s = 0 , 1o , (/) )' % (s, Z)
        cg, new = w.wcongr(cond('h'), {'h': N}, 'h = %s' % N, {'h': idh})
        el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (N, HCLS(Z, BLANK), N, cond(N)))
        both = w.s([m, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (a, N, cond(N)))
        nm = w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (a, N))
        f2 = w.s([w.s([both], 'simprd', '( %s -> %s )' % (a, cond(N))), L(ifq)], 'eqtrd', '( %s -> %s )' % (a, NCD(N, t)))
        p = fam_pack(w, a, NCD, t, L(tn), N, nm, f2)
        return w.s([p], 'ralrimiva', '( %s -> A. r e. %s %s e. ( %s ` %s ) )' % (ph, DOM, N, NF, t))

    def nfss(self, t, tn):
        w, ph = self.w, self.ph
        fv = famval(w, ph, NCD, t, tn)
        rab = '{ h e. TMSt | %s }' % NCD('h', t)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % rab)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, rab))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, rab, S))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ %s )' % (ph, NF, t, S))


def cnfl_m(w, a, m, mmem, flv, flstep):
    return H.cnfl_val(w, a, {'mem': mmem}, m, flv, flstep)


def tmiwupi():
    lab = 'tmiwupi'
    w = W(lab, 'One iteration of Lean\'s ` walkUp ` slot loop at the machine ( ` forSlots_runs ` \'s ` hb ` at the '
               'invariant of ` walkUp_runs ` ): the test ` !flag ` holds while slots are left, ` moveSlot scr tbl s j ` '
               '(~ tmimvs ) moves slot ` i ` of ` L ` from ` scr ` onto ` tbl ` , and the peek of ` blank ` sets the flag '
               'to ` decide ( i + 1 = # L ) ` .')
    ps = PSI
    f = Fc(w, ps)
    c, mk = f.c, f.mk
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (ps, R_))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ifz = w.s([ii, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (ps, R_))
    I1 = '( i + 1 )'
    i1fz = w.s([ii, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ps, I1, R_))
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ps, R_))
    ir = w.s([inn], 'nn0red', '( %s -> i e. RR )' % ps)
    ine = w.s([w.s([ir, ilt], 'ltned', '( %s -> i =/= %s )' % (ps, R_))], 'neneqd', '( %s -> -. i = %s )' % (ps, R_))
    # the test on ( NF ` i )
    NI = '( %s ` i )' % NF
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    f0 = w.s([mc, w.s([Lm(ine)], 'iffalsed', '( %s -> if ( i = %s , 1o , (/) ) = (/) )' % (pm, R_))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ht = w.s([cnfl_m(w, pm, 'm', mm, '(/)', f0)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNFL))
    # N1 ` i = S
    sv = w.s([mk['tv']], 'fvexd' if False else 'id', '') if False else w.s([], 'fvex', '%s e. _V' % S)
    n1v = w.s([w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ps, S)), inn, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` i ) = %s )' % (ps, N1C, S))
    n1s = w.s([n1v, f.ex[SSS(S)]], 'eqsstrd', '( %s -> ( %s ` i ) C_ %s )' % (ps, N1C, S))
    # the body: moveSlot at the stacks PDB( i )
    Li = '( L ` i )'
    li = w.s([f.lw, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (ps, Li, SLOT))
    pi, sti = f.pdb('i', ifz)
    vwi, wwi, edi = f.words('i', ifz)
    vw1, ww1, ed1 = f.words(I1, i1fz)
    P_i = PDB('i')
    pvI = updkv(w, ps, UP('D', 'K', Wt('i')), "I'", Vt('i'), mk['tv'],
                stkcl(w, ps, mk, 'D', f.dd, [('K', Wt('i'))], {Wt('i'): wwi}), mk['k']["I'"]['kd'], w.s([vwi], 'elexd', '( %s -> %s e. _V )' % (ps, Vt('i'))))
    drp = w.s([f.lw, ii, w.inst('ttsesdrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(DROP('L', 'i')), ESL(Li), ES(DROP('L', I1))))
    eli = w.s([li, w.s([w.s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi', "( %s e. %s -> %s e. Word Gamma' )" % (Li, SLOT, ESL(Li)))],
              'syl', "( %s -> %s e. Word Gamma' )" % (ps, ESL(Li)))
    va = w.s([drp], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (ps, Vt('i'), ESL(Li), ES(DROP('L', I1)), Z0X))
    vb = w.s([eli, ed1, f.zxw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ %s ) )' % (ps, ESL(Li), ES(DROP('L', I1)), Z0X, ESL(Li), Vt(I1)))
    vv = w.s([va, vb], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ps, Vt('i'), ESL(Li), Vt(I1)))
    dki = w.s([pvI, vv], 'eqtrd', "( %s -> ( %s ` I' ) = ( %s ++ %s ) )" % (ps, P_i, ESL(Li), Vt(I1)))
    # slot bound of L ` i
    lr = w.s([f.lw, ii, w.inst('algranfv')], 'syl2anc', '( %s -> %s e. ran L )' % (ps, Li))
    ido = w.s([], 'id', '( o = %s -> o = %s )' % (Li, Li))
    cg, new = w.wcongr(SB('o'), {'o': Li}, 'o = %s' % Li, {'o': ido})
    assert new == SB(Li), new
    rsp = w.s([cg], 'rspcv', '( %s e. ran L -> ( %s -> %s ) )' % (Li, RSB, SB(Li)))
    sbi = w.s([lr, c[RSB], rsp], 'sylc', '( %s -> %s )' % (ps, SB(Li)))
    ex = dict(f.ex)
    ex.update({STKD(P_i): sti, 'O e. %s' % SLOT: None})
    del ex['O e. %s' % SLOT]
    ex.update({'%s e. %s' % (Li, SLOT): li, WRD(Vt(I1), GAM): vw1, "( %s ` I' ) = ( %s ++ %s )" % (P_i, ESL(Li), Vt(I1)): dki, SB(Li): sbi})
    MVM = {'K': "I'", 'J': 'K', 'I': 'I', "I'": 'J', 'P': PL('P', 4), 'E': PL('P', 2), 'D': P_i, 'O': Li, 'R': Vt(I1)}
    t, cc = inst(w, ps, 'tmimvs', MVM, Bld(w, ps, c, ex))
    Ca, Da, na = triple_parts(cc)
    # post stacks
    DPOST = UP(UP(P_i, "I'", Vt(I1)), 'K', CC(ESL(Li), '( %s ` K )' % P_i))
    assert Da == CLN(PL('P', 2), S, DPOST), Da
    pK = w.s([updnv(w, ps, UP('D', 'K', Wt('i')), "I'", Vt('i'), 'K', mk['tv'], stkcl(w, ps, mk, 'D', f.dd, [('K', Wt('i'))], {Wt('i'): wwi}),
                    mk['k']["I'"]['kd'], w.s([vwi], 'elexd', '( %s -> %s e. _V )' % (ps, Vt('i'))), mk['k']['K']['kd'], f.ne('K', "I'")),
              updkv(w, ps, 'D', 'K', Wt('i'), mk['tv'], f.dd, mk['k']['K']['kd'], w.s([wwi], 'elexd', '( %s -> %s e. _V )' % (ps, Wt('i'))))],
             'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, P_i, Wt('i')))
    r1, x1 = w.rewrite(DPOST, {'( %s ` K )' % P_i: (Wt('i'), pK)}, ps)
    EW_ = CC(ESL(Li), Wt('i'))
    eww = w.s([eli, wwi, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, EW_))
    chain = [('K', Wt('i')), ("I'", Vt('i')), ("I'", Vt(I1)), ('K', EW_)]
    assert x1 == chain_text('D', chain), x1
    nst, out = stk_normalize(w, ps, mk, 'D', f.dd, f.ne, chain, {Wt('i'): wwi, Vt('i'): vwi, Vt(I1): vw1, EW_: eww}, K4)
    assert out == [('K', EW_), ("I'", Vt(I1))], out
    # EW_ = W( i + 1 )
    rv = w.s([f.lw, ii, w.inst('ttsesrev')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(REV(PFX('L', I1))), ESL(Li), ES(REV(PFX('L', 'i')))))
    pf = w.s([f.lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ps, PFX('L', 'i'), WSLOT))
    erp = w.s([w.s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ps, REV(PFX('L', 'i')), WSLOT)), w.inst('ttsescl')], 'syl',
              "( %s -> %s e. Word Gamma' )" % (ps, ES(REV(PFX('L', 'i')))))
    wa = w.s([eli, erp, f.qw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = %s )' % (ps, ESL(Li), ES(REV(PFX('L', 'i'))), QW, EW_))
    wb = w.s([rv], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (ps, Wt(I1), ESL(Li), ES(REV(PFX('L', 'i'))), QW))
    we = w.s([wb, wa], 'eqtrd', '( %s -> %s = %s )' % (ps, Wt(I1), EW_))
    r2, x2 = w.rewrite(chain_text('D', out), {EW_: (Wt(I1), w.s([we], 'eqcomd', '( %s -> %s = %s )' % (ps, EW_, Wt(I1))))}, ps)
    assert x2 == PDB(I1), x2
    p1, st1 = f.pdb(I1, i1fz)
    fin = w.s([w.s([w.s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (ps, DPOST, chain_text('D', out))), r2], 'eqtrd', '( %s -> %s = %s )' % (ps, DPOST, PDB(I1))),
               p1], 'eqtr4d', "( %s -> %s = ( P' ` %s ) )" % (ps, DPOST, I1))
    deq1 = clneq(w, ps, PL('P', 2), S, fin, DPOST, "( P' ` %s )" % I1)
    deq2 = clnneq(w, ps, PL('P', 2), w.s([n1v], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, S, N1C)), S, '( %s ` i )' % N1C, "( P' ` %s )" % I1)
    deq = w.s([deq1, deq2], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, CLN(PL('P', 2), '( %s ` i )' % N1C, "( P' ` %s )" % I1)))
    # pre: shrink to ( NF ` i ) and P_i -> ( P' ` i )
    B0 = PL(PL('P', 4), 0)
    nss = f.nfss('i', inn)
    t1 = hrssc(w, ps, mk['phm'], t, Ca, Da, na, CLN(B0, NI, P_i), clnss(w, ps, B0, NI, S, P_i, nss))
    ceq = clneq(w, ps, B0, NI, w.s([pi], 'eqcomd', "( %s -> %s = ( P' ` i ) )" % (ps, P_i)), P_i, "( P' ` i )")
    t2, C2, D2, n2 = hrrw(w, ps, t1, CLN(B0, NI, P_i), Da, na, ceq=ceq, deq=deq)
    # the peek of blank after the body
    ifq, zg = f.zflag(I1, i1fz)
    pk = f.peek_to_nf("( Z' ` %s )" % I1, zg, ifq, I1, i1n, '( %s ` i )' % N1C, n1s)
    body = TRI(C2, D2, n2)
    want = LBODY
    got = cj(((HT(NI, CNFL), SSS('( %s ` i )' % N1C)), (body, 'A. r e. ( %s ` i ) ( %s ` <. r , ( inl ` ( Z\' ` %s ) ) >. ) e. ( %s ` %s )'
                                                       % (N1C, RDBL, I1, NF, I1))))
    assert got == want, '\nGOT  %s\nWANT %s' % (got, want)
    a1 = w.s([ht, n1s], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, HT(NI, CNFL), SSS('( %s ` i )' % N1C)))
    a2 = w.s([t2, pk], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, body, concl(w, ps, pk)))
    w.qed([a1, a2], 'jca', '( %s -> %s )' % (ps, LBODY))
    return w.run()


ST_T = '( %s -> %s )' % (PH, cj(FRAME))


def tmiwupt():
    lab = 'tmiwupt'
    w = W(lab, 'The frame of Lean\'s ` walkUp ` slot loop at the machine: the invariant\'s classes and stacks and the '
               'peeked letter over ` 0 ... # L ` , the test ` !flag ` failing at ` # L ` , the first peek of ` blank ` '
               'and the final ` popTop ` .')
    ps = PH
    f = Fc(w, ps)
    mk = f.mk
    # typings and peek data over ( 0 ... R )
    pt = '( %s /\\ i e. ( 0 ... %s ) )' % (ps, R_)
    g = Fc(w, pt)
    ifz = w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (pt, R_))
    inn = w.s([ifz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    pi, sti = g.pdb('i', ifz)
    mem = w.s([pi, sti], 'eqeltrd', "( %s -> ( P' ` i ) e. %s )" % (pt, STK_T))
    ty = w.s([g.nfss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYP[len('A. i e. ( 0 ... %s ) ' % R_):]))
    typ = w.s([ty], 'ralrimiva', '( %s -> %s )' % (ps, LTYP))
    vwi, wwi, edi = g.words('i', ifz)
    pvI = updkv(w, pt, UP('D', 'K', Wt('i')), "I'", Vt('i'), g.mk['tv'],
                stkcl(w, pt, g.mk, 'D', g.dd, [('K', Wt('i'))], {Wt('i'): wwi}), g.mk['k']["I'"]['kd'], w.s([vwi], 'elexd', '( %s -> %s e. _V )' % (pt, Vt('i'))))
    k1 = w.s([w.s([pi], 'fveq1d', "( %s -> ( ( P' ` i ) ` I' ) = ( %s ` I' ) )" % (pt, PDB('i'))), pvI], 'eqtrd', "( %s -> ( ( P' ` i ) ` I' ) = %s )" % (pt, Vt('i')))
    z, x, eq, hg, tg = g.zx('i', ifz)
    k2 = w.s([k1, eq], 'eqtrd', "( %s -> ( ( P' ` i ) ` I' ) = ( <\" %s \"> ++ %s ) )" % (pt, HD0(Vt('i')), TL1(Vt('i'))))
    rz = w.s([w.s([z], 's1eqd', "( %s -> <\" ( Z' ` i ) \"> = <\" %s \"> )" % (pt, HD0(Vt('i')))), x], 'oveq12d',
             "( %s -> ( <\" ( Z' ` i ) \"> ++ ( X' ` i ) ) = ( <\" %s \"> ++ %s ) )" % (pt, HD0(Vt('i')), TL1(Vt('i'))))
    k3 = w.s([k2, rz], 'eqtr4d', "( %s -> ( ( P' ` i ) ` I' ) = ( <\" ( Z' ` i ) \"> ++ ( X' ` i ) ) )" % pt)
    zg = w.s([z, hg], 'eqeltrd', "( %s -> ( Z' ` i ) e. Gamma' )" % pt)
    xg = w.s([x, tg], 'eqeltrd', "( %s -> ( X' ` i ) e. Word Gamma' )" % pt)
    pk = w.s([k3, zg, xg], '3jca', '( %s -> %s )' % (pt, LPKD[len('A. i e. ( 0 ... %s ) ' % R_):]))
    pkd = w.s([pk], 'ralrimiva', '( %s -> %s )' % (ps, LPKD))
    # exit
    NR = '( %s ` %s )' % (NF, R_)
    pm = '( %s /\\ m e. %s )' % (ps, NR)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, R_, Lm(f.rn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NR)))
    f1 = w.s([mc, w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (pm, R_, R_))], 'iftrued', '( %s -> if ( %s = %s , 1o , (/) ) = 1o )' % (pm, R_, R_))],
             'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    c0 = cnfl_m(w, pm, 'm', mm, '1o', f1)
    exi = w.s([not1o(w, pm, c0, CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXIT))
    # the first peek
    z0 = w.s([f.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, R_))
    ifq0, zg0 = f.zflag('0', z0)
    pk0 = f.peek_to_nf("( Z' ` 0 )", zg0, ifq0, '0', closed(w, ps, '0nn0', '0 e. NN0'), S, f.ex[SSS(S)])
    # the final pop
    rfz = w.s([f.rn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, R_, R_))
    ifqr, zgr = f.zflag(R_, rfz)
    pop = pop_iface(w, ps, mk, NR, f.nfss(R_, f.rn), "( Z' ` %s )" % R_, zgr)
    a1 = w.s([typ, pkd], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LTYP, LPKD))
    a2 = w.s([exi, pk0, pop], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ps, LEXIT, LPK0, LPOP))
    w.qed([a1, a2], 'jca', ST_T)
    return w.run()


ST_L = '( %s -> %s )' % (PH, LCONCL)


def tmiwupl():
    lab = 'tmiwupl'
    w = W(lab, 'Lean\'s ` walkUp ` at the machine with the invariant\'s families as letters: ~ tm2fwup at the '
               'handlers ` readBlank ` , ` !flag ` , ` fun v _ => v ` , the body ~ tmiwupi , the frame ~ tmiwupt .')
    ps = PH
    f = Fc(w, ps)
    ex = dict(f.ex)
    fr = w.s([], 'tmiwupt', ST_T)
    ex.update(parts(w, ps, fr, FRAME))
    ex['%s e. NN0' % R_] = f.rn
    cl = Closure(w, ps, {'N': ('NN0', f.c['N e. NN0']), 'B': ('NN0', f.c['B e. NN0'])})
    ex['%s e. NN0' % SLOTC] = cl.mem(SLOTC, 'NN0')
    bi = w.s([], 'tmiwupi', '( %s -> %s )' % (PSI, LBODY))
    ex[LPER] = w.s([bi], 'ralrimiva', '( %s -> %s )' % (ps, LPER))
    st = Bld(w, ps, f.c, ex)(LTREE)
    w.qed([st, w.inst('tm2fwup')], 'syl', ST_L)
    return w.run()


def tmiwup():
    lab = 'tmiwup'
    ps = cj(TREE_WUP)
    w = W(lab, 'Lean\'s ` walkUp_runs ` at the machine: wherever ` walkUp tbl j s scr ` is installed, the slots ` L ` on '
               '` scr ` (down to the ` blank ` marker, which is popped) move back onto ` tbl ` in reverse order, every '
               'other stack restored, within ` L.length ( slotC N b + 2 ) + 3 ` steps (~ tmiwupl at the families of '
               '` SlotsInv ` ).')
    c = Ctx(w, ps, TREE_WUP)
    eqs = {'%s = %s' % (F_, F_): closed(w, ps, 'eqid', '%s = %s' % (F_, F_)) for F_ in (PDF, ZDF, XDF)}
    t, cc = inst(w, ps, 'tmiwupl', {"P'": PDF, "Z'": ZDF, "X'": XDF}, Bld(w, ps, c, eqs))
    Ca, Da, na = triple_parts(cc)
    TL = tsub(T_L, {"P'": PDF, "Z'": ZDF, "X'": XDF})
    root = Bld(w, ps, c, eqs)(TL)
    f = Fc(w, ps, tree=TL, root=root, lets={"P'": PDF, "Z'": ZDF, "X'": XDF})
    mk = f.mk
    fam = {"P'": PDF, "X'": XDF}
    # ( PDF ` 0 ) = D
    z0 = w.s([f.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, R_))
    p0, st0 = f.pdb('0', z0)
    p0 = w.s([p0], 'id', '') if False else p0
    vw0, ww0, ed0 = f.words('0', z0)
    pz = closed(w, ps, 'pfx00', '%s = (/)' % PFX('L', '0'))
    rz = w.s([w.s([pz], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ps, REV(PFX('L', '0')))), closed(w, ps, 'rev0', '( reverse ` (/) ) = (/)')], 'eqtrd',
             '( %s -> %s = (/) )' % (ps, REV(PFX('L', '0'))))
    ez = w.s([w.s([rz], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(REV(PFX('L', '0'))), ES('(/)'))), closed(w, ps, 'ttses0', ST_ES0)], 'eqtrd',
             '( %s -> %s = (/) )' % (ps, ES(REV(PFX('L', '0')))))
    w0 = w.s([w.s([ez], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, Wt('0'), QW)), w.s([f.qw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, QW, QW))],
             'eqtrd', '( %s -> %s = %s )' % (ps, Wt('0'), QW))
    dk = c['( D ` K ) = %s' % QW]
    wk = w.s([dk, w0], 'eqtr4d', '( %s -> ( D ` K ) = %s )' % (ps, Wt('0')))
    d0 = w.s([f.lw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = L )' % (ps, DROP('L', '0')))
    v0 = w.s([w.s([d0], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP('L', '0')), ES('L')))], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (ps, Vt('0'), ES('L'), Z0X))
    di = c["( D ` I' ) = ( %s ++ %s )" % (ES('L'), Z0X)]
    vi = w.s([di, v0], 'eqtr4d', "( %s -> ( D ` I' ) = %s )" % (ps, Vt('0')))
    u1 = upidv(w, ps, 'D', 'K', Wt('0'), wk, mk['tv'], f.dd, mk['k']['K']['kd'])
    r1, x1 = w.rewrite(PDB('0'), {UP('D', 'K', Wt('0')): ('D', u1)}, ps)
    u2 = upidv(w, ps, 'D', "I'", Vt('0'), vi, mk['tv'], f.dd, mk['k']["I'"]['kd'])
    pd = w.s([w.s([p0, r1], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ps, PDF, x1)), u2], 'eqtrd', '( %s -> ( %s ` 0 ) = D )' % (ps, PDF))
    ceq = clneq(w, ps, PL('P', 0), S, pd, '( %s ` 0 )' % PDF, 'D')
    # the final stacks
    rfz = w.s([f.rn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, R_, R_))
    pr, str_ = f.pdb(R_, rfz)
    z, x, eq, hg, tg = f.zx(R_, rfz)
    vwr, wwr, edr = f.words(R_, rfz)
    FIN0 = UP('( %s ` %s )' % (PDF, R_), "I'", '( %s ` %s )' % (XDF, R_))
    r2, x2 = w.rewrite(FIN0, {'( %s ` %s )' % (PDF, R_): (PDB(R_), pr), '( %s ` %s )' % (XDF, R_): (TL1(Vt(R_)), x)}, ps)
    assert x2 == UP(PDB(R_), "I'", TL1(Vt(R_))), x2
    togk = lambda X, k, g: w.s([g, mk['k'][k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(k)))
    DKW = UP('D', 'K', Wt(R_))
    dkw = stkcl(w, ps, mk, 'D', f.dd, [('K', Wt(R_))], {Wt(R_): wwr})
    u3 = up2(w, ps, DKW, "I'", Vt(R_), TL1(Vt(R_)), mk['tv'], dkw, mk['k']["I'"]['kd'], togk(Vt(R_), "I'", vwr), togk(TL1(Vt(R_)), "I'", tg))
    # W( # L ) = ES( rev L ++ U ) ++ Y
    pl = w.s([f.lw, w.inst('pfxid')], 'syl', '( %s -> %s = L )' % (ps, PFX('L', R_)))
    rl = w.s([f.lw, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ps, REV('L'), WSLOT))
    e1 = w.s([w.s([pl], 'fveq2d', '( %s -> %s = %s )' % (ps, REV(PFX('L', R_)), REV('L')))], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(REV(PFX('L', R_))), ES(REV('L'))))
    ecc = w.s([rl, f.uw, w.inst('ttsesccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES('( %s ++ U )' % REV('L')), ES(REV('L')), ES('U')))
    erl = w.s([rl, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ps, ES(REV('L'))))
    eu = w.s([f.uw, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ps, ES('U')))
    ass = w.s([erl, eu, f.yw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ Y ) = ( %s ++ %s ) )' % (ps, ES(REV('L')), ES('U'), ES(REV('L')), QW))
    TGT = CC(ES('( %s ++ U )' % REV('L')), 'Y')
    e2 = w.s([w.s([ecc], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ Y ) )' % (ps, TGT, ES(REV('L')), ES('U'))), ass], 'eqtrd',
             '( %s -> %s = ( %s ++ %s ) )' % (ps, TGT, ES(REV('L')), QW))
    e3 = w.s([w.s([e1], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (ps, Wt(R_), ES(REV('L')), QW)), e2], 'eqtr4d', '( %s -> %s = %s )' % (ps, Wt(R_), TGT))
    # TL1( V( # L ) ) = X
    sw = closed(w, ps, 'swrd00', '( L substr <. %s , %s >. ) = (/)' % (R_, R_))
    ev = w.s([w.s([w.s([sw], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP('L', R_)), ES('(/)'))), closed(w, ps, 'ttses0', ST_ES0)], 'eqtrd',
                  '( %s -> %s = (/) )' % (ps, ES(DROP('L', R_))))], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, Vt(R_), Z0X))
    vr = w.s([ev, w.s([f.zxw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, Z0X, Z0X))], 'eqtrd', '( %s -> %s = %s )' % (ps, Vt(R_), Z0X))
    r4, x4 = w.rewrite(TL1(Vt(R_)), {Vt(R_): (Z0X, vr)}, ps)
    assert x4 == TL1(Z0X), x4
    n1 = closed(w, ps, 's1len', '( # ` <" 0 "> ) = 1')
    n1r = w.s([n1], 'eqcomd', '( %s -> 1 = ( # ` <" 0 "> ) )' % ps)
    cln = w.s([f.s0, f.xw, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" 0 "> ) + ( # ` X ) ) )' % (ps, Z0X))
    o1 = w.s([n1r, cln], 'opeq12d', '( %s -> <. 1 , ( # ` %s ) >. = <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` X ) ) >. )' % (ps, Z0X))
    o2 = w.s([o1], 'oveq2d', '( %s -> %s = ( %s substr <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` X ) ) >. ) )' % (ps, TL1(Z0X), Z0X))
    s2 = w.s([f.s0, f.xw, w.inst('swrdccat2')], 'syl2anc', '( %s -> ( %s substr <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` X ) ) >. ) = X )' % (ps, Z0X))
    tx = w.s([w.s([r4, o2], 'eqtrd', '( %s -> %s = ( %s substr <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` X ) ) >. ) )' % (ps, TL1(Vt(R_)), Z0X)), s2],
             'eqtrd', '( %s -> %s = X )' % (ps, TL1(Vt(R_))))
    r5, x5 = w.rewrite(UP(DKW, "I'", TL1(Vt(R_))), {Wt(R_): (TGT, e3), TL1(Vt(R_)): ('X', tx)}, ps)
    FIN = UP(UP('D', 'K', TGT), "I'", 'X')
    assert x5 == FIN, x5
    fe = w.s([w.s([r2, u3], 'eqtrd', '( %s -> %s = %s )' % (ps, FIN0, UP(DKW, "I'", TL1(Vt(R_))))), r5], 'eqtrd', '( %s -> %s = %s )' % (ps, FIN0, FIN))
    deq = clneq(w, ps, 'E', S, fe, FIN0, FIN)
    hrrw(w, ps, t, Ca, Da, na, ceq=ceq, deq=deq, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
