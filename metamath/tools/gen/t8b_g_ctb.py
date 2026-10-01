"""T8b: copyTbl at the machine (Lean ` copyTbl_runs ` ) on its installation predicate TMIctb.

  tmictbi   one iteration: the body ` copySlot src dst s s' ; moveSlot src hold s s' ` (~ tmicps , ~ tmimvs )
            and the peek of ` blank `
  tmictbt   the frame: typings and peek data over ( 0 ... # L ), the exit test, the first peek
  tmictbl   ~ tm2fctb assembled, the families as letters P' Z' X'
  tmictb    copyTbl_runs

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_g_ctb.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, lineq, nlinarith
from t7lib import famval, fam_unpack, fam_pack, mval
from t8a_e_slot import stkcl
from t8a_f_wup import find, cnfl_m

SEL = sys.argv[1:]
R_ = '( # ` L )'
Z0X = '( <" 0 "> ++ X )'
QJ = '( <" 0 "> ++ ( D ` J ) )'
QI = '( <" 0 "> ++ ( D ` I ) )'


def Vt(t):
    return CC(ES(DROP('L', t)), Z0X)


def Jt(t):
    return CC(ES(REV(PFX('L', t))), QJ)


def It(t):
    return CC(ES(REV(PFX('L', t))), QI)


def PDB(t):
    return UP(UP(UP('D', 'K', Vt(t)), 'J', Jt(t)), 'I', It(t))


PDF = '( j e. NN0 |-> %s )' % PDB('j')
ZDF = '( j e. NN0 |-> %s )' % HD0(Vt('j'))
XDF = '( j e. NN0 |-> %s )' % TL1(Vt('j'))
NCD = lambda h, t: '( TMfl ` %s ) = if ( %s = %s , 1o , (/) )' % (h, t, R_)
NF = '( j e. NN0 |-> { h e. TMSt | %s } )' % NCD('h', 'j')
N1C = '( NN0 X. { %s } )' % S
FAMEQ = ("P' = %s" % PDF, "Z' = %s" % ZDF, "X' = %s" % XDF)
T_L = (TREE_CTB, FAMEQ)
PH = cj(T_L)
PSI = '( %s /\\ i e. ( 0 ..^ %s ) )' % (PH, R_)
TB = '( %s + %s )' % (CPSC, SLOTC)          # the body's bound T'
# the walkUp triple's bound at the slot list ( reverse ` L )
WUPR = '( ( ( # ` %s ) x. ( %s + 2 ) ) + 3 )' % (REV('L'), SLOTC)

GM = dict(FRAGS['ctb'].lmap())
GM.update({'K': 'K', 'J': 'J', 'I': 'I', 'F': RDBL, 'C0': CNFL, 'Y': BLANK, 'R': R_, "T'": TB, 'O': S, 'N': NF, 'N1': N1C,
           'P': "P'", 'Z': "Z'", 'X': "X'", 'U': WUPR, 'D': 'D', "N'": S, "D'": DFIN_CTB})
_LA, _LC = split_imp(stmt('tm2fctb'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LPER = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ..^ '))[0]
LBODY = LPER[len('A. i e. ( 0 ..^ %s ) ' % R_):]
LTYP = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ... %s ) ( ( ( j e. NN0' % R_))[0]
LPKD = find(LTREE, lambda t: t.startswith("A. i e. ( 0 ... %s ) ( ( ( P' ` i ) ` K )" % R_))[0]
LEXIT = 'A. m e. ( %s ` %s ) -. ( %s ` m ) = 1o' % (NF, R_, CNFL)
LPK0 = "A. r e. %s ( %s ` <. r , ( inl ` ( Z' ` 0 ) ) >. ) e. ( %s ` 0 )" % (S, RDBL, NF)
for _t in (LEXIT, LPK0):
    assert find(LTREE, lambda t, _t=_t: t == _t), _t
FRAME = ((LTYP, LPKD), (LEXIT, LPK0))


class Fc:
    """facts under ph (the copyTbl antecedent with the family equations, possibly extended)"""
    def __init__(self, w, ph, tree=None, root=None, lets=None):
        self.L = lets or {"P'": "P'", "Z'": "Z'", "X'": "X'"}
        self.w, self.ph = w, ph
        tree = tree or T_L
        if root is None and ph != cj(tree):
            root = w.s([], 'simpl', '( %s -> %s )' % (ph, cj(tree)))
        self.c, self.mk, self.ne, self.ex = self._hs(tree, root)
        c = self.c
        self.lw = c['L e. %s' % WSLOT]
        self.xw, self.dd = c[WRD('X', GAM)], c[STKD('D')]
        self.rn = w.s([self.lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, R_))
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        s0 = w.s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        self.s0 = s0
        self.zxw = w.s([s0, self.xw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Z0X))
        mk, dd = self.mk, self.dd
        self.dj = w.s([stkfv(w, ph, 'D', 'J', mk['tv'], dd, mk['k']['J']['kd']), mk['k']['J']['wge']], 'eleqtrd', "( %s -> ( D ` J ) e. Word Gamma' )" % ph)
        self.di = w.s([stkfv(w, ph, 'D', 'I', mk['tv'], dd, mk['k']['I']['kd']), mk['k']['I']['wge']], 'eleqtrd', "( %s -> ( D ` I ) e. Word Gamma' )" % ph)
        self.qj = w.s([s0, self.dj, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, QJ))
        self.qi = w.s([s0, self.di, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, QI))
        self.memo = {}

    def _hs(self, tree, root):
        w, ph = self.w, self.ph
        c = Ctx(w, ph, tree, root=root) if root is not None else Ctx(w, ph, tree)
        mk = machine(w, ph, c, K5)
        ne = ne_fn(w, ph, c, set(flat(dist_tree(K5))))
        base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        base.update(unfold_all(w, ph, c[FRAGS['ctb'].pred()], 'ctb', K5, 'P', 'E', rec=False))
        f = FRAGS['ctb']; lm = f.lmap()
        for j, (fn, cks, en, exn) in enumerate(f.children):
            P_ = PL('P', f.slot(j))
            pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
            base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
        for s_ in K5:
            base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K5):
            for b in K5[i_ + 1:]:
                base['%s =/= %s' % (a, b)] = ne(a, b)
                base['%s =/= %s' % (b, a)] = ne(b, a)
        ex = dict(base)
        ex.update(H.handler_extra(w, ph, mk, H.IFACE))
        hi = w.s([mk['seq'], w.inst('tmctbhi')], 'syl', '( %s -> %s )' % (ph, cj(HI_TREE)))
        ex.update(parts(w, ph, hi, HI_TREE))
        FLT = (('TMcar e. ( 2o ^m ( 2nd ` T ) )', 'TMda e. ( 2o ^m ( 2nd ` T ) )'),
               ('TMdb e. ( 2o ^m ( 2nd ` T ) )', 'TMfl e. ( 2o ^m ( 2nd ` T ) )'))
        fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ph, cj(FLT)))
        ex.update(parts(w, ph, fl, FLT))
        for n in ('0', '2', '3', '4'):
            ex["%s e. Gamma'" % n] = closed(w, ph, 'gamma%s' % n, "%s e. Gamma'" % n)
        ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
        return c, mk, ne, ex

    def ifz(self, t, tfz):
        return self.w.s([tfz, self.w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (self.ph, t))

    def words(self, t, tfz):
        """typings of the family words at t e. ( 0 ... # L ): V( t ), J( t ), I( t ), ES( drop ), ES( rev pfx )"""
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
        jw = w.s([er, self.qj, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Jt(t)))
        iw = w.s([er, self.qi, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, It(t)))
        self.memo[key] = (vw, jw, iw, ed, er)
        return self.memo[key]

    def vn0(self, t, tfz):
        w, ph = self.w, self.ph
        vw, jw, iw, ed, er = self.words(t, tfz)
        c0 = w.s([ed, self.zxw, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( %s = (/) /\\ %s = (/) ) ) )' % (ph, Vt(t), ES(DROP('L', t)), Z0X))
        c1 = w.s([self.s0, self.xw, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( <" 0 "> = (/) /\\ X = (/) ) ) )' % (ph, Z0X))
        n0 = closed(w, ph, 's1nz', '<" 0 "> =/= (/)')
        n1 = w.s([w.s([n0], 'neneqd', '( %s -> -. <" 0 "> = (/) )' % ph)], 'intnanrd', '( %s -> -. ( <" 0 "> = (/) /\\ X = (/) ) )' % ph)
        n2 = w.s([c1, n1], 'mtbird', '( %s -> -. %s = (/) )' % (ph, Z0X))
        n3 = w.s([n2], 'intnand', '( %s -> -. ( %s = (/) /\\ %s = (/) ) )' % (ph, ES(DROP('L', t)), Z0X))
        n4 = w.s([c0, n3], 'mtbird', '( %s -> -. %s = (/) )' % (ph, Vt(t)))
        return w.s([n4], 'neqned', '( %s -> %s =/= (/) )' % (ph, Vt(t)))

    def stacks(self, t, tfz):
        """the Stacks object of PDB( t ) (base D)"""
        key = ('s', t)
        if key in self.memo:
            return self.memo[key]
        w, ph, mk = self.w, self.ph, self.mk
        vw, jw, iw, ed, er = self.words(t, tfz)
        vals = {k: selfval(w, ph, mk, 'D', self.dd, k) for k in K5}
        st = Stacks(w, ph, mk, 'D', self.dd, self.ne, vals).upd('K', Vt(t), vw).upd('J', Jt(t), jw).upd('I', It(t), iw)
        assert st.D == PDB(t)
        self.memo[key] = st
        return st

    def pdb(self, t, tfz):
        """( ph -> ( P' ` t ) = PDB( t ) ), the Stacks of PDB( t )"""
        key = ('p', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        st = self.stacks(t, tfz)
        tn = self.ifz(t, tfz)
        v = mval(w, ph, 'j', 'NN0', PDB, t, tn, w.s([st.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PDB(t))))
        PL_ = self.L["P'"]
        e = w.s([self.c['%s = %s' % (PL_, PDF)]], 'fveq1d', "( %s -> ( %s ` %s ) = ( %s ` %s ) )" % (ph, PL_, t, PDF, t))
        r = w.s([e, v], 'eqtrd', "( %s -> ( %s ` %s ) = %s )" % (ph, PL_, t, PDB(t)))
        self.memo[key] = (r, st)
        return r, st

    def fam(self, letter, F, X_of, t, tfz, xex):
        w, ph = self.w, self.ph
        tn = self.ifz(t, tfz)
        v = mval(w, ph, 'j', 'NN0', X_of, t, tn, xex)
        letter = self.L[letter]
        e = w.s([self.c['%s = %s' % (letter, F)]], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, letter, t, F, t))
        return w.s([e, v], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, letter, t, X_of(t)))

    def zx(self, t, tfz):
        w, ph = self.w, self.ph
        vw, jw, iw, ed, er = self.words(t, tfz)
        eq, hg, tg = word_split(w, ph, Vt(t), vw, self.vn0(t, tfz))
        z = self.fam("Z'", ZDF, lambda s: HD0(Vt(s)), t, tfz, w.s([hg], 'elexd', '( %s -> %s e. _V )' % (ph, HD0(Vt(t)))))
        x = self.fam("X'", XDF, lambda s: TL1(Vt(s)), t, tfz, w.s([tg], 'elexd', '( %s -> %s e. _V )' % (ph, TL1(Vt(t)))))
        return z, x, eq, hg, tg

    def zflag(self, t, tfz):
        w, ph = self.w, self.ph
        z, x, eq, hg, tg = self.zx(t, tfz)
        hd = w.s([self.lw, self.xw, tfz, w.inst('ttseshd')], 'syl3anc', '( %s -> ( %s = 0 <-> %s = %s ) )' % (ph, HD0(Vt(t)), t, R_))
        e1 = w.s([z], 'eqeq1d', "( %s -> ( ( Z' ` %s ) = 0 <-> %s = 0 ) )" % (ph, t, HD0(Vt(t))))
        e2 = w.s([e1, hd], 'bitrd', "( %s -> ( ( Z' ` %s ) = 0 <-> %s = %s ) )" % (ph, t, t, R_))
        ifq = w.s([e2], 'ifbid', "( %s -> if ( ( Z' ` %s ) = 0 , 1o , (/) ) = if ( %s = %s , 1o , (/) ) )" % (ph, t, t, R_))
        zg = w.s([z, hg], 'eqeltrd', "( %s -> ( Z' ` %s ) e. Gamma' )" % (ph, t))
        return ifq, zg

    def peek_to_nf(self, Z, zg, ifq, t, tn, DOM, dss):
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


def tmictbi():
    lab = 'tmictbi'
    w = W(lab, 'One iteration of Lean\'s ` copyTbl ` slot loop at the machine ( ` forSlots_runs ` \'s ` hb ` at the '
               'invariant of ` copyTbl_runs ` ): the test ` !flag ` holds while slots are left, ` copySlot src dst s s\' ` '
               '(~ tmicps ) pushes a copy of slot ` i ` on ` dst ` , ` moveSlot src hold s s\' ` (~ tmimvs ) moves it onto '
               '` hold ` , and the peek of ` blank ` sets the flag to ` decide ( i + 1 = # L ) ` .')
    ps = PSI
    f = Fc(w, ps)
    c, mk = f.c, f.mk
    s = w.s
    ii = s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (ps, R_))
    inn = s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ifz = s([ii, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (ps, R_))
    I1 = '( i + 1 )'
    i1fz = s([ii, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ps, I1, R_))
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    ilt = s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ps, R_))
    ir = s([inn], 'nn0red', '( %s -> i e. RR )' % ps)
    ine = s([s([ir, ilt], 'ltned', '( %s -> i =/= %s )' % (ps, R_))], 'neneqd', '( %s -> -. i = %s )' % (ps, R_))
    NI = '( %s ` i )' % NF
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, 'i', Lm(inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    f0 = s([mc, s([Lm(ine)], 'iffalsed', '( %s -> if ( i = %s , 1o , (/) ) = (/) )' % (pm, R_))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ht = s([cnfl_m(w, pm, 'm', mm, '(/)', f0)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNFL))
    sv = s([], 'fvex', '%s e. _V' % S)
    n1v = s([s([sv], 'a1i', '( %s -> %s e. _V )' % (ps, S)), inn, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` i ) = %s )' % (ps, N1C, S))
    n1s = s([n1v, f.ex[SSS(S)]], 'eqsstrd', '( %s -> ( %s ` i ) C_ %s )' % (ps, N1C, S))
    # the body at PDB( i )
    Li = '( L ` i )'
    li = s([f.lw, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (ps, Li, SLOT))
    pi, Si = f.pdb('i', ifz)
    vw1, jw1, iw1, ed1, er1 = f.words(I1, i1fz)
    drp = s([f.lw, ii, w.inst('ttsesdrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(DROP('L', 'i')), ESL(Li), ES(DROP('L', I1))))
    eli = s([li, s([s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi', "( %s e. %s -> %s e. Word Gamma' )" % (Li, SLOT, ESL(Li)))],
            'syl', "( %s -> %s e. Word Gamma' )" % (ps, ESL(Li)))
    va = s([drp], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (ps, Vt('i'), ESL(Li), ES(DROP('L', I1)), Z0X))
    vb = s([eli, ed1, f.zxw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ %s ) )' % (ps, ESL(Li), ES(DROP('L', I1)), Z0X, ESL(Li), Vt(I1)))
    vv = s([va, vb], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ps, Vt('i'), ESL(Li), Vt(I1)))
    dki = s([Si.vals['K'][1], vv], 'eqtrd', "( %s -> ( %s ` K ) = ( %s ++ %s ) )" % (ps, PDB('i'), ESL(Li), Vt(I1)))
    lr = s([f.lw, ii, w.inst('algranfv')], 'syl2anc', '( %s -> %s e. ran L )' % (ps, Li))
    ido = s([], 'id', '( o = %s -> o = %s )' % (Li, Li))
    cg, new = w.wcongr(SB('o'), {'o': Li}, 'o = %s' % Li, {'o': ido})
    rsp = s([cg], 'rspcv', '( %s e. ran L -> ( %s -> %s ) )' % (Li, RSB, SB(Li)))
    sbi = s([lr, c[RSB], rsp], 'sylc', '( %s -> %s )' % (ps, SB(Li)))
    ex = dict(f.ex)
    ex.update({'%s e. %s' % (Li, SLOT): li, WRD(Vt(I1), GAM): vw1, SB(Li): sbi})
    run = Run(w, ps, mk, Si, ex, c)
    EJ = CC(ESL(Li), Jt('i'))
    ejw = s([eli, Si.vals['J'][2], w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, EJ))
    run.call('tmicps', {'K': 'K', 'J': 'J', 'I': "I'", "I'": 'I"', 'P': PL('P', 5), 'E': PL(PL('P', 6), 0), 'O': Li, 'R': Vt(I1)},
             {'( %s ` K ) = ( %s ++ %s )' % (PDB('i'), ESL(Li), Vt(I1)): dki}, [('J', EJ, ejw)])
    S1 = run.S
    EI = CC(ESL(Li), It('i'))
    eiw = s([eli, Si.vals['I'][2], w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, EI))
    dk1 = s([S1.vals['K'][1], vv], 'eqtrd', "( %s -> ( %s ` K ) = ( %s ++ %s ) )" % (ps, S1.D, ESL(Li), Vt(I1)))
    run.call('tmimvs', {'K': 'K', 'J': 'I', 'I': "I'", "I'": 'I"', 'P': PL('P', 6), 'E': PL('P', 4), 'O': Li, 'R': Vt(I1)},
             {'( %s ` K ) = ( %s ++ %s )' % (S1.D, ESL(Li), Vt(I1)): dk1}, [('K', Vt(I1), vw1), ('I', EI, eiw)])
    cur, out = run.normalize(K5)
    assert out == [('K', Vt(I1)), ('J', EJ), ('I', EI)], out
    # EJ = J( i + 1 ), EI = I( i + 1 )
    rv = s([f.lw, ii, w.inst('ttsesrev')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(REV(PFX('L', I1))), ESL(Li), ES(REV(PFX('L', 'i')))))
    vwi, jwi, iwi, edi, eri = f.words('i', ifz)
    rules = {}
    for Q, qw, Et, Tt in ((QJ, f.qj, EJ, Jt), (QI, f.qi, EI, It)):
        wa = s([eli, eri, qw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = %s )' % (ps, ESL(Li), ES(REV(PFX('L', 'i'))), Q, Et))
        wb = s([rv], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (ps, Tt(I1), ESL(Li), ES(REV(PFX('L', 'i'))), Q))
        we = s([wb, wa], 'eqtrd', '( %s -> %s = %s )' % (ps, Tt(I1), Et))
        rules[Et] = (Tt(I1), s([we], 'eqcomd', '( %s -> %s = %s )' % (ps, Et, Tt(I1))))
    DP0 = chain_text(PDB('i'), out)
    chi = [('K', Vt('i')), ('J', Jt('i')), ('I', It('i'))] + out
    assert chain_text('D', chi) == DP0
    gm = {Vt('i'): vwi, Jt('i'): jwi, It('i'): iwi, Vt(I1): vw1, EJ: ejw, EI: eiw}
    nst, out2 = stk_normalize(w, ps, mk, 'D', f.dd, f.ne, chi, gm, K5)
    assert out2 == out, out2
    DPOST = chain_text('D', out2)
    r2, x2 = w.rewrite(DPOST, rules, ps)
    r2 = s([nst, r2], 'eqtrd', '( %s -> %s = %s )' % (ps, DP0, x2))
    assert x2 == PDB(I1), x2
    p1, S1_ = f.pdb(I1, i1fz)
    fin = s([r2, p1], 'eqtr4d', "( %s -> %s = ( P' ` %s ) )" % (ps, DP0, I1))
    Ca, Da, na = run.C0, run.cur, run.n
    E4 = PL('P', 4)
    deq1 = clneq(w, ps, E4, S, fin, DP0, "( P' ` %s )" % I1)
    deq2 = clnneq(w, ps, E4, s([n1v], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, S, N1C)), S, '( %s ` i )' % N1C, "( P' ` %s )" % I1)
    deq = s([deq1, deq2], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, CLN(E4, '( %s ` i )' % N1C, "( P' ` %s )" % I1)))
    B0 = PL(PL('P', 5), 0)
    nss = f.nfss('i', inn)
    t1 = hrssc(w, ps, mk['phm'], run.tri, Ca, Da, na, CLN(B0, NI, PDB('i')), clnss(w, ps, B0, NI, S, PDB('i'), nss))
    ceq = clneq(w, ps, B0, NI, s([pi], 'eqcomd', "( %s -> %s = ( P' ` i ) )" % (ps, PDB('i'))), PDB('i'), "( P' ` i )")
    neq = s([], 'eqidd', '( %s -> %s = %s )' % (ps, na, na))
    assert na == '( %s + %s )' % (CPSC, SLOTC), na
    t2, C2, D2, n2 = hrrw(w, ps, t1, CLN(B0, NI, PDB('i')), Da, na, ceq=ceq, deq=deq)
    ifq, zg = f.zflag(I1, i1fz)
    pk = f.peek_to_nf("( Z' ` %s )" % I1, zg, ifq, I1, i1n, '( %s ` i )' % N1C, n1s)
    body = TRI(C2, D2, n2)
    got = cj(((HT(NI, CNFL), SSS('( %s ` i )' % N1C)), (body, 'A. r e. ( %s ` i ) ( %s ` <. r , ( inl ` ( Z\' ` %s ) ) >. ) e. ( %s ` %s )'
                                                       % (N1C, RDBL, I1, NF, I1))))
    assert got == LBODY, '\nGOT  %s\nWANT %s' % (got, LBODY)
    a1 = s([ht, n1s], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, HT(NI, CNFL), SSS('( %s ` i )' % N1C)))
    a2 = s([t2, pk], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, body, concl(w, ps, pk)))
    w.qed([a1, a2], 'jca', '( %s -> %s )' % (ps, LBODY))
    return w.run()


ST_T = '( %s -> %s )' % (PH, cj(FRAME))


def tmictbt():
    lab = 'tmictbt'
    w = W(lab, 'The frame of Lean\'s ` copyTbl ` slot loop at the machine: the invariant\'s classes and stacks and the '
               'peeked letter over ` 0 ... # L ` , the test ` !flag ` failing at ` # L ` , the first peek of ` blank ` .')
    ps = PH
    f = Fc(w, ps)
    s = w.s
    pt = '( %s /\\ i e. ( 0 ... %s ) )' % (ps, R_)
    g = Fc(w, pt)
    ifz = s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (pt, R_))
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    pi, Si = g.pdb('i', ifz)
    mem = s([pi, Si.memb], 'eqeltrd', "( %s -> ( P' ` i ) e. %s )" % (pt, STK_T))
    ty = s([g.nfss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYP[len('A. i e. ( 0 ... %s ) ' % R_):]))
    typ = s([ty], 'ralrimiva', '( %s -> %s )' % (ps, LTYP))
    k1 = s([s([pi], 'fveq1d', "( %s -> ( ( P' ` i ) ` K ) = ( %s ` K ) )" % (pt, PDB('i'))), Si.vals['K'][1]], 'eqtrd',
           "( %s -> ( ( P' ` i ) ` K ) = %s )" % (pt, Vt('i')))
    z, x, eq, hg, tg = g.zx('i', ifz)
    k2 = s([k1, eq], 'eqtrd', "( %s -> ( ( P' ` i ) ` K ) = ( <\" %s \"> ++ %s ) )" % (pt, HD0(Vt('i')), TL1(Vt('i'))))
    rz = s([s([z], 's1eqd', "( %s -> <\" ( Z' ` i ) \"> = <\" %s \"> )" % (pt, HD0(Vt('i')))), x], 'oveq12d',
           "( %s -> ( <\" ( Z' ` i ) \"> ++ ( X' ` i ) ) = ( <\" %s \"> ++ %s ) )" % (pt, HD0(Vt('i')), TL1(Vt('i'))))
    k3 = s([k2, rz], 'eqtr4d', "( %s -> ( ( P' ` i ) ` K ) = ( <\" ( Z' ` i ) \"> ++ ( X' ` i ) ) )" % pt)
    zg = s([z, hg], 'eqeltrd', "( %s -> ( Z' ` i ) e. Gamma' )" % pt)
    xg = s([x, tg], 'eqeltrd', "( %s -> ( X' ` i ) e. Word Gamma' )" % pt)
    pk = s([k3, zg, xg], '3jca', '( %s -> %s )' % (pt, LPKD[len('A. i e. ( 0 ... %s ) ' % R_):]))
    pkd = s([pk], 'ralrimiva', '( %s -> %s )' % (ps, LPKD))
    NR = '( %s ` %s )' % (NF, R_)
    pm = '( %s /\\ m e. %s )' % (ps, NR)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, R_, Lm(f.rn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NR)))
    f1 = s([mc, s([s([], 'eqidd', '( %s -> %s = %s )' % (pm, R_, R_))], 'iftrued', '( %s -> if ( %s = %s , 1o , (/) ) = 1o )' % (pm, R_, R_))],
           'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    c0 = cnfl_m(w, pm, 'm', mm, '1o', f1)
    exi = s([not1o(w, pm, c0, CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXIT))
    z0 = s([f.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, R_))
    ifq0, zg0 = f.zflag('0', z0)
    pk0 = f.peek_to_nf("( Z' ` 0 )", zg0, ifq0, '0', closed(w, ps, '0nn0', '0 e. NN0'), S, f.ex[SSS(S)])
    a1 = s([typ, pkd], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LTYP, LPKD))
    a2 = s([exi, pk0], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LEXIT, LPK0))
    w.qed([a1, a2], 'jca', ST_T)
    return w.run()


ST_L = '( %s -> %s )' % (PH, LCONCL)


def tmictbl():
    lab = 'tmictbl'
    w = W(lab, 'Lean\'s ` copyTbl ` at the machine with the invariant\'s families as letters: ~ tm2fctb at the handlers '
               '` readBlank ` , ` !flag ` , the pushes of ` blank ` , the body ~ tmictbi , the frame ~ tmictbt , the final '
               '` walkUp src s\' s hold ` by ~ tmiwup .')
    ps = PH
    f = Fc(w, ps)
    c, mk, s = f.c, f.mk, w.s
    ex = dict(f.ex)
    fr = s([], 'tmictbt', ST_T)
    ex.update(parts(w, ps, fr, FRAME))
    ex['%s e. NN0' % R_] = f.rn
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0'])})
    ex['%s e. NN0' % TB] = cl.mem(TB, 'NN0')
    bi = s([], 'tmictbi', '( %s -> %s )' % (PSI, LBODY))
    ex[LPER] = s([bi], 'ralrimiva', '( %s -> %s )' % (ps, LPER))
    # ( P' ` 0 ) = UPD( UPD( D , J , <" 0 "> ++ D`J ) , I , <" 0 "> ++ D`I )
    z0 = s([f.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, R_))
    p0, S0 = f.pdb('0', z0)
    pz = closed(w, ps, 'pfx00', '%s = (/)' % PFX('L', '0'))
    rz = s([s([pz], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ps, REV(PFX('L', '0')))), closed(w, ps, 'rev0', '( reverse ` (/) ) = (/)')], 'eqtrd',
           '( %s -> %s = (/) )' % (ps, REV(PFX('L', '0'))))
    ez = s([s([rz], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(REV(PFX('L', '0'))), ES('(/)'))), closed(w, ps, 'ttses0', A8.ST_ES0)], 'eqtrd',
           '( %s -> %s = (/) )' % (ps, ES(REV(PFX('L', '0')))))
    d0 = s([f.lw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = L )' % (ps, DROP('L', '0')))
    v0 = s([s([d0], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP('L', '0')), ES('L')))], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (ps, Vt('0'), ES('L'), Z0X))
    vk = s([c['( D ` K ) = ( %s ++ %s )' % (ES('L'), Z0X)], v0], 'eqtr4d', '( %s -> ( D ` K ) = %s )' % (ps, Vt('0')))
    rules = {}
    for Q, qw, Tt in ((QJ, f.qj, Jt), (QI, f.qi, It)):
        e1 = s([s([ez], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, Tt('0'), Q)), s([qw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, Q, Q))],
               'eqtrd', '( %s -> %s = %s )' % (ps, Tt('0'), Q))
        rules[Tt('0')] = (Q, e1)
    u1 = upidv(w, ps, 'D', 'K', Vt('0'), vk, mk['tv'], f.dd, mk['k']['K']['kd'])
    rules[UP('D', 'K', Vt('0'))] = ('D', u1)
    r1, x1 = w.rewrite(PDB('0'), rules, ps)
    P0T = UP(UP('D', 'J', CC('<" 0 ">', '( D ` J )')), 'I', CC('<" 0 ">', '( D ` I )'))
    assert x1 == P0T, x1
    ex["( P' ` 0 ) = %s" % P0T] = s([p0, r1], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ps, P0T))
    ex['I =/= J'] = f.ne('I', 'J')
    # the walkUp triple from C( E , ( N ` R ) , ( P' ` R ) )
    rfz = s([f.rn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, R_, R_))
    pr, SR = f.pdb(R_, rfz)
    RL = REV('L')
    rlw = s([f.lw, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ps, RL, WSLOT))
    pl = s([f.lw, w.inst('pfxid')], 'syl', '( %s -> %s = L )' % (ps, PFX('L', R_)))
    er = s([s([pl], 'fveq2d', '( %s -> %s = %s )' % (ps, REV(PFX('L', R_)), RL))], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(REV(PFX('L', R_))), ES(RL)))
    sw = closed(w, ps, 'swrd00', '( L substr <. %s , %s >. ) = (/)' % (R_, R_))
    e0 = s([s([sw], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP('L', R_)), ES('(/)'))), closed(w, ps, 'ttses0', A8.ST_ES0)], 'eqtrd',
           '( %s -> %s = (/) )' % (ps, ES(DROP('L', R_))))
    # the K value of PDB( R ) as ES( (/) ) ++ Z0X
    kv = s([SR.vals['K'][1], s([s([sw], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP('L', R_)), ES('(/)')))], 'oveq1d',
                                '( %s -> %s = ( %s ++ %s ) )' % (ps, Vt(R_), ES('(/)'), Z0X))], 'eqtrd',
           '( %s -> ( %s ` K ) = ( %s ++ %s ) )' % (ps, PDB(R_), ES('(/)'), Z0X))
    iv = s([SR.vals['I'][1], s([er], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (ps, It(R_), ES(RL), QI))], 'eqtrd',
           "( %s -> ( %s ` I ) = ( %s ++ ( <\" 0 \"> ++ ( D ` I ) ) ) )" % (ps, PDB(R_), ES(RL)))
    rn2 = s([f.lw, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran L )' % (ps, RL))
    RSBR = 'A. o e. ran %s %s' % (RL, SB('o'))
    exu = dict(f.ex)
    exu.update({STKD(PDB(R_)): SR.memb, '%s e. %s' % (RL, WSLOT): rlw, '(/) e. %s' % WSLOT: s([], 'wrd0', '(/) e. %s' % WSLOT) if False else
                s([s([], 'wrd0', '(/) e. %s' % WSLOT)], 'a1i', '( %s -> (/) e. %s )' % (ps, WSLOT)),
                "( D ` I ) e. Word Gamma'": f.di, WRD(Z0X, GAM): f.zxw,
                "( %s ` I ) = ( %s ++ ( <\" 0 \"> ++ ( D ` I ) ) )" % (PDB(R_), ES(RL)): iv,
                '( %s ` K ) = ( %s ++ %s )' % (PDB(R_), ES('(/)'), Z0X): kv,
                RSBR: s([rn2, c[RSB], w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ps, RSBR))})
    MU = {'K': 'K', 'J': 'I"', 'I': "I'", "I'": 'I', 'P': PL('P', 7), 'E': 'E', 'D': PDB(R_), 'L': RL, 'U': '(/)',
          'X': '( D ` I )', 'Y': Z0X}
    tu, ccu = inst(w, ps, 'tmiwup', MU, Bld(w, ps, c, exu))
    Cu, Du, nu = triple_parts(ccu)
    assert nu == WUPR, nu
    E7 = PL(PL('P', 7), 0)
    NR = '( %s ` %s )' % (NF, R_)
    tu = hrssc(w, ps, mk['phm'], tu, Cu, Du, nu, CLN(E7, NR, PDB(R_)), clnss(w, ps, E7, NR, S, PDB(R_), f.nfss(R_, f.rn)))
    Cu = CLN(E7, NR, PDB(R_))
    ceq = clneq(w, ps, E7, NR, s([pr], 'eqcomd', "( %s -> %s = ( P' ` %s ) )" % (ps, PDB(R_), R_)), PDB(R_), "( P' ` %s )" % R_)
    # the post: [ K : Vt R , J : Jt R , I : It R , K : X5 , I : ( D ` I ) ]
    X5 = CC(ES('( %s ++ (/) )' % REV(RL)), Z0X)
    rr = s([f.lw, w.inst('revrev')], 'syl', '( %s -> %s = L )' % (ps, REV(RL)))
    c0 = s([s([rr, w.inst('revcl')], 'syl', '') if False else s([f.lw, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ps, RL, WSLOT))], 'id', '') if False else None
    rrw = s([rlw, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ps, REV(RL), WSLOT))
    cz = s([rrw, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ps, REV(RL), REV(RL)))
    x5a = s([cz, rr], 'eqtrd', '( %s -> ( %s ++ (/) ) = L )' % (ps, REV(RL)))
    x5b = s([s([x5a], 'fveq2d', '( %s -> %s = %s )' % (ps, ES('( %s ++ (/) )' % REV(RL)), ES('L')))], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (ps, X5, ES('L'), Z0X))
    x5 = s([x5b, c['( D ` K ) = ( %s ++ %s )' % (ES('L'), Z0X)]], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (ps, X5))
    chain = [('K', Vt(R_)), ('J', Jt(R_)), ('I', It(R_)), ('K', X5), ('I', '( D ` I )')]
    assert Du == CLN('E', S, chain_text('D', chain)), Du
    r5, x5t = w.rewrite(chain_text('D', chain), {X5: ('( D ` K )', x5)}, ps)
    ch2 = [(k, '( D ` K )' if v == X5 else v) for k, v in chain]
    vwr, jwr, iwr, edr, err = f.words(R_, rfz)
    dkw = s([stkfv(w, ps, 'D', 'K', mk['tv'], f.dd, mk['k']['K']['kd']), mk['k']['K']['wge']], 'eleqtrd', "( %s -> ( D ` K ) e. Word Gamma' )" % ps)
    gam = {Vt(R_): vwr, Jt(R_): jwr, It(R_): iwr, '( D ` K )': dkw, '( D ` I )': f.di}
    nst, out = stk_normalize(w, ps, mk, 'D', f.dd, f.ne, ch2, gam, K5)
    assert out == [('J', Jt(R_))], out
    jr = s([er], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (ps, Jt(R_), ES(RL), QJ))
    r6, x6 = w.rewrite(chain_text('D', out), {Jt(R_): (CC(ES(RL), QJ), jr)}, ps)
    assert x6 == DFIN_CTB, x6
    fe = s([s([r5, nst], 'eqtrd', '( %s -> %s = %s )' % (ps, chain_text('D', chain), chain_text('D', out))), r6], 'eqtrd',
           '( %s -> %s = %s )' % (ps, chain_text('D', chain), DFIN_CTB))
    tu, Cu, Du, nu = hrrw(w, ps, tu, Cu, Du, nu, ceq=ceq, deq=clneq(w, ps, 'E', S, fe, chain_text('D', chain), DFIN_CTB))
    ex[TRI(Cu, Du, nu)] = tu
    LRL = '( # ` %s )' % RL
    cl.leaf(LRL, 'NN0', s([rlw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LRL)))
    ex['%s e. NN0' % WUPR] = cl.mem(WUPR, 'NN0')
    st = Bld(w, ps, f.c, ex)(LTREE)
    w.qed([st, w.inst('tm2fctb')], 'syl', ST_L)
    return w.run()


def tmictb():
    lab = 'tmictb'
    ps = cj(TREE_CTB)
    w = W(lab, 'Lean\'s ` copyTbl_runs ` at the machine: wherever ` copyTbl src dst hold s s\' ` is installed, the slots '
               '` L ` on ` src ` (down to the ` blank ` marker) are copied onto ` dst ` in reverse order above a fresh '
               '` blank ` , ` src ` and every other stack restored, within ` copyC ( # L ) N b ` steps (~ tmictbl at the '
               'families of ` SlotsInv ` , ~ ttcopycx ).')
    c = Ctx(w, ps, TREE_CTB)
    s = w.s
    eqs = {'%s = %s' % (F_, F_): closed(w, ps, 'eqid', '%s = %s' % (F_, F_)) for F_ in (PDF, ZDF, XDF)}
    t, cc = inst(w, ps, 'tmictbl', {"P'": PDF, "Z'": ZDF, "X'": XDF}, Bld(w, ps, c, eqs))
    Ca, Da, na = triple_parts(cc)
    lw = c['L e. %s' % WSLOT]
    rl = s([lw, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ps, REV('L'), R_))
    n1eq, n1t = w.rewrite(na, {'( # ` %s )' % REV('L'): (R_, rl)}, ps)
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0'])})
    rn = s([lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, R_))
    cl.leaf(R_, 'NN0', rn)
    CN = '( N x. ( ( 6 x. B ) + ; 1 7 ) )'
    j3 = s([rn, cl.mem(CN, 'NN0'), cl.mem(SLOTC, 'NN0')], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ps, R_, CN, SLOTC))
    le = s([j3, w.inst('ttcopycx')], 'syl', '( %s -> %s <_ %s )' % (ps, n1t, COPYC(R_)))
    t2, C2, D2, n2 = hrrw(w, ps, t, Ca, Da, na, neq=n1eq)
    phm = s([c[PHM]], 'id', '') if False else None
    ctx_phm = Ctx(w, ps, TREE_CTB)
    from t7_e_cmp import machine as _m
    mk = _m(w, ps, ctx_phm, K5)
    hrle(w, ps, mk['phm'], t2, C2, D2, n2, COPYC(R_), cl.mem(COPYC(R_), 'NN0'), le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
