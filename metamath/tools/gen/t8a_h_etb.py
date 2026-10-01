"""T8a: emptyTbl at the machine (Lean ` emptyTbl_runs ` , ` emptyTbl_le_B ` ) on its installation predicate TMIetb.

  tmietbi   one iteration after the pushed ket: ` predNum c s ; isZero c s ` (~ tmiprds , ~ tmiizs )
  tmietbt   the frame: typings over ( 0 ... L ), the exit test, the prologue ` isZero c s ` and the
            epilogue ` dropNum c `
  tmietbl   ~ tm2fetb assembled, the stack family a letter P'
  tmietb    emptyTbl_runs (bound in ` bl L ` )
  tmietbb   emptyTbl_le_B

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_h_etb.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
from lin import linarith, lineq, nlinarith
from t7lib import famval, fam_unpack, fam_pack, mval
from t8a_e_slot import stkcl
from t8a_f_wup import find, cnfl_m

SEL = sys.argv[1:]
BLL = '( bl ` L )'
DJ = '( D ` J )'
Z0J = '( <" 0 "> ++ %s )' % DJ
X4 = '( <" 4 "> ++ X )'
ENC = lambda t: '( encodeNat ` %s )' % t


def Kt(t):
    return EW('( L - %s )' % t, 'X')


def Jt(t):
    return CC('( 3 repeatS %s )' % t, Z0J)


def PDB(t):
    return UP(UP('D', 'K', Kt(t)), 'J', Jt(t))


PDF = '( j e. NN0 |-> %s )' % PDB('j')
NCD = lambda h, t: '( TMfl ` %s ) = if ( ( L - %s ) = 0 , 1o , (/) )' % (h, t)
NF = '( j e. NN0 |-> { h e. TMSt | %s } )' % NCD('h', 'j')
UB = '( ( 2 x. %s ) + 5 )' % BLL
TE = '( ( ( 2 x. %s ) + 3 ) + ( ( 2 x. %s ) + 5 ) )' % (BLL, BLL)
FAMEQ = "P' = %s" % PDF
T_L = (TREE_ETB, FAMEQ)
PH = cj(T_L)
PSI = '( %s /\\ i e. ( 0 ..^ L ) )' % PH

GM = dict(FRAGS['etb'].lmap())
GM.update({'K': 'J', 'Y': BLANK, "Y'": KET, 'C0': CNFL, 'R': 'L', "T'": TE, 'O': S, 'N': NF, 'P': "P'", 'U': UB, "U'": '1',
           "D'": DFIN_ETB, "N'": S})
_LA, _LC = split_imp(stmt('tm2fetb'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LPER = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ..^ '))[0]
LBODY = LPER[len('A. i e. ( 0 ..^ L ) '):]
LTYP = find(LTREE, lambda t: t.startswith('A. i e. ( 0 ... L ) '))[0]
LEXIT = 'A. m e. ( %s ` L ) -. ( %s ` m ) = 1o' % (NF, CNFL)
P1_, A_, Bp_, E0_ = GM['P1'], GM['A'], GM["B'"], GM['E']
LPRO = TRI(CLN(P1_, S, UP('D', 'J', Z0J)), CLN(A_, '( %s ` 0 )' % NF, "( P' ` 0 )"), UB)
LEPI = TRI(CLN(E0_, '( %s ` L )' % NF, "( P' ` L )"), CLN('E', S, DFIN_ETB), '1')
for _t in (LEXIT, LPRO, LEPI):
    assert find(LTREE, lambda t, _t=_t: t == _t), _t
FRAME = ((LTYP, LEXIT), (LPRO, LEPI))
K3_ = ['K', 'J', 'I']


class Ec:
    """facts under ph (the emptyTbl antecedent with the family equation, possibly extended)"""
    def __init__(self, w, ph, tree=None, root=None, pl="P'"):
        self.w, self.ph, self.pl = w, ph, pl
        tree = tree or T_L
        if root is None and ph != cj(tree):
            root = w.s([], 'simpl', '( %s -> %s )' % (ph, cj(tree)))
        self.c = c = Ctx(w, ph, tree, root=root)
        mk = self.mk = machine(w, ph, c, K3_)
        ne = self.ne = ne_fn(w, ph, c, set(flat(dist_tree(K3_))))
        base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        base.update(unfold_all(w, ph, c[FRAGS['etb'].pred()], 'etb', K3_, 'P', 'E', rec=False))
        fr = FRAGS['etb']; lm = fr.lmap()
        for j, (fn, cks, en, exn) in enumerate(fr.children):
            P_ = PL('P', fr.slot(j))
            pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
            base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
        for s_ in K3_:
            base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K3_):
            for b in K3_[i_ + 1:]:
                base['%s =/= %s' % (a, b)] = ne(a, b)
                base['%s =/= %s' % (b, a)] = ne(b, a)
        ex = self.ex = dict(base)
        ex.update(H.handler_extra(w, ph, mk, H.IFACE))
        ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
        self.ln, self.xw, self.dd = c['L e. NN0'], c[WRD('X', GAM)], c[STKD('D')]
        dk = mk['k']['J']
        self.djw = w.s([stkfv(w, ph, 'D', 'J', mk['tv'], self.dd, dk['kd']), dk['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, DJ))
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        self.s0 = w.s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        self.z0j = w.s([self.s0, self.djw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Z0J))
        self.g3 = closed(w, ph, 'gamma3', "3 e. Gamma'")
        self.bl = w.s([self.ln, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, BLL))
        self.memo = {}

    def lt(self, t, tn, tle):
        """( L - t ) e. NN0"""
        return self.w.s([tn, self.ln, tle, self.w.inst('nn0sub2')], 'syl3anc', '( %s -> ( L - %s ) e. NN0 )' % (self.ph, t))

    def words(self, t, tn, tle):
        key = ('w', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        lt = self.lt(t, tn, tle)
        kw = ewg(w, ph, '( L - %s )' % t, lt, 'X', self.xw)
        rw = w.s([self.g3, tn, w.inst('repsw')], 'syl2anc', "( %s -> ( 3 repeatS %s ) e. Word Gamma' )" % (ph, t))
        jw = w.s([rw, self.z0j, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Jt(t)))
        self.memo[key] = (kw, jw, rw, lt)
        return self.memo[key]

    def stacks(self, t, tn, tle):
        w, ph = self.w, self.ph
        kw, jw, rw, lt = self.words(t, tn, tle)
        vals = {s_: selfval(w, ph, self.mk, 'D', self.dd, s_) for s_ in K3_}
        S0 = Stacks(w, ph, self.mk, 'D', self.dd, self.ne, vals)
        return S0, S0.upd('K', Kt(t), kw).upd('J', Jt(t), jw)

    def pdb(self, t, tn, tle):
        w, ph = self.w, self.ph
        S0, St = self.stacks(t, tn, tle)
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

    def enclen(self, t, tn, tle, cl):
        """( ph -> ( # ` ( encodeNat ` ( L - t ) ) ) <_ ( bl ` L ) )"""
        w, ph = self.w, self.ph
        lt = self.lt(t, tn, tle)
        E = ENC('( L - %s )' % t)
        e1 = w.s([lt, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = ( bl ` ( L - %s ) ) )' % (ph, E, t))
        p = w.s([closed(w, ph, '2nn0', '2 e. NN0'), self.bl, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, BLL))
        cl.leaf('( 2 ^ %s )' % BLL, 'NN0', p)
        lb = w.s([self.ln, w.inst('blpow2')], 'syl', '( %s -> L < ( 2 ^ %s ) )' % (ph, BLL))
        tlt = linarith(w, ph, [lb, cl.ge0(t)], '( L - %s ) < ( 2 ^ %s )' % (t, BLL), closure=cl)
        b = w.s([lt, self.bl, tlt, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` ( L - %s ) ) <_ %s )' % (ph, t, BLL))
        return w.s([e1, b], 'eqbrtrd', '( %s -> ( # ` %s ) <_ %s )' % (ph, E, BLL))


def enc_ib(w, ps, t, tn, X):
    gv = w.s([tn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (ps, t, ENC(t)))
    return w.s([gv], 'oveq1d', '( %s -> %s = %s )' % (ps, EW(t, X), CC('( inclBool o. %s )' % ENC(t), YX(X))))


def tmietbi():
    lab = 'tmietbi'
    w = W(lab, 'One iteration of Lean\'s ` emptyTbl ` loop at the machine ( ` emptyBody_runs ` after its ` pushSym tbl ket ` ): '
               'the test ` !flag ` holds while the counter is not zero, and ` predNum c s ; isZero c s ` counts down '
               '(~ tmiprds , ~ tmiizs , ~ tmcpredenc ).')
    ps = PSI
    f = Ec(w, ps)
    c, mk = f.c, f.mk
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ L ) )' % ps)
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < L )' % ps)
    ir = w.s([inn], 'nn0red', '( %s -> i e. RR )' % ps)
    lr = w.s([f.ln], 'nn0red', '( %s -> L e. RR )' % ps)
    ile = w.s([ir, lr, ilt], 'ltled', '( %s -> i <_ L )' % ps)
    I1 = '( i + 1 )'
    i1fz = w.s([ii, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... L ) )' % (ps, I1))
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    i1le = w.s([i1fz, w.inst('elfzle2')], 'syl', '( %s -> %s <_ L )' % (ps, I1))
    iz, lz = w.s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ps), w.s([f.ln], 'nn0zd', '( %s -> L e. ZZ )' % ps)
    lin_ = w.s([ilt, w.s([iz, lz, w.inst('znnsub')], 'syl2anc', '( %s -> ( i < L <-> ( L - i ) e. NN ) )' % ps)], 'mpbid', '( %s -> ( L - i ) e. NN )' % ps)
    ln0 = w.s([w.s([lin_], 'nnne0d', '( %s -> ( L - i ) =/= 0 )' % ps)], 'neneqd', '( %s -> -. ( L - i ) = 0 )' % ps)
    NI = '( %s ` i )' % NF
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl0 = w.s([mc, w.s([Lm(ln0)], 'iffalsed', '( %s -> if ( ( L - i ) = 0 , 1o , (/) ) = (/) )' % pm)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ht = w.s([cnfl_m(w, pm, 'm', mm, '(/)', fl0)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNFL))
    # the stacks after the pushed ket
    pi, S0, Si = f.pdb('i', inn, ile)
    kw, jw, rw, lti = f.words('i', inn, ile)
    K3J = CC('<" 3 ">', Jt('i'))
    s3 = w.s([f.g3], 's1cld', "( %s -> <\" 3 \"> e. Word Gamma' )" % ps)
    k3j = w.s([s3, jw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, K3J))
    Sp = Si.upd('J', K3J, k3j)
    run = Run(w, ps, mk, Sp, f.ex, c)
    E = ENC('( L - i )')
    ew = w.s([lti, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, E))
    kv = w.s([Sp.vals['K'][1], enc_ib(w, ps, '( L - i )', lti, 'X')], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, Sp.D, CC('( inclBool o. %s )' % E, X4)))
    PBW = '( predBits ` %s )' % E
    pbw = w.s([ew, w.inst('predbitscl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, PBW))
    PBV = CC('( inclBool o. %s )' % PBW, X4)
    pbv = w.s([wib(w, ps, PBW, pbw), wg4(w, ps, 'X', f.xw), w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ps, PBV))
    nss = f.nfss('i', inn)
    run.call('tmiprds', {'K': 'K', 'J': 'I', 'P': PL('P', 4), 'E': PL(PL('P', 5), 0), 'L': E, 'X': 'X'},
             {'( %s ` K ) = %s' % (Sp.D, CC('( inclBool o. %s )' % E, X4)): kv, '%s e. Word 2o' % E: ew},
             [('K', PBV, pbv)], pre=(NI, nss))
    S2 = run.S
    # predBits ( encodeNat ( L - i ) ) = encodeNat ( L - ( i + 1 ) )
    cl = Closure(w, ps, {'L': ('NN0', f.ln), 'i': ('NN0', inn)})
    pe = w.s([lin_, w.inst('tmcpredenc')], 'syl', '( %s -> %s = %s )' % (ps, PBW, ENC('( ( L - i ) - 1 )')))
    le1 = lineq(w, ps, '( ( L - i ) - 1 )', '( L - %s )' % I1, closure=cl)
    pe2 = w.s([pe, w.s([le1], 'fveq2d', '( %s -> %s = %s )' % (ps, ENC('( ( L - i ) - 1 )'), ENC('( L - %s )' % I1)))], 'eqtrd',
              '( %s -> %s = %s )' % (ps, PBW, ENC('( L - %s )' % I1)))
    lt1 = f.lt(I1, i1n, i1le)
    tn = w.s([w.s([pe2], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ps, PBW, ENC('( L - %s )' % I1))),
              w.s([lt1, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = ( L - %s ) )' % (ps, ENC('( L - %s )' % I1), I1))], 'eqtrd',
             '( %s -> ( toNat ` %s ) = ( L - %s ) )' % (ps, PBW, I1))
    OLD = '{ h e. TMSt | ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) }' % PBW
    ce = w.s([w.s([w.s([tn], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( L - %s ) = 0 ) )' % (ps, PBW, I1))], 'ifbid',
                  '( %s -> if ( ( toNat ` %s ) = 0 , 1o , (/) ) = if ( ( L - %s ) = 0 , 1o , (/) ) )' % (ps, PBW, I1))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, PBW, NCD('h', I1)))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, PBW, NCD('h', I1)))],
             'rabbidva', '( %s -> %s = { h e. TMSt | %s } )' % (ps, OLD, NCD('h', I1)))
    fv1 = famval(w, ps, NCD, I1, i1n)
    rb2 = w.s([rb, w.s([fv1], 'eqcomd', '( %s -> { h e. TMSt | %s } = ( %s ` %s ) )' % (ps, NCD('h', I1), NF, I1))], 'eqtrd',
              '( %s -> %s = ( %s ` %s ) )' % (ps, OLD, NF, I1))
    run.call('tmiizs', {'K': 'K', 'I': 'I', 'P': PL('P', 5), 'E': PL('P', 1), 'L': PBW, 'X': 'X'},
             {'( %s ` K ) = %s' % (S2.D, PBV): S2.vals['K'][1], '%s e. Word 2o' % PBW: pbw}, [], cls_rw=(rb2, '( %s ` %s )' % (NF, I1)))
    full = [('K', Kt('i')), ('J', Jt('i')), ('J', K3J)] + run.chain
    assert chain_text('D', full) == run.S.D, (chain_text('D', full), run.S.D)
    gam = dict(run.gam)
    gam.update({Kt('i'): kw, Jt('i'): jw, K3J: k3j, PBV: pbv})
    nst, out = stk_normalize(w, ps, mk, 'D', f.dd, f.ne, full, gam, K3_)
    assert out == [('K', PBV), ('J', K3J)], out
    # PBV = Kt( i + 1 ) , K3J = Jt( i + 1 )
    ib1 = enc_ib(w, ps, '( L - %s )' % I1, lt1, 'X')
    kk = w.s([w.s([w.s([pe2], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. %s ) )' % (ps, PBW, ENC('( L - %s )' % I1)))], 'oveq1d',
                  '( %s -> %s = %s )' % (ps, PBV, CC('( inclBool o. %s )' % ENC('( L - %s )' % I1), X4))), ib1], 'eqtr4d', '( %s -> %s = %s )' % (ps, PBV, Kt(I1)))
    zc = w.s([f.g3], 'elexd', '( %s -> 3 e. _V )' % ps)
    rs1 = w.s([zc, w.inst('repsw1')], 'syl', '( %s -> ( 3 repeatS 1 ) = <" 3 "> )' % ps)
    rcc = w.s([zc, closed(w, ps, '1nn0', '1 e. NN0'), inn, w.inst('repswccat')], 'syl3anc',
              '( %s -> ( ( 3 repeatS 1 ) ++ ( 3 repeatS i ) ) = ( 3 repeatS ( 1 + i ) ) )' % ps)
    ac = w.s([closed(w, ps, 'ax-1cn', '1 e. CC'), w.s([inn], 'nn0cnd', '( %s -> i e. CC )' % ps), w.inst('addcom')], 'syl2anc', '( %s -> ( 1 + i ) = ( i + 1 ) )' % ps)
    rcc2 = w.s([w.s([w.s([rs1], 'oveq1d', '( %s -> ( ( 3 repeatS 1 ) ++ ( 3 repeatS i ) ) = ( <" 3 "> ++ ( 3 repeatS i ) ) )' % ps), rcc], 'eqtr3d',
                    '( %s -> ( <" 3 "> ++ ( 3 repeatS i ) ) = ( 3 repeatS ( 1 + i ) ) )' % ps),
                w.s([ac], 'oveq2d', '( %s -> ( 3 repeatS ( 1 + i ) ) = ( 3 repeatS ( i + 1 ) ) )' % ps)], 'eqtrd',
               '( %s -> ( <" 3 "> ++ ( 3 repeatS i ) ) = ( 3 repeatS ( i + 1 ) ) )' % ps)
    cas = w.s([s3, rw, f.z0j, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 3 "> ++ ( 3 repeatS i ) ) ++ %s ) = %s )' % (ps, Z0J, K3J))
    jj = w.s([cas, w.s([rcc2], 'oveq1d', '( %s -> ( ( <" 3 "> ++ ( 3 repeatS i ) ) ++ %s ) = %s )' % (ps, Z0J, Jt(I1)))], 'eqtr3d',
             '( %s -> %s = %s )' % (ps, K3J, Jt(I1)))
    r2, x2 = w.rewrite(chain_text('D', out), {PBV: (Kt(I1), kk), K3J: (Jt(I1), jj)}, ps)
    assert x2 == PDB(I1), x2
    p1, _, _ = f.pdb(I1, i1n, i1le)
    fin_ = w.s([w.s([nst, r2], 'eqtrd', '( %s -> %s = %s )' % (ps, run.S.D, PDB(I1))), p1], 'eqtr4d', "( %s -> %s = ( P' ` %s ) )" % (ps, run.S.D, I1))
    head = run.cur[:-len(' X. { %s } ) )' % run.S.D)]
    ncls = head.split(' } X. ( ', 1)[1]
    deq = clneq(w, ps, A_, ncls, fin_, run.S.D, "( P' ` %s )" % I1)
    # the pre stacks : UPD( ( P' ` i ) , J , ( <" 3 "> ++ ( ( P' ` i ) ` J ) ) )
    GEN = UP("( P' ` i )", 'J', CC('<" 3 ">', "( ( P' ` i ) ` J )"))
    q1, y1 = w.rewrite(GEN, {"( P' ` i )": (PDB('i'), pi)}, ps)
    q2, y2 = w.rewrite(y1, {'( %s ` J )' % PDB('i'): (Jt('i'), Si.vals['J'][1])}, ps)
    assert y2 == Sp.D, y2
    pre = w.s([w.s([q1, q2], 'eqtrd', '( %s -> %s = %s )' % (ps, GEN, Sp.D))], 'eqcomd', '( %s -> %s = %s )' % (ps, Sp.D, GEN))
    ceq = clneq(w, ps, Bp_, NI, pre, Sp.D, GEN)
    t2, C2, D2, n2 = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, ceq=ceq, deq=deq)
    for e_, st_ in [('( # ` %s )' % E, w.s([ew, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, E))),
                    ('( # ` %s )' % PBW, w.s([pbw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, PBW))),
                    (BLL, f.bl)]:
        cl.leaf(e_, 'NN0', st_)
    el = f.enclen('i', inn, ile, cl)
    pbl = w.s([ew, w.inst('predbitslen')], 'syl', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (ps, PBW, E))
    le = linarith(w, ps, [el, pbl], '%s <_ %s' % (n2, TE), closure=cl)
    t3 = hrle(w, ps, mk['phm'], t2, C2, D2, n2, TE, cl.mem(TE, 'NN0'), le)
    got = '( %s /\\ %s )' % (HT(NI, CNFL), TRI(C2, D2, TE))
    assert got == LBODY, '\nGOT  %s\nWANT %s' % (got, LBODY)
    w.qed([ht, t3], 'jca', '( %s -> %s )' % (ps, LBODY))
    return w.run()


ST_T = '( %s -> %s )' % (PH, cj(FRAME))


def tmietbt():
    lab = 'tmietbt'
    w = W(lab, 'The frame of Lean\'s ` emptyTbl ` loop at the machine: the invariant\'s classes and stacks over '
               '` 0 ... L ` , the test ` !flag ` failing at ` L ` , the prologue ` isZero c s ` (~ tmiizs ) after the '
               '` blank ` marker, and the epilogue ` dropNum c ` (~ tmidrop ) with ~ ttetb0 .')
    ps = PH
    f = Ec(w, ps)
    c, mk = f.c, f.mk
    pt = '( %s /\\ i e. ( 0 ... L ) )' % ps
    g = Ec(w, pt)
    ifz = w.s([], 'simpr', '( %s -> i e. ( 0 ... L ) )' % pt)
    inn = w.s([ifz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = w.s([ifz, w.inst('elfzle2')], 'syl', '( %s -> i <_ L )' % pt)
    pi, S0i, Si = g.pdb('i', inn, ile)
    mem = w.s([pi, Si.memb], 'eqeltrd', "( %s -> ( P' ` i ) e. %s )" % (pt, STK_T))
    ty = w.s([g.nfss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYP[len('A. i e. ( 0 ... L ) '):]))
    typ = w.s([ty], 'ralrimiva', '( %s -> %s )' % (ps, LTYP))
    NFL_ = '( %s ` L )' % NF
    pm = '( %s /\\ m e. %s )' % (ps, NFL_)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCD, 'L', Lm(f.ln), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NFL_)))
    lcn = w.s([f.ln], 'nn0cnd', '( %s -> L e. CC )' % ps)
    ll0 = w.s([lcn], 'subidd', '( %s -> ( L - L ) = 0 )' % ps)
    f1 = w.s([mc, w.s([Lm(ll0)], 'iftrued', '( %s -> if ( ( L - L ) = 0 , 1o , (/) ) = 1o )' % pm)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    exi = w.s([not1o(w, pm, cnfl_m(w, pm, 'm', mm, '1o', f1), CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXIT))
    # the prologue
    tv, dd = mk['tv'], f.dd
    kK, kJ = mk['k']['K'], mk['k']['J']
    togk = lambda X, k, g_: w.s([g_, mk['k'][k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(k)))
    D1 = UP('D', 'J', Z0J)
    d1 = updcl(w, ps, 'D', 'J', Z0J, tv, dd, kJ['kd'], togk(Z0J, 'J', f.z0j))
    dk = c['( D ` K ) = %s' % EW('L', 'X')]
    dkb = w.s([dk, enc_ib(w, ps, 'L', f.ln, 'X')], 'eqtrd', '( %s -> ( D ` K ) = %s )' % (ps, CC('( inclBool o. %s )' % ENC('L'), X4)))
    d1k = w.s([updnv(w, ps, 'D', 'J', Z0J, 'K', tv, dd, kJ['kd'], w.s([f.z0j], 'elexd', '( %s -> %s e. _V )' % (ps, Z0J)), kK['kd'], f.ne('K', 'J')), dkb],
              'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, D1, CC('( inclBool o. %s )' % ENC('L'), X4)))
    ew = w.s([f.ln, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENC('L')))
    ex = dict(f.ex)
    ex.update({STKD(D1): d1, '( %s ` K ) = %s' % (D1, CC('( inclBool o. %s )' % ENC('L'), X4)): d1k, '%s e. Word 2o' % ENC('L'): ew})
    t, cc = inst(w, ps, 'tmiizs', {'K': 'K', 'I': 'I', 'P': PL('P', 3), 'E': PL('P', 1), 'L': ENC('L'), 'X': 'X', 'D': D1}, Bld(w, ps, c, ex))
    Ca, Da, na = triple_parts(cc)
    OLD = '{ h e. TMSt | ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) }' % ENC('L')
    tl = w.s([f.ln, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = L )' % (ps, ENC('L')))
    l0 = w.s([lcn], 'subid1d', '( %s -> ( L - 0 ) = L )' % ps)
    tl0 = w.s([tl, l0], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( L - 0 ) )' % (ps, ENC('L')))
    ce = w.s([w.s([w.s([tl0], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( L - 0 ) = 0 ) )' % (ps, ENC('L')))], 'ifbid',
                  '( %s -> if ( ( toNat ` %s ) = 0 , 1o , (/) ) = if ( ( L - 0 ) = 0 , 1o , (/) ) )' % (ps, ENC('L')))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, ENC('L'), NCD('h', '0')))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, ENC('L'), NCD('h', '0')))],
             'rabbidva', '( %s -> %s = { h e. TMSt | %s } )' % (ps, OLD, NCD('h', '0')))
    z0 = closed(w, ps, '0nn0', '0 e. NN0')
    fv0 = famval(w, ps, NCD, '0', z0)
    rb2 = w.s([rb, w.s([fv0], 'eqcomd', '( %s -> { h e. TMSt | %s } = ( %s ` 0 ) )' % (ps, NCD('h', '0'), NF))], 'eqtrd', '( %s -> %s = ( %s ` 0 ) )' % (ps, OLD, NF))
    cn = clnneq(w, ps, A_, rb2, OLD, '( %s ` 0 )' % NF, D1)
    z0le = w.s([f.ln], 'nn0ge0d', '( %s -> 0 <_ L )' % ps)
    p0, _, _ = f.pdb('0', z0, z0le)
    k0 = w.s([w.s([w.s([l0], 'fveq2d', '( %s -> ( encNatGam ` ( L - 0 ) ) = ( encNatGam ` L ) )' % ps)], 'oveq1d',
                  '( %s -> %s = %s )' % (ps, Kt('0'), EW('L', 'X')))], 'id', '') if False else \
        w.s([w.s([l0], 'fveq2d', '( %s -> ( encNatGam ` ( L - 0 ) ) = ( encNatGam ` L ) )' % ps)], 'oveq1d', '( %s -> %s = %s )' % (ps, Kt('0'), EW('L', 'X')))
    a0 = w.s([dk, k0], 'eqtr4d', '( %s -> ( D ` K ) = %s )' % (ps, Kt('0')))
    r0 = w.s([w.s([f.g3], 'elexd', '( %s -> 3 e. _V )' % ps), w.inst('repsw0')], 'syl', '( %s -> ( 3 repeatS 0 ) = (/) )' % ps)
    j0 = w.s([w.s([r0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, Jt('0'), Z0J)), w.s([f.z0j, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, Z0J, Z0J))],
             'eqtrd', '( %s -> %s = %s )' % (ps, Jt('0'), Z0J))
    u1 = upidv(w, ps, 'D', 'K', Kt('0'), a0, tv, dd, kK['kd'])
    r1, x1 = w.rewrite(PDB('0'), {UP('D', 'K', Kt('0')): ('D', u1), Jt('0'): (Z0J, j0)}, ps)
    assert x1 == D1, x1
    pe = w.s([w.s([p0, r1], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ps, D1))], 'eqcomd', "( %s -> %s = ( P' ` 0 ) )" % (ps, D1))
    cs = clneq(w, ps, A_, '( %s ` 0 )' % NF, pe, D1, "( P' ` 0 )")
    deq = w.s([cn, cs], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, CLN(A_, '( %s ` 0 )' % NF, "( P' ` 0 )")))
    ln_ = w.s([f.ln, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ps, ENC('L'), BLL))
    neq, n1_ = w.rewrite(na, {'( # ` %s )' % ENC('L'): (BLL, ln_)}, ps)
    assert n1_ == UB, n1_
    pro, _, _, _ = hrrw(w, ps, t, Ca, Da, na, deq=deq, neq=neq)
    # the epilogue
    lfz = w.s([f.ln, w.inst('nn0fz0')], 'sylib', '( %s -> L e. ( 0 ... L ) )' % ps)
    lle = w.s([w.s([f.ln], 'nn0red', '( %s -> L e. RR )' % ps)], 'leidd', '( %s -> L <_ L )' % ps)
    pL, S0L, SL = f.pdb('L', f.ln, lle)
    kwL, jwL, rwL, ltL = f.words('L', f.ln, lle)
    sw1 = upc(w, ps, 'D', 'K', Kt('L'), 'J', Jt('L'), tv, dd, f.ne('K', 'J'), kK['kd'], togk(Kt('L'), 'K', kwL), kJ['kd'], togk(Jt('L'), 'J', jwL))
    D0 = UP('D', 'J', Jt('L'))
    d0s = updcl(w, ps, 'D', 'J', Jt('L'), tv, dd, kJ['kd'], togk(Jt('L'), 'J', jwL))
    WL = '( encNatGam ` ( L - L ) )'
    wlb = w.s([ltL, w.s([w.s([], 'tm2lbitf', 'encNatGam : NN0 --> Word ( { 1 } X. 2o )')], 'ffvelcdmi',
                        '( ( L - L ) e. NN0 -> %s e. Word ( { 1 } X. 2o ) )' % WL)], 'syl', '( %s -> %s e. Word ( { 1 } X. 2o ) )' % (ps, WL))
    ex2 = dict(f.ex)
    ex2.update({STKD(D0): d0s, '%s e. Word ( { 1 } X. 2o )' % WL: wlb})
    t, cc = inst(w, ps, 'tmidrop', {'K': 'K', 'P': PL('P', 6), 'E': 'E', 'W': WL, 'X': 'X', 'D': D0}, Bld(w, ps, c, ex2))
    Ca, Da, na = triple_parts(cc)
    assert Ca == CLN(E0_, S, UP(D0, 'K', Kt('L'))), Ca
    tE = hrssc(w, ps, mk['phm'], t, Ca, Da, na, CLN(E0_, NFL_, UP(D0, 'K', Kt('L'))), clnss(w, ps, E0_, NFL_, S, UP(D0, 'K', Kt('L')), f.nfss('L', f.ln)))
    pe2 = w.s([w.s([pL, sw1], 'eqtrd', "( %s -> ( P' ` L ) = %s )" % (ps, UP(D0, 'K', Kt('L'))))], 'eqcomd', "( %s -> %s = ( P' ` L ) )" % (ps, UP(D0, 'K', Kt('L'))))
    ceq = clneq(w, ps, E0_, NFL_, pe2, UP(D0, 'K', Kt('L')), "( P' ` L )")
    sw2 = upc(w, ps, 'D', 'J', Jt('L'), 'K', 'X', tv, dd, f.ne('J', 'K'), kJ['kd'], togk(Jt('L'), 'J', jwL), kK['kd'], togk('X', 'K', f.xw))
    tb = w.s([w.s([f.ln, w.inst('ttetb0')], 'syl', '( %s -> ( L encTblAsc EmptyTbl ) = ( 3 repeatS L ) )' % ps)], 'eqcomd',
             '( %s -> ( 3 repeatS L ) = ( L encTblAsc EmptyTbl ) )' % ps)
    r3, x3 = w.rewrite(UP(UP('D', 'K', 'X'), 'J', Jt('L')), {'( 3 repeatS L )': ('( L encTblAsc EmptyTbl )', tb)}, ps)
    assert x3 == DFIN_ETB, x3
    fe = w.s([sw2, r3], 'eqtrd', '( %s -> %s = %s )' % (ps, UP(D0, 'K', 'X'), DFIN_ETB))
    deq2 = clneq(w, ps, 'E', S, fe, UP(D0, 'K', 'X'), DFIN_ETB)
    e0 = w.s([closed(w, ps, '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ps)
    e0b = w.s([closed(w, ps, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ps)
    eg0 = w.s([w.s([e0, e0b], 'eqtrd', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. (/) ) )' % ps), closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd',
              '( %s -> ( encNatGam ` 0 ) = (/) )' % ps)
    wl0 = w.s([w.s([ll0], 'fveq2d', '( %s -> %s = ( encNatGam ` 0 ) )' % (ps, WL)), eg0], 'eqtrd', '( %s -> %s = (/) )' % (ps, WL))
    h0 = w.s([w.s([wl0], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (ps, WL)), closed(w, ps, 'hash0', '( # ` (/) ) = 0')], 'eqtrd',
             '( %s -> ( # ` %s ) = 0 )' % (ps, WL))
    n1 = w.s([w.s([h0], 'oveq1d', '( %s -> ( ( # ` %s ) + 1 ) = ( 0 + 1 ) )' % (ps, WL)), closed(w, ps, '0p1e1', '( 0 + 1 ) = 1')], 'eqtrd',
             '( %s -> ( ( # ` %s ) + 1 ) = 1 )' % (ps, WL))
    epi, _, _, _ = hrrw(w, ps, tE, CLN(E0_, NFL_, UP(D0, 'K', Kt('L'))), Da, na, ceq=ceq, deq=deq2, neq=n1)
    a1 = w.s([typ, exi], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LTYP, LEXIT))
    a2 = w.s([pro, epi], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LPRO, LEPI))
    w.qed([a1, a2], 'jca', ST_T)
    return w.run()


ST_L = '( %s -> %s )' % (PH, LCONCL)


def tmietbl():
    lab = 'tmietbl'
    w = W(lab, 'Lean\'s ` emptyTbl ` at the machine with the invariant\'s stack family a letter: ~ tm2fetb at the '
               'test ` !flag ` , the marker ` blank = 0 ` , the pushed ` ket = 3 ` , the body ~ tmietbi , the frame ~ tmietbt .')
    ps = PH
    f = Ec(w, ps)
    c, mk = f.c, f.mk
    ex = dict(f.ex)
    fr = w.s([], 'tmietbt', ST_T)
    ex.update(parts(w, ps, fr, FRAME))
    cl = Closure(w, ps, {'L': ('NN0', f.ln)})
    cl.leaf(BLL, 'NN0', f.bl)
    for e_ in (TE, UB, '1'):
        ex['%s e. NN0' % e_] = cl.mem(e_, 'NN0')
    for n_ in ('0', '3'):
        ex["%s e. %s" % (n_, GX('J'))] = w.s([closed(w, ps, 'gamma%s' % n_, "%s e. Gamma'" % n_), mk['k']['J']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ps, n_, GX('J')))
    bi = w.s([], 'tmietbi', '( %s -> %s )' % (PSI, LBODY))
    ex[LPER] = w.s([bi], 'ralrimiva', '( %s -> %s )' % (ps, LPER))
    st = Bld(w, ps, c, ex)(LTREE)
    w.qed([st, w.inst('tm2fetb')], 'syl', ST_L)
    return w.run()


def tmietb():
    lab = 'tmietb'
    ps = cj(TREE_ETB)
    w = W(lab, 'Lean\'s ` emptyTbl_runs ` at the machine: wherever ` emptyTbl c tbl s ` is installed, the counter ` L ` on '
               '` c ` is consumed and the empty table on ` [ 0 , L ) ` (a ` blank ` marker, then ` L ` kets) pushed on ` tbl ` , '
               'every other stack restored, within ` L ( 4 ( bl L ) + 10 ) + 2 ( bl L ) + 8 ` steps (Lean\'s bound '
               '` L ( 4 log L + 14 ) + 2 log L + 11 ` at ` log L = bl L - 1 ` is at least this; ~ tmietbl ).')
    c = Ctx(w, ps, TREE_ETB)
    eqs = {'%s = %s' % (PDF, PDF): closed(w, ps, 'eqid', '%s = %s' % (PDF, PDF))}
    t, cc = inst(w, ps, 'tmietbl', {"P'": PDF}, Bld(w, ps, c, eqs))
    Ca, Da, na = triple_parts(cc)
    ln = c['L e. NN0']
    cl = Closure(w, ps, {'L': ('NN0', ln)})
    cl.leaf(BLL, 'NN0', w.s([ln, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ps, BLL)))
    neq = lineq(w, ps, na, ETBC, closure=cl, products=True)
    hrrw(w, ps, t, Ca, Da, na, neq=neq, qed=True)
    return w.run()


def tmietbb():
    lab = 'tmietbb'
    ps = cj(TREE_ETBB)
    w = W(lab, 'Lean\'s ` emptyTbl_le_B ` at the machine: with ` L < 2 ^ B ` , ` emptyTbl c tbl s ` runs within '
               '` ( L + 1 ) x. ( TMB ` B ) ` steps (~ tmietb , ~ tm2llistb ).')
    c = Ctx(w, ps, TREE_ETBB)
    t, cc = inst(w, ps, 'tmietb', {}, Bld(w, ps, c, {}))
    Ca, Da, na = triple_parts(cc)
    ln, bb, lt = c['L e. NN0'], c['B e. NN0'], c['L < ( 2 ^ B )']
    bl = w.s([ln, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ps, BLL))
    blb = w.s([ln, bb, lt, w.inst('blle')], 'syl3anc', '( %s -> %s <_ B )' % (ps, BLL))
    cl = Closure(w, ps, {'L': ('NN0', ln), 'B': ('NN0', bb)})
    cl.leaf(BLL, 'NN0', bl)
    C_ = '( ( 4 x. %s ) + ; 1 0 )' % BLL
    D_ = '( ( 2 x. %s ) + 8 )' % BLL
    c1 = linarith(w, ps, [blb, cl.ge0('B')], '%s <_ ( ; 6 4 x. ( B + 2 ) )' % C_, closure=cl)
    c2 = linarith(w, ps, [blb, cl.ge0('B')], '%s <_ ( ; 6 4 x. ( B + 2 ) )' % D_, closure=cl)
    j = w.s([w.s([ln, bb], 'jca', '( %s -> ( L e. NN0 /\\ B e. NN0 ) )' % ps),
             w.s([cl.mem(C_, 'NN0'), cl.mem(D_, 'NN0')], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ps, C_, D_)),
             w.s([c1, c2], 'jca', '( %s -> ( %s <_ ( ; 6 4 x. ( B + 2 ) ) /\\ %s <_ ( ; 6 4 x. ( B + 2 ) ) ) )' % (ps, C_, D_))], '3jca',
            '( %s -> ( ( L e. NN0 /\\ B e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s <_ ( ; 6 4 x. ( B + 2 ) ) /\\ %s <_ ( ; 6 4 x. ( B + 2 ) ) ) ) )'
            % (ps, C_, D_, C_, D_))
    assert na == '( ( L x. %s ) + %s )' % (C_, D_), na
    le = w.s([j, w.inst('tm2llistb')], 'syl', '( %s -> %s <_ ( ( L + 1 ) x. ( TMB ` B ) ) )' % (ps, na))
    tb = w.s([w.s([bb, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ps)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ps)
    cl.leaf('( TMB ` B )', 'NN0', tb)
    hrle(w, ps, c[PHM], t, Ca, Da, na, '( ( L + 1 ) x. ( TMB ` B ) )', cl.mem('( ( L + 1 ) x. ( TMB ` B ) )', 'NN0'), le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
