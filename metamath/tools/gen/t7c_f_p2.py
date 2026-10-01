"""T7c: Lean's ` pow2 x y s s' ` (Prims.lean) at the machine, on the installation
predicate TMIpow2.

  defs      append the syntax and df- of TMIpow2 to the sortie file
  tmip2u    the unfolding theorem
  tmip2enc  ( encNatGam ` ( 2 ^ E ) ) as its digits
  tmip2i    one iteration: predNum x s' ; pushSym y 0 ; isZero x s
  tmip2t    the typings, the exit test, the prologue
  tmip2l    ~ tm2floopu assembled ( P' a letter)
  tmip2c    pow2_correct (the length bound)
  tmip2b    pow2_le_B

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_f_p2.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *
from cl import Closure
import lin
from lin import linarith, lineq, nlinarith

lin.FASTPATH = True
SEL = sys.argv[1:]

P2F = FRAGS['p2']


def defs():
    import t7b_a_defs as AD
    AD.main(['p2'])


def tmip2u():
    import t7b_b_unf as UF
    return UF.unf('p2')


Z0 = '<. 1 , (/) >.'
B1 = '<. 1 , 1o >.'
ST_ENC = '( F e. NN0 -> ( encNatGam ` ( 2 ^ F ) ) = ( ( %s repeatS F ) ++ <" %s "> ) )' % (Z0, B1)


def tmip2enc():
    lab = 'tmip2enc'
    ph = 'F e. NN0'
    w = W(lab, 'The stack word of ` 2 ^ F ` : ` F ` zero bits then a one (Lean ` encodeNat_two_pow ` ).')
    fn = w.s([], 'id', '( %s -> F e. NN0 )' % ph)
    p = '( 2 ^ F )'
    pn = w.s([closed(w, ph, '2nn0', '2 e. NN0'), fn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, p))
    pz = w.s([pn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, p))
    pnn = w.s([closed(w, ph, '2nn', '2 e. NN'), fn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, p))
    prp = w.s([pnn], 'nnrpd', '( %s -> %s e. RR+ )' % (ph, p))
    e1 = w.s([pn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. ( encodeNat ` %s ) ) )' % (ph, p, p))
    e2 = w.s([pn, w.inst('encnatbwrd')], 'syl', '( %s -> ( encodeNat ` %s ) = ( %s bwrd ( bl ` %s ) ) )' % (ph, p, p, p))
    e3 = w.s([fn, w.inst('blp2')], 'syl', '( %s -> ( bl ` %s ) = ( F + 1 ) )' % (ph, p))
    e23 = w.s([e2, w.s([e3], 'oveq2d', '( %s -> ( %s bwrd ( bl ` %s ) ) = ( %s bwrd ( F + 1 ) ) )' % (ph, p, p, p))], 'eqtrd',
              '( %s -> ( encodeNat ` %s ) = ( %s bwrd ( F + 1 ) ) )' % (ph, p, p))
    BIT = 'if ( F e. ( bits ` %s ) , 1o , (/) )' % p
    e4 = w.s([pz, fn, w.inst('bwrdp1')], 'syl2anc', '( %s -> ( %s bwrd ( F + 1 ) ) = ( ( %s bwrd F ) ++ <" %s "> ) )' % (ph, p, p, BIT))
    fz = w.s([fn], 'nn0zd', '( %s -> F e. ZZ )' % ph)
    fuz = w.s([fz, w.inst('uzid')], 'syl', '( %s -> F e. ( ZZ>= ` F ) )' % ph)
    e5 = w.s([pz, fn, fuz, w.inst('bwrdmod')], 'syl3anc', '( %s -> ( ( %s mod %s ) bwrd F ) = ( %s bwrd F ) )' % (ph, p, p, p))
    m0 = w.s([prp, w.inst('modid0')], 'syl', '( %s -> ( %s mod %s ) = 0 )' % (ph, p, p))
    e6 = w.s([w.s([w.s([m0], 'oveq1d', '( %s -> ( ( %s mod %s ) bwrd F ) = ( 0 bwrd F ) )' % (ph, p, p)), e5], 'eqtr3d',
                  '( %s -> ( %s bwrd F ) = ( 0 bwrd F ) )' % (ph, p)),
              w.s([w.s([fn, w.inst('bwrep0')], 'syl', '( %s -> ( (/) repeatS F ) = ( 0 bwrd F ) )' % ph)], 'eqcomd',
                  '( %s -> ( 0 bwrd F ) = ( (/) repeatS F ) )' % ph)], 'eqtrd', '( %s -> ( %s bwrd F ) = ( (/) repeatS F ) )' % (ph, p))
    bv = w.s([pz, fn, w.inst('bitsval2')], 'syl2anc', '( %s -> ( F e. ( bits ` %s ) <-> -. 2 || ( |_ ` ( %s / %s ) ) ) )' % (ph, p, p, p))
    dv = w.s([w.s([pnn], 'nncnd', '( %s -> %s e. CC )' % (ph, p)), w.s([pnn], 'nnne0d', '( %s -> %s =/= 0 )' % (ph, p)), w.inst('divid')], 'syl2anc',
             '( %s -> ( %s / %s ) = 1 )' % (ph, p, p))
    fl1 = w.s([w.s([dv], 'fveq2d', '( %s -> ( |_ ` ( %s / %s ) ) = ( |_ ` 1 ) )' % (ph, p, p)),
               closed(w, ph, 'fl1' if False else 'flid', '') if False else w.s([closed(w, ph, '1z', '1 e. ZZ'), w.inst('flid')], 'syl', '( %s -> ( |_ ` 1 ) = 1 )' % ph)],
              'eqtrd', '( %s -> ( |_ ` ( %s / %s ) ) = 1 )' % (ph, p, p))
    nd = w.s([w.s([fl1], 'breq2d', '( %s -> ( 2 || ( |_ ` ( %s / %s ) ) <-> 2 || 1 ) )' % (ph, p, p)), closed(w, ph, 'n2dvds1', '-. 2 || 1')], 'mtbird',
             '( %s -> -. 2 || ( |_ ` ( %s / %s ) ) )' % (ph, p, p))
    fin = w.s([nd, bv], 'mpbird', '( %s -> F e. ( bits ` %s ) )' % (ph, p))
    it = w.s([fin], 'iftrued', '( %s -> %s = 1o )' % (ph, BIT))
    w1 = w.s([e6, w.s([it], 's1eqd', '( %s -> <" %s "> = <" 1o "> )' % (ph, BIT))], 'oveq12d',
             '( %s -> ( ( %s bwrd F ) ++ <" %s "> ) = ( ( (/) repeatS F ) ++ <" 1o "> ) )' % (ph, p, BIT))
    EN = '( ( (/) repeatS F ) ++ <" 1o "> )'
    en = w.s([w.s([e23, e4], 'eqtrd', '( %s -> ( encodeNat ` %s ) = ( ( %s bwrd F ) ++ <" %s "> ) )' % (ph, p, p, BIT)), w1], 'eqtrd',
             '( %s -> ( encodeNat ` %s ) = %s )' % (ph, p, EN))
    z2 = closed(w, ph, '0el2o', '(/) e. 2o')
    o2 = closed(w, ph, '1oel2o', '1o e. 2o')
    ff = closed(w, ph, 'inclboolf', "inclBool : 2o --> Gamma'")
    rw_ = w.s([z2, fn, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS F ) e. Word 2o )' % ph)
    s1 = w.s([o2], 's1cld', '( %s -> <" 1o "> e. Word 2o )' % ph)
    cc = w.s([rw_, s1, ff, w.inst('ccatco')], 'syl3anc', '( %s -> ( inclBool o. %s ) = ( ( inclBool o. ( (/) repeatS F ) ) ++ ( inclBool o. <" 1o "> ) ) )' % (ph, EN))
    rc = w.s([z2, fn, ff, w.inst('repsco')], 'syl3anc', '( %s -> ( inclBool o. ( (/) repeatS F ) ) = ( ( inclBool ` (/) ) repeatS F ) )' % ph)
    rc2 = w.s([rc, w.s([w.s([z2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ph, Z0))], 'oveq1d',
                       '( %s -> ( ( inclBool ` (/) ) repeatS F ) = ( %s repeatS F ) )' % (ph, Z0))], 'eqtrd',
              '( %s -> ( inclBool o. ( (/) repeatS F ) ) = ( %s repeatS F ) )' % (ph, Z0))
    sc = w.s([w.s([o2, ff, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" 1o "> ) = <" ( inclBool ` 1o ) "> )' % ph),
              w.s([w.s([o2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = %s )' % (ph, B1))], 's1eqd',
                  '( %s -> <" ( inclBool ` 1o ) "> = <" %s "> )' % (ph, B1))], 'eqtrd', '( %s -> ( inclBool o. <" 1o "> ) = <" %s "> )' % (ph, B1))
    g = w.s([cc, w.s([rc2, sc], 'oveq12d', '( %s -> ( ( inclBool o. ( (/) repeatS F ) ) ++ ( inclBool o. <" 1o "> ) ) = ( ( %s repeatS F ) ++ <" %s "> ) )'
                     % (ph, Z0, B1))], 'eqtrd', '( %s -> ( inclBool o. %s ) = ( ( %s repeatS F ) ++ <" %s "> ) )' % (ph, EN, Z0, B1))
    w.qed([e1, w.s([w.s([en], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` %s ) ) = ( inclBool o. %s ) )' % (ph, p, EN)), g], 'eqtrd',
                    '( %s -> ( inclBool o. ( encodeNat ` %s ) ) = ( ( %s repeatS F ) ++ <" %s "> ) )' % (ph, p, Z0, B1))], 'eqtrd', ST_ENC)
    return w.run()


K4 = ['K', 'J', 'I', "I'"]
LMP = P2F.lmap()
CNFL = '( u e. TMSt |-> if ( ( TMfl ` u ) = 1o , (/) , 1o ) )'
def NC2(h, t):
    return '( TMfl ` %s ) = if ( ( F - %s ) = 0 , 1o , (/) )' % (h, t)
FAMF = lambda cond: '( j e. NN0 |-> { h e. TMSt | %s } )' % cond('h', 'j')
RAB = lambda cond, t: '{ h e. TMSt | %s }' % cond('h', t)
N2F = FAMF(NC2)
def YV(t):
    return '( ( %s repeatS %s ) ++ ( <" %s "> ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (Z0, t, B1)
def PB2(t):
    return UP(UP('D', 'K', EW('( F - %s )' % t, 'X')), 'J', YV(t))
PDF2 = '( j e. NN0 |-> %s )' % PB2('j')
PV = "P'"
ENCF = '( encodeNat ` F )'
TP = '( ( 4 x. ( # ` %s ) ) + 9 )' % ENCF
DATA_P = (('F e. NN0', WRD('X', GAM), STKD('D')), ('( D ` K ) = %s' % EW('F', 'X'), '%s = %s' % (PV, PDF2)))
T_P = ((T_PHM7, P2F.pred()), (idx_tree(K4), dist_tree(K4)), DATA_P)
PHP = cj(T_P)
PSIP = '( %s /\\ i e. ( 0 ..^ F ) )' % PHP
GM2 = {'A': LMP['L'], 'B0': LMP['B0'], 'E': LMP['X0'], 'C0': CNFL, 'R': 'F', "T'": TP, 'N': N2F, 'P': PV}
_LA, _LC = split_imp(stmt('tm2floopu'))
LTREE = tsub(parse_conj(_LA), GM2)
LCONCL = tsub_text(_LC, GM2)
LTYP, LPER, LEXIT = LTREE[1]
assert LPER.startswith('A. i e. ( 0 ..^ F ) ')
LBODY = LPER[len('A. i e. ( 0 ..^ F ) '):]


class Pc:
    """facts under ps (the pow2 antecedent T_P or a substituted tree)"""
    def __init__(self, w, ps, tree=None, root=None, lift=None, pv=None):
        self.w, self.ps = w, ps
        self.PV = pv or PV
        tree = tree or T_P
        if root is None and ps != cj(tree):
            root = w.s([], lift or 'simpl', '( %s -> %s )' % (ps, cj(tree)))
        self.c = c = Ctx(w, ps, tree, root=root)
        self.mk = machine(w, ps, c, K4)
        self.ne = ne_fn(w, ps, c, set(flat(dist_tree(K4))))
        mk = self.mk
        self.base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        self.base.update(unfold_all(w, ps, c[P2F.pred()], 'p2', K4, 'P', 'E', rec=False))
        lmp = P2F.lmap()
        for j_, (fn_, ks_, en_, ex_) in enumerate(P2F.children):
            P_ = PL('P', P2F.slot(j_))
            pr = FRAGS[fn_].pred(ks_, 'T', 'M', P_, lmp[ex_])
            self.base.update(unfold_all(w, ps, self.base[pr], fn_, ks_, P_, lmp[ex_], rec=False))
        for s_ in K4:
            self.base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K4):
            for b in K4[i_ + 1:]:
                self.base['%s =/= %s' % (a, b)] = self.ne(a, b)
                self.base['%s =/= %s' % (b, a)] = self.ne(b, a)
        self.fn = c['F e. NN0']
        self.cl = Closure(w, ps, {'F': ('NN0', self.fn)})
        self.memo = {}

    def yw(self, t, tn):
        """( ps -> YV( t ) e. Word Gamma' )"""
        w, ps = self.w, self.ps
        zg = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, Z0))
        bg = w.s([closed(w, ps, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, B1))
        rw_ = w.s([zg, tn, w.inst('repsw')], 'syl2anc', "( %s -> ( %s repeatS %s ) e. Word Gamma' )" % (ps, Z0, t))
        dj = w.s([stkfv(w, ps, 'D', 'J', self.mk['tv'], self.c[STKD('D')], self.mk['k']['J']['kd']), self.mk['k']['J']['wge']], 'eleqtrd',
                 "( %s -> ( D ` J ) e. Word Gamma' )" % ps)
        r1 = wg4(w, ps, '( D ` J )', dj)
        r2 = wgcat(w, ps, '<" %s ">' % B1, YX('( D ` J )'), w.s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, B1)), r1)
        return wgcat(w, ps, '( %s repeatS %s )' % (Z0, t), '( <" %s "> ++ %s )' % (B1, YX('( D ` J )')), rw_, r2)

    def pv(self, t, tn, tle):
        """( ps -> ( P' ` t ) = PB2( t ) ), Stacks of PB2( t ), the numbers F - t"""
        key = ('pv', t)
        if key in self.memo:
            return self.memo[key]
        w, ps, c, cl = self.w, self.ps, self.c, self.cl
        FT = '( F - %s )' % t
        ftn = w.s([tn, self.fn, tle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ps, FT))
        dd = c[STKD('D')]
        vals = {}
        for s_ in K4:
            vals[s_] = selfval(w, ps, self.mk, 'D', dd, s_)
        S = Stacks(w, ps, self.mk, 'D', dd, self.ne, vals)
        S = S.upd('K', EW(FT, 'X'), ewg(w, ps, FT, ftn, 'X', c[WRD('X', GAM)]))
        S = S.upd('J', YV(t), self.yw(t, tn))
        assert S.D == PB2(t)
        pv0 = mval(w, ps, 'j', 'NN0', PB2, t, tn, w.s([S.memb], 'elexd', '( %s -> %s e. _V )' % (ps, PB2(t))))
        pe = w.s([c['%s = %s' % (self.PV, PDF2)]], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, self.PV, t, PDF2, t))
        pvs = w.s([pe, pv0], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, self.PV, t, PB2(t)))
        self.memo[key] = (pvs, S, ftn)
        return self.memo[key]

    def pvals(self, t, tn, tle):
        w, ps = self.w, self.ps
        pvs, S, ftn = self.pv(t, tn, tle)
        PT = '( %s ` %s )' % (self.PV, t)
        mem = w.s([pvs, S.memb], 'eqeltrd', '( %s -> %s e. %s )' % (ps, PT, STK_T))
        out = {}
        for s_ in K4:
            txt, st, g = S.vals[s_]
            e = w.s([pvs], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, PT, s_, S.D, s_))
            out[s_] = (txt, w.s([e, st], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PT, s_, txt)), g)
        return mem, Stacks(w, ps, self.mk, PT, mem, self.ne, out), ftn

    def famss(self, t, tn):
        w, ps = self.w, self.ps
        fv = famval(w, ps, NC2, t, tn)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % RAB(NC2, t))], 'a1i', '( %s -> %s C_ TMSt )' % (ps, RAB(NC2, t)))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, RAB(NC2, t)))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ ( 2nd ` T ) )' % (ps, N2F, t))


def enc_ib(w, ps, t, tn, X):
    """( ps -> EW( t , X ) = ( ( inclBool o. ( encodeNat ` t ) ) ++ ( <" 4 "> ++ X ) ) )"""
    gv = w.s([tn, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. %s ) )' % (ps, ENG(t), ENC(t)))
    return w.s([gv], 'oveq1d', '( %s -> %s = %s )' % (ps, EW(t, X), CC('( inclBool o. %s )' % ENC(t), YX(X))))


def lenle(w, ps, t, tn, tle, fn, cl):
    """( ps -> ( # ` ( encodeNat ` t ) ) <_ ( # ` ( encodeNat ` F ) ) ) for t <_ F"""
    lt = w.s([tn, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = ( bl ` %s ) )' % (ps, ENC(t), t))
    lf = w.s([fn, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = ( bl ` F ) )' % (ps, ENCF))
    blf = w.s([fn, w.inst('blcl')], 'syl', '( %s -> ( bl ` F ) e. NN0 )' % ps)
    fp = w.s([fn, w.inst('blpow2')], 'syl', '( %s -> F < ( 2 ^ ( bl ` F ) ) )' % ps)
    if 'p2bl' not in cl.__dict__:
        cl.p2bl = w.s([closed(w, ps, '2nn0', '2 e. NN0'), blf, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ ( bl ` F ) ) e. NN0 )' % ps)
        cl.leaf('( 2 ^ ( bl ` F ) )', 'NN0', cl.p2bl)
    cl.have(t, 'NN0', tn)
    tp = linarith(w, ps, [tle, fp], '%s < ( 2 ^ ( bl ` F ) )' % t, closure=cl, atoms=['( 2 ^ ( bl ` F ) )'])
    bl_ = w.s([tn, blf, tp, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` %s ) <_ ( bl ` F ) )' % (ps, t))
    return w.s([w.s([lt, bl_], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( bl ` F ) )' % (ps, ENC(t))), lf], 'breqtrrd',
               '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (ps, ENC(t), ENCF))


def tmip2i():
    lab = 'tmip2i'
    C = '( %s -> %s )' % (PSIP, LBODY)
    w = W(lab, 'One iteration of Lean\'s ` pow2 ` loop at the machine ( ` pow2Body_runs ` at ` P2Inv ` ): the test '
               '` !flag ` holds while ` i < e ` , and ` predNum x s\' ; pushSym y 0 ; isZero x s ` takes the exponent '
               'on ` x ` from ` e - i ` to ` e - ( i + 1 ) ` and pushes one more zero on ` y ` .')
    ps = PSIP
    pc = Pc(w, ps)
    cl = pc.cl
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ F ) )' % ps)
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < F )' % ps)
    ile = w.s([ilt], 'ltled', '( %s -> i <_ F )' % ps)
    cl.leaf('i', 'NN0', inn)
    I1 = '( i + 1 )'
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    i1le = w.s([w.s([cl.mem('i', 'ZZ'), cl.mem('F', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < F <-> %s <_ F ) )' % (ps, I1)), ilt],
               'mpbird' if False else 'mpbir' if False else 'bitrd' if False else 'syl' if False else 'mpbid', '') if False else None
    zl = w.s([cl.mem('i', 'ZZ'), cl.mem('F', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < F <-> %s <_ F ) )' % (ps, I1))
    i1le = w.s([ilt, zl], 'mpbid', '( %s -> %s <_ F )' % (ps, I1))
    FI, FI1 = '( F - i )', '( F - %s )' % I1
    finn = w.s([w.s([cl.mem('i', 'ZZ'), cl.mem('F', 'ZZ'), w.inst('znnsub')], 'syl2anc', '( %s -> ( i < F <-> %s e. NN ) )' % (ps, FI)), ilt],
               'mpbid' if False else 'mpbird' if False else 'sylibr' if False else 'mpbid', '') if False else None
    zn = w.s([cl.mem('i', 'ZZ'), cl.mem('F', 'ZZ'), w.inst('znnsub')], 'syl2anc', '( %s -> ( i < F <-> %s e. NN ) )' % (ps, FI))
    finn = w.s([ilt, zn], 'mpbid', '( %s -> %s e. NN )' % (ps, FI))
    mem, SP, fin0 = pc.pvals('i', inn, ile)
    PT = "( %s ` i )" % PV
    run = Run(w, ps, pc.mk, SP, pc.base, pc.c)
    EF = ENC(FI)
    efw = w.s([fin0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, EF))
    PBw = '( predBits ` %s )' % EF
    pbw = w.s([efw, w.inst('predbitscl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, PBw))
    kv = w.s([SP.vals['K'][1], enc_ib(w, ps, FI, fin0, 'X')], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, PT, CC('( inclBool o. %s )' % EF, YX('X'))))
    xg = pc.c[WRD('X', GAM)]
    nss = pc.famss('i', inn)
    NI = '( %s ` i )' % N2F
    APB = CC('( inclBool o. %s )' % PBw, YX('X'))
    apbg = wgcat(w, ps, '( inclBool o. %s )' % PBw, YX('X'), wib(w, ps, PBw, pbw), wg4(w, ps, 'X', xg))
    run.call('tmiprds', {'K': 'K', 'J': "I'", 'L': EF, 'X': 'X', 'P': PL('P', 5), 'E': PL('P', 3)},
             {'( %s ` K ) = %s' % (PT, CC('( inclBool o. %s )' % EF, YX('X'))): kv, WRD(EF, '2o'): efw},
             [('K', APB, apbg)], pre=(NI, nss))
    zg = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, Z0))
    yvi = SP.vals['J'][0]
    ZY = '( <" %s "> ++ %s )' % (Z0, yvi)
    zyg = wgcat(w, ps, '<" %s ">' % Z0, yvi, w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, Z0)), SP.vals['J'][2])
    ssS = closed(w, ps, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    run.call('tm2fpshn', {'A': PL('P', 3), 'E': PL(PL('P', 6), 0), 'K': 'J', 'Z': Z0, 'N': SS},
             {'%s e. %s' % (Z0, GX('J')): w.s([zg, pc.mk['k']['J']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ps, Z0, GX('J'))),
              '( 2nd ` T ) C_ ( 2nd ` T )': ssS}, [('J', ZY, zyg)])
    # isZero x s : the class
    pe = w.s([finn, w.inst('tmcpredenc')], 'syl', '( %s -> %s = ( encodeNat ` ( %s - 1 ) ) )' % (ps, PBw, FI))
    f1e = lineq(w, ps, '( %s - 1 )' % FI, FI1, closure=cl)
    fi1n = w.s([i1n, pc.fn, i1le, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ps, FI1))
    pe2 = w.s([pe, w.s([f1e], 'fveq2d', '( %s -> ( encodeNat ` ( %s - 1 ) ) = %s )' % (ps, FI, ENC(FI1)))], 'eqtrd', '( %s -> %s = %s )' % (ps, PBw, ENC(FI1)))
    tn = w.s([w.s([pe2], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ps, PBw, ENC(FI1))),
              w.s([fi1n, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = %s )' % (ps, ENC(FI1), FI1))], 'eqtrd',
             '( %s -> ( toNat ` %s ) = %s )' % (ps, PBw, FI1))
    OLD = '{ h e. TMSt | ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) }' % PBw
    ce = w.s([w.s([w.s([tn], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> %s = 0 ) )' % (ps, PBw, FI1))], 'ifbid',
                  '( %s -> if ( ( toNat ` %s ) = 0 , 1o , (/) ) = if ( %s = 0 , 1o , (/) ) )' % (ps, PBw, FI1))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, PBw, NC2('h', I1)))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, PBw, NC2('h', I1)))],
             'rabbidva', '( %s -> %s = %s )' % (ps, OLD, RAB(NC2, I1)))
    fv1 = famval(w, ps, NC2, I1, i1n)
    rb2 = w.s([rb, w.s([fv1], 'eqcomd', '( %s -> %s = ( %s ` %s ) )' % (ps, RAB(NC2, I1), N2F, I1))], 'eqtrd',
              '( %s -> %s = ( %s ` %s ) )' % (ps, OLD, N2F, I1))
    S = run.S
    run.call('tmiizs', {'K': 'K', 'I': 'I', 'L': PBw, 'X': 'X', 'P': PL('P', 6), 'E': PL('P', 2)},
             {'( %s ` K ) = %s' % (S.D, APB): S.vals['K'][1], WRD(PBw, '2o'): pbw}, [], cls_rw=(rb2, '( %s ` %s )' % (N2F, I1)))
    cur, out = run.normalize(K4)
    assert out == [('K', APB), ('J', ZY)], out
    # the stacks : UPD( UPD( PT , K , APB ) , J , ZY ) = ( P' ` ( i + 1 ) )
    pvi, Si, _ = pc.pv('i', inn, ile)
    DQ = UP(UP(PT, 'K', APB), 'J', ZY)
    r1, n1_ = w.rewrite(DQ, {PT: (PB2('i'), pvi)}, ps)
    a_, b_ = EW(FI, 'X'), YV('i')
    togk = lambda X, s_, g: w.s([g, pc.mk['k'][s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s_)))
    kK, kJ = pc.mk['k']['K'], pc.mk['k']['J']
    u4 = up4(w, ps, 'D', 'K', a_, 'J', b_, APB, ZY, pc.mk['tv'], pc.c[STKD('D')], pc.ne('K', 'J'), kK['kd'],
             togk(a_, 'K', Si.vals['K'][2]), togk(APB, 'K', apbg), kJ['kd'], togk(b_, 'J', Si.vals['J'][2]), togk(ZY, 'J', zyg))
    NEWD = UP(UP('D', 'K', APB), 'J', ZY)
    e1 = w.s([r1, u4], 'eqtrd', '( %s -> %s = %s )' % (ps, DQ, NEWD))
    # APB = EW( F - ( i + 1 ) , X )
    ib1 = enc_ib(w, ps, FI1, fi1n, 'X')
    ap = w.s([w.s([w.s([pe2], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. %s ) )' % (ps, PBw, ENC(FI1)))], 'oveq1d',
                  '( %s -> %s = %s )' % (ps, APB, CC('( inclBool o. %s )' % ENC(FI1), YX('X')))), ib1], 'eqtr4d',
             '( %s -> %s = %s )' % (ps, APB, EW(FI1, 'X')))
    # ZY = YV( i + 1 )
    zcl = w.s([zg], 'elexd', '( %s -> %s e. _V )' % (ps, Z0))
    rs1 = w.s([zcl, w.inst('repsw1')], 'syl', '( %s -> ( %s repeatS 1 ) = <" %s "> )' % (ps, Z0, Z0))
    rcc = w.s([zcl, closed(w, ps, '1nn0', '1 e. NN0'), inn, w.inst('repswccat')], 'syl3anc',
              '( %s -> ( ( %s repeatS 1 ) ++ ( %s repeatS i ) ) = ( %s repeatS ( 1 + i ) ) )' % (ps, Z0, Z0, Z0))
    ac = w.s([closed(w, ps, 'ax-1cn', '1 e. CC'), cl.mem('i', 'CC'), w.inst('addcom')], 'syl2anc', '( %s -> ( 1 + i ) = ( i + 1 ) )' % ps)
    rcc2 = w.s([w.s([w.s([rs1], 'oveq1d', '( %s -> ( ( %s repeatS 1 ) ++ ( %s repeatS i ) ) = ( <" %s "> ++ ( %s repeatS i ) ) )' % (ps, Z0, Z0, Z0, Z0)), rcc],
                    'eqtr3d', '( %s -> ( <" %s "> ++ ( %s repeatS i ) ) = ( %s repeatS ( 1 + i ) ) )' % (ps, Z0, Z0, Z0)),
                w.s([ac], 'oveq2d', '( %s -> ( %s repeatS ( 1 + i ) ) = ( %s repeatS ( i + 1 ) ) )' % (ps, Z0, Z0))], 'eqtrd',
               '( %s -> ( <" %s "> ++ ( %s repeatS i ) ) = ( %s repeatS ( i + 1 ) ) )' % (ps, Z0, Z0, Z0))
    REST = '( <" %s "> ++ ( <" 4 "> ++ ( D ` J ) ) )' % B1
    rwi = w.s([zg, inn, w.inst('repsw')], 'syl2anc', "( %s -> ( %s repeatS i ) e. Word Gamma' )" % (ps, Z0))
    restg = w.s([w.s([Si.vals['J'][2]], 'id', '') if False else rwi], 'id', '') if False else None
    djg = w.s([stkfv(w, ps, 'D', 'J', pc.mk['tv'], pc.c[STKD('D')], kJ['kd']), kJ['wge']], 'eleqtrd', "( %s -> ( D ` J ) e. Word Gamma' )" % ps)
    bg = w.s([closed(w, ps, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, B1))
    restg = wgcat(w, ps, '<" %s ">' % B1, YX('( D ` J )'), w.s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, B1)), wg4(w, ps, '( D ` J )', djg))
    cas = w.s([w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, Z0)), rwi, restg, w.inst('ccatass')], 'syl3anc',
              '( %s -> ( ( <" %s "> ++ ( %s repeatS i ) ) ++ %s ) = %s )' % (ps, Z0, Z0, REST, ZY))
    zy = w.s([cas, w.s([rcc2], 'oveq1d', '( %s -> ( ( <" %s "> ++ ( %s repeatS i ) ) ++ %s ) = %s )' % (ps, Z0, Z0, REST, YV(I1)))], 'eqtr3d',
             '( %s -> %s = %s )' % (ps, ZY, YV(I1)))
    r2, n2_ = w.rewrite(NEWD, {APB: (EW(FI1, 'X'), ap), ZY: (YV(I1), zy)}, ps)
    assert n2_ == PB2(I1), n2_
    pv1, _, _ = pc.pv(I1, i1n, i1le)
    deq_s = w.s([w.s([e1, r2], 'eqtrd', '( %s -> %s = %s )' % (ps, DQ, PB2(I1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ps, DQ, PV, I1))
    head = run.cur[:-len(' X. { %s } ) )' % DQ)]
    ncls = head.split(' } X. ( ', 1)[1]
    d = clneq(w, ps, LMP['L'], ncls, deq_s, DQ, '( %s ` %s )' % (PV, I1))
    t2, C2, D2, n2 = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=d)
    # the bound
    l1 = lenle(w, ps, FI, fin0, w.s([cl.mem('F', 'RR'), cl.mem('i', 'RR'), w.s([inn], 'nn0ge0d', '( %s -> 0 <_ i )' % ps)], 'jca', '') if False else
               linarith(w, ps, [cl.ge0('i')], '%s <_ F' % FI, closure=cl), pc.fn, cl)
    l2 = lenle(w, ps, FI1, fi1n, linarith(w, ps, [cl.ge0('i')], '%s <_ F' % FI1, closure=cl), pc.fn, cl)
    lp = w.s([w.s([pe2], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ps, PBw, ENC(FI1))), l2], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (ps, PBw, ENCF))
    for a_t, st_ in [('( # ` %s )' % EF, w.s([efw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, EF))),
                     ('( # ` %s )' % PBw, w.s([pbw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, PBw))),
                     ('( # ` %s )' % ENCF, w.s([w.s([pc.fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF)), w.inst('lencl')], 'syl',
                                                '( %s -> ( # ` %s ) e. NN0 )' % (ps, ENCF)))]:
        cl.leaf(a_t, 'NN0', st_)
    le = linarith(w, ps, [l1, lp], '%s <_ %s' % (n2, TP), closure=cl)
    t3 = hrle(w, ps, pc.mk['phm'], t2, C2, D2, n2, TP, cl.mem(TP, 'NN0'), le)
    # HT
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NC2, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    nz = w.s([w.s([finn], 'nnne0d', '( %s -> %s =/= 0 )' % (ps, FI))], 'neneqd', '( %s -> -. %s = 0 )' % (ps, FI))
    f0 = w.s([mc, w.s([Lm(nz)], 'iffalsed', '( %s -> if ( %s = 0 , 1o , (/) ) = (/) )' % (pm, FI))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    X_of = lambda t_: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t_
    xex = ifex_closed(w, pm, '( TMfl ` m ) = 1o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    htm = w.s([cv, w.s([not1o(w, pm, f0, 'TMfl', 'm')], 'iffalsed', '( %s -> %s = 1o )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CNFL))
    ht = w.s([htm], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNFL))
    w.qed([ht, t3], 'jca', C)
    return w.run()


REST = '( <" %s "> ++ ( <" 4 "> ++ ( D ` J ) ) )' % B1
PRO_N = '( ( 1 + 1 ) + ( ( 2 x. ( # ` %s ) ) + 5 ) )' % ENCF
PROT = TRI(CLN(LMP['A'], SS, 'D'), CLN(LMP['L'], '( %s ` 0 )' % N2F, '( %s ` 0 )' % PV), PRO_N)


def prologue(w, ps, pc):
    """the prologue triple PROT under ps"""
    cl = pc.cl
    dd = pc.c[STKD('D')]
    xg = pc.c[WRD('X', GAM)]
    vals = {s_: selfval(w, ps, pc.mk, 'D', dd, s_) for s_ in K4}
    vals['K'] = (EW('F', 'X'), pc.c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ps, 'F', pc.fn, 'X', xg))
    S0 = Stacks(w, ps, pc.mk, 'D', dd, pc.ne, vals)
    run = Run(w, ps, pc.mk, S0, pc.base, pc.c)
    ssS = closed(w, ps, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    g4 = closed(w, ps, 'gamma4', "4 e. Gamma'")
    bg = w.s([closed(w, ps, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, B1))
    kJ = pc.mk['k']['J']
    dj = S0.vals['J']
    V1 = YX('( D ` J )')
    v1g = wg4(w, ps, '( D ` J )', dj[2])
    run.call('tm2fpshn', {'A': LMP['A'], 'E': LMP["A'"], 'K': 'J', 'Z': '4', 'N': SS},
             {'4 e. %s' % GX('J'): w.s([g4, kJ['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ps, GX('J'))), '( 2nd ` T ) C_ ( 2nd ` T )': ssS},
             [('J', V1, v1g)])
    v2g = wgcat(w, ps, '<" %s ">' % B1, V1, w.s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, B1)), v1g)
    run.call('tm2fpshn', {'A': LMP["A'"], 'E': LMP['Z0'], 'K': 'J', 'Z': B1, 'N': SS},
             {'%s e. %s' % (B1, GX('J')): w.s([bg, kJ['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ps, B1, GX('J'))), '( 2nd ` T ) C_ ( 2nd ` T )': ssS},
             [('J', REST, v2g)])
    S = run.S
    efw = w.s([pc.fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF))
    kv = w.s([S.vals['K'][1], enc_ib(w, ps, 'F', pc.fn, 'X')], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, S.D, CC('( inclBool o. %s )' % ENCF, YX('X'))))
    tn = w.s([pc.fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ps, ENCF))
    f0 = w.s([cl.mem('F', 'CC')], 'subid1d', '( %s -> ( F - 0 ) = F )' % ps)
    tn0 = w.s([tn, f0], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( F - 0 ) )' % (ps, ENCF))
    OLD = '{ h e. TMSt | ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) }' % ENCF
    ce = w.s([w.s([w.s([tn0], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( F - 0 ) = 0 ) )' % (ps, ENCF))], 'ifbid',
                  '( %s -> if ( ( toNat ` %s ) = 0 , 1o , (/) ) = if ( ( F - 0 ) = 0 , 1o , (/) ) )' % (ps, ENCF))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, ENCF, NC2('h', '0')))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = if ( ( toNat ` %s ) = 0 , 1o , (/) ) <-> %s ) )' % (ps, ENCF, NC2('h', '0')))],
             'rabbidva', '( %s -> %s = %s )' % (ps, OLD, RAB(NC2, '0')))
    z0 = closed(w, ps, '0nn0', '0 e. NN0')
    fv0 = famval(w, ps, NC2, '0', z0)
    rb2 = w.s([rb, w.s([fv0], 'eqcomd', '( %s -> %s = ( %s ` 0 ) )' % (ps, RAB(NC2, '0'), N2F))], 'eqtrd', '( %s -> %s = ( %s ` 0 ) )' % (ps, OLD, N2F))
    run.call('tmiizs', {'K': 'K', 'I': 'I', 'L': ENCF, 'X': 'X', 'P': PL('P', 4), 'E': LMP['L']},
             {'( %s ` K ) = %s' % (S.D, CC('( inclBool o. %s )' % ENCF, YX('X'))): kv, WRD(ENCF, '2o'): efw}, [], cls_rw=(rb2, '( %s ` 0 )' % N2F))
    cur, out = run.normalize(K4)
    assert out == [('J', REST)], out
    # UPD( D , J , REST ) = ( P' ` 0 )
    z0le = w.s([pc.fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ps)
    pv0, S0p, _ = pc.pv('0', z0, z0le)
    zcl = w.s([w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, Z0))], 'elexd', '( %s -> %s e. _V )' % (ps, Z0))
    r0 = w.s([zcl, w.inst('repsw0')], 'syl', '( %s -> ( %s repeatS 0 ) = (/) )' % (ps, Z0))
    cl0 = w.s([v2g, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, REST, REST))
    yv0 = w.s([w.s([r0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, YV('0'), REST)), cl0], 'eqtrd', '( %s -> %s = %s )' % (ps, YV('0'), REST))
    ek = w.s([w.s([w.s([f0], 'fveq2d', '( %s -> ( encNatGam ` ( F - 0 ) ) = ( encNatGam ` F ) )' % ps)], 'oveq1d',
                  '( %s -> %s = %s )' % (ps, EW('( F - 0 )', 'X'), EW('F', 'X')))], 'id', '') if False else \
        w.s([w.s([f0], 'fveq2d', '( %s -> ( encNatGam ` ( F - 0 ) ) = ( encNatGam ` F ) )' % ps)], 'oveq1d',
            '( %s -> %s = %s )' % (ps, EW('( F - 0 )', 'X'), EW('F', 'X')))
    r1, x1 = w.rewrite(PB2('0'), {EW('( F - 0 )', 'X'): (EW('F', 'X'), ek), YV('0'): (REST, yv0)}, ps)
    DK = UP('D', 'K', EW('F', 'X'))
    assert x1 == UP(DK, 'J', REST), x1
    u1 = upidv(w, ps, 'D', 'K', EW('F', 'X'), pc.c['( D ` K ) = %s' % EW('F', 'X')], pc.mk['tv'], dd, pc.mk['k']['K']['kd'])
    r2, x2 = w.rewrite(x1, {DK: ('D', u1)}, ps)
    p0 = w.s([w.s([pv0, r1], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ps, PV, x1)), r2], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ps, PV, x2))
    d = clneq(w, ps, LMP['L'], '( %s ` 0 )' % N2F, w.s([p0], 'eqcomd', '( %s -> %s = ( %s ` 0 ) )' % (ps, x2, PV)), x2, '( %s ` 0 )' % PV)
    t2, C2, D2, n2 = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=d)
    assert HR(C2, 'T', 'M', D2, n2) == PROT, (HR(C2, 'T', 'M', D2, n2), PROT)
    return t2


def tmip2t():
    lab = 'tmip2t'
    C = '( %s -> ( %s /\\ %s /\\ %s ) )' % (PHP, LTYP, LEXIT, PROT)
    w = W(lab, 'The frame of Lean\'s ` pow2 ` loop at the machine: the invariant\'s classes and stacks for '
               '` i <_ e ` , the test ` !flag ` failing at ` e ` , and the prologue ` pushSym y comma ; pushSym y 1 ; '
               'isZero x s ` entering the invariant at 0.')
    ps = PHP
    pc = Pc(w, ps)
    cl = pc.cl
    pt = '( %s /\\ i e. ( 0 ... F ) )' % ps
    pt_c = Pc(w, pt)
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ... F ) )' % pt)
    inn = w.s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = w.s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ F )' % pt)
    mem, _, _ = pt_c.pvals('i', inn, ile)
    typ = w.s([w.s([pt_c.famss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYP[len('A. i e. ( 0 ... F ) '):]))], 'ralrimiva', '( %s -> %s )' % (ps, LTYP))
    NFF = '( %s ` F )' % N2F
    pm = '( %s /\\ m e. %s )' % (ps, NFF)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NC2, 'F', Lm(pc.fn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NFF)))
    ff = w.s([cl.mem('F', 'CC')], 'subidd', '( %s -> ( F - F ) = 0 )' % ps)
    f1 = w.s([mc, w.s([Lm(ff)], 'iftrued', '( %s -> if ( ( F - F ) = 0 , 1o , (/) ) = 1o )' % pm)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    X_of = lambda t_: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t_
    xex = ifex_closed(w, pm, '( TMfl ` m ) = 1o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    c0 = w.s([cv, w.s([f1], 'iftrued', '( %s -> %s = (/) )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CNFL))
    ex_ = w.s([not1o(w, pm, c0, CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXIT))
    t = prologue(w, ps, pc)
    w.qed([typ, ex_, t], '3jca', C)
    return w.run()


LBND = triple_parts(LCONCL)[2]
BNDL = '( %s + %s )' % (PRO_N, LBND)
CONCL_L = TRI(CLN(LMP['A'], SS, 'D'), CLN(LMP['X0'], '( %s ` F )' % N2F, '( %s ` F )' % PV), BNDL)


def tmip2l():
    lab = 'tmip2l'
    C = '( %s -> %s )' % (PHP, CONCL_L)
    w = W(lab, 'Lean\'s ` pow2 ` at the machine up to the final ` dropNum ` : the prologue and ~ tm2floopu at the '
               'families of ` P2Inv ` (the exponent ` e - i ` on ` x ` , ` i ` zeros above the one on ` y ` ).')
    ps = PHP
    pc = Pc(w, ps)
    cl = pc.cl
    ex = dict(pc.base)
    from t7_e_cmp import lamty
    b01 = w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', 'if ( ( TMfl ` u ) = 1o , (/) , 1o ) e. 2o')
    ex[CTY(CNFL)] = lamty(w, ps, pc.mk, CNFL, lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t, '2o', w.s([], '2oex', '2o e. _V'), b01)
    ex['F e. NN0'] = pc.fn
    efn = w.s([w.s([pc.fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF)), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, ENCF))
    cl.leaf('( # ` %s )' % ENCF, 'NN0', efn)
    ex['%s e. NN0' % TP] = cl.mem(TP, 'NN0')
    tg = w.s([], 'tmip2t', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ps, LTYP, LEXIT, PROT))
    ex[LTYP] = w.s([tg, w.inst('simp1')], 'syl', '( %s -> %s )' % (ps, LTYP))
    ex[LEXIT] = w.s([tg, w.inst('simp2')], 'syl', '( %s -> %s )' % (ps, LEXIT))
    pro = w.s([tg, w.inst('simp3')], 'syl', '( %s -> %s )' % (ps, PROT))
    bi = w.s([], 'tmip2i', '( %s -> %s )' % (PSIP, LBODY))
    ex[LPER] = w.s([bi], 'ralrimiva', '( %s -> %s )' % (ps, LPER))
    st = Bld(w, ps, pc.c, ex)(LTREE)
    lp = w.s([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ps, LCONCL))
    Cp, Dp, np_ = triple_parts(PROT)
    Cl, Dl, nl = triple_parts(LCONCL)
    assert Dp == Cl, (Dp, Cl)
    w.qed([pc.mk['phm'], pro, lp], 'syl3anc', C)
    return w.run()


T_C = ((T_PHM7, P2F.pred()), (idx_tree(K4), dist_tree(K4)), (('F e. NN0', WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % EW('F', 'X')))
DFIN = UP(UP('D', 'K', 'X'), 'J', EW('( 2 ^ F )', '( D ` J )'))
BNDC = '( %s + 1 )' % BNDL
CONCL_C = TRI(CLN(LMP['A'], SS, 'D'), CLN('E', SS, DFIN), BNDC)


def tmip2c():
    lab = 'tmip2c'
    ps = cj(T_C)
    C = '( %s -> %s )' % (ps, CONCL_C)
    w = W(lab, 'Lean\'s ` pow2_correct ` at the machine: wherever ` pow2 x y s s\' ` is installed, the exponent ` e ` '
               'on ` x ` is consumed and ` 2 ^ e ` pushed on ` y ` , the other stacks restored (~ tmip2l at its stack '
               'family, then ` dropNum x ` ).')
    c = Ctx(w, ps, T_C)
    eq = closed(w, ps, 'eqid', '%s = %s' % (PDF2, PDF2))
    TP2 = tsub(T_P, {PV: PDF2})
    root = Bld(w, ps, c, {'%s = %s' % (PDF2, PDF2): eq})(TP2)
    pc = Pc(w, ps, tree=TP2, root=root, pv=PDF2)
    cl = pc.cl
    t, cc = inst(w, ps, 'tmip2l', {PV: PDF2}, Bld(w, ps, pc.c, {'%s = %s' % (PDF2, PDF2): eq}))
    Ca, Da, n = triple_parts(cc)
    fle = w.s([w.s([pc.fn], 'nn0red', '( %s -> F e. RR )' % ps)], 'leidd', '( %s -> F <_ F )' % ps)
    pvF, SF, _ = pc.pv('F', pc.fn, fle)
    ff = w.s([cl.mem('F', 'CC')], 'subidd', '( %s -> ( F - F ) = 0 )' % ps)
    efe = w.s([w.s([ff], 'fveq2d', '( %s -> ( encNatGam ` ( F - F ) ) = ( encNatGam ` 0 ) )' % ps)], 'oveq1d',
              '( %s -> %s = %s )' % (ps, EW('( F - F )', 'X'), EW('0', 'X')))
    r1, x1 = w.rewrite(PB2('F'), {EW('( F - F )', 'X'): (EW('0', 'X'), efe)}, ps)
    DJY = UP('D', 'J', YV('F'))
    z0 = closed(w, ps, '0nn0', '0 e. NN0')
    xg = pc.c[WRD('X', GAM)]
    e0g = ewg(w, ps, '0', z0, 'X', xg)
    yfg = pc.yw('F', pc.fn)
    togk = lambda X, s_, g: w.s([g, pc.mk['k'][s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s_)))
    kK, kJ = pc.mk['k']['K'], pc.mk['k']['J']
    dd = pc.c[STKD('D')]
    sw = upc(w, ps, 'D', 'K', EW('0', 'X'), 'J', YV('F'), pc.mk['tv'], dd, pc.ne('K', 'J'), kK['kd'], togk(EW('0', 'X'), 'K', e0g),
             kJ['kd'], togk(YV('F'), 'J', yfg))
    PRE = UP(DJY, 'K', EW('0', 'X'))
    pF = w.s([w.s([pvF, r1], 'eqtrd', '( %s -> ( %s ` F ) = %s )' % (ps, PDF2, x1)), sw], 'eqtrd', '( %s -> ( %s ` F ) = %s )' % (ps, PDF2, PRE))
    NFF = '( %s ` F )' % N2F
    d1 = clneq(w, ps, LMP['X0'], NFF, pF, '( %s ` F )' % PDF2, PRE)
    t1, C1, D1, n1 = hrrw(w, ps, t, Ca, Da, n, deq=d1)
    # dropNum x
    djy = updcl(w, ps, 'D', 'J', YV('F'), pc.mk['tv'], dd, kJ['kd'], togk(YV('F'), 'J', yfg))
    ew0 = w.s([z0, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ps)
    e00 = w.s([closed(w, ps, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ps)
    co0 = closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')
    eg0 = w.s([w.s([ew0, e00], 'eqtrd', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. (/) ) )' % ps), co0], 'eqtrd', '( %s -> ( encNatGam ` 0 ) = (/) )' % ps)
    wb = w.s([eg0, closed(w, ps, 'wrd0', '(/) e. Word %s' % BITS)], 'eqeltrd', '( %s -> ( encNatGam ` 0 ) e. Word %s )' % (ps, BITS))
    ex = dict(pc.base)
    ex.update({STKD(DJY): djy, WRD(ENG('0'), BITS): wb, WRD('X', GAM): xg})
    t2, c2 = inst(w, ps, 'tmidrop', {'K': 'K', 'W': ENG('0'), 'X': 'X', 'P': PL('P', 7), 'E': 'E', 'D': DJY}, Bld(w, ps, pc.c, ex))
    C2, D2, n2 = triple_parts(c2)
    fam_ss = pc.famss('F', pc.fn)
    t2b = hrssc(w, ps, pc.mk['phm'], t2, C2, D2, n2, CLN(LMP['X0'], NFF, PRE), clnss(w, ps, LMP['X0'], NFF, SS, PRE, fam_ss))
    t12 = hrseq(w, ps, pc.mk['phm'], t1, t2b, C1, D1, D2, n1, n2)
    # the final stacks
    FIN = UP(DJY, 'K', 'X')
    assert D2 == CLN('E', SS, FIN), D2
    sw2 = upc(w, ps, 'D', 'J', YV('F'), 'K', 'X', pc.mk['tv'], dd, pc.ne('J', 'K'), kJ['kd'], togk(YV('F'), 'J', yfg), kK['kd'], togk('X', 'K', xg))
    dj = w.s([stkfv(w, ps, 'D', 'J', pc.mk['tv'], dd, kJ['kd']), kJ['wge']], 'eleqtrd', "( %s -> ( D ` J ) e. Word Gamma' )" % ps)
    zg = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, Z0))
    bg = w.s([closed(w, ps, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, B1))
    rwF = w.s([zg, pc.fn, w.inst('repsw')], 'syl2anc', "( %s -> ( %s repeatS F ) e. Word Gamma' )" % (ps, Z0))
    b1w = w.s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, B1))
    ca = w.s([rwF, b1w, wg4(w, ps, '( D ` J )', dj), w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( ( %s repeatS F ) ++ <" %s "> ) ++ %s ) = %s )' % (ps, Z0, B1, YX('( D ` J )'), YV('F')))
    en = w.s([pc.fn, w.inst('tmip2enc')], 'syl', '( %s -> ( encNatGam ` ( 2 ^ F ) ) = ( ( %s repeatS F ) ++ <" %s "> ) )' % (ps, Z0, B1))
    yv = w.s([w.s([en], 'oveq1d', '( %s -> %s = ( ( ( %s repeatS F ) ++ <" %s "> ) ++ %s ) )' % (ps, EW('( 2 ^ F )', '( D ` J )'), Z0, B1, YX('( D ` J )'))), ca],
             'eqtrd', '( %s -> %s = %s )' % (ps, EW('( 2 ^ F )', '( D ` J )'), YV('F')))
    r2, x2 = w.rewrite(UP(UP('D', 'K', 'X'), 'J', YV('F')), {YV('F'): (EW('( 2 ^ F )', '( D ` J )'), w.s([yv], 'eqcomd', '( %s -> %s = %s )' % (ps, YV('F'), EW('( 2 ^ F )', '( D ` J )'))))}, ps)
    assert x2 == DFIN, x2
    fin = w.s([sw2, r2], 'eqtrd', '( %s -> %s = %s )' % (ps, FIN, DFIN))
    d2 = clneq(w, ps, 'E', SS, fin, FIN, DFIN)
    # the bound ( # ` ( encNatGam ` 0 ) ) = 0
    h0 = w.s([w.s([eg0], 'fveq2d', '( %s -> ( # ` ( encNatGam ` 0 ) ) = ( # ` (/) ) )' % ps), closed(w, ps, 'hash0', '( # ` (/) ) = 0')], 'eqtrd',
             '( %s -> ( # ` ( encNatGam ` 0 ) ) = 0 )' % ps)
    NT = '( %s + %s )' % (n1, n2)
    efn = w.s([w.s([pc.fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF)), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, ENCF))
    cl.leaf('( # ` %s )' % ENCF, 'NN0', efn)
    cl.leaf('( # ` ( encNatGam ` 0 ) )', 'NN0', w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` ( encNatGam ` 0 ) ) e. NN0 )' % ps))
    neq = lineq(w, ps, NT, BNDC, hyps=[h0], closure=cl, products=True, atoms=['( # ` %s )' % ENCF, 'F', '( # ` ( encNatGam ` 0 ) )'])
    hrrw(w, ps, t12, C1, D2, NT, deq=d2, neq=neq, qed=True)
    return w.run()


T_B = ((T_PHM7, P2F.pred()), (idx_tree(K4), dist_tree(K4)),
       ((('F e. NN0', 'N e. NN0', 'F < N'), (WRD('X', GAM), STKD('D'))), '( D ` K ) = %s' % EW('F', 'X')))
CONCL_B = TRI(CLN(LMP['A'], SS, 'D'), CLN('E', SS, DFIN), '( TMB ` N )')


def tmip2b():
    lab = 'tmip2b'
    ps = cj(T_B)
    C = '( %s -> %s )' % (ps, CONCL_B)
    w = W(lab, 'Lean\'s ` pow2_le_B ` at the machine: ` pow2 x y s s\' ` with the exponent ` e < b ` on ` x ` runs '
               'within ` B b ` steps (~ tmip2c ).')
    c = Ctx(w, ps, T_B)
    phm = c[PHM]
    t, cc = inst(w, ps, 'tmip2c', {}, Bld(w, ps, c, {}))
    Ca, Da, n = triple_parts(cc)
    fn, nn = c['F e. NN0'], c['N e. NN0']
    cl = Closure(w, ps, {'F': ('NN0', fn), 'N': ('NN0', nn)})
    L = '( # ` %s )' % ENCF
    efw = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF))
    cl.leaf(L, 'NN0', w.s([efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, L)))
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    np_ = w.s([w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ps), nn, w.inst('bernneq3')], 'syl2anc', '( %s -> N < ( 2 ^ N ) )' % ps)
    cl.atom('( 2 ^ N )')
    flt = linarith(w, ps, [c['F < N'], np_], 'F < ( 2 ^ N )', closure=cl, atoms=['( 2 ^ N )'])
    ln = w.s([fn, nn, flt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ps, L))
    fle = w.s([c['F < N']], 'ltled', '( %s -> F <_ N )' % ps)
    Q = '( 4 x. ( ( N + 2 ) ^ 2 ) )'
    le1 = nlinarith(w, ps, [ln, fle, cl.ge0('F'), cl.ge0(L), cl.ge0('N')], '%s <_ %s' % (n, Q), closure=cl, atoms=['F', L, 'N'])
    four = closed(w, ps, '4nn0', '4 e. NN0')
    le4 = w.s([closed(w, ps, '4re', '4 e. RR'), closed(w, ps, '6nn0' if False else '4re', '') if False else None], '', '') if False else None
    import num
    l64 = w.s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ps)
    qd = w.s([nn, four, l64, w.inst('tmbquad')], 'syl3anc', '( %s -> %s <_ ( TMB ` N ) )' % (ps, Q))
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ps)], 'nnnn0d', '( %s -> ( TMB ` N ) e. NN0 )' % ps)
    cl.leaf('( TMB ` N )', 'NN0', tbn)
    le = w.s([le1, qd, w.s([cl.mem(n, 'RR'), cl.mem(Q, 'RR'), cl.mem('( TMB ` N )', 'RR')], '3jca', '') if False else None], '', '') if False else None
    le = w.s([cl.mem(n, 'RR'), cl.mem(Q, 'RR'), cl.mem('( TMB ` N )', 'RR'), le1, qd], 'letrd' if False else 'letrd', '') if False else None
    le = w.s([le1, qd], 'letrd', '( %s -> %s <_ ( TMB ` N ) )' % (ps, n))
    hrle(w, ps, phm, t, Ca, Da, n, '( TMB ` N )', tbn, le, qed=True)
    return w.run()


STMTS = {'tmip2enc': ST_ENC}
STMTS['tmip2b'] = '( %s -> %s )' % (cj(T_B), CONCL_B)
STMTS['tmip2c'] = '( %s -> %s )' % (cj(T_C), CONCL_C)
STMTS['tmip2l'] = '( %s -> %s )' % (PHP, CONCL_L)
STMTS['tmip2t'] = '( %s -> ( %s /\\ %s /\\ %s ) )' % (PHP, LTYP, LEXIT, PROT)
STMTS['tmip2i'] = '( %s -> %s )' % (PSIP, LBODY)

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
