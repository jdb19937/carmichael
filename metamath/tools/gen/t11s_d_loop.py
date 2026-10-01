"""T11 helper (scan): the scan loop ` loop carry scanBody ` of ` scanF ` at the machine (Steps23.lean ` SCInv ` ,
` scanBody_runs ` ), ~ tm2floop at the families ` N' ` (class), ` P' ` (stacks), ` U' ` (charge), the letters
bound by equations in the antecedent (t11s_b_defs.py for the scan texts).

  tmiscca   the body at ` k ` not coprime: ` coprimeToF ` (~ tmicptb ), the branch, ` scanNext ` (~ tmiscn )
  tmisccb   the body at ` k ` coprime, pool below ` theta ` : ... ` scanTest ` (~ tmisct ), ` dropListQ 6 ` (~ tmidpl ), ` scanNext `
  tmisccc   the body at a success: ... ` scanTest ` , ` load' ( carry := false , flag := true ) `
  tmiscia   one iteration at the families, ` k + i ` not coprime (~ tmiscca at ` k + i ` )
  tmiscib   ... coprime, pool below ` theta ` (~ tmisccb )
  tmiscic   the successful iteration (~ tmisccc )
  tmiscfi   one iteration (the three cases)
  tmiscft   the frame: the families' typings, the carry clear at ` R `
  tmiscfl   ~ tm2floop at the families

    MM_DB=sorties/t11.mm MM_HEAP=16g python3 tools/gen/t11s_d_loop.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t7lib import famval, fam_unpack, mval, rab_in, not1o
from t7b_h_dmq import rab_elim
from t10_e_doa import lift_from
from t10_u_s2s import me_bound_n
from t11p_d_plf import cmp_test, cty, pw2mono, tbn
import t8alib as A8
import t6blib
import num
from t11s_b_defs import *
import t11s_c_arith as CA
import t11s_f_ub as UBL
t6blib._STMT.update(CA.STMTS)
t6blib._STMT.update(UBL.STMTS)

SEL = sys.argv[1:]
UO = os.environ.get('T11S_UO') == '1'

MS = MS_
UU = '( TMB ` %s )' % MS
K64 = '( ; 6 4 x. %s )' % UU
TBB = '( TMB ` B )'
CB = '( C + B )'
M2 = '( ( 2 x. %s ) + 2 )' % CB
T2 = '( TMB ` %s )' % M2
COND = lambda h, j: '( ( TMcar ` %s ) = if ( %s = R , (/) , 1o ) /\\ ( TMfl ` %s ) = if ( %s , 1o , (/) ) )' % (h, j, h, SJ(j))
NCL = lambda j: '{ h e. TMSt | %s }' % COND('h', j)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
FU = lambda j: 'if ( %s , ( %s + 1 ) , %s )' % (SJ(j), HI(j), HI(j))
KG = lambda j: 'if ( %s , ( %s - 1 ) , %s )' % (SJ(j), GI(j), GI(j))
D6 = '( D ` 6 )'
S6 = lambda j: 'if ( %s , %s , %s )' % (SJ(j), ENCL(PFS, D6), D6)
E1 = lambda x: EWg('Z', EWg(x, "X'"))
E2 = lambda x: EWg(x, 'Y')
PB = lambda j: UPS('D', ('1', E1(FU(j))), ('2', E2(KG(j))), ('6', S6(j)))
PFM = '( j e. NN0 |-> %s )' % PB('j')
J1 = lambda j: '( %s + 1 )' % j
UB = lambda j: '( ( ( %s x. %s ) - ( %s x. %s ) ) - 1 )' % (K64, VN(j), K64, VN(J1(j)))
UFM = '( j e. NN0 |-> %s )' % UB('j')
NV, PV, UV = "N'", "P'", "U'"
PSI_T = (TREE_SCF, (REQ, ('%s = %s' % (NV, NFM), '%s = %s' % (PV, PFM), '%s = %s' % (UV, UFM))))
PSI = cj(PSI_T)
LMF = FRAGS['scf'].lmap()
PSB = PL('P', FRAGS['scf'].slot(3))
LSB = FRAGS['scb'].lmap(PSB, LMF['Z2'])
PCH = lambda j: PL(PSB, FRAGS['scb'].slot(j))
GM = {'A': LMF['Z2'], 'B0': LMF['Y4'], 'E': LMF['Y5'], 'C0': 'TMcar', 'R': 'R', 'N': NV, 'P': PV, 'U': UV}
_LA, _LC = split_imp(stmt('tm2floop'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
_pre = 'A. i e. ( 0 ..^ R ) '
assert LPER.startswith(_pre)
LBODY = LPER[len(_pre):]
_lb = parse_conj(LBODY)
TRI_I = cj(_lb[1])
UI = '( %s ` i )' % UV
CONC_C = '( %s e. NN0 /\\ %s )' % (UI, TRI_I)
TI_ = (PSI_T, IFZ)
CASES = {'tmiscia': (TI_, '-. %s' % CPc(GI('i'))),
         'tmiscib': ((TI_, CPc(GI('i'))), '-. %s' % OLE(GI('i'))),
         'tmiscic': ((TI_, CPc(GI('i'))), OLE(GI('i')))}
for _l, _t in CASES.items():
    add11(_l, _t, CONC_C)
add11('tmiscfi', TI_, LBODY)
add11('tmiscft', PSI_T, '( %s /\\ %s )' % (LTYP, LEXIT))
add11('tmiscfl', PSI_T, LCONCL)
for _l in ('tmiscia', 'tmiscib', 'tmiscic', 'tmiscfi', 'tmiscft', 'tmiscfl'):
    ORDER11.remove(_l)
    ORDER11.insert(ORDER11.index('tmiscfb'), _l)
STMTS_D = {l: STMTS11[l] for l in ('tmiscia', 'tmiscib', 'tmiscic', 'tmiscfi', 'tmiscft', 'tmiscfl')}

if __name__ == '__main__' and 'show' in SEL:
    for _l in STMTS_D:
        print(_l, len(STMTS_D[_l].split()))
    print(LBODY)


class Wrap:
    """a Ctx with the arithmetic context AT (and ( AT /\\ IFZ )) available as steps"""
    def __init__(self, c, extra):
        self.c, self.extra = c, extra

    def __getitem__(self, k):
        if k in self.extra:
            return self.extra[k]
        return self.c[k]


def entry_unfold(B, fname, ks, P_, E_):
    """unfold the predicate fname at ( P_ , E_ ) one level, and so on down its entry callee"""
    f = FRAGS[fname]
    pr = f.pred(ks, 'T', 'M', P_, E_)
    B.ex.update(unfold_all(B.w, B.ph, B.ex[pr], fname, ks, P_, E_, rec=False))
    start = getattr(f, 'start', None) or (f.labels[0] if f.labels else f.children[0][2])
    if start in f.labels:
        return
    j = [k for k, ch in enumerate(f.children) if ch[2] == start][0]
    fn, cks, en, exn = f.children[j]
    m = f.at(ks, P_, E_)
    lm = f.lmap(P_, E_)
    entry_unfold(B, fn, [m.get(k, k) for k in cks], PL(P_, f.slot(j)), lm[exn])


def rab_h_eq(w, ph, A, psf, chf, bi_at, x='h', y='g'):
    """( ph -> { x e. A | psf( x ) } = { x e. A | chf( x ) } ) for an antecedent in which x occurs (~ rabbidva forbids it):
    through the fresh y (~ cbvrabv ); bi_at( pp , t ) : ( pp -> ( psf( t ) <-> chf( t ) ) ) under pp = ( ph /\\ t e. A )"""
    s = w.s
    RB = lambda v, f: '{ %s e. %s | %s }' % (v, A, f(v))
    ex = s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))
    c1, n1 = w.wcongr(psf(x), {x: y}, '%s = %s' % (x, y), {x: ex})
    assert n1 == psf(y), (n1, psf(y))
    cb1 = s([c1], 'cbvrabv', '%s = %s' % (RB(x, psf), RB(y, psf)))
    pp = '( %s /\\ %s e. %s )' % (ph, y, A)
    mid = s([bi_at(pp, y)], 'rabbidva', '( %s -> %s = %s )' % (ph, RB(y, psf), RB(y, chf)))
    ey = s([], 'id', '( %s = %s -> %s = %s )' % (y, x, y, x))
    c2, n2 = w.wcongr(chf(y), {y: x}, '%s = %s' % (y, x), {y: ey})
    assert n2 == chf(x), (n2, chf(x))
    cb2 = s([c2], 'cbvrabv', '%s = %s' % (RB(y, chf), RB(x, chf)))
    a = s([s([cb1], 'a1i', '( %s -> %s = %s )' % (ph, RB(x, psf), RB(y, psf))), mid], 'eqtrd', '( %s -> %s = %s )' % (ph, RB(x, psf), RB(y, chf)))
    return s([a, s([cb2], 'a1i', '( %s -> %s = %s )' % (ph, RB(y, chf), RB(x, chf)))], 'eqtrd', '( %s -> %s = %s )' % (ph, RB(x, psf), RB(x, chf)))


def rab_h_ss(w, ph, A, psf, chf, im_at, x='h', y='g'):
    """( ph -> { x e. A | psf( x ) } C_ { x e. A | chf( x ) } ) likewise (~ ss2rabdv through the fresh y);
    im_at( pp , t ) : ( pp -> ( psf( t ) -> chf( t ) ) )"""
    s = w.s
    RB = lambda v, f: '{ %s e. %s | %s }' % (v, A, f(v))
    ex = s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))
    c1, n1 = w.wcongr(psf(x), {x: y}, '%s = %s' % (x, y), {x: ex})
    assert n1 == psf(y), (n1, psf(y))
    cb1 = s([c1], 'cbvrabv', '%s = %s' % (RB(x, psf), RB(y, psf)))
    pp = '( %s /\\ %s e. %s )' % (ph, y, A)
    mid = s([im_at(pp, y)], 'ss2rabdv', '( %s -> %s C_ %s )' % (ph, RB(y, psf), RB(y, chf)))
    ey = s([], 'id', '( %s = %s -> %s = %s )' % (y, x, y, x))
    c2, n2 = w.wcongr(chf(y), {y: x}, '%s = %s' % (y, x), {y: ey})
    assert n2 == chf(x), (n2, chf(x))
    cb2 = s([c2], 'cbvrabv', '%s = %s' % (RB(y, chf), RB(x, chf)))
    a = s([s([cb1], 'a1i', '( %s -> %s = %s )' % (ph, RB(x, psf), RB(y, psf))), mid], 'eqsstrd', '( %s -> %s C_ %s )' % (ph, RB(x, psf), RB(y, chf)))
    return s([a, s([cb2], 'a1i', '( %s -> %s = %s )' % (ph, RB(y, chf), RB(x, chf)))], 'sseqtrd', '( %s -> %s C_ %s )' % (ph, RB(x, psf), RB(x, chf)))


class Sf(Base):
    """the facts under an antecedent containing the scf tree and AT's letters"""
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        s = w.s
        fn, zn, on, gn, hn = c0['F e. NN0'], c0['Z e. NN0'], c0['O e. NN0'], c0['G e. NN0'], c0['H e. NN0']
        ww, bn, cn = c0['W e. Word NN0'], c0['B e. NN0'], c0['C e. NN0']
        xw, x2w, yw, y2w = c0[WG('X')], c0[WG("X'")], c0[WG('Y')], c0[WG("Y'")]
        EOX, EHX = EWg('O', 'X'), EWg('H', "X'")
        eox, ehx = ewg_(w, ph, 'O', on, 'X', xw), ewg_(w, ph, 'H', hn, "X'", x2w)
        eqs = {'0': (EWg('F', EOX), ewg_(w, ph, 'F', fn, EOX, eox)), '1': (EWg('Z', EHX), ewg_(w, ph, 'Z', zn, EHX, ehx)),
               '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', yw)), '4': (ENCL('W', "Y'"), enclg(w, ph, 'W', ww, "Y'", y2w))}
        Base.__init__(self, w, ph, T, N8, 'scf', eqs)
        self.g(EOX, eox)
        self.fn, self.zn, self.on, self.gn, self.hn, self.ww, self.bn, self.cn = fn, zn, on, gn, hn, ww, bn, cn
        self.xw, self.x2w, self.yw, self.y2w = xw, x2w, yw, y2w
        self.at = Bld(w, ph, self.c, {})(AT)
        self.r0 = CA.r0facts(w, ph, self.at)
        self.rn = self.r0['R e. NN0']
        self.rle = self.r0['R <_ H']
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
        cl = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn), 'G': ('NN0', gn), 'H': ('NN0', hn), 'R': ('NN0', self.rn)})
        cl.leaf('( # ` W )', 'NN0', self.nw)
        self.cl = cl
        self.msn = cl.mem(MS, 'NN0')
        cl.leaf(UU, 'NN0', tbn(w, ph, MS, self.msn))
        self.uu1 = s([s([self.msn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, UU)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, UU))
        self.pvs, self.nvs = {}, {}

    # ---------------- the arithmetic context
    def atc(self, extra=None):
        d = {cj(AT): self.at}
        d.update(extra or {})
        return Wrap(self.c, d)

    def jn(self, t, tn, tle):
        """facts at t ( tn : t e. NN0 , tle : t <_ R ): H - t e. NN0 , G + t e. NN0 (memoised)"""
        w, ph, s = self.w, self.ph, self.w.s
        if not hasattr(self, 'jns'):
            self.jns = {}
        if t in self.jns:
            return self.jns[t]
        rr = lambda st, x: s([st], 'nn0red', '( %s -> %s e. RR )' % (ph, x))
        th = s([rr(tn, t), rr(self.rn, 'R'), rr(self.hn, 'H'), tle, self.rle], 'letrd', '( %s -> %s <_ H )' % (ph, t))
        htn = s([tn, self.hn, th, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, HI(t)))
        gtn = s([self.gn, tn], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, GI(t)))
        self.jns[t] = (htn, gtn)
        return htn, gtn

    def pbst(self, t, tn, tle):
        """the Stacks of PB( t ) (memoised)"""
        w, ph, s = self.w, self.ph, self.w.s
        if not hasattr(self, 'pbs'):
            self.pbs = {}
        if t in self.pbs:
            return self.pbs[t]
        self.pbs[t] = self._pbst(t, tn, tle)
        return self.pbs[t]

    def _pbst(self, t, tn, tle):
        w, ph, s = self.w, self.ph, self.w.s
        htn, gtn = self.jn(t, tn, tle)
        fun = s([s([htn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, HI(t))), htn], 'ifcld',
                '( %s -> %s e. NN0 )' % (ph, FU(t)))
        # KG( t ) : under SJ( t ) , t = R >_ 1
        pa = '( %s /\\ %s )' % (ph, SJ(t))
        L = lambda st: lift_from(w, ph, pa, st)
        sj = s([], 'simpr', '( %s -> %s )' % (pa, SJ(t)))
        te = s([sj], 'simpld', '( %s -> %s = R )' % (pa, t))
        nn = s([sj], 'simprd', '( %s -> -. %s )' % (pa, NONE))
        r1 = s([s([nn, L(self.r0['( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (NONE, KF)])], 'mpd',
                  '( %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (pa, KF))], 'simpld', '( %s -> 1 <_ R )' % pa)
        cla = Closure(w, pa, {'G': ('NN0', L(self.gn)), 'R': ('NN0', L(self.rn))})
        cla.leaf(t, 'NN0', L(tn))
        t1 = s([r1, te], 'breqtrrd', '( %s -> 1 <_ %s )' % (pa, t))
        tg = s([s([cla.mem(t, 'RR'), cla.mem('G', 'RR')], 'addge02d', '( %s -> ( 0 <_ G <-> %s <_ %s ) )' % (pa, t, GI(t))), cla.ge0('G')],
               'mpbird' if False else 'mpbid', '( %s -> %s <_ %s )' % (pa, t, GI(t)))
        g1 = s([closed(w, pa, '1re', '1 e. RR'), cla.mem(t, 'RR'), cla.mem(GI(t), 'RR'), t1, tg], 'letrd', '( %s -> 1 <_ %s )' % (pa, GI(t)))
        ga = s([closed(w, pa, '1nn0', '1 e. NN0'), L(gtn), g1, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( %s - 1 ) e. NN0 )' % (pa, GI(t)))
        gb = lift_from(w, ph, '( %s /\\ -. %s )' % (ph, SJ(t)), gtn)
        kgn = s([ga, gb], 'ifclda', '( %s -> %s e. NN0 )' % (ph, KG(t)))
        # S6( t )
        dj = s([s([CA.base4(w, pa, [L(self.ww), L(self.fn), L(self.zn), L(self.on)], '( G e. NN0 /\\ H e. NN0 )',
                               s([L(self.gn), L(self.hn)], 'jca', '( %s -> ( G e. NN0 /\\ H e. NN0 ) )' % pa)),
                   s([nn], 'neqned', '( %s -> %s )' % (pa, SOMEne))], 'jca',
                  '( %s -> ( ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( G e. NN0 /\\ H e. NN0 ) ) /\\ %s ) )' % (pa, SOMEne)),
                w.inst('scandj')], 'syl', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (pa, KF, PFS))
        pfw = s([dj], 'simprd', '( %s -> %s e. Word NN0 )' % (pa, PFS))
        d6 = self.S0.vals['6'][2]
        sa = enclg(w, pa, PFS, pfw, D6, L(d6))
        s6g = s([sa, lift_from(w, ph, '( %s /\\ -. %s )' % (ph, SJ(t)), d6)], 'ifclda', "( %s -> %s e. Word Gamma' )" % (ph, S6(t)))
        x2w = self.x2w
        g1_ = self.g(E1(FU(t)), ewg_(w, ph, 'Z', self.zn, EWg(FU(t), "X'"), ewg_(w, ph, FU(t), fun, "X'", x2w)))
        g2_ = self.g(E2(KG(t)), ewg_(w, ph, KG(t), kgn, 'Y', self.yw))
        self.g(S6(t), s6g)
        return self.S0.upd('1', E1(FU(t)), g1_).upd('2', E2(KG(t)), g2_).upd('6', S6(t), s6g)

    def pv(self, t, tn, tle):
        """(( ph -> ( P' ` t ) = PB( t ) ), Stacks)"""
        if t not in self.pvs:
            fam = self.c['%s = %s' % (PV, PFM)]
            self.pvs[t] = fam_at(self.w, self.ph, self.mk, self.ne, fam, PV, 'j', 'NN0', PB, t, tn, self.pbst(t, tn, tle))
        return self.pvs[t]

    def nv(self, t, tn):
        """( ph -> ( N' ` t ) = NCL( t ) )"""
        w, ph, s = self.w, self.ph, self.w.s
        if t not in self.nvs:
            fam = self.c['%s = %s' % (NV, NFM)]
            e = s([fam], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, NV, t, NFM, t))
            self.nvs[t] = s([e, famval(w, ph, COND, t, tn)], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, NV, t, NCL(t)))
        return self.nvs[t]

    def nvss(self, t, tn):
        w, ph, s = self.w, self.ph, self.w.s
        return s([self.nv(t, tn), self.ss(NCL(t))], 'eqsstrd', '( %s -> ( %s ` %s ) C_ %s )' % (ph, NV, t, S))

    def uv(self, t, tn):
        """( ph -> ( U' ` t ) = UB( t ) )"""
        w, ph, s = self.w, self.ph, self.w.s
        fam = self.c['%s = %s' % (UV, UFM)]
        e = s([fam], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, UV, t, UFM, t))
        return s([e, mval(w, ph, 'j', 'NN0', UB, t, tn, s([s([], 'ovex', '%s e. _V' % UB(t))], 'a1i', '( %s -> %s e. _V )' % (ph, UB(t))))],
                 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, UV, t, UB(t)))

    def vnn(self, t, tn, tle):
        """( ph -> VN( t ) e. NN0 )"""
        w, ph, s = self.w, self.ph, self.w.s
        htn, gtn = self.jn(t, tn, tle)
        b = CA.base4(w, ph, [self.ww, self.fn, self.zn, self.on], '%s e. NN0' % GI(t), gtn)
        sc = s([s([b, htn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (ph, concl(w, ph, b), HI(t))), w.inst('scancl')], 'syl',
               '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, SCf(GI(t), HI(t))))
        v = s([sc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, Vf(t)))
        return s([closed(w, ph, '0nn0', '0 e. NN0'), v], 'ifcld', '( %s -> %s e. NN0 )' % (ph, VN(t)))


def pnr(w, ph, E, en):
    """( ph -> ( 2 ^ E ) e. RR )"""
    return w.s([w.s([closed(w, ph, '2nn', '2 e. NN'), en, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, E))], 'nnred',
               '( %s -> ( 2 ^ %s ) e. RR )' % (ph, E))


def ralb_mono(w, ph, Wd, wdw, M, mn, N, nn_, le, ral):
    """( ph -> A. a e. ran Wd a < ( 2 ^ N ) ) from ral : ( ph -> A. a e. ran Wd a < ( 2 ^ M ) ) and le : ( 2 ^ M ) <_ ( 2 ^ N )"""
    s = w.s
    PM, PN = '( 2 ^ %s )' % M, '( 2 ^ %s )' % N
    pa = '( %s /\\ p e. ran %s )' % (ph, Wd)
    L = lambda st: lift_from(w, ph, pa, st)
    pin = s([], 'simpr', '( %s -> p e. ran %s )' % (pa, Wd))
    plt = s([s([], 'breq1', '( a = p -> ( a < %s <-> p < %s ) )' % (PM, PM)), pin, L(ral)], 'rspcdva', '( %s -> p < %s )' % (pa, PM))
    pr = s([s([s([s([L(wdw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, Wd, Wd)), w.inst('frn')], 'syl',
                 '( %s -> ran %s C_ NN0 )' % (pa, Wd)), pin], 'sseldd', '( %s -> p e. NN0 )' % pa)], 'nn0red', '( %s -> p e. RR )' % pa)
    pl = s([pr, pnr(w, pa, M, L(mn)), pnr(w, pa, N, L(nn_)), plt, L(le)], 'ltletrd', '( %s -> p < %s )' % (pa, PN))
    rp = s([pl], 'ralrimiva', '( %s -> A. p e. ran %s p < %s )' % (ph, Wd, PN))
    return s([rp, s([s([], 'breq1', '( p = a -> ( p < %s <-> a < %s ) )' % (PN, PN))], 'cbvralvw',
                    '( A. p e. ran %s p < %s <-> A. a e. ran %s a < %s )' % (Wd, PN, Wd, PN))], 'sylib',
             '( %s -> A. a e. ran %s a < %s )' % (ph, Wd, PN))


def pool_at(w, ph, B, k, kn):
    """the pool at k: PA1 e. Word NN0 , ( ph -> A. a e. ran PA1 a < ( 2 ^ B ) ) , LEN <_ CPA , CPA e. NN0"""
    s = w.s
    fn, zn, ww = B.fn, B.zn, B.ww
    DV_ = '( DivisorsOf ` W )'
    DV1, DV2 = '( 1st ` %s )' % DV_, '( 2nd ` %s )' % DV_
    PG = '( ( ( F PoolGo Z ) ` %s ) ` %s )' % (k, DV1)
    PGD, PG2 = '( 1st ` %s )' % PG, '( 2nd ` %s )' % PG
    dvc = s([ww, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, DV_))
    dv1w = s([dvc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DV1))
    dv2n = s([dvc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, DV2))
    FZK = '( ( F e. NN0 /\\ Z e. NN0 ) /\\ %s e. NN0 )' % k
    fzk = s([s([fn, zn], 'jca', '( %s -> ( F e. NN0 /\\ Z e. NN0 ) )' % ph), kn], 'jca', '( %s -> %s )' % (ph, FZK))
    fzkd = s([fzk, dv1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (ph, FZK, DV1))
    pgc = s([fzkd, w.inst('poolgocl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, PG))
    pgw = s([pgc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PGD))
    p2n = s([pgc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, PG2))
    pav = s([s([s([s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph), zn], 'jca',
                  '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % ph),
               kn], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ %s e. NN0 ) )' % (ph, k)), w.inst('poolalgval')], 'syl',
            '( %s -> %s = <. %s , ( %s + %s ) >. )' % (ph, PA(k), PGD, DV2, PG2))
    SS = '( %s + %s )' % (DV2, PG2)
    ssn = s([dv2n, p2n], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, SS))
    a1 = s([s([pav], 'fveq2d', '( %s -> %s = ( 1st ` <. %s , %s >. ) )' % (ph, PA1(k), PGD, SS)),
            s([pgw, ssn, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, PGD, SS, PGD))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, PA1(k), PGD))
    a2 = s([s([pav], 'fveq2d', '( %s -> %s = ( 2nd ` <. %s , %s >. ) )' % (ph, CPA(k), PGD, SS)),
            s([pgw, ssn, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, PGD, SS, SS))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, CPA(k), SS))
    paw = s([a1, pgw], 'eqeltrd', '( %s -> %s e. Word NN0 )' % (ph, PA1(k)))
    can = s([a2, ssn], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, CPA(k)))
    mem = s([fzkd, w.inst('tmpgmem')], 'syl', '( %s -> ( A. q e. ran %s ( q <_ F /\\ Z < q ) /\\ ( ( # ` %s ) <_ %s /\\ ( # ` %s ) <_ %s ) ) )'
            % (ph, PGD, PGD, PG2, DV1, PG2))
    ral = s([mem], 'simpld', '( %s -> A. q e. ran %s ( q <_ F /\\ Z < q ) )' % (ph, PGD))
    lpg = s([s([mem], 'simprd', '( %s -> ( ( # ` %s ) <_ %s /\\ ( # ` %s ) <_ %s ) )' % (ph, PGD, PG2, DV1, PG2))], 'simpld',
            '( %s -> ( # ` %s ) <_ %s )' % (ph, PGD, PG2))
    lpa = s([s([a1], 'fveq2d', '( %s -> %s = ( # ` %s ) )' % (ph, LENk(k), PGD)), lpg], 'eqbrtrd', '( %s -> %s <_ %s )' % (ph, LENk(k), PG2))
    cl = Closure(w, ph, {})
    for x_, st_ in ((LENk(k), s([paw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LENk(k)))), (PG2, p2n), (DV2, dv2n), (CPA(k), can)):
        cl.leaf(x_, 'NN0', st_)
    lca = linarith(w, ph, [lpa, a2, cl.ge0(DV2)], '%s <_ %s' % (LENk(k), CPA(k)), closure=cl)
    # entries <_ F < 2 ^ B
    pa = '( %s /\\ p e. ran %s )' % (ph, PA1(k))
    L = lambda st: lift_from(w, ph, pa, st)
    ain = s([s([], 'simpr', '( %s -> p e. ran %s )' % (pa, PA1(k))), s([L(a1)], 'rneqd', '( %s -> ran %s = ran %s )' % (pa, PA1(k), PGD))],
            'eleqtrd', '( %s -> p e. ran %s )' % (pa, PGD))
    qa = s([s([], 'breq1', '( q = p -> ( q <_ F <-> p <_ F ) )'), s([], 'breq2', '( q = p -> ( Z < q <-> Z < p ) )')], 'anbi12d',
           '( q = p -> ( ( q <_ F /\\ Z < q ) <-> ( p <_ F /\\ Z < p ) ) )')
    af = s([s([qa, ain, L(ral)], 'rspcdva', '( %s -> ( p <_ F /\\ Z < p ) )' % pa)], 'simpld', '( %s -> p <_ F )' % pa)
    pr = s([s([s([s([L(pgw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, PGD, PGD)), w.inst('frn')], 'syl',
                 '( %s -> ran %s C_ NN0 )' % (pa, PGD)), ain], 'sseldd', '( %s -> p e. NN0 )' % pa)], 'nn0red', '( %s -> p e. RR )' % pa)
    plt = s([pr, s([L(fn)], 'nn0red', '( %s -> F e. RR )' % pa), pnr(w, pa, 'B', L(B.bn)), af, L(B.c[LT2('F')])], 'lelttrd',
            '( %s -> p < ( 2 ^ B ) )' % pa)
    rp = s([plt], 'ralrimiva', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (ph, PA1(k)))
    ralb = s([rp, s([s([], 'breq1', '( p = a -> ( p < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
                    '( A. p e. ran %s p < ( 2 ^ B ) <-> A. a e. ran %s a < ( 2 ^ B ) )' % (PA1(k), PA1(k)))], 'sylib',
             '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (ph, PA1(k)))
    return dict(paw=paw, ralb=ralb, lca=lca, can=can, lenn=cl.mem(LENk(k), 'NN0'))


# ------------------------------------------------------------ the iteration cores (small antecedent: k = G , f = H)
ACPg, CPAg, LENg = ACP('G'), CPA('G'), LENk('G')
H1_ = '( H + 1 )'
G1_ = '( G + 1 )'
DATA_CORE = ((((STKD('D'), 'W e. Word NN0', ('F e. NN0', 'Z e. NN0', 'O e. NN0')), (('G e. NN0', 'H e. NN0'), ('C e. NN0', 'B e. NN0')),
               ((RALB('W', 'C'), 'A. a e. ran W 1 <_ a'), (LT2('F'), LT2('Z')), (LT2('O'), LT2(G1_), LT2(H1_)))),
              ((WG('X'), WG("X'")), (WG('Y'), WG("Y'"))),
              ((DEQ(0, EWg('F', EWg('O', 'X'))), DEQ(1, EWg('Z', EWg(H1_, "X'")))), (DEQ(2, EWg('G', 'Y')), DEQ(4, ENCL('W', "Y'"))))))
CCOND = {'a': '-. %s' % CPc('G'), 'b': (CPc('G'), '-. %s' % OLE('G')), 'c': (CPc('G'), OLE('G'))}
CORE_T = {k: (TREE0('scf', DATA_CORE), v) for k, v in CCOND.items()}
NCF = lambda f: '{ h e. TMSt | ( ( TMcar ` h ) = if ( %s = 0 , (/) , 1o ) /\\ ( TMfl ` h ) = (/) ) }' % f
NTT = '{ h e. TMSt | ( ( TMcar ` h ) = (/) /\\ ( TMfl ` h ) = 1o ) }'
CCOST = {'a': '( ( ( %s + 1 ) x. %s ) - 1 )' % (ACPg, K64), 'b': '( ( ( ( %s + %s ) + 1 ) x. %s ) - 1 )' % (ACPg, CPAg, K64)}
CCOST['c'] = CCOST['b']
DPOST_AB = UPS('D', ('1', E1('H')), ('2', E2(G1_)))
DPOST_C = UP('D', '6', ENCL(PA1('G'), D6))
CORE_C = {'a': TRI(CLN(LMF['Y4'], S, 'D'), CLN(LMF['Z2'], NCF('H'), DPOST_AB), CCOST['a']),
          'b': TRI(CLN(LMF['Y4'], S, 'D'), CLN(LMF['Z2'], NCF('H'), DPOST_AB), CCOST['b']),
          'c': TRI(CLN(LMF['Y4'], S, 'D'), CLN(LMF['Z2'], NTT, DPOST_C), CCOST['c'])}
for _k in 'abc':
    add11('tmiscc' + _k, CORE_T[_k], CORE_C[_k])
    ORDER11.remove('tmiscc' + _k)
    ORDER11.insert(ORDER11.index('tmiscia'), 'tmiscc' + _k)


class Cc(Base):
    """the facts under the core antecedent"""
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        fn, zn, on, gn, hn = c0['F e. NN0'], c0['Z e. NN0'], c0['O e. NN0'], c0['G e. NN0'], c0['H e. NN0']
        ww, bn, cn = c0['W e. Word NN0'], c0['B e. NN0'], c0['C e. NN0']
        xw, x2w, yw, y2w = c0[WG('X')], c0[WG("X'")], c0[WG('Y')], c0[WG("Y'")]
        EOX, EHX = EWg('O', 'X'), EWg(H1_, "X'")
        s = w.s
        h1n = s([hn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, H1_))
        eox, ehx = ewg_(w, ph, 'O', on, 'X', xw), ewg_(w, ph, H1_, h1n, "X'", x2w)
        eqs = {'0': (EWg('F', EOX), ewg_(w, ph, 'F', fn, EOX, eox)), '1': (EWg('Z', EHX), ewg_(w, ph, 'Z', zn, EHX, ehx)),
               '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', yw)), '4': (ENCL('W', "Y'"), enclg(w, ph, 'W', ww, "Y'", y2w))}
        Base.__init__(self, w, ph, T, N8, 'scf', eqs)
        self.g(EOX, eox)
        self.g(EHX, ehx)
        self.fn, self.zn, self.on, self.gn, self.hn, self.ww, self.bn, self.cn = fn, zn, on, gn, hn, ww, bn, cn
        self.xw, self.x2w, self.yw, self.y2w, self.h1n = xw, x2w, yw, y2w, h1n
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
        cl = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn), 'G': ('NN0', gn), 'H': ('NN0', hn)})
        cl.leaf('( # ` W )', 'NN0', self.nw)
        self.cl = cl
        self.msn = cl.mem(MS, 'NN0')
        cl.leaf(UU, 'NN0', tbn(w, ph, MS, self.msn))
        self.uu1 = s([s([self.msn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, UU)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, UU))


def core_proof(lab):
    kind = lab[-1]
    T = numtree11(CORE_T[kind])
    ph = cj(T)
    desc = {'a': '` k ` not coprime to ` Q ` : ` coprimeToF ` (~ tmicptb ) clears the flag and ` scanNext ` (~ tmiscn ) moves to '
                 '` k + 1 ` ',
            'b': '` k ` coprime, its pool shorter than ` theta ` : ` coprimeToF ` (~ tmicptb ), ` scanTest ` (~ tmisct ), ` dropListQ 6 ` '
                 '(~ tmidpl ) and ` scanNext ` (~ tmiscn )',
            'c': '` k ` a success: ` coprimeToF ` (~ tmicptb ), ` scanTest ` (~ tmisct ) and ` load\' ( carry := false , flag := true ) ` '
                 'leave the pool on 6'}[kind]
    w = W(lab, 'The body ` scanBody ` of Lean\'s ` scanF ` loop at the machine ( ` scanBody_runs ` ) at ` k ` with fuel ` f + 1 ` , '
               '%s, within ` ( a %s+ 1 ) 64 U - 1 ` steps ( ` U = B ( 12 ( # Q + 1 ) ( bq + b ) + # Q + 24 ) ` ).'
          % (desc, '' if kind == 'a' else '+ c '))
    s = w.s
    B = Cc(w, ph, T)
    c, mk = B.c, B.mk
    cl = B.cl
    for j in ((1, 2, 4) if kind != 'a' else (1, 4)):
        fn_, cks, en, exn = FRAGS['scb'].children[j]
        entry_unfold(B, fn_, cks, PCH(j), LSB[exn])
    P2B = '( 2 ^ B )'
    cl.atom(P2B)
    glt = linarith(w, ph, [c[LT2(G1_)]], 'G < %s' % P2B, closure=cl)
    ww = B.ww
    R = B.run()
    # 1. coprimeToF at N := C + B
    cbn = cl.mem(CB, 'NN0')
    le2 = pw2mono(w, ph, 'C', B.cn, CB, cbn, linarith(w, ph, [cl.ge0('B')], 'C <_ %s' % CB, closure=cl))
    rcb = ralb_mono(w, ph, 'W', ww, 'C', B.cn, CB, cbn, le2, c[RALB('W', 'C')])
    lb2 = pw2mono(w, ph, 'B', B.bn, CB, cbn, linarith(w, ph, [cl.ge0('C')], 'B <_ %s' % CB, closure=cl))
    P2CB = '( 2 ^ %s )' % CB
    cl.atom(P2CB)
    gcb = linarith(w, ph, [glt, lb2], 'G < %s' % P2CB, closure=cl)
    B.call(R, 'tmicptb', {'W': 'W', 'G': 'G', 'N': CB, 'X': "Y'", 'Y': 'Y', 'P': PCH(0), 'E': LSB['Z1']},
           {'%s e. NN0' % CB: cbn, RALB('W', CB): rcb, 'G < %s' % P2CB: gcb}, [])
    CC_ = '( 1st ` %s )' % CPT('G')
    N1 = NFL(CC_)
    pm = '( %s /\\ m e. %s )' % (ph, N1)
    mm, mf = A8.nfl_unpack(w, pm, CC_, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, N1)))
    if kind == 'a':
        ncp = c['-. %s' % CPc('G')]
        fne = s([mf, lift_from(w, ph, pm, s([ncp], 'neqned', '( %s -> %s =/= 1o )' % (ph, CC_)))], 'eqnetrd', '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
        nf = s([s([fne], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (ph, N1))
        B.call(R, 'tm2fbrg', {'A': LSB['Z1'], 'C': 'TMfl', 'E': LSB['Y5'], 'Q': GT(LSB['Y2']), 'N': N1},
               {STMT(GT(LSB['Y2'])): gotocl(w, ph, mk['tv'], LSB['Y2'], B.ex[LAB(LSB['Y2'])]), SSS(N1): B.ss(N1),
                'A. m e. %s -. ( TMfl ` m ) = 1o' % N1: nf}, [])
    else:
        cp = c[CPc('G')]
        f1 = s([mf, lift_from(w, ph, pm, cp)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
        B.call(R, 'tm2lbrt', {'A': LSB['Z1'], 'C': 'TMfl', 'E': LSB['Y2'], 'Q': GT(LSB['Y5']), 'N': N1},
               {STMT(GT(LSB['Y5'])): gotocl(w, ph, mk['tv'], LSB['Y5'], B.ex[LAB(LSB['Y5'])]), SSS(N1): B.ss(N1),
                'A. m e. %s ( TMfl ` m ) = 1o' % N1: s([f1], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ph, N1))}, [])
        pf = pool_at(w, ph, B, 'G', B.gn)
        E6 = ENCL(PA1('G'), D6)
        B.call(R, 'tmisct', {"X'": EWg(H1_, "X'"), 'P': PCH(1), 'E': LSB['Z2']}, {'G < %s' % P2B: glt},
               [('6', E6, B.g(E6, enclg(w, ph, PA1('G'), pf['paw'], D6, B.S0.vals['6'][2])))], pre=(N1, B.ss(N1)))
        N2 = CMPC('O', LENg)
        if kind == 'b':
            nle = c['-. %s' % OLE('G')]
            ngt, _ = cmp_test(w, ph, 'ngt', 'O', B.on, LENg, pf['lenn'], False, nle)
            B.call(R, 'tm2fbrg', {'A': LSB['Z2'], 'C': CNGT, 'E': LSB['Y3'], 'Q': GT(LSB['Z3']), 'N': N2},
                   {STMT(GT(LSB['Z3'])): gotocl(w, ph, mk['tv'], LSB['Z3'], B.ex[LAB(LSB['Z3'])]), SSS(N2): B.ss(N2),
                    'A. m e. %s -. ( %s ` m ) = 1o' % (N2, CNGT): ngt, CTY(CNGT): cty(w, ph, mk, CNGT)}, [])
            B.call(R, 'tmidpl', {'K': '6', 'L': PA1('G'), 'R': D6, 'B': 'B', 'P': PCH(2), 'E': LSB['Y4']},
                   {'%s e. Word NN0' % PA1('G'): pf['paw'], RALB(PA1('G')): pf['ralb']},
                   [('6', D6, B.S0.vals['6'][2])], pre=(N2, B.ss(N2)))
        else:
            ole = c[OLE('G')]
            ngt, _ = cmp_test(w, ph, 'ngt', 'O', B.on, LENg, pf['lenn'], True, ole)
            B.call(R, 'tm2lbrt', {'A': LSB['Z2'], 'C': CNGT, 'E': LSB['Z3'], 'Q': GT(LSB['Y3']), 'N': N2},
                   {STMT(GT(LSB['Y3'])): gotocl(w, ph, mk['tv'], LSB['Y3'], B.ex[LAB(LSB['Y3'])]), SSS(N2): B.ss(N2),
                    'A. m e. %s ( %s ` m ) = 1o' % (N2, CNGT): ngt, CTY(CNGT): cty(w, ph, mk, CNGT)}, [])
            kw = lambda t: {'car': '(/)', 'fl': '1o'}
            pr_ = '( %s /\\ r e. %s )' % (ph, N2)
            rr, _ = rab_elim(w, pr_, N2, lambda t: '( TMcmp ` %s ) = ( O Ncmp %s )' % (t, LENg), 'r',
                             s([], 'simpr', '( %s -> r e. %s )' % (pr_, N2)))
            nv = lset_val2(w, pr_, kw, 'r', rr)
            NR = '( %s ` r )' % L_TT
            CT_ = lambda t: '( ( TMcar ` %s ) = (/) /\\ ( TMfl ` %s ) = 1o )' % (t, t)
            inm = rab_in(w, pr_, NTT, CT_, NR, nv['mem'], s([nv['fields']['car'], nv['fields']['fl']], 'jca', '( %s -> %s )' % (pr_, CT_(NR))))
            hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, N2, L_TT, NTT))
            B.call(R, 'tm2flg', {'A': LSB['Z3'], 'E': LMF['Z2'], 'F': L_TT, 'N': N2, "N'": NTT},
                   {LTY(L_TT): lset_ty2(w, ph, mk, L_TT, kw), SSS(N2): B.ss(N2), SSS(NTT): B.ss(NTT),
                    'A. r e. %s ( %s ` r ) e. %s' % (N2, L_TT, NTT): hl}, [])
    if kind in 'ab':
        g1n = s([B.gn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, G1_))
        E1n, E2n = E1('H'), E2(G1_)
        g1n_ = B.g(E1n, ewg_(w, ph, 'Z', B.zn, EWg('H', "X'"), B.g(EWg('H', "X'"), ewg_(w, ph, 'H', B.hn, "X'", B.x2w))))
        g2n_ = B.g(E2n, ewg_(w, ph, G1_, g1n, 'Y', B.yw))
        slot = 4 if kind == 'a' else 3
        kw_ = {} if kind == 'b' else {'pre': (N1, B.ss(N1))}
        B.call(R, 'tmiscn', {'P': PCH(slot), 'E': LMF['Z2']}, {}, [('1', E1n, g1n_), ('2', E2n, g2n_)], **kw_)
    cur, out = R.normalize(N8)
    if kind in 'ab':
        assert out == [('1', E1n), ('2', E2n)], out
    else:
        assert out == [('6', E6)], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the bound
    COST = CCOST[kind]
    cpc = s([ww, B.gn, w.inst('coprimetocl')], 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (ph, CPT('G')))
    acn = s([cpc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, ACPg))
    cl.leaf(ACPg, 'NN0', acn)
    cl.leaf(TBB, 'NN0', tbn(w, ph, 'B', B.bn))
    m2n = cl.mem(M2, 'NN0')
    cl.leaf(T2, 'NN0', tbn(w, ph, M2, m2n))
    nwg = cl.ge0('( # ` W )')
    wb = s([B.nw, B.bn], 'nn0mulcld', '( %s -> ( ( # ` W ) x. B ) e. NN0 )' % ph)
    wc = s([B.nw, B.cn], 'nn0mulcld', '( %s -> ( ( # ` W ) x. C ) e. NN0 )' % ph)
    hyps0 = [nwg, s([wb], 'nn0ge0d', '( %s -> 0 <_ ( ( # ` W ) x. B ) )' % ph), s([wc], 'nn0ge0d', '( %s -> 0 <_ ( ( # ` W ) x. C ) )' % ph),
             cl.ge0('B'), cl.ge0('C')]
    t2m = s([m2n, B.msn, linarith(w, ph, hyps0, '%s <_ %s' % (M2, MS), closure=cl, products=True), w.inst('tmbmono')], 'syl3anc',
            '( %s -> %s <_ %s )' % (ph, T2, UU))
    tbm = s([B.bn, B.msn, linarith(w, ph, hyps0, 'B <_ %s' % MS, closure=cl, products=True), w.inst('tmbmono')], 'syl3anc',
            '( %s -> %s <_ %s )' % (ph, TBB, UU))
    A1 = '( %s + 1 )' % ACPg
    h1 = s([cl.mem(T2, 'RR'), cl.mem(UU, 'RR'), cl.mem(A1, 'RR'), cl.ge0(A1), t2m], 'lemul2ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A1, T2, A1, UU))
    au = s([cl.mem(ACPg, 'RR'), cl.mem(UU, 'RR'), cl.ge0(ACPg), cl.ge0(UU)], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (ph, ACPg, UU))
    hyps = [h1, tbm, B.uu1, au]
    atoms = [UU, TBB, T2, ACPg]
    if kind in 'bc':
        cl.leaf(CPAg, 'NN0', pf['can'])
        cl.leaf(LENg, 'NN0', pf['lenn'])
        C1_, L1_ = '( %s + 1 )' % CPAg, '( %s + 1 )' % LENg
        l1 = s([cl.mem(L1_, 'RR'), cl.mem(C1_, 'RR'), cl.mem(UU, 'RR'), cl.ge0(UU),
                linarith(w, ph, [pf['lca']], '%s <_ %s' % (L1_, C1_), closure=cl)], 'lemul1ad',
               '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, L1_, UU, C1_, UU))
        cu = s([cl.mem(CPAg, 'RR'), cl.mem(UU, 'RR'), cl.ge0(CPAg), cl.ge0(UU)], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (ph, CPAg, UU))
        hyps += [l1, cu, pf['lca']]
        atoms += [CPAg, LENg]
    if kind == 'b':
        cl4 = Closure(w, ph, {'B': ('NN0', B.bn)})
        cl4.leaf(TBB, 'NN0', tbn(w, ph, 'B', B.bn))
        l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
        qd = s([B.bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
               '( %s -> ( 4 x. ( ( B + 2 ) ^ 2 ) ) <_ %s )' % (ph, TBB))
        b3 = nlinarith(w, ph, [qd, cl4.ge0('B')], '( B + 3 ) <_ %s' % TBB, closure=cl4, atoms=['B', TBB])
        b3u = linarith(w, ph, [b3, tbm], '( B + 3 ) <_ %s' % UU, closure=cl, atoms=atoms)
        lb = s([cl.mem('( B + 3 )', 'RR'), cl.mem(UU, 'RR'), cl.mem(LENg, 'RR'), cl.ge0(LENg), b3u], 'lemul2ad',
               '( %s -> ( %s x. ( B + 3 ) ) <_ ( %s x. %s ) )' % (ph, LENg, LENg, UU))
        hyps.append(lb)
        hyps.append(s([cl.mem(LENg, 'RR'), cl.mem(UU, 'RR'), cl.ge0(LENg), cl.ge0(UU)], 'mulge0d',
                      '( %s -> 0 <_ ( %s x. %s ) )' % (ph, LENg, UU)))
    le = linarith(w, ph, hyps, '%s <_ %s' % (n, COST), closure=cl, atoms=atoms, products=True)
    cz = linarith(w, ph, hyps, '0 <_ %s' % COST, closure=cl, atoms=atoms, products=True)
    cn_ = s([s([cl.mem(COST, 'ZZ'), cz], 'jca', '( %s -> ( %s e. ZZ /\\ 0 <_ %s ) )' % (ph, COST, COST)),
             s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (COST, COST, COST))], 'sylibr', '( %s -> %s e. NN0 )' % (ph, COST))
    st = hrle(w, ph, mk['phm'], t, C, D, n, COST, cn_, le)
    finish(w, st, lab)
    return w.run(unify_only=UO)


def tmiscca(): return core_proof('tmiscca')
def tmisccb(): return core_proof('tmisccb')
def tmisccc(): return core_proof('tmisccc')


def conv_proof(lab):
    kind = lab[-1]
    tree = CASES[lab]
    T = numtree11(tree)
    ph = cj(T)
    w = W(lab, 'One iteration of Lean\'s ` scanF ` loop at the machine ( ` SCInv ` , ` scanBody_runs ` ) in the case of ~ tmiscc%s at '
               '` k + i ` with fuel ` R - i ` : the families go from ` i ` to ` i + 1 ` within ` ( U\' ` i ) = 64 U ( VN i - VN ( i + 1 ) ) '
               '- 1 ` steps (~ tmscv%s , ~ tmscr%s ).' % (kind, kind, 's' if kind == 'c' else 'n'))
    s = w.s
    B = Sf(w, ph, T)
    c, mk = B.c, B.mk
    io = c[IFZ]
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ph)
    i1le = s([io, w.inst('elfzop1le2')], 'syl', '( %s -> %s <_ R )' % (ph, I1))
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, I1))
    ile = s([s([inn], 'nn0red', '( %s -> i e. RR )' % ph), s([B.rn], 'nn0red', '( %s -> R e. RR )' % ph), ilt], 'ltled', '( %s -> i <_ R )' % ph)
    cl = B.cl
    cl.leaf('i', 'NN0', inn)
    hin, gin = B.jn('i', inn, ile)
    hi1n, gi1n = B.jn(I1, i1n, i1le)
    HP = '( %s + 1 )' % HI(I1)
    hpn = s([hi1n, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, HP))
    P2B = '( 2 ^ B )'
    cl.atom(P2B)
    ghb = c['( G + H ) < ( 2 ^ B )']
    G1 = '( %s + 1 )' % GI('i')
    # the arithmetic of the iteration (~ tmscari , over letters)
    ari, cari = inst(w, ph, 'tmscari', {}, Bld(w, ph, c, {'R e. NN0': B.rn, 'i e. NN0': inn, '( i + 1 ) <_ R': i1le, 'R <_ H': B.rle,
                                                          '( G + H ) < ( 2 ^ B )': ghb}))
    ca1, ca2 = parse_conj(UBL.C_ARI)
    ar1 = s([ari], 'simpld', '( %s -> %s )' % (ph, cj(ca1)))
    ar2 = s([ari], 'simprd', '( %s -> %s )' % (ph, cj(ca2)))
    hh = s([ar1], 'simpld', '( %s -> %s = %s )' % (ph, HI('i'), HP))
    gm = s([ar1], 'simprd', '( %s -> ( %s - 1 ) = %s )' % (ph, GI(I1), GI('i')))
    g1lt = s([ar2], 'simpld', '( %s -> %s < %s )' % (ph, G1, P2B))
    hplt = s([ar2], 'simprd', '( %s -> %s < %s )' % (ph, HP, P2B))
    tia = s([B.at, io], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, cj(AT), IFZ))
    # the arithmetic of the case
    if kind == 'a':
        cnd = c['-. %s' % CPc(GI('i'))]
        nsuc = s([cnd], 'intnanrd', '( %s -> -. %s )' % (ph, SUC(GI('i'))))
        va = s([s([tia, cnd], 'jca', '( %s -> %s )' % (ph, cj(CA.TREES['tmscva'][0]))), w.inst('tmscva')], 'syl',
               '( %s -> %s )' % (ph, CA.TREES['tmscva'][1]))
    elif kind == 'b':
        cp, nle = c[CPc(GI('i'))], c['-. %s' % OLE(GI('i'))]
        cnd = s([cp, nle], 'jca', '( %s -> ( %s /\\ -. %s ) )' % (ph, CPc(GI('i')), OLE(GI('i'))))
        nsuc = s([nle], 'intnand', '( %s -> -. %s )' % (ph, SUC(GI('i'))))
        va = s([s([tia, cnd], 'jca', '( %s -> %s )' % (ph, cj(CA.TREES['tmscvb'][0]))), w.inst('tmscvb')], 'syl',
               '( %s -> %s )' % (ph, CA.TREES['tmscvb'][1]))
    else:
        cp, ole = c[CPc(GI('i'))], c[OLE(GI('i'))]
        cnd = s([cp, ole], 'jca', '( %s -> %s )' % (ph, SUC(GI('i'))))
        vv = s([s([tia, cnd], 'jca', '( %s -> %s )' % (ph, cj(CA.TREES['tmscvc'][0]))), w.inst('tmscvc')], 'syl',
               '( %s -> %s )' % (ph, CA.TREES['tmscvc'][1]))
        va = s([vv], 'simpld', '( %s -> %s = ( ( %s + %s ) + 1 ) )' % (ph, VN('i'), ACP(GI('i')), CPA(GI('i'))))
        v10 = s([vv], 'simprd', '( %s -> %s = 0 )' % (ph, VN(I1)))
        rs = s([s([tia, cnd], 'jca', '( %s -> %s )' % (ph, cj(CA.TREES['tmscrs'][0]))), w.inst('tmscrs')], 'syl',
               '( %s -> %s )' % (ph, CA.TREES['tmscrs'][1]))
        rs1 = s([rs], 'simpld', '( %s -> ( -. %s /\\ %s = R ) )' % (ph, NONE, I1))
        nn_ = s([rs1], 'simpld', '( %s -> -. %s )' % (ph, NONE))
        i1r = s([rs1], 'simprd', '( %s -> %s = R )' % (ph, I1))
        pfe = s([rs], 'simprd', '( %s -> %s = %s )' % (ph, PFS, PA1(GI('i'))))
        sj1 = s([i1r, nn_], 'jca', '( %s -> %s )' % (ph, SJ(I1)))
    if kind in 'ab':
        rn_ = s([s([tia, nsuc], 'jca', '( %s -> %s )' % (ph, cj(CA.TREES['tmscrn'][0]))), w.inst('tmscrn')], 'syl',
                '( %s -> %s )' % (ph, CA.TREES['tmscrn'][1]))
        nsj1 = s([rn_], 'simpld', '( %s -> -. %s )' % (ph, SJ(I1)))
        bi1 = s([rn_], 'simprd', '( %s -> ( %s = R <-> %s = 0 ) )' % (ph, I1, HI(I1)))
    nsi = s([s([s([cl.mem('i', 'RR'), ilt], 'ltned', '( %s -> i =/= R )' % ph)], 'neneqd', '( %s -> -. i = R )' % ph)], 'intnanrd',
            '( %s -> -. %s )' % (ph, SJ('i')))
    # the pre stacks: PB( i ) = SP
    E1p, E2p = E1(HP), E2(GI('i'))
    g1p = B.g(E1p, ewg_(w, ph, 'Z', B.zn, EWg(HP, "X'"), B.g(EWg(HP, "X'"), ewg_(w, ph, HP, hpn, "X'", B.x2w))))
    g2p = B.g(E2p, ewg_(w, ph, GI('i'), gin, 'Y', B.yw))
    SP = B.S0.upd('1', E1p, g1p).upd('2', E2p, g2p)
    chain0 = [('1', E1p), ('2', E2p)]
    pvi, SI = B.pv('i', inn, ile)
    rules_i = {FU('i'): (HP, s([s([nsi], 'iffalsed', '( %s -> %s = %s )' % (ph, FU('i'), HI('i'))), hh], 'eqtrd', '( %s -> %s = %s )' % (ph, FU('i'), HP))),
               KG('i'): (GI('i'), s([nsi], 'iffalsed', '( %s -> %s = %s )' % (ph, KG('i'), GI('i')))),
               S6('i'): (D6, s([nsi], 'iffalsed', '( %s -> %s = %s )' % (ph, S6('i'), D6)))}
    rpi, xpi = w.rewrite(PB('i'), rules_i, ph)
    assert xpi == UP(SP.D, '6', D6), xpi
    u6 = upidv(w, ph, SP.D, '6', D6, SP.vals['6'][1], mk['tv'], SP.memb, mk['k']['6']['kd'])
    PT = '( %s ` i )' % PV
    pre_eq = s([s([s([pvi, rpi], 'eqtrd', '( %s -> %s = %s )' % (ph, PT, xpi)), u6], 'eqtrd', '( %s -> %s = %s )' % (ph, PT, SP.D))], 'eqcomd',
               '( %s -> %s = %s )' % (ph, SP.D, PT))
    # the core at k := G + i , f := H - ( i + 1 ) , D := SP
    m = {'G': GI('i'), 'H': HI(I1), 'D': SP.D}
    ex = {STKD(SP.D): SP.memb, '%s e. NN0' % GI('i'): gin, '%s e. NN0' % HI(I1): hi1n, '%s < %s' % (G1, P2B): g1lt, '%s < %s' % (HP, P2B): hplt}
    for k_, (txt, st_, g_) in SP.vals.items():
        ex['( %s ` %s ) = %s' % (SP.D, k_, txt)] = st_
    cst = CCOND[kind] if isinstance(CCOND[kind], str) else cj(CCOND[kind])
    ex[tsub_text(cst, m)] = cnd
    for k_, v_ in B.gam.items():
        if v_ is not None:
            ex[WG(k_)] = v_
    tc, cc = inst(w, ph, 'tmiscc' + kind, m, Bld(w, ph, c, ex))
    C, D, n = triple_parts(cc)
    t = tc
    Dst = triple_D(D)
    lab_ = LMF['Z2']
    if kind == 'c':
        # the core's post reads stack 6 of its own D (` ( SP ` 6 ) ` ): untouched by the updates at 1 and 2, it is ` ( D ` 6 ) `
        S6D = '( %s ` 6 )' % SP.D
        r6, Dst6 = w.rewrite(Dst, {S6D: (D6, SP.vals['6'][1])}, ph)
        t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, lab_, NTT, r6, Dst, Dst6))
        Dst = Dst6
    P1T = '( %s ` %s )' % (PV, I1)
    N1T = '( %s ` %s )' % (NV, I1)
    pv1, S1 = B.pv(I1, i1n, i1le)
    if kind in 'ab':
        E1n, E2n = E1(HI(I1)), E2(G1)
        g1n = s([gin, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, G1))
        B.g(E1n, ewg_(w, ph, 'Z', B.zn, EWg(HI(I1), "X'"), B.g(EWg(HI(I1), "X'"), ewg_(w, ph, HI(I1), hi1n, "X'", B.x2w))))
        B.g(E2n, ewg_(w, ph, G1, g1n, 'Y', B.yw))
        chain = chain0 + [('1', E1n), ('2', E2n)]
    else:
        pf = pool_at(w, ph, B, GI('i'), gin)
        E6 = ENCL(PA1(GI('i')), D6)
        B.g(E6, enclg(w, ph, PA1(GI('i')), pf['paw'], D6, B.S0.vals['6'][2]))
        chain = chain0 + [('6', E6)]
    assert chain_text('D', chain) == Dst, (chain_text('D', chain), Dst)
    nst, out = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chain, B.gam, N8)
    Dn = chain_text('D', out)
    if nst is None:
        nst = s([], 'eqidd', '( %s -> %s = %s )' % (ph, Dst, Dst))
    if kind in 'ab':
        assert out == [('1', E1n), ('2', E2n)], out
        ga = s([cl.mem('G', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph)], 'addassd',
               '( %s -> %s = %s )' % (ph, G1, GI(I1)))
        rd, xd = w.rewrite(Dn, {G1: (GI(I1), ga)}, ph)
        r1 = {FU(I1): (HI(I1), s([nsj1], 'iffalsed', '( %s -> %s = %s )' % (ph, FU(I1), HI(I1)))),
              KG(I1): (GI(I1), s([nsj1], 'iffalsed', '( %s -> %s = %s )' % (ph, KG(I1), GI(I1)))),
              S6(I1): (D6, s([nsj1], 'iffalsed', '( %s -> %s = %s )' % (ph, S6(I1), D6)))}
        rp1, xp1 = w.rewrite(PB(I1), r1, ph)
        assert xp1 == UP(xd, '6', D6), (xp1, xd)
        SX = B.S0.upd('1', E1n, B.gam[E1n]).upd('2', E2(GI(I1)), B.g(E2(GI(I1)), ewg_(w, ph, GI(I1), gi1n, 'Y', B.yw)))
        assert SX.D == xd, (SX.D, xd)
        u6b = upidv(w, ph, SX.D, '6', D6, SX.vals['6'][1], mk['tv'], SX.memb, mk['k']['6']['kd'])
        deq = s([s([nst, rd], 'eqtrd', '( %s -> %s = %s )' % (ph, Dst, xd)),
                 s([s([pv1, rp1], 'eqtrd', '( %s -> %s = %s )' % (ph, P1T, xp1)), u6b], 'eqtrd', '( %s -> %s = %s )' % (ph, P1T, xd))], 'eqtr4d',
                '( %s -> %s = %s )' % (ph, Dst, P1T))
        NC = NCF(HI(I1))
        VCAR = 'if ( %s = 0 , (/) , 1o )' % HI(I1)
        ic = s([s([bi1], 'bicomd', '( %s -> ( %s = 0 <-> %s = R ) )' % (ph, HI(I1), I1))], 'ifbid',
               '( %s -> %s = if ( %s = R , (/) , 1o ) )' % (ph, VCAR, I1))
        fc = s([s([nsj1], 'iffalsed', '( %s -> if ( %s , 1o , (/) ) = (/) )' % (ph, SJ(I1)))], 'eqcomd',
               '( %s -> (/) = if ( %s , 1o , (/) ) )' % (ph, SJ(I1)))
        PSab = lambda t: '( ( TMcar ` %s ) = %s /\\ ( TMfl ` %s ) = (/) )' % (t, VCAR, t)
        assert NC == '{ h e. TMSt | %s }' % PSab('h'), NC

        def bi_ab(pp, t):
            return s([s([lift_from(w, ph, pp, ic)], 'eqeq2d', '( %s -> ( ( TMcar ` %s ) = %s <-> ( TMcar ` %s ) = if ( %s = R , (/) , 1o ) ) )'
                        % (pp, t, VCAR, t, I1)),
                      s([lift_from(w, ph, pp, fc)], 'eqeq2d', '( %s -> ( ( TMfl ` %s ) = (/) <-> ( TMfl ` %s ) = if ( %s , 1o , (/) ) ) )'
                        % (pp, t, t, SJ(I1)))],
                     'anbi12d', '( %s -> ( %s <-> %s ) )' % (pp, PSab(t), COND(t, I1)))
        nq = rab_h_eq(w, ph, 'TMSt', PSab, lambda t: COND(t, I1), bi_ab)
        rule = COST_RHS = '( ( %s x. %s ) - 1 )' % ('( %s + 1 )' % ACP(GI('i')) if kind == 'a' else
                                                   '( ( %s + %s ) + 1 )' % (ACP(GI('i')), CPA(GI('i'))), K64)
    else:
        assert out == [('1', E1p), ('2', E2p), ('6', E6)], out
        r1 = {FU(I1): (HP, s([sj1], 'iftrued', '( %s -> %s = %s )' % (ph, FU(I1), HP))),
              KG(I1): ('( %s - 1 )' % GI(I1), s([sj1], 'iftrued', '( %s -> %s = ( %s - 1 ) )' % (ph, KG(I1), GI(I1)))),
              S6(I1): (ENCL(PFS, D6), s([sj1], 'iftrued', '( %s -> %s = %s )' % (ph, S6(I1), ENCL(PFS, D6))))}
        rp1, xp1 = w.rewrite(PB(I1), r1, ph)
        rp2, xp2 = w.rewrite(xp1, {'( %s - 1 )' % GI(I1): (GI('i'), gm), PFS: (PA1(GI('i')), pfe)}, ph)
        assert xp2 == Dn, (xp2, Dn)
        deq = s([nst, s([s([s([pv1, rp1], 'eqtrd', '( %s -> %s = %s )' % (ph, P1T, xp1)), rp2], 'eqtrd', '( %s -> %s = %s )' % (ph, P1T, Dn))],
                        'eqcomd', '( %s -> %s = %s )' % (ph, Dn, P1T))], 'eqtrd', '( %s -> %s = %s )' % (ph, Dst, P1T))
        NC = NTT
        ca = s([s([s([i1r], 'iftrued', '( %s -> if ( %s = R , (/) , 1o ) = (/) )' % (ph, I1))], 'eqcomd',
                  '( %s -> (/) = if ( %s = R , (/) , 1o ) )' % (ph, I1))], 'id', '') if False else \
            s([s([i1r], 'iftrued', '( %s -> if ( %s = R , (/) , 1o ) = (/) )' % (ph, I1))], 'eqcomd', '( %s -> (/) = if ( %s = R , (/) , 1o ) )' % (ph, I1))
        fa = s([s([sj1], 'iftrued', '( %s -> if ( %s , 1o , (/) ) = 1o )' % (ph, SJ(I1)))], 'eqcomd', '( %s -> 1o = if ( %s , 1o , (/) ) )' % (ph, SJ(I1)))
        PSc = lambda t: '( ( TMcar ` %s ) = (/) /\\ ( TMfl ` %s ) = 1o )' % (t, t)
        assert NC == '{ h e. TMSt | %s }' % PSc('h'), NC

        def bi_c(pp, t):
            return s([s([lift_from(w, ph, pp, ca)], 'eqeq2d', '( %s -> ( ( TMcar ` %s ) = (/) <-> ( TMcar ` %s ) = if ( %s = R , (/) , 1o ) ) )'
                        % (pp, t, t, I1)),
                      s([lift_from(w, ph, pp, fa)], 'eqeq2d', '( %s -> ( ( TMfl ` %s ) = 1o <-> ( TMfl ` %s ) = if ( %s , 1o , (/) ) ) )'
                        % (pp, t, t, SJ(I1)))],
                     'anbi12d', '( %s -> ( %s <-> %s ) )' % (pp, PSc(t), COND(t, I1)))
        nq = rab_h_eq(w, ph, 'TMSt', PSc, lambda t: COND(t, I1), bi_c)
    nq2 = s([nq, s([B.nv(I1, i1n)], 'eqcomd', '( %s -> %s = %s )' % (ph, NCL(I1), N1T))], 'eqtrd', '( %s -> %s = %s )' % (ph, NC, N1T))
    ceq = s([clnneq(w, ph, lab_, nq2, NC, N1T, Dst), clneq(w, ph, lab_, N1T, deq, Dst, P1T)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN(lab_, N1T, P1T)))
    # the pre class ( N' ` i )
    NI = '( %s ` i )' % NV
    C2 = CLN(LMF['Y4'], NI, SP.D)
    assert C == CLN(LMF['Y4'], S, SP.D), C[:300]
    t = hrssc(w, ph, mk['phm'], t, C, D, n, C2, clnss(w, ph, LMF['Y4'], NI, S, SP.D, B.nvss('i', inn)))
    cpre = clneq(w, ph, LMF['Y4'], NI, pre_eq, SP.D, PT)
    # the charge: the core's bound = UB( i ) (~ tmscuba / ~ tmscubb / ~ tmscubc at ` U := 64 U , A := VN i ,
    # B := VN ( i + 1 ) , C := a , D := c ` : the identity is proved once over letters, not under this antecedent)
    UBI = UB('i')
    vin = B.vnn('i', inn, ile)
    vi1n = B.vnn(I1, i1n, i1le)
    cpc = s([B.ww, gin, w.inst('coprimetocl')], 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (ph, CPT(GI('i'))))
    acn = s([cpc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, ACP(GI('i'))))
    uun_ = s([B.msn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, UU))
    n64 = s([s([s([], '6nn0', '6 e. NN0'), s([], '4nn', '4 e. NN')], 'decnncl', '; 6 4 e. NN')], 'a1i', '( %s -> ; 6 4 e. NN )' % ph)
    k64n = s([n64, uun_], 'nnmulcld', '( %s -> %s e. NN )' % (ph, K64))
    m_ub = {'U': K64, 'A': VN('i'), 'B': VN(I1), 'C': ACP(GI('i'))}
    ex_ub = {'%s e. NN' % K64: k64n, '%s e. NN0' % VN('i'): vin, '%s e. NN0' % VN(I1): vi1n, '%s e. NN0' % ACP(GI('i')): acn,
             concl(w, ph, va): va}
    if kind in 'bc':
        pf2 = pf if kind == 'c' else pool_at(w, ph, B, GI('i'), gin)
        m_ub['D'] = CPA(GI('i'))
        ex_ub['%s e. NN0' % CPA(GI('i'))] = pf2['can']
    if kind == 'c':
        ex_ub['%s = 0' % VN(I1)] = v10
    stu, ccu = inst(w, ph, 'tmscub' + kind, m_ub, Bld(w, ph, c, ex_ub))
    assert ccu == '( %s = %s /\\ %s e. NN0 )' % (n, UBI, UBI), (ccu[:400], n[:400])
    ne_ = s([stu], 'simpld', '( %s -> %s = %s )' % (ph, n, UBI))
    ubn = s([stu], 'simprd', '( %s -> %s e. NN0 )' % (ph, UBI))
    uvi = B.uv('i', inn)
    ue = s([ne_, s([uvi], 'eqcomd', '( %s -> %s = %s )' % (ph, UBI, UI))], 'eqtrd', '( %s -> %s = %s )' % (ph, n, UI))
    t, C, D, n = hrrw(w, ph, t, C2, D, n, ceq=cpre, deq=ceq, neq=ue)
    uin = s([uvi, ubn], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, UI))
    st = s([uin, t], 'jca', '( %s -> %s )' % (ph, CONC_C))
    finish(w, st, lab)
    return w.run(unify_only=UO)


def tmiscia(): return conv_proof('tmiscia')
def tmiscib(): return conv_proof('tmiscib')
def tmiscic(): return conv_proof('tmiscic')


def tmiscfi():
    lab = 'tmiscfi'
    PJ = cj(TI_)
    w = W(lab, 'One iteration of Lean\'s ` scanF ` loop at the machine ( ` scanBody_runs ` ): below ` R ` the carry is set, and '
               '` scanBody ` takes the families from ` i ` to ` i + 1 ` within ` ( U\' ` i ) ` steps, by cases on the coprimality '
               'of ` k + i ` and on ` theta <_ # P ` (~ tmiscia , ~ tmiscib , ~ tmiscic ).')
    s = w.s
    st = {l: s([], l, STMTS11[l]) for l in CASES}
    P1 = '( %s /\\ %s )' % (PJ, CPc(GI('i')))
    bc = s([st['tmiscic'], st['tmiscib']], 'pm2.61dan', '( %s -> %s )' % (P1, CONC_C))
    a = s([bc, st['tmiscia']], 'pm2.61dan', '( %s -> %s )' % (PJ, CONC_C))
    c = Ctx(w, PJ, TI_)
    io = c[IFZ]
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % PJ)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % PJ)
    ir = s([s([inn], 'nn0red', '( %s -> i e. RR )' % PJ), ilt], 'ltned', '( %s -> i =/= R )' % PJ)
    nir = s([ir], 'neneqd', '( %s -> -. i = R )' % PJ)
    NI = '( %s ` i )' % NV
    pm = '( %s /\\ m e. %s )' % (PJ, NI)
    L = lambda x: lift_from(w, PJ, pm, x)
    fe = s([c['%s = %s' % (NV, NFM)]], 'fveq1d', '( %s -> %s = ( %s ` i ) )' % (PJ, NI, NFM))
    mni = s([s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)), L(fe)], 'eleqtrd', '( %s -> m e. ( %s ` i ) )' % (pm, NFM))
    mm, mc = fam_unpack(w, pm, COND, 'i', L(inn), 'm', mni)
    car = s([s([mc], 'simpld', '( %s -> ( TMcar ` m ) = if ( i = R , (/) , 1o ) )' % pm),
             L(s([nir], 'iffalsed', '( %s -> if ( i = R , (/) , 1o ) = 1o )' % PJ))], 'eqtrd', '( %s -> ( TMcar ` m ) = 1o )' % pm)
    part1 = s([car], 'ralrimiva', '( %s -> A. m e. %s ( TMcar ` m ) = 1o )' % (PJ, NI))
    ui = s([a], 'simpld', '( %s -> %s e. NN0 )' % (PJ, UI))
    tr = s([a], 'simprd', '( %s -> %s )' % (PJ, TRI_I))
    w.qed([s([part1, ui], 'jca', '( %s -> ( A. m e. %s ( TMcar ` m ) = 1o /\\ %s e. NN0 ) )' % (PJ, NI, UI)), tr], 'jca', STMTS11[lab])
    return w.run(unify_only=UO)


def tmiscft():
    lab = 'tmiscft'
    w = W(lab, 'The frame of Lean\'s ` scanF ` loop at the machine: for ` i <_ R ` the class family is a set of states and the '
               'stack family a stack assignment, and at ` R ` the carry is clear.')
    s = w.s
    DI = 'i e. ( 0 ... R )'
    TT = numtree11((PSI_T, DI))
    pt = cj(TT)
    B = Sf(w, pt, TT)
    ii = B.c[DI]
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ R )' % pt)
    pv, St = B.pv('i', inn, ile)
    body = LTYP[len('A. %s ' % DI):]
    one = s([B.nvss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))
    k = s([], 't10stk', ST_NUMS)
    one0 = s([k, one], 'mpan2', '( %s -> %s )' % (cj((PSI_T, DI)), body))
    typ = s([one0], 'ralrimiva', '( %s -> %s )' % (PSI, LTYP))
    TE = numtree11(PSI_T)
    pe = cj(TE)
    c = Ctx(w, pe, TE)
    at = Bld(w, pe, c, {})(AT)
    r0 = CA.r0facts(w, pe, at)
    rn = r0['R e. NN0']
    NE = '( %s ` R )' % NV
    pm = '( %s /\\ m e. %s )' % (pe, NE)
    L = lambda x: lift_from(w, pe, pm, x)
    fe = s([c['%s = %s' % (NV, NFM)]], 'fveq1d', '( %s -> %s = ( %s ` R ) )' % (pe, NE, NFM))
    mni = s([s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)), L(fe)], 'eleqtrd', '( %s -> m e. ( %s ` R ) )' % (pm, NFM))
    mm, mc = fam_unpack(w, pm, COND, 'R', L(rn), 'm', mni)
    c0 = s([s([mc], 'simpld', '( %s -> ( TMcar ` m ) = if ( R = R , (/) , 1o ) )' % pm),
            s([s([], 'eqidd', '( %s -> R = R )' % pm)], 'iftrued', '( %s -> if ( R = R , (/) , 1o ) = (/) )' % pm)], 'eqtrd',
           '( %s -> ( TMcar ` m ) = (/) )' % pm)
    ex_ = s([not1o(w, pm, c0, 'TMcar', 'm')], 'ralrimiva', '( %s -> %s )' % (pe, LEXIT))
    ex0 = s([k, ex_], 'mpan2', '( %s -> %s )' % (PSI, LEXIT))
    w.qed([typ, ex0], 'jca', STMTS11[lab])
    return w.run(unify_only=UO)


def tmiscfl():
    lab = 'tmiscfl'
    w = W(lab, 'Lean\'s ` scanF ` loop at the machine: ~ tm2floop at the families ( ` N\' ` , ` P\' ` , ` U\' ` letters), ` R ` '
               'iterations of ` scanBody ` (~ tmiscfi ), the frame by ~ tmiscft .')
    s = w.s
    T = numtree11(PSI_T)
    ph = cj(T)
    B = Sf(w, ph, T)
    fn_, cks, en, exn = FRAGS['scb'].children[0]
    entry_unfold(B, fn_, cks, PCH(0), LSB[exn])
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmiscft', STMTS11['tmiscft']))
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    per = s([s([], 'tmiscfi', STMTS11['tmiscfi'])], 'ralrimiva', '( %s -> %s )' % (PSI, LPER))
    ex[LPER] = lift_from(w, PSI, ph, per)
    ex['R e. NN0'] = B.rn
    st = Bld(w, ph, B.c, ex)(LTREE)
    st2 = s([st, w.inst('tm2floop')], 'syl', '( %s -> %s )' % (ph, LCONCL))
    finish(w, st2, lab)
    return w.run(unify_only=UO)


if __name__ == '__main__':
    for l in SEL:
        if l != 'show':
            globals()[l]()

