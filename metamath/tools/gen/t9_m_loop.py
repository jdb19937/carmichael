"""T9: the extraction loop ` loop ( !flag ) ( exBody ... ) ` of ` extractGoF ` at the machine (Lean ` exLoop_runs ` ),
on the installation predicate TMIexg, at the families of the state sequence ` ExSt ` (blueprint D3).

  tmiexgi   one iteration: at ` i < ExIt ` , ` exBody ` (~ tmiexb ) at the state ` ( ExSt ` i ) ` and the pool element
            ` W ` i ` takes the family at ` i ` to the family at ` i + 1 ` ; the bounds from ~ exinv
  tmiexgt   the frame: the families' typings for ` i <_ ExIt ` and the test ` !flag ` failing at ` ExIt `
  tmiexgl   ~ tm2floopu at the families ( ` P' ` a letter)

    MM_DB=sorties/t9.mm python3 tools/gen/t9_m_loop.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
from t7lib import famval, fam_unpack, ifex_closed
from t9_h_seq import PH_S as PH_S_Z
from t9_i_inv import BODY as BODY_Z

SEL = sys.argv[1:]
LMG = FRAGS['exg'].lmap()
Z0 = Z0G
PH_S0 = tsub_text(PH_S_Z, {'Z': Z0})
Si = lambda t: '( %s ` %s )' % (SQG, t)
NW = '( # ` W )'
DRP = lambda t: '( W substr <. %s , %s >. )' % (t, NW)
REST = lambda t: ENCL(DRP(t), 'X')
HIT = lambda t: '%s = 1o' % ZH(Si(t))
K3 = lambda t: '( <" 3 "> ++ %s )' % REST(t)
KV = lambda t: 'if ( %s , %s , %s )' % (HIT(t), K3(t), REST(t))
EGY = EWg('G', 'Y')
K0V = lambda t: EWg(ZM(Si(t)), EGY)
J0V = lambda t: ENCL(ZU(Si(t)), 'R')
PBG = lambda t: UPS('D', ('K', KV(t)), ("I'", ACCW(ZA(Si(t)))), ('K0', K0V(t)), ('J0', J0V(t)))
FLC = lambda t: 'if ( ( %s = %s \\/ %s ) , 1o , (/) )' % (t, NW, HIT(t))
COND = lambda h, t: '( TMfl ` %s ) = %s' % (h, FLC(t))
NCL = lambda t: '{ h e. TMSt | %s }' % COND('h', t)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
PF = '( j e. NN0 |-> %s )' % PBG('j')
PV = "P'"
PSI_T = (TREE_EXG, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
EXC_ = EXC('L', 'H', 'Q')
GM = {'A': LMG['Q2'], 'B0': LMG['B0'], 'E': LMG['Q3'], 'C0': CNFL, 'R': RG, "T'": EXC_, 'N': NFM, 'P': PV}
_LA, _LC = split_imp(stmt('tm2floopu'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
_pre = 'A. i e. ( 0 ..^ %s ) ' % RG
assert LPER.startswith(_pre)
LBODY = LPER[len(_pre):]
T_I = (PSI_T, 'i e. ( 0 ..^ %s )' % RG)
PSI_I = cj(T_I)
ST_I = '( %s -> %s )' % (PSI_I, LBODY)
ST_T = '( %s -> ( %s /\\ %s ) )' % (PSI, LTYP, LEXIT)
ST_L = '( %s -> %s )' % (PSI, LCONCL)
BODYI = lambda t, c: tsub_text(BODY_Z(t, c), {'Z': Z0})


class Lg(Base):
    """the facts under an antecedent whose tree contains PSI_T"""
    def __init__(self, w, ph, T, root=None):
        s = w.s
        c0 = Ctx(w, ph, T)
        self.c0 = c0
        ln, gn, ww = c0['L e. NN'], c0['G e. NN0'], c0['W e. Word NN0']
        fn, uw, an = c0['F e. NN0'], c0['U e. Word NN0'], c0['A e. Tbl']
        l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
        xw, x2w, yw, rw = c0[WG('X')], c0[WG("X'")], c0[WG('Y')], c0[WG('R')]
        egy = ewg_(w, ph, 'G', gn, 'Y', yw)
        eqs = {'K': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), 'J': (EWg('L', "X'"), ewg_(w, ph, 'L', l0, "X'", x2w)),
               "I'": (ACCW('A'), accw_g(w, ph, 'A', an, 'L', l0)), 'K0': (EWg('F', EGY), ewg_(w, ph, 'F', fn, EGY, egy)),
               'J0': (ENCL('U', 'R'), enclg(w, ph, 'U', uw, 'R', rw))}
        Base.__init__(self, w, ph, T, K8, 'exg', eqs)
        self.g(EGY, egy)
        self.ln, self.gn, self.ww, self.fn, self.uw, self.an, self.l0 = ln, gn, ww, fn, uw, an, l0
        self.xw = xw
        # the initial state
        e0 = s([s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % ph)
        z3 = s([an, e0], 'opelxpd', '( %s -> <. A , (/) >. e. ( Tbl X. 2o ) )' % ph)
        z2 = s([uw, z3], 'opelxpd', '( %s -> <. U , <. A , (/) >. >. e. ( Word NN0 X. ( Tbl X. 2o ) ) )' % ph)
        self.z0 = s([fn, z2], 'opelxpd', '( %s -> %s e. %s )' % (ph, Z0, STY))
        self.pS = s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph),
                     s([ww, self.z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY))], 'jca', '( %s -> %s )' % (ph, PH_S0))
        ip = s([self.pS, w.inst('exitp')], 'syl', '( %s -> ( %s e. ( 0 ... %s ) /\\ ( %s = %s \\/ %s ) /\\ A. i e. ( 0 ..^ %s ) ( i e. ( 0 ..^ %s ) /\\ -. %s ) ) )'
               % (ph, RG, NW, RG, NW, HIT(RG), RG, NW, HIT('i')))
        self.rz = s([ip], 'simp1d', '( %s -> %s e. ( 0 ... %s ) )' % (ph, RG, NW))
        self.ror = s([ip], 'simp2d', '( %s -> ( %s = %s \\/ %s ) )' % (ph, RG, NW, HIT(RG)))
        self.ral = s([ip], 'simp3d', '( %s -> A. i e. ( 0 ..^ %s ) ( i e. ( 0 ..^ %s ) /\\ -. %s ) )' % (ph, RG, NW, HIT('i')))
        self.rn = s([self.rz, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, RG))
        self.rle = s([self.rz, w.inst('elfzle2')], 'syl', '( %s -> %s <_ %s )' % (ph, RG, NW))
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
        self.pvs = {}

    def sti(self, t, tz):
        """( ph -> Si( t ) e. STY ) from tz : t e. ( 0 ... # W )"""
        w, ph, s = self.w, self.ph, self.w.s
        return s([s([self.pS, tz], 'jca', '( %s -> ( %s /\\ %s e. ( 0 ... %s ) ) )' % (ph, PH_S0, t, NW)), w.inst('exstcl')], 'syl',
                 '( %s -> %s e. %s )' % (ph, Si(t), STY))

    def comps(self, t, tz):
        """typings of the components of Si( t ): m NN0, used Word NN0, table Tbl"""
        w, ph, s = self.w, self.ph, self.w.s
        st = self.sti(t, tz)
        T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
        mz = s([st, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, ZM(Si(t))))
        z2 = s([st, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. %s )' % (ph, Si(t), T23))
        uz = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ZU(Si(t))))
        z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` %s ) ) e. ( Tbl X. 2o ) )' % (ph, Si(t)))
        az = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, ZA(Si(t))))
        return st, mz, uz, az

    def pbst(self, t, tz):
        """the Stacks of PBG( t ), t e. ( 0 ... # W ) by tz"""
        w, ph, s = self.w, self.ph, self.w.s
        st, mz, uz, az = self.comps(t, tz)
        dw = s([self.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DRP(t)))
        gr = self.g(REST(t), enclg(w, ph, DRP(t), dw, 'X', self.xw))
        s3 = s([closed(w, ph, 'gamma3', "3 e. Gamma'")], 's1cld', "( %s -> <\" 3 \"> e. Word Gamma' )" % ph)
        g3 = self.g(K3(t), wgcat(w, ph, '<" 3 ">', REST(t), s3, gr))
        gk = self.g(KV(t), s([g3, gr], 'ifcld', "( %s -> %s e. Word Gamma' )" % (ph, KV(t))))
        ga = self.g(ACCW(ZA(Si(t))), accw_g(w, ph, ZA(Si(t)), az, 'L', self.l0))
        gm = self.g(K0V(t), ewg_(w, ph, ZM(Si(t)), mz, EGY, self.gam[EGY]))
        gu = self.g(J0V(t), enclg(w, ph, ZU(Si(t)), uz, 'R', self.c0[WG('R')]))
        self.dw = dw
        return self.S0.upd('K', KV(t), gk).upd("I'", ACCW(ZA(Si(t))), ga).upd('K0', K0V(t), gm).upd('J0', J0V(t), gu)

    def pv(self, t, tz, tn):
        """( ph -> ( P' ` t ) = PBG( t ) ) and the Stacks at ( P' ` t )"""
        if t not in self.pvs:
            fam = self.c0['%s = %s' % (PV, PF)]
            self.pvs[t] = fam_at(self.w, self.ph, self.mk, self.ne, fam, PV, 'j', 'NN0', PBG, t, tn, self.pbst(t, tz))
        return self.pvs[t]

    def famss(self, t, tn):
        """( ph -> ( NFM ` t ) C_ ( 2nd ` T ) )"""
        w, ph = self.w, self.ph
        fv = famval(w, ph, COND, t, tn)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NCL(t))], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NCL(t)))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NCL(t)))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ ( 2nd ` T ) )' % (ph, NFM, t))


def cnfl_at(w, pm, mm, fl, val_is_1):
    """( pm -> ( CNFL ` m ) = 1o ) from ( TMfl ` m ) = (/) (val_is_1 False) , or ( pm -> -. ( CNFL ` m ) = 1o ) from
    ( TMfl ` m ) = 1o"""
    s = w.s
    X_of = lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t
    xex = ifex_closed(w, pm, '( TMfl ` m ) = 1o', '(/)', '1o', s([], '0ex', '(/) e. _V'), s([], '1oex', '1o e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    if val_is_1:
        c0 = s([cv, s([fl], 'iftrued', '( %s -> %s = (/) )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CNFL))
        return not1o(w, pm, c0, CNFL, 'm')
    fne = s([fl, s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o')], 'a1i', '( %s -> (/) =/= 1o )' % pm)], 'eqnetrd',
            '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
    return s([cv, s([s([fne], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)], 'iffalsed', '( %s -> %s = 1o )' % (pm, X_of('m')))], 'eqtrd',
             '( %s -> ( %s ` m ) = 1o )' % (pm, CNFL))


def tmiexgi():
    lab = 'tmiexgi'
    ph = PSI_I
    w = W(lab, 'One iteration of Lean\'s ` extractGoF ` loop at the machine (` exLoop_runs ` ): below the stop index '
               '` ExIt ` the flag is clear, and ` exBody ` (~ tmiexb ) at the state ` ( ExSt ` i ) ` and the pool element ` W ` i ` '
               'takes the family at ` i ` to the family at ` i + 1 ` (~ exstp1 ) within ` exC ` steps, its size hypotheses '
               'from the invariant ~ exinv at some ` c <_ N + i ` .')
    s = w.s
    # ------------------------------------------------ under ph: the flag and the invariant
    c1 = Ctx(w, ph, T_I)
    L1 = Lg(w, ph, T_I)
    io = c1['i e. ( 0 ..^ %s )' % RG]
    ib = s([io, s([L1.ral, w.inst('rsp')], 'syl', '( %s -> ( i e. ( 0 ..^ %s ) -> ( i e. ( 0 ..^ %s ) /\\ -. %s ) ) )' % (ph, RG, NW, HIT('i')))],
           'mpd', '( %s -> ( i e. ( 0 ..^ %s ) /\\ -. %s ) )' % (ph, NW, HIT('i')))
    iw = s([ib], 'simpld', '( %s -> i e. ( 0 ..^ %s ) )' % (ph, NW))
    nh = s([ib], 'simprd', '( %s -> -. %s )' % (ph, HIT('i')))
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([iw, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ph, NW))
    cla = Closure(w, ph, {'i': ('NN0', inn), NW: ('NN0', L1.nw)})
    ine = s([s([cla.mem('i', 'RR'), ilt], 'ltned', '( %s -> i =/= %s )' % (ph, NW))], 'neneqd', '( %s -> -. i = %s )' % (ph, NW))
    nor = s([s([ine, nh], 'jca', '( %s -> ( -. i = %s /\\ -. %s ) )' % (ph, NW, HIT('i'))),
             s([], 'ioran', '( -. ( i = %s \\/ %s ) <-> ( -. i = %s /\\ -. %s ) )' % (NW, HIT('i'), NW, HIT('i')))], 'sylibr',
            '( %s -> -. ( i = %s \\/ %s ) )' % (ph, NW, HIT('i')))
    fz = s([nor], 'iffalsed', '( %s -> %s = (/) )' % (ph, FLC('i')))
    NI = '( %s ` i )' % NFM
    pm = '( %s /\\ m e. %s )' % (ph, NI)
    mm, mc = fam_unpack(w, pm, COND, 'i', Lft(w, pm, ph, inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl0 = s([mc, Lft(w, pm, ph, fz)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    part1 = s([cnfl_at(w, pm, mm, fl0, False)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ph, NI, CNFL))
    # the invariant at i
    iz = s([iw, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (ph, NW))
    zc = tup_comps(w, ph, Z0, s([], 'eqidd', '( %s -> %s = %s )' % (ph, Z0, Z0)), 'F', 'U', 'A', '(/)',
                   {'m': s([L1.fn], 'elexd', '( %s -> F e. _V )' % ph), 'u': s([L1.uw], 'elexd', '( %s -> U e. _V )' % ph),
                    'a': s([L1.an], 'elexd', '( %s -> A e. _V )' % ph), 'h': vex_(w, ph, '(/)')})
    tbz = s([c1[TBB('A')], s([zc['a'], w.inst('tmextbb')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBB(ZA(Z0), 'N'), TBB('A', 'N')))], 'mpbird',
            '( %s -> %s )' % (ph, TBB(ZA(Z0), 'N')))
    mlz = s([s([zc['m']], 'breq1d', '( %s -> ( %s < ( 2 ^ C ) <-> F < ( 2 ^ C ) ) )' % (ph, ZM(Z0))), c1['F < ( 2 ^ C )']], 'mpbird',
            '( %s -> %s < ( 2 ^ C ) )' % (ph, ZM(Z0)))
    tinv, cinv = inst(w, ph, 'exinv', {'Z': Z0, 'I': 'i'}, Bld(w, ph, c1, {'%s e. %s' % (Z0, STY): L1.z0, TBB(ZA(Z0), 'N'): tbz,
                                                                        '%s < ( 2 ^ C )' % ZM(Z0): mlz, 'i e. ( 0 ... %s )' % NW: iz}))
    assert cinv == 'E. c e. ( 0 ... ( N + i ) ) %s' % BODYI('i', 'c'), cinv
    # ------------------------------------------------ under pc: the witness c
    BI = BODYI('i', 'c')
    TC = ((T_I, 'c e. ( 0 ... ( N + i ) )'), BI)
    pc = cj(TC)
    B = Lg(w, pc, TC)
    c, mk = B.c, B.mk
    Lc = lambda st: Lft(w, pc, '( %s /\\ c e. ( 0 ... ( N + i ) ) )' % ph, Lft(w, '( %s /\\ c e. ( 0 ... ( N + i ) ) )' % ph, ph, st))
    iw_, nh_, inn_, iz_ = Lc(iw), Lc(nh), Lc(inn), Lc(iz)
    cz = c['c e. ( 0 ... ( N + i ) )']
    cn = s([cz, w.inst('elfznn0')], 'syl', '( %s -> c e. NN0 )' % pc)
    cle = s([cz, w.inst('elfzle2')], 'syl', '( %s -> c <_ ( N + i ) )' % pc)
    bdy = c[BI]
    TBC = TBB(ZA(Si('i')), 'c')
    MLT_ = '%s < ( 2 ^ ( C + ( B x. ( ( N + i ) - c ) ) ) )' % ZM(Si('i'))
    tbc = s([bdy], 'simp1d', '( %s -> %s )' % (pc, TBC))
    mlt = s([bdy], 'simp2d', '( %s -> %s )' % (pc, MLT_))
    i1z = s([iw_, w.inst('fzofzp1')], 'syl', '( %s -> ( i + 1 ) e. ( 0 ... %s ) )' % (pc, NW))
    i1n = s([inn_, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pc)
    i1le = s([i1z, w.inst('elfzle2')], 'syl', '( %s -> ( i + 1 ) <_ %s )' % (pc, NW))
    # the family at i
    pvi, SI = B.pv('i', iz_, inn_)
    PT = '( %s ` i )' % PV
    st, mz, uz, az = B.comps('i', iz_)
    # np at i: ( W ` i ) above the rest
    V1 = DRP('( i + 1 )')
    WI = '( W ` i )'
    win = s([B.ww, iw_, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, WI))
    v1w = s([B.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, V1))
    dr = s([B.ww, iw_, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (pc, DRP('i'), WI, V1))
    ec = s([win, v1w, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" %s "> ++ %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )'
           % (pc, WI, V1, WI, V1))
    e1 = s([s([dr], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( <" %s "> ++ %s ) ) )' % (pc, DRP('i'), WI, V1)), ec], 'eqtrd',
           '( %s -> ( encList ` %s ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (pc, DRP('i'), WI, V1))
    ew = encw(w, pc, WI, win)
    s4 = s([closed(w, pc, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % pc)
    elv = s([v1w, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, V1))
    ca1 = s([ew, wgcat(w, pc, '<" 4 ">', '( encList ` %s )' % V1, s4, elv), B.xw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ X ) = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) )'
            % (pc, WI, V1, WI, V1))
    ca2 = s([s4, elv, B.xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) = ( <" 4 "> ++ %s ) )' % (pc, V1, REST('( i + 1 )')))
    KT = EWg(WI, REST('( i + 1 )'))
    r1 = s([s([e1], 'oveq1d', '( %s -> %s = ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ X ) )' % (pc, REST('i'), WI, V1)), ca1], 'eqtrd',
           '( %s -> %s = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) )' % (pc, REST('i'), WI, V1))
    r2 = s([r1, s([ca2], 'oveq2d', '( %s -> ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) = %s )' % (pc, WI, V1, KT))], 'eqtrd',
           '( %s -> %s = %s )' % (pc, REST('i'), KT))
    kif = s([nh_], 'iffalsed', '( %s -> %s = %s )' % (pc, KV('i'), REST('i')))
    kv = s([SI.vals['K'][1], s([kif, r2], 'eqtrd', '( %s -> %s = %s )' % (pc, KV('i'), KT))], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (pc, PT, KT))
    # numbers
    NS = {v: ('NN0', c['%s e. NN0' % v]) for v in ('N', 'B', 'C', 'H', 'O', 'Q')}
    cl = Closure(w, pc, dict(NS, i=('NN0', inn_), c=('NN0', cn)))
    cl.leaf(NW, 'NN0', s([B.ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pc, NW)))
    DN = '( ( N + i ) - c )'
    dn = s([cn, cl.mem('( N + i )', 'NN0'), cle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (pc, DN))
    cld = Closure(w, pc, dict(NS, i=('NN0', inn_), c=('NN0', cn)))
    cld.leaf(DN, 'NN0', dn)
    CP = '( C + ( B x. %s ) )' % DN
    cpn = cld.mem(CP, 'NN0')
    BDN = '( B x. %s )' % DN
    c1le = linarith(w, pc, [cle, i1le, c['( N + %s ) <_ H' % NW]], '( c + 1 ) <_ H', closure=cl)
    one = linarith(w, pc, [c['1 <_ C'], cld.ge0(BDN)], '1 <_ %s' % CP, closure=cld, atoms=[BDN])
    bw = s([cl.mem('( i + 1 )', 'RR'), cl.mem(NW, 'RR'), cl.mem('B', 'RR'), cl.ge0('B'), i1le], 'lemul2ad',
           '( %s -> ( B x. ( i + 1 ) ) <_ ( B x. %s ) )' % (pc, NW))
    ob = linarith(w, pc, [bw, c['( C + ( B x. ( N + %s ) ) ) <_ O' % NW]], '( %s + ( B x. ( c + 1 ) ) ) <_ O' % CP, closure=cl, products=True)
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ %s ) )' % (pc, NW)), iw_, w.inst('fnfvelrn')], 'syl2anc',
           '( %s -> %s e. ran W )' % (pc, WI))
    wlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ B ) <-> %s < ( 2 ^ B ) ) )' % (WI, WI)), wr, c[RALB('W')]], 'rspcdva',
            '( %s -> %s < ( 2 ^ B ) )' % (pc, WI))
    # exBody
    m = {'D': PT, 'Z': Si('i'), 'F': WI, 'S': V1, 'N': 'c', 'C': CP, 'P': '( P ` 6 )', 'E': '( P ` 1 )'}
    ex = dict(B.ex)
    ex.update({'%s e. ( TM2Stk ` T )' % PT: SI.memb, '%s e. %s' % (Si('i'), STY): st, '%s e. NN0' % WI: win, '%s e. Word NN0' % V1: v1w,
               '( %s ` K ) = %s' % (PT, KT): kv, '( %s ` J ) = %s' % (PT, EWg('L', "X'")): SI.vals['J'][1],
               "( %s ` I' ) = %s" % (PT, ACCW(ZA(Si('i')))): SI.vals["I'"][1], '( %s ` K0 ) = %s' % (PT, K0V('i')): SI.vals['K0'][1],
               '( %s ` J0 ) = %s' % (PT, J0V('i')): SI.vals['J0'][1], 'c e. NN0': cn, '%s e. NN0' % CP: cpn, TBC: tbc,
               '%s < ( 2 ^ B )' % WI: wlt, '( c + 1 ) <_ H': c1le, MLT_: mlt, '1 <_ %s' % CP: one,
               '( %s + ( B x. ( c + 1 ) ) ) <_ O' % CP: ob})
    t, cc = inst(w, pc, 'tmiexb', m, Bld(w, pc, c, ex))
    C, D, n = triple_parts(cc)
    assert n == EXC_, n
    # the pre class: ( NFM ` i )
    C2 = CLN(LMG['B0'], NI, PT)
    t = hrssc(w, pc, mk['phm'], t, C, D, n, C2, clnss(w, pc, LMG['B0'], NI, S, PT, B.famss('i', inn_)))
    # the post: ZP = ( ExSt ` ( i + 1 ) )
    ZPi = '( %s ( L ExStOp G ) %s )' % (Si('i'), WI)
    sp = s([s([B.pS, inn_], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (pc, PH_S0)), w.inst('exstp1')], 'syl',
           '( %s -> %s = %s )' % (pc, Si('( i + 1 )'), ZPi))
    spe = s([sp], 'eqcomd', '( %s -> %s = %s )' % (pc, ZPi, Si('( i + 1 )')))
    FINC_ = NFLi('( %s = (/) \\/ %s = 1o )' % (V1, ZH(ZPi)))
    DF_ = tsub_text(DFIN_EXB, m)
    assert D == CLN('( P ` 1 )', FINC_, DF_), D
    pv1, S1 = B.pv('( i + 1 )', i1z, i1n)
    P1 = '( %s ` ( i + 1 ) )' % PV
    r1_, x1 = w.rewrite(DF_, {ZPi: (Si('( i + 1 )'), spe), PT: (PBG('i'), pvi)}, pc)
    chi = [('K', KV('i')), ("I'", ACCW(ZA(Si('i')))), ('K0', K0V('i')), ('J0', J0V('i')),
           ('K', KV('( i + 1 )')), ("I'", ACCW(ZA(Si('( i + 1 )')))), ('K0', K0V('( i + 1 )')), ('J0', J0V('( i + 1 )'))]
    assert x1 == chain_text('D', chi), x1
    nst, out2 = stk_normalize(w, pc, mk, 'D', B.dd, B.ne, chi, B.gam, K8)
    assert chain_text('D', out2) == PBG('( i + 1 )'), out2
    deq = s([s([r1_, nst], 'eqtrd', '( %s -> %s = %s )' % (pc, DF_, PBG('( i + 1 )'))), pv1], 'eqtr4d', '( %s -> %s = %s )' % (pc, DF_, P1))
    # the class: V1 = (/) <-> ( i + 1 ) = # W
    FINC2 = NFLi('( %s = (/) \\/ %s )' % (V1, HIT('( i + 1 )')))
    rc, xc = w.rewrite(FINC_, {ZPi: (Si('( i + 1 )'), spe)}, pc)
    assert xc == FINC2, xc
    nwn = s([B.ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pc, NW))
    sl = s([B.ww, i1z, s([nwn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (pc, NW, NW)), w.inst('swrdlen')], 'syl3anc',
           '( %s -> ( # ` %s ) = ( %s - ( i + 1 ) ) )' % (pc, V1, NW))
    h0 = s([s([s([], 'ovex', '%s e. _V' % V1)], 'a1i', '( %s -> %s e. _V )' % (pc, V1)), w.inst('hasheq0')], 'syl',
           '( %s -> ( ( # ` %s ) = 0 <-> %s = (/) ) )' % (pc, V1, V1))
    s0 = s([s([sl], 'eqeq1d', '( %s -> ( ( # ` %s ) = 0 <-> ( %s - ( i + 1 ) ) = 0 ) )' % (pc, V1, NW)),
            s([cl.mem(NW, 'CC'), cl.mem('( i + 1 )', 'CC')], 'subeq0ad', '( %s -> ( ( %s - ( i + 1 ) ) = 0 <-> %s = ( i + 1 ) ) )' % (pc, NW, NW))], 'bitrd',
           '( %s -> ( ( # ` %s ) = 0 <-> %s = ( i + 1 ) ) )' % (pc, V1, NW))
    ve = s([s([h0, s0], 'bitr3d', '( %s -> ( %s = (/) <-> %s = ( i + 1 ) ) )' % (pc, V1, NW)),
            s([s([], 'eqcom', '( %s = ( i + 1 ) <-> ( i + 1 ) = %s )' % (NW, NW))], 'a1i', '( %s -> ( %s = ( i + 1 ) <-> ( i + 1 ) = %s ) )' % (pc, NW, NW))],
           'bitrd', '( %s -> ( %s = (/) <-> ( i + 1 ) = %s ) )' % (pc, V1, NW))
    ob2 = s([ve], 'orbi1d', '( %s -> ( ( %s = (/) \\/ %s ) <-> ( ( i + 1 ) = %s \\/ %s ) ) )' % (pc, V1, HIT('( i + 1 )'), NW, HIT('( i + 1 )')))
    FC2 = '( %s = (/) \\/ %s )' % (V1, HIT('( i + 1 )'))
    V2 = 'if ( %s , 1o , (/) )' % FC2
    ib_ = s([ob2], 'ifbid', '( %s -> %s = %s )' % (pc, V2, FLC('( i + 1 )')))
    cq0 = s([s([s([ib_], 'eqeq2d', '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (pc, V2, FLC('( i + 1 )')))], 'adantr',
               '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (pc, V2, FLC('( i + 1 )')))], 'rabbidva',
            '( %s -> %s = %s )' % (pc, FINC2, NCL('( i + 1 )')))
    cq = s([rc, cq0], 'eqtrd', '( %s -> %s = %s )' % (pc, FINC_, NCL('( i + 1 )')))
    N1 = '( %s ` ( i + 1 ) )' % NFM
    cq2 = s([cq, s([famval(w, pc, COND, '( i + 1 )', i1n)], 'eqcomd', '( %s -> %s = %s )' % (pc, NCL('( i + 1 )'), N1))], 'eqtrd',
            '( %s -> %s = %s )' % (pc, FINC_, N1))
    ceq = s([clnneq(w, pc, '( P ` 1 )', cq2, FINC_, N1, DF_), clneq(w, pc, '( P ` 1 )', N1, deq, DF_, P1)], 'eqtrd',
            '( %s -> %s = %s )' % (pc, D, CLN('( P ` 1 )', N1, P1)))
    t, C, D, n = hrrw(w, pc, t, C2, D, n, deq=ceq)
    TRIP = '%s ( T TM2Hoare M ) <. %s , %s >.' % (C, D, n)
    tx = s([t], 'ex', '( ( %s /\\ c e. ( 0 ... ( N + i ) ) ) -> ( %s -> %s ) )' % (ph, BI, TRIP))
    lim = s([tx], 'rexlimdva', '( %s -> ( E. c e. ( 0 ... ( N + i ) ) %s -> %s ) )' % (ph, BI, TRIP))
    part2 = s([tinv, lim], 'mpd', '( %s -> %s )' % (ph, TRIP))
    w.qed([part1, part2], 'jca', ST_I)
    return w.run()


def tmiexgt():
    lab = 'tmiexgt'
    ph = PSI
    w = W(lab, 'The frame of Lean\'s ` extractGoF ` loop at the machine: for ` i <_ ExIt ` the class family is a set of states '
               'and the stack family a stack assignment (~ exstcl ), and at ` ExIt ` the test ` !flag ` fails (~ exitp ).')
    s = w.s
    TT = (PSI_T, 'i e. ( 0 ... %s )' % RG)
    pt = cj(TT)
    B = Lg(w, pt, TT)
    ii = B.c0['i e. ( 0 ... %s )' % RG]
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ %s )' % (pt, RG))
    cl = Closure(w, pt, {'i': ('NN0', inn), NW: ('NN0', B.nw)})
    cl.leaf(RG, 'NN0', B.rn)
    iw = linarith(w, pt, [ile, B.rle], 'i <_ %s' % NW, closure=cl, atoms=[RG])
    iz = s([s([inn, B.nw, iw], '3jca', '( %s -> ( i e. NN0 /\\ %s e. NN0 /\\ i <_ %s ) )' % (pt, NW, NW)), w.inst('elfz2nn0')], 'sylibr',
           '( %s -> i e. ( 0 ... %s ) )' % (pt, NW))
    pv, St = B.pv('i', iz, inn)
    body = LTYP[len('A. i e. ( 0 ... %s ) ' % RG):]
    typ = s([s([B.famss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))], 'ralrimiva', '( %s -> %s )' % (ph, LTYP))
    # the exit
    L = Lg(w, ph, PSI_T)
    NE = '( %s ` %s )' % (NFM, RG)
    pm = '( %s /\\ m e. %s )' % (ph, NE)
    mm, mc = fam_unpack(w, pm, COND, RG, Lft(w, pm, ph, L.rn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)))
    f1 = s([L.ror], 'iftrued', '( %s -> %s = 1o )' % (ph, FLC(RG)))
    fl1 = s([mc, Lft(w, pm, ph, f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    ex_ = s([cnfl_at(w, pm, mm, fl1, True)], 'ralrimiva', '( %s -> %s )' % (ph, LEXIT))
    w.qed([typ, ex_], 'jca', ST_T)
    return w.run()


def tmiexgl():
    lab = 'tmiexgl'
    ph = PSI
    w = W(lab, 'Lean\'s ` exLoop_runs ` at the machine: ~ tm2floopu at the families of the state sequence ( ` P\' ` a letter), '
               '` ExIt ` iterations of ` exBody ` (~ tmiexgi ), the frame by ~ tmiexgt .')
    s = w.s
    B = Lg(w, ph, PSI_T)
    B.deep('exg', 0)
    ex = dict(B.ex)
    fr = s([], 'tmiexgt', ST_T)
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    ex[LPER] = s([s([], 'tmiexgi', ST_I)], 'ralrimiva', '( %s -> %s )' % (ph, LPER))
    ex['%s e. NN0' % RG] = B.rn
    cl = Closure(w, ph, {v: ('NN0', B.c['%s e. NN0' % v]) for v in ('H', 'Q')})
    cl.leaf('L', 'NN0', B.l0)
    tq = s([s([B.c['Q e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` Q ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` Q ) e. NN0 )' % ph)
    cl.leaf('( TMB ` Q )', 'NN0', tq)
    ex['%s e. NN0' % EXC_] = cl.mem(EXC_, 'NN0')
    st = Bld(w, ph, B.c, ex)(LTREE)
    w.qed([st, w.inst('tm2floopu')], 'syl', ST_L)
    return w.run()


STMTS = {'tmiexgi': ST_I, 'tmiexgt': ST_T, 'tmiexgl': ST_L}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
