"""T9: exBody at the machine (Lean ` exBody_runs_none ` , ` exBody_runs_some ` ) on its installation predicate TMIexb.

  tmiexbn   the ` none ` branch after ` exPre ` : ` ite flag ` , ` popTop snap ; peekBra np `
  tmiexbs   the ` some S ` branch after ` exPre ` : ` ite flag ` , ` exSome ` (~ tmiexs )
  tmiexb    exBody_runs: ` exPre ` (~ tmiexp ), the two branches by cases, the budget (~ tmexprec , ~ tmexsomec )

    MM_DB=sorties/t9.mm python3 tools/gen/t9_l_exb.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import num
from t9_h_seq import ST_OPV
from t9_k_arith import ST_PC, ST_SC, EXY

SEL = sys.argv[1:]
LMB = FRAGS['exb'].lmap()
AZ = ZA('Z')
A1 = DP1('L', 'F', AZ)
SLP_ = SLF('L', 'F', AZ)
ESLI = '( ( encSlot ` %s ) ++ ( D ` I ) )' % SLP_
DP_ = UPS('D', ('K', NPREST), ('I', ESLI), ("I'", ACCW(A1)))
NSL = NFLi('%s = ( inr ` (/) )' % SLP_)
FINC = NFLi('( S = (/) \\/ %s = 1o )' % ZH(ZP))
WV = '( 2nd ` %s )' % SLP_
MMZ = '( %s x. %s )' % (ZM('Z'), PRL(WV))
ST_BN = '( ( %s /\\ %s = ( inr ` (/) ) ) -> %s )' % (cj(TREE_EXB), SLP_, TRI(CLN(LMB['Q1'], NSL, DP_), CLN('E', FINC, DFIN_EXB), '3'))
BSOME = '( 1 + %s )' % EXSOMEC('L', '( N + 1 )', 'B', '( # ` %s )' % WV, 'O')
ST_BS = '( ( %s /\\ %s =/= ( inr ` (/) ) ) -> %s )' % (cj(TREE_EXB), SLP_, TRI(CLN(LMB['Q1'], NSL, DP_), CLN('E', FINC, DFIN_EXB), BSOME))


class Exb(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        s = w.s
        ln, zs, fn, gn, vw = c0['L e. NN'], c0['Z e. %s' % STY], c0['F e. NN0'], c0['G e. NN0'], c0['S e. Word NN0']
        l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
        T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
        mz = s([zs, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, ZM('Z')))
        z2 = s([zs, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` Z ) e. %s )' % (ph, T23))
        uz = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ZU('Z')))
        z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` Z ) ) e. ( Tbl X. 2o ) )' % ph)
        az = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, AZ))
        xw, x2w, yw, rw = c0[WG('X')], c0[WG("X'")], c0[WG('Y')], c0[WG('R')]
        npg = enclg(w, ph, 'S', vw, 'X', xw)
        egy = ewg_(w, ph, 'G', gn, 'Y', yw)
        eqs = {'K': (EWg('F', NPREST), ewg_(w, ph, 'F', fn, NPREST, npg)), 'J': (EWg('L', "X'"), ewg_(w, ph, 'L', l0, "X'", x2w)),
               "I'": (ACCW(AZ), accw_g(w, ph, AZ, az, 'L', l0)), 'K0': (EWg(ZM('Z'), EWg('G', 'Y')), ewg_(w, ph, ZM('Z'), mz, EWg('G', 'Y'), egy)),
               'J0': (ENCL(ZU('Z'), 'R'), enclg(w, ph, ZU('Z'), uz, 'R', rw))}
        Base.__init__(self, w, ph, T, K8, 'exb', eqs)
        self.g(NPREST, npg); self.g(EWg('G', 'Y'), egy)
        self.ln, self.l0, self.zs, self.fn, self.gn, self.vw = ln, l0, zs, fn, gn, vw
        self.mz, self.uz, self.az = mz, uz, az
        dp = s([s([s([ln, fn], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % ph), az], 'jca', '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ %s e. Tbl ) )' % (ph, AZ)),
                w.inst('dpstepcl')], 'syl', '( %s -> %s e. ( Tbl X. NN0 ) )' % (ph, DPS_('L', 'F', AZ)))
        self.a1 = s([dp, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, A1))
        ML = '( 1 mod L )'
        self.mln = s([closed(w, ph, '1z', '1 e. ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ML))
        self.slt = s([self.a1, self.mln, w.inst('tblfv')], 'syl2anc', '( %s -> %s e. ( Word NN0 |_| 1o ) )' % (ph, SLP_))
        esw = s([self.slt, s([s([], 'ttabslotf', "encSlot : ( Word NN0 |_| 1o ) --> Word Gamma'")], 'ffvelcdmi',
                             "( %s e. ( Word NN0 |_| 1o ) -> ( encSlot ` %s ) e. Word Gamma' )" % (SLP_, SLP_))], 'syl',
                "( %s -> ( encSlot ` %s ) e. Word Gamma' )" % (ph, SLP_))
        self.esw = esw
        self.g(ESLI, wgcat(w, ph, '( encSlot ` %s )' % SLP_, '( D ` I )', esw, self.S0.vals['I'][2]))
        self.g(ACCW(A1), accw_g(w, ph, A1, self.a1, 'L', l0))
        self.opv = s([s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), s([zs, fn], 'jca', '( %s -> ( Z e. %s /\\ F e. NN0 ) )' % (ph, STY))],
                        'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ ( Z e. %s /\\ F e. NN0 ) ) )' % (ph, STY)), w.inst('exstopv')], 'syl',
                     '( %s -> %s = %s )' % (ph, ZP, STOPB('L', 'G', 'Z', 'F')))

    def dp(self):
        return self.S0.upd('K', NPREST, self.gam[NPREST]).upd('I', ESLI, self.gam[ESLI]).upd("I'", ACCW(A1), self.gam[ACCW(A1)])

    def fin_eq(self, zp, m_, u_, a_, h_, Kval):
        """( ph -> DFIN_EXB = chain ) : the components of ZP replaced (zp : tup_comps), the if on the hit flag by Kval
        (a pair ( text , step ( ph -> if ( ... ) = text ) )), the K0 / J0 values of D where they agree"""
        w, ph, s = self.w, self.ph, self.w.s
        IFK = 'if ( %s = 1o , ( <" 3 "> ++ %s ) , %s )' % (ZH(ZP), NPREST, NPREST)
        rules = {IFK: Kval, ZA(ZP): (a_, zp['a']), ZM(ZP): (m_, zp['m']), ZU(ZP): (u_, zp['u'])}
        r, x = w.rewrite(DFIN_EXB, rules, ph)
        return r, x


def exb_hdr(w, ph, T):
    B = Exb(w, ph, T)
    return B, w.s, B.c, B.mk


def tmiexbn():
    lab = 'tmiexbn'
    T = (TREE_EXB, '%s = ( inr ` (/) )' % SLP_)
    ph = cj(T)
    w = W(lab, 'The ` none ` branch of Lean\'s ` exBody ` at the machine: after ` exPre ` the flag is set, ` popTop snap ` removes '
               'the ` ket ` of the empty slot and ` peekBra np ` sets the flag to ` P\' = [] ` (Lean ` exNone_runs ` ).')
    B, s, c, mk = exb_hdr(w, ph, T)
    sn = c['%s = ( inr ` (/) )' % SLP_]
    R = B.run(B.dp())
    ex = {SSS(NSL): B.ss(NSL), SSS(FINC): B.ss(FINC), STMT(GT(LMB['X1'])): gotocl(w, ph, mk['tv'], LMB['X1'], None) if False else None}
    B.deep('exb', 1)
    ex[STMT(GT(LMB['X1']))] = gotocl(w, ph, mk['tv'], LMB['X1'], B.ex[LAB(LMB['X1'])])
    # the flag is 1o on NSL
    one = s([sn], 'iftrued', '( %s -> if ( %s = ( inr ` (/) ) , 1o , (/) ) = 1o )' % (ph, SLP_))
    pm = '( %s /\\ m e. %s )' % (ph, NSL)
    mm, mf = A8.nfl_unpack(w, pm, 'if ( %s = ( inr ` (/) ) , 1o , (/) )' % SLP_, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NSL)))
    ht = s([s([mf, Lft(w, pm, ph, one)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ph, NSL))
    ex['A. m e. %s ( TMfl ` m ) = 1o' % NSL] = ht
    ex[CTY('TMfl')] = B.ex[CTY('TMfl')]
    B.call(R, 'tm2lbrt', {'A': LMB['Q1'], 'C': 'TMfl', 'E': LMB['Q2'], 'Q': GT(LMB['X1']), 'N': NSL}, ex, [])
    # popTop snap : ( encSlot ` none ) = <" 3 ">
    sv = s([B.slt, w.inst('ttabslotv')], 'syl', '( %s -> ( encSlot ` %s ) = if ( %s = ( inr ` (/) ) , <" 3 "> , ( encList ` %s ) ) )' % (ph, SLP_, SLP_, WV))
    s3 = s([sv, s([sn], 'iftrued', '( %s -> if ( %s = ( inr ` (/) ) , <" 3 "> , ( encList ` %s ) ) = <" 3 "> )' % (ph, SLP_, WV))], 'eqtrd',
           '( %s -> ( encSlot ` %s ) = <" 3 "> )' % (ph, SLP_))
    S1 = R.S
    iv = s([S1.vals['I'][1], s([s3], 'oveq1d', '( %s -> %s = ( <" 3 "> ++ ( D ` I ) ) )' % (ph, ESLI))], 'eqtrd',
           '( %s -> ( %s ` I ) = ( <" 3 "> ++ ( D ` I ) ) )' % (ph, S1.D))
    g3 = closed(w, ph, 'gamma3', "3 e. Gamma'")
    pi = A8.pop_iface(w, ph, mk, NSL, B.ss(NSL), '3', g3, NSL, s([s([], 'ssid', '%s C_ %s' % (NSL, NSL))], 'a1i', '( %s -> %s C_ %s )' % (ph, NSL, NSL)))
    B.call(R, 'tm2lpop', {'A': LMB['Q2'], 'E': LMB['Q3'], 'K': 'I', 'F': PID, 'Z': '3', 'X': '( D ` I )', 'N': NSL, "N'": NSL},
           {'( %s ` I ) = ( <" 3 "> ++ ( D ` I ) )' % S1.D: iv, "3 e. Gamma'": g3,
            'A. r e. %s ( %s ` <. r , ( inl ` 3 ) >. ) e. %s' % (NSL, PID, NSL): pi, SSS(NSL): B.ss(NSL)},
           [('I', '( D ` I )', B.gam['( D ` I )'])])
    # peekBra np into FINC
    S2 = R.S
    V_ = NPREST
    vn0 = encl_ne0(w, ph, 'S', B.vw, 'X', c[WG('X')])
    eq, hg, tg = A8.word_split(w, ph, V_, B.gam[V_], vn0)
    HD, TL = A8.HD0(V_), A8.TL1(V_)
    kv = s([S2.vals['K'][1], eq], 'eqtrd', '( %s -> ( %s ` K ) = ( <" %s "> ++ %s ) )' % (ph, S2.D, HD, TL))
    hb = s([B.vw, c[WG('X')], w.inst('tmexhdb')], 'syl2anc', '( %s -> ( %s = 2 <-> S = (/) ) )' % (ph, HD))
    T1 = ZT(ZM('Z'), ZU('Z'), A1, '(/)')
    zeq = s([B.opv, s([sn], 'iftrued', '( %s -> %s = %s )' % (ph, STOPB('L', 'G', 'Z', 'F'), T1))], 'eqtrd', '( %s -> %s = %s )' % (ph, ZP, T1))
    zp = tup_comps(w, ph, ZP, zeq, ZM('Z'), ZU('Z'), A1, '(/)', {'m': vex_(w, ph, ZM('Z')), 'u': vex_(w, ph, ZU('Z')), 'a': vex_(w, ph, A1), 'h': vex_(w, ph, '(/)')})
    nh = s([s([zp['h']], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (ph, ZH(ZP))),
            s([s([s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')], 'a1i', '( %s -> -. (/) = 1o )' % ph)], 'mtbird', '( %s -> -. %s = 1o )' % (ph, ZH(ZP)))
    orb = s([s([nh, w.inst('biorf')], 'syl', '( %s -> ( S = (/) <-> ( %s = 1o \\/ S = (/) ) ) )' % (ph, ZH(ZP))),
             s([s([], 'orcom', '( ( %s = 1o \\/ S = (/) ) <-> ( S = (/) \\/ %s = 1o ) )' % (ZH(ZP), ZH(ZP)))], 'a1i',
               '( %s -> ( ( %s = 1o \\/ S = (/) ) <-> ( S = (/) \\/ %s = 1o ) ) )' % (ph, ZH(ZP), ZH(ZP)))], 'bitrd',
            '( %s -> ( S = (/) <-> ( S = (/) \\/ %s = 1o ) ) )' % (ph, ZH(ZP)))
    hb2 = s([hb, orb], 'bitrd', '( %s -> ( %s = 2 <-> ( S = (/) \\/ %s = 1o ) ) )' % (ph, HD, ZH(ZP)))
    FL = 'if ( ( S = (/) \\/ %s = 1o ) , 1o , (/) )' % ZH(ZP)
    ifeq = s([hb2], 'ifbid', '( %s -> if ( %s = 2 , 1o , (/) ) = %s )' % (ph, HD, FL))
    pk = A8.peek_iface(w, ph, mk, RDBRA, HD, hg, ifeq, FL)
    pkN = s([B.ss(NSL), pk, w.inst('ssralv')], 'sylc', '( %s -> A. r e. %s ( TMrdBra ` <. r , ( inl ` %s ) >. ) e. %s )' % (ph, NSL, HD, FINC))
    B.call(R, 'tm2lpk', {'A': LMB['Q3'], 'E': 'E', 'K': 'K', 'F': RDBRA, 'Z': HD, 'X': TL, 'N': NSL, "N'": FINC},
           {'( %s ` K ) = ( <" %s "> ++ %s )' % (S2.D, HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
            'A. r e. %s ( TMrdBra ` <. r , ( inl ` %s ) >. ) e. %s' % (NSL, HD, FINC): pkN, SSS(NSL): B.ss(NSL), SSS(FINC): B.ss(FINC)}, [])
    e, nrm, out2 = renorm(w, ph, B, R, [('K', NPREST), ('I', ESLI), ("I'", ACCW(A1))], K8)
    assert out2 == [('K', NPREST), ("I'", ACCW(A1))], out2
    # DFIN_EXB -> the same chain
    IFK = 'if ( %s = 1o , ( <" 3 "> ++ %s ) , %s )' % (ZH(ZP), NPREST, NPREST)
    ik = s([nh], 'iffalsed', '( %s -> %s = %s )' % (ph, IFK, NPREST))
    r1, x1 = B.fin_eq(zp, ZM('Z'), ZU('Z'), A1, '(/)', (NPREST, ik))
    K0v, J0v = EWg(ZM('Z'), EWg('G', 'Y')), ENCL(ZU('Z'), 'R')
    k0 = s([c['( D ` K0 ) = %s' % K0v]], 'eqcomd', '( %s -> %s = ( D ` K0 ) )' % (ph, K0v))
    j0 = s([c['( D ` J0 ) = %s' % J0v]], 'eqcomd', '( %s -> %s = ( D ` J0 ) )' % (ph, J0v))
    r2, x2 = w.rewrite(x1, {K0v: ('( D ` K0 )', k0), J0v: ('( D ` J0 )', j0)}, ph)
    chi = [('K', NPREST), ("I'", ACCW(A1)), ('K0', '( D ` K0 )'), ('J0', '( D ` J0 )')]
    assert x2 == chain_text('D', chi), x2
    n3, out3 = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chi, B.gam, K8)
    assert out3 == [('K', NPREST), ("I'", ACCW(A1))], out3
    fe = s([s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, DFIN_EXB, x2)), n3], 'eqtrd', '( %s -> %s = %s )' % (ph, DFIN_EXB, nrm))
    Dc = triple_D(R.cur)
    deq = s([e, s([fe], 'eqcomd', '( %s -> %s = %s )' % (ph, nrm, DFIN_EXB))], 'eqtrd', '( %s -> %s = %s )' % (ph, Dc, DFIN_EXB))
    t, C, D, n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, 'E', FINC, deq, Dc, DFIN_EXB))
    neq = lineq(w, ph, n, '3', closure=Closure(w, ph, {}))
    hrrw(w, ph, t, C, D, n, neq=neq, qed=True)
    return w.run()



def tmiexbs():
    lab = 'tmiexbs'
    T = (TREE_EXB, '%s =/= ( inr ` (/) )' % SLP_)
    ph = cj(T)
    w = W(lab, 'The ` some S ` branch of Lean\'s ` exBody ` at the machine: after ` exPre ` the flag is clear and ` exSome ` '
               '(~ tmiexs ) runs with the witness ` S ` of slot ` 1 mod L ` , the table bounded by ` N + 1 ` (~ ttabtbdp ).')
    B, s, c, mk = exb_hdr(w, ph, T)
    ss_ = c['%s =/= ( inr ` (/) )' % SLP_]
    nsl = s([ss_], 'neneqd', '( %s -> -. %s = ( inr ` (/) ) )' % (ph, SLP_))
    B.deep('exb', 1)
    R = B.run(B.dp())
    ex = {SSS(NSL): B.ss(NSL), STMT(GT(LMB['Q2'])): gotocl(w, ph, mk['tv'], LMB['Q2'], B.ex[LAB(LMB['Q2'])]), CTY('TMfl'): B.ex[CTY('TMfl')]}
    z0 = s([nsl], 'iffalsed', '( %s -> if ( %s = ( inr ` (/) ) , 1o , (/) ) = (/) )' % (ph, SLP_))
    pm = '( %s /\\ m e. %s )' % (ph, NSL)
    mm, mf = A8.nfl_unpack(w, pm, 'if ( %s = ( inr ` (/) ) , 1o , (/) )' % SLP_, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NSL)))
    f0 = s([mf, Lft(w, pm, ph, z0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ex['A. m e. %s -. ( TMfl ` m ) = 1o' % NSL] = s([not1o(w, pm, f0, 'TMfl', 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (ph, NSL))
    B.call(R, 'tm2fbrg', {'A': LMB['Q1'], 'C': 'TMfl', 'E': LMB['X1'], 'Q': GT(LMB['Q2']), 'N': NSL}, ex, [])
    # the witness and its bounds
    cl = Closure(w, ph, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'C': ('NN0', c['C e. NN0']), 'O': ('NN0', c['O e. NN0'])})
    sv = s([B.slt, w.inst('ttabslotv')], 'syl', '( %s -> ( encSlot ` %s ) = if ( %s = ( inr ` (/) ) , <" 3 "> , ( encList ` %s ) ) )' % (ph, SLP_, SLP_, WV))
    se = s([sv, s([nsl], 'iffalsed', '( %s -> if ( %s = ( inr ` (/) ) , <" 3 "> , ( encList ` %s ) ) = ( encList ` %s ) )' % (ph, SLP_, WV, WV))], 'eqtrd',
           '( %s -> ( encSlot ` %s ) = ( encList ` %s ) )' % (ph, SLP_, WV))
    S1 = R.S
    iv = s([S1.vals['I'][1], s([se], 'oveq1d', '( %s -> %s = %s )' % (ph, ESLI, ENCL(WV, '( D ` I )')))], 'eqtrd',
           '( %s -> ( %s ` I ) = %s )' % (ph, S1.D, ENCL(WV, '( D ` I )')))
    tb1 = s([s([s([B.ln, B.fn, B.az], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ %s e. Tbl ) )' % (ph, AZ)),
                s([c['N e. NN0'], c['B e. NN0'], c['F < ( 2 ^ B )']], '3jca', '( %s -> ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) )' % ph), c[TBB(AZ)]], '3jca',
               '( %s -> ( ( L e. NN /\\ F e. NN0 /\\ %s e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) /\\ %s ) )' % (ph, AZ, TBB(AZ))),
             w.inst('ttabtbdp')], 'syl', '( %s -> %s )' % (ph, TBB(A1, '( N + 1 )')))
    ML = '( 1 mod L )'
    TBI = lambda d: '( ( %s ` %s ) =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` ( %s ` %s ) ) ) <_ ( N + 1 ) /\\ A. q e. ran ( 2nd ` ( %s ` %s ) ) q < ( 2 ^ B ) ) )' % (A1, d, A1, d, A1, d)
    idd = s([], 'id', '( d = %s -> d = %s )' % (ML, ML))
    cg, new = w.wcongr(TBI('d'), {'d': ML}, 'd = %s' % ML, {'d': idd})
    at = s([cg, B.mln, tb1], 'rspcdva', '( %s -> %s )' % (ph, TBI(ML)))
    both = s([ss_, at], 'mpd', '( %s -> ( ( # ` %s ) <_ ( N + 1 ) /\\ A. q e. ran %s q < ( 2 ^ B ) ) )' % (ph, WV, WV))
    wl = s([both], 'simpld', '( %s -> ( # ` %s ) <_ ( N + 1 ) )' % (ph, WV))
    wq = s([both], 'simprd', '( %s -> A. q e. ran %s q < ( 2 ^ B ) )' % (ph, WV))
    wp = s([wq, s([s([], 'breq1', '( q = p -> ( q < ( 2 ^ B ) <-> p < ( 2 ^ B ) ) )')], 'cbvralvw',
                  '( A. q e. ran %s q < ( 2 ^ B ) <-> A. p e. ran %s p < ( 2 ^ B ) )' % (WV, WV))], 'sylib', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (ph, WV))
    wa = s([wq, s([s([], 'breq1', '( q = a -> ( q < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
                  '( A. q e. ran %s q < ( 2 ^ B ) <-> %s )' % (WV, RALB(WV)))], 'sylib', '( %s -> %s )' % (ph, RALB(WV)))
    wvw = s([B.slt, w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, WV))
    pr = s([wvw, c['B e. NN0'], wp, w.inst('tplprodle')], 'syl3anc', '( %s -> %s <_ ( 2 ^ ( ( # ` %s ) x. B ) ) )' % (ph, PRL(WV), WV))
    LWV = '( # ` %s )' % WV
    cl.leaf(LWV, 'NN0', s([wvw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LWV)))
    prn = s([s([wvw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, WV)), w.inst('xp1st')], 'syl',
            '( %s -> %s e. NN0 )' % (ph, PRL(WV)))
    EY = '( %s x. B )' % LWV
    eyn = s([cl.mem(LWV, 'NN0'), c['B e. NN0']], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, EY))
    pw = lambda e, en: s([s([closed(w, ph, '2nn', '2 e. NN'), en, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, e))], 'nnred',
                         '( %s -> ( 2 ^ %s ) e. RR )' % (ph, e))
    p_c, p_y, p_o = pw('C', c['C e. NN0']), pw(EY, eyn), pw('O', c['O e. NN0'])
    mr = s([B.mz], 'nn0red', '( %s -> %s e. RR )' % (ph, ZM('Z')))
    prr = s([prn], 'nn0red', '( %s -> %s e. RR )' % (ph, PRL(WV)))
    l1 = s([prr, p_y, mr, s([B.mz], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, ZM('Z'))), pr], 'lemul2ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. ( 2 ^ %s ) ) )' % (ph, ZM('Z'), PRL(WV), ZM('Z'), EY))
    pyrp = s([s([closed(w, ph, '2nn', '2 e. NN'), eyn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, EY))], 'nnrpd',
             '( %s -> ( 2 ^ %s ) e. RR+ )' % (ph, EY))
    lm = s([mr, p_c, pyrp], 'ltmul1d', '( %s -> ( %s < ( 2 ^ C ) <-> ( %s x. ( 2 ^ %s ) ) < ( ( 2 ^ C ) x. ( 2 ^ %s ) ) ) )' % (ph, ZM('Z'), ZM('Z'), EY, EY))
    l2 = s([c['%s < ( 2 ^ C )' % ZM('Z')], lm], 'mpbid', '( %s -> ( %s x. ( 2 ^ %s ) ) < ( ( 2 ^ C ) x. ( 2 ^ %s ) ) )' % (ph, ZM('Z'), EY, EY))
    ea = s([closed(w, ph, '2cn', '2 e. CC'), c['C e. NN0'], eyn, w.inst('expadd')], 'syl3anc', '( %s -> ( 2 ^ ( C + %s ) ) = ( ( 2 ^ C ) x. ( 2 ^ %s ) ) )' % (ph, EY, EY))
    bw = s([cl.mem(LWV, 'RR'), cl.mem('( N + 1 )', 'RR'), cl.mem('B', 'RR'), cl.ge0('B'), wl], 'lemul1ad',
           '( %s -> ( %s x. B ) <_ ( ( N + 1 ) x. B ) )' % (ph, LWV))
    dle = linarith(w, ph, [bw, c['( C + ( B x. ( N + 1 ) ) ) <_ O']], '( C + %s ) <_ O' % EY, closure=cl, products=True)
    def pmono(e1, e1n, le_):
        """( 2 ^ e1 ) <_ ( 2 ^ O )"""
        ez = s([s([e1n], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e1)), cl.mem('O', 'ZZ'), le_], '3jca', '( %s -> ( %s e. ZZ /\\ O e. ZZ /\\ %s <_ O ) )' % (ph, e1, e1))
        eu = s([ez, w.inst('eluz2')], 'sylibr', '( %s -> O e. ( ZZ>= ` %s ) )' % (ph, e1))
        return s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), eu, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ %s ) <_ ( 2 ^ O ) )' % (ph, e1))
    cyn = s([c['C e. NN0'], eyn], 'nn0addcld', '( %s -> ( C + %s ) e. NN0 )' % (ph, EY))
    po = pmono('( C + %s )' % EY, cyn, dle)
    RA = '( ( 2 ^ C ) x. ( 2 ^ %s ) )' % EY
    rr_ = s([p_c, p_y], 'remulcld', '( %s -> %s e. RR )' % (ph, RA))
    ra_o = s([ea, po], 'eqbrtrrd', '( %s -> %s <_ ( 2 ^ O ) )' % (ph, RA))
    mpr = s([mr, prr], 'remulcld', '( %s -> %s e. RR )' % (ph, MMZ))
    mpy = s([mr, p_y], 'remulcld', '( %s -> ( %s x. ( 2 ^ %s ) ) e. RR )' % (ph, ZM('Z'), EY))
    t1 = s([mpr, mpy, rr_, l1, l2], 'lelttrd', '( %s -> %s < %s )' % (ph, MMZ, RA))
    fpo = s([mpr, rr_, p_o, t1, ra_o], 'ltletrd', '( %s -> %s < ( 2 ^ O ) )' % (ph, MMZ))
    clo = linarith(w, ph, [c['( C + ( B x. ( N + 1 ) ) ) <_ O'], cl.ge0('B'), cl.ge0('N')], 'C <_ O', closure=cl, products=True)
    mo = s([mr, p_c, p_o, c['%s < ( 2 ^ C )' % ZM('Z')], pmono('C', c['C e. NN0'], clo)], 'ltletrd', '( %s -> %s < ( 2 ^ O ) )' % (ph, ZM('Z')))
    cy = linarith(w, ph, [c['1 <_ C']], '%s < ( C + %s )' % (EY, EY), closure=cl, atoms=[EY])
    ey1 = s([s([closed(w, ph, '2re', '2 e. RR'), s([eyn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, EY)), s([cyn], 'nn0zd', '( %s -> ( C + %s ) e. ZZ )' % (ph, EY))],
               '3jca', '( %s -> ( 2 e. RR /\\ %s e. ZZ /\\ ( C + %s ) e. ZZ ) )' % (ph, EY, EY)),
             s([closed(w, ph, '1lt2', '1 < 2'), cy], 'jca', '( %s -> ( 1 < 2 /\\ %s < ( C + %s ) ) )' % (ph, EY, EY)), w.inst('ltexp2a')], 'syl2anc',
            '( %s -> ( 2 ^ %s ) < ( 2 ^ ( C + %s ) ) )' % (ph, EY, EY))
    pcy = pw('( C + %s )' % EY, cyn)
    pwo = s([prr, p_y, pcy, pr, ey1], 'lelttrd', '( %s -> %s < ( 2 ^ ( C + %s ) ) )' % (ph, PRL(WV), EY))
    pwo2 = s([prr, pcy, p_o, pwo, po], 'ltletrd', '( %s -> %s < ( 2 ^ O ) )' % (ph, PRL(WV)))
    # exSome
    K3 = 'if ( G < %s , ( <" 3 "> ++ %s ) , %s )' % (MMZ, NPREST, NPREST)
    k3g = s([wgcat(w, ph, '<" 3 ">', NPREST, s([closed(w, ph, 'gamma3', "3 e. Gamma'")], 's1cld', "( %s -> <\" 3 \"> e. Word Gamma' )" % ph), B.gam[NPREST]),
             B.gam[NPREST]], 'ifcld', "( %s -> %s e. Word Gamma' )" % (ph, K3))
    B.g(K3, k3g)
    gae = B.g(ACCW('EmptyTbl'), accw_g(w, ph, 'EmptyTbl', closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl'), 'L', B.l0))
    mmn = s([B.mz, prn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, MMZ))
    gk0 = B.g(EWg(MMZ, EWg('G', 'Y')), ewg_(w, ph, MMZ, mmn, EWg('G', 'Y'), B.gam[EWg('G', 'Y')]))
    WU = '( %s ++ %s )' % (WV, ZU('Z'))
    wuw = s([wvw, B.uz, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ph, WU))
    gj0 = B.g(ENCL(WU, 'R'), enclg(w, ph, WU, wuw, 'R', c[WG('R')]))
    FINS = NFLi('( G < %s \\/ S = (/) )' % MMZ)
    B.call(R, 'tmiexs', {'W': WV, 'Z': '( D ` I )', 'A': A1, 'N': '( N + 1 )', 'F': ZM('Z'), 'G': 'G', 'H': 'O', 'U': ZU('Z'), 'S': 'S',
                         'X': 'X', "X'": "X'", 'Y': 'Y', 'R': 'R', 'L': 'L', 'B': 'B', 'P': PL('P', 4), 'E': 'E'},
           {'( %s ` I ) = %s' % (S1.D, ENCL(WV, '( D ` I )')): iv, 'L e. NN0': B.l0, '%s e. Tbl' % A1: B.a1,
            '( N + 1 ) e. NN0': s([c['N e. NN0'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph), TBB(A1, '( N + 1 )'): tb1,
            '%s e. Word NN0' % WV: wvw, RALB(WV): wa, '%s e. NN0' % ZM('Z'): B.mz, '%s e. Word NN0' % ZU('Z'): B.uz,
            '%s < ( 2 ^ O )' % ZM('Z'): mo, '%s < ( 2 ^ O )' % PRL(WV): pwo2, '%s < ( 2 ^ O )' % MMZ: fpo},
           [('K', K3, k3g), ('I', '( D ` I )', B.gam['( D ` I )']), ("I'", ACCW('EmptyTbl'), gae), ('K0', EWg(MMZ, EWg('G', 'Y')), gk0),
            ('J0', ENCL(WU, 'R'), gj0)], pre=(NSL, B.ss(NSL)))
    e, nrm, out2 = renorm(w, ph, B, R, [('K', NPREST), ('I', ESLI), ("I'", ACCW(A1))], K8)
    assert out2 == [('K', K3), ("I'", ACCW('EmptyTbl')), ('K0', EWg(MMZ, EWg('G', 'Y'))), ('J0', ENCL(WU, 'R'))], out2
    # the next state's components
    HT = 'if ( G < %s , 1o , (/) )' % MMZ
    T2 = ZT(MMZ, WU, 'EmptyTbl', HT)
    zeq = s([B.opv, s([nsl], 'iffalsed', '( %s -> %s = %s )' % (ph, STOPB('L', 'G', 'Z', 'F'), T2))], 'eqtrd', '( %s -> %s = %s )' % (ph, ZP, T2))
    hv = s([s([s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V')], 'ifex', '%s e. _V' % HT)], 'a1i', '( %s -> %s e. _V )' % (ph, HT))
    zp = tup_comps(w, ph, ZP, zeq, MMZ, WU, 'EmptyTbl', HT, {'m': vex_(w, ph, MMZ), 'u': vex_(w, ph, WU), 'a': vex_(w, ph, 'EmptyTbl'), 'h': hv})
    if1 = s([], 'tmexif1', '( %s = 1o <-> G < %s )' % (HT, MMZ))
    hh = s([s([zp['h']], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (ph, ZH(ZP), HT)), s([if1], 'a1i', '( %s -> ( %s = 1o <-> G < %s ) )' % (ph, HT, MMZ))],
           'bitrd', '( %s -> ( %s = 1o <-> G < %s ) )' % (ph, ZH(ZP), MMZ))
    IFK = 'if ( %s = 1o , ( <" 3 "> ++ %s ) , %s )' % (ZH(ZP), NPREST, NPREST)
    ik = s([hh], 'ifbid', '( %s -> %s = %s )' % (ph, IFK, K3))
    r1, x1 = B.fin_eq(zp, MMZ, WU, 'EmptyTbl', HT, (K3, ik))
    assert x1 == nrm, (x1, nrm)
    Dc = triple_D(R.cur)
    deq = s([e, s([r1], 'eqcomd', '( %s -> %s = %s )' % (ph, nrm, DFIN_EXB))], 'eqtrd', '( %s -> %s = %s )' % (ph, Dc, DFIN_EXB))
    # the class
    ob = s([s([hh], 'orbi2d', '( %s -> ( ( S = (/) \\/ %s = 1o ) <-> ( S = (/) \\/ G < %s ) ) )' % (ph, ZH(ZP), MMZ)),
            s([s([], 'orcom', '( ( S = (/) \\/ G < %s ) <-> ( G < %s \\/ S = (/) ) )' % (MMZ, MMZ))], 'a1i',
              '( %s -> ( ( S = (/) \\/ G < %s ) <-> ( G < %s \\/ S = (/) ) ) )' % (ph, MMZ, MMZ))], 'bitrd',
           '( %s -> ( ( S = (/) \\/ %s = 1o ) <-> ( G < %s \\/ S = (/) ) ) )' % (ph, ZH(ZP), MMZ))
    V1 = 'if ( ( G < %s \\/ S = (/) ) , 1o , (/) )' % MMZ
    V2 = 'if ( ( S = (/) \\/ %s = 1o ) , 1o , (/) )' % ZH(ZP)
    ib = s([s([ob], 'ifbid', '( %s -> %s = %s )' % (ph, V2, V1))], 'eqcomd', '( %s -> %s = %s )' % (ph, V1, V2))
    cq = s([s([s([ib], 'eqeq2d', '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ph, V1, V2))], 'adantr',
              '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ph, V1, V2))], 'rabbidva', '( %s -> %s = %s )' % (ph, FINS, FINC))
    t, C, D, n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=s([clnneq(w, ph, 'E', cq, FINS, FINC, Dc), clneq(w, ph, 'E', FINC, deq, Dc, DFIN_EXB)], 'eqtrd',
                                                           '( %s -> %s = %s )' % (ph, CLN('E', FINS, Dc), CLN('E', FINC, DFIN_EXB))))
    assert n == BSOME, (n, BSOME)
    qed_as(w, t, ST_BS)
    return w.run()



def tmiexb():
    lab = 'tmiexb'
    ph = cj(TREE_EXB)
    w = W(lab, 'Lean\'s ` exBody_runs_none ` and ` exBody_runs_some ` at the machine, in one statement: wherever ` exBody np nL snap '
               'acc s t nm nu ` is installed, with ` p ` above the rest ` P\' ` of the pool on ` np ` and the state ` Z = ( m , used , t , '
               'hit ) ` on ` nm ` , ` nu ` , ` acc ` , one element runs and the stacks hold the next state ` ( Z ( L ExStOp n ) p ) ` , the '
               'flag says whether to stop, ` np ` carries the marker exactly at a hit (~ tmiexp , ~ tmiexbn , ~ tmiexbs ), within '
               '` exC L Nb X = 20 ( L + 1 ) ^ 2 ( Nb + 2 ) B X ` steps.')
    B, s, c, mk = exb_hdr(w, ph, TREE_EXB)
    R = B.run()
    B.call(R, 'tmiexp', {'K': 'K', 'J': 'J', 'I': 'I', "I'": "I'", 'I"': 'I"', 'I0': 'I0', 'J0': 'J0', 'F': 'F', 'L': 'L', 'A': AZ, 'N': 'N',
                         'B': 'B', 'X': NPREST, 'Y': "X'", 'P': PL('P', 3), 'E': PL('P', 0)}, {'%s e. Tbl' % AZ: B.az},
           [('K', NPREST, B.gam[NPREST]), ('I', ESLI, B.gam[ESLI]), ("I'", ACCW(A1), B.gam[ACCW(A1)])])
    t0, C0, D0, n0 = R.tri, R.C0, R.cur, R.n
    assert D0 == CLN(LMB['Q1'], NSL, DP_), D0
    EXC_ = EXC('L', 'H', 'Q')
    cl = Closure(w, ph, {v: ('NN0', c['%s e. NN0' % v]) for v in ('N', 'B', 'H', 'O', 'Q')})
    cl.leaf('L', 'NN0', B.l0)
    TQ = '( TMB ` Q )'
    tqn = s([c['Q e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TQ))
    l1n = s([B.ln, w.inst('peano2nn')], 'syl', '( %s -> ( L + 1 ) e. NN )' % ph)
    l2n = s([l1n, closed(w, ph, '2nn0', '2 e. NN0'), w.inst('nnexpcl')], 'syl2anc', '( %s -> ( ( L + 1 ) ^ 2 ) e. NN )' % ph)
    h2n = s([c['H e. NN0'], closed(w, ph, '2nn', '2 e. NN'), w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> ( H + 2 ) e. NN )' % ph)
    lhn = s([l2n, h2n, w.inst('nnmulcl')], 'syl2anc', '( %s -> ( ( ( L + 1 ) ^ 2 ) x. ( H + 2 ) ) e. NN )' % ph)
    eyn = s([lhn, tqn, w.inst('nnmulcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, EXY))
    cl.leaf(EXY, 'NN0', s([eyn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, EXY)))
    ey1 = s([eyn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, EXY))
    pc_in = s([s([B.l0, c['N e. NN0'], c['H e. NN0']], '3jca', '( %s -> ( L e. NN0 /\\ N e. NN0 /\\ H e. NN0 ) )' % ph),
               s([c['B e. NN0'], c['Q e. NN0']], 'jca', '( %s -> ( B e. NN0 /\\ Q e. NN0 ) )' % ph),
               s([c['( N + 1 ) <_ H'], c['B <_ Q']], 'jca', '( %s -> ( ( N + 1 ) <_ H /\\ B <_ Q ) )' % ph)], '3jca',
              '( %s -> %s )' % (ph, ST_PC.split(' -> ', 1)[0][2:]))
    pcb = s([pc_in, w.inst('tmexprec')], 'syl', '( %s -> ( %s + 1 ) <_ ( 7 x. %s ) )' % (ph, EXPREC('L', 'N', 'B'), EXY))
    EP = EXPREC('L', 'N', 'B')
    outs = []
    for none in (True, False):
        cnd = ('%s = ( inr ` (/) )' if none else '%s =/= ( inr ` (/) )') % SLP_
        pc = '( %s /\\ %s )' % (ph, cnd)
        Lc = lambda st: Lft(w, pc, ph, st)
        tb = s([], 'tmiexbn' if none else 'tmiexbs', ST_BN if none else ST_BS)
        nb = '3' if none else BSOME
        t2 = hrseq(w, pc, Lc(mk['phm']), Lc(t0), tb, C0, D0, CLN('E', FINC, DFIN_EXB), n0, nb)
        NT = '( %s + %s )' % (n0, nb)
        clc = Closure(w, pc, {})
        for k, (kind, st) in list({v: ('NN0', c['%s e. NN0' % v]) for v in ('N', 'B', 'H', 'O', 'Q')}.items()):
            clc.leaf(k, kind, Lc(st))
        clc.leaf('L', 'NN0', Lc(B.l0))
        clc.leaf(EXY, 'NN0', Lc(cl.mem(EXY, 'NN0')))
        for b_ in ('B', 'Q', 'O'):
            tb_ = '( TMB ` %s )' % b_
            clc.leaf(tb_, 'NN0', s([s([Lc(c['%s e. NN0' % b_]), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, tb_))], 'nnnn0d',
                                   '( %s -> %s e. NN0 )' % (pc, tb_)))
        if none:
            le = linarith(w, pc, [Lc(pcb), Lc(ey1)], '%s <_ %s' % (NT, EXC_), closure=clc, atoms=[EP, EXY])
        else:
            # # S <_ N + 1 , then exSomeC_le
            tb1 = s([s([s([Lc(B.ln), Lc(B.fn), Lc(B.az)], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ %s e. Tbl ) )' % (pc, AZ)),
                        s([Lc(c['N e. NN0']), Lc(c['B e. NN0']), Lc(c['F < ( 2 ^ B )'])], '3jca', '( %s -> ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) )' % pc),
                        Lc(c[TBB(AZ)])], '3jca',
                       '( %s -> ( ( L e. NN /\\ F e. NN0 /\\ %s e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) /\\ %s ) )' % (pc, AZ, TBB(AZ))),
                     w.inst('ttabtbdp')], 'syl', '( %s -> %s )' % (pc, TBB(A1, '( N + 1 )')))
            ML = '( 1 mod L )'
            TBI = lambda d: '( ( %s ` %s ) =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` ( %s ` %s ) ) ) <_ ( N + 1 ) /\\ A. q e. ran ( 2nd ` ( %s ` %s ) ) q < ( 2 ^ B ) ) )' % (A1, d, A1, d, A1, d)
            idd = s([], 'id', '( d = %s -> d = %s )' % (ML, ML))
            cg, new = w.wcongr(TBI('d'), {'d': ML}, 'd = %s' % ML, {'d': idd})
            at = s([cg, Lc(B.mln), tb1], 'rspcdva', '( %s -> %s )' % (pc, TBI(ML)))
            both = s([s([], 'simpr', '( %s -> %s )' % (pc, cnd)), at], 'mpd', '( %s -> ( ( # ` %s ) <_ ( N + 1 ) /\\ A. q e. ran %s q < ( 2 ^ B ) ) )' % (pc, WV, WV))
            wl = s([both], 'simpld', '( %s -> ( # ` %s ) <_ ( N + 1 ) )' % (pc, WV))
            wvw = s([Lc(B.slt), w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, WV))
            ln_ = s([wvw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, WV))
            sc_in = s([s([Lc(B.l0), Lc(c['N e. NN0']), Lc(c['H e. NN0'])], '3jca', '( %s -> ( L e. NN0 /\\ N e. NN0 /\\ H e. NN0 ) )' % pc),
                       s([Lc(c['B e. NN0']), Lc(c['O e. NN0']), Lc(c['Q e. NN0'])], '3jca', '( %s -> ( B e. NN0 /\\ O e. NN0 /\\ Q e. NN0 ) )' % pc),
                       s([s([ln_, wl], 'jca', '( %s -> ( ( # ` %s ) e. NN0 /\\ ( # ` %s ) <_ ( N + 1 ) ) )' % (pc, WV, WV)),
                          s([Lc(c['( N + 1 ) <_ H']), Lc(c['B <_ Q'])], 'jca', '( %s -> ( ( N + 1 ) <_ H /\\ B <_ Q ) )' % pc),
                          s([Lc(c['O <_ Q']), Lc(c['( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q'])], 'jca',
                            '( %s -> ( O <_ Q /\\ ( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q ) )' % pc)], '3jca',
                         '( %s -> ( ( ( # ` %s ) e. NN0 /\\ ( # ` %s ) <_ ( N + 1 ) ) /\\ ( ( N + 1 ) <_ H /\\ B <_ Q ) /\\ ( O <_ Q /\\ ( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q ) ) )'
                         % (pc, WV, WV))], '3jca', '( %s -> %s )' % (pc, tsub_text(ST_SC.split(' -> ', 1)[0][2:], {'S': '( # ` %s )' % WV})))
            SCB = EXSOMEC('L', '( N + 1 )', 'B', '( # ` %s )' % WV, 'O')
            scb = s([sc_in, w.inst('tmexsomec')], 'syl', '( %s -> %s <_ ( ; 1 3 x. %s ) )' % (pc, SCB, EXY))
            clc.leaf('( # ` %s )' % WV, 'NN0', ln_)
            ARGS = '( ( ( 2 x. ( ( # ` %s ) + 1 ) ) x. B ) + 4 )' % WV
            TAS = '( TMB ` %s )' % ARGS
            clc.leaf(TAS, 'NN0', s([s([clc.mem(ARGS, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, TAS))], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, TAS)))
            le = linarith(w, pc, [Lc(pcb), scb], '%s <_ %s' % (NT, EXC_), closure=clc, atoms=[EP, EXY, SCB])
        outs.append(hrle(w, pc, Lc(mk['phm']), t2, C0, CLN('E', FINC, DFIN_EXB), NT, EXC_, clc.mem(EXC_, 'NN0'), le))
    cn = s([outs[0]], 'ex', '( %s -> ( %s = ( inr ` (/) ) -> %s ) )' % (ph, SLP_, CONCL_EXB))
    cs = s([outs[1]], 'ex', '( %s -> ( %s =/= ( inr ` (/) ) -> %s ) )' % (ph, SLP_, CONCL_EXB))
    w.qed([cn, cs], 'pm2.61dne', STMTS9['tmiexb'])
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
