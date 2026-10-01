"""T10: the divOut loop ` loop flag divOutBody ` of ` divOutF ` at the machine (Lean ` divOutF_le_B ` ) at
` xd xr xf s t u = 4 6 7 1 2 3 ` , on TMIdof, at the families of ` r / d ^ i ` (the witness of Lean's ` DOInv ` ,
~ dosh ).

  tmidofi   one iteration: below ` ( divOut d r f ).2 ` the flag is set, and ` divOutBody ` takes the family at ` i `
            to the family at ` i + 1 `
  tmidoft   the frame: the families' typings, and the flag clear at ` ( divOut d r f ).2 `
  tmidofl   ~ tm2floopu at the families ( ` P' ` a letter)
  tmidofb   divOutF_le_B: ` divOutTest ` (~ tmidotb ), the loop, ` dropNum u `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_f_dof.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import famval, fam_unpack, ifex_closed, mval
from cl import Closure
from t10_e_doa import DOX, P1, P2, RI, SHV, ST_DOSH, ST_DOCP, ST_DOFZ, snd_of, fst_of, ex_, lift_from
from t10_d_dot import DotB, skip_ty

SEL = sys.argv[1:]
LMF = FRAGS['dof'].lmap()
R_ = P2(DOX('F', 'H'))
RJ = RI
QJ = lambda t: '( |_ ` ( %s / G ) )' % RJ(t)
HM = lambda t: '( H - %s )' % t
PB = lambda t: UPS('D', ('3', EWg(QJ(t), DK(3))), ('7', EWg(HM(t), 'Y')), ('6', EWg(RJ(t), "X'")))
ORD376 = ['0', '1', '2', '3', '4', '5', '7', '6']
FLC = lambda t: 'if ( ( ( %s mod G ) = 0 /\\ %s =/= 0 ) , 1o , (/) )' % (RJ(t), HM(t))
COND = lambda h, t: '( TMfl ` %s ) = %s' % (h, FLC(t))
NCL = lambda t: '{ h e. TMSt | %s }' % COND('h', t)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
PF = '( j e. NN0 |-> %s )' % PB('j')
PV = "P'"
TPR = '( ( 9 x. ( TMB ` B ) ) + 2 )'
PSI_T = (TREE_DOF, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
GM = {'A': LMF['Z1'], 'B0': LMF['Y2'], 'E': LMF['Y3'], 'C0': 'TMfl', 'R': R_, "T'": TPR, 'N': NFM, 'P': PV}
_LA, _LC = split_imp(stmt('tm2floopu'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
_pre = 'A. i e. ( 0 ..^ %s ) ' % R_
assert LPER.startswith(_pre)
LBODY = LPER[len(_pre):]
T_I = (PSI_T, 'i e. ( 0 ..^ %s )' % R_)
add_stmt('tmidofi', T_I, LBODY)
add_stmt('tmidoft', PSI_T, '( %s /\\ %s )' % (LTYP, LEXIT))
add_stmt('tmidofl', PSI_T, LCONCL)
add_stmt('tmidofb', TREE_DOF, CONCL_DOF)


class Lf(DotB):
    """the facts under an antecedent containing the dof tree"""
    def __init__(self, w, ph, T, fname='dof'):
        c0 = Ctx(w, ph, T)
        gnn, fn, hn = c0['G e. NN'], c0['F e. NN0'], c0['H e. NN0']
        gn = w.s([gnn], 'nnnn0d', '( %s -> G e. NN0 )' % ph)
        xw, x2w, yw = c0[WG('X')], c0[WG("X'")], c0[WG('Y')]
        eqs = {'4': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xw)), '6': (EWg('F', "X'"), ewg_(w, ph, 'F', fn, "X'", x2w)),
               '7': (EWg('H', 'Y'), ewg_(w, ph, 'H', hn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, fname, eqs)
        s = w.s
        self.gnn, self.gn, self.fn, self.hn, self.bn = gnn, gn, fn, hn, self.c['B e. NN0']
        self.xw, self.x2w, self.yw = xw, x2w, yw
        self.p3 = s([s([gnn, fn, hn], '3jca', '( %s -> ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) )' % ph)], 'id',
                    '( %s -> ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) )' % ph) if False else \
            s([gnn, fn, hn], '3jca', '( %s -> ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) )' % ph)
        self.dcl = s([s([gnn, fn], 'jca', '( %s -> ( G e. NN /\\ F e. NN0 ) )' % ph), hn, w.inst('divoutcl')], 'syl2anc',
                     '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, DOX('F', 'H')))
        self.rn = s([self.dcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, R_))
        self.tbn = s([s([self.bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d',
                     '( %s -> ( TMB ` B ) e. NN0 )' % ph)
        self.pvs = {}

    def at(self, t, tn, tle):
        """the numbers at t e. NN0 with tle : t <_ R: ( t <_ H /\\ DO = SHV( t ) ) and the typings of RJ( t ) , HM( t )"""
        w, ph, s = self.w, self.ph, self.w.s
        sh = s([s([self.p3, s([tn, tle], 'jca', '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ph, t, t, R_))], 'jca',
                  '( %s -> ( ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) /\\ ( %s e. NN0 /\\ %s <_ %s ) ) )' % (ph, t, t, R_)),
                w.inst('dosh')], 'syl', '( %s -> ( %s <_ H /\\ %s = %s ) )' % (ph, t, DOX('F', 'H'), SHV(t)))
        th = s([sh], 'simpld', '( %s -> %s <_ H )' % (ph, t))
        dv = s([sh], 'simprd', '( %s -> %s = %s )' % (ph, DOX('F', 'H'), SHV(t)))
        gt = s([self.gnn, tn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( G ^ %s ) e. NN )' % (ph, t))
        rjn = s([self.fn, gt, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, RJ(t)))
        hmn = s([tn, self.hn, th, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, HM(t)))
        qjn = s([rjn, self.gnn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, QJ(t)))
        # RJ( t ) <_ F , QJ( t ) <_ F
        cl = Closure(w, ph, {'F': ('NN0', self.fn)})
        l1 = s([self.fn, gt, w.inst('fldivnn0le')], 'syl2anc', '( %s -> %s <_ ( F / ( G ^ %s ) ) )' % (ph, RJ(t), t))
        l2 = s([self.fn, gt, w.inst('nn0ledivnn')], 'syl2anc', '( %s -> ( F / ( G ^ %s ) ) <_ F )' % (ph, t))
        dvr = s([s([self.fn], 'nn0red', '( %s -> F e. RR )' % ph), s([gt], 'nnrpd', '( %s -> ( G ^ %s ) e. RR+ )' % (ph, t))],
                'rerpdivcld', '( %s -> ( F / ( G ^ %s ) ) e. RR )' % (ph, t))
        rle = s([s([rjn], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ(t))), dvr, s([self.fn], 'nn0red', '( %s -> F e. RR )' % ph), l1, l2],
                'letrd', '( %s -> %s <_ F )' % (ph, RJ(t)))
        q1 = s([rjn, self.gnn, w.inst('fldivnn0le')], 'syl2anc', '( %s -> %s <_ ( %s / G ) )' % (ph, QJ(t), RJ(t)))
        q2 = s([rjn, self.gnn, w.inst('nn0ledivnn')], 'syl2anc', '( %s -> ( %s / G ) <_ %s )' % (ph, RJ(t), RJ(t)))
        dq = s([s([rjn], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ(t))), s([self.gnn], 'nnrpd', '( %s -> G e. RR+ )' % ph)],
               'rerpdivcld', '( %s -> ( %s / G ) e. RR )' % (ph, RJ(t)))
        qle = s([s([qjn], 'nn0red', '( %s -> %s e. RR )' % (ph, QJ(t))), dq, s([rjn], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ(t))), q1, q2],
                'letrd', '( %s -> %s <_ %s )' % (ph, QJ(t), RJ(t)))
        return dict(sh=sh, th=th, dv=dv, gt=gt, rjn=rjn, hmn=hmn, qjn=qjn, rle=rle, qle=qle)

    def pbst(self, t, nums):
        w, ph = self.w, self.ph
        g3 = self.g(EWg(QJ(t), DK(3)), ewg_(w, ph, QJ(t), nums['qjn'], DK(3), self.gam[DK(3)]))
        g6 = self.g(EWg(RJ(t), "X'"), ewg_(w, ph, RJ(t), nums['rjn'], "X'", self.x2w))
        g7 = self.g(EWg(HM(t), 'Y'), ewg_(w, ph, HM(t), nums['hmn'], 'Y', self.yw))
        self.last = [('3', EWg(QJ(t), DK(3))), ('7', EWg(HM(t), 'Y')), ('6', EWg(RJ(t), "X'"))]
        return self.S0.upd('3', EWg(QJ(t), DK(3)), g3).upd('7', EWg(HM(t), 'Y'), g7).upd('6', EWg(RJ(t), "X'"), g6)

    def pv(self, t, tn, nums):
        if t not in self.pvs:
            fam = self.c['%s = %s' % (PV, PF)]
            self.pvs[t] = fam_at(self.w, self.ph, self.mk, self.ne, fam, PV, 'j', 'NN0', PB, t, tn, self.pbst(t, nums))
        return self.pvs[t]

    def famss(self, t, tn):
        w, ph = self.w, self.ph
        fv = famval(w, ph, COND, t, tn)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NCL(t))], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NCL(t)))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NCL(t)))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ ( 2nd ` T ) )' % (ph, NFM, t))

    def cost(self, t, nums):
        """cm = ( 2nd ` DOX( RJ t , HM t ) ) , ( ph -> R = ( cm + t ) ) and the docp equivalence at t"""
        w, ph, s = self.w, self.ph, self.w.s
        Dt = DOX(RJ(t), HM(t))
        cm = P2(Dt)
        rr = snd_of(w, ph, DOX('F', 'H'), P1(Dt), '( %s + %s )' % (cm, t), nums['dv'], ex_(w, ph, P1(Dt), 'fvex'),
                    ex_(w, ph, '( %s + %s )' % (cm, t), 'ovex'))
        cp = s([s([self.gnn, nums['rjn'], nums['hmn']], '3jca', '( %s -> ( G e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ph, RJ(t), HM(t))),
                w.inst('docp')], 'syl', '( %s -> ( 0 < %s <-> ( %s =/= 0 /\\ ( %s mod G ) = 0 ) ) )' % (ph, cm, HM(t), RJ(t)))
        dcl = s([s([self.gnn, nums['rjn']], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (ph, RJ(t))), nums['hmn'], w.inst('divoutcl')],
                'syl2anc', '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, Dt))
        cmn = s([dcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, cm))
        return cm, rr, cp, cmn


def flag_true(w, ph, t, both):
    """( ph -> FLC( t ) = 1o ) from both : ( ph -> ( HM t =/= 0 /\\ ( RJ t mod G ) = 0 ) )"""
    s = w.s
    c = s([s([both], 'simprd', '( %s -> ( %s mod G ) = 0 )' % (ph, RJ(t))), s([both], 'simpld', '( %s -> %s =/= 0 )' % (ph, HM(t)))], 'jca',
          '( %s -> ( ( %s mod G ) = 0 /\\ %s =/= 0 ) )' % (ph, RJ(t), HM(t)))
    return s([c], 'iftrued', '( %s -> %s = 1o )' % (ph, FLC(t)))


def cnd_fl(w, pm, mm, fl, one):
    """( pm -> ( TMfl ` m ) = 1o ) (one) or ( pm -> -. ( TMfl ` m ) = 1o ) from fl : ( pm -> ( TMfl ` m ) = 1o / (/) )"""
    if one:
        return fl
    s = w.s
    fne = s([fl, s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o')], 'a1i', '( %s -> (/) =/= 1o )' % pm)], 'eqnetrd',
            '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
    return s([fne], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)


def tmidofi():
    lab = 'tmidofi'
    T = numtree(T_I)
    ph = cj(T)
    w = W(lab, 'One iteration of Lean\'s ` divOutF ` loop at the machine ( ` DOInv ` , ` divOutBody_runs ` ): below '
               '` ( divOut d r f ).2 ` the flag is set (~ docp ), and ` divOutBody ` ( ` dropNum xr ; moveEntry u xr s ; '
               'predNum xf s ; divOutTest ` ) takes the family at ` i ` ( ` r / d ^ i ` on ` xr ` , ` f - i ` on ` xf ` , '
               '` r / d ^ ( i + 1 ) ` on ` u ` ) to the family at ` i + 1 ` within ` 9 B b + 2 ` steps.')
    s = w.s
    B = Lf(w, ph, T)
    c, mk = B.c, B.mk
    B.deep('dof', 1)
    io = c['i e. ( 0 ..^ %s )' % R_]
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ph, R_))
    cl = Closure(w, ph, {'i': ('NN0', inn), 'H': ('NN0', B.hn), 'F': ('NN0', B.fn), 'B': ('NN0', B.bn)})
    cl.leaf(R_, 'NN0', B.rn)
    ile = linarith(w, ph, [ilt], 'i <_ %s' % R_, closure=cl)
    nums = B.at('i', inn, ile)
    cm, rr, cp, cmn = B.cost('i', nums)
    cl.leaf(cm, 'NN0', cmn)
    cpos = linarith(w, ph, [rr, ilt], '0 < %s' % cm, closure=cl)
    both = s([cpos, cp], 'mpbid', '( %s -> ( %s =/= 0 /\\ ( %s mod G ) = 0 ) )' % (ph, HM('i'), RJ('i')))
    f1 = flag_true(w, ph, 'i', both)
    NI = '( %s ` i )' % NFM
    pm = '( %s /\\ m e. %s )' % (ph, NI)
    mm, mc = fam_unpack(w, pm, COND, 'i', lift_from(w, ph, pm, inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl1 = s([mc, lift_from(w, ph, pm, f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    part1 = s([fl1], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ph, NI))
    # the family at i
    pvi, SI = B.pv('i', inn, nums)
    PT = '( %s ` i )' % PV
    Spb = B.pbst('i', nums)
    chain0 = list(B.last)
    R = B.run()
    R.S, R.chain = Spb, list(chain0)
    for _k, (_txt, _st, _g) in Spb.vals.items():
        R.gam[_txt] = _g
    S37 = R.at(chain0[:2])
    TB = '( TMB ` B )'
    P2_ = lambda k: PL(PL('P', 2), k)
    p2 = '( 2 ^ B )'
    rlt = s([s([nums['rjn']], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ('i'))), cl.mem('F', 'RR'), cl.mem(p2, 'RR'), nums['rle'],
             c['F < ( 2 ^ B )']], 'lelttrd', '( %s -> %s < %s )' % (ph, RJ('i'), p2))
    # 1. dropNum 6
    B.call(R, 'tmidropb', {'K': '6', 'F': RJ('i'), 'N': 'B', 'X': "X'", 'P': P2_(0), 'E': PL(P2_(1), 0)},
           {'%s e. NN0' % RJ('i'): nums['rjn'], '%s < %s' % (RJ('i'), p2): rlt}, [('6', "X'", B.x2w)], on=(S37, chain0[:2]))
    # 2. moveEntry 3 6 1
    WQ = '( encNatGam ` %s )' % QJ('i')
    EQX = EWg(QJ('i'), "X'")
    B.call(R, 'tmime', {'K': '3', 'J': '6', 'I': '1', 'W': WQ, 'X': DK(3), 'P': P2_(1), 'E': PL(P2_(2), 0)},
           {WRD(WQ, BITS): engb(w, ph, QJ('i'), nums['qjn'])},
           [('3', DK(3), B.gam[DK(3)]), ('6', EQX, B.g(EQX, ewg_(w, ph, QJ('i'), nums['qjn'], "X'", B.x2w)))])
    # 3. predNum 7 1
    hmnn = s([s([nums['hmn'], s([both], 'simpld', '( %s -> %s =/= 0 )' % (ph, HM('i')))], 'jca',
                '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (ph, HM('i'), HM('i'))),
              s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (HM('i'), HM('i'), HM('i')))], 'sylibr',
             '( %s -> %s e. NN )' % (ph, HM('i')))
    hlt = linarith(w, ph, [c['H < ( 2 ^ B )'], cl.ge0('i')], '%s < %s' % (HM('i'), p2), closure=cl)
    H1 = '( %s - 1 )' % HM('i')
    h1n = s([hmnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, H1))
    EH1 = EWg(H1, 'Y')
    B.call(R, 'tmiprdbs', {'K': '7', 'J': '1', 'F': HM('i'), 'N': 'B', 'X': 'Y', 'P': P2_(2), 'E': PL(PL(P2_(3), 3), 0)},
           {'%s e. NN' % HM('i'): hmnn, '%s < %s' % (HM('i'), p2): hlt}, [('7', EH1, B.g(EH1, ewg_(w, ph, H1, h1n, 'Y', B.yw)))])
    # 4. divOutTest at ( r / d ^ ( i + 1 ) ) , ( f - i ) - 1
    qlt = s([s([nums['qjn']], 'nn0red', '( %s -> %s e. RR )' % (ph, QJ('i'))), s([nums['rjn']], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ('i'))),
             cl.mem(p2, 'RR'), nums['qle'], rlt], 'lelttrd', '( %s -> %s < %s )' % (ph, QJ('i'), p2))
    h1lt = linarith(w, ph, [c['H < ( 2 ^ B )'], cl.ge0('i')], '%s < %s' % (H1, p2), closure=cl)
    FQ2 = '( |_ ` ( %s / G ) )' % QJ('i')
    q2n = s([nums['qjn'], B.gnn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FQ2))
    E3 = EWg(FQ2, DK(3))
    FIN = 'if ( ( ( %s mod G ) = 0 /\\ %s =/= 0 ) , 1o , (/) )' % (QJ('i'), H1)
    B.call(R, 'tmidotb', {'F': QJ('i'), 'H': H1, 'X': 'X', "X'": "X'", 'Y': 'Y', 'P': P2_(3), 'E': LMF['Z1']},
           {'%s e. NN0' % QJ('i'): nums['qjn'], '%s < %s' % (QJ('i'), p2): qlt, '%s e. NN0' % H1: h1n, '%s < %s' % (H1, p2): h1lt},
           [('3', E3, B.g(E3, ewg_(w, ph, FQ2, q2n, DK(3), B.gam[DK(3)])))])
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the bound
    tbn = B.tbn
    cl.leaf(TB, 'NN0', tbn)
    LW = '( # ` %s )' % WQ
    cl.leaf(LW, 'NN0', s([encw(w, ph, QJ('i'), nums['qjn']), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))
    lw = s([s([nums['qjn'], w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` %s ) ) )' % (ph, LW, QJ('i'))),
            s([nums['qjn'], B.bn, qlt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` %s ) ) <_ B )' % (ph, QJ('i')))],
           'eqbrtrd', '( %s -> %s <_ B )' % (ph, LW))
    import num
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([B.bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( B + 2 ) ^ 2 ) ) <_ ( TMB ` B ) )' % ph)
    me = nlinarith(w, ph, [lw, qd, cl.ge0('B'), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ %s' % (LW, TB), closure=cl, atoms=['B', LW, TB])
    le = linarith(w, ph, [me], '%s <_ %s' % (n, TPR), closure=cl, atoms=[LW, TB])
    C2 = CLN(LMF['Y2'], NI, PB('i'))
    # the post: stacks to PB( i + 1 ) , class to ( NFM ` ( i + 1 ) )
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ph)
    i1le = s([s([s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ph), s([B.rn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, R_)), w.inst('zltp1le')], 'syl2anc',
                '( %s -> ( i < %s <-> ( i + 1 ) <_ %s ) )' % (ph, R_, R_)), ilt], 'mpbid' if False else 'mpbird', '') if False else \
        s([ilt, s([s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ph), s([B.rn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, R_)), w.inst('zltp1le')],
                  'syl2anc', '( %s -> ( i < %s <-> ( i + 1 ) <_ %s ) )' % (ph, R_, R_))], 'mpbid', '( %s -> ( i + 1 ) <_ %s )' % (ph, R_))
    nums1 = B.at('( i + 1 )', i1n, i1le)
    pv1, S1 = B.pv('( i + 1 )', i1n, nums1)
    P1T = '( %s ` ( i + 1 ) )' % PV
    Gi = '( G ^ i )'
    qd_ = s([cl.mem('F', 'RR'), nums['gt'], B.gnn, w.inst('fldiv2')], 'syl3anc', '( %s -> %s = ( |_ ` ( F / ( %s x. G ) ) ) )' % (ph, QJ('i'), Gi))
    ep = s([s([B.gnn], 'nncnd', '( %s -> G e. CC )' % ph), inn, w.inst('expp1')], 'syl2anc', '( %s -> ( G ^ ( i + 1 ) ) = ( %s x. G ) )' % (ph, Gi))
    qe = s([qd_, s([s([s([ep], 'eqcomd', '( %s -> ( %s x. G ) = ( G ^ ( i + 1 ) ) )' % (ph, Gi))], 'oveq2d',
                      '( %s -> ( F / ( %s x. G ) ) = ( F / ( G ^ ( i + 1 ) ) ) )' % (ph, Gi))], 'fveq2d',
                   '( %s -> ( |_ ` ( F / ( %s x. G ) ) ) = %s )' % (ph, Gi, RJ('( i + 1 )')))], 'eqtrd', '( %s -> %s = %s )' % (ph, QJ('i'), RJ('( i + 1 )')))
    fe = s([cl.mem('H', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph), w.inst('subsub4')],
           'syl3anc', '( %s -> %s = %s )' % (ph, H1, HM('( i + 1 )')))
    RULES = {QJ('i'): (RJ('( i + 1 )'), qe), H1: (HM('( i + 1 )'), fe)}
    cur, out2 = R.normalize(ORD376)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t = hrle(w, ph, mk['phm'], t, C, D, n, TPR, cl.mem(TPR, 'NN0'), le)
    n = TPR
    t = hrssc(w, ph, mk['phm'], t, C, D, n, C2, clnss(w, ph, LMF['Y2'], NI, S, PB('i'), B.famss('i', inn)))
    Dst = triple_D(D)
    xn = chain_text('D', out2)
    assert Dst == xn, (Dst, xn)
    r2_, x2 = w.rewrite(xn, RULES, ph)
    assert x2 == PB('( i + 1 )'), (x2, PB('( i + 1 )'))
    deq = s([r2_, pv1], 'eqtr4d', '( %s -> %s = %s )' % (ph, Dst, P1T))
    Ncur = D.split(' } X. ( ', 1)[1].rsplit(' X. { ', 1)[0]
    assert Ncur == NFL(FIN), Ncur
    rc, xc = w.rewrite(FIN, RULES, ph)
    assert xc == FLC('( i + 1 )'), xc
    N1 = '( %s ` ( i + 1 ) )' % NFM
    cq = s([nfl_eq(w, ph, FIN, FLC('( i + 1 )'), rc), s([famval(w, ph, COND, '( i + 1 )', i1n)], 'eqcomd',
                                                         '( %s -> %s = %s )' % (ph, NCL('( i + 1 )'), N1))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, NFL(FIN), N1))
    lab_ = LMF['Z1']
    ceq = s([clnneq(w, ph, lab_, cq, NFL(FIN), N1, Dst), clneq(w, ph, lab_, N1, deq, Dst, P1T)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN(lab_, N1, P1T)))
    cpre = clneq(w, ph, LMF['Y2'], NI, s([pvi], 'eqcomd', '( %s -> %s = %s )' % (ph, PB('i'), PT)), PB('i'), PT)
    t, C, D, n = hrrw(w, ph, t, C2, D, n, ceq=cpre, deq=ceq)
    st = s([part1, t], 'jca', '( %s -> %s )' % (ph, LBODY))
    finish(w, st, lab)
    return w.run()


def tmidoft():
    lab = 'tmidoft'
    w = W(lab, 'The frame of Lean\'s ` divOutF ` loop at the machine: for ` i <_ ( divOut d r f ).2 ` the class family is a set '
               'of states and the stack family a stack assignment, and at ` ( divOut d r f ).2 ` the flag is clear (~ dosh , '
               '~ docp ).')
    s = w.s
    TT = numtree((PSI_T, 'i e. ( 0 ... %s )' % R_))
    pt = cj(TT)
    B = Lf(w, pt, TT)
    ii = B.c['i e. ( 0 ... %s )' % R_]
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ %s )' % (pt, R_))
    nums = B.at('i', inn, ile)
    pv, St = B.pv('i', inn, nums)
    body = LTYP[len('A. i e. ( 0 ... %s ) ' % R_):]
    one = s([B.famss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))
    # discharge the numeral facts inside, then generalize
    T0 = (PSI_T, 'i e. ( 0 ... %s )' % R_)
    p0 = cj(T0)
    k = s([], 't10stk', ST_NUMS)
    one0 = s([k, one], 'mpan2', '( %s -> %s )' % (p0, body))
    typ = s([one0], 'ralrimiva', '( %s -> %s )' % (PSI, LTYP))
    # the exit
    TE = numtree(PSI_T)
    pe = cj(TE)
    L = Lf(w, pe, TE)
    rle = s([s([L.rn], 'nn0red', '( %s -> %s e. RR )' % (pe, R_))], 'leidd', '( %s -> %s <_ %s )' % (pe, R_, R_))
    nr = L.at(R_, L.rn, rle)
    cm, rr, cp, cmn = L.cost(R_, nr)
    cl = Closure(w, pe, {})
    cl.leaf(R_, 'NN0', L.rn)
    cl.leaf(cm, 'NN0', cmn)
    np_ = linarith(w, pe, [rr], '%s <_ 0' % cm, closure=cl)
    nlt = s([s([cl.mem(cm, 'RR'), s([], '0re', '0 e. RR') if False else closed(w, pe, '0re', '0 e. RR'), np_], 'lenltd',
               '( %s -> -. 0 < %s )' % (pe, cm))], 'id', '( %s -> -. 0 < %s )' % (pe, cm)) if False else \
        s([np_, s([cl.mem(cm, 'RR'), closed(w, pe, '0re', '0 e. RR')], 'lenltd', '( %s -> ( %s <_ 0 <-> -. 0 < %s ) )' % (pe, cm, cm))],
          'mpbid', '( %s -> -. 0 < %s )' % (pe, cm))
    X_ = '( %s =/= 0 /\\ ( %s mod G ) = 0 )' % (HM(R_), RJ(R_))
    nb = s([nlt, cp], 'mtbid', '( %s -> -. %s )' % (pe, X_))
    Y_ = '( ( %s mod G ) = 0 /\\ %s =/= 0 )' % (RJ(R_), HM(R_))
    nb2 = s([nb, s([s([], 'ancom', '( %s <-> %s )' % (Y_, X_))], 'a1i', '( %s -> ( %s <-> %s ) )' % (pe, Y_, X_))], 'mtbird',
            '( %s -> -. %s )' % (pe, Y_))
    f0 = s([nb2], 'iffalsed', '( %s -> %s = (/) )' % (pe, FLC(R_)))
    NE = '( %s ` %s )' % (NFM, R_)
    pm = '( %s /\\ m e. %s )' % (pe, NE)
    mm, mc = fam_unpack(w, pm, COND, R_, lift_from(w, pe, pm, L.rn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)))
    fl = s([mc, lift_from(w, pe, pm, f0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ex_ = s([cnd_fl(w, pm, mm, fl, False)], 'ralrimiva', '( %s -> %s )' % (pe, LEXIT))
    ex0 = s([k, ex_], 'mpan2', '( %s -> %s )' % (PSI, LEXIT))
    w.qed([typ, ex0], 'jca', STMTS10[lab])
    return w.run()


def tmidofl():
    lab = 'tmidofl'
    w = W(lab, 'Lean\'s ` divOutF ` loop at the machine: ~ tm2floopu at the families ( ` P\' ` a letter), '
               '` ( divOut d r f ).2 ` iterations of ` divOutBody ` (~ tmidofi ), the frame by ~ tmidoft .')
    s = w.s
    T = numtree(PSI_T)
    ph = cj(T)
    B = Lf(w, ph, T)
    B.deep('dof', 1)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmidoft', STMTS10['tmidoft']))
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    it = s([], 'tmidofi', STMTS10['tmidofi'])
    per = s([it], 'ralrimiva', '( %s -> %s )' % (PSI, LPER))
    ex[LPER] = lift_from(w, PSI, ph, per)
    ex['%s e. NN0' % R_] = B.rn
    cl = Closure(w, ph, {'B': ('NN0', B.bn)})
    cl.leaf('( TMB ` B )', 'NN0', B.tbn)
    ex['%s e. NN0' % TPR] = cl.mem(TPR, 'NN0')
    st = Bld(w, ph, B.c, ex)(LTREE)
    st2 = s([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ph, LCONCL))
    finish(w, st2, lab)
    return w.run()


def tmidofb():
    lab = 'tmidofb'
    T = numtree(TREE_DOF)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` divOutF_le_B ` at the machine ( ` xd xr xf s t u = 4 6 7 1 2 3 ` ): ` divOutTest ` (~ tmidotb ), '
               'the loop (~ tmidofl at the families of ` r / d ^ i ` ), ` dropNum u ` : ` xr ` holds ` ( divOut d r f ).1 ` , '
               '` xf ` the fuel left, every other stack restored, within ` ( ( divOut d r f ).2 + 1 ) B ( 3 b + 4 ) ` steps.')
    s = w.s
    B = Lf(w, ph, T)
    c, mk = B.c, B.mk
    from t7lib import mval
    TB = '( TMB ` B )'
    # 1. divOutTest
    R = B.run()
    FQ = '( |_ ` ( F / G ) )'
    fqn = s([B.fn, B.gnn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FQ))
    E3 = EWg(FQ, DK(3))
    B.call(R, 'tmidotb', {'P': PL('P', 1), 'E': LMF['Z1']}, {}, [('3', E3, B.g(E3, ewg_(w, ph, FQ, fqn, DK(3), B.gam[DK(3)])))])
    S3 = R.S
    # 2. the family at 0
    z0 = closed(w, ph, '0nn0', '0 e. NN0')
    zle = s([B.rn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, R_))
    g0 = s([s([s([B.gnn], 'nncnd', '( %s -> G e. CC )' % ph), w.inst('exp0')], 'syl', '( %s -> ( G ^ 0 ) = 1 )' % ph)], 'oveq2d',
           '( %s -> ( F / ( G ^ 0 ) ) = ( F / 1 ) )' % ph)
    d1 = s([s([B.fn], 'nn0cnd', '( %s -> F e. CC )' % ph), w.inst('div1')], 'syl', '( %s -> ( F / 1 ) = F )' % ph)
    fz = s([s([B.fn], 'nn0zd', '( %s -> F e. ZZ )' % ph), w.inst('flid')], 'syl', '( %s -> ( |_ ` F ) = F )' % ph)
    r0 = s([s([s([g0, d1], 'eqtrd', '( %s -> ( F / ( G ^ 0 ) ) = F )' % ph)], 'fveq2d', '( %s -> %s = ( |_ ` F ) )' % (ph, RJ('0'))), fz],
           'eqtrd', '( %s -> %s = F )' % (ph, RJ('0')))
    h0 = s([s([B.hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('subid1')], 'syl', '( %s -> ( H - 0 ) = H )' % ph)
    R0 = {RJ('0'): ('F', r0), HM('0'): ('H', h0)}
    # class
    rcl, xcl = w.rewrite(FLC('0'), R0, ph)
    assert xcl == FINV_DOT, xcl
    N0 = '( %s ` 0 )' % NFM
    ceq0 = s([s([famval(w, ph, COND, '0', z0), nfl_eq(w, ph, FLC('0'), FINV_DOT, rcl)], 'eqtrd',
                '( %s -> %s = %s )' % (ph, N0, NFL(FINV_DOT)))], 'eqcomd', '( %s -> %s = %s )' % (ph, NFL(FINV_DOT), N0))
    # stacks
    nums0 = B.at('0', z0, zle)
    PB0 = PB('0')
    pbx = s([B.pbst('0', nums0).memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB0))
    pfv = mval(w, ph, 'j', 'NN0', PB, '0', z0, pbx)
    rs, xs = w.rewrite(PB0, R0, ph)
    S37 = S3.upd('7', EWg('H', 'Y'), B.gam[EWg('H', 'Y')])
    assert xs == UP(S37.D, '6', EWg('F', "X'")), xs
    u7 = upidv(w, ph, S3.D, '7', EWg('H', 'Y'), S3.vals['7'][1], mk['tv'], S3.memb, mk['k']['7']['kd'])
    rr7, x7 = w.rewrite(xs, {S37.D: (S3.D, u7)}, ph)
    assert x7 == UP(S3.D, '6', EWg('F', "X'")), x7
    u6 = upidv(w, ph, S3.D, '6', EWg('F', "X'"), S3.vals['6'][1], mk['tv'], S3.memb, mk['k']['6']['kd'])
    pf0 = '( %s ` 0 )' % PF
    se = s([s([s([s([pfv, rs], 'eqtrd', '( %s -> %s = %s )' % (ph, pf0, xs)), rr7], 'eqtrd', '( %s -> %s = %s )' % (ph, pf0, x7)), u6],
              'eqtrd', '( %s -> %s = %s )' % (ph, pf0, S3.D))], 'eqcomd', '( %s -> %s = %s )' % (ph, S3.D, pf0))
    lab0 = LMF['Z1']
    ceq = s([clnneq(w, ph, lab0, ceq0, NFL(FINV_DOT), N0, S3.D), clneq(w, ph, lab0, N0, se, S3.D, pf0)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, R.cur, CLN(lab0, N0, pf0)))
    t1, C1, D1, n1 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=ceq)
    # 3. the loop at P' := PF
    ex = {'%s = %s' % (PF, PF): s([s([], 'eqid', '%s = %s' % (PF, PF))], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}
    tl, cl_ = inst(w, ph, 'tmidofl', {PV: PF}, Bld(w, ph, c, ex))
    C2, D2, n2 = triple_parts(cl_)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, mk['phm'], t1, tl, C1, D1, D2, n1, n2)
    n12 = '( %s + %s )' % (n1, n2)
    # 4. dropNum 3 from ( PF ` R )
    numsR = B.at(R_, B.rn, s([s([B.rn], 'nn0red', '( %s -> %s e. RR )' % (ph, R_))], 'leidd', '( %s -> %s <_ %s )' % (ph, R_, R_)))
    SR = B.pbst(R_, numsR)
    pbr = s([SR.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB(R_)))
    pfr = mval(w, ph, 'j', 'NN0', PB, R_, B.rn, pbr)
    PFR = '( %s ` %s )' % (PF, R_)
    NR = '( %s ` %s )' % (NFM, R_)
    chi = list(B.last)
    ORD3 = ['0', '1', '2', '4', '5', '7', '6', '3']
    nst, outR = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chi, B.gam, ORD3)
    deqR = s([pfr, nst], 'eqtrd', '( %s -> %s = %s )' % (ph, PFR, chain_text('D', outR)))
    t12, C12, D12, n12 = hrrw(w, ph, t12, C1, D2, n12, deq=clneq(w, ph, LMF['Y3'], NR, deqR, PFR, chain_text('D', outR)))
    R2 = B.run()
    SRr = B.S0
    for k_, v_ in outR:
        SRr = SRr.upd(k_, v_, B.gam[v_])
    R2.S, R2.chain = SRr, list(outR)
    for _k, (_txt, _st, _g) in SRr.vals.items():
        R2.gam[_txt] = _g
    S76 = R2.at(outR[:2])
    p2 = '( 2 ^ B )'
    cl = Closure(w, ph, {'F': ('NN0', B.fn), 'B': ('NN0', B.bn), 'H': ('NN0', B.hn)})
    rlt = s([s([numsR['rjn']], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ(R_))), cl.mem('F', 'RR'), cl.mem(p2, 'RR'), numsR['rle'],
             c['F < ( 2 ^ B )']], 'lelttrd', '( %s -> %s < %s )' % (ph, RJ(R_), p2))
    qlt = s([s([numsR['qjn']], 'nn0red', '( %s -> %s e. RR )' % (ph, QJ(R_))), s([numsR['rjn']], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ(R_))),
             cl.mem(p2, 'RR'), numsR['qle'], rlt], 'lelttrd', '( %s -> %s < %s )' % (ph, QJ(R_), p2))
    B.call(R2, 'tmidropb', {'K': '3', 'F': QJ(R_), 'N': 'B', 'X': DK(3), 'P': PL('P', 3), 'E': 'E'},
           {'%s e. NN0' % QJ(R_): numsR['qjn'], '%s < %s' % (QJ(R_), p2): qlt}, [('3', DK(3), B.gam[DK(3)])],
           on=(S76, outR[:2]))
    cur, outF = R2.normalize(N8)
    t3, C3, D3, n3 = R2.tri, R2.C0, R2.cur, R2.n
    FT = chain_text('D', outR)
    C3n = CLN(LMF['Y3'], NR, FT)
    t3 = hrssc(w, ph, mk['phm'], t3, C3, D3, n3, C3n, clnss(w, ph, LMF['Y3'], NR, S, FT, B.famss(R_, B.rn)))
    C3 = C3n
    assert C3 == D12, (C3, D12)
    t = hrseq(w, ph, mk['phm'], t12, t3, C1, D12, D3, n12, n3)
    nT = '( %s + %s )' % (n12, n3)
    # 5. ( 1st ` DO ) = RJ( R )
    cm, rr, cp, cmn = B.cost(R_, numsR)
    cl.leaf(R_, 'NN0', B.rn)
    cl.leaf(cm, 'NN0', cmn)
    c0 = lineq(w, ph, cm, '0', closure=cl, hyps=[rr]) if False else None
    cz = s([s([s([cl.mem(cm, 'RR'), cl.mem(R_, 'RR')], 'jca', '') if False else None] if False else [], 'id', '') if False else None] if False else [], 'id', '') if False else None
    c0le = linarith(w, ph, [rr], '%s <_ 0' % cm, closure=cl)
    c0 = s([s([s([cmn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, cm)), c0le], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ 0 ) )' % (ph, cm, cm)),
            s([cl.mem(cm, 'RR'), closed(w, ph, '0re', '0 e. RR'), w.inst('letri3')], 'syl2anc',
              '( %s -> ( %s = 0 <-> ( %s <_ 0 /\\ 0 <_ %s ) ) )' % (ph, cm, cm, cm))], 'sylibr', '') if False else \
        s([s([c0le, s([cmn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, cm))], 'jca', '( %s -> ( %s <_ 0 /\\ 0 <_ %s ) )' % (ph, cm, cm)),
           s([cl.mem(cm, 'RR'), closed(w, ph, '0re', '0 e. RR'), w.inst('letri3')], 'syl2anc',
             '( %s -> ( %s = 0 <-> ( %s <_ 0 /\\ 0 <_ %s ) ) )' % (ph, cm, cm, cm))], 'mpbird', '( %s -> %s = 0 )' % (ph, cm))
    Dr = DOX(RJ(R_), HM(R_))
    fzr = s([s([s([B.gnn, numsR['rjn'], numsR['hmn']], '3jca', '( %s -> ( G e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ph, RJ(R_), HM(R_))),
                c0], 'jca', '( %s -> ( ( G e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) /\\ %s = 0 ) )' % (ph, RJ(R_), HM(R_), cm)),
             w.inst('dofz')], 'syl', '( %s -> %s = %s )' % (ph, P1(Dr), RJ(R_)))
    f1 = fst_of(w, ph, DOX('F', 'H'), P1(Dr), '( %s + %s )' % (cm, R_), numsR['dv'], ex_(w, ph, P1(Dr), 'fvex'),
                ex_(w, ph, '( %s + %s )' % (cm, R_), 'ovex'))
    fr = s([s([f1, fzr], 'eqtrd', '( %s -> %s = %s )' % (ph, P1(DOX('F', 'H')), RJ(R_)))], 'eqcomd',
           '( %s -> %s = %s )' % (ph, RJ(R_), P1(DOX('F', 'H'))))
    Dcur = triple_D(D3)
    rf, xf = w.rewrite(Dcur, {RJ(R_): (P1(DOX('F', 'H')), fr)}, ph)
    DF_ = UPS('D', ('6', EWg(P1(DOX('F', 'H')), "X'")), ('7', EWg(HM(R_), 'Y')))
    assert xf == DF_, (xf, DF_)
    t, C, D, n = hrrw(w, ph, t, C1, D3, nT, deq=clneq(w, ph, 'E', S, rf, Dcur, xf))
    # 6. the bound
    TB3 = '( TMB ` ( ( 3 x. B ) + 4 ) )'
    BND = '( ( %s + 1 ) x. %s )' % (R_, TB3)
    tb3 = s([B.bn, w.inst('tplb34')], 'syl', '( %s -> %s = ( ; 2 7 x. %s ) )' % (ph, TB3, TB))
    cl.leaf(TB, 'NN0', B.tbn)
    cl.leaf(TB3, 'NN0', s([s([s([B.bn, closed(w, ph, '3nn0', '3 e. NN0'), w.inst('nn0mulcl')] if False else [], 'id', '') if False else None] if False else [], 'id', '') if False else
                           s([s([s([closed(w, ph, '3nn0', '3 e. NN0'), B.bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 3 x. B ) e. NN0 )' % ph),
                                 closed(w, ph, '4nn0', '4 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 3 x. B ) + 4 ) e. NN0 )' % ph),
                              w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB3))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB3)))
    t1b = s([s([B.bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB))
    le = nlinarith(w, ph, [tb3, t1b, cl.ge0(R_)], '%s <_ %s' % (n, BND), closure=cl, atoms=[R_, TB, TB3])
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
