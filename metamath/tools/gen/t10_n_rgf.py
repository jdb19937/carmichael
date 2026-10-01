"""T10: the resGo loop ` loop ( !flag ) resGoBody ` of ` resGoF ` at the machine (Lean ` resGoF_runs ` ), on TMIrgf, at
the families of ` resGo z99 y q i ` (~ rgstep , ~ rgenc ), with the Sum-form loop rule ~ tm2floop (per-iteration charge
` 8 X ( a_( i + 1 ) - a_i ) - 1 ` , ` X = B ( 4 b + 10 ) ` , telescoping to Lean's ` 8 X ( resGo .. ).2 ` ).

  tmirgfi   one iteration (the body ` resTestF ; incr 2 6 ; predNum 3 6 ; isZero 3 6 ` )
  tmirgft   the frame
  tmirgfl   ~ tm2floop at the families
  tmirgf    resGoF_runs

    MM_DB=sorties/t10.mm python3 tools/gen/t10_n_rgf.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import famval, fam_unpack, ifex_closed, mval
from cl import Closure
from t10_e_doa import P1, P2, snd_of, fst_of, ex_, lift_from
from t10_l_rga import RGX, KC, KEEPW, IPC, SMC, CST, STV, rgcl
from t10_m_rgl import EL, ST_RGENC, ST_RGLN
from t5lib import hrssd, cfgcl

SEL = sys.argv[1:]
LMR = FRAGS['rgf'].lmap()
LB = FRAGS['rgb'].lmap(PL('P', 2), LMR['Z1'])
QI = lambda t: '( Q + %s )' % t
HM = lambda t: '( H - %s )' % t
LI = lambda t: P1(RGX('Q', t))
AI = lambda t: P2(RGX('Q', t))
PB = lambda t: UPS('D', ('2', EWg(QI(t), 'Z')), ('3', EWg(HM(t), "Z'")), ('5', EL(t)))
FLC = lambda t: 'if ( %s = 0 , 1o , (/) )' % HM(t)
COND = lambda h, t: '( TMfl ` %s ) = %s' % (h, FLC(t))
NCL = lambda t: '{ h e. TMSt | %s }' % COND('h', t)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
PF = '( j e. NN0 |-> %s )' % PB('j')
PV = "P'"
XB = '( TMB ` ( ( 4 x. B ) + ; 1 0 ) )'
K8X = '( 8 x. %s )' % XB
UB = lambda t: '( ( ( %s x. %s ) - ( %s x. %s ) ) - 1 )' % (K8X, AI('( %s + 1 )' % t), K8X, AI(t))
UF = '( j e. NN0 |-> %s )' % UB('j')
PSI_T = (TREE_RGF, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
GM = {'A': LMR['Z1'], 'B0': LMR['Y2'], 'E': LMR['Y3'], 'C0': CNFL, 'R': 'H', 'N': NFM, 'P': PV, 'U': UF}
_LA, _LC = split_imp(stmt('tm2floop'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
LBODY = LPER[len('A. i e. ( 0 ..^ H ) '):]
T_I = (PSI_T, 'i e. ( 0 ..^ H )')
add_stmt('tmirgfi', T_I, LBODY)
add_stmt('tmirgft', PSI_T, '( %s /\\ %s )' % (LTYP, LEXIT))
add_stmt('tmirgfl', PSI_T, LCONCL)
ORD235 = ['0', '1', '4', '6', '7', '2', '3', '5']


class Lr(Base):
    def __init__(self, w, ph, T, fname='rgf'):
        c0 = Ctx(w, ph, T)
        s = w.s
        gn, ynn, qnn, hn = c0['G e. NN0'], c0['Y e. NN'], c0['Q e. NN'], c0['H e. NN0']
        yn = s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph)
        qn = s([qnn], 'nnnn0d', '( %s -> Q e. NN0 )' % ph)
        xw, x2w, zw, z2w, rw_ = c0[WG('X')], c0[WG("X'")], c0[WG('Z')], c0[WG("Z'")], c0[WG('R')]
        s2 = s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
        eqs = {'0': (EWg('Y', 'X'), ewg_(w, ph, 'Y', yn, 'X', xw)), '1': (EWg('G', "X'"), ewg_(w, ph, 'G', gn, "X'", x2w)),
               '2': (EWg('Q', 'Z'), ewg_(w, ph, 'Q', qn, 'Z', zw)), '3': (EWg('H', "Z'"), ewg_(w, ph, 'H', hn, "Z'", z2w)),
               '5': ('( <" 2 "> ++ R )', wgcat(w, ph, '<" 2 ">', 'R', s2, rw_))}
        Base.__init__(self, w, ph, T, N8, fname, eqs)
        self.gn, self.ynn, self.qnn, self.qn, self.hn, self.bn = gn, ynn, qnn, qn, hn, self.c['B e. NN0']
        self.zw, self.z2w, self.rw = zw, z2w, rw_
        self.pvs = {}

    def at(self, t, tn, tle):
        w, ph, s = self.w, self.ph, self.w.s
        xc = rgcl(w, ph, 'Q', t, self.gn, self.ynn, self.qnn, tn)
        lw = s([xc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, LI(t)))
        an = s([xc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, AI(t)))
        qtn = s([self.qnn, tn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, QI(t)))
        hmn = s([tn, self.hn, tle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, HM(t)))
        rl = s([lw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word NN0 )' % (ph, LI(t)))
        elg = wgcat(w, ph, '( encList ` ( reverse ` %s ) )' % LI(t), 'R', s([rl, w.inst('tm2lenccl')], 'syl',
                                                                           "( %s -> ( encList ` ( reverse ` %s ) ) e. Word Gamma' )" % (ph, LI(t))), self.rw)
        return dict(lw=lw, an=an, qtn=qtn, hmn=hmn, rl=rl, elg=elg)

    def pbst(self, t, nums):
        w, ph = self.w, self.ph
        g2 = self.g(EWg(QI(t), 'Z'), ewg_(w, ph, QI(t), w.s([nums['qtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, QI(t))), 'Z', self.zw))
        g3 = self.g(EWg(HM(t), "Z'"), ewg_(w, ph, HM(t), nums['hmn'], "Z'", self.z2w))
        g5 = self.g(EL(t), nums['elg'])
        self.last = [('2', EWg(QI(t), 'Z')), ('3', EWg(HM(t), "Z'")), ('5', EL(t))]
        return self.S0.upd('2', EWg(QI(t), 'Z'), g2).upd('3', EWg(HM(t), "Z'"), g3).upd('5', EL(t), g5)

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


def tmbn(w, ph, x, xn):
    s = w.s
    return s([s([xn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` %s ) e. NN )' % (ph, x))], 'nnnn0d', '( %s -> ( TMB ` %s ) e. NN0 )' % (ph, x))


def lin_nn0(w, ph, a, b, an, bn, op):
    s = w.s
    if op == 'x.':
        return s([an, bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( %s x. %s ) e. NN0 )' % (ph, a, b))
    return s([an, bn, w.inst('nn0addcl')], 'syl2anc', '( %s -> ( %s + %s ) e. NN0 )' % (ph, a, b))


def tmirgfi():
    lab = 'tmirgfi'
    T = numtree(T_I)
    ph = cj(T)
    w = W(lab, 'One iteration of Lean\'s ` resGoF ` loop at the machine ( ` RGInv ` , ` resGoBody_runs ` ): below the fuel the flag is '
               'clear, and ` resGoBody ` ( ` resTestF ; incr 2 6 ; predNum 3 6 ; isZero 3 6 ` ) takes the family at ` i ` to the family '
               'at ` i + 1 ` (~ rgstep , ~ rgenc ) within ` 8 X ( a_( i + 1 ) - a_i ) - 1 ` steps.')
    s = w.s
    B = Lr(w, ph, T)
    c, mk = B.c, B.mk
    B.deep('rgf', 1)
    io = c['i e. ( 0 ..^ H )']
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < H )' % ph)
    cl = Closure(w, ph, {'i': ('NN0', inn), 'H': ('NN0', B.hn), 'Q': ('NN', B.qnn), 'B': ('NN0', B.bn), 'G': ('NN0', B.gn)})
    ile = linarith(w, ph, [ilt], 'i <_ H', closure=cl)
    nums = B.at('i', inn, ile)
    hpos = linarith(w, ph, [ilt], '0 < %s' % HM('i'), closure=cl)
    hne0 = s([hpos], 'gt0ne0d', '( %s -> %s =/= 0 )' % (ph, HM('i')))
    f0 = s([s([hne0], 'neneqd', '( %s -> -. %s = 0 )' % (ph, HM('i')))], 'iffalsed', '( %s -> %s = (/) )' % (ph, FLC('i')))
    NI = '( %s ` i )' % NFM
    pm = '( %s /\\ m e. %s )' % (ph, NI)
    mm, mc = fam_unpack(w, pm, COND, 'i', lift_from(w, ph, pm, inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl0 = s([mc, lift_from(w, ph, pm, f0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    from t9_m_loop import cnfl_at
    part1 = s([cnfl_at(w, pm, mm, fl0, False)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ph, NI, CNFL))
    i1 = '( i + 1 )'
    p2 = '( 2 ^ B )'
    cl.atom(p2)
    qlt = linarith(w, ph, [c['( Q + H ) < ( 2 ^ B )'], ilt], '%s < %s' % (QI('i'), p2), closure=cl)
    # the run from PB( i )
    pvi, SI = B.pv('i', inn, nums)
    PT = '( %s ` i )' % PV
    Spb = B.pbst('i', nums)
    R = B.run()
    R.S, R.chain = Spb, list(B.last)
    for _k, (_txt, _st, _g) in Spb.vals.items():
        R.gam[_txt] = _g
    Pb = lambda k: PL(PL('P', 2), k)
    # 1. resTestF at q := Q + i
    q_ = QI('i')
    KCq = KC(q_)
    V5 = IFV('%s' % KCq, EWg(q_, EL('i')), EL('i'))
    RKq = tsub_text(RK_, {'Q': q_})
    assert '%s = 1o' % RKq == KCq, (RKq, KCq)
    g5 = s([ewg_(w, ph, q_, s([nums['qtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, q_)), EL('i'), nums['elg']), nums['elg']], 'ifcld',
           "( %s -> %s e. Word Gamma' )" % (ph, V5))
    B.call(R, 'tmirts', {'Q': q_, 'P': Pb(0), 'E': LB['Y2']}, {'%s e. NN' % q_: nums['qtn'], '%s < %s' % (q_, p2): qlt},
           [('5', V5, B.g(V5, g5))])
    # 2. incr 2 6 ; 3. predNum 3 6 ; 4. isZero 3 6
    Q1_ = '( %s + 1 )' % q_
    q1n = s([s([nums['qtn'], w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (ph, Q1_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, Q1_))
    E2 = EWg(Q1_, 'Z')
    B.call(R, 'tmiincbs', {'K': '2', 'J': '6', 'F': q_, 'N': 'B', 'X': 'Z', 'P': Pb(1), 'E': LB['Y3']},
           {'%s e. NN0' % q_: s([nums['qtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, q_)), '%s < %s' % (q_, p2): qlt},
           [('2', E2, B.g(E2, ewg_(w, ph, Q1_, q1n, 'Z', B.zw)))])
    hmnn = s([s([nums['hmn'], hne0], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (ph, HM('i'), HM('i'))),
              s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (HM('i'), HM('i'), HM('i')))], 'sylibr',
             '( %s -> %s e. NN )' % (ph, HM('i')))
    hlt = linarith(w, ph, [c['( Q + H ) < ( 2 ^ B )'], cl.ge0('i'), cl.ge0('Q')], '%s < %s' % (HM('i'), p2), closure=cl)
    H1 = '( %s - 1 )' % HM('i')
    h1n = s([hmnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, H1))
    E3 = EWg(H1, "Z'")
    B.call(R, 'tmiprdbs', {'K': '3', 'J': '6', 'F': HM('i'), 'N': 'B', 'X': "Z'", 'P': Pb(2), 'E': LB['Y4']},
           {'%s e. NN' % HM('i'): hmnn, '%s < %s' % (HM('i'), p2): hlt}, [('3', E3, B.g(E3, ewg_(w, ph, H1, h1n, "Z'", B.z2w)))])
    h1lt = linarith(w, ph, [c['( Q + H ) < ( 2 ^ B )'], cl.ge0('i'), cl.ge0('Q')], '%s < %s' % (H1, p2), closure=cl)
    B.call(R, 'tmiizbs', {'K': '3', 'I': '6', 'F': H1, 'N': 'B', 'X': "Z'", 'P': Pb(3), 'E': LMR['Z1']},
           {'%s e. NN0' % H1: h1n, '%s < %s' % (H1, p2): h1lt}, [])
    cur, out2 = R.normalize(ORD235)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the bound: n <_ U ` i
    TB, T37 = '( TMB ` B )', '( TMB ` ( ( 3 x. B ) + 7 ) )'
    b37 = s([s([closed(w, ph, '3nn0', '3 e. NN0'), B.bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 3 x. B ) e. NN0 )' % ph),
             closed(w, ph, '7nn0', '7 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 3 x. B ) + 7 ) e. NN0 )' % ph)
    b410 = s([s([closed(w, ph, '4nn0', '4 e. NN0'), B.bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % ph),
              closed(w, ph, '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % ph)
    xn = tmbn(w, ph, '( ( 4 x. B ) + ; 1 0 )', b410)
    t37n = tmbn(w, ph, '( ( 3 x. B ) + 7 )', b37)
    tbn = tmbn(w, ph, 'B', B.bn)
    for x_, st_ in ((TB, tbn), (T37, t37n), (XB, xn)):
        cl.leaf(x_, 'NN0', st_)
    m1 = s([B.bn, b410, linarith(w, ph, [cl.ge0('B')], 'B <_ ( ( 4 x. B ) + ; 1 0 )', closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, XB))
    m2 = s([b37, b410, linarith(w, ph, [cl.ge0('B')], '( ( 3 x. B ) + 7 ) <_ ( ( 4 x. B ) + ; 1 0 )', closure=cl), w.inst('tmbmono')], 'syl3anc',
           '( %s -> %s <_ %s )' % (ph, T37, XB))
    xp = s([s([b410, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, XB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, XB))
    IP, SM = IPC(q_), SMC(q_)
    ipn = s([s([s([nums['qtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, q_)), w.inst('isprimetdcl')], 'syl',
               '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (ph, q_)), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, IP))
    smn = s([s([B.ynn, s([nums['qtn'], w.inst('nnm1nn0')], 'syl', '( %s -> ( %s - 1 ) e. NN0 )' % (ph, q_)), w.inst('smoothtdcl')], 'syl2anc',
               '( %s -> ( Y SmoothTD ( %s - 1 ) ) e. ( 2o X. NN0 ) )' % (ph, q_)), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, SM))
    ip1 = s([s([s([nums['qtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, q_)), w.inst('iptpos')], 'syl', '( %s -> 1 <_ %s )' % (ph, IP))], 'id', '') if False else \
        s([s([nums['qtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, q_)), w.inst('iptpos')], 'syl', '( %s -> 1 <_ %s )' % (ph, IP))
    for x_, st_ in ((IP, ipn), (SM, smn)):
        cl.leaf(x_, 'NN0', st_)
    # product facts
    IP1 = '( %s + 1 )' % IP
    h1_ = s([cl.mem(T37, 'RR'), cl.mem(XB, 'RR'), cl.mem(IP1, 'RR'), linarith(w, ph, [cl.ge0(IP)], '0 <_ %s' % IP1, closure=cl), m2], 'lemul2ad',
            '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, IP1, T37, IP1, XB))
    h2_ = s([s([closed(w, ph, '1re', '1 e. RR'), cl.mem(IP, 'RR'), cl.mem(XB, 'RR'), cl.ge0(XB), ip1], 'lemul1ad',
               '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, XB, IP, XB))], 'id', '') if False else \
        s([closed(w, ph, '1re', '1 e. RR'), cl.mem(IP, 'RR'), cl.mem(XB, 'RR'), cl.ge0(XB), ip1], 'lemul1ad',
          '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, XB, IP, XB))
    h3_ = s([cl.mem(SM, 'RR'), cl.mem(XB, 'RR'), cl.ge0(SM), cl.ge0(XB)], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (ph, SM, XB))
    # U ` i value: a_( i + 1 ) = a_i + CST
    stp = s([s([s([B.gn, B.ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([B.qnn, inn], 'jca', '( %s -> ( Q e. NN /\\ i e. NN0 ) )' % ph)],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ i e. NN0 ) ) )' % ph), w.inst('rgstep')], 'syl',
            '( %s -> %s = %s )' % (ph, RGX('Q', i1), STV('Q', 'i')))
    a1 = snd_of(w, ph, RGX('Q', i1), '( %s ++ %s )' % (LI('i'), KEEPW(q_)), '( %s + %s )' % (AI('i'), CST(q_)), stp,
                ex_(w, ph, '( %s ++ %s )' % (LI('i'), KEEPW(q_)), 'ovex'), ex_(w, ph, '( %s + %s )' % (AI('i'), CST(q_)), 'ovex'))
    cl.leaf(AI('i'), 'NN0', nums['an'])
    UV = UB('i')
    KA1, KA0 = '( %s x. %s )' % (K8X, AI(i1)), '( %s x. %s )' % (K8X, AI('i'))
    ka1 = s([a1], 'oveq2d', '( %s -> %s = ( %s x. ( %s + %s ) ) )' % (ph, KA1, K8X, AI('i'), CST(q_)))
    idn = lineq(w, ph, '( %s x. ( %s + %s ) )' % (K8X, AI('i'), CST(q_)),
                '( ( ( ( 8 x. ( %s x. %s ) ) + ( 8 x. ( %s x. %s ) ) ) + ( 8 x. ( %s x. %s ) ) ) + ( 8 x. %s ) )' % (XB, AI('i'), XB, IP, XB, SM, XB),
                closure=cl, products=True)
    id0 = lineq(w, ph, KA0, '( 8 x. ( %s x. %s ) )' % (XB, AI('i')), closure=cl, products=True)
    ka1b = s([ka1, idn], 'eqtrd', '( %s -> %s = ( ( ( ( 8 x. ( %s x. %s ) ) + ( 8 x. ( %s x. %s ) ) ) + ( 8 x. ( %s x. %s ) ) ) + ( 8 x. %s ) ) )'
             % (ph, KA1, XB, AI('i'), XB, IP, XB, SM, XB))
    a1n = s([rgcl(w, ph, 'Q', i1, B.gn, B.ynn, B.qnn, s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, i1))), w.inst('xp2nd')],
            'syl', '( %s -> %s e. NN0 )' % (ph, AI(i1)))
    k8n = lin_nn0(w, ph, '8', XB, closed(w, ph, '8nn0', '8 e. NN0'), xn, 'x.')
    cl.leaf(KA1, 'NN0', lin_nn0(w, ph, K8X, AI(i1), k8n, a1n, 'x.'))
    cl.leaf(KA0, 'NN0', lin_nn0(w, ph, K8X, AI('i'), k8n, nums['an'], 'x.'))
    AX = '( %s x. %s )' % (XB, AI('i'))
    le = linarith(w, ph, [ka1b, id0, h1_, h2_, h3_, m1, xp], '%s <_ %s' % (n, UV), closure=cl, products=True)
    uvn = linarith(w, ph, [ka1b, id0, h2_, h3_, xp], '0 <_ %s' % UV, closure=cl, products=True)
    uvz = s([s([cl.mem(UV, 'ZZ'), uvn], 'jca', '( %s -> ( %s e. ZZ /\\ 0 <_ %s ) )' % (ph, UV, UV)),
             s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (UV, UV, UV))], 'sylibr', '( %s -> %s e. NN0 )' % (ph, UV))
    uval = mval(w, ph, 'j', 'NN0', UB, 'i', inn, ex_(w, ph, UV, 'ovex'))
    UI = '( %s ` i )' % UF
    ue = s([uval], 'eqcomd', '( %s -> %s = %s )' % (ph, UV, UI))
    uin = s([uval, uvz], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, UI))
    t = hrle(w, ph, mk['phm'], t, C, D, n, UV, uvz, le)
    n = UV
    C2 = CLN(LMR['Y2'], NI, PB('i'))
    t = hrssc(w, ph, mk['phm'], t, C, D, n, C2, clnss(w, ph, LMR['Y2'], NI, S, PB('i'), B.famss('i', inn)))
    # post
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, i1))
    i1le = s([ilt, s([s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ph), s([B.hn], 'nn0zd', '( %s -> H e. ZZ )' % ph), w.inst('zltp1le')],
                     'syl2anc', '( %s -> ( i < H <-> ( i + 1 ) <_ H ) )' % ph)], 'mpbid', '( %s -> ( i + 1 ) <_ H )' % ph)
    nums1 = B.at(i1, i1n, i1le)
    pv1, S1 = B.pv(i1, i1n, nums1)
    P1T = '( %s ` ( i + 1 ) )' % PV
    ga = s([cl.mem('Q', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph), w.inst('addass')],
           'syl3anc', '( %s -> %s = %s )' % (ph, Q1_, QI(i1)))
    fe = s([cl.mem('H', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph), w.inst('subsub4')],
           'syl3anc', '( %s -> %s = %s )' % (ph, H1, HM(i1)))
    enc = s([s([s([s([B.gn, B.ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([B.qnn, inn], 'jca', '( %s -> ( Q e. NN /\\ i e. NN0 ) )' % ph)],
                  'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ i e. NN0 ) ) )' % ph), B.rw], 'jca',
               "( %s -> ( ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ i e. NN0 ) ) /\\ R e. Word Gamma' ) )" % ph), w.inst('rgenc')], 'syl',
            '( %s -> %s = %s )' % (ph, EL(i1), V5))
    RULES = {V5: (EL(i1), s([enc], 'eqcomd', '( %s -> %s = %s )' % (ph, V5, EL(i1)))), H1: (HM(i1), fe), Q1_: (QI(i1), ga)}
    Dst = triple_D(D)
    xn_ = chain_text('D', out2)
    assert Dst == xn_, (Dst, xn_)
    r2_, x2 = w.rewrite(xn_, RULES, ph)
    assert x2 == PB(i1), (x2, PB(i1))
    deq = s([r2_, pv1], 'eqtr4d', '( %s -> %s = %s )' % (ph, Dst, P1T))
    FIN = 'if ( %s = 0 , 1o , (/) )' % H1
    Ncur = D.split(' } X. ( ', 1)[1].rsplit(' X. { ', 1)[0]
    assert Ncur == NFL(FIN), Ncur
    rc, xc = w.rewrite(FIN, RULES, ph)
    assert xc == FLC(i1), xc
    N1 = '( %s ` ( i + 1 ) )' % NFM
    cq = s([nfl_eq(w, ph, FIN, FLC(i1), rc), s([famval(w, ph, COND, i1, i1n)], 'eqcomd', '( %s -> %s = %s )' % (ph, NCL(i1), N1))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, NFL(FIN), N1))
    lab_ = LMR['Z1']
    ceq = s([clnneq(w, ph, lab_, cq, NFL(FIN), N1, Dst), clneq(w, ph, lab_, N1, deq, Dst, P1T)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN(lab_, N1, P1T)))
    cpre = clneq(w, ph, LMR['Y2'], NI, s([pvi], 'eqcomd', '( %s -> %s = %s )' % (ph, PB('i'), PT)), PB('i'), PT)
    t, C, D, n = hrrw(w, ph, t, C2, D, n, ceq=cpre, deq=ceq, neq=ue)
    st = s([s([part1, uin], 'jca', '( %s -> ( A. m e. %s ( %s ` m ) = 1o /\\ %s e. NN0 ) )' % (ph, NI, CNFL, UI)), t], 'jca',
           '( %s -> %s )' % (ph, LBODY))
    finish(w, st, lab)
    return w.run()


def tmirgft():
    lab = 'tmirgft'
    w = W(lab, 'The frame of Lean\'s ` resGoF ` loop at the machine: for ` i <_ fuel ` the class family is a set of states and '
               'the stack family a stack assignment, and after ` fuel ` iterations the flag is set.')
    s = w.s
    TT = numtree((PSI_T, 'i e. ( 0 ... H )'))
    pt = cj(TT)
    B = Lr(w, pt, TT)
    ii = B.c['i e. ( 0 ... H )']
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ H )' % pt)
    nums = B.at('i', inn, ile)
    pv, St = B.pv('i', inn, nums)
    body = LTYP[len('A. i e. ( 0 ... H ) '):]
    one = s([B.famss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))
    k = s([], 't10stk', ST_NUMS)
    one0 = s([k, one], 'mpan2', '( %s -> %s )' % (cj((PSI_T, 'i e. ( 0 ... H )')), body))
    typ = s([one0], 'ralrimiva', '( %s -> %s )' % (PSI, LTYP))
    TE = numtree(PSI_T)
    pe = cj(TE)
    L = Lr(w, pe, TE)
    hh = s([s([L.hn], 'nn0cnd', '( %s -> H e. CC )' % pe)], 'subidd', '( %s -> ( H - H ) = 0 )' % pe)
    f1 = s([hh], 'iftrued', '( %s -> %s = 1o )' % (pe, FLC('H')))
    NE = '( %s ` H )' % NFM
    pm = '( %s /\\ m e. %s )' % (pe, NE)
    mm, mc = fam_unpack(w, pm, COND, 'H', lift_from(w, pe, pm, L.hn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)))
    fl = s([mc, lift_from(w, pe, pm, f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    from t9_m_loop import cnfl_at
    ex_ = s([cnfl_at(w, pm, mm, fl, True)], 'ralrimiva', '( %s -> %s )' % (pe, LEXIT))
    ex0 = s([k, ex_], 'mpan2', '( %s -> %s )' % (PSI, LEXIT))
    w.qed([typ, ex0], 'jca', STMTS10[lab])
    return w.run()


def tmirgfl():
    lab = 'tmirgfl'
    w = W(lab, 'Lean\'s ` resGoF ` loop at the machine: ~ tm2floop at the families ( ` P\' ` a letter), ` fuel ` iterations of '
               '` resGoBody ` (~ tmirgfi ), the frame by ~ tmirgft .')
    s = w.s
    T = numtree(PSI_T)
    ph = cj(T)
    B = Lr(w, ph, T)
    B.deep('rgf', 1)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmirgft', STMTS10['tmirgft']))
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    per = s([s([], 'tmirgfi', STMTS10['tmirgfi'])], 'ralrimiva', '( %s -> %s )' % (PSI, LPER))
    ex[LPER] = lift_from(w, PSI, ph, per)
    st = Bld(w, ph, B.c, ex)(LTREE)
    st2 = s([st, w.inst('tm2floop')], 'syl', '( %s -> %s )' % (ph, LCONCL))
    finish(w, st2, lab)
    return w.run()


def tmirgf():
    lab = 'tmirgf'
    T = numtree(TREE_RGF)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` resGoF_runs ` at the machine: ` isZero 3 6 ` , the loop (~ tmirgfl at the families of ` resGo z99 y q i ` ), '
               '` revList 5 4 6 ` ; the kept numbers are pushed on stack 4 in order (~ revrev ), the charges telescope (~ telfsumo2 ).')
    s = w.s
    B = Lr(w, ph, T)
    c, mk = B.c, B.mk
    TB = '( TMB ` B )'
    # 1. isZero 3 6
    R = B.run()
    B.call(R, 'tmiizbs', {'K': '3', 'I': '6', 'F': 'H', 'N': 'B', 'X': "Z'", 'P': PL('P', 1), 'E': LMR['Z1']},
           {'H < ( 2 ^ B )': linarith(w, ph, [c['( Q + H ) < ( 2 ^ B )'], _cl0(w, ph, B).ge0('Q')], 'H < ( 2 ^ B )',
                                      closure=_cl0(w, ph, B), atoms=['( 2 ^ B )'])}, [])
    # 2. to the family at 0
    z0 = closed(w, ph, '0nn0', '0 e. NN0')
    h0 = s([s([B.hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('subid1')], 'syl', '( %s -> ( H - 0 ) = H )' % ph)
    q0 = s([s([B.qnn], 'nncnd', '( %s -> Q e. CC )' % ph), w.inst('addrid')], 'syl', '( %s -> ( Q + 0 ) = Q )' % ph)
    r0 = s([s([s([B.gn, B.ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), B.qnn], 'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ Q e. NN ) )' % ph),
            w.inst('resgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (ph, RGX('Q', '0')))
    ee = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % ph)
    ze = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ph)
    l0 = fst_of(w, ph, RGX('Q', '0'), '(/)', '0', r0, ee, ze)
    a0 = snd_of(w, ph, RGX('Q', '0'), '(/)', '0', r0, ee, ze)
    rv0 = s([s([l0], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` (/) ) )' % (ph, LI('0'))),
             s([s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % ph)], 'eqtrd', '( %s -> ( reverse ` %s ) = (/) )' % (ph, LI('0')))
    en0 = s([s([rv0], 'fveq2d', '( %s -> ( encList ` ( reverse ` %s ) ) = ( encList ` (/) ) )' % (ph, LI('0'))),
             s([s([], 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'a1i', '( %s -> ( encList ` (/) ) = <" 2 "> )' % ph)], 'eqtrd',
            '( %s -> ( encList ` ( reverse ` %s ) ) = <" 2 "> )' % (ph, LI('0')))
    R0 = {HM('0'): ('H', h0), QI('0'): ('Q', q0), '( encList ` ( reverse ` %s ) )' % LI('0'): ('<" 2 ">', en0)}
    rcl, xcl = w.rewrite(FLC('0'), R0, ph)
    N0 = '( %s ` 0 )' % NFM
    ceq0 = s([s([famval(w, ph, COND, '0', z0), nfl_eq(w, ph, FLC('0'), xcl, rcl)], 'eqtrd', '( %s -> %s = %s )' % (ph, N0, NFL(xcl)))], 'eqcomd',
             '( %s -> %s = %s )' % (ph, NFL(xcl), N0))
    zle = s([B.hn], 'nn0ge0d', '( %s -> 0 <_ H )' % ph)
    nums0 = B.at('0', z0, zle)
    Sp0 = B.pbst('0', nums0)
    pfv = mval(w, ph, 'j', 'NN0', PB, '0', z0, s([Sp0.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB('0'))))
    rs, xs = w.rewrite(PB('0'), R0, ph)
    kd = lambda k_: mk['k'][k_]['kd']
    cur_ = xs
    chain = s([pfv, rs], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PF, xs))
    for k_, v_ in (('2', EWg('Q', 'Z')), ('3', EWg('H', "Z'"))):
        u_ = upidv(w, ph, 'D', k_, v_, B.S0.vals[k_][1], mk['tv'], B.dd, kd(k_))
        r_, x_ = w.rewrite(cur_, {UP('D', k_, v_): ('D', u_)}, ph)
        chain = s([chain, r_], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PF, x_))
        cur_ = x_
    assert cur_ == UP('D', '5', '( <" 2 "> ++ R )'), cur_
    u5 = upidv(w, ph, 'D', '5', '( <" 2 "> ++ R )', B.S0.vals['5'][1], mk['tv'], B.dd, kd('5'))
    pf0 = '( %s ` 0 )' % PF
    se = s([s([chain, u5], 'eqtrd', '( %s -> %s = D )' % (ph, pf0))], 'eqcomd', '( %s -> D = %s )' % (ph, pf0))
    lab0 = LMR['Z1']
    ceq = s([clnneq(w, ph, lab0, ceq0, NFL(xcl), N0, 'D'), clneq(w, ph, lab0, N0, se, 'D', pf0)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, R.cur, CLN(lab0, N0, pf0)))
    t1, C1, D1, n1 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=ceq)
    # 3. the loop
    ex = {'%s = %s' % (PF, PF): s([s([], 'eqid', '%s = %s' % (PF, PF))], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}
    tl, cl_ = inst(w, ph, 'tmirgfl', {PV: PF}, Bld(w, ph, c, ex))
    C2, D2, n2 = triple_parts(cl_)
    assert C2 == D1, (C2, D1)
    t = hrseq(w, ph, mk['phm'], t1, tl, C1, D1, D2, n1, n2)
    n = '( %s + %s )' % (n1, n2)
    # 4. ( PF ` H ) = PB( H ) ; revList 5 4 6
    numsH = B.at('H', B.hn, s([s([B.hn], 'nn0red', '( %s -> H e. RR )' % ph)], 'leidd', '( %s -> H <_ H )' % ph))
    SpH = B.pbst('H', numsH)
    pfh = mval(w, ph, 'j', 'NN0', PB, 'H', B.hn, s([SpH.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB('H'))))
    PFH = '( %s ` H )' % PF
    NH = '( %s ` H )' % NFM
    t, C, D, n = hrrw(w, ph, t, C1, D2, n, deq=clneq(w, ph, LMR['Y3'], NH, pfh, PFH, PB('H')))
    R2 = B.run()
    R2.S, R2.chain = SpH, list(B.last)
    for _k, (_txt, _st, _g) in SpH.vals.items():
        R2.gam[_txt] = _g
    LH = LI('H')
    RLH = '( reverse ` %s )' % LH
    # the entries of the list are below 2 ^ B (~ resgomem , ~ tm2lrnrev )
    pa = '( %s /\\ a e. ran %s )' % (ph, RLH)
    ain = s([s([], 'simpr', '( %s -> a e. ran %s )' % (pa, RLH)), s([lift_from(w, ph, pa, numsH['lw']), w.inst('tm2lrnrev')], 'syl',
                                                                    '( %s -> ran %s C_ ran %s )' % (pa, RLH, LH))], 'sseldd' if False else 'ssneld' if False else 'sseldd', '') if False else \
        s([s([lift_from(w, ph, pa, numsH['lw']), w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (pa, RLH, LH)),
           s([], 'simpr', '( %s -> a e. ran %s )' % (pa, RLH))], 'sseldd', '( %s -> a e. ran %s )' % (pa, LH))
    lwv = lift_from(w, ph, pa, numsH['lw'])
    an0 = s([s([lwv, w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, LH, LH)) if False else None] if False else [], 'id', '') if False else None
    frn = s([s([lwv, w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, LH, LH)), w.inst('frnd') if False else w.inst('frn')], 'syl',
            '( %s -> ran %s C_ NN0 )' % (pa, LH))
    ann = s([frn, ain], 'sseldd', '( %s -> a e. NN0 )' % pa)
    gm = s([s([s([lift_from(w, ph, pa, B.gn), lift_from(w, ph, pa, B.ynn), lift_from(w, ph, pa, B.qnn)], '3jca',
                 '( %s -> ( G e. NN0 /\\ Y e. NN /\\ Q e. NN ) )' % pa), s([lift_from(w, ph, pa, B.hn), ann], 'jca', '( %s -> ( H e. NN0 /\\ a e. NN0 ) )' % pa)],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN /\\ Q e. NN ) /\\ ( H e. NN0 /\\ a e. NN0 ) ) )' % pa), w.inst('resgomem')], 'syl',
           '( %s -> ( a e. ran %s <-> ( ( Q <_ a /\\ a < ( Q + H ) ) /\\ ( G < a /\\ a e. Prime /\\ A. p e. Prime ( p || ( a - 1 ) -> p <_ Y ) ) ) ) )' % (pa, LH))
    gm2 = s([ain, gm], 'mpbid', '( %s -> ( ( Q <_ a /\\ a < ( Q + H ) ) /\\ ( G < a /\\ a e. Prime /\\ A. p e. Prime ( p || ( a - 1 ) -> p <_ Y ) ) ) )' % pa)
    alq = s([s([gm2], 'simpld', '( %s -> ( Q <_ a /\\ a < ( Q + H ) ) )' % pa)], 'simprd', '( %s -> a < ( Q + H ) )' % pa)
    clp = Closure(w, pa, {'a': ('NN0', ann), 'B': ('NN0', lift_from(w, ph, pa, B.bn))})
    clp.leaf('( Q + H )', 'NN0', s([lift_from(w, ph, pa, B.qn), lift_from(w, ph, pa, B.hn), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( Q + H ) e. NN0 )' % pa))
    alt = linarith(w, pa, [alq, lift_from(w, ph, pa, c['( Q + H ) < ( 2 ^ B )'])], 'a < ( 2 ^ B )', closure=clp)
    ral = s([alt], 'ralrimiva', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (ph, RLH))
    E4 = '( ( encList ` ( reverse ` %s ) ) ++ %s )' % (RLH, DK(4))
    g4 = wgcat(w, ph, '( encList ` ( reverse ` %s ) )' % RLH, DK(4),
               s([s([numsH['rl'], w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word NN0 )' % (ph, RLH)), w.inst('tm2lenccl')], 'syl',
                 "( %s -> ( encList ` ( reverse ` %s ) ) e. Word Gamma' )" % (ph, RLH)), B.S0.vals['4'][2])
    B.call(R2, 'tmilrevb', {'K': '5', 'J': '4', 'I': '6', 'L': RLH, 'R': 'R', 'B': 'B', 'P': PL('P', 3), 'E': 'E'},
           {'%s e. Word NN0' % RLH: numsH['rl'], 'A. a e. ran %s a < ( 2 ^ B )' % RLH: ral}, [('5', 'R', B.rw), ('4', E4, B.g(E4, g4))],
           pre=(NH, B.famss('H', B.hn)))
    cur, of = R2.normalize(['0', '1', '6', '7', '2', '3', '4', '5'])
    t3, C3, D3, n3 = R2.tri, R2.C0, R2.cur, R2.n
    assert C3 == D, (C3, D)
    t = hrseq(w, ph, mk['phm'], t, t3, C1, D, D3, n, n3)
    n = '( %s + %s )' % (n, n3)
    # the stacks
    hh = s([s([B.hn], 'nn0cnd', '( %s -> H e. CC )' % ph)], 'subidd', '( %s -> ( H - H ) = 0 )' % ph)
    rr_ = s([numsH['lw'], w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = %s )' % (ph, RLH, LH))
    Dc = triple_D(D3)
    rf, xf = w.rewrite(Dc, {HM('H'): ('0', hh), '( reverse ` %s )' % RLH: (LH, rr_)}, ph)
    DF_ = UPS('D', ('2', EWg('( Q + H )', 'Z')), ('3', EWg('0', "Z'")), ('4', ENCL('( 1st ` %s )' % RG_, DK(4))), ('5', 'R'))
    assert xf == DF_, (xf, DF_)
    t, C, D, n = hrrw(w, ph, t, C1, D3, n, deq=clneq(w, ph, 'E', S, rf, Dc, xf))
    # 5. the bound
    SMT = 'sum_ i e. ( 0 ..^ H ) ( ( %s ` i ) + 1 )' % UF
    KA = lambda k_: '( %s x. %s )' % (K8X, AI(k_))
    pi = '( %s /\\ i e. ( 0 ..^ H ) )' % ph
    iin = s([s([], 'simpr', '( %s -> i e. ( 0 ..^ H ) )' % pi), w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    uv = mval(w, pi, 'j', 'NN0', UB, 'i', iin, ex_(w, pi, UB('i'), 'ovex'))
    DIF = '( %s - %s )' % (KA('( i + 1 )'), KA('i'))

    def k8c(pp):
        b410 = s([s([closed(w, pp, '4nn0', '4 e. NN0'), lift_from(w, ph, pp, B.bn), w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % pp),
                  closed(w, pp, '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % pp)
        xn = tmbn(w, pp, '( ( 4 x. B ) + ; 1 0 )', b410)
        return s([closed(w, pp, '8nn0', '8 e. NN0'), xn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pp, K8X))

    def asn(pp, tt, ttn):
        xc = rgcl(w, pp, 'Q', tt, lift_from(w, ph, pp, B.gn), lift_from(w, ph, pp, B.ynn), lift_from(w, ph, pp, B.qnn), ttn)
        return s([xc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pp, AI(tt)))
    i1n = s([iin, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    k8 = k8c(pi)
    dcc = s([s([s([k8], 'nn0cnd', '( %s -> %s e. CC )' % (pi, K8X)), s([asn(pi, '( i + 1 )', i1n)], 'nn0cnd', '( %s -> %s e. CC )' % (pi, AI('( i + 1 )')))],
               'mulcld', '( %s -> %s e. CC )' % (pi, KA('( i + 1 )'))),
             s([s([k8], 'nn0cnd', '( %s -> %s e. CC )' % (pi, K8X)), s([asn(pi, 'i', iin)], 'nn0cnd', '( %s -> %s e. CC )' % (pi, AI('i')))],
               'mulcld', '( %s -> %s e. CC )' % (pi, KA('i')))], 'subcld', '( %s -> %s e. CC )' % (pi, DIF))
    npc = s([dcc, s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % pi), w.inst('npcan')], 'syl2anc',
            '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (pi, DIF, DIF))
    term = s([s([uv], 'oveq1d', '( %s -> ( ( %s ` i ) + 1 ) = ( %s + 1 ) )' % (pi, UF, UB('i'))), npc], 'eqtrd',
             '( %s -> ( ( %s ` i ) + 1 ) = %s )' % (pi, UF, DIF))
    se_ = s([term], 'sumeq2dv', '( %s -> %s = sum_ i e. ( 0 ..^ H ) %s )' % (ph, SMT, DIF))

    def kcong(a_):
        e = s([], 'id', '( k = %s -> k = %s )' % (a_, a_))
        cg, new = w.congr(KA('k'), {'k': a_}, 'k = %s' % a_, {'k': e})
        assert new == KA(a_), new
        return cg
    huz = s([B.hn, s([s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % ph)], 'eleqtrd', '( %s -> H e. ( ZZ>= ` 0 ) )' % ph)
    pk = '( %s /\\ k e. ( 0 ... H ) )' % ph
    kn_ = s([s([], 'simpr', '( %s -> k e. ( 0 ... H ) )' % pk), w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    kac = s([s([k8c(pk)], 'nn0cnd', '( %s -> %s e. CC )' % (pk, K8X)), s([asn(pk, 'k', kn_)], 'nn0cnd', '( %s -> %s e. CC )' % (pk, AI('k')))], 'mulcld',
            '( %s -> %s e. CC )' % (pk, KA('k')))
    tel = s([kcong('i'), kcong('( i + 1 )'), kcong('0'), kcong('H'), huz, kac], 'telfsumo2',
            '( %s -> sum_ i e. ( 0 ..^ H ) %s = ( %s - %s ) )' % (ph, DIF, KA('H'), KA('0')))
    k8h = k8c(ph)
    k00 = s([s([a0], 'oveq2d', '( %s -> %s = ( %s x. 0 ) )' % (ph, KA('0'), K8X)), s([s([k8h], 'nn0cnd', '( %s -> %s e. CC )' % (ph, K8X)), w.inst('mul01')],
                                                                                       'syl', '( %s -> ( %s x. 0 ) = 0 )' % (ph, K8X))], 'eqtrd',
            '( %s -> %s = 0 )' % (ph, KA('0')))
    stl = s([se_, tel], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (ph, SMT, KA('H'), KA('0')))
    cl = Closure(w, ph, {'B': ('NN0', B.bn), 'H': ('NN0', B.hn)})
    XBn = s([s([k8h], 'id', '') if False else None] if False else [], 'id', '') if False else None
    b410 = s([s([closed(w, ph, '4nn0', '4 e. NN0'), B.bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % ph),
              closed(w, ph, '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % ph)
    xn = tmbn(w, ph, '( ( 4 x. B ) + ; 1 0 )', b410)
    tbn = tmbn(w, ph, 'B', B.bn)
    cl.leaf(XB, 'NN0', xn)
    cl.leaf(TB, 'NN0', tbn)
    ahn = asn(ph, 'H', B.hn)
    cl.leaf(AI('H'), 'NN0', ahn)
    LLH = '( # ` %s )' % RLH
    lln = s([numsH['rl'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LLH))
    cl.leaf(LLH, 'NN0', lln)
    BND = '( ( %s + 1 ) x. ( ; 1 1 x. %s ) )' % (AI('H'), XB)
    kh = lineq(w, ph, BND, '( ( ; 1 1 x. ( %s x. %s ) ) + ( ; 1 1 x. %s ) )' % (AI('H'), XB, XB), closure=cl, products=True)
    kah = lineq(w, ph, KA('H'), '( 8 x. ( %s x. %s ) )' % (AI('H'), XB), closure=cl, products=True)
    rl1 = s([s([numsH['lw'], w.inst('revlen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ph, LLH, LH)),
             s([s([s([s([B.gn, B.ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([B.qnn, B.hn], 'jca', '( %s -> ( Q e. NN /\\ H e. NN0 ) )' % ph)],
                     'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ H e. NN0 ) ) )' % ph), w.inst('rgln')], 'syl',
                 '( %s -> ( ( # ` %s ) <_ H /\\ H <_ %s ) )' % (ph, LH, AI('H')))], 'id', '') if False else None], 'id', '') if False else None
    rgl = s([s([s([B.gn, B.ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([B.qnn, B.hn], 'jca', '( %s -> ( Q e. NN /\\ H e. NN0 ) )' % ph)],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ H e. NN0 ) ) )' % ph), w.inst('rgln')], 'syl',
            '( %s -> ( ( # ` %s ) <_ H /\\ H <_ %s ) )' % (ph, LH, AI('H')))
    rvl = s([numsH['lw'], w.inst('revlen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ph, LLH, LH))
    lle = s([s([rvl, s([rgl], 'simpld', '( %s -> ( # ` %s ) <_ H )' % (ph, LH))], 'eqbrtrd', '( %s -> %s <_ H )' % (ph, LLH)),
             s([rgl], 'simprd', '( %s -> H <_ %s )' % (ph, AI('H')))], 'jca', '') if False else None
    l1 = s([rvl, s([rgl], 'simpld', '( %s -> ( # ` %s ) <_ H )' % (ph, LH))], 'eqbrtrd', '( %s -> %s <_ H )' % (ph, LLH))
    l2 = s([rgl], 'simprd', '( %s -> H <_ %s )' % (ph, AI('H')))
    m1 = s([B.bn, b410, linarith(w, ph, [cl.ge0('B')], 'B <_ ( ( 4 x. B ) + ; 1 0 )', closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, XB))
    la = linarith(w, ph, [l1, l2], '%s <_ %s' % (LLH, AI('H')), closure=cl)
    pr1 = s([cl.mem(LLH, 'RR'), cl.mem(AI('H'), 'RR'), cl.mem(TB, 'RR'), cl.ge0(TB), la], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, LLH, TB, AI('H'), TB))
    pr2 = s([cl.mem(TB, 'RR'), cl.mem(XB, 'RR'), cl.mem(AI('H'), 'RR'), cl.ge0(AI('H')), m1], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, AI('H'), TB, AI('H'), XB))
    xp = s([s([b410, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, XB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, XB))
    cl.leaf(SMT, 'RR', s([stl, s([s([s([k8h, ahn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, KA('H')))], 'nn0red', '( %s -> %s e. RR )' % (ph, KA('H'))),
                                 s([s([k8h, s([s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % ph) if False else closed(w, ph, '0nn0', '0 e. NN0'), w.inst('nn0mulcl')], 'syl2anc', '') if False else
                                    s([k00, closed(w, ph, '0re', '0 e. RR')], 'eqeltrd', '( %s -> %s e. RR )' % (ph, KA('0')))], 'id', '') if False else
                                 s([k00, closed(w, ph, '0re', '0 e. RR')], 'eqeltrd', '( %s -> %s e. RR )' % (ph, KA('0')))], 'resubcld',
                               '( %s -> ( %s - %s ) e. RR )' % (ph, KA('H'), KA('0')))], 'eqeltrd', '( %s -> %s e. RR )' % (ph, SMT)))
    cl.leaf(AI('0'), 'NN0', s([a0, closed(w, ph, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, AI('0'))))
    ax0 = s([cl.mem(AI('H'), 'RR'), cl.mem(XB, 'RR'), cl.ge0(AI('H')), cl.ge0(XB)], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (ph, AI('H'), XB))
    lt0 = s([cl.mem(LLH, 'RR'), cl.mem(TB, 'RR'), cl.ge0(LLH), cl.ge0(TB)], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (ph, LLH, TB))
    le = linarith(w, ph, [stl, k00, kh, kah, pr1, pr2, m1, xp, ax0, lt0], '%s <_ %s' % (n, BND), closure=cl, products=True)
    bn_ = s([s([ahn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, AI('H'))),
             s([closed(w, ph, '11nn0' if False else '11nn0', '; 1 1 e. NN0') if False else s([s([], '1nn0', '1 e. NN0'), s([], '1nn0', '1 e. NN0')], 'deccl', '; 1 1 e. NN0') if False else
                closed(w, ph, 'dec11nn0' if False else '11nn0', '; 1 1 e. NN0'), xn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( ; 1 1 x. %s ) e. NN0 )' % (ph, XB)),
             w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, BND))
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, bn_, le)
    finish(w, st, lab)
    return w.run()


def _cl0(w, ph, B):
    cl = Closure(w, ph, {'Q': ('NN', B.qnn), 'H': ('NN0', B.hn), 'B': ('NN0', B.bn)})
    return cl


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
