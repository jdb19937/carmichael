"""T10: the smoothGo loop ` loop ( !flag ) smoothGoBody ` of ` smoothGoF ` at the machine (Lean ` smoothGoF_le_B ` ) at
` xd xr xf xF s t u = 4 6 7 0 1 2 3 ` , on TMIsgf, at the families of ~ sgsh ( ` d + i ` , ` r_i ` , ` fuel - i ` ), with
the Sum-form loop rule ~ tm2floop (per-iteration charge ` K ( a_( i + 1 ) - a_i ) - 1 ` , ` K = B ( 4 b + 10 ) ` ,
telescoping to Lean's ` ( smoothGo d r fuel ).2 * K ` ).

  tmisgfi   one iteration (the body ` dup ; divOutF ; dropNum ; incr ; predNum ; isZero ` )
  tmisgft   the frame
  tmisgfl   ~ tm2floop at the families
  tmisgfb   smoothGoF_le_B

    MM_DB=sorties/t10.mm python3 tools/gen/t10_h_sgf.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import famval, fam_unpack, ifex_closed, mval
from cl import Closure
from t10_e_doa import DOX, P1, P2, RI, SHV, snd_of, fst_of, ex_, lift_from
from t10_g_sga import SGX, DOG, RS, AS, GI, QS, CS, ST_SGSTEP, ST_SGFLE, sgcl, docl, comp
from t10_f_dof import cnd_fl
from t5lib import hrssd

SEL = sys.argv[1:]
LMS = FRAGS['sgf'].lmap()
HM = lambda t: '( H - %s )' % t
PB = lambda t: UPS('D', ('0', EWg(HM(t), 'Y')), ('4', EWg(GI(t), 'X')), ('6', EWg(RS(t), "X'")))
FLC = lambda t: 'if ( %s = 0 , 1o , (/) )' % HM(t)
COND = lambda h, t: '( TMfl ` %s ) = %s' % (h, FLC(t))
NCL = lambda t: '{ h e. TMSt | %s }' % COND('h', t)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
PF = '( j e. NN0 |-> %s )' % PB('j')
PV = "P'"
KB = '( TMB ` ( ( 4 x. B ) + ; 1 0 ) )'
UB = lambda t: '( ( ( %s x. %s ) - ( %s x. %s ) ) - 1 )' % (KB, AS('( %s + 1 )' % t), KB, AS(t))
UF = '( j e. NN0 |-> %s )' % UB('j')
PSI_T = (TREE_SGF, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
GM = {'A': LMS['Z1'], 'B0': LMS['Y2'], 'E': 'E', 'C0': CNFL, 'R': 'H', 'N': NFM, 'P': PV, 'U': UF}
_LA, _LC = split_imp(stmt('tm2floop'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
_pre = 'A. i e. ( 0 ..^ H ) '
assert LPER.startswith(_pre)
LBODY = LPER[len(_pre):]
T_I = (PSI_T, 'i e. ( 0 ..^ H )')
add_stmt('tmisgfi', T_I, LBODY)
add_stmt('tmisgft', PSI_T, '( %s /\\ %s )' % (LTYP, LEXIT))
add_stmt('tmisgfl', PSI_T, LCONCL)
add_stmt('tmisgfb', TREE_SGF, CONCL_SGF)
ORD046 = ['1', '2', '3', '5', '7', '0', '4', '6']


class Ls(Base):
    def __init__(self, w, ph, T, fname='sgf'):
        c0 = Ctx(w, ph, T)
        gnn, fn, hn = c0['G e. NN'], c0['F e. NN0'], c0['H e. NN0']
        gn = w.s([gnn], 'nnnn0d', '( %s -> G e. NN0 )' % ph)
        xw, x2w, yw = c0[WG('X')], c0[WG("X'")], c0[WG('Y')]
        eqs = {'4': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xw)), '6': (EWg('F', "X'"), ewg_(w, ph, 'F', fn, "X'", x2w)),
               '0': (EWg('H', 'Y'), ewg_(w, ph, 'H', hn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, fname, eqs)
        s = w.s
        self.gnn, self.gn, self.fn, self.hn, self.bn = gnn, gn, fn, hn, self.c['B e. NN0']
        self.xw, self.x2w, self.yw = xw, x2w, yw
        self.ph2 = s([gnn, fn], 'jca', '( %s -> ( G e. NN /\\ F e. NN0 ) )' % ph)
        self.tbn = s([s([self.bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d',
                     '( %s -> ( TMB ` B ) e. NN0 )' % ph)
        self.pvs = {}

    def at(self, t, tn, tle):
        """numbers at t e. NN0 , t <_ H"""
        w, ph, s = self.w, self.ph, self.w.s
        xc = sgcl(w, ph, 'G', 'F', t, self.gnn, self.fn, tn)
        rn = comp(w, ph, SGX('G', 'F', t), xc, 1)
        an = comp(w, ph, SGX('G', 'F', t), xc, 2)
        gtn = s([self.gnn, tn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, GI(t)))
        hmn = s([tn, self.hn, tle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, HM(t)))
        rle = s([s([self.ph2, tn], 'jca', '( %s -> ( ( G e. NN /\\ F e. NN0 ) /\\ %s e. NN0 ) )' % (ph, t)), w.inst('sgfle')], 'syl',
                '( %s -> %s <_ F )' % (ph, RS(t)))
        return dict(rn=rn, an=an, gtn=gtn, hmn=hmn, rle=rle, xc=xc)

    def pbst(self, t, nums):
        w, ph = self.w, self.ph
        g0 = self.g(EWg(HM(t), 'Y'), ewg_(w, ph, HM(t), nums['hmn'], 'Y', self.yw))
        g4 = self.g(EWg(GI(t), 'X'), ewg_(w, ph, GI(t), w.s([nums['gtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, GI(t))), 'X', self.xw))
        g6 = self.g(EWg(RS(t), "X'"), ewg_(w, ph, RS(t), nums['rn'], "X'", self.x2w))
        self.last = [('0', EWg(HM(t), 'Y')), ('4', EWg(GI(t), 'X')), ('6', EWg(RS(t), "X'"))]
        return self.S0.upd('0', EWg(HM(t), 'Y'), g0).upd('4', EWg(GI(t), 'X'), g4).upd('6', EWg(RS(t), "X'"), g6)

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


def pos_tmb(w, ph, bn, b):
    s = w.s
    return s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` %s ) e. NN )' % (ph, b)), w.inst('nnge1')], 'syl',
             '( %s -> 1 <_ ( TMB ` %s ) )' % (ph, b))


def tmisgfi():
    lab = 'tmisgfi'
    T = numtree(T_I)
    ph = cj(T)
    w = W(lab, 'One iteration of Lean\'s ` smoothGoF ` loop at the machine ( ` SGInv ` , ` smoothGoBody_runs ` ): below the fuel '
               'the flag is clear, and ` smoothGoBody ` ( ` dup xr xf s ; divOutF ; dropNum xf ; incr xd s ; predNum xF s ; '
               'isZero xF s ` ) takes the family at ` i ` to the family at ` i + 1 ` (~ sgstep ) within ` K ( a_( i + 1 ) - a_i ) - 1 ` '
               'steps, ` K = B ( 4 b + 10 ) ` .')
    s = w.s
    B = Ls(w, ph, T)
    c, mk = B.c, B.mk
    B.deep('sgf', 1)
    io = c['i e. ( 0 ..^ H )']
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < H )' % ph)
    cl = Closure(w, ph, {'i': ('NN0', inn), 'H': ('NN0', B.hn), 'F': ('NN0', B.fn), 'B': ('NN0', B.bn), 'G': ('NN', B.gnn)})
    ile = linarith(w, ph, [ilt], 'i <_ H', closure=cl)
    nums = B.at('i', inn, ile)
    # the flag
    hne = s([s([cl.mem(HM('i'), 'RR') if False else linarith(w, ph, [ilt], '0 < %s' % HM('i'), closure=cl)], 'gt0ne0d',
               '( %s -> %s =/= 0 )' % (ph, HM('i'))) if False else None] if False else [], 'id', '') if False else None
    hpos = linarith(w, ph, [ilt], '0 < %s' % HM('i'), closure=cl)
    hne0 = s([hpos], 'gt0ne0d', '( %s -> %s =/= 0 )' % (ph, HM('i')))
    f0 = s([s([hne0], 'neneqd', '( %s -> -. %s = 0 )' % (ph, HM('i')))], 'iffalsed', '( %s -> %s = (/) )' % (ph, FLC('i')))
    NI = '( %s ` i )' % NFM
    pm = '( %s /\\ m e. %s )' % (ph, NI)
    mm, mc = fam_unpack(w, pm, COND, 'i', lift_from(w, ph, pm, inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl0 = s([mc, lift_from(w, ph, pm, f0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    from t9_m_loop import cnfl_at
    part1 = s([cnfl_at(w, pm, mm, fl0, False)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ph, NI, CNFL))
    # U ` i
    UV = UB('i')
    i1 = '( i + 1 )'
    stp = s([s([B.ph2, inn], 'jca', '( %s -> ( ( G e. NN /\\ F e. NN0 ) /\\ i e. NN0 ) )' % ph), w.inst('sgstep')], 'syl',
            '( %s -> ( %s = %s /\\ %s = ( ( %s + %s ) + 1 ) ) )' % (ph, RS(i1), QS('i'), AS(i1), AS('i'), CS('i')))
    rq = s([stp], 'simpld', '( %s -> %s = %s )' % (ph, RS(i1), QS('i')))
    aq = s([stp], 'simprd', '( %s -> %s = ( ( %s + %s ) + 1 ) )' % (ph, AS(i1), AS('i'), CS('i')))
    Dg = DOG(GI('i'), RS('i'), RS('i'))
    dcl = docl(w, ph, GI('i'), RS('i'), RS('i'), nums['gtn'], nums['rn'], nums['rn'])
    cn = comp(w, ph, Dg, dcl, 2)
    qn = comp(w, ph, Dg, dcl, 1)
    B1 = '( B + 1 )'
    b1n = s([B.bn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, B1))
    TB1 = '( TMB ` %s )' % B1
    k410 = s([B.bn, w.inst('tplb410')], 'syl', '( %s -> %s = ( ; 6 4 x. %s ) )' % (ph, KB, TB1))
    t1n = s([s([b1n, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB1))
    cl.leaf(TB1, 'NN0', t1n)
    cl.leaf(CS('i'), 'NN0', cn)
    cl.leaf(AS('i'), 'NN0', nums['an'])
    cl.leaf(AS(i1), 'NN0', comp(w, ph, SGX('G', 'F', i1), sgcl(w, ph, 'G', 'F', i1, B.gnn, B.fn, s([inn, w.inst('peano2nn0')], 'syl',
                                                                                                       '( %s -> %s e. NN0 )' % (ph, i1))), 2))
    kn = s([s([s([s([closed(w, ph, '4nn0', '4 e. NN0'), B.bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % ph),
                  closed(w, ph, ';10nn0' if False else 'dec10nn0' if False else '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc',
                 '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % ph), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, KB))], 'nnnn0d',
           '( %s -> %s e. NN0 )' % (ph, KB))
    cl.leaf(KB, 'NN0', kn)
    t1p = pos_tmb(w, ph, b1n, B1)
    # the value K ( c + 1 ) - 1 of U ` i
    KA1, KA0 = '( %s x. %s )' % (KB, AS(i1)), '( %s x. %s )' % (KB, AS('i'))
    KC = '( %s x. %s )' % (TB1, CS('i'))
    ka1 = s([s([aq], 'oveq2d', '( %s -> %s = ( %s x. ( ( %s + %s ) + 1 ) ) )' % (ph, KA1, KB, AS('i'), CS('i')))], 'id', '') if False else \
        s([aq], 'oveq2d', '( %s -> %s = ( %s x. ( ( %s + %s ) + 1 ) ) )' % (ph, KA1, KB, AS('i'), CS('i')))
    # bits: numbers < 2 ^ ( B + 1 )
    p2, p21 = '( 2 ^ B )', '( 2 ^ %s )' % B1
    ex2 = s([s([closed(w, ph, '2cn', '2 e. CC'), B.bn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ph, p21, p2))], 'id', '') if False else \
        s([closed(w, ph, '2cn', '2 e. CC'), B.bn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ph, p21, p2))
    cl.atom(p2)
    cl.atom(p21)
    rlt = linarith(w, ph, [nums['rle'], c['F < ( 2 ^ B )']], '%s < %s' % (RS('i'), p2), closure=cl,
                   atoms=[RS('i'), p2]) if False else None
    cl.leaf(RS('i'), 'NN0', nums['rn'])
    rlt = linarith(w, ph, [nums['rle'], c['F < ( 2 ^ B )']], '%s < %s' % (RS('i'), p2), closure=cl)
    r1lt = linarith(w, ph, [rlt, ex2, cl.ge0(RS('i'))], '%s < %s' % (RS('i'), p21), closure=cl)
    glt1 = linarith(w, ph, [c['G < ( 2 ^ B )'], c['H < ( 2 ^ B )'], ilt, ex2, cl.ge0('i')], '%s < %s' % (GI('i'), p21), closure=cl)
    # the run from PB( i )
    pvi, SI = B.pv('i', inn, nums)
    PT = '( %s ` i )' % PV
    Spb = B.pbst('i', nums)
    chain0 = list(B.last)
    R = B.run()
    R.S, R.chain = Spb, list(chain0)
    for _k, (_txt, _st, _g) in Spb.vals.items():
        R.gam[_txt] = _g
    Pb = lambda k: PL(PL('P', 2), k)
    LB = FRAGS['sgb'].lmap(PL('P', 2), LMS['Z1'])
    # 1. dup 6 7 1
    E7 = EWg(RS('i'), DK(7))
    B.call(R, 'tmidupb', {'K': '6', 'J': '7', 'I': '1', 'F': RS('i'), 'N': 'B', 'X': "X'", 'P': Pb(0), 'E': LB['Y2']},
           {'%s e. NN0' % RS('i'): nums['rn'], '%s < %s' % (RS('i'), p2): rlt}, [('7', E7, B.g(E7, ewg_(w, ph, RS('i'), nums['rn'], DK(7), B.gam[DK(7)])))])
    # 2. divOutF at ( G + i ) , r_i , fuel r_i , width B + 1
    Q6 = EWg(QS('i'), "X'")
    RM = '( %s - %s )' % (RS('i'), CS('i'))
    E7b = EWg(RM, DK(7))
    # c_i <_ r_i (dosh at the count)
    Rc = CS('i')
    rcle0 = s([s([s([nums['gtn'], nums['rn'], nums['rn']], '3jca', '( %s -> ( %s e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ph, GI('i'), RS('i'), RS('i'))),
                  s([cn, s([s([cn], 'nn0red', '( %s -> %s e. RR )' % (ph, Rc))], 'leidd', '( %s -> %s <_ %s )' % (ph, Rc, Rc))], 'jca',
                    '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ph, Rc, Rc, Rc))], 'jca',
                 '( %s -> ( ( %s e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s <_ %s ) ) )' % (ph, GI('i'), RS('i'), RS('i'), Rc, Rc, Rc)),
               s([], 'dosh' if False else 'dosh', '') if False else w.inst_sub('dosh', {}) if False else None] if False else [], 'id', '') if False else None
    shv = tsub_text(SHV('I'), {'G': GI('i'), 'F': RS('i'), 'H': RS('i'), 'I': Rc})
    dsh = inst(w, ph, 'dosh', {'G': GI('i'), 'F': RS('i'), 'H': RS('i'), 'I': Rc},
               Bld(w, ph, c, {'%s e. NN' % GI('i'): nums['gtn'], '%s e. NN0' % RS('i'): nums['rn'], '%s e. NN0' % Rc: cn,
                              '%s <_ %s' % (Rc, Rc): s([s([cn], 'nn0red', '( %s -> %s e. RR )' % (ph, Rc))], 'leidd', '( %s -> %s <_ %s )' % (ph, Rc, Rc))}))[0]
    rcle = s([dsh], 'simpld', '( %s -> %s <_ %s )' % (ph, Rc, RS('i')))
    rmn = s([cn, nums['rn'], rcle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, RM))
    B.call(R, 'tmidofb', {'G': GI('i'), 'F': RS('i'), 'H': RS('i'), 'B': B1, 'X': 'X', "X'": "X'", 'Y': DK(7), 'P': Pb(1), 'E': LB['Y3']},
           {'%s e. NN' % GI('i'): nums['gtn'], '%s e. NN0' % RS('i'): nums['rn'], '%s e. NN0' % B1: b1n,
            '%s < %s' % (GI('i'), p21): glt1, '%s < %s' % (RS('i'), p21): r1lt},
           [('6', Q6, B.g(Q6, ewg_(w, ph, QS('i'), qn, "X'", B.x2w))), ('7', E7b, B.g(E7b, ewg_(w, ph, RM, rmn, DK(7), B.gam[DK(7)])))])
    # 3. dropNum 7

    # 7 is updated last in the chain after normalizing with 7 last
    cur, outa = R.normalize(['1', '2', '3', '5', '0', '4', '6', '7'])
    assert outa[-1][0] == '7', outa
    Son = R.at(outa[:-1])
    rmlt = linarith(w, ph, [rlt, cl.ge0(Rc)], '%s < %s' % (RM, p2), closure=cl)
    B.call(R, 'tmidropb', {'K': '7', 'F': RM, 'N': 'B', 'X': DK(7), 'P': Pb(2), 'E': LB['Y4']},
           {'%s e. NN0' % RM: rmn, '%s < %s' % (RM, p2): rmlt}, [('7', DK(7), B.gam[DK(7)])], on=(Son, outa[:-1]))
    # 4. incr 4 1
    G1 = '( %s + 1 )' % GI('i')
    g1n = s([s([nums['gtn'], w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (ph, G1))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, G1))
    EG1 = EWg(G1, 'X')
    B.call(R, 'tmiincbs', {'K': '4', 'J': '1', 'F': GI('i'), 'N': B1, 'X': 'X', 'P': Pb(3), 'E': LB['Y5']},
           {'%s e. NN0' % GI('i'): s([nums['gtn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, GI('i'))), '%s e. NN0' % B1: b1n,
            '%s < %s' % (GI('i'), p21): glt1}, [('4', EG1, B.g(EG1, ewg_(w, ph, G1, g1n, 'X', B.xw)))])
    # 5. predNum 0 1
    hmnn = s([s([nums['hmn'], hne0], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (ph, HM('i'), HM('i'))),
              s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (HM('i'), HM('i'), HM('i')))], 'sylibr',
             '( %s -> %s e. NN )' % (ph, HM('i')))
    hlt = linarith(w, ph, [c['H < ( 2 ^ B )'], cl.ge0('i')], '%s < %s' % (HM('i'), p2), closure=cl)
    H1 = '( %s - 1 )' % HM('i')
    h1n = s([hmnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, H1))
    EH1 = EWg(H1, 'Y')
    B.call(R, 'tmiprdbs', {'K': '0', 'J': '1', 'F': HM('i'), 'N': 'B', 'X': 'Y', 'P': Pb(4), 'E': LB['Y6']},
           {'%s e. NN' % HM('i'): hmnn, '%s < %s' % (HM('i'), p2): hlt}, [('0', EH1, B.g(EH1, ewg_(w, ph, H1, h1n, 'Y', B.yw)))])
    # 6. isZero 0 1
    h1lt = linarith(w, ph, [c['H < ( 2 ^ B )'], cl.ge0('i')], '%s < %s' % (H1, p2), closure=cl)
    B.call(R, 'tmiizbs', {'K': '0', 'I': '1', 'F': H1, 'N': 'B', 'X': 'Y', 'P': Pb(5), 'E': LMS['Z1']},
           {'%s e. NN0' % H1: h1n, '%s < %s' % (H1, p2): h1lt}, [])
    cur, out2 = R.normalize(ORD046)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the bound: n <_ U ` i
    TB = '( TMB ` B )'
    cl.leaf(TB, 'NN0', B.tbn)
    tbm = s([B.bn, b1n, linarith(w, ph, [], 'B <_ %s' % B1, closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, TB1))
    TB3 = '( TMB ` ( ( 3 x. %s ) + 4 ) )' % B1
    k34 = s([b1n, w.inst('tplb34')], 'syl', '( %s -> %s = ( ; 2 7 x. %s ) )' % (ph, TB3, TB1))
    cl.leaf(TB3, 'NN0', s([k34, cl.mem('( ; 2 7 x. %s )' % TB1, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, TB3)))
    ka1n = s([kn, cl.mem(AS(i1), 'NN0'), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, KA1))
    ka0n = s([kn, nums['an'], w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, KA0))
    Q = '( ( %s + %s ) + 1 )' % (AS('i'), CS('i'))
    kd = s([ka1, s([k410], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( ; 6 4 x. %s ) x. %s ) )' % (ph, KB, Q, TB1, Q))], 'eqtrd',
           '( %s -> %s = ( ( ; 6 4 x. %s ) x. %s ) )' % (ph, KA1, TB1, Q))
    k0 = s([k410], 'oveq1d', '( %s -> %s = ( ( ; 6 4 x. %s ) x. %s ) )' % (ph, KA0, TB1, AS('i')))
    k3 = s([k34], 'oveq2d', '( %s -> ( ( %s + 1 ) x. %s ) = ( ( %s + 1 ) x. ( ; 2 7 x. %s ) ) )' % (ph, CS('i'), TB3, CS('i'), TB1))
    # polynomial identities (products of atoms)
    CT, AT = '( %s x. %s )' % (CS('i'), TB1), '( %s x. %s )' % (AS('i'), TB1)
    i1_ = lineq(w, ph, '( ( ; 6 4 x. %s ) x. %s )' % (TB1, Q), '( ( ( ; 6 4 x. %s ) + ( ; 6 4 x. %s ) ) + ( ; 6 4 x. %s ) )' % (AT, CT, TB1),
                closure=cl, products=True)
    i0_ = lineq(w, ph, '( ( ; 6 4 x. %s ) x. %s )' % (TB1, AS('i')), '( ; 6 4 x. %s )' % AT, closure=cl, products=True)
    i3_ = lineq(w, ph, '( ( %s + 1 ) x. ( ; 2 7 x. %s ) )' % (CS('i'), TB1), '( ( ; 2 7 x. %s ) + ( ; 2 7 x. %s ) )' % (CT, TB1),
                closure=cl, products=True)
    ctn = s([cn, t1n, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, CT))
    cl.leaf(CT, 'NN0', ctn)
    cl.leaf(AT, 'NN0', s([nums['an'], t1n, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, AT)))
    cl.leaf(KA1, 'NN0', ka1n)
    cl.leaf(KA0, 'NN0', ka0n)
    PX = '( ( %s + 1 ) x. %s )' % (CS('i'), TB3)
    cl.leaf(PX, 'NN0', s([s([cn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, CS('i'))),
                          s([k34, cl.mem('( ; 2 7 x. %s )' % TB1, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, TB3)), w.inst('nn0mulcl')],
                         'syl2anc', '( %s -> %s e. NN0 )' % (ph, PX)))
    e1 = s([kd, i1_], 'eqtrd', '( %s -> %s = ( ( ( ; 6 4 x. %s ) + ( ; 6 4 x. %s ) ) + ( ; 6 4 x. %s ) ) )' % (ph, KA1, AT, CT, TB1))
    e0 = s([k0, i0_], 'eqtrd', '( %s -> %s = ( ; 6 4 x. %s ) )' % (ph, KA0, AT))
    e3 = s([k3, i3_], 'eqtrd', '( %s -> %s = ( ( ; 2 7 x. %s ) + ( ; 2 7 x. %s ) ) )' % (ph, PX, CT, TB1))
    le = linarith(w, ph, [e1, e0, e3, tbm, t1p, cl.ge0(CT)], '%s <_ %s' % (n, UV), closure=cl, atoms=[TB, TB1, PX, CT, AT, KA1, KA0])
    uvn = linarith(w, ph, [e1, e0, t1p, cl.ge0(CT)], '0 <_ %s' % UV, closure=cl, atoms=[TB1, CT, AT, KA1, KA0])
    uvz = s([s([s([s([kn, cl.mem(AS(i1), 'NN0'), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, KA1)), w.inst('nn0zd')], 'syl',
                  '( %s -> %s e. ZZ )' % (ph, KA1)) if False else cl.mem(UV, 'ZZ'), uvn], 'jca', '( %s -> ( %s e. ZZ /\\ 0 <_ %s ) )' % (ph, UV, UV)),
            s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (UV, UV, UV))], 'sylibr', '( %s -> %s e. NN0 )' % (ph, UV))
    # U ` i
    uval = mval(w, ph, 'j', 'NN0', UB, 'i', inn, ex_(w, ph, UV, 'ovex'))
    UI = '( %s ` i )' % UF
    ue = s([uval], 'eqcomd', '( %s -> %s = %s )' % (ph, UV, UI))
    uin = s([uval, uvz], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, UI))
    t = hrle(w, ph, mk['phm'], t, C, D, n, UV, uvz, le)
    n = UV
    C2 = CLN(LMS['Y2'], NI, PB('i'))
    t = hrssc(w, ph, mk['phm'], t, C, D, n, C2, clnss(w, ph, LMS['Y2'], NI, S, PB('i'), B.famss('i', inn)))
    # post
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, i1))
    i1le = s([ilt, s([s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ph), s([B.hn], 'nn0zd', '( %s -> H e. ZZ )' % ph), w.inst('zltp1le')],
                     'syl2anc', '( %s -> ( i < H <-> ( i + 1 ) <_ H ) )' % ph)], 'mpbid', '( %s -> ( i + 1 ) <_ H )' % ph)
    nums1 = B.at(i1, i1n, i1le)
    pv1, S1 = B.pv(i1, i1n, nums1)
    P1T = '( %s ` ( i + 1 ) )' % PV
    ga = s([cl.mem('G', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph), w.inst('addass')],
           'syl3anc', '( %s -> %s = %s )' % (ph, G1, GI(i1)))
    fe = s([cl.mem('H', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph), w.inst('subsub4')],
           'syl3anc', '( %s -> %s = %s )' % (ph, H1, HM(i1)))
    qe = s([rq], 'eqcomd', '( %s -> %s = %s )' % (ph, QS('i'), RS(i1)))
    RULES = {QS('i'): (RS(i1), qe), H1: (HM(i1), fe), G1: (GI(i1), ga)}
    Dst = triple_D(D)
    xn = chain_text('D', out2)
    assert Dst == xn, (Dst, xn)
    r2_, x2 = w.rewrite(xn, RULES, ph)
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
    lab_ = LMS['Z1']
    ceq = s([clnneq(w, ph, lab_, cq, NFL(FIN), N1, Dst), clneq(w, ph, lab_, N1, deq, Dst, P1T)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN(lab_, N1, P1T)))
    cpre = clneq(w, ph, LMS['Y2'], NI, s([pvi], 'eqcomd', '( %s -> %s = %s )' % (ph, PB('i'), PT)), PB('i'), PT)
    t, C, D, n = hrrw(w, ph, t, C2, D, n, ceq=cpre, deq=ceq, neq=ue)
    st = s([s([part1, uin], 'jca', '( %s -> ( A. m e. %s ( %s ` m ) = 1o /\\ %s e. NN0 ) )' % (ph, NI, CNFL, UI)), t], 'jca',
           '( %s -> %s )' % (ph, LBODY))
    finish(w, st, lab)
    return w.run()


def tmisgft():
    lab = 'tmisgft'
    w = W(lab, 'The frame of Lean\'s ` smoothGoF ` loop at the machine: for ` i <_ fuel ` the class family is a set of states and '
               'the stack family a stack assignment, and at ` fuel ` iterations the flag is set (the test ` !flag ` fails).')
    s = w.s
    TT = numtree((PSI_T, 'i e. ( 0 ... H )'))
    pt = cj(TT)
    B = Ls(w, pt, TT)
    ii = B.c['i e. ( 0 ... H )']
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ H )' % pt)
    nums = B.at('i', inn, ile)
    pv, St = B.pv('i', inn, nums)
    body = LTYP[len('A. i e. ( 0 ... H ) '):]
    one = s([B.famss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))
    T0 = (PSI_T, 'i e. ( 0 ... H )')
    k = s([], 't10stk', ST_NUMS)
    one0 = s([k, one], 'mpan2', '( %s -> %s )' % (cj(T0), body))
    typ = s([one0], 'ralrimiva', '( %s -> %s )' % (PSI, LTYP))
    TE = numtree(PSI_T)
    pe = cj(TE)
    L = Ls(w, pe, TE)
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


def tmisgfl():
    lab = 'tmisgfl'
    w = W(lab, 'Lean\'s ` smoothGoF ` loop at the machine: ~ tm2floop at the families ( ` P\' ` a letter), ` fuel ` iterations of '
               '` smoothGoBody ` (~ tmisgfi ), the frame by ~ tmisgft .')
    s = w.s
    T = numtree(PSI_T)
    ph = cj(T)
    B = Ls(w, ph, T)
    B.deep('sgf', 1)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmisgft', STMTS10['tmisgft']))
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    per = s([s([], 'tmisgfi', STMTS10['tmisgfi'])], 'ralrimiva', '( %s -> %s )' % (PSI, LPER))
    ex[LPER] = lift_from(w, PSI, ph, per)
    st = Bld(w, ph, B.c, ex)(LTREE)
    st2 = s([st, w.inst('tm2floop')], 'syl', '( %s -> %s )' % (ph, LCONCL))
    finish(w, st2, lab)
    return w.run()


def tmisgfb():
    lab = 'tmisgfb'
    T = numtree(TREE_SGF)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` smoothGoF_le_B ` at the machine ( ` xd xr xf xF s t u = 4 6 7 0 1 2 3 ` ): ` isZero xF s ` , then the '
               'loop (~ tmisgfl ) at the families of ~ sgsh ; the charges telescope (~ telfsumo2 ) to '
               '` ( smoothGo d r fuel ).2 B ( 4 b + 10 ) ` .')
    s = w.s
    B = Ls(w, ph, T)
    c, mk = B.c, B.mk
    TB = '( TMB ` B )'
    # 1. isZero 0 1
    R = B.run()
    B.call(R, 'tmiizbs', {'K': '0', 'I': '1', 'F': 'H', 'N': 'B', 'X': 'Y', 'P': PL('P', 1), 'E': LMS['Z1']}, {}, [])
    # 2. to the family at 0
    z0 = closed(w, ph, '0nn0', '0 e. NN0')
    h0 = s([s([B.hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('subid1')], 'syl', '( %s -> ( H - 0 ) = H )' % ph)
    g0 = s([s([B.gnn], 'nncnd', '( %s -> G e. CC )' % ph), w.inst('addrid')], 'syl', '( %s -> ( G + 0 ) = G )' % ph)
    s0 = s([B.gnn, B.fn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. F , 0 >. )' % (ph, SGX('G', 'F', '0')))
    fe = s([B.fn], 'elexd', '( %s -> F e. _V )' % ph)
    ze = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ph)
    r0 = fst_of(w, ph, SGX('G', 'F', '0'), 'F', '0', s0, fe, ze)
    a0 = snd_of(w, ph, SGX('G', 'F', '0'), 'F', '0', s0, fe, ze)
    R0 = {HM('0'): ('H', h0), GI('0'): ('G', g0), RS('0'): ('F', r0)}
    rcl, xcl = w.rewrite(FLC('0'), R0, ph)
    assert xcl == 'if ( H = 0 , 1o , (/) )', xcl
    N0 = '( %s ` 0 )' % NFM
    ceq0 = s([s([famval(w, ph, COND, '0', z0), nfl_eq(w, ph, FLC('0'), xcl, rcl)], 'eqtrd', '( %s -> %s = %s )' % (ph, N0, NFL(xcl)))], 'eqcomd',
             '( %s -> %s = %s )' % (ph, NFL(xcl), N0))
    zle = s([B.hn], 'nn0ge0d', '( %s -> 0 <_ H )' % ph)
    nums0 = B.at('0', z0, zle)
    Sp0 = B.pbst('0', nums0)
    pfv = mval(w, ph, 'j', 'NN0', PB, '0', z0, s([Sp0.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB('0'))))
    rs, xs = w.rewrite(PB('0'), R0, ph)
    kd = lambda k_: mk['k'][k_]['kd']
    u0 = upidv(w, ph, 'D', '0', EWg('H', 'Y'), B.S0.vals['0'][1], mk['tv'], B.dd, kd('0'))
    rr0, x0 = w.rewrite(xs, {UP('D', '0', EWg('H', 'Y')): ('D', u0)}, ph)
    u4 = upidv(w, ph, 'D', '4', EWg('G', 'X'), B.S0.vals['4'][1], mk['tv'], B.dd, kd('4'))
    rr4, x4 = w.rewrite(x0, {UP('D', '4', EWg('G', 'X')): ('D', u4)}, ph)
    u6 = upidv(w, ph, 'D', '6', EWg('F', "X'"), B.S0.vals['6'][1], mk['tv'], B.dd, kd('6'))
    assert x4 == UP('D', '6', EWg('F', "X'")), x4
    pf0 = '( %s ` 0 )' % PF
    chain = s([pfv, rs], 'eqtrd', '( %s -> %s = %s )' % (ph, pf0, xs))
    for r_, x_ in ((rr0, x0), (rr4, x4)):
        chain = s([chain, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, pf0, x_))
    se = s([s([chain, u6], 'eqtrd', '( %s -> %s = D )' % (ph, pf0))], 'eqcomd', '( %s -> D = %s )' % (ph, pf0))
    lab0 = LMS['Z1']
    ceq = s([clnneq(w, ph, lab0, ceq0, NFL(xcl), N0, 'D'), clneq(w, ph, lab0, N0, se, 'D', pf0)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, R.cur, CLN(lab0, N0, pf0)))
    t1, C1, D1, n1 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=ceq)
    # 3. the loop
    ex = {'%s = %s' % (PF, PF): s([s([], 'eqid', '%s = %s' % (PF, PF))], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}
    tl, cl_ = inst(w, ph, 'tmisgfl', {PV: PF}, Bld(w, ph, c, ex))
    C2, D2, n2 = triple_parts(cl_)
    assert C2 == D1, (C2, D1)
    t = hrseq(w, ph, mk['phm'], t1, tl, C1, D1, D2, n1, n2)
    n = '( %s + %s )' % (n1, n2)
    # 4. the post: ( PF ` H ) = PB( H ) with ( H - H ) = 0 , class to ( 2nd ` T )
    numsH = B.at('H', B.hn, s([s([B.hn], 'nn0red', '( %s -> H e. RR )' % ph)], 'leidd', '( %s -> H <_ H )' % ph))
    SpH = B.pbst('H', numsH)
    pfh = mval(w, ph, 'j', 'NN0', PB, 'H', B.hn, s([SpH.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB('H'))))
    hh = s([s([B.hn], 'nn0cnd', '( %s -> H e. CC )' % ph)], 'subidd', '( %s -> ( H - H ) = 0 )' % ph)
    rh, xh = w.rewrite(PB('H'), {HM('H'): ('0', hh)}, ph)
    DF_ = UPS('D', ('0', EWg('0', 'Y')), ('4', EWg('( G + H )', 'X')), ('6', EWg('( 1st ` %s )' % SG_, "X'")))
    assert xh == DF_, (xh, DF_)
    PFH = '( %s ` H )' % PF
    NH = '( %s ` H )' % NFM
    dq = s([pfh, rh], 'eqtrd', '( %s -> %s = %s )' % (ph, PFH, DF_))
    t, C, D, n = hrrw(w, ph, t, C1, D2, n, deq=clneq(w, ph, 'E', NH, dq, PFH, DF_))
    D3 = CLN('E', S, DF_)
    ssd = clnss(w, ph, 'E', NH, S, DF_, B.famss('H', B.hn))
    dmem = SpH  # unused
    from t5lib import cfgcl
    Sdf = B.S0.upd('0', EWg('0', 'Y'), ewg_(w, ph, '0', closed(w, ph, '0nn0', '0 e. NN0'), 'Y', B.yw))
    Sdf = Sdf.upd('4', EWg('( G + H )', 'X'), ewg_(w, ph, '( G + H )', s([s([B.gnn, B.hn, w.inst('nnnn0addcl')], 'syl2anc',
                                                                                 '( %s -> ( G + H ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( G + H ) e. NN0 )' % ph),
                                                     'X', B.xw))
    Sdf = Sdf.upd('6', EWg('( 1st ` %s )' % SG_, "X'"), ewg_(w, ph, '( 1st ` %s )' % SG_, numsH['rn'], "X'", B.x2w))
    assert Sdf.D == DF_, Sdf.D
    cfg = cfgcl(w, ph, 'E', S, DF_, mk['tv'], B.ex[LAB('E')], B.ss(S) if False else closed(w, ph, 'ssid', '%s C_ %s' % (S, S)), Sdf.memb)
    t = hrssd(w, ph, mk['phm'], t, C, D, n, D3, ssd, cfg)
    D = D3
    # 5. the bound
    SMT = 'sum_ i e. ( 0 ..^ H ) ( ( %s ` i ) + 1 )' % UF
    KA = lambda k_: '( %s x. %s )' % (KB, AS(k_))
    pi = '( %s /\\ i e. ( 0 ..^ H ) )' % ph
    iin = s([s([], 'simpr', '( %s -> i e. ( 0 ..^ H ) )' % pi), w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    uv = mval(w, pi, 'j', 'NN0', UB, 'i', iin, ex_(w, pi, UB('i'), 'ovex'))
    DIF = '( %s - %s )' % (KA('( i + 1 )'), KA('i'))
    difc = s([s([], 'ovex', '') if False else ex_(w, pi, DIF, 'ovex')], 'id', '') if False else None
    kbn = s([s([s([s([closed(w, pi, '4nn0', '4 e. NN0'), lift_from(w, ph, pi, B.bn), w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % pi),
                   closed(w, pi, '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % pi),
                 w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pi, KB))], 'nncnd', '( %s -> %s e. CC )' % (pi, KB))

    def asc(tt, ttn):
        xc = sgcl(w, pi, 'G', 'F', tt, lift_from(w, ph, pi, B.gnn), lift_from(w, ph, pi, B.fn), ttn)
        return s([comp(w, pi, SGX('G', 'F', tt), xc, 2)], 'nn0cnd', '( %s -> %s e. CC )' % (pi, AS(tt)))
    i1n = s([iin, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    dcc = s([s([kbn, asc('( i + 1 )', i1n)], 'mulcld', '( %s -> %s e. CC )' % (pi, KA('( i + 1 )'))),
             s([kbn, asc('i', iin)], 'mulcld', '( %s -> %s e. CC )' % (pi, KA('i')))], 'subcld', '( %s -> %s e. CC )' % (pi, DIF))
    npc = s([dcc, s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % pi), w.inst('npcan')], 'syl2anc',
            '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (pi, DIF, DIF))
    term = s([s([uv], 'oveq1d', '( %s -> ( ( %s ` i ) + 1 ) = ( %s + 1 ) )' % (pi, UF, UB('i'))), npc], 'eqtrd',
             '( %s -> ( ( %s ` i ) + 1 ) = %s )' % (pi, UF, DIF))
    se_ = s([term], 'sumeq2dv', '( %s -> %s = sum_ i e. ( 0 ..^ H ) %s )' % (ph, SMT, DIF))
    # telescoping
    def kcong(a_):
        e = s([], 'id', '( %s = %s -> %s = %s )' % ('k', a_, 'k', a_))
        cg, new = w.congr(KA('k'), {'k': a_}, 'k = %s' % a_, {'k': e})
        assert new == KA(a_), new
        return cg
    t1_, t2_, t3_, t4_ = kcong('i'), kcong('( i + 1 )'), kcong('0'), kcong('H')
    huz = s([B.hn, s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi' if False else 'eleqtrd', '') if False else \
        s([B.hn, s([s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % ph)], 'eleqtrd', '( %s -> H e. ( ZZ>= ` 0 ) )' % ph)
    pk = '( %s /\\ k e. ( 0 ... H ) )' % ph
    kn_ = s([s([], 'simpr', '( %s -> k e. ( 0 ... H ) )' % pk), w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    kxc = sgcl(w, pk, 'G', 'F', 'k', lift_from(w, ph, pk, B.gnn), lift_from(w, ph, pk, B.fn), kn_)
    kbk = s([s([s([s([closed(w, pk, '4nn0', '4 e. NN0'), lift_from(w, ph, pk, B.bn), w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % pk),
                   closed(w, pk, '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % pk),
                 w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pk, KB))], 'nncnd', '( %s -> %s e. CC )' % (pk, KB))
    kac = s([kbk, s([comp(w, pk, SGX('G', 'F', 'k'), kxc, 2)], 'nn0cnd', '( %s -> %s e. CC )' % (pk, AS('k')))], 'mulcld',
            '( %s -> %s e. CC )' % (pk, KA('k')))
    tel = s([t1_, t2_, t3_, t4_, huz, kac], 'telfsumo2', '( %s -> sum_ i e. ( 0 ..^ H ) %s = ( %s - %s ) )' % (ph, DIF, KA('H'), KA('0')))
    ka0 = s([a0], 'oveq2d', '( %s -> %s = ( %s x. 0 ) )' % (ph, KA('0'), KB))
    BND = '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (SG_, KB)
    cl = Closure(w, ph, {'B': ('NN0', B.bn)})
    kbn0 = s([s([s([s([closed(w, ph, '4nn0', '4 e. NN0'), B.bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % ph),
                    closed(w, ph, '10nn0', '; 1 0 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> ( ( 4 x. B ) + ; 1 0 ) e. NN0 )' % ph),
                  w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, KB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, KB))
    cl.leaf(KB, 'NN0', kbn0)
    cl.leaf(TB, 'NN0', B.tbn)
    xH = sgcl(w, ph, 'G', 'F', 'H', B.gnn, B.fn, B.hn)
    cl.leaf(AS('H'), 'NN0', comp(w, ph, SGX('G', 'F', 'H'), xH, 2))
    kh = lineq(w, ph, BND, '( %s + %s )' % (KA('H'), KB), closure=cl, products=True)
    kah = s([kbn0, comp(w, ph, SGX('G', 'F', 'H'), xH, 2), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, KA('H')))
    cl.leaf(KA('H'), 'NN0', kah)
    cl.leaf(KA('0'), 'NN0', s([ka0, s([kbn0, closed(w, ph, '0nn0', '0 e. NN0'), w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( %s x. 0 ) e. NN0 )' % (ph, KB))],
                              'eqeltrd', '( %s -> %s e. NN0 )' % (ph, KA('0'))))
    stl = s([se_, tel], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (ph, SMT, KA('H'), KA('0')))
    cl.leaf(SMT, 'RR', s([stl, s([cl.mem(KA('H'), 'RR'), cl.mem(KA('0'), 'RR')], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (ph, KA('H'), KA('0')))],
                         'eqeltrd', '( %s -> %s e. RR )' % (ph, SMT)))
    k00 = s([s([kbn0], 'nn0cnd', '( %s -> %s e. CC )' % (ph, KB)), w.inst('mul01')], 'syl', '( %s -> ( %s x. 0 ) = 0 )' % (ph, KB))
    B1 = '( B + 1 )'
    b1n = s([B.bn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, B1))
    TB1 = '( TMB ` %s )' % B1
    k410 = s([B.bn, w.inst('tplb410')], 'syl', '( %s -> %s = ( ; 6 4 x. %s ) )' % (ph, KB, TB1))
    t1n = s([s([b1n, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB1))
    cl.leaf(TB1, 'NN0', t1n)
    tbm = s([B.bn, b1n, linarith(w, ph, [], 'B <_ %s' % B1, closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB, TB1))
    t1p = pos_tmb(w, ph, b1n, B1)
    ka00 = s([ka0, k00], 'eqtrd', '( %s -> %s = 0 )' % (ph, KA('0')))
    le = linarith(w, ph, [stl, ka00, kh, k410, tbm, t1p], '%s <_ %s' % (n, BND), closure=cl,
                  atoms=[TB, TB1, KB, SMT, KA('H'), KA('0'), BND])
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0') if False else
              s([s([s([comp(w, ph, SGX('G', 'F', 'H'), xH, 2), w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` %s ) + 1 ) e. NN0 )' % (ph, SG_)), kbn0,
                    w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, BND))], 'id', '') if False else
              s([s([comp(w, ph, SGX('G', 'F', 'H'), xH, 2), w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` %s ) + 1 ) e. NN0 )' % (ph, SG_)), kbn0,
                 w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, BND)), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
