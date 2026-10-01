"""T10: Lean's ` dropN x c s ` at ` 4 5 6 ` (TM/Lists.lean ` dropN_runs ` , ` dropN_le_B ` ) on TMIdn: the loop
` loop ( !flag ) ( dropNBody ) ` at the families ` W substr <. i , # W >. ` on 4, ` N - i ` on 5.

  tmidni   one iteration: below ` N ` the flag is clear, and ` dropNBody ` ( ` dropNum 4 ; predNum 5 6 ; isZero 5 6 ;
           peekBraOr 4 ` ) takes the family at ` i ` to the family at ` i + 1 `
  tmidnt   the frame: the families' typings, and the flag set at ` N `
  tmidnl   ~ tm2floopu at the families ( ` P' ` a letter)
  tmidnb   dropN_le_B (with ` N <_ # W ` ): ` isZero 5 6 ; peekBraOr 4 ` , the loop, ` dropNum 5 `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_t_dn.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import famval, fam_unpack, ifex_closed, mval
from cl import Closure
from t10_e_doa import lift_from
from t10_s_rbo import rbo_ty, rbo_iface
import t8alib as A8

SEL = sys.argv[1:]
LMN = FRAGS['dn'].lmap()
NW = '( # ` W )'
DRP = lambda t: '( W substr <. %s , %s >. )' % (t, NW)
REST = lambda t: ENCL(DRP(t), 'X')
NM = lambda t: '( N - %s )' % t
PB = lambda t: UPS('D', ('5', EWg(NM(t), 'Y')), ('4', REST(t)))
ORD54 = ['0', '1', '2', '3', '5', '4', '6', '7']
FLC = lambda t: 'if ( %s = N , 1o , (/) )' % t
COND = lambda h, t: '( TMfl ` %s ) = %s' % (h, FLC(t))
NCL = lambda t: '{ h e. TMSt | %s }' % COND('h', t)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
PF = '( j e. NN0 |-> %s )' % PB('j')
PV = "P'"
TPR = '( ( 3 x. ( TMB ` B ) ) + 1 )'
PSI_T = (TREE_DN, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
GM = {'A': LMN['Z2'], 'B0': LMN['Y2'], 'E': LMN['Y3'], 'C0': CNFL, 'R': 'N', "T'": TPR, 'N': NFM, 'P': PV}
_LA, _LC = split_imp(stmt('tm2floopu'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
_pre = 'A. i e. ( 0 ..^ N ) '
assert LPER.startswith(_pre)
LBODY = LPER[len(_pre):]
T_I = (PSI_T, 'i e. ( 0 ..^ N )')
add_stmt('tmidni', T_I, LBODY)
add_stmt('tmidnt', PSI_T, '( %s /\\ %s )' % (LTYP, LEXIT))
add_stmt('tmidnl', PSI_T, LCONCL)
PBL = lambda k: PL(PL('P', 3), k)          # dropNBody's labels inside dropN


def cnfl_at(w, pm, mm, fl, val_is_1):
    """( pm -> ( CNFL ` m ) = 1o ) from ( TMfl ` m ) = (/) (val_is_1 False), ( pm -> -. ( CNFL ` m ) = 1o ) from
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


def drp_empty(w, ph, ww, nwn, t, tz):
    """( ph -> ( DRP( t ) = (/) <-> t = # W ) ) from tz : ( ph -> t e. ( 0 ... # W ) )"""
    s = w.s
    V1 = DRP(t)
    sl = s([ww, tz, s([nwn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NW, NW)), w.inst('swrdlen')], 'syl3anc',
           '( %s -> ( # ` %s ) = ( %s - %s ) )' % (ph, V1, NW, t))
    h0 = s([s([s([], 'ovex', '%s e. _V' % V1)], 'a1i', '( %s -> %s e. _V )' % (ph, V1)), w.inst('hasheq0')], 'syl',
           '( %s -> ( ( # ` %s ) = 0 <-> %s = (/) ) )' % (ph, V1, V1))
    tn = s([tz, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, t))
    s0 = s([s([sl], 'eqeq1d', '( %s -> ( ( # ` %s ) = 0 <-> ( %s - %s ) = 0 ) )' % (ph, V1, NW, t)),
            s([s([nwn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, NW)), s([tn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, t))], 'subeq0ad',
              '( %s -> ( ( %s - %s ) = 0 <-> %s = %s ) )' % (ph, NW, t, NW, t))], 'bitrd',
           '( %s -> ( ( # ` %s ) = 0 <-> %s = %s ) )' % (ph, V1, NW, t))
    return s([s([h0, s0], 'bitr3d', '( %s -> ( %s = (/) <-> %s = %s ) )' % (ph, V1, NW, t)),
              s([s([], 'eqcom', '( %s = %s <-> %s = %s )' % (NW, t, t, NW))], 'a1i', '( %s -> ( %s = %s <-> %s = %s ) )' % (ph, NW, t, t, NW))],
             'bitrd', '( %s -> ( %s = (/) <-> %s = %s ) )' % (ph, V1, t, NW))


class Ld(Base):
    """the facts under an antecedent containing the dn tree"""
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        ww, nn, bn = c0['W e. Word NN0'], c0['N e. NN0'], c0['B e. NN0']
        xw, yw = c0[WG('X')], c0[WG('Y')]
        eqs = {'4': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), '5': (EWg('N', 'Y'), ewg_(w, ph, 'N', nn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, 'dn', eqs)
        s = w.s
        self.ww, self.nn, self.bn, self.xw, self.yw = ww, nn, bn, xw, yw
        self.nwn = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
        self.tbn = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
        self.pvs = {}

    def tz(self, t, tn, tle):
        """( ph -> t e. ( 0 ... # W ) ) from t <_ N"""
        w, ph, s = self.w, self.ph, self.w.s
        cl = Closure(w, ph, {'N': ('NN0', self.nn)})
        cl.leaf(NW, 'NN0', self.nwn)
        cl.leaf(t, 'NN0', tn)
        le = linarith(w, ph, [tle, self.c['N <_ %s' % NW]], '%s <_ %s' % (t, NW), closure=cl)
        return s([s([tn, self.nwn, le], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, t, NW, t, NW)),
                  w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, t, NW))

    def nmn(self, t, tn, tle):
        return self.w.s([tn, self.nn, tle, self.w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (self.ph, NM(t)))

    def pbst(self, t, tn, tle):
        w, ph, s = self.w, self.ph, self.w.s
        dw = s([self.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DRP(t)))
        g4 = self.g(REST(t), enclg(w, ph, DRP(t), dw, 'X', self.xw))
        g5 = self.g(EWg(NM(t), 'Y'), ewg_(w, ph, NM(t), self.nmn(t, tn, tle), 'Y', self.yw))
        self.last = [('5', EWg(NM(t), 'Y')), ('4', REST(t))]
        return self.S0.upd('5', EWg(NM(t), 'Y'), g5).upd('4', REST(t), g4)

    def pv(self, t, tn, tle):
        if t not in self.pvs:
            fam = self.c['%s = %s' % (PV, PF)]
            self.pvs[t] = fam_at(self.w, self.ph, self.mk, self.ne, fam, PV, 'j', 'NN0', PB, t, tn, self.pbst(t, tn, tle))
        return self.pvs[t]

    def famss(self, t, tn):
        w, ph = self.w, self.ph
        fv = famval(w, ph, COND, t, tn)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NCL(t))], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NCL(t)))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NCL(t)))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ ( 2nd ` T ) )' % (ph, NFM, t))


def peek_step(w, ph, B, R, V, vw, CND, bi_rest, A, E):
    """peekBraOr 4 at the current stacks, stack 4 = ( ( encList ` V ) ++ X ) , pre class the current NFL( V0 ) :
    bi_rest ( HD -> ( ( V0 = 1o \\/ V = (/) ) <-> CND ) ) given as a function of the step ( ph -> ( HD = 2 <-> V = (/) ) )"""
    s = w.s
    W_ = ENCL(V, 'X')
    vn0 = encl_ne0(w, ph, V, vw, 'X', B.xw)
    wg = B.gam[W_]
    eq, hg, tg = A8.word_split(w, ph, W_, wg, vn0)
    HD, TL = A8.HD0(W_), A8.TL1(W_)
    kv = s([R.S.vals['4'][1], eq], 'eqtrd', '( %s -> ( %s ` 4 ) = ( <" %s "> ++ %s ) )' % (ph, R.S.D, HD, TL))
    hb = s([vw, B.xw, w.inst('tmexhdb')], 'syl2anc', '( %s -> ( %s = 2 <-> %s = (/) ) )' % (ph, HD, V))
    Npre = R.cur.split(' } X. ( ', 1)[1].rsplit(' X. { ', 1)[0]
    assert Npre.startswith('{ h e. TMSt | ( TMfl ` h ) = '), Npre
    V0 = Npre[len('{ h e. TMSt | ( TMfl ` h ) = '):-2]
    bi = bi_rest(HD, hb, V0)
    pk = rbo_iface(w, ph, B.mk, V0, HD, hg, bi, CND)
    N1 = A8.NFL('if ( %s , 1o , (/) )' % CND)
    ex = {'( %s ` 4 ) = ( <" %s "> ++ %s )' % (R.S.D, HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
          'A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (Npre, RBO, HD, N1): pk,
          '%s e. %s' % (RBO, A8.HDLS): rbo_ty(w, ph, B.mk), '%s C_ %s' % (Npre, S): B.ss(Npre), '%s C_ %s' % (N1, S): B.ss(N1)}
    B.call(R, 'tm2lpk', {'A': A, 'E': E, 'K': '4', 'F': RBO, 'Z': HD, 'X': TL, 'N': Npre, "N'": N1}, ex, [])
    return N1


def tmidni():
    lab = 'tmidni'
    T = numtree(T_I)
    ph = cj(T)
    w = W(lab, 'One iteration of Lean\'s ` dropN ` loop at the machine ( ` DropInv ` , ` dropNBody_runs ` ): below ` N ` the '
               'flag is clear, and ` dropNBody ` ( ` dropNum 4 ; predNum 5 6 ; isZero 5 6 ; peekBraOr 4 ` ) takes the family '
               'at ` i ` ( ` W substr <. i , # W >. ` on 4, ` N - i ` on 5) to the family at ` i + 1 ` within ` 3 B b + 1 ` steps.')
    s = w.s
    B = Ld(w, ph, T)
    c, mk = B.c, B.mk
    B.deep('dn', 1)
    io = c['i e. ( 0 ..^ N )']
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < N )' % ph)
    cl = Closure(w, ph, {'i': ('NN0', inn), 'N': ('NN0', B.nn), 'B': ('NN0', B.bn)})
    cl.leaf(NW, 'NN0', B.nwn)
    ile = linarith(w, ph, [ilt], 'i <_ N', closure=cl)
    # the flag at i
    ine = s([s([cl.mem('i', 'RR'), ilt], 'ltned', '( %s -> i =/= N )' % ph)], 'neneqd', '( %s -> -. i = N )' % ph)
    f0 = s([ine], 'iffalsed', '( %s -> %s = (/) )' % (ph, FLC('i')))
    NI = '( %s ` i )' % NFM
    pm = '( %s /\\ m e. %s )' % (ph, NI)
    mm, mc = fam_unpack(w, pm, COND, 'i', lift_from(w, ph, pm, inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    fl0 = s([mc, lift_from(w, ph, pm, f0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    part1 = s([cnfl_at(w, pm, mm, fl0, False)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ph, NI, CNFL))
    # the family at i, stack 4 split at its head entry
    pvi, SI = B.pv('i', inn, ile)
    PT = '( %s ` i )' % PV
    iz = B.tz('i', inn, ile)
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ph)
    i1le = s([ilt, s([s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ph), s([B.nn], 'nn0zd', '( %s -> N e. ZZ )' % ph), w.inst('zltp1le')],
                     'syl2anc', '( %s -> ( i < N <-> ( i + 1 ) <_ N ) )' % ph)], 'mpbid', '( %s -> ( i + 1 ) <_ N )' % ph)
    ilw = linarith(w, ph, [i1le, c['N <_ %s' % NW]], 'i < %s' % NW, closure=cl)
    iw = s([s([inn, s([B.nwn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, NW)), ilw], '3jca',
              '( %s -> ( i e. NN0 /\\ %s e. ZZ /\\ i < %s ) )' % (ph, NW, NW)), w.inst('elfzo0z')], 'sylibr',
           '( %s -> i e. ( 0 ..^ %s ) )' % (ph, NW))
    WI = '( W ` i )'
    V1 = DRP('( i + 1 )')
    win = s([B.ww, iw, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WI))
    v1w = s([B.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, V1))
    dr = s([B.ww, iw, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, DRP('i'), WI, V1))
    ec = s([win, v1w, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" %s "> ++ %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )'
           % (ph, WI, V1, WI, V1))
    e1 = s([s([dr], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( <" %s "> ++ %s ) ) )' % (ph, DRP('i'), WI, V1)), ec], 'eqtrd',
           '( %s -> ( encList ` %s ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (ph, DRP('i'), WI, V1))
    ew = encw(w, ph, WI, win)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    elv = s([v1w, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, V1))
    ca1 = s([ew, wgcat(w, ph, '<" 4 ">', '( encList ` %s )' % V1, s4, elv), B.xw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ X ) = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) )'
            % (ph, WI, V1, WI, V1))
    ca2 = s([s4, elv, B.xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) = ( <" 4 "> ++ %s ) )' % (ph, V1, REST('( i + 1 )')))
    KT = EWg(WI, REST('( i + 1 )'))
    r1 = s([s([e1], 'oveq1d', '( %s -> %s = ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ X ) )' % (ph, REST('i'), WI, V1)), ca1], 'eqtrd',
           '( %s -> %s = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) )' % (ph, REST('i'), WI, V1))
    r2 = s([r1, s([ca2], 'oveq2d', '( %s -> ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) = %s )' % (ph, WI, V1, KT))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, REST('i'), KT))
    g1 = B.g(REST('( i + 1 )'), enclg(w, ph, V1, v1w, 'X', B.xw))
    gk = B.g(KT, ewg_(w, ph, WI, win, REST('( i + 1 )'), g1))
    Spb = B.pbst('i', inn, ile)
    chain0 = [('5', EWg(NM('i'), 'Y')), ('4', KT)]
    R = B.run()
    S5 = B.S0.upd('5', EWg(NM('i'), 'Y'), B.gam[EWg(NM('i'), 'Y')])
    Ssp = S5.upd('4', KT, gk)
    R.S, R.chain = Ssp, list(chain0)
    for _k, (_txt, _st, _g) in Ssp.vals.items():
        R.gam[_txt] = _g
    p2 = '( 2 ^ B )'
    # 1. dropNum 4
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ %s ) )' % (ph, NW)), iw, w.inst('fnfvelrn')], 'syl2anc',
           '( %s -> %s e. ran W )' % (ph, WI))
    wlt = s([s([], 'breq1', '( a = %s -> ( a < %s <-> %s < %s ) )' % (WI, p2, WI, p2)), wr, c[RALB('W')]], 'rspcdva',
            '( %s -> %s < %s )' % (ph, WI, p2))
    B.call(R, 'tmidropb', {'K': '4', 'F': WI, 'N': 'B', 'X': REST('( i + 1 )'), 'P': PBL(1), 'E': PL(PBL(2), 0)},
           {'%s e. NN0' % WI: win, '%s < %s' % (WI, p2): wlt}, [('4', REST('( i + 1 )'), g1)], on=(S5, chain0[:1]))
    # 2. predNum 5 6
    NMi = NM('i')
    cl.leaf(NMi, 'NN0', B.nmn('i', inn, ile)) if False else None
    nmnn = s([s([ilt, s([cl.mem('i', 'RR'), cl.mem('N', 'RR')], 'posdifd', '( %s -> ( i < N <-> 0 < %s ) )' % (ph, NMi))], 'mpbid',
                '( %s -> 0 < %s )' % (ph, NMi)), s([B.nmn('i', inn, ile)], 'id', '( %s -> %s e. NN0 )' % (ph, NMi))], 'jca',
             '( %s -> ( 0 < %s /\\ %s e. NN0 ) )' % (ph, NMi, NMi)) if False else None
    nmp = s([ilt, s([cl.mem('i', 'RR'), cl.mem('N', 'RR')], 'posdifd', '( %s -> ( i < N <-> 0 < %s ) )' % (ph, NMi))], 'mpbid',
            '( %s -> 0 < %s )' % (ph, NMi))
    nmnn = s([s([B.nmn('i', inn, ile), nmp], 'jca', '( %s -> ( %s e. NN0 /\\ 0 < %s ) )' % (ph, NMi, NMi)),
              s([], 'elnnnn0b', '( %s e. NN <-> ( %s e. NN0 /\\ 0 < %s ) )' % (NMi, NMi, NMi))], 'sylibr', '( %s -> %s e. NN )' % (ph, NMi))
    nlt = linarith(w, ph, [c['N < %s' % p2], cl.ge0('i')], '%s < %s' % (NMi, p2), closure=cl)
    NM1 = '( %s - 1 )' % NMi
    nm1n = s([nmnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, NM1))
    E51 = EWg(NM1, 'Y')
    B.call(R, 'tmiprdbs', {'K': '5', 'J': '6', 'F': NMi, 'N': 'B', 'X': 'Y', 'P': PBL(2), 'E': PL(PBL(3), 0)},
           {'%s e. NN' % NMi: nmnn, '%s < %s' % (NMi, p2): nlt}, [('5', E51, B.g(E51, ewg_(w, ph, NM1, nm1n, 'Y', B.yw)))])
    # 3. isZero 5 6
    n1lt = linarith(w, ph, [c['N < %s' % p2], cl.ge0('i')], '%s < %s' % (NM1, p2), closure=cl)
    B.call(R, 'tmiizbs', {'K': '5', 'I': '6', 'F': NM1, 'N': 'B', 'X': 'Y', 'P': PBL(3), 'E': PBL(0)},
           {'%s e. NN0' % NM1: nm1n, '%s < %s' % (NM1, p2): n1lt}, [])
    # 4. peekBraOr 4: the flag becomes ( ( N - i ) - 1 = 0 \/ i + 1 = # W ) , i.e. i + 1 = N
    I1 = '( i + 1 )'
    i1z = s([iw, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ph, I1, NW))
    de = drp_empty(w, ph, B.ww, B.nwn, I1, i1z)
    CND = '%s = N' % I1

    def bi_rest(HD, hb, V0):
        assert V0 == 'if ( %s = 0 , 1o , (/) )' % NM1, V0
        e1_ = s([s([], 'tmcif1', '( %s = 1o <-> %s = 0 )' % (V0, NM1))], 'a1i', '( %s -> ( %s = 1o <-> %s = 0 ) )' % (ph, V0, NM1))
        e2_ = s([hb, de], 'bitrd', '( %s -> ( %s = 2 <-> %s = %s ) )' % (ph, HD, I1, NW))
        ob = s([e1_, e2_], 'orbi12d', '( %s -> ( ( %s = 1o \\/ %s = 2 ) <-> ( %s = 0 \\/ %s = %s ) ) )' % (ph, V0, HD, NM1, I1, NW))
        pa = '( %s /\\ %s = 0 )' % (ph, NM1)
        cla = Closure(w, pa, {'i': ('NN0', lift_from(w, ph, pa, inn)), 'N': ('NN0', lift_from(w, ph, pa, B.nn))})
        da = lineq(w, pa, I1, 'N', hyps=[s([], 'simpr', '( %s -> %s = 0 )' % (pa, NM1))], closure=cla)
        pb = '( %s /\\ %s = %s )' % (ph, I1, NW)
        clb = Closure(w, pb, {'i': ('NN0', lift_from(w, ph, pb, inn)), 'N': ('NN0', lift_from(w, ph, pb, B.nn))})
        clb.leaf(NW, 'NN0', lift_from(w, ph, pb, B.nwn))
        db = lineq(w, pb, I1, 'N', hyps=[s([], 'simpr', '( %s -> %s = %s )' % (pb, I1, NW)), lift_from(w, ph, pb, i1le),
                                         lift_from(w, ph, pb, c['N <_ %s' % NW])], closure=clb)
        pc_ = '( %s /\\ %s = N )' % (ph, I1)
        clc = Closure(w, pc_, {'i': ('NN0', lift_from(w, ph, pc_, inn)), 'N': ('NN0', lift_from(w, ph, pc_, B.nn))})
        dc = lineq(w, pc_, NM1, '0', hyps=[s([], 'simpr', '( %s -> %s = N )' % (pc_, I1))], closure=clc)
        OR = '( %s = 0 \\/ %s = %s )' % (NM1, I1, NW)
        fw = s([s([da], 'ex', '( %s -> ( %s = 0 -> %s ) )' % (ph, NM1, CND)), s([db], 'ex', '( %s -> ( %s = %s -> %s ) )' % (ph, I1, NW, CND))],
               'jaod', '( %s -> ( %s -> %s ) )' % (ph, OR, CND))
        bw = s([s([dc], 'orcd', '( %s -> %s )' % (pc_, OR))], 'ex', '( %s -> ( %s -> %s ) )' % (ph, CND, OR))
        ib = s([fw, bw], 'impbid', '( %s -> ( %s <-> %s ) )' % (ph, OR, CND))
        return s([ob, ib], 'bitrd', '( %s -> ( ( %s = 1o \\/ %s = 2 ) <-> %s ) )' % (ph, V0, HD, CND))
    N1c = peek_step(w, ph, B, R, V1, v1w, CND, bi_rest, PBL(0), PL('P', 1))
    # the post
    cur, out2 = R.normalize(ORD54)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    TB = '( TMB ` B )'
    cl.leaf(TB, 'NN0', B.tbn)
    le = linarith(w, ph, [], '%s <_ %s' % (n, TPR), closure=cl, atoms=[TB])
    t = hrle(w, ph, mk['phm'], t, C, D, n, TPR, cl.mem(TPR, 'NN0'), le)
    n = TPR
    X1 = chain_text('D', chain0)
    C2 = CLN(LMN['Y2'], NI, X1)
    t = hrssc(w, ph, mk['phm'], t, C, D, n, C2, clnss(w, ph, LMN['Y2'], NI, S, X1, B.famss('i', inn)))
    i1lN = i1le
    pv1, S1 = B.pv(I1, i1n, i1lN)
    P1T = '( %s ` %s )' % (PV, I1)
    fe = s([cl.mem('N', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph), w.inst('subsub4')],
           'syl3anc', '( %s -> %s = %s )' % (ph, NM1, NM(I1)))
    Dst = triple_D(D)
    assert Dst == chain_text('D', out2), (Dst, out2)
    r2_, x2 = w.rewrite(Dst, {NM1: (NM(I1), fe)}, ph)
    assert x2 == PB(I1), (x2, PB(I1))
    deq = s([r2_, pv1], 'eqtr4d', '( %s -> %s = %s )' % (ph, Dst, P1T))
    Ncur = D.split(' } X. ( ', 1)[1].rsplit(' X. { ', 1)[0]
    assert Ncur == N1c == NCL(I1), (Ncur, N1c)
    N1 = '( %s ` %s )' % (NFM, I1)
    cq = s([famval(w, ph, COND, I1, i1n)], 'eqcomd', '( %s -> %s = %s )' % (ph, NCL(I1), N1))
    lab_ = PL('P', 1)
    ceq = s([clnneq(w, ph, lab_, cq, Ncur, N1, Dst), clneq(w, ph, lab_, N1, deq, Dst, P1T)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN(lab_, N1, P1T)))
    # the pre: X1 = PB( i ) = ( P' ` i )
    rx, xx = w.rewrite(X1, {KT: (REST('i'), s([r2], 'eqcomd', '( %s -> %s = %s )' % (ph, KT, REST('i'))))}, ph)
    assert xx == PB('i'), xx
    cpre = clneq(w, ph, LMN['Y2'], NI, s([rx, s([pvi], 'eqcomd', '( %s -> %s = %s )' % (ph, PB('i'), PT))], 'eqtrd',
                                         '( %s -> %s = %s )' % (ph, X1, PT)), X1, PT)
    t, C, D, n = hrrw(w, ph, t, C2, D, n, ceq=cpre, deq=ceq)
    st = s([part1, t], 'jca', '( %s -> %s )' % (ph, LBODY))
    finish(w, st, lab)
    return w.run()


def tmidnt():
    lab = 'tmidnt'
    w = W(lab, 'The frame of Lean\'s ` dropN ` loop at the machine: for ` i <_ N ` the class family is a set of states and '
               'the stack family a stack assignment, and at ` N ` the flag is set.')
    s = w.s
    TT = numtree((PSI_T, 'i e. ( 0 ... N )'))
    pt = cj(TT)
    B = Ld(w, pt, TT)
    ii = B.c['i e. ( 0 ... N )']
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ N )' % pt)
    pv, St = B.pv('i', inn, ile)
    body = LTYP[len('A. i e. ( 0 ... N ) '):]
    one = s([B.famss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))
    p0 = cj((PSI_T, 'i e. ( 0 ... N )'))
    k = s([], 't10stk', ST_NUMS)
    one0 = s([k, one], 'mpan2', '( %s -> %s )' % (p0, body))
    typ = s([one0], 'ralrimiva', '( %s -> %s )' % (PSI, LTYP))
    TE = numtree(PSI_T)
    pe = cj(TE)
    L = Ld(w, pe, TE)
    f1 = s([s([], 'eqidd', '( %s -> N = N )' % pe)], 'iftrued', '( %s -> %s = 1o )' % (pe, FLC('N')))
    NE = '( %s ` N )' % NFM
    pm = '( %s /\\ m e. %s )' % (pe, NE)
    mm, mc = fam_unpack(w, pm, COND, 'N', lift_from(w, pe, pm, L.nn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)))
    fl = s([mc, lift_from(w, pe, pm, f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    ex_ = s([cnfl_at(w, pm, mm, fl, True)], 'ralrimiva', '( %s -> %s )' % (pe, LEXIT))
    ex0 = s([k, ex_], 'mpan2', '( %s -> %s )' % (PSI, LEXIT))
    w.qed([typ, ex0], 'jca', STMTS10[lab])
    return w.run()


def tmidnl():
    lab = 'tmidnl'
    w = W(lab, 'Lean\'s ` dropN ` loop at the machine: ~ tm2floopu at the families ( ` P\' ` a letter), ` N ` iterations '
               'of ` dropNBody ` (~ tmidni ), the frame by ~ tmidnt .')
    s = w.s
    T = numtree(PSI_T)
    ph = cj(T)
    B = Ld(w, ph, T)
    B.deep('dn', 1)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmidnt', STMTS10['tmidnt']))
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    per = s([s([], 'tmidni', STMTS10['tmidni'])], 'ralrimiva', '( %s -> %s )' % (PSI, LPER))
    ex[LPER] = lift_from(w, PSI, ph, per)
    ex['N e. NN0'] = B.nn
    cl = Closure(w, ph, {'B': ('NN0', B.bn)})
    cl.leaf('( TMB ` B )', 'NN0', B.tbn)
    ex['%s e. NN0' % TPR] = cl.mem(TPR, 'NN0')
    ex['%s e. ( 2o ^m %s )' % (CNFL, S)] = B.ex['%s e. ( 2o ^m %s )' % (CNFL, S)]
    st = Bld(w, ph, B.c, ex)(LTREE)
    st2 = s([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ph, LCONCL))
    finish(w, st2, lab)
    return w.run()


def tmidnb():
    lab = 'tmidnb'
    T = numtree(TREE_DN)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` dropN_le_B ` at the machine ( ` x c s = 4 5 6 ` , with ` N <_ # W ` ): ` isZero 5 6 ; peekBraOr 4 ` , '
               'the loop (~ tmidnl ), ` dropNum 5 ` : stack 4 holds the list without its first ` N ` entries, the counter is '
               'consumed, every other stack restored, within ` ( # W + 1 ) 4 B b ` steps.')
    s = w.s
    B = Ld(w, ph, T)
    c, mk = B.c, B.mk
    p2 = '( 2 ^ B )'
    TB = '( TMB ` B )'
    cl = Closure(w, ph, {'N': ('NN0', B.nn), 'B': ('NN0', B.bn)})
    cl.leaf(NW, 'NN0', B.nwn)
    # 1. isZero 5 6
    R = B.run()
    B.call(R, 'tmiizbs', {'K': '5', 'I': '6', 'F': 'N', 'N': 'B', 'X': 'Y', 'P': PL('P', 2), 'E': LMN['Z1']},
           {'N e. NN0': B.nn, 'N < %s' % p2: c['N < %s' % p2]}, [])
    # 2. peekBraOr 4
    CND = '0 = N'

    def bi_rest(HD, hb, V0):
        assert V0 == 'if ( N = 0 , 1o , (/) )', V0
        e1_ = s([s([], 'tmcif1', '( %s = 1o <-> N = 0 )' % V0)], 'a1i', '( %s -> ( %s = 1o <-> N = 0 ) )' % (ph, V0))
        ob = s([e1_, hb], 'orbi12d', '( %s -> ( ( %s = 1o \\/ %s = 2 ) <-> ( N = 0 \\/ W = (/) ) ) )' % (ph, V0, HD))
        OR = '( N = 0 \\/ W = (/) )'
        pa = '( %s /\\ N = 0 )' % ph
        da = s([s([], 'simpr', '( %s -> N = 0 )' % pa)], 'eqcomd', '( %s -> 0 = N )' % pa)
        pb = '( %s /\\ W = (/) )' % ph
        h0 = s([s([s([], 'simpr', '( %s -> W = (/) )' % pb)], 'fveq2d', '( %s -> %s = ( # ` (/) ) )' % (pb, NW)),
                closed(w, pb, 'hash0', '( # ` (/) ) = 0')], 'eqtrd', '( %s -> %s = 0 )' % (pb, NW))
        clb = Closure(w, pb, {'N': ('NN0', lift_from(w, ph, pb, B.nn))})
        clb.leaf(NW, 'NN0', lift_from(w, ph, pb, B.nwn))
        db = lineq(w, pb, '0', 'N', hyps=[h0, clb.ge0('N'), lift_from(w, ph, pb, c['N <_ %s' % NW])], closure=clb)
        pc_ = '( %s /\\ 0 = N )' % ph
        dc = s([s([s([], 'simpr', '( %s -> 0 = N )' % pc_)], 'eqcomd', '( %s -> N = 0 )' % pc_)], 'orcd', '( %s -> %s )' % (pc_, OR))
        fw = s([s([da], 'ex', '( %s -> ( N = 0 -> %s ) )' % (ph, CND)), s([db], 'ex', '( %s -> ( W = (/) -> %s ) )' % (ph, CND))],
               'jaod', '( %s -> ( %s -> %s ) )' % (ph, OR, CND))
        bw = s([dc], 'ex', '( %s -> ( %s -> %s ) )' % (ph, CND, OR))
        ib = s([fw, bw], 'impbid', '( %s -> ( %s <-> %s ) )' % (ph, OR, CND))
        return s([ob, ib], 'bitrd', '( %s -> ( ( %s = 1o \\/ %s = 2 ) <-> %s ) )' % (ph, V0, HD, CND))
    N1c = peek_step(w, ph, B, R, 'W', B.ww, CND, bi_rest, LMN['Z1'], LMN['Z2'])
    assert N1c == NCL('0'), N1c
    # 3. the family at 0
    z0 = closed(w, ph, '0nn0', '0 e. NN0')
    zle = s([B.nn], 'nn0ge0d', '( %s -> 0 <_ N )' % ph)
    N0 = '( %s ` 0 )' % NFM
    ceq0 = s([famval(w, ph, COND, '0', z0)], 'eqcomd', '( %s -> %s = %s )' % (ph, NCL('0'), N0))
    PB0 = PB('0')
    pbx = s([B.pbst('0', z0, zle).memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB0))
    pfv = mval(w, ph, 'j', 'NN0', PB, '0', z0, pbx)
    h0 = s([cl.mem('N', 'CC'), w.inst('subid1')], 'syl', '( %s -> ( N - 0 ) = N )' % ph)
    pv_ = s([B.ww, B.nwn, w.inst('pfxval')], 'syl2anc', '( %s -> ( W prefix %s ) = %s )' % (ph, NW, DRP('0')))
    w0 = s([pv_, s([B.ww, w.inst('pfxid')], 'syl', '( %s -> ( W prefix %s ) = W )' % (ph, NW))], 'eqtr3d', '( %s -> %s = W )' % (ph, DRP('0')))
    rs, xs = w.rewrite(PB0, {NM('0'): ('N', h0), DRP('0'): ('W', w0)}, ph)
    X5 = UP('D', '5', EWg('N', 'Y'))
    assert xs == UP(X5, '4', ENCL('W', 'X')), xs
    u5 = upidv(w, ph, 'D', '5', EWg('N', 'Y'), B.S0.vals['5'][1], mk['tv'], B.dd, mk['k']['5']['kd'])
    r5, x5 = w.rewrite(xs, {X5: ('D', u5)}, ph)
    assert x5 == UP('D', '4', ENCL('W', 'X')), x5
    u4 = upidv(w, ph, 'D', '4', ENCL('W', 'X'), B.S0.vals['4'][1], mk['tv'], B.dd, mk['k']['4']['kd'])
    pf0 = '( %s ` 0 )' % PF
    se = s([s([s([s([pfv, rs], 'eqtrd', '( %s -> %s = %s )' % (ph, pf0, xs)), r5], 'eqtrd', '( %s -> %s = %s )' % (ph, pf0, x5)), u4],
              'eqtrd', '( %s -> %s = D )' % (ph, pf0))], 'eqcomd', '( %s -> D = %s )' % (ph, pf0))
    lab0 = LMN['Z2']
    assert R.S.D == 'D'
    ceq = s([clnneq(w, ph, lab0, ceq0, NCL('0'), N0, 'D'), clneq(w, ph, lab0, N0, se, 'D', pf0)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, R.cur, CLN(lab0, N0, pf0)))
    t1, C1, D1, n1 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=ceq)
    # 4. the loop at P' := PF
    ex = {'%s = %s' % (PF, PF): s([s([], 'eqid', '%s = %s' % (PF, PF))], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}
    tl, cl_ = inst(w, ph, 'tmidnl', {PV: PF}, Bld(w, ph, c, ex))
    C2, D2, n2 = triple_parts(cl_)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, mk['phm'], t1, tl, C1, D1, D2, n1, n2)
    n12 = '( %s + %s )' % (n1, n2)
    # 5. dropNum 5 from ( PF ` N )
    nle = s([cl.mem('N', 'RR')], 'leidd', '( %s -> N <_ N )' % ph)
    SR = B.pbst('N', B.nn, nle)
    pbr = s([SR.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB('N')))
    pfr = mval(w, ph, 'j', 'NN0', PB, 'N', B.nn, pbr)
    PFR = '( %s ` N )' % PF
    NR = '( %s ` N )' % NFM
    chi = list(B.last)
    ORD5 = ['0', '1', '2', '3', '4', '6', '7', '5']
    nst, outR = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chi, B.gam, ORD5)
    deqR = s([pfr, nst], 'eqtrd', '( %s -> %s = %s )' % (ph, PFR, chain_text('D', outR)))
    t12, C12, D12, n12 = hrrw(w, ph, t12, C1, D2, n12, deq=clneq(w, ph, LMN['Y3'], NR, deqR, PFR, chain_text('D', outR)))
    R2 = B.run()
    SRr = B.S0
    for k_, v_ in outR:
        SRr = SRr.upd(k_, v_, B.gam[v_])
    R2.S, R2.chain = SRr, list(outR)
    for _k, (_txt, _st, _g) in SRr.vals.items():
        R2.gam[_txt] = _g
    S4 = R2.at(outR[:1])
    NN_ = NM('N')
    nnn = B.nmn('N', B.nn, nle)
    cl.leaf(NN_, 'NN0', nnn) if False else None
    nnlt = linarith(w, ph, [c['N < %s' % p2], cl.ge0('N')], '%s < %s' % (NN_, p2), closure=cl)
    B.call(R2, 'tmidropb', {'K': '5', 'F': NN_, 'N': 'B', 'X': 'Y', 'P': PL('P', 4), 'E': 'E'},
           {'%s e. NN0' % NN_: nnn, '%s < %s' % (NN_, p2): nnlt}, [('5', 'Y', B.yw)], on=(S4, outR[:1]))
    cur, outF = R2.normalize(N8)
    t3, C3, D3, n3 = R2.tri, R2.C0, R2.cur, R2.n
    FT = chain_text('D', outR)
    C3n = CLN(LMN['Y3'], NR, FT)
    t3 = hrssc(w, ph, mk['phm'], t3, C3, D3, n3, C3n, clnss(w, ph, LMN['Y3'], NR, S, FT, B.famss('N', B.nn)))
    assert C3n == D12, (C3n, D12)
    t = hrseq(w, ph, mk['phm'], t12, t3, C1, D12, D3, n12, n3)
    nT = '( %s + %s )' % (n12, n3)
    assert D3 == CONCL_DN.split(' ( T TM2Hoare M ) <. ', 1)[1].rsplit(' , ', 1)[0], D3
    # 6. the bound
    BND = '( ( %s + 1 ) x. ( 4 x. %s ) )' % (NW, TB)
    cl.leaf(TB, 'NN0', B.tbn)
    import num
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([B.bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( B + 2 ) ^ 2 ) ) <_ %s )' % (ph, TB))
    t2 = nlinarith(w, ph, [qd, cl.ge0('B')], '2 <_ %s' % TB, closure=cl, atoms=['B', TB])
    p1 = s([cl.mem('N', 'RR'), cl.mem(NW, 'RR'), cl.mem(TB, 'RR'), cl.ge0(TB), c['N <_ %s' % NW]], 'lemul1ad',
           '( %s -> ( N x. %s ) <_ ( %s x. %s ) )' % (ph, TB, NW, TB))
    p2_ = s([closed(w, ph, '2re', '2 e. RR'), cl.mem(TB, 'RR'), cl.mem('N', 'RR'), cl.ge0('N'), t2], 'lemul2ad',
            '( %s -> ( N x. 2 ) <_ ( N x. %s ) )' % (ph, TB))
    le = linarith(w, ph, [p1, p2_, t2], '%s <_ %s' % (nT, BND), closure=cl, atoms=['N', NW, TB], products=True)
    st = hrle(w, ph, mk['phm'], t, C1, D3, nT, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
