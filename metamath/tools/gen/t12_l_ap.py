"""T12: allPrimeTDF at the machine (Step5.lean ` apBody ` , ` allPrimeTDF ` ; blueprint D4).

  t12apcost  ` ( 2nd ( AllPrimeTD W ) ) = sum_ j ( ( 2nd ( IsPrimeTD ( W ` j ) ) ) + 1 ) ` (telescoped, ~ telfsumo )
  t12apfst   the machine's allPrime flag is ` ( 1st ( AllPrimeTD W ) ) ` (~ allprimetdfst , ~ isprimetdspec , ~ ralrn )
  tmiapai    one entry of the loop ( ` apBody_runs ` ) along the family ` P' ` (~ tmiptb , ~ tmiaca , ~ tmidropb )
  tmiapat    the frame (the family's typing, its column 5, its values at 0 and at the end)
  tmiapal    ` accLoopF apBody ` at the family (~ tmiacl )
  tmiap      ` allPrimeTDF_runs ` : ~ tmilcpyb then ~ tmiapal

    MM_DB=sorties/t12.mm python3 tools/gen/t12_l_ap.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq, nlinarith
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t10_n_rgf import tmbn
from t10_e_doa import lift_from
from t10_d_dot import cls_to
from t10_u_s2s import expose
from a4alib import projeq, paircl
import t8alib as A8
import t7c_h_lst as LST
import t12_j_acc as ACC
import t12_k_ko as KO
from t12_k_ko import flag_if, ral_ran, acc_step, LG, NLG, DOM, EB, C5, PV
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
TB = lambda x: '( TMB ` %s )' % x
IP1 = lambda p: '( 1st ` ( IsPrimeTD ` %s ) )' % p
IP2 = lambda p: '( 2nd ` ( IsPrimeTD ` %s ) )' % p
PT = lambda p: '%s = 1o' % IP1(p)                 # the machine's test at p
PT_I = lambda i: PT('( W ` %s )' % i)
ANDW = lambda tcond: 'A. i e. ( 0 ..^ ( # ` W ) ) %s' % tcond('i')
NW = '( # ` W )'
SUMC = 'sum_ j e. ( 0 ..^ %s ) ( %s + 1 )' % (NW, IP2('( W ` j )'))
ST_APCOST = '( W e. Word NN0 -> ( 2nd ` ( AllPrimeTD ` W ) ) = %s )' % SUMC
ST_APFST = '( W e. Word NN0 -> ( 1st ` ( AllPrimeTD ` W ) ) = if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o ) )' % ANDW(PT_I)
B37 = '( ( 3 x. B ) + 7 )'


def t12apcost():
    lab = 't12apcost'
    A = 'W e. Word NN0'
    w = W(lab, 'The cost of ` allPrimeTD ` is the sum of the entries\' ` isPrimeTD ` costs plus one each (Lean\'s '
               '` allPrimeTD_cons ` at every suffix, telescoped by ~ telfsumo ).')
    s = w.s
    lw = s([], 'id', '( %s -> W e. Word NN0 )' % A)
    SUB = lambda k: '( W substr <. %s , %s >. )' % (k, NW)
    KF = lambda k: '( 2nd ` ( AllPrimeTD ` %s ) )' % SUB(k)
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (A, NW)
    jj = s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NW))
    lwj = s([], 'simpl', '( %s -> W e. Word NN0 )' % pj)
    D_ = '( W ` j )'
    S1 = '<" %s ">' % D_
    J1 = '( j + 1 )'
    dn = s([lwj, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pj, D_))
    dr = s([lwj, jj, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (pj, SUB('j'), S1, SUB(J1)))
    rw = s([lwj, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pj, SUB(J1)))
    cs = s([dn, rw, w.inst('allprimetdcs')], 'syl2anc',
           '( %s -> ( AllPrimeTD ` ( %s ++ %s ) ) = <. if ( %s = 1o , ( 1st ` ( AllPrimeTD ` %s ) ) , (/) ) , ( ( %s + ( 2nd ` ( AllPrimeTD ` %s ) ) ) + 1 ) >. )'
           % (pj, S1, SUB(J1), IP1(D_), SUB(J1), IP2(D_), SUB(J1)))
    IFE = 'if ( %s = 1o , ( 1st ` ( AllPrimeTD ` %s ) ) , (/) )' % (IP1(D_), SUB(J1))
    SUM_ = '( ( %s + %s ) + 1 )' % (IP2(D_), KF(J1))
    e1 = s([s([dr], 'fveq2d', '( %s -> ( AllPrimeTD ` %s ) = ( AllPrimeTD ` ( %s ++ %s ) ) )' % (pj, SUB('j'), S1, SUB(J1))), cs], 'eqtrd',
           '( %s -> ( AllPrimeTD ` %s ) = <. %s , %s >. )' % (pj, SUB('j'), IFE, SUM_))
    cl1 = s([rw, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (pj, SUB(J1)))
    a1, b1 = paircl(w, pj, '( AllPrimeTD ` %s )' % SUB(J1), cl1, '2o', 'NN0')
    ipc = s([dn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (pj, D_))
    ia, ib = paircl(w, pj, '( IsPrimeTD ` %s )' % D_, ipc, '2o', 'NN0')
    xa = s([a1, s([s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % pj)], 'ifcld', '( %s -> %s e. 2o )' % (pj, IFE))
    xb = s([s([ib, b1], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (pj, IP2(D_), KF(J1))), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pj, SUM_))
    k2 = projeq(w, pj, '( AllPrimeTD ` %s )' % SUB('j'), e1, IFE, SUM_, xa, xb, 2)
    cl = Closure(w, pj, {})
    cl.leaf(IP2(D_), 'NN0', ib); cl.leaf(KF(J1), 'NN0', b1)
    cl.leaf(KF('j'), 'NN0', s([k2, xb], 'eqeltrd', '( %s -> %s e. NN0 )' % (pj, KF('j'))))
    dif = linarith_eq(w, pj, '( %s + 1 )' % IP2(D_), '( %s - %s )' % (KF('j'), KF(J1)), [k2], cl)
    SUMD = 'sum_ j e. ( 0 ..^ %s ) ( %s - %s )' % (NW, KF('j'), KF(J1))
    se = s([dif], 'sumeq2dv', '( %s -> %s = %s )' % (A, SUMC, SUMD))

    def kcong(a_):
        e = s([], 'id', '( k = %s -> k = %s )' % (a_, a_))
        cg, new = w.congr(KF('k'), {'k': a_}, 'k = %s' % a_, {'k': e})
        assert new == KF(a_), new
        return cg
    nw = s([lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (A, NW))
    huz = s([nw, s([s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % A)], 'eleqtrd', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (A, NW))
    pk = '( %s /\\ k e. ( 0 ... %s ) )' % (A, NW)
    lwk = s([], 'simpl', '( %s -> W e. Word NN0 )' % pk)
    rwk = s([lwk, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pk, SUB('k')))
    clk = s([rwk, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (pk, SUB('k')))
    kac = s([s([clk, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pk, KF('k')))], 'nn0cnd', '( %s -> %s e. CC )' % (pk, KF('k')))
    tel = s([kcong('j'), kcong(J1), kcong('0'), kcong(NW), huz, kac], 'telfsumo', '( %s -> %s = ( %s - %s ) )' % (A, SUMD, KF('0'), KF(NW)))
    e_0 = s([s([s([lw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = W )' % (A, SUB('0')))], 'fveq2d', '( %s -> ( AllPrimeTD ` %s ) = ( AllPrimeTD ` W ) )' % (A, SUB('0')))],
            'fveq2d', '( %s -> %s = ( 2nd ` ( AllPrimeTD ` W ) ) )' % (A, KF('0')))
    z0 = s([s([s([s([], 'swrd00', '%s = (/)' % SUB(NW))], 'fveq2i', '( AllPrimeTD ` %s ) = ( AllPrimeTD ` (/) )' % SUB(NW)),
                s([], 'allprimetd0', '( AllPrimeTD ` (/) ) = <. 1o , 0 >.')], 'eqtri', '( AllPrimeTD ` %s ) = <. 1o , 0 >.' % SUB(NW))], 'fveq2i',
            '%s = ( 2nd ` <. 1o , 0 >. )' % KF(NW))
    z1 = s([z0, s([s([], '1oex', '1o e. _V'), s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. 1o , 0 >. ) = 0')], 'eqtri', '%s = 0' % KF(NW))
    AW = '( 2nd ` ( AllPrimeTD ` W ) )'
    awn = s([s([lw, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. ( 2o X. NN0 ) )' % A), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (A, AW))
    d2 = s([e_0, s([z1], 'a1i', '( %s -> %s = 0 )' % (A, KF(NW)))], 'oveq12d', '( %s -> ( %s - %s ) = ( %s - 0 ) )' % (A, KF('0'), KF(NW), AW))
    d3 = s([s([awn], 'nn0cnd', '( %s -> %s e. CC )' % (A, AW))], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A, AW, AW))
    w.qed([s([se, tel, d2, d3], '3eqtrd' if False else '3eqtrd', '( %s -> %s = %s )' % (A, SUMC, AW)) if False else
           s([s([s([se, tel], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A, SUMC, KF('0'), KF(NW))), d2, d3], '3eqtrd', '( %s -> %s = %s )' % (A, SUMC, AW))],
             'eqcomd', '( %s -> %s = %s )' % (A, AW, SUMC)), w.inst('biid')], 'mpbi', ST_APCOST)
    return w.run()


def linarith_eq(w, ph, a, b, hyps, cl):
    s = w.s
    l1 = linarith(w, ph, hyps, '%s <_ %s' % (a, b), closure=cl)
    l2 = linarith(w, ph, hyps, '%s <_ %s' % (b, a), closure=cl)
    rr = s([cl.mem(a, 'RR'), cl.mem(b, 'RR')], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (ph, a, b))
    bi = s([rr, w.inst('letri3')], 'syl', '( %s -> ( %s = %s <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (ph, a, b, a, b, b, a))
    return s([bi, s([l1, l2], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ph, a, b, b, a))], 'mpbird', '( %s -> %s = %s )' % (ph, a, b))


def t12apfst():
    lab = 't12apfst'
    A = 'W e. Word NN0'
    w = W(lab, 'The machine\'s allPrime flag (the conjunction of ` isPrimeTD ` over the entries) is A1b\'s '
               '` ( 1st ( AllPrimeTD S ) ) ` (~ allprimetdfst , ~ isprimetdspec , ~ ralrn ).')
    s = w.s
    ww = s([], 'id', '( %s -> W e. Word NN0 )' % A)
    AP = '( 1st ` ( AllPrimeTD ` W ) )'
    fst = s([ww, w.inst('allprimetdfst')], 'syl', '( %s -> ( %s = 1o <-> A. p e. ran W p e. Prime ) )' % (A, AP))
    pp = '( %s /\\ p e. ran W )' % A
    pnn = s([s([s([s([ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % A), w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % A)],
              'adantr', '( %s -> ran W C_ NN0 )' % pp), s([], 'simpr', '( %s -> p e. ran W )' % pp)], 'sseldd', '( %s -> p e. NN0 )' % pp)
    bi = s([pnn, w.inst('isprimetdspec')], 'syl', '( %s -> ( %s <-> p e. Prime ) )' % (pp, PT('p')))
    rb = s([bi], 'ralbidva', '( %s -> ( A. p e. ran W %s <-> A. p e. ran W p e. Prime ) )' % (A, PT('p')))
    rr = ral_ran(w, A, PT, 'p', ww)
    iff = s([fst, s([s([rb], 'bicomd', '( %s -> ( A. p e. ran W p e. Prime <-> A. p e. ran W %s ) )' % (A, PT('p'))), rr], 'bitrd',
                     '( %s -> ( A. p e. ran W p e. Prime <-> %s ) )' % (A, ANDW(PT_I)))], 'bitrd', '( %s -> ( %s = 1o <-> %s ) )' % (A, AP, ANDW(PT_I)))
    a2 = s([s([ww, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. ( 2o X. NN0 ) )' % A), w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (A, AP))
    w.qed([flag_if(w, A, ANDW(PT_I), AP, iff, a2), w.inst('biid')], 'mpbi', ST_APFST)
    return w.run()


# ------------------------------------------------------------ the loop: apa = accLoopF apBody at the family
# bit bounds: the entries below 2 ^ B ; the accumulator, isZero and dropNum 1 at 3 B + 7 (no entry needed for 1 < 2 ^ ( 3 B + 7 ) )
ACC = lambda k: 'if ( A. i e. ( 0 ..^ %s ) %s , 1 , 0 )' % (k, PT_I('i'))
E1 = lambda k: EWg(ACC(k), DK(1))
PB = lambda k: UPS('D', ('1', E1(k)), ('5', C5(k)))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
DATA_APL = ((STKD('D'), 'W e. Word NN0', 'B e. NN0'), (RALB('W', 'B'), WG('R')), DEQ(5, ENCL('W', 'R')))
TREE_APA = TREE0('apa', DATA_APL)
PSI_T = (TREE_APA, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
TB37 = TB(B37)
KC = '( ( 2 x. %s ) + ( %s + 1 ) )' % (TB37, TB('B'))
YJ = lambda j: '( ( %s x. ( %s + 1 ) ) + %s )' % (TB37, IP2('( W ` %s )' % j), KC)
YF = '( i e. NN0 |-> %s )' % YJ('i')
APC2 = '( 2nd ` ( AllPrimeTD ` W ) )'
UC = '( ( %s x. %s ) + ( %s x. ( %s + 2 ) ) )' % (TB37, APC2, NW, KC)
LMA = FRAGS['apa'].lmap()
GM_AP = {'A0': LMA['Z1'], 'P0': LMA['Z2'], 'P1': LMA['Z3'], 'A': LMA['Z4'], "A'": LMA['Y1'], 'A"': LMA['Z5'], "E'": LMA['Z6'], 'E"': LMA['Z7'],
         'Q': PL('P', 8), 'Q1': PL('P', 9), 'E': 'E', 'L': LG, 'R': 'R', 'D': 'D', 'P': PV, 'Y': YF, 'U': UC, 'G': ACC(NLG), 'B': B37}
_GA, _GC = split_imp(STMTS12['tmiacl'])
GTREE = tsub(parse_conj(_GA), GM_AP)
GCONCL = tsub_text(_GC, GM_AP)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in _fl if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
P0EQ = [t for t in _fl if t.startswith('( %s ` 0 ) = ' % PV)][0]
PNEQ = [t for t in _fl if t.startswith('( %s ` %s ) = ' % (PV, NLG))][0]
SUMLE = [t for t in _fl if t.startswith('sum_ ')][0]
HOARE_YJ = PERB.split(' /\\ ', 1)[1][:-2].rsplit(' , ', 1)[0] + ' , %s >.' % YJ('j')
add12('tmiapai', (PSI_T, 'j e. ( 0 ..^ %s )' % NLG), HOARE_YJ)
add12('tmiapat', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FTY, FCOL, P0EQ, PNEQ))
APFLAG = 'if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o )' % ANDW(PT_I)
APAC = '( %s + ( ( 2 x. %s ) + 6 ) )' % (UC, TB37)
CONCL_APAL = TRI(CS('apa'), CLN('E', NFL(APFLAG), UP('D', '5', 'R')), APAC)
add12('tmiapal', PSI_T, CONCL_APAL)
DATA_AP = ((STKD('D'), 'W e. Word NN0', 'B e. NN0'), (RALB('W', 'B'), WG('X')), DEQ(4, ENCL('W', 'X')))
TREE_AP = TREE0('ap', DATA_AP)
CONCL_AP = TRI(CS('ap'), CLN('E', NFL('( 1st ` ( AllPrimeTD ` W ) )'), 'D'), '( ( %s + 1 ) x. ( 4 x. %s ) )' % (APC2, TB37))
add12('tmiap', TREE_AP, CONCL_AP)


class Apa(Base):
    def __init__(self, w, ph, T, fname='apa'):
        c0 = Ctx(w, ph, T)
        ww, bn, rw = c0['W e. Word NN0'], c0['B e. NN0'], c0[WG('R')]
        Base.__init__(self, w, ph, T, N8, fname, {'5': (ENCL('W', 'R'), enclg(w, ph, 'W', ww, 'R', rw))})
        s = w.s
        self.ww, self.bn, self.rw = ww, bn, rw
        self.lgw = s([ww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([ww, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = ( # ` W ) )' % (ph, NLG))
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
        self.nlg = s([self.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
        self.cl = Closure(w, ph, {'B': ('NN0', bn)})
        self.cl.leaf('( # ` W )', 'NN0', self.nw)
        self.cl.leaf(NLG, 'NN0', self.nlg)
        self.cl.leaf(TB('B'), 'NN0', tmbn(w, ph, 'B', bn))
        self.b37n = self.cl.mem(B37, 'NN0')
        self.cl.leaf(TB37, 'NN0', tmbn(w, ph, B37, self.b37n))
        self.d1 = self.S0.vals['1'][2]
        # 1 < 2 ^ ( 3 B + 7 ) and 2 ^ B <_ 2 ^ ( 3 B + 7 )
        self.cl.atom('( 2 ^ B )'); self.cl.atom('( 2 ^ %s )' % B37)
        u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
        self.b37lt = s([u2, self.b37n, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ph, B37, B37))
        u = s([s([s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), s([self.b37n], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, B37)),
                 linarith(w, ph, [self.cl.ge0('B')], 'B <_ %s' % B37, closure=self.cl)], '3jca',
                '( %s -> ( B e. ZZ /\\ %s e. ZZ /\\ B <_ %s ) )' % (ph, B37, B37)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` B ) )' % (ph, B37))
        self.pble = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u, w.inst('leexp2a')], 'syl3anc',
                      '( %s -> ( 2 ^ B ) <_ ( 2 ^ %s ) )' % (ph, B37))
        self.tbmono = s([bn, self.b37n, linarith(w, ph, [self.cl.ge0('B')], 'B <_ %s' % B37, closure=self.cl), w.inst('tmbmono')], 'syl3anc',
                        '( %s -> %s <_ %s )' % (ph, TB('B'), TB37))
        self.tb1 = s([s([self.b37n, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB37)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB37))

    def accn(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        a = s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ACC(k)))
        cond = 'A. i e. ( 0 ..^ %s ) %s' % (k, PT_I('i'))
        pt, pn = '( %s /\\ %s )' % (ph, cond), '( %s /\\ -. %s )' % (ph, cond)
        l1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = 1 )' % (pt, ACC(k))), closed(w, pt, '1le1', '1 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pt, ACC(k)))
        l2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = 0 )' % (pn, ACC(k))), closed(w, pn, '0le1', '0 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pn, ACC(k)))
        return a, s([l1, l2], 'pm2.61dan', '( %s -> %s <_ 1 )' % (ph, ACC(k)))

    def acclt(self, k):
        """( ph -> ACC( k ) < 2 ^ ( 3 B + 7 ) )"""
        an, le = self.accn(k)
        cl = Closure(self.w, self.ph, {'B': ('NN0', self.bn)})
        cl.leaf(ACC(k), 'NN0', an)
        cl.atom('( 2 ^ %s )' % B37)
        return an, linarith(self.w, self.ph, [le, self.b37lt, cl.ge0('B')], '%s < ( 2 ^ %s )' % (ACC(k), B37), closure=cl)

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        an, _ = self.accn(k)
        g1 = self.g(E1(k), ewg_(w, ph, ACC(k), an, DK(1), self.d1))
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g5 = self.g(C5(k), wgcat(w, ph, EB(k), 'R', eb, self.rw))
        return self.S0.upd('1', E1(k), g1).upd('5', C5(k), g5)


def tmiapai():
    lab = 'tmiapai'
    T = numtree((PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    ph = cj(T)
    w = W(lab, 'One entry of Lean\'s ` allPrimeTDF ` loop at the machine ( ` apBody_runs ` ): along the family of the accumulator, '
               '` isPrimeTDF 5 2 3 6 0 1 ` (~ tmiptb ) on the entry at the top of 5, ` accAnd ` (~ tmiaca ), ` dropNum 5 ` '
               '(~ tmidropb ).')
    s = w.s
    B = Apa(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    jj = c['j e. ( 0 ..^ %s )' % NLG]
    jW = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` W ) ) )' % (ph, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` W ) ) )' % ph)
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    J1 = '( j + 1 )'
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (ph, J1, DOM))
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % ph)
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j'))
    PTX = '( %s ` j )' % PV
    WJ = '( W ` j )'
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % ph), jW, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (ph, LG, WJ))
    wjn = s([B.ww, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WJ))
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = s([lgj, encw(w, ph, WJ, wjn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG))
    ca1 = s([egj, g4, B.rw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, B.rw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ R ) = ( <" 4 "> ++ %s ) )' % (ph, EB(J1), C5(J1)))
    r1 = s([s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) )' % (ph, C5('j'), LG, EB(J1))), ca1], 'eqtrd',
           '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ph, C5('j'), LG, EB(J1)))
    V5 = EWg(WJ, C5(J1))
    r2 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) = %s )' % (ph, LG, EB(J1), V5))
    iv = s([SJ.vals['5'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, C5('j'), V5))], 'eqtrd', '( %s -> ( %s ` 5 ) = %s )' % (ph, PTX, V5))
    g51 = B.g(C5(J1), wgcat(w, ph, EB(J1), 'R', eb1, B.rw))
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ ( # ` W ) ) )' % ph), jW, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran W )' % (ph, WJ))
    wjlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ B ) <-> %s < ( 2 ^ B ) ) )' % (WJ, WJ)), wr, c[RALB('W', 'B')]], 'rspcdva', '( %s -> %s < ( 2 ^ B ) )' % (ph, WJ))
    accj, acclt = B.acclt('j')
    cl.leaf(ACC('j'), 'NN0', accj)
    B.deep('apa', 0)
    v2 = dict(SJ.vals)
    v2['5'] = (V5, iv, B.g(V5, ewg_(w, ph, WJ, wjn, C5(J1), g51)))
    SJ2 = Stacks(w, ph, mk, SJ.D, SJ.memb, SJ.ne, v2)
    R = B.run(SJ2)
    lm_apb = FRAGS['apb'].lmap(PL('P', 7), LMA['Z5'])
    P7 = PL('P', 7)
    # 1. isPrimeTDF 5 2 3 6 0 1
    B.call(R, 'tmiptb', {'K': '5', 'J': '2', 'I': '3', "I'": '6', 'I"': '0', 'I0': '1', 'F': WJ, 'N': 'B', 'X': C5(J1), 'P': PL(P7, 0), 'E': lm_apb['Y2']},
           {'%s e. NN0' % WJ: wjn, '%s < ( 2 ^ B )' % WJ: wjlt, WG(C5(J1)): g51}, [])
    O = IP1(WJ)
    IFO = 'if ( %s = 1o , %s , 0 )' % (O, ACC('j'))
    ifon = s([accj, closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, IFO))
    EI = EWg(IFO, DK(1))
    B.call(R, 'tmiaca', {'A': ACC('j'), 'B': B37, 'X': DK(1), 'O': O, 'P': PL(P7, 1), 'E': lm_apb['Y3']},
           {'%s e. NN0' % ACC('j'): accj, '%s e. NN0' % B37: B.b37n, '%s < ( 2 ^ %s )' % (ACC('j'), B37): acclt, WG(DK(1)): B.d1},
           [('1', EI, B.g(EI, ewg_(w, ph, IFO, ifon, DK(1), B.d1)))])
    Son, old = expose(w, ph, B, R, '5')
    B.call(R, 'tmidropb', {'K': '5', 'F': WJ, 'N': 'B', 'X': C5(J1), 'P': PL(P7, 2), 'E': LMA['Z5']},
           {'%s e. NN0' % WJ: wjn, '%s < ( 2 ^ B )' % WJ: wjlt, WG(C5(J1)): g51}, [('5', C5(J1), g51)], on=(Son, old))
    e, nrm, out2 = renorm(w, ph, B, R, [('1', E1('j')), ('5', C5('j'))], N8, PT=PTX, pv=pvj)
    assert out2 == [('1', EI), ('5', C5(J1))], out2
    jn0 = s([jn, w.inst('elnn0uz')], 'sylib', '( %s -> j e. ( ZZ>= ` 0 ) )' % ph)
    ast = acc_step(w, ph, jn, jn0, PT_I, '%s = 1o' % O, s([], 'biid', '( %s <-> %s )' % (PT(WJ), PT(WJ))) if False else
                   s([s([], 'biid', '( %s <-> %s )' % (PT(WJ), PT(WJ)))], 'a1i', '( %s -> ( %s <-> %s ) )' % (ph, PT(WJ), PT(WJ))))
    r_, nrm2 = w.rewrite(nrm, {IFO: (ACC(J1), ast)}, ph)
    assert nrm2 == PB(J1), '\n%s\n%s' % (nrm2, PB(J1))
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1))
    D0 = triple_D(R.cur)
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, D0, PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LMA['Z5'], S, deq, D0, '( %s ` %s )' % (PV, J1)))
    ipc = s([wjn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (ph, WJ))
    cl.leaf(IP2(WJ), 'NN0', s([ipc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, IP2(WJ))))
    le = linarith(w, ph, [cl.ge0(IP2(WJ)), cl.ge0(TB37)], '%s <_ %s' % (n, YJ('j')), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, YJ('j'), cl.mem(YJ('j'), 'NN0'), le)
    assert TRI(C, D, YJ('j')) == HOARE_YJ, '\n%s\n%s' % (TRI(C, D, YJ('j')), HOARE_YJ)
    finish(w, st, lab)
    return w.run()


def tmiapat():
    lab = 'tmiapat'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` allPrimeTDF ` loop at the machine: the family of the accumulator is a stack family '
               'whose 5 column is the rest of the copied list, at 0 it is the stacks with the accumulator ` 1 ` pushed, at the '
               'end the accumulator is the conjunction of the primality tests and the list\'s ` bra ` remains.')
    s = w.s
    B = Apa(w, ph, T)
    c, mk = B.c, B.mk
    fam = c['%s = %s' % (PV, PF)]
    ph0t = (TREE_APA, NUMS)
    ph0 = cj(ph0t)
    TK = (ph0t, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Apa(w, pk, TK)
    Sk = Bk.pbst('k')
    fm = s([Sk.memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    j0 = s([c[cj(TREE_APA)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fm2 = s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)), fm2],
            'mpbird', '( %s -> %s )' % (ph, FTY))
    TJ = (T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Apa(w, pj, TJ)
    jz = Bj.c['j e. %s' % DOM]
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', jz, Bj.pbst('j'))
    col = s([SJ.vals['5'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    z0 = s([B.nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0'))
    a0 = s([s([s([], 'ral0', 'A. i e. (/) %s' % PT_I('i')), s([s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'raleqi',
                                                          '( A. i e. ( 0 ..^ 0 ) %s <-> A. i e. (/) %s )' % (PT_I('i'), PT_I('i')))], 'mpbir',
              'A. i e. ( 0 ..^ 0 ) %s' % PT_I('i'))], 'iftruei', '%s = 1' % ACC('0'))
    e1 = s([s([s([a0], 'a1i', '( %s -> %s = 1 )' % (ph, ACC('0')))], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` 1 ) )' % (ph, ACC('0')))], 'oveq1d',
           '( %s -> %s = %s )' % (ph, E1('0'), EWg('1', DK(1))))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le_ = s([B.ww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` W ) = ( encListB ` %s ) )' % (ph, LG))
    e5 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le_], 'eqtr4d', '( %s -> %s = ( encList ` W ) )' % (ph, EB('0')))],
           'oveq1d', '( %s -> %s = %s )' % (ph, C5('0'), ENCL('W', 'R')))
    e5b = s([e5, s([c[DEQ(5, ENCL('W', 'R'))]], 'eqcomd', '( %s -> %s = ( D ` 5 ) )' % (ph, ENCL('W', 'R')))], 'eqtrd', '( %s -> %s = ( D ` 5 ) )' % (ph, C5('0')))
    rr, xx = w.rewrite(PB('0'), {E1('0'): (EWg('1', DK(1)), e1), C5('0'): ('( D ` 5 )', e5b)}, ph)
    assert xx == UPS('D', ('1', EWg('1', DK(1))), ('5', DK(5))), xx
    B.g(EWg('1', DK(1)), ewg_(w, ph, '1', closed(w, ph, '1nn0', '1 e. NN0'), DK(1), B.d1))
    nst, outn = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, [('1', EWg('1', DK(1))), ('5', DK(5))], B.gam, N8)
    assert outn == [('1', EWg('1', DK(1)))], outn
    p0 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx)), nst], 'eqtrd', '( %s -> %s )' % (ph, P0EQ))
    nz = s([B.nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    pvN, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, NLG, nz, B.pbst(NLG))
    DR = '( %s substr <. %s , %s >. )' % (LG, NLG, NLG)
    e2 = s([s([closed(w, ph, 'swrd00', '%s = (/)' % DR)], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (ph, DR)),
            closed(w, ph, 'tm2lencb0', '( encListB ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encListB ` %s ) = <" 2 "> )' % (ph, DR))
    e5n = s([e2], 'oveq1d', '( %s -> %s = ( <" 2 "> ++ R ) )' % (ph, C5(NLG)))
    rN, xN = w.rewrite(PB(NLG), {C5(NLG): ('( <" 2 "> ++ R )', e5n)}, ph)
    pn = s([pvN, rN], 'eqtrd', '( %s -> %s )' % (ph, PNEQ))
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([p0, pn], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ph, FTY, FCOL, P0EQ, PNEQ))
    finish(w, st, lab)
    return w.run()


def tmiapal():
    lab = 'tmiapal'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` accLoopF apBody ` at the machine: ~ tmiacl at the family of the accumulator ( ` P\' ` a letter; the '
               'entries by ~ tmiapai , the frame by ~ tmiapat , the entries\' budget summed by ~ t12apcost ); the flag is the '
               'conjunction of the primality tests over the list, the list\'s ` bra ` is gone from 5.')
    s = w.s
    B = Apa(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    ex = dict(B.ex)
    B.deep('apa', 0)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmiapat', STMTS12['tmiapat']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))
    ex[FTY] = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    ex[P0EQ] = s([a2], 'simpld', '( %s -> %s )' % (ph, P0EQ))
    ex[PNEQ] = s([a2], 'simprd', '( %s -> %s )' % (ph, PNEQ))
    # PER: the body theorem with ( YF ` j ) = YJ( j ) under ( PSI /\ j e. ( 0 ..^ NLG ) )
    def yjeq(pj, jn, ycn):
        cg, new = w.congr(YJ('j'), {'j': 'j'}, 'j = j', {'j': s([], 'id', '( j = j -> j = j )')}) if False else (None, None)
        return s([jn, ycn, s([w.congr(YJ('i'), {'i': 'j'}, 'i = j', {'i': s([], 'id', '( i = j -> i = j )')})[0], s([], 'eqid', '%s = %s' % (YF, YF))], 'fvmptg',
                             '( ( j e. NN0 /\\ %s e. NN0 ) -> ( %s ` j ) = %s )' % (YJ('j'), YF, YJ('j')))], 'syl2anc',
                 '( %s -> ( %s ` j ) = %s )' % (pj, YF, YJ('j')))

    def yjn_of(pj, T_):
        cj_ = Ctx(w, pj, T_)
        bnj, wwj = cj_['B e. NN0'], cj_['W e. Word NN0']
        clj = Closure(w, pj, {'B': ('NN0', bnj)})
        clj.leaf(TB('B'), 'NN0', tmbn(w, pj, 'B', bnj))
        clj.leaf(TB37, 'NN0', tmbn(w, pj, B37, clj.mem(B37, 'NN0')))
        jj_ = cj_['j e. ( 0 ..^ %s )' % NLG] if 'j e. ( 0 ..^ %s )' % NLG in cj_.all() else None
        return clj, wwj, jj_
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (PSI, NLG)
    bj = s([], 'tmiapai', STMTS12['tmiapai'])
    clj, wwj, jj_ = yjn_of(pj, (PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    jn = s([jj_, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
    lgj = s([wwj, closed(w, pj, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = ( # ` W ) )' % (pj, NLG))
    jW = s([jj_, s([lgj], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` W ) ) )' % (pj, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` W ) ) )' % pj)
    wjn = s([wwj, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` j ) e. NN0 )' % pj)
    clj.leaf(IP2('( W ` j )'), 'NN0', s([s([wjn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` ( W ` j ) ) e. ( 2o X. NN0 ) )' % pj), w.inst('xp2nd')], 'syl',
                                       '( %s -> %s e. NN0 )' % (pj, IP2('( W ` j )'))))
    ycn = clj.mem(YJ('j'), 'NN0')
    yj = yjeq(pj, jn, ycn)
    Cb, Db, nb = triple_parts(HOARE_YJ)
    tb, _, _, _ = hrrw(w, pj, bj, Cb, Db, nb, neq=s([yj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (pj, YJ('j'), YF)))
    yjn = s([yj, ycn], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (pj, YF))
    perb = s([yjn, tb], 'jca', '( %s -> %s )' % (pj, PERB))
    ex[PER] = lift_from(w, PSI, ph, s([perb], 'ralrimiva', '( %s -> %s )' % (PSI, PER)))
    # the sum: sum_ j ( ( YF ` j ) + 2 ) = TB37 x. sum_ j ( c_j + 1 ) + NLG x. ( KC + 2 ) = UC (with NLG = # W)
    pj2 = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLG)
    clj2, wwj2, jj2 = yjn_of(pj2, (T, 'j e. ( 0 ..^ %s )' % NLG))
    jn2 = s([jj2, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj2)
    lgj2 = s([wwj2, closed(w, pj2, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = ( # ` W ) )' % (pj2, NLG))
    jW2 = s([jj2, s([lgj2], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` W ) ) )' % (pj2, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` W ) ) )' % pj2)
    wjn2 = s([wwj2, jW2, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` j ) e. NN0 )' % pj2)
    CJ1 = '( %s + 1 )' % IP2('( W ` j )')
    cj1n = s([s([s([wjn2, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` ( W ` j ) ) e. ( 2o X. NN0 ) )' % pj2), w.inst('xp2nd')], 'syl',
               '( %s -> %s e. NN0 )' % (pj2, IP2('( W ` j )'))), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pj2, CJ1))
    clj2.leaf(IP2('( W ` j )'), 'NN0', s([cj1n], 'id', '') if False else s([s([wjn2, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` ( W ` j ) ) e. ( 2o X. NN0 ) )' % pj2), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pj2, IP2('( W ` j )'))))
    ycn2 = clj2.mem(YJ('j'), 'NN0')
    yj2 = yjeq(pj2, jn2, ycn2)
    # ( ( YF ` j ) + 2 ) = ( ( TB37 x. c_j+1 ) + ( KC + 2 ) )
    TERM = '( ( %s x. %s ) + ( %s + 2 ) )' % (TB37, CJ1, KC)
    te = s([s([yj2], 'oveq1d', '( %s -> ( ( %s ` j ) + 2 ) = ( %s + 2 ) )' % (pj2, YF, YJ('j'))), lineq(w, pj2, '( %s + 2 )' % YJ('j'), TERM, closure=clj2)], 'eqtrd',
           '( %s -> ( ( %s ` j ) + 2 ) = %s )' % (pj2, YF, TERM))
    SJ_ = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NLG, YF)
    A_ = '( 0 ..^ %s )' % NLG
    se = s([te], 'sumeq2dv', '( %s -> %s = sum_ j e. %s %s )' % (ph, SJ_, A_, TERM))
    fzf = s([s([], 'fzofi', '%s e. Fin' % A_)], 'a1i', '( %s -> %s e. Fin )' % (ph, A_))
    pcc = s([s([cl.mem(TB37, 'CC')], 'adantr', '( %s -> %s e. CC )' % (pj2, TB37)), s([cj1n], 'nn0cnd', '( %s -> %s e. CC )' % (pj2, CJ1))], 'mulcld',
            '( %s -> ( %s x. %s ) e. CC )' % (pj2, TB37, CJ1))
    kcc = s([cl.mem('( %s + 2 )' % KC, 'CC')], 'adantr', '( %s -> ( %s + 2 ) e. CC )' % (pj2, KC))
    SA = 'sum_ j e. %s ( %s x. %s )' % (A_, TB37, CJ1)
    SB = 'sum_ j e. %s ( %s + 2 )' % (A_, KC)
    e3 = s([fzf, pcc, kcc], 'fsumadd', '( %s -> sum_ j e. %s %s = ( %s + %s ) )' % (ph, A_, TERM, SA, SB))
    SC = 'sum_ j e. %s %s' % (A_, CJ1)
    e4 = s([fzf, s([cj1n], 'nn0cnd', '( %s -> %s e. CC )' % (pj2, CJ1)), cl.mem(TB37, 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = %s )' % (ph, TB37, SC, SA))
    e5 = s([fzf, cl.mem('( %s + 2 )' % KC, 'CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> %s = ( ( # ` %s ) x. ( %s + 2 ) ) )' % (ph, SB, A_, KC))
    hf = s([s([B.nlg, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, A_, NLG))], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( %s + 2 ) ) = ( %s x. ( %s + 2 ) ) )' % (ph, A_, KC, NLG, KC))
    # SC = sum over ( 0 ..^ # W ) = APC2 (t12apcost)
    sce = s([s([B.lg], 'oveq2d', '( %s -> %s = ( 0 ..^ ( # ` W ) ) )' % (ph, A_))], 'sumeq1d', '( %s -> %s = sum_ j e. ( 0 ..^ ( # ` W ) ) %s )' % (ph, SC, CJ1))
    apc = s([B.ww, w.inst('t12apcost')], 'syl', '( %s -> %s = sum_ j e. ( 0 ..^ ( # ` W ) ) %s )' % (ph, APC2, CJ1))
    sc2 = s([sce, s([apc], 'eqcomd', '( %s -> sum_ j e. ( 0 ..^ ( # ` W ) ) %s = %s )' % (ph, CJ1, APC2))], 'eqtrd', '( %s -> %s = %s )' % (ph, SC, APC2))
    ea = s([s([e4], 'eqcomd', '( %s -> %s = ( %s x. %s ) )' % (ph, SA, TB37, SC)), s([sc2], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ph, TB37, SC, TB37, APC2))],
           'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (ph, SA, TB37, APC2))
    eb = s([e5, hf, s([B.lg], 'oveq1d', '( %s -> ( %s x. ( %s + 2 ) ) = ( %s x. ( %s + 2 ) ) )' % (ph, NLG, KC, NW, KC))], '3eqtrd',
           '( %s -> %s = ( %s x. ( %s + 2 ) ) )' % (ph, SB, NW, KC))
    seq_ = s([se, e3, s([ea, eb], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (ph, SA, SB, UC))], '3eqtrd', '( %s -> %s = %s )' % (ph, SJ_, UC))
    apcn = s([s([B.ww, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, APC2))
    cl.leaf(APC2, 'NN0', apcn)
    sumr = s([s([seq_, cl.mem(UC, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, SJ_))], 'nn0red', '( %s -> %s e. RR )' % (ph, SJ_))
    ex[SUMLE] = s([sumr, seq_], 'eqled', '( %s -> %s )' % (ph, SUMLE))
    accN, accltN = B.acclt(NLG)
    ex['%s e. NN0' % ACC(NLG)] = accN
    ex['%s < ( 2 ^ %s )' % (ACC(NLG), B37)] = accltN
    ex['%s e. NN0' % B37] = B.b37n
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex['%s e. NN0' % UC] = cl.mem(UC, 'NN0')
    ex[WG('R')] = B.rw
    st = Bld(w, ph, c, ex)(GTREE)
    st2 = s([st, w.inst('tmiacl')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    C0, D0, n0 = triple_parts(GCONCL)
    rd, D1 = w.rewrite(D0, {NLG: ('( # ` W )', B.lg)}, ph)
    t, C, D, n = hrrw(w, ph, st2, C0, D0, n0, deq=rd)
    assert TRI(C, D, n) == CONCL_APAL, '\n%s\n%s' % (TRI(C, D, n), CONCL_APAL)
    finish(w, t, lab)
    return w.run()


def tmiap():
    lab = 'tmiap'
    T = numtree(TREE_AP)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` allPrimeTDF_runs ` at the machine: ` copyList 4 5 2 3 ` (~ tmilcpyb ) then the accumulator loop '
               '(~ tmiapal ); every stack restored, the flag ` ( 1st ( AllPrimeTD S ) ) ` (~ t12apfst ), within '
               '` ( ( allPrimeTD S ).2 + 1 ) 4 B ( 3 b + 7 ) ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    ww, bn, xw = c0['W e. Word NN0'], c0['B e. NN0'], c0[WG('X')]
    B = Base(w, ph, T, N8, 'ap', {'4': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw))})
    c, mk = B.c, B.mk
    g = lambda k: B.S0.vals[k][2]
    LM = FRAGS['ap'].lmap()
    R = B.run()
    V5 = ENCL('W', DK(5))
    B.call(R, 'tmilcpyb', {'K': '4', 'J': '5', 'I': '2', "I'": '3', 'L': 'W', 'R': 'X', 'B': 'B', 'P': PL('P', 0), 'E': LM['Y2']},
           {}, [('5', V5, B.g(V5, enclg(w, ph, 'W', ww, DK(5), g('5'))))])
    PFi = tsub_text(PF, {'D': R.S.D, 'R': DK(5)})
    B.call(R, 'tmiapal', {'W': 'W', 'B': 'B', 'R': DK(5), PV: PFi, 'P': PL('P', 1), 'E': 'E'},
           {WG(DK(5)): g('5'), '%s = %s' % (PFi, PFi): s([s([], 'eqid', '%s = %s' % (PFi, PFi))], 'a1i', '( %s -> %s = %s )' % (ph, PFi, PFi))},
           [('5', DK(5), g('5'))])
    cur, out = R.normalize(N8)
    assert out == [], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the flag
    fl = s([ww, w.inst('t12apfst')], 'syl', '( %s -> ( 1st ` ( AllPrimeTD ` W ) ) = %s )' % (ph, APFLAG))
    t, C, D, n = cls_to(w, ph, (t, C, D, n), APFLAG, '( 1st ` ( AllPrimeTD ` W ) )', s([fl], 'eqcomd', '( %s -> %s = ( 1st ` ( AllPrimeTD ` W ) ) )' % (ph, APFLAG)))
    cl = Closure(w, ph, {'B': ('NN0', bn)})
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl.leaf('( # ` W )', 'NN0', nw)
    cl.leaf(TB('B'), 'NN0', tmbn(w, ph, 'B', bn))
    b37n = cl.mem(B37, 'NN0')
    cl.leaf(TB37, 'NN0', tmbn(w, ph, B37, b37n))
    apcn = s([s([ww, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, APC2))
    cl.leaf(APC2, 'NN0', apcn)
    # # W <_ ( 2nd AllPrimeTD W ) : every term of the sum is at least 1
    apc = s([ww, w.inst('t12apcost')], 'syl', '( %s -> %s = %s )' % (ph, APC2, SUMC))
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NW)
    wjn = s([s([ww], 'adantr', '( %s -> W e. Word NN0 )' % pj), s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NW)), w.inst('wrdsymbcl')], 'syl2anc',
            '( %s -> ( W ` j ) e. NN0 )' % pj)
    CJ1 = '( %s + 1 )' % IP2('( W ` j )')
    c2n = s([s([wjn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` ( W ` j ) ) e. ( 2o X. NN0 ) )' % pj), w.inst('xp2nd')], 'syl',
            '( %s -> %s e. NN0 )' % (pj, IP2('( W ` j )')))
    clj = Closure(w, pj, {})
    clj.leaf(IP2('( W ` j )'), 'NN0', c2n)
    one = linarith(w, pj, [clj.ge0(IP2('( W ` j )'))], '1 <_ %s' % CJ1, closure=clj)
    fzf = s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NW)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NW))
    S1 = 'sum_ j e. ( 0 ..^ %s ) 1' % NW
    ge = s([fzf, s([closed(w, pj, '1re', '1 e. RR')], 'id', '') if False else closed(w, pj, '1re', '1 e. RR'), s([c2n, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pj, CJ1)),
            one], 'fsumle', '( %s -> %s <_ %s )' % (ph, S1, SUMC)) if False else None
    ge = s([fzf, closed(w, pj, '1re', '1 e. RR'), s([s([c2n, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pj, CJ1))], 'nn0red', '( %s -> %s e. RR )' % (pj, CJ1)), one],
           'fsumle', '( %s -> %s <_ %s )' % (ph, S1, SUMC))
    s1 = s([s([fzf, closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> %s = ( ( # ` ( 0 ..^ %s ) ) x. 1 ) )' % (ph, S1, NW)),
            s([s([nw, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (ph, NW, NW))], 'oveq1d', '( %s -> ( ( # ` ( 0 ..^ %s ) ) x. 1 ) = ( %s x. 1 ) )' % (ph, NW, NW)),
            s([cl.mem(NW, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (ph, NW, NW))], '3eqtrd', '( %s -> %s = %s )' % (ph, S1, NW))
    nwle = s([s([s1], 'eqcomd', '( %s -> %s = %s )' % (ph, NW, S1)), s([ge, s([apc], 'eqcomd', '( %s -> %s = %s )' % (ph, SUMC, APC2))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, S1, APC2))],
             'eqbrtrd', '( %s -> %s <_ %s )' % (ph, NW, APC2))
    mono = s([bn, b37n, linarith(w, ph, [cl.ge0('B')], 'B <_ %s' % B37, closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB('B'), TB37))
    # 27 TMB ( B + 1 ) = TMB ( 3 B + 7 ) and TMB B <_ TMB ( B + 1 )
    t34 = s([cl.mem('( B + 1 )', 'NN0'), w.inst('tplb34')], 'syl', '( %s -> ( TMB ` ( ( 3 x. ( B + 1 ) ) + 4 ) ) = ( ; 2 7 x. ( TMB ` ( B + 1 ) ) ) )' % ph)
    e37 = lineq(w, ph, '( ( 3 x. ( B + 1 ) ) + 4 )', B37, closure=cl)
    t37 = s([s([e37], 'fveq2d', '( %s -> ( TMB ` ( ( 3 x. ( B + 1 ) ) + 4 ) ) = %s )' % (ph, TB37)), t34], 'eqtr3d', '( %s -> %s = ( ; 2 7 x. ( TMB ` ( B + 1 ) ) ) )' % (ph, TB37))
    cl.leaf('( TMB ` ( B + 1 ) )', 'NN0', tmbn(w, ph, '( B + 1 )', cl.mem('( B + 1 )', 'NN0')))
    mono1 = s([bn, cl.mem('( B + 1 )', 'NN0'), linarith(w, ph, [], 'B <_ ( B + 1 )', closure=cl), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ ( TMB ` ( B + 1 ) ) )' % (ph, TB('B')))
    tb8 = s([bn, closed(w, ph, '8nn0', '8 e. NN0'), s([num.le_lit(w, '8', '; 6 4')], 'a1i', '( %s -> 8 <_ ; 6 4 )' % ph), w.inst('tmblin')], 'syl3anc',
            '( %s -> ( 8 x. ( B + 2 ) ) <_ %s )' % (ph, TB('B')))
    BND = triple_parts(CONCL_AP)[2]
    le = linarith(w, ph, [mono, t37, mono1, tb8, nwle, cl.ge0('B'), cl.ge0(NW), cl.ge0(APC2)], '%s <_ %s' % (n, BND), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
