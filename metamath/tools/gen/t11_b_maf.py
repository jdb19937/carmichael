"""T11: Lean's ` mulAllF x y r s t ` at ` 6 3 5 0 1 ` (PrimList.lean ` mulAllF_le_B ` ) on TMImaf: ~ tm2fmla at the
family of ` MulAllInv ` .

  tmimafs   the open-list word one entry on: ` encList ( rev ( mulAll q ( l.take ( j + 1 ) ) ) ) ++ Z ` is the entry
            ` l[j] * q ` pushed on ` encList ( rev ( mulAll q ( l.take j ) ) ) ++ Z `
  tmimafi   one entry of the ` forEntries ` loop: ` dup 3 1 0 ; mulC 6 1 5 0 3 ` at ` MulAllInv ` ( ` mulAllBody_runs ` )
  tmimaft   the frame: the family's typing and ` x ` column, its value at 0 after ` pushSym 5 bra ` , and the closing
            ` revList 5 6 0 `
  tmimafl   ~ tm2fmla assembled ( P' a letter)
  tmimafb   mulAllF_le_B

    MM_DB=sorties/t11.mm python3 tools/gen/t11_b_maf.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, nlinarith, lineq
from t7lib import mval
from t10_e_doa import lift_from
import num

SEL = sys.argv[1:]
LG = '( encNatGam o. W )'
NLG = '( # ` %s )' % LG
DOM = '( 0 ... %s )' % NLG
EB = lambda k: '( encListB ` ( %s substr <. %s , %s >. ) )' % (LG, k, NLG)
C6 = lambda k: '( %s ++ X )' % EB(k)
MP = lambda k: '( 1st ` ( F MulAll ( W prefix %s ) ) )' % k
RM = lambda k: '( reverse ` %s )' % MP(k)
C5 = lambda k: ENCL(RM(k), DK(5))
PB = lambda k: UPS('D', ('5', C5(k)), ('6', C6(k)))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
PV = "P'"
PSI_T = (TREE_MAF, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
YB = '( 2 x. ( TMB ` N ) )'
N2 = '( 2 x. N )'
UB = '( ( ( # ` W ) + 1 ) x. ( TMB ` %s ) )' % N2
MAW = '( 1st ` %s )' % MA_
DFIN = UP('D', '6', ENCL(MAW, 'X'))
LMP = FRAGS['maf'].lmap()
GM = {'P0': LMP['Z1'], 'P1': LMP['Z2'], 'A': LMP['Z3'], "A'": LMP['Y1'], 'A"': LMP['Z4'], 'E': LMP['Z5'], "E'": LMP['Y2'],
      'E"': 'E', 'K': '6', 'I': '5', 'F': RDBRA, 'C': CNFL, 'F"': PID, 'N': S, "N'": S, 'N"': S, 'L': LG, 'R': 'X',
      'Y': YB, 'P': PV, 'D': 'D', "D'": DFIN, 'U': UB}
_GA, _GC = split_imp(stmt('tm2fmla'))
GTREE = tsub(parse_conj(_GA), GM)
GCONCL = tsub_text(_GC, GM)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in _fl if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
P0EQ = [t for t in _fl if t.startswith('( %s ` 0 ) = ' % PV)][0]
REVT = [t for t in _fl if t.startswith('( { ( inl ` %s ) }' % LMP['Y2'])][0]

# the open-list word lemma
ST_S = ("( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ ( J e. ( 0 ..^ ( # ` W ) ) /\\ Z e. Word Gamma' ) ) -> "
        "( ( encList ` ( reverse ` ( 1st ` ( F MulAll ( W prefix ( J + 1 ) ) ) ) ) ) ++ Z ) = "
        "( ( encNatGam ` ( ( W ` J ) x. F ) ) ++ ( <\" 4 \"> ++ ( ( encList ` ( reverse ` ( 1st ` ( F MulAll ( W prefix J ) ) ) ) ) ++ Z ) ) ) )")
STMTS11['tmimafs'] = ST_S
ORDER11.insert(0, 'tmimafs')
add11('tmimafi', (PSI_T, 'j e. ( 0 ..^ %s )' % NLG), PERB)
add11('tmimaft', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FTY, FCOL, P0EQ, REVT))
add11('tmimafl', PSI_T, GCONCL)
for _l in ('tmimafi', 'tmimaft', 'tmimafl'):
    ORDER11.remove(_l)
    ORDER11.insert(ORDER11.index('tmimafb'), _l)


class Maf(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        ww, fn, nn = c0['W e. Word NN0'], c0['F e. NN0'], c0['N e. NN0']
        xw, yw = c0[WG('X')], c0[WG('Y')]
        eqs = {'6': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), '3': (EWg('F', 'Y'), ewg_(w, ph, 'F', fn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, 'maf', eqs)
        s = w.s
        self.ww, self.fn, self.nn, self.xw, self.yw = ww, fn, nn, xw, yw
        self.lgw = s([ww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([ww, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc',
                    '( %s -> %s = ( # ` W ) )' % (ph, NLG))
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
        self.cl = Closure(w, ph, {'N': ('NN0', nn), 'F': ('NN0', fn)})
        self.cl.leaf('( # ` W )', 'NN0', self.nw)
        self.d5 = self.S0.vals['5'][2]
        self.kz = {}

    def mpw(self, k):
        """( ph -> MP( k ) e. Word NN0 )"""
        w, ph, s = self.w, self.ph, self.w.s
        pw = s([self.ww, w.inst('pfxcl')], 'syl', '( %s -> ( W prefix %s ) e. Word NN0 )' % (ph, k))
        cl = s([self.fn, pw, w.inst('mulallcl')], 'syl2anc', '( %s -> ( F MulAll ( W prefix %s ) ) e. ( Word NN0 X. NN0 ) )' % (ph, k))
        return s([cl, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, MP(k)))

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        rw = s([self.mpw(k), w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RM(k)))
        g5 = self.g(C5(k), enclg(w, ph, RM(k), rw, DK(5), self.d5))
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g6 = self.g(C6(k), wgcat(w, ph, EB(k), 'X', eb, self.xw))
        return self.S0.upd('5', C5(k), g5).upd('6', C6(k), g6)


def tmimafs():
    lab = 'tmimafs'
    ph = "( ( W e. Word NN0 /\\ F e. NN0 ) /\\ ( J e. ( 0 ..^ ( # ` W ) ) /\\ Z e. Word Gamma' ) )"
    w = W(lab, 'The open list of ` mulAllF ` one entry on (Lean ` mulAllBody_runs ` , ` take_succ ` , ` List.reverse_append ` ): '
               'the reversed products of the first ` j + 1 ` entries are the product ` l[j] * q ` pushed on the reversed '
               'products of the first ` j ` (~ mulallsnoc ).')
    s = w.s
    c = Ctx(w, ph, (('W e. Word NN0', 'F e. NN0'), ('J e. ( 0 ..^ ( # ` W ) )', "Z e. Word Gamma'")))
    ww, fn, jj, zw = c['W e. Word NN0'], c['F e. NN0'], c['J e. ( 0 ..^ ( # ` W ) )'], c["Z e. Word Gamma'"]
    WJ = '( W ` J )'
    wj = s([ww, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WJ))
    P0, P1 = '( W prefix J )', '( W prefix ( J + 1 ) )'
    pf = s([ww, jj, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (ph, P1, P0, WJ))
    pw = s([ww, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, P0))
    M0 = '( 1st ` ( F MulAll %s ) )' % P0
    AQ = '( %s x. F )' % WJ
    sn = s([s([fn, wj], 'jca', '( %s -> ( F e. NN0 /\\ %s e. NN0 ) )' % (ph, WJ)), pw, w.inst('mulallsnoc')], 'syl2anc',
           '( %s -> ( 1st ` ( F MulAll ( %s ++ <" %s "> ) ) ) = ( %s ++ <" %s "> ) )' % (ph, P0, WJ, M0, AQ))
    e1 = s([s([s([pf], 'oveq2d', '( %s -> ( F MulAll %s ) = ( F MulAll ( %s ++ <" %s "> ) ) )' % (ph, P1, P0, WJ))], 'fveq2d',
              '( %s -> %s = ( 1st ` ( F MulAll ( %s ++ <" %s "> ) ) ) )' % (ph, MP('( J + 1 )'), P0, WJ)), sn], 'eqtrd',
           '( %s -> %s = ( %s ++ <" %s "> ) )' % (ph, MP('( J + 1 )'), M0, AQ))
    m0w = s([s([fn, pw, w.inst('mulallcl')], 'syl2anc', '( %s -> ( F MulAll %s ) e. ( Word NN0 X. NN0 ) )' % (ph, P0)), w.inst('xp1st')],
            'syl', '( %s -> %s e. Word NN0 )' % (ph, M0))
    aqn = s([wj, fn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, AQ))
    s1 = s([aqn, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (ph, AQ))
    r1 = s([m0w, s1, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` %s ) ) )'
           % (ph, M0, AQ, AQ, M0))
    r2 = s([s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (AQ, AQ))], 'a1i', '( %s -> ( reverse ` <" %s "> ) = <" %s "> )' % (ph, AQ, AQ))
    RV = '( reverse ` %s )' % M0
    r3 = s([r1, s([r2], 'oveq1d', '( %s -> ( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, AQ, RV, AQ, RV))], 'eqtrd',
           '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( <" %s "> ++ %s ) )' % (ph, M0, AQ, AQ, RV))
    rv = s([s([e1], 'fveq2d', '( %s -> %s = ( reverse ` ( %s ++ <" %s "> ) ) )' % (ph, RM('( J + 1 )'), M0, AQ)), r3], 'eqtrd',
           '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, RM('( J + 1 )'), AQ, RV))
    rvw = s([m0w, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RV))
    ec = s([aqn, rvw, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" %s "> ++ %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )'
           % (ph, AQ, RV, AQ, RV))
    el = s([s([rv], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( <" %s "> ++ %s ) ) )' % (ph, RM('( J + 1 )'), AQ, RV)), ec], 'eqtrd',
           '( %s -> ( encList ` %s ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (ph, RM('( J + 1 )'), AQ, RV))
    EGA = '( encNatGam ` %s )' % AQ
    ELR = '( encList ` %s )' % RV
    ega = s([aqn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EGA))
    elr = s([rvw, w.inst('tm2lenccl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ELR))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    g4 = s([s4, elr, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ %s ) e. Word Gamma' )" % (ph, ELR))
    a1 = s([ega, g4, zw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ Z ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ Z ) ) )'
           % (ph, EGA, ELR, EGA, ELR))
    a2 = s([s4, elr, zw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ Z ) = ( <" 4 "> ++ ( %s ++ Z ) ) )' % (ph, ELR, ELR))
    t1 = s([s([el], 'oveq1d', '( %s -> ( ( encList ` %s ) ++ Z ) = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ Z ) )' % (ph, RM('( J + 1 )'), EGA, ELR)), a1],
           'eqtrd', '( %s -> ( ( encList ` %s ) ++ Z ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ Z ) ) )' % (ph, RM('( J + 1 )'), EGA, ELR))
    w.qed([t1, s([a2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ Z ) ) = ( %s ++ ( <" 4 "> ++ ( %s ++ Z ) ) ) )' % (ph, EGA, ELR, EGA, ELR))],
          'eqtrd', ST_S)
    return w.run()


def tmimafi():
    lab = 'tmimafi'
    T = numtree11((PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    ph = cj(T)
    w = W(lab, 'One entry of Lean\'s ` mulAllF ` loop at the machine ( ` mulAllBody_runs ` ): at the family of ` MulAllInv ` , '
               '` dup 3 1 0 ` (~ tmidupb ) copies ` q ` and ` mulC 6 1 5 0 3 ` (~ tmimulb ) pushes ` l[j] * q ` on the open '
               'list, within ` 2 B b ` steps.')
    B = Maf(w, ph, T)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    jj = c['j e. ( 0 ..^ %s )' % NLG]
    jW = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` W ) ) )' % (ph, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` W ) ) )' % ph)
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    J1 = '( j + 1 )'
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (ph, J1, DOM))
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j'))
    PT = '( %s ` j )' % PV
    # ( PT ` 6 ) = EW( ( W ` j ) , C6( j + 1 ) )
    WJ = '( W ` j )'
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % ph), jW, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (ph, LG, WJ))
    wjn = s([B.ww, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WJ))
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = s([lgj, encw(w, ph, WJ, wjn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG))
    ca1 = s([egj, g4, B.xw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ X ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ X ) ) )' % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, B.xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ X ) = ( <" 4 "> ++ %s ) )' % (ph, EB(J1), C6(J1)))
    r1 = s([s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ X ) )' % (ph, C6('j'), LG, EB(J1))), ca1], 'eqtrd',
           '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ X ) ) )' % (ph, C6('j'), LG, EB(J1)))
    r2 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ X ) ) = %s )' % (ph, LG, EB(J1), EWg(WJ, C6(J1))))
    iv = s([SJ.vals['6'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, C6('j'), EWg(WJ, C6(J1))))], 'eqtrd',
           '( %s -> ( %s ` 6 ) = %s )' % (ph, PT, EWg(WJ, C6(J1))))
    g61 = B.g(C6(J1), wgcat(w, ph, EB(J1), 'X', eb1, B.xw))
    wjn = s([B.ww, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WJ))
    # the numbers
    ral = c[RALB('W', 'N')]
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ ( # ` W ) ) )' % ph), jW, w.inst('fnfvelrn')], 'syl2anc',
           '( %s -> %s e. ran W )' % (ph, WJ))
    wjlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ N ) <-> %s < ( 2 ^ N ) ) )' % (WJ, WJ)), wr, ral], 'rspcdva', '( %s -> %s < ( 2 ^ N ) )' % (ph, WJ))
    AQ = '( %s x. F )' % WJ
    aqn = s([wjn, B.fn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, AQ))
    # the Run
    B.deep('maf', 0)
    v2 = dict(SJ.vals)
    v2['6'] = (EWg(WJ, C6(J1)), iv, B.g(EWg(WJ, C6(J1)), ewg_(w, ph, WJ, wjn, C6(J1), g61)))
    SJ2 = Stacks(w, ph, mk, SJ.D, SJ.memb, SJ.ne, v2)
    R = B.run(SJ2)
    E1 = EWg('F', DK(1))
    g1 = B.g(E1, ewg_(w, ph, 'F', B.fn, DK(1), B.S0.vals['1'][2]))
    LAB = FRAGS['maf'].lmap()
    lm_ab = FRAGS['mab'].lmap(PL('P', 5), LAB['Z4'])
    B.call(R, 'tmidupb', {'K': '3', 'J': '1', 'I': '0', 'F': 'F', 'N': 'N', 'X': 'Y', 'P': PL(PL('P', 5), 0), 'E': lm_ab['Y2']},
           {'F e. NN0': B.fn, 'N e. NN0': B.nn, 'F < ( 2 ^ N )': c[LT2('F', 'N')]}, [('1', E1, g1)])
    E5 = EWg(AQ, C5('j'))
    g5 = B.g(E5, ewg_(w, ph, AQ, aqn, C5('j'), B.gam[C5('j')]))
    B.call(R, 'tmimulb', {'K': '6', 'J': '1', 'I': '5', "I'": '0', 'I"': '3', 'F': WJ, 'G': 'F', 'N': 'N', 'X': C6(J1), 'Y': DK(1),
                          'P': PL(PL('P', 5), 1), 'E': LAB['Z4']},
           {'( %s ` 6 ) = %s' % (PT, EWg(WJ, C6(J1))): iv, '%s e. NN0' % WJ: wjn, 'F e. NN0': B.fn, 'N e. NN0': B.nn,
            '%s < ( 2 ^ N )' % WJ: wjlt, 'F < ( 2 ^ N )': c[LT2('F', 'N')]},
           [('5', E5, g5), ('6', C6(J1), g61), ('1', DK(1), B.S0.vals['1'][2])])
    e, nrm, out2 = renorm(w, ph, B, R, [('5', C5('j')), ('6', C6('j'))], N8, PT=PT, pv=pvj)
    assert out2 == [('5', E5), ('6', C6(J1))], out2
    st = s([s([B.ww, B.fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph),
            s([jW, B.d5], 'jca', "( %s -> ( j e. ( 0 ..^ ( # ` W ) ) /\\ ( D ` 5 ) e. Word Gamma' ) )" % ph), w.inst('tmimafs')], 'syl2anc',
           '( %s -> %s = %s )' % (ph, C5(J1), E5))
    r_, nrm2 = w.rewrite(nrm, {E5: (C5(J1), s([st], 'eqcomd', '( %s -> %s = %s )' % (ph, E5, C5(J1))))}, ph)
    assert nrm2 == PB(J1), nrm2
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1))
    D0 = triple_D(R.cur)
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, D0, PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LAB['Z4'], S, deq, D0, '( %s ` %s )' % (PV, J1)))
    TB_ = '( TMB ` N )'
    cl.leaf(TB_, 'NN0', s([s([B.nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB_)))
    le = linarith(w, ph, [], '%s <_ %s' % (n, YB), closure=cl, atoms=[TB_])
    st = hrle(w, ph, mk['phm'], t, C, D, n, YB, cl.mem(YB, 'NN0'), le)
    finish(w, st, lab)
    return w.run()




def ran_bound(w, ph, B, k):
    """( ph -> A. a e. ran RM( k ) a < ( 2 ^ ( 2 x. N ) ) ): an entry of the reversed products is a product ` d q ` with
    ` d , q < 2 ^ N ` (~ mulallel , ~ tm2lrnrev ; Lean ` mulAll_mem_lt ` )"""
    s = w.s
    MPk = MP(k)
    PW = '( W prefix %s )' % k
    P2 = '( 2 ^ N )'
    Q2 = '( 2 ^ %s )' % N2
    pw = s([B.ww, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PW))
    mpw = B.mpw(k)
    pa = '( %s /\\ p e. ran %s )' % (ph, RM(k))
    L = lambda st: lift_from(w, ph, pa, st)
    ain = s([], 'simpr', '( %s -> p e. ran %s )' % (pa, RM(k)))
    a1 = s([L(s([mpw, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (ph, RM(k), MPk))), ain], 'sseldd',
           '( %s -> p e. ran %s )' % (pa, MPk))
    an = s([s([s([L(mpw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, MPk, MPk)), w.inst('frn')], 'syl',
              '( %s -> ran %s C_ NN0 )' % (pa, MPk)), a1], 'sseldd', '( %s -> p e. NN0 )' % pa)
    el = s([s([L(B.fn), an], 'jca', '( %s -> ( F e. NN0 /\\ p e. NN0 ) )' % pa), L(pw), w.inst('mulallel')], 'syl2anc',
           '( %s -> ( p e. ran %s <-> E. d e. ran %s p = ( d x. F ) ) )' % (pa, MPk, PW))
    ex = s([el, a1], 'mpbid', '( %s -> E. d e. ran %s p = ( d x. F ) )' % (pa, PW))
    pd = '( ( %s /\\ d e. ran %s ) /\\ p = ( d x. F ) )' % (pa, PW)
    Ld = lambda st: lift_from(w, ph, pd, st)
    dinp = s([], 'simplr', '( %s -> d e. ran %s )' % (pd, PW))
    kz = B.kz[k]
    rs = s([B.ww, kz, w.inst('pfxres')], 'syl2anc', '( %s -> %s = ( W |` ( 0 ..^ %s ) ) )' % (ph, PW, k))
    rss = s([s([rs], 'rneqd', '( %s -> ran %s = ran ( W |` ( 0 ..^ %s ) ) )' % (ph, PW, k)),
             s([s([], 'rnresss', 'ran ( W |` ( 0 ..^ %s ) ) C_ ran W' % k)], 'a1i', '( %s -> ran ( W |` ( 0 ..^ %s ) ) C_ ran W )' % (ph, k))],
            'eqsstrd', '( %s -> ran %s C_ ran W )' % (ph, PW))
    dW = s([Ld(rss), dinp], 'sseldd', '( %s -> d e. ran W )' % pd)
    rv = s([s([], 'breq1', '( a = d -> ( a < %s <-> d < %s ) )' % (P2, P2))], 'rspcv', '( d e. ran W -> ( A. a e. ran W a < %s -> d < %s ) )' % (P2, P2))
    dlt = s([dW, Ld(B.c[RALB('W', 'N')]), rv], 'sylc', '( %s -> d < %s )' % (pd, P2))
    dn = s([s([s([Ld(B.ww), w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % pd), w.inst('frn')], 'syl',
              '( %s -> ran W C_ NN0 )' % pd), dW], 'sseldd', '( %s -> d e. NN0 )' % pd)
    fn, nn = Ld(B.fn), Ld(B.nn)
    pn = s([closed(w, pd, '2nn', '2 e. NN'), nn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (pd, P2))
    pr = s([pn], 'nnred', '( %s -> %s e. RR )' % (pd, P2))
    m = s([s([dn], 'nn0red', '( %s -> d e. RR )' % pd), pr, s([fn], 'nn0red', '( %s -> F e. RR )' % pd), pr,
           s([dn], 'nn0ge0d', '( %s -> 0 <_ d )' % pd), s([fn], 'nn0ge0d', '( %s -> 0 <_ F )' % pd), dlt, Ld(B.c[LT2('F', 'N')])],
          'ltmul12ad', '( %s -> ( d x. F ) < ( %s x. %s ) )' % (pd, P2, P2))
    tw = s([s([nn], 'nn0cnd', '( %s -> N e. CC )' % pd)], '2timesd', '( %s -> ( 2 x. N ) = ( N + N ) )' % pd)
    ea = s([closed(w, pd, '2cn', '2 e. CC'), nn, nn], 'expaddd', '( %s -> ( 2 ^ ( N + N ) ) = ( %s x. %s ) )' % (pd, P2, P2))
    e2 = s([s([tw], 'oveq2d', '( %s -> %s = ( 2 ^ ( N + N ) ) )' % (pd, Q2)), ea], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (pd, Q2, P2, P2))
    m2 = s([m, e2], 'breqtrrd', '( %s -> ( d x. F ) < %s )' % (pd, Q2))
    lt = s([s([], 'simpr', '( %s -> p = ( d x. F ) )' % pd), m2], 'eqbrtrd', '( %s -> p < %s )' % (pd, Q2))
    r1 = s([s([lt], 'ex', '( ( %s /\\ d e. ran %s ) -> ( p = ( d x. F ) -> p < %s ) )' % (pa, PW, Q2))], 'rexlimdva',
           '( %s -> ( E. d e. ran %s p = ( d x. F ) -> p < %s ) )' % (pa, PW, Q2))
    r2 = s([ex, r1], 'mpd', '( %s -> p < %s )' % (pa, Q2))
    rp = s([r2], 'ralrimiva', '( %s -> A. p e. ran %s p < %s )' % (ph, RM(k), Q2))
    cb = s([s([], 'breq1', '( p = a -> ( p < %s <-> a < %s ) )' % (Q2, Q2))], 'cbvralvw',
           '( A. p e. ran %s p < %s <-> A. a e. ran %s a < %s )' % (RM(k), Q2, RM(k), Q2))
    return s([rp, cb], 'sylib', '( %s -> A. a e. ran %s a < %s )' % (ph, RM(k), Q2))


def tmimaft():
    lab = 'tmimaft'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` mulAllF ` loop at the machine: the family of ` MulAllInv ` is a stack family whose '
               '` x ` column is the rest of the list, at ` 0 ` it is the stacks after ` pushSym 5 bra ` , and at the end '
               '` revList 5 6 0 ` (~ tmilrevb ) moves the products onto ` x ` in the order of the list.')
    s = w.s
    B = Maf(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    fam = c['%s = %s' % (PV, PF)]
    ph0t = (TREE_MAF, NUMS)
    ph0 = cj(ph0t)
    # typing
    TK = (ph0t, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Maf(w, pk, TK)
    Sk = Bk.pbst('k')
    fm = s([Sk.memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    j0 = s([c[cj(TREE_MAF)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fm2 = s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)), fm2],
            'mpbird', '( %s -> %s )' % (ph, FTY))
    # the x column
    TJ = (T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Maf(w, pj, TJ)
    jz = Bj.c['j e. %s' % DOM]
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', jz, Bj.pbst('j'))
    col = s([SJ.vals['6'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    # the value at 0
    nlg = s([B.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
    z0 = s([nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0'))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le_ = s([B.ww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` W ) = ( encListB ` %s ) )' % (ph, LG))
    e6 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le_], 'eqtr4d',
              '( %s -> %s = ( encList ` W ) )' % (ph, EB('0'))) ], 'oveq1d', '( %s -> %s = %s )' % (ph, C6('0'), ENCL('W', 'X')))
    e6b = s([e6, s([c['( D ` 6 ) = %s' % ENCL('W', 'X')]], 'eqcomd', '( %s -> %s = ( D ` 6 ) )' % (ph, ENCL('W', 'X')))], 'eqtrd',
            '( %s -> %s = ( D ` 6 ) )' % (ph, C6('0')))
    m0 = s([s([s([s([], 'pfx00', '( W prefix 0 ) = (/)')], 'oveq2i', '( F MulAll ( W prefix 0 ) ) = ( F MulAll (/) )'),
               s([B.fn, w.inst('mulall0')], 'syl', '( %s -> ( F MulAll (/) ) = <. (/) , 0 >. )' % ph)], 'syl5eq' if False else 'eqtrid',
              '( %s -> ( F MulAll ( W prefix 0 ) ) = <. (/) , 0 >. )' % ph)], 'fveq2d',
            '( %s -> %s = ( 1st ` <. (/) , 0 >. ) )' % (ph, MP('0')))
    m1 = s([m0, s([s([s([], '0ex', '(/) e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. (/) , 0 >. ) = (/)')], 'a1i',
                  '( %s -> ( 1st ` <. (/) , 0 >. ) = (/) )' % ph)], 'eqtrd', '( %s -> %s = (/) )' % (ph, MP('0')))
    r0 = s([s([m1], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ph, RM('0'))), s([s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i',
                                                                                       '( %s -> ( reverse ` (/) ) = (/) )' % ph)],
           'eqtrd', '( %s -> %s = (/) )' % (ph, RM('0')))
    e5 = s([s([s([r0], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` (/) ) )' % (ph, RM('0'))),
               s([s([], 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'a1i', '( %s -> ( encList ` (/) ) = <" 2 "> )' % ph)], 'eqtrd',
              '( %s -> ( encList ` %s ) = <" 2 "> )' % (ph, RM('0')))], 'oveq1d', '( %s -> %s = ( <" 2 "> ++ ( D ` 5 ) ) )' % (ph, C5('0')))
    V5 = '( <" 2 "> ++ ( D ` 5 ) )'
    rr, xx = w.rewrite(PB('0'), {C5('0'): (V5, e5), C6('0'): ('( D ` 6 )', e6b)}, ph)
    assert xx == UPS('D', ('5', V5), ('6', DK(6))), xx
    s4 = s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
    B.g(V5, wgcat(w, ph, '<" 2 ">', DK(5), s4, B.d5))
    nst, outn = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, [('5', V5), ('6', DK(6))], B.gam, N8)
    assert outn == [('5', V5)], outn
    p0 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx)), nst], 'eqtrd', '( %s -> %s )' % (ph, P0EQ))
    # the closing revList 5 6 0
    nz = s([nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    pvN, SN = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, NLG, nz, B.pbst(NLG))
    B.kz[NLG] = s([nz, s([B.lg], 'oveq2d', '( %s -> %s = ( 0 ... ( # ` W ) ) )' % (ph, DOM))], 'eleqtrd', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (ph, NLG))
    PTN = '( %s ` %s )' % (PV, NLG)
    SR = SN.upd('6', 'X', B.g('X', B.xw))
    R = B.run(SR)
    B.deep('maf', 1)
    R.base.update(B.ex)
    n2n = cl.mem(N2, 'NN0')
    rmw = s([B.mpw(NLG), w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RM(NLG)))
    ral = ran_bound(w, ph, B, NLG)
    RR = '( reverse ` %s )' % RM(NLG)
    rrw = s([rmw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RR))
    g6 = B.g(ENCL(RR, 'X'), enclg(w, ph, RR, rrw, 'X', B.xw))
    B.call(R, 'tmilrevb', {'K': '5', 'J': '6', 'I': '0', 'L': RM(NLG), 'R': DK(5), 'B': N2, 'P': PL('P', 6), 'E': 'E'},
           {'%s e. Word NN0' % RM(NLG): rmw, WG(DK(5)): B.d5, '%s e. NN0' % N2: n2n, 'A. a e. ran %s a < ( 2 ^ %s )' % (RM(NLG), N2): ral},
           [('5', DK(5), B.d5), ('6', ENCL(RR, 'X'), g6)])
    PT6 = UP(PTN, '6', 'X')
    rw1, x1 = w.rewrite(PT6, {PTN: (PB(NLG), pvN)}, ph)
    e, nrm, out2 = renorm(w, ph, B, R, [('5', C5(NLG)), ('6', C6(NLG)), ('6', 'X')], N8, PT=PT6, pv=rw1)
    assert out2 == [('6', ENCL(RR, 'X'))], out2
    # reverse ( reverse MP ) = MP = ( 1st ` ( F MulAll W ) )
    rv = s([B.mpw(NLG), w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, RR, MP(NLG)))
    pf = s([s([B.lg], 'oveq2d', '( %s -> ( W prefix %s ) = ( W prefix ( # ` W ) ) )' % (ph, NLG)),
            s([B.ww, w.inst('pfxid')], 'syl', '( %s -> ( W prefix ( # ` W ) ) = W )' % ph)], 'eqtrd', '( %s -> ( W prefix %s ) = W )' % (ph, NLG))
    mw = s([s([pf], 'oveq2d', '( %s -> ( F MulAll ( W prefix %s ) ) = %s )' % (ph, NLG, MA_))], 'fveq2d', '( %s -> %s = %s )' % (ph, MP(NLG), MAW))
    r2, x2 = w.rewrite(nrm, {RR: (MAW, s([rv, mw], 'eqtrd', '( %s -> %s = %s )' % (ph, RR, MAW)))}, ph)
    assert x2 == DFIN, x2
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    D0 = triple_D(D)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, s([e, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, DFIN)), D0, DFIN))
    # the bound: ( # RM ) = # W
    ln = s([s([B.mpw(NLG), w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RM(NLG), MP(NLG))),
            s([s([mw], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, MP(NLG), MAW)),
               s([B.fn, B.ww, w.inst('mulalllen')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, MAW))], 'eqtrd',
              '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, MP(NLG)))], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RM(NLG)))
    rn, n2 = w.rewrite(n, {'( # ` %s )' % RM(NLG): ('( # ` W )', ln)}, ph)
    assert n2 == UB, (n2, UB)
    t, C, D, n = hrrw(w, ph, t, C, D, n, neq=rn)
    assert C == CLN(LMP['Y2'], S, PT6), (C, PT6)
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([p0, t], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, REVT))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ph, FTY, FCOL, P0EQ, REVT))
    finish(w, st, lab)
    return w.run()


def tmimafl():
    lab = 'tmimafl'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` mulAllF_le_B ` at the machine up to the bound: ~ tm2fmla at the family of ` MulAllInv ` ( ` P\' ` a '
               'letter), the entries by ~ tmimafi , the frame by ~ tmimaft .')
    s = w.s
    B = Maf(w, ph, T)
    B.deep('maf', 0)
    B.deep('maf', 1)
    c, mk, cl = B.c, B.mk, B.cl
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmimaft', STMTS11['tmimaft']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, REVT))
    ex[FTY] = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    ex[P0EQ] = s([a2], 'simpld', '( %s -> %s )' % (ph, P0EQ))
    ex[REVT] = s([a2], 'simprd', '( %s -> %s )' % (ph, REVT))
    per = s([s([], 'tmimafi', STMTS11['tmimafi'])], 'ralrimiva', '( %s -> %s )' % (PSI, PER))
    ex[PER] = lift_from(w, PSI, ph, per)
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex[WG('X')] = B.xw
    TB_ = '( TMB ` N )'
    cl.leaf(TB_, 'NN0', s([s([B.nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB_)))
    T2 = '( TMB ` %s )' % N2
    cl.leaf(T2, 'NN0', s([s([cl.mem(N2, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, T2))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, T2)))
    ex['%s e. NN0' % YB] = cl.mem(YB, 'NN0')
    ex['%s e. NN0' % UB] = cl.mem(UB, 'NN0')
    NQ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
    ssq = s([s([], 'ssrab2', '%s C_ %s' % (NQ, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, NQ, S))
    POPI_ = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (S, PID, S)
    ex['A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (NQ, PID, S)] = s([ssq, ex[POPI_], w.inst('ssralv')], 'sylc',
                                                                         '( %s -> A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s )' % (ph, NQ, PID, S))
    st = Bld(w, ph, c, ex)(GTREE)
    st2 = s([st, w.inst('tm2fmla')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    finish(w, st2, lab)
    return w.run()


def tmimafb():
    lab = 'tmimafb'
    T = numtree11(TREE_MAF)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` mulAllF_le_B ` at the machine ( ` x y r s t = 6 3 5 0 1 ` ): with a list ` l ` of numbers below '
               '` 2 ^ b ` on ` 6 ` and ` q < 2 ^ b ` on ` 3 ` , ` 6 ` ends with the list ` ( mulAll q l ).1 ` , every other stack '
               'restored, within ` ( ( mulAll q l ).2 + 1 ) B ( 4 b + 2 ) ` steps (~ tmimafl at the family).')
    s = w.s
    B = Maf(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    eq = s([], 'eqid', '%s = %s' % (PF, PF))
    t, cc = inst(w, ph, 'tmimafl', {PV: PF}, Bld(w, ph, c, {'%s = %s' % (PF, PF): s([eq], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}))
    C, D, n = triple_parts(cc)
    assert C == CS('maf') and D == CLN('E', S, DFIN), (C, D)
    TB_ = '( TMB ` N )'
    T2 = '( TMB ` %s )' % N2
    ARG = '( ( 4 x. N ) + 2 )'
    TA = '( TMB ` %s )' % ARG
    for x, a in ((TB_, 'N'), (T2, N2), (TA, ARG)):
        cl.leaf(x, 'NN0', s([s([cl.mem(a, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, x))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, x)))
    rn, n2 = w.rewrite(n, {NLG: ('( # ` W )', B.lg)}, ph)
    # TA = 8 x. T2
    sc = s([closed(w, ph, '1nn0', '1 e. NN0'), cl.mem(N2, 'NN0'), w.inst('tplbscale')], 'syl2anc',
           '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( TMB ` ( ( ( 1 + 1 ) x. %s ) + ( 2 x. 1 ) ) ) )' % (ph, T2, N2))
    ae = lineq(w, ph, '( ( ( 1 + 1 ) x. %s ) + ( 2 x. 1 ) )' % N2, ARG, closure=cl, products=True)
    sc2 = s([sc, s([ae], 'fveq2d', '( %s -> ( TMB ` ( ( ( 1 + 1 ) x. %s ) + ( 2 x. 1 ) ) ) = %s )' % (ph, N2, TA))], 'eqtrd',
            '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = %s )' % (ph, T2, TA))
    e8 = s([s([s([], '1p1e2', '( 1 + 1 ) = 2')], 'oveq1i', '( ( 1 + 1 ) ^ 3 ) = ( 2 ^ 3 )'), s([], 'cu2', '( 2 ^ 3 ) = 8')], 'eqtri',
           '( ( 1 + 1 ) ^ 3 ) = 8')
    ta = s([s([s([e8], 'oveq1i', '( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( 8 x. %s )' % (T2, T2))], 'a1i',
              '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( 8 x. %s ) )' % (ph, T2, T2)), sc2], 'eqtr3d', '( %s -> ( 8 x. %s ) = %s )' % (ph, T2, TA))
    mc = s([B.fn, B.ww, w.inst('mulallcost')], 'syl2anc', '( %s -> ( 2nd ` %s ) = ( # ` W ) )' % (ph, MA_))
    BND = '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (MA_, TA)
    RHS2 = '( ( ( # ` W ) + 1 ) x. ( 8 x. %s ) )' % T2
    rr, x_ = w.rewrite(RHS2, {'( 8 x. %s )' % T2: (TA, ta), '( # ` W )': ('( 2nd ` %s )' % MA_, s([mc], 'eqcomd', '( %s -> ( # ` W ) = ( 2nd ` %s ) )' % (ph, MA_)))}, ph)
    assert x_ == BND, x_
    mono = s([B.nn, cl.mem(N2, 'NN0'), linarith(w, ph, [cl.ge0('N')], 'N <_ %s' % N2, closure=cl), w.inst('tmbmono')], 'syl3anc',
             '( %s -> %s <_ %s )' % (ph, TB_, T2))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([cl.mem(N2, 'NN0'), closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, N2, T2))
    t16 = nlinarith(w, ph, [qd, cl.ge0('N')], '; 1 6 <_ %s' % T2, closure=cl, atoms=['N', T2])
    NW = '( # ` W )'
    f1 = s([cl.mem(TB_, 'RR'), cl.mem(T2, 'RR'), cl.mem(NW, 'RR'), cl.ge0(NW), mono], 'lemul2ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, NW, TB_, NW, T2))
    f2 = s([s([s([], ';16re' if False else '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph), cl.mem(T2, 'RR'), cl.mem(NW, 'RR'), cl.ge0(NW),
            linarith(w, ph, [t16], '2 <_ %s' % T2, closure=cl, atoms=[T2])], 'lemul2ad', '( %s -> ( %s x. 2 ) <_ ( %s x. %s ) )' % (ph, NW, NW, T2))
    le2 = linarith(w, ph, [f1, f2, mono, t16, cl.ge0(NW)], '%s <_ %s' % (n2, RHS2), closure=cl, atoms=[NW, TB_, T2], products=True)
    le = s([s([s([rn], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, RHS2, n2, RHS2)),
               s([rr], 'breq2d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, RHS2, n, BND))], 'bitr3d',
              '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n2, RHS2, n, BND)), le2], 'mpbid', '( %s -> %s <_ %s )' % (ph, n, BND))
    cl.leaf('( 2nd ` %s )' % MA_, 'NN0', s([mc, B.nw], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (ph, MA_)))
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
