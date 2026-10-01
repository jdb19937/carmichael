"""T11: Lean's ` divisorsOfF x z a c s t ` at ` 5 3 7 6 0 1 ` (PrimList.lean ` divisorsOfF_le_B ` ) on TMIdvs: ~ tm2fdvs at
the family of ` DivInv ` (the accumulator reversed on ` 7 ` , ` Q.reverse ` consumed from ` 3 ` ).

  tmidvsi   one element: ` copyList 7 6 0 1 ; mulAllF 6 3 5 0 1 ; appendList 6 7 1 0 ; dropNum 3 ` ( ` divBody_runs ` )
  tmidvst   the frame: typing, the ` z ` column, the prologue ` revList 5 3 0 ` , ` pushSym 7 bra ; pushNum 7 1 ` , the closing
            ` revList 7 5 0 `
  tmidvsl   ~ tm2fdvs assembled ( P' a letter)
  tmidvsb   divisorsOfF_le_B

    MM_DB=sorties/t11.mm python3 tools/gen/t11_d_dvs.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, nlinarith, lineq
from t7lib import mval
from t10_e_doa import lift_from
from t10_u_s2s import expose
import num
import t11_c_darith as DA

SEL = sys.argv[1:]
RW = '( reverse ` W )'
LG = '( encNatGam o. %s )' % RW
NLG = '( # ` %s )' % LG
DOM = '( 0 ... %s )' % NLG
EB = lambda k: '( encListB ` ( %s substr <. %s , %s >. ) )' % (LG, k, NLG)
C3 = lambda k: '( %s ++ ( D ` 3 ) )' % EB(k)
ACC = DA.ACC
C7 = lambda k: ENCL(ACC(k), DK(7))
PB = lambda k: UPS('D', ('3', C3(k)), ('5', 'X'), ('7', C7(k)))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
PV = "P'"
PSI_T = (TREE_DVS, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
MM = DA.MM
MP_ = '( ( 4 x. %s ) + 2 )' % MM
CC_ = '( 4 x. ( TMB ` %s ) )' % MP_
YF = '( i e. NN0 |-> ( ( ( 2 ^ i ) + 1 ) x. %s ) )' % CC_
DP = UPS('D', ('3', ENCL(RW, DK(3))), ('5', 'X'))
UA = '( ( ( # ` W ) x. ( ( 2 x. N ) + 6 ) ) + 4 )'
UC = '( ( ( 2 ^ ( # ` W ) ) + 1 ) x. ( TMB ` %s ) )' % MM
DVW = '( 1st ` %s )' % DV_
DFIN = UP('D', '5', ENCL(DVW, 'X'))
LMP = FRAGS['dvs'].lmap()
GM = {'P1': LMP['Z4'], 'A': LMP['Z5'], "A'": LMP['Y2'], 'A"': LMP['Z6'], 'E': LMP['Z7'], "E'": LMP['Y3'], 'E"': 'E', 'P0': LMP['Y1'],
      'Q0': LMP['Z1'], "Q'": LMP['Z2'], 'K': '3', 'J': '7', 'F': RDBRA, 'C': CNFL, 'F"': PID, 'N': S, 'O': S, "N'": S, 'N"': S,
      'L': LG, 'R': DK(3), 'Y': YF, 'P': PV, 'D': 'D', "D'": DP, 'D"': DFIN, 'U': UA, "U'": '2', 'U"': UC}
_GA, _GC = split_imp(stmt('tm2fdvs'))
GTREE = tsub(parse_conj(_GA), GM)
GCONCL = tsub_text(_GC, GM)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in _fl if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
PRO1 = [t for t in _fl if t.startswith('( { ( inl ` %s ) }' % LMP['Y1'])][0]
PRO2 = [t for t in _fl if t.startswith('( { ( inl ` %s ) }' % LMP['Z2'])][0]
REVT = [t for t in _fl if t.startswith('( { ( inl ` %s ) }' % LMP['Y3'])][0]
add11('tmidvsi', (PSI_T, 'j e. ( 0 ..^ %s )' % NLG), PERB)
add11('tmidvst', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) )' % (FTY, FCOL, PRO1, PRO2, REVT))
add11('tmidvsl', PSI_T, GCONCL)
for _l in ('tmidvsi', 'tmidvst', 'tmidvsl'):
    ORDER11.remove(_l)
    ORDER11.insert(ORDER11.index('tmidvsb'), _l)

if __name__ == '__main__' and 'show' in SEL:
    print(PERB); print(); print(PRO1); print(); print(PRO2); print(); print(REVT); print(); print(GCONCL)


class Dvs(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        ww, nn, xw = c0['W e. Word NN0'], c0['N e. NN0'], c0[WG('X')]
        eqs = {'5': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw))}
        Base.__init__(self, w, ph, T, N8, 'dvs', eqs)
        s = w.s
        self.ww, self.nn, self.xw = ww, nn, xw
        self.ral = c0[RALB('W', 'N')]
        self.rww = s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RW))
        self.lgw = s([self.rww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([s([self.rww, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc',
                       '( %s -> %s = ( # ` %s ) )' % (ph, NLG, RW)), s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))],
                    'eqtrd', '( %s -> %s = ( # ` W ) )' % (ph, NLG))
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
        self.cl = Closure(w, ph, {'N': ('NN0', nn)})
        self.cl.leaf('( # ` W )', 'NN0', self.nw)
        self.hw = s([ww, nn, self.ral], '3jca', '( %s -> %s )' % (ph, DA.HW))
        self.g('X', xw)

    def accw(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        d, rp, pw, rw = DA.dvw(w, ph, self.ww, k, None)
        return s([d, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ACC(k)))

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g3 = self.g(C3(k), wgcat(w, ph, EB(k), DK(3), eb, self.S0.vals['3'][2]))
        g7 = self.g(C7(k), enclg(w, ph, ACC(k), self.accw(k), DK(7), self.S0.vals['7'][2]))
        return self.S0.upd('3', C3(k), g3).upd('5', 'X', self.xw).upd('7', C7(k), g7)

    def jfz(self, j, jz):
        """( ph -> j e. ( 0 ... ( # ` W ) ) ) from jz : j e. DOM"""
        return self.w.s([jz, self.w.s([self.lg], 'oveq2d', '( %s -> %s = ( 0 ... ( # ` W ) ) )' % (self.ph, DOM))], 'eleqtrd',
                        '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (self.ph, j))


def tb(w, ph, cl, x):
    """register ( TMB ` x ) as a closure leaf"""
    T_ = '( TMB ` %s )' % x
    cl.leaf(T_, 'NN0', w.s([w.s([cl.mem(x, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, T_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, T_)))
    return T_


def tmidvsi():
    lab = 'tmidvsi'
    T = numtree11((PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    ph = cj(T)
    w = W(lab, 'One element of Lean\'s ` divisorsOfF ` loop at the machine ( ` divBody_runs ` ): at the family of ` DivInv ` , '
               '` copyList 7 6 0 1 ` (~ tmilcpyb ), ` mulAllF ` (~ tmimafb ), ` appendList 6 7 0 1 ` (~ tmilappb ) and '
               '` dropNum 3 ` (~ tmidropb ) take the accumulator of the first ` j ` elements of ` Q.reverse ` to that of the first '
               '` j + 1 ` (~ tmdvacc ), within ` ( 2 ^ j + 1 ) 4 B ( 4 ( # Q b + 1 ) + 2 ) ` steps.')
    B = Dvs(w, ph, T)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    jj = c['j e. ( 0 ..^ %s )' % NLG]
    jW = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` W ) ) )' % (ph, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` W ) ) )' % ph)
    jR = s([jW, s([s([s([B.ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqcomd',
                     '( %s -> ( # ` W ) = ( # ` %s ) )' % (ph, RW))], 'oveq2d', '( %s -> ( 0 ..^ ( # ` W ) ) = ( 0 ..^ ( # ` %s ) ) )' % (ph, RW))],
           'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` %s ) ) )' % (ph, RW))
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    J1 = '( j + 1 )'
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (ph, J1, DOM))
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j'))
    PT = '( %s ` j )' % PV
    Q = '( %s ` j )' % RW
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.rww, w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (ph, RW, RW)), jR, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (ph, LG, Q))
    qn = s([B.rww, jR, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Q))
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    d3 = B.S0.vals['3'][2]
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = s([lgj, encw(w, ph, Q, qn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG))
    ca1 = s([egj, g4, d3, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ ( D ` 3 ) ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) ) )' % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, d3, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) = ( <" 4 "> ++ %s ) )' % (ph, EB(J1), C3(J1)))
    r1 = s([s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ ( D ` 3 ) ) )' % (ph, C3('j'), LG, EB(J1))), ca1], 'eqtrd',
           '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) ) )' % (ph, C3('j'), LG, EB(J1)))
    r2 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) ) = %s )' % (ph, LG, EB(J1), EWg(Q, C3(J1))))
    iv = s([SJ.vals['3'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, C3('j'), EWg(Q, C3(J1))))], 'eqtrd',
           '( %s -> ( %s ` 3 ) = %s )' % (ph, PT, EWg(Q, C3(J1))))
    g31 = B.g(C3(J1), wgcat(w, ph, EB(J1), DK(3), eb1, d3))
    # the arithmetic
    hj = s([B.hw, jW], 'jca', '( %s -> ( %s /\\ j e. ( 0 ..^ ( # ` W ) ) ) )' % (ph, DA.HW))
    ACJ = ACC('j')
    MJ = '( 1st ` ( %s MulAll %s ) )' % (Q, ACJ)
    mb = s([hj, w.inst('tmdvmbd')], 'syl', '( %s -> ( ( %s < ( 2 ^ N ) /\\ %s < ( 2 ^ %s ) ) /\\ A. a e. ran %s a < ( 2 ^ ( 2 x. %s ) ) ) )'
           % (ph, Q, Q, MM, MJ, MM))
    qlt = s([s([mb], 'simpld', '( %s -> ( %s < ( 2 ^ N ) /\\ %s < ( 2 ^ %s ) ) )' % (ph, Q, Q, MM))], 'simpld', '( %s -> %s < ( 2 ^ N ) )' % (ph, Q))
    qlm = s([s([mb], 'simpld', '( %s -> ( %s < ( 2 ^ N ) /\\ %s < ( 2 ^ %s ) ) )' % (ph, Q, Q, MM))], 'simprd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, Q, MM))
    mjb = s([mb], 'simprd', '( %s -> A. a e. ran %s a < ( 2 ^ ( 2 x. %s ) ) )' % (ph, MJ, MM))
    jW0 = s([jW, w.inst('elfzofz')], 'syl', '( %s -> j e. ( 0 ... ( # ` W ) ) )' % ph)
    ab = s([s([B.hw, jW0], 'jca', '( %s -> ( %s /\\ j e. ( 0 ... ( # ` W ) ) ) )' % (ph, DA.HW)), w.inst('tmdvbnd')], 'syl',
           '( %s -> A. a e. ran %s a < ( 2 ^ %s ) )' % (ph, ACJ, MM))
    acw = B.accw('j')
    mjw = s([s([qn, acw, w.inst('mulallcl')], 'syl2anc', '( %s -> ( %s MulAll %s ) e. ( Word NN0 X. NN0 ) )' % (ph, Q, ACJ)), w.inst('xp1st')], 'syl',
            '( %s -> %s e. Word NN0 )' % (ph, MJ))
    mmn = cl.mem(MM, 'NN0')
    m2n = cl.mem('( 2 x. %s )' % MM, 'NN0')
    # the Run
    v2 = dict(SJ.vals)
    v2['3'] = (EWg(Q, C3(J1)), iv, B.g(EWg(Q, C3(J1)), ewg_(w, ph, Q, qn, C3(J1), g31)))
    SJ2 = Stacks(w, ph, mk, SJ.D, SJ.memb, SJ.ne, v2)
    B.deep('dvs', 1)
    R = B.run(SJ2)
    P8 = PL('P', 8)
    lmb = FRAGS['dvb'].lmap(P8, LMP['Z6'])
    E6a = ENCL(ACJ, DK(6))
    g6a = B.g(E6a, enclg(w, ph, ACJ, acw, DK(6), B.S0.vals['6'][2]))
    B.call(R, 'tmilcpyb', {'K': '7', 'J': '6', 'I': '0', "I'": '1', 'L': ACJ, 'R': DK(7), 'B': MM, 'P': PL(P8, 0), 'E': lmb['Y2']},
           {'%s e. Word NN0' % ACJ: acw, '%s e. NN0' % MM: mmn, RALB(ACJ, MM): ab}, [('6', E6a, g6a)])
    E6b = ENCL(MJ, DK(6))
    g6b = B.g(E6b, enclg(w, ph, MJ, mjw, DK(6), B.S0.vals['6'][2]))
    B.call(R, 'tmimafb', {'W': ACJ, 'F': Q, 'N': MM, 'X': DK(6), 'Y': C3(J1), 'P': PL(P8, 1), 'E': lmb['Y3']},
           {'%s e. Word NN0' % ACJ: acw, '%s e. NN0' % Q: qn, '%s e. NN0' % MM: mmn, RALB(ACJ, MM): ab, LT2(Q, MM): qlm}, [('6', E6b, g6b)])
    MA2 = '( %s ++ %s )' % (MJ, ACJ)
    ma2w = s([mjw, acw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ph, MA2))
    E7 = ENCL(MA2, DK(7))
    g7 = B.g(E7, enclg(w, ph, MA2, ma2w, DK(7), B.S0.vals['7'][2]))
    B.call(R, 'tmilappb', {'K': '6', 'J': '7', 'I': '0', "I'": '1', 'L': MJ, 'U': ACJ, 'R': DK(6), "R'": DK(7), 'B': '( 2 x. %s )' % MM,
                           'P': PL(P8, 2), 'E': lmb['Y4']},
           {'%s e. Word NN0' % MJ: mjw, '%s e. Word NN0' % ACJ: acw, '( 2 x. %s ) e. NN0' % MM: m2n, RALB(MJ, '( 2 x. %s )' % MM): mjb},
           [('6', DK(6), B.S0.vals['6'][2]), ('7', E7, g7)])
    Son, old = expose(w, ph, B, R, '3')
    B.call(R, 'tmidropb', {'K': '3', 'F': Q, 'N': 'N', 'X': C3(J1), 'P': PL(P8, 3), 'E': LMP['Z6']},
           {'%s e. NN0' % Q: qn, 'N e. NN0': B.nn, '%s < ( 2 ^ N )' % Q: qlt}, [('3', C3(J1), g31)], on=(Son, old))
    e, nrm, out2 = renorm(w, ph, B, R, [('3', C3('j')), ('5', 'X'), ('7', C7('j'))], N8, PT=PT, pv=pvj)
    assert out2 == [('3', C3(J1)), ('5', 'X'), ('7', E7)], out2
    st = s([s([B.ww, jW], 'jca', '( %s -> ( W e. Word NN0 /\\ j e. ( 0 ..^ ( # ` W ) ) ) )' % ph), w.inst('tmdvacc')], 'syl',
           '( %s -> %s = %s )' % (ph, ACC(J1), MA2))
    r_, nrm2 = w.rewrite(nrm, {MA2: (ACC(J1), s([st], 'eqcomd', '( %s -> %s = %s )' % (ph, MA2, ACC(J1))))}, ph)
    assert nrm2 == PB(J1), nrm2
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1))
    D0 = triple_D(R.cur)
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, D0, PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LMP['Z6'], S, deq, D0, '( %s ` %s )' % (PV, J1)))
    # the bound
    P2J = '( 2 ^ j )'
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % ph)
    cl.leaf(P2J, 'NN0', s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), jn], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, P2J)))
    ln1 = s([s([B.ww, jW0], 'jca', '( %s -> ( W e. Word NN0 /\\ j e. ( 0 ... ( # ` W ) ) ) )' % ph), w.inst('tmdvlen')], 'syl',
            '( %s -> ( # ` %s ) = %s )' % (ph, ACJ, P2J))
    ln2 = s([s([qn, acw, w.inst('mulallcost')], 'syl2anc', '( %s -> ( 2nd ` ( %s MulAll %s ) ) = ( # ` %s ) )' % (ph, Q, ACJ, ACJ)), ln1], 'eqtrd',
            '( %s -> ( 2nd ` ( %s MulAll %s ) ) = %s )' % (ph, Q, ACJ, P2J))
    ln3 = s([s([qn, acw, w.inst('mulalllen')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, MJ, ACJ)), ln1], 'eqtrd',
            '( %s -> ( # ` %s ) = %s )' % (ph, MJ, P2J))
    rn, n2 = w.rewrite(n, {'( # ` %s )' % ACJ: (P2J, ln1), '( 2nd ` ( %s MulAll %s ) )' % (Q, ACJ): (P2J, ln2), '( # ` %s )' % MJ: (P2J, ln3)}, ph)
    TM1, TM2, TMP, TN = tb(w, ph, cl, MM), tb(w, ph, cl, '( 2 x. %s )' % MM), tb(w, ph, cl, MP_), tb(w, ph, cl, 'N')
    jlt = s([jj, w.inst('elfzolt2')], 'syl', '( %s -> j < %s )' % (ph, NLG))
    jlt2 = s([jlt, B.lg], 'breqtrd', '( %s -> j < ( # ` W ) )' % ph)
    j1l = s([jlt2, s([cl.mem('j', 'ZZ') if False else s([jn], 'nn0zd', '( %s -> j e. ZZ )' % ph), cl.mem('( # ` W )', 'ZZ'), w.inst('zltp1le')], 'syl2anc',
                     '( %s -> ( j < ( # ` W ) <-> ( j + 1 ) <_ ( # ` W ) ) )' % ph)], 'mpbid', '( %s -> ( j + 1 ) <_ ( # ` W ) )' % ph)
    cl.leaf('j', 'NN0', jn)
    w1 = linarith(w, ph, [j1l, cl.ge0('j')], '1 <_ ( # ` W )', closure=cl)
    nm = s([s([s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % ph), cl.mem('( # ` W )', 'RR'), cl.mem('N', 'RR'), cl.ge0('N'), w1], 'lemul1ad',
           '( %s -> ( 1 x. N ) <_ ( ( # ` W ) x. N ) )' % ph)
    mono = lambda a, b_, ta, tb_: s([cl.mem(a, 'NN0'), cl.mem(b_, 'NN0'), linarith(w, ph, [nm, cl.ge0('N'), cl.ge0('( # ` W )')], '%s <_ %s' % (a, b_),
                                                                                   closure=cl, products=True), w.inst('tmbmono')], 'syl3anc',
                                    '( %s -> %s <_ %s )' % (ph, ta, tb_))
    m1 = mono(MM, MP_, TM1, TMP)
    m2 = mono('( 2 x. %s )' % MM, MP_, TM2, TMP)
    m3 = mono('N', MP_, TN, TMP)
    P1 = '( %s + 1 )' % P2J
    f1 = s([cl.mem(TM1, 'RR'), cl.mem(TMP, 'RR'), cl.mem(P1, 'RR'), cl.ge0(P1), m1], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, P1, TM1, P1, TMP))
    f2 = s([cl.mem(TM2, 'RR'), cl.mem(TMP, 'RR'), cl.mem(P1, 'RR'), cl.ge0(P1), m2], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, P1, TM2, P1, TMP))
    f3 = s([s([s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % ph), cl.mem(P1, 'RR'), cl.mem(TMP, 'RR'), cl.ge0(TMP),
            linarith(w, ph, [cl.ge0(P2J)], '1 <_ %s' % P1, closure=cl)], 'lemul1ad', '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, TMP, P1, TMP))
    YV = '( ( ( 2 ^ j ) + 1 ) x. %s )' % CC_
    le2 = linarith(w, ph, [f1, f2, f3, m3], '%s <_ %s' % (n2, YV), closure=cl, atoms=[P2J, TM1, TM2, TMP, TN], products=True)
    le = s([s([rn], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, YV, n2, YV)), le2], 'mpbird', '( %s -> %s <_ %s )' % (ph, n, YV))
    t = hrle(w, ph, mk['phm'], t, C, D, n, YV, cl.mem(YV, 'NN0'), le)
    hy = s([s([s([], 'oveq2', '( i = j -> ( 2 ^ i ) = ( 2 ^ j ) )')], 'oveq1d', '( i = j -> ( ( 2 ^ i ) + 1 ) = ( ( 2 ^ j ) + 1 ) )')], 'oveq1d',
           '( i = j -> ( ( ( 2 ^ i ) + 1 ) x. %s ) = %s )' % (CC_, YV))
    fvm = s([hy, s([], 'eqid', '%s = %s' % (YF, YF)), s([], 'ovex', '%s e. _V' % YV)], 'fvmpt', '( j e. NN0 -> ( %s ` j ) = %s )' % (YF, YV))
    fvj = s([jn, fvm], 'syl', '( %s -> ( %s ` j ) = %s )' % (ph, YF, YV))
    t, C, D, n = hrrw(w, ph, t, C, D, YV, neq=s([fvj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (ph, YV, YF)))
    yn = s([fvj, cl.mem(YV, 'NN0')], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (ph, YF))
    finish(w, s([yn, t], 'jca', '( %s -> %s )' % (ph, PERB)), lab)
    return w.run()



def tmidvst():
    lab = 'tmidvst'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` divisorsOfF ` loop at the machine: the family of ` DivInv ` is a stack family whose ` z ` '
               'column is the rest of ` Q.reverse ` ; the prologue ` revList 5 3 0 ` (~ tmilrevn ), ` pushSym 7 bra ; pushNum 7 1 ` '
               'enters it at ` 0 ` , and the closing ` revList 7 5 0 ` (~ tmilrevb ) leaves ` divisorsOf Q ` on ` x ` .')
    s = w.s
    B = Dvs(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    fam = c['%s = %s' % (PV, PF)]
    ph0t = (TREE_DVS, NUMS)
    ph0 = cj(ph0t)
    TK = (ph0t, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Dvs(w, pk, TK)
    fm = s([Bk.pbst('k').memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    j0 = s([c[cj(TREE_DVS)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)),
             s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))], 'mpbird', '( %s -> %s )' % (ph, FTY))
    TJ = (T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Dvs(w, pj, TJ)
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', Bj.c['j e. %s' % DOM], Bj.pbst('j'))
    col = s([SJ.vals['3'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    B.deep('dvs', 0)
    B.deep('dvs', 2)
    # 1. revList 5 3 0
    R1 = B.run()
    E3 = ENCL(RW, DK(3))
    g3 = B.g(E3, enclg(w, ph, RW, B.rww, DK(3), B.S0.vals['3'][2]))
    B.call(R1, 'tmilrevn', {'K': '5', 'J': '3', 'I': '0', 'L': 'W', 'R': 'X', 'B': 'N', 'P': PL('P', 7), 'E': LMP['Z1']},
           {RALB('W', 'N'): B.ral}, [('5', 'X', B.xw), ('3', E3, g3)])
    cur, out = R1.normalize(N8)
    assert out == [('3', E3), ('5', 'X')], out
    assert triple_D(R1.cur) == DP
    pro1 = R1.tri
    # 2. pushSym 7 comma ; pushSym 7 ( bit true ) from UPD( DP , 7 , <" 2 "> ++ D7 )
    SDP = R1.at(out)
    V2 = '( <" 2 "> ++ ( D ` 7 ) )'
    s2 = s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
    g2 = B.g(V2, wgcat(w, ph, '<" 2 ">', DK(7), s2, B.S0.vals['7'][2]))
    R2 = B.run()
    R2.gam.update(B.gam)
    R2.S, R2.chain = R2.at(out + [('7', V2)]), out + [('7', V2)]
    for _k, (_t, _st, _g) in R2.S.vals.items():
        R2.gam[_t] = _g
    V4 = '( <" 4 "> ++ %s )' % V2
    g4 = B.g(V4, wg4(w, ph, V2, g2))
    B.call(R2, 'tm2fpshn', {'A': LMP['Z2'], 'E': LMP['Z3'], 'K': '7', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('7'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['7']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('7')))},
           [('7', V4, g4)])
    V1 = '( <" %s "> ++ %s )' % (B1, V4)
    bg = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1))
    g1 = B.g(V1, wgcat(w, ph, '<" %s ">' % B1, V4, s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1)), g4))
    B.call(R2, 'tm2fpshn', {'A': LMP['Z3'], 'E': LMP['Z4'], 'K': '7', 'Z': B1, 'N': S},
           {'%s e. %s' % (B1, GX('7')): s([bg, mk['k']['7']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1, GX('7')))}, [('7', V1, g1)])
    cur2, out2 = R2.normalize(N8)
    assert out2 == [('3', E3), ('5', 'X'), ('7', V1)], out2
    # PB( 0 ) is that
    nlg = s([B.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
    z0 = s([nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0'))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le_ = s([B.rww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, RW, LG))
    e3 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le_], 'eqtr4d',
              '( %s -> %s = ( encList ` %s ) )' % (ph, EB('0'), RW))], 'oveq1d', '( %s -> %s = %s )' % (ph, C3('0'), E3))
    # ACC( 0 ) = <" 1 ">
    rp0 = s([s([s([], 'pfx00', '( %s prefix 0 ) = (/)' % RW)], 'fveq2i', '( reverse ` ( %s prefix 0 ) ) = ( reverse ` (/) )' % RW),
             s([], 'rev0', '( reverse ` (/) ) = (/)')], 'eqtri', '( reverse ` ( %s prefix 0 ) ) = (/)' % RW)
    dj0 = s([s([s([rp0], 'fveq2i', '( DivisorsOf ` ( reverse ` ( %s prefix 0 ) ) ) = ( DivisorsOf ` (/) )' % RW),
                s([], 'divisorsof0', '( DivisorsOf ` (/) ) = <. <" 1 "> , 0 >.')], 'eqtri',
               '( DivisorsOf ` ( reverse ` ( %s prefix 0 ) ) ) = <. <" 1 "> , 0 >.' % RW)], 'fveq2i',
            '%s = ( 1st ` <. <" 1 "> , 0 >. )' % DA.DJ('0'))
    dj1 = s([dj0, s([s([s([], 's1cli', '<" 1 "> e. Word _V')], 'elexi', '<" 1 "> e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st',
                    '( 1st ` <. <" 1 "> , 0 >. ) = <" 1 ">')], 'eqtri', '%s = <" 1 ">' % DA.DJ('0'))
    ac0 = s([s([dj1], 'fveq2i', '%s = ( reverse ` <" 1 "> )' % ACC('0')), s([], 'revs1', '( reverse ` <" 1 "> ) = <" 1 ">')], 'eqtri', '%s = <" 1 ">' % ACC('0'))
    o1 = s([s([], '1nn0', '1 e. NN0'), s([], 'wrd0', '(/) e. Word NN0'), w.inst('tm2lenccons')], 'mp2an' if False else 'mp2an',
           '( encList ` ( <" 1 "> ++ (/) ) ) = ( ( encNatGam ` 1 ) ++ ( <" 4 "> ++ ( encList ` (/) ) ) )') if False else None
    enc1 = s([s([s([], '1nn0', '1 e. NN0'), s([], 'wrd0', '(/) e. Word NN0')], 'pm3.2i', '( 1 e. NN0 /\\ (/) e. Word NN0 )'), w.inst('tm2lenccons')], 'ax-mp',
             '( encList ` ( <" 1 "> ++ (/) ) ) = ( ( encNatGam ` 1 ) ++ ( <" 4 "> ++ ( encList ` (/) ) ) )')
    cr = s([s([s([], '1nn0', '1 e. NN0'), w.inst('s1cl')], 'ax-mp', '<" 1 "> e. Word NN0'), w.inst('ccatrid')], 'ax-mp', '( <" 1 "> ++ (/) ) = <" 1 ">')
    enc2 = s([s([s([cr], 'fveq2i', '( encList ` ( <" 1 "> ++ (/) ) ) = ( encList ` <" 1 "> )')], 'eqcomi', '( encList ` <" 1 "> ) = ( encList ` ( <" 1 "> ++ (/) ) )'),
              enc1], 'eqtri', '( encList ` <" 1 "> ) = ( ( encNatGam ` 1 ) ++ ( <" 4 "> ++ ( encList ` (/) ) ) )')
    enc3 = s([enc2, s([s([], 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'oveq2i',
                     '( <" 4 "> ++ ( encList ` (/) ) ) = ( <" 4 "> ++ <" 2 "> )') if False else None], 'id', '') if False else None
    e7a = s([s([s([ac0], 'fveq2i', '( encList ` %s ) = ( encList ` <" 1 "> )' % ACC('0')), enc2], 'eqtri',
               '( encList ` %s ) = ( ( encNatGam ` 1 ) ++ ( <" 4 "> ++ ( encList ` (/) ) ) )' % ACC('0'))], 'a1i',
            '( %s -> ( encList ` %s ) = ( ( encNatGam ` 1 ) ++ ( <" 4 "> ++ ( encList ` (/) ) ) ) )' % (ph, ACC('0')))
    EN1 = '( encNatGam ` 1 )'
    EL0 = '( encList ` (/) )'
    en1w = encw(w, ph, '1', closed(w, ph, '1nn0', '1 e. NN0'))
    el0w = s([s([], 'wrd0', '(/) e. Word NN0') if False else closed(w, ph, 'wrd0', '(/) e. Word NN0'), w.inst('tm2lenccl')], 'syl',
             "( %s -> %s e. Word Gamma' )" % (ph, EL0))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    g40 = s([s4, el0w, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ %s ) e. Word Gamma' )" % (ph, EL0))
    d7 = B.S0.vals['7'][2]
    as1 = s([en1w, g40, d7, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ ( D ` 7 ) ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 7 ) ) ) )'
              % (ph, EN1, EL0, EN1, EL0))
    as2 = s([s4, el0w, d7, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` 7 ) ) = ( <" 4 "> ++ ( %s ++ ( D ` 7 ) ) ) )' % (ph, EL0, EL0))
    ez = s([s([s([s([], 'tm2lenc0', '%s = <" 2 ">' % EL0)], 'oveq1i', '( %s ++ ( D ` 7 ) ) = %s' % (EL0, V2))], 'oveq2i',
              '( <" 4 "> ++ ( %s ++ ( D ` 7 ) ) ) = %s' % (EL0, V4))], 'a1i', '( %s -> ( <" 4 "> ++ ( %s ++ ( D ` 7 ) ) ) = %s )' % (ph, EL0, V4))
    e7b = s([s([s([e7a], 'oveq1d', '( %s -> %s = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ ( D ` 7 ) ) )' % (ph, C7('0'), EN1, EL0)), as1], 'eqtrd',
               '( %s -> %s = ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 7 ) ) ) )' % (ph, C7('0'), EN1, EL0)),
             s([s([as2, ez], 'eqtrd', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` 7 ) ) = %s )' % (ph, EL0, V4))], 'oveq2d',
               '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 7 ) ) ) = ( %s ++ %s ) )' % (ph, EN1, EL0, EN1, V4))], 'eqtrd',
            '( %s -> %s = ( %s ++ %s ) )' % (ph, C7('0'), EN1, V4))
    e7c = s([e7b, s([s([g2, w.inst('tmienc1')], 'syl', '( %s -> ( %s ++ ( <" 4 "> ++ %s ) ) = ( <" %s "> ++ ( <" 4 "> ++ %s ) ) )' % (ph, EN1, V2, B1, V2))],
                    'id', '') if False else s([g2, w.inst('tmienc1')], 'syl', '( %s -> ( %s ++ ( <" 4 "> ++ %s ) ) = ( <" %s "> ++ ( <" 4 "> ++ %s ) ) )' % (ph, EN1, V2, B1, V2))],
            'eqtrd', '( %s -> %s = %s )' % (ph, C7('0'), V1))
    rr, xx = w.rewrite(PB('0'), {C3('0'): (E3, e3), C7('0'): (V1, e7c)}, ph)
    assert xx == chain_text('D', out2), xx
    D2 = triple_D(R2.cur)
    e, nrm, _ = renorm(w, ph, B, R2, [], N8) if False else (None, None, None)
    # R2's stacks are already normal relative to D (its base is B.S0)
    deq2 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx))], 'eqcomd', '( %s -> %s = ( %s ` 0 ) )' % (ph, xx, PV))
    assert D2 == xx, (D2, xx)
    t2, C2, D2c, n2 = hrrw(w, ph, R2.tri, R2.C0, R2.cur, R2.n, deq=clneq(w, ph, LMP['Z4'], S, deq2, xx, '( %s ` 0 )' % PV),
                           neq=s([s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( %s -> ( 1 + 1 ) = 2 )' % ph))
    # the pre class: ( D ` 7 ) = ( DP ` 7 )
    SD = R1.at(out)
    d7e = s([SD.vals['7'][1]], 'eqcomd', '( %s -> ( D ` 7 ) = ( %s ` 7 ) )' % (ph, DP))
    PRE_OLD = UP(DP, '7', V2)
    PRE_NEW = UP(DP, '7', '( <" 2 "> ++ ( %s ` 7 ) )' % DP)
    ue = upeq(w, ph, DP, '7', s([d7e], 'oveq2d', '( %s -> %s = ( <" 2 "> ++ ( %s ` 7 ) ) )' % (ph, V2, DP)), V2, '( <" 2 "> ++ ( %s ` 7 ) )' % DP)
    assert C2 == CLN(LMP['Z2'], S, PRE_OLD), (C2[:300], PRE_OLD[:300])
    t2, C2, D2c, n2 = hrrw(w, ph, t2, C2, D2c, n2, ceq=clneq(w, ph, LMP['Z2'], S, ue, PRE_OLD, PRE_NEW))
    # 3. the closing revList 7 5 0 from UPD( ( P' ` NLG ) , 3 , D3 )
    nz = s([nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    pvN, SN = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, NLG, nz, B.pbst(NLG))
    PTN = '( %s ` %s )' % (PV, NLG)
    SR = SN.upd('3', DK(3), B.S0.vals['3'][2])
    R3 = B.run(SR)
    nzW = B.jfz(NLG, nz)
    ACN = ACC(NLG)
    acw = B.accw(NLG)
    mmn = cl.mem(MM, 'NN0')
    ab = s([s([B.hw, nzW], 'jca', '( %s -> ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) )' % (ph, DA.HW, NLG)), w.inst('tmdvbnd')], 'syl',
           '( %s -> A. a e. ran %s a < ( 2 ^ %s ) )' % (ph, ACN, MM))
    RA = '( reverse ` %s )' % ACN
    raw = s([acw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RA))
    E5 = ENCL(RA, 'X')
    g5 = B.g(E5, enclg(w, ph, RA, raw, 'X', B.xw))
    B.call(R3, 'tmilrevb', {'K': '7', 'J': '5', 'I': '0', 'L': ACN, 'R': DK(7), 'B': MM, 'P': PL('P', 9), 'E': 'E'},
           {'%s e. Word NN0' % ACN: acw, '%s e. NN0' % MM: mmn, RALB(ACN, MM): ab}, [('7', DK(7), B.S0.vals['7'][2]), ('5', E5, g5)])
    PT3 = UP(PTN, '3', DK(3))
    rw1, x1 = w.rewrite(PT3, {PTN: (PB(NLG), pvN)}, ph)
    e3_, nrm3, out3 = renorm(w, ph, B, R3, [('3', C3(NLG)), ('5', 'X'), ('7', C7(NLG)), ('3', DK(3))], N8, PT=PT3, pv=rw1)
    assert out3 == [('5', E5)], out3
    # reverse ACC( NLG ) = ( 1st ` ( DivisorsOf ` W ) )
    dw, rpw, pww, rw_ = DA.dvw(w, ph, B.ww, NLG, None)
    rv = s([dw, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, RA, DA.DJ(NLG)))
    nlr = s([B.lg, s([s([B.ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqcomd', '( %s -> ( # ` W ) = ( # ` %s ) )' % (ph, RW))],
            'eqtrd', '( %s -> %s = ( # ` %s ) )' % (ph, NLG, RW))
    pf = s([s([nlr], 'oveq2d', '( %s -> %s = ( %s prefix ( # ` %s ) ) )' % (ph, DA.PJ(NLG), RW, RW)), s([B.rww, w.inst('pfxid')], 'syl',
                                                                                                     '( %s -> ( %s prefix ( # ` %s ) ) = %s )' % (ph, RW, RW, RW))],
           'eqtrd', '( %s -> %s = %s )' % (ph, DA.PJ(NLG), RW))
    rr2 = s([s([pf], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` %s ) )' % (ph, DA.PJ(NLG), RW)), s([B.ww, w.inst('revrev')], 'syl',
                                                                                                    '( %s -> ( reverse ` %s ) = W )' % (ph, RW))],
            'eqtrd', '( %s -> ( reverse ` %s ) = W )' % (ph, DA.PJ(NLG)))
    dj = s([s([rr2], 'fveq2d', '( %s -> ( DivisorsOf ` ( reverse ` %s ) ) = %s )' % (ph, DA.PJ(NLG), DV_))], 'fveq2d', '( %s -> %s = %s )' % (ph, DA.DJ(NLG), DVW))
    r4, x4 = w.rewrite(nrm3, {RA: (DVW, s([rv, dj], 'eqtrd', '( %s -> %s = %s )' % (ph, RA, DVW)))}, ph)
    assert x4 == DFIN, x4
    t3, C3_, D3_, n3 = R3.tri, R3.C0, R3.cur, R3.n
    D30 = triple_D(D3_)
    t3, C3_, D3_, n3 = hrrw(w, ph, t3, C3_, D3_, n3, deq=clneq(w, ph, 'E', S, s([e3_, r4], 'eqtrd', '( %s -> %s = %s )' % (ph, D30, DFIN)), D30, DFIN))
    ln = s([s([B.ww, nzW], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. ( 0 ... ( # ` W ) ) ) )' % (ph, NLG)), w.inst('tmdvlen')], 'syl',
           '( %s -> ( # ` %s ) = ( 2 ^ %s ) )' % (ph, ACN, NLG))
    ln2 = s([ln, s([B.lg], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ ( # ` W ) ) )' % (ph, NLG))], 'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` W ) ) )' % (ph, ACN))
    rn, n3b = w.rewrite(n3, {'( # ` %s )' % ACN: ('( 2 ^ ( # ` W ) )', ln2)}, ph)
    assert n3b == UC, n3b
    t3, C3_, D3_, n3 = hrrw(w, ph, t3, C3_, D3_, n3, neq=rn)
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([pro1, t2, t3], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, PRO1, PRO2, REVT))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) ) )' % (ph, FTY, FCOL, PRO1, PRO2, REVT))
    finish(w, st, lab)
    return w.run()



def tmidvsl():
    lab = 'tmidvsl'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` divisorsOfF_le_B ` at the machine up to the bound: ~ tm2fdvs at the family of ` DivInv ` ( ` P\' ` a '
               'letter), the elements by ~ tmidvsi , the frame by ~ tmidvst .')
    s = w.s
    B = Dvs(w, ph, T)
    for j in range(3):
        B.deep('dvs', j)
    c, mk, cl = B.c, B.mk, B.cl
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmidvst', STMTS11['tmidvst']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, PRO1, PRO2, REVT))
    ex[FTY] = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    for k_, x_ in (('simp1', PRO1), ('simp2', PRO2), ('simp3', REVT)):
        ex[x_] = s([a2, w.inst(k_)], 'syl', '( %s -> %s )' % (ph, x_))
    per = s([s([], 'tmidvsi', STMTS11['tmidvsi'])], 'ralrimiva', '( %s -> %s )' % (PSI, PER))
    ex[PER] = lift_from(w, PSI, ph, per)
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex[WG(DK(3))] = B.S0.vals['3'][2]
    ex['%s e. ( TM2Stk ` T )' % DP] = None
    del ex['%s e. ( TM2Stk ` T )' % DP]
    tb(w, ph, cl, 'N'); tb(w, ph, cl, MM)
    ex['%s e. NN0' % UA] = cl.mem(UA, 'NN0')
    ex['%s e. NN0' % UC] = cl.mem(UC, 'NN0') if False else None
    P2W = '( 2 ^ ( # ` W ) )'
    cl.leaf(P2W, 'NN0', s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), B.nw], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, P2W)))
    ex['%s e. NN0' % UC] = cl.mem(UC, 'NN0')
    ex['2 e. NN0'] = closed(w, ph, '2nn0', '2 e. NN0')
    # D' is a stack assignment
    S1 = B.S0.upd('3', ENCL(RW, DK(3)), B.g(ENCL(RW, DK(3)), enclg(w, ph, RW, B.rww, DK(3), B.S0.vals['3'][2]))).upd('5', 'X', B.xw)
    ex['%s e. ( TM2Stk ` T )' % DP] = S1.memb
    NQ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
    ssq = s([s([], 'ssrab2', '%s C_ %s' % (NQ, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, NQ, S))
    POPI_ = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (S, PID, S)
    ex['A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (NQ, PID, S)] = s([ssq, ex[POPI_], w.inst('ssralv')], 'sylc',
                                                                         '( %s -> A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s )' % (ph, NQ, PID, S))
    st = Bld(w, ph, c, ex)(GTREE)
    st2 = s([st, w.inst('tm2fdvs')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    finish(w, st2, lab)
    return w.run()


def tmidvsb():
    lab = 'tmidvsb'
    T = numtree11(TREE_DVS)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` divisorsOfF_le_B ` at the machine ( ` x z a c s t = 5 3 7 6 0 1 ` ): a list ` Q ` of numbers below '
               '` 2 ^ b ` on ` 5 ` is replaced by ` ( divisorsOf Q ).1 ` , every other stack restored, within '
               '` ( ( divisorsOf Q ).2 + 1 ) B ( 12 ( # Q ) b + 22 ) ` steps (~ tmidvsl at the family, ~ tmdvgeo ).')
    s = w.s
    B = Dvs(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    eq = s([], 'eqid', '%s = %s' % (PF, PF))
    t, cc = inst(w, ph, 'tmidvsl', {PV: PF}, Bld(w, ph, c, {'%s = %s' % (PF, PF): s([eq], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}))
    C, D, n = triple_parts(cc)
    assert C == CS('dvs') and D == CLN('E', S, DFIN), (C, D)
    SUM = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NLG, YF)
    TMP = tb(w, ph, cl, MP_)
    TM1 = tb(w, ph, cl, MM)
    TN = tb(w, ph, cl, 'N')
    CC = CC_
    nlg = s([B.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
    geo = s([cl.mem(CC, 'NN0'), nlg, w.inst('tmdvgeo')], 'syl2anc', '( %s -> ( %s + 2 ) <_ ( ( 2 ^ %s ) x. ( ( 2 x. %s ) + 2 ) ) )' % (ph, SUM, NLG, CC))
    P2W = '( 2 ^ ( # ` W ) )'
    geo2 = s([geo, s([s([B.lg], 'oveq2d', '( %s -> ( 2 ^ %s ) = %s )' % (ph, NLG, P2W))], 'oveq1d',
                     '( %s -> ( ( 2 ^ %s ) x. ( ( 2 x. %s ) + 2 ) ) = ( %s x. ( ( 2 x. %s ) + 2 ) ) )' % (ph, NLG, CC, P2W, CC))], 'breqtrd',
             '( %s -> ( %s + 2 ) <_ ( %s x. ( ( 2 x. %s ) + 2 ) ) )' % (ph, SUM, P2W, CC))
    # the sum is a real number: from the geometric bound's left side
    cl.leaf(P2W, 'NN0', s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), B.nw], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, P2W)))
    # the target: ( ( 2nd DivOf ) + 1 ) = 2 ^ # W , TMB ( 12 # W N + 22 ) = 27 TMB MP_
    ce = s([B.ww, w.inst('divisorsofcsteq')], 'syl', '( %s -> ( ( 2nd ` %s ) + 1 ) = %s )' % (ph, DV_, P2W))
    ARG = '( ( ( ; 1 2 x. ( # ` W ) ) x. N ) + ; 2 2 )'
    TA = '( TMB ` %s )' % ARG
    sc = s([closed(w, ph, '2nn0', '2 e. NN0'), cl.mem(MP_, 'NN0'), w.inst('tplbscale')], 'syl2anc',
           '( %s -> ( ( ( 2 + 1 ) ^ 3 ) x. %s ) = ( TMB ` ( ( ( 2 + 1 ) x. %s ) + ( 2 x. 2 ) ) ) )' % (ph, TMP, MP_))
    ae = lineq(w, ph, '( ( ( 2 + 1 ) x. %s ) + ( 2 x. 2 ) )' % MP_, ARG, closure=cl, products=True)
    sc2 = s([sc, s([ae], 'fveq2d', '( %s -> ( TMB ` ( ( ( 2 + 1 ) x. %s ) + ( 2 x. 2 ) ) ) = %s )' % (ph, MP_, TA))], 'eqtrd',
            '( %s -> ( ( ( 2 + 1 ) ^ 3 ) x. %s ) = %s )' % (ph, TMP, TA))
    e27 = s([s([s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq1i', '( ( 2 + 1 ) ^ 3 ) = ( 3 ^ 3 )'), num.mul_lits(w, '( 3 ^ 3 )', '; 2 7') if False else
             s([], '3exp3', '( 3 ^ 3 ) = ; 2 7')], 'eqtri', '( ( 2 + 1 ) ^ 3 ) = ; 2 7')
    ta = s([s([s([e27], 'oveq1i', '( ( ( 2 + 1 ) ^ 3 ) x. %s ) = ( ; 2 7 x. %s )' % (TMP, TMP))], 'a1i',
              '( %s -> ( ( ( 2 + 1 ) ^ 3 ) x. %s ) = ( ; 2 7 x. %s ) )' % (ph, TMP, TMP)), sc2], 'eqtr3d', '( %s -> ( ; 2 7 x. %s ) = %s )' % (ph, TMP, TA))
    BND = '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (DV_, TA)
    RHS2 = '( %s x. ( ; 2 7 x. %s ) )' % (P2W, TMP)
    rr = s([ce, s([ta], 'eqcomd', '( %s -> %s = ( ; 2 7 x. %s ) )' % (ph, TA, TMP))], 'oveq12d', '( %s -> %s = %s )' % (ph, BND, RHS2))
    # facts for the linear bound
    tp = s([B.nw, w.inst('tpl2pow')], 'syl', '( %s -> ( ( # ` W ) + 1 ) <_ %s )' % (ph, P2W))
    nmle = linarith(w, ph, [cl.ge0('N'), cl.ge0('( # ` W )')], 'N <_ %s' % MP_, closure=cl, products=True) if False else None
    m1 = s([cl.mem(MM, 'NN0'), cl.mem(MP_, 'NN0'), linarith(w, ph, [cl.ge0('N'), cl.ge0('( # ` W )')], '%s <_ %s' % (MM, MP_), closure=cl, products=True),
            w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TM1, TMP))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([cl.mem(MP_, 'NN0'), closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, MP_, TMP))
    cl2 = Closure(w, ph, {'N': ('NN0', B.nn)})
    cl2.leaf('( # ` W )', 'NN0', B.nw)
    tb(w, ph, cl2, MP_)
    big = nlinarith(w, ph, [qd, cl2.ge0(MP_)], '( %s + ; 1 6 ) <_ %s' % (MP_, TMP), closure=cl2, atoms=[MP_, TMP])
    # P2W x. TMP >= TMP , >= 16 P2W
    one = linarith(w, ph, [tp, cl.ge0('( # ` W )')], '1 <_ %s' % P2W, closure=cl)
    k1 = s([s([s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % ph), cl.mem(P2W, 'RR'), cl.mem(TMP, 'RR'), cl.ge0(TMP), one], 'lemul1ad',
           '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, TMP, P2W, TMP))
    k2 = s([cl.mem('( %s + ; 1 6 )' % MP_, 'RR'), cl.mem(TMP, 'RR'), cl.mem(P2W, 'RR'), cl.ge0(P2W), big], 'lemul2ad',
           '( %s -> ( %s x. ( %s + ; 1 6 ) ) <_ ( %s x. %s ) )' % (ph, P2W, MP_, P2W, TMP))
    k3 = s([cl.mem(TM1, 'RR'), cl.mem(TMP, 'RR'), cl.mem('( %s + 1 )' % P2W, 'RR'), cl.ge0('( %s + 1 )' % P2W), m1], 'lemul2ad',
           '( %s -> ( ( %s + 1 ) x. %s ) <_ ( ( %s + 1 ) x. %s ) )' % (ph, P2W, TM1, P2W, TMP))
    k4 = s([cl.mem('( ( # ` W ) + 1 )', 'RR'), cl.mem(P2W, 'RR'), cl.mem('N', 'RR'), cl.ge0('N'), tp], 'lemul1ad',
           '( %s -> ( ( ( # ` W ) + 1 ) x. N ) <_ ( %s x. N ) )' % (ph, P2W))
    # n <_ RHS2 : SUM enters only through geo2
    SUMR = SUM
    t16 = linarith(w, ph, [big, cl2.ge0(MP_)], '; 1 6 <_ %s' % TMP, closure=cl2, atoms=[MP_, TMP])
    h3 = s([s([s([], ';16re' if False else '1re', '1 e. RR')], 'id', '') if False else cl.mem('; 1 6', 'RR'), cl.mem(TMP, 'RR'), cl.mem(P2W, 'RR'), cl.ge0(P2W), t16],
           'lemul2ad', '( %s -> ( %s x. ; 1 6 ) <_ ( %s x. %s ) )' % (ph, P2W, P2W, TMP))
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLG)
    jn = s([s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NLG)), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
    YV = '( ( ( 2 ^ j ) + 1 ) x. %s )' % CC
    hy = s([s([s([], 'oveq2', '( i = j -> ( 2 ^ i ) = ( 2 ^ j ) )')], 'oveq1d', '( i = j -> ( ( 2 ^ i ) + 1 ) = ( ( 2 ^ j ) + 1 ) )')], 'oveq1d',
           '( i = j -> ( ( ( 2 ^ i ) + 1 ) x. %s ) = %s )' % (CC, YV))
    fvm = s([hy, s([], 'eqid', '%s = %s' % (YF, YF)), s([], 'ovex', '%s e. _V' % YV)], 'fvmpt', '( j e. NN0 -> ( %s ` j ) = %s )' % (YF, YV))
    fvj = s([jn, fvm], 'syl', '( %s -> ( %s ` j ) = %s )' % (pj, YF, YV))
    clj = Closure(w, pj, {'N': ('NN0', s([B.nn], 'adantr', '( %s -> N e. NN0 )' % pj)), 'j': ('NN0', jn)})
    clj.leaf('( # ` W )', 'NN0', s([B.nw], 'adantr', '( %s -> ( # ` W ) e. NN0 )' % pj))
    tb(w, pj, clj, MP_)
    clj.leaf('( 2 ^ j )', 'NN0', s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % pj), jn], 'nn0expcld', '( %s -> ( 2 ^ j ) e. NN0 )' % pj))
    yjn = s([s([fvj, clj.mem(YV, 'NN0')], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (pj, YF)), closed(w, pj, '2nn0', '2 e. NN0')], 'nn0addcld',
            '( %s -> ( ( %s ` j ) + 2 ) e. NN0 )' % (pj, YF))
    smn = s([s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NLG)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NLG)), yjn], 'fsumnn0cl', '( %s -> %s e. NN0 )' % (ph, SUM))
    cl.leaf(SUM, 'NN0', smn)
    X1 = '( ( ( %s + 2 ) + ( ( %s + 1 ) x. %s ) ) + ( ( %s x. ( ( 2 x. %s ) + 2 ) ) + 2 ) )' % (UA, P2W, TMP, P2W, CC)
    la = linarith(w, ph, [geo2, k3], '%s <_ %s' % (n, X1), closure=cl, atoms=[SUMR, P2W, TMP, TM1, 'N', '( # ` W )'], products=True)
    lb = linarith(w, ph, [k1, h3, big, tp, cl.ge0('N'), cl.ge0('( # ` W )'), cl.ge0(P2W), cl.ge0('( ( # ` W ) x. N )')], '%s <_ %s' % (X1, RHS2), closure=cl,
                  atoms=[P2W, TMP, 'N', '( # ` W )'], products=True)
    le2 = s([cl.mem(n, 'RR') if False else s([la], 'id', '') if False else None], 'id', '') if False else None
    le2 = linarith(w, ph, [la, lb], '%s <_ %s' % (n, RHS2), closure=cl, atoms=[SUMR, P2W, TMP, TM1, 'N', '( # ` W )'], products=True)
    le = s([s([rr], 'breq2d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, BND, n, RHS2)), le2], 'mpbird', '( %s -> %s <_ %s )' % (ph, n, BND))
    cl.leaf('( 2nd ` %s )' % DV_, 'NN0', s([s([s([B.ww, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, DV_)), w.inst('xp2nd')], 'syl',
                                            '( %s -> ( 2nd ` %s ) e. NN0 )' % (ph, DV_))], 'id', '') if False else
            s([s([B.ww, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, DV_)), w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (ph, DV_)))
    tb(w, ph, cl, ARG)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        if l != 'show':
            globals()[l]()
