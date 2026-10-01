"""T9: exPre at the machine (Lean ` exPre_runs ` ) on its installation predicate TMIexp.

  tmiexpa   ` copyTbl acc snap np s t ; dpStepF np nL snap acc s t ` (~ tmictbb , ~ tmidpsb )
  tmiexpb   ` pushNum t 1 ; dup nL snap s ; modC t snap np acc s nu ` (~ tm2fpshn , ~ tmidupb , ~ tmimodcb )
  tmiexp    exPre_runs: the two parts, ` lookupSlot acc t snap s np ` (~ tmilksb ), ` peekKet snap ` (~ tm2lpk )

    MM_DB=sorties/t9.mm python3 tools/gen/t9_g_exp.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import num

SEL = sys.argv[1:]
LMP_ = FRAGS['exp'].lmap()
A1 = DP1('L', 'F', 'A')
ACC0 = lambda a: '( ( L encTblAsc %s ) ++ ( <" 0 "> ++ (/) ) )' % a
TB = '( TMB ` B )'
T1 = LSUM('( ( ( L + 1 ) x. ( N + 2 ) ) x. %s )' % TB, '( ( ( ( L + 1 ) ^ 2 ) x. ( N + 2 ) ) x. %s )' % TB)
T2 = LSUM(TB, TB, TB)
DA1 = UPS('D', ('K', 'X'), ("I'", ACC0(A1)))
ML = '( 1 mod L )'
DB1 = UPS('D', ('K', 'X'), ("I'", ACC0(A1)), ('I0', EWg(ML, '( D ` I0 )')))
ST_A = '( %s -> %s )' % (cj(TREE_EXP), TRI(CEN9('exp', 'D'), CLN(LMP_['Q1'], S, DA1), T1))
ST_B = '( %s -> %s )' % (cj(TREE_EXP), TRI(CLN(LMP_['Q1'], S, DA1), CLN(LMP_['X4'], S, DB1), T2))


class Exp(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        s = w.s
        fn, ln, an = c0['F e. NN0'], c0['L e. NN'], c0['A e. Tbl']
        l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
        xw, yw = c0[WG('X')], c0[WG('Y')]
        eqs = {'K': (EWg('F', 'X'), ewg_(w, ph, 'F', fn, 'X', xw)), 'J': (EWg('L', 'Y'), ewg_(w, ph, 'L', l0, 'Y', yw))}
        Base.__init__(self, w, ph, T, K7P, 'exp', eqs)
        c = self.c
        self.fn, self.ln, self.l0, self.an = fn, ln, l0, an
        self.bn, self.nn = c['B e. NN0'], c['N e. NN0']
        # acc as ( L encTblAsc A ) ++ ( <" 0 "> ++ (/) )
        s0 = s([closed(w, ph, 'gamma0', "0 e. Gamma'")], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        self.s0 = s0
        cr = s([s0, w.inst('ccatrid')], 'syl', '( %s -> ( <" 0 "> ++ (/) ) = <" 0 "> )' % ph)
        self.cr = cr
        e0 = s([cr], 'oveq2d', '( %s -> %s = %s )' % (ph, ACC0('A'), ACCW('A')))
        av = s([c["( D ` I' ) = %s" % ACCW('A')], e0], 'eqtr4d', "( %s -> ( D ` I' ) = %s )" % (ph, ACC0('A')))
        z0g = wgcat(w, ph, '<" 0 ">', '(/)', s0, closed(w, ph, 'wrd0', "(/) e. Word Gamma'"))
        self.z0g = self.g('( <" 0 "> ++ (/) )', z0g)
        g = self.g(ACC0('A'), wgcat(w, ph, '( L encTblAsc A )', '( <" 0 "> ++ (/) )', tblw(w, ph, 'A', an, 'L', l0), z0g))
        self.S0.vals["I'"] = (ACC0('A'), av, g)
        self.g('(/)', closed(w, ph, 'wrd0', "(/) e. Word Gamma'"))
        self.g('X', xw); self.g('Y', yw)
        self.a1 = s([s([s([ln, fn], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % ph), an], 'jca',
                       '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) )' % ph), w.inst('dpstepcl')], 'syl',
                    '( %s -> %s e. ( Tbl X. NN0 ) )' % (ph, DPS_('L', 'F', 'A')))
        self.a1t = s([self.a1, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, A1))
        self.cl = Closure(w, ph, {'B': ('NN0', self.bn), 'N': ('NN0', self.nn), 'L': ('NN0', l0)})
        self.cl.leaf(TB, 'NN0', s([s([self.bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d',
                                  '( %s -> %s e. NN0 )' % (ph, TB)))

    def sa(self):
        g = self.g(ACC0(A1), wgcat(self.w, self.ph, '( L encTblAsc %s )' % A1, '( <" 0 "> ++ (/) )',
                                   tblw(self.w, self.ph, A1, self.a1t, 'L', self.l0), self.z0g))
        return self.S0.upd('K', 'X', self.gam['X']).upd("I'", ACC0(A1), g)


def tmiexpa():
    lab = 'tmiexpa'
    ph = cj(TREE_EXP)
    w = W(lab, 'The first half of Lean\'s ` exPre ` at the machine: ` copyTbl acc snap np s t ` (~ tmictbb ) snapshots the '
               'table onto ` snap ` , ` dpStepF np nL snap acc s t ` (~ tmidpsb ) runs the DP step at the pool element ` p ` .')
    B = Exp(w, ph, TREE_EXP)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    R = B.run()
    DSC = '( ( L encTblDesc A ) ++ ( <" 0 "> ++ ( D ` I ) ) )'
    j = s([B.an, B.l0], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ph)
    RS = '( A |` ( 0 ..^ L ) )'
    bb = s([j, w.inst('tttbles')], 'syl', '( %s -> ( ( L encTblAsc A ) = ( encSlots ` %s ) /\\ ( L encTblDesc A ) = ( encSlots ` ( reverse ` %s ) ) ) )'
           % (ph, RS, RS))
    tw = s([s([j, w.inst('tttblw')], 'syl', '( %s -> ( %s e. Word ( Word NN0 |_| 1o ) /\\ ( # ` %s ) = L ) )' % (ph, RS, RS))],
           'simpld', '( %s -> %s e. Word ( Word NN0 |_| 1o ) )' % (ph, RS))
    rw_ = s([tw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word ( Word NN0 |_| 1o ) )' % (ph, RS))
    dsg = s([s([bb], 'simprd', '( %s -> ( L encTblDesc A ) = ( encSlots ` ( reverse ` %s ) ) )' % (ph, RS)),
             s([rw_, w.inst('ttsescl')], 'syl', "( %s -> ( encSlots ` ( reverse ` %s ) ) e. Word Gamma' )" % (ph, RS))], 'eqeltrd',
            "( %s -> ( L encTblDesc A ) e. Word Gamma' )" % ph)
    gds = B.g(DSC, wgcat(w, ph, '( L encTblDesc A )', '( <" 0 "> ++ ( D ` I ) )', dsg, wg4(w, ph, '( D ` I )', B.S0.vals['I'][2]) if False else
                         wgcat(w, ph, '<" 0 ">', '( D ` I )', B.s0, B.S0.vals['I'][2])))
    B.call(R, 'tmictbb', {'K': "I'", 'J': 'I', 'I': 'K', "I'": 'I"', 'I"': 'I0', 'A': 'A', 'L': 'L', 'X': '(/)', 'N': 'N', 'B': 'B',
                          'P': PL('P', 3), 'E': LMP_['X1']}, {'L e. NN0': B.l0}, [('I', DSC, gds)])
    gA1 = B.g(ACC0(A1), wgcat(w, ph, '( L encTblAsc %s )' % A1, '( <" 0 "> ++ (/) )', tblw(w, ph, A1, B.a1t, 'L', B.l0), B.z0g))
    B.call(R, 'tmidpsb', {'K': 'K', 'J': 'J', 'I': 'I', "I'": "I'", 'I"': 'I"', 'I0': 'I0', 'F': 'F', 'L': 'L', 'A': 'A', 'N': 'N',
                          'B': 'B', 'X': 'X', 'Y': 'Y', 'R': '( D ` I )', 'U': '(/)', 'P': PL('P', 4), 'E': LMP_['Q1']}, {},
           [('K', 'X', B.gam['X']), ('I', '( D ` I )', B.gam['( D ` I )']),
            ("I'", ACC0(A1), gA1)])
    cur, out = R.normalize(K7P)
    assert out == [('K', 'X'), ("I'", ACC0(A1))], out
    assert R.n == T1, R.n
    assert concl(w, ph, R.tri) == ST_A[len(ph) + 6:-2], concl(w, ph, R.tri)
    qed_as(w, R.tri, ST_A)
    return w.run()



def tb16(w, ph, cl, bn, b='B'):
    """( ph -> ; 1 6 <_ ( TMB ` b ) )"""
    s = w.s
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ ( TMB ` %s ) )' % (ph, b, b))
    return nlinarith(w, ph, [qd, cl.ge0(b)], '; 1 6 <_ ( TMB ` %s )' % b, closure=cl, atoms=[b, '( TMB ` %s )' % b])


def tmiexpb():
    lab = 'tmiexpb'
    ph = cj(TREE_EXP)
    w = W(lab, 'The middle of Lean\'s ` exPre ` at the machine: ` pushNum t 1 ` (two pushes), ` dup nL snap s ` (~ tmidupb ) '
               'and ` modC t snap np acc s nu ` (~ tmimodcb ) leave ` 1 mod L ` on ` t ` .')
    B = Exp(w, ph, TREE_EXP)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    SA = B.sa()
    R = B.run(SA)
    J4 = '( <" 4 "> ++ ( D ` I0 ) )'
    g4 = B.g(J4, wg4(w, ph, '( D ` I0 )', B.S0.vals['I0'][2]))
    B.call(R, 'tm2fpshn', {'A': PL('P', 0), 'E': PL('P', 1), 'K': 'I0', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('I0'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['I0']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('I0')))},
           [('I0', J4, g4)])
    J41 = '( <" %s "> ++ %s )' % (B1, J4)
    bg = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1))
    g41 = B.g(J41, wgcat(w, ph, '<" %s ">' % B1, J4, s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1)), g4))
    B.call(R, 'tm2fpshn', {'A': PL('P', 1), 'E': LMP_['X2'], 'K': 'I0', 'Z': B1, 'N': S},
           {'%s e. %s' % (B1, GX('I0')): s([bg, mk['k']['I0']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1, GX('I0')))},
           [('I0', J41, g41)])
    ELI = EWg('L', '( D ` I )')
    gli = B.g(ELI, ewg_(w, ph, 'L', B.l0, '( D ` I )', B.S0.vals['I'][2]))
    B.call(R, 'tmidupb', {'K': 'J', 'J': 'I', 'I': 'I"', 'F': 'L', 'N': 'B', 'X': 'Y', 'P': PL('P', 5), 'E': LMP_['X3']},
           {'L e. NN0': B.l0}, [('I', ELI, gli)])
    S3 = R.S
    E1 = EWg('1', '( D ` I0 )')
    e1 = s([S3.vals['I0'][1], s([B.S0.vals['I0'][2], w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (ph, E1, J41))], 'eqtr4d',
           '( %s -> ( %s ` I0 ) = %s )' % (ph, S3.D, E1))
    lge1 = s([B.ln, w.inst('nnge1')], 'syl', '( %s -> 1 <_ L )' % ph)
    two = s([s([closed(w, ph, '2nn', '2 e. NN'), B.bn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ B ) e. NN )' % ph)], 'nnred',
            '( %s -> ( 2 ^ B ) e. RR )' % ph)
    one = s([closed(w, ph, '1re', '1 e. RR'), s([B.ln], 'nnred', '( %s -> L e. RR )' % ph), two, lge1, c['L < ( 2 ^ B )']], 'lelttrd',
            '( %s -> 1 < ( 2 ^ B ) )' % ph)
    EML = EWg(ML, '( D ` I0 )')
    mln = s([closed(w, ph, '1z', '1 e. ZZ'), B.ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ML))
    gml = B.g(EML, ewg_(w, ph, ML, mln, '( D ` I0 )', B.S0.vals['I0'][2]))
    B.call(R, 'tmimodcb', {'K': 'I0', 'J': 'I', 'I': 'K', "I'": "I'", 'I"': 'I"', 'I0': 'J0', 'F': '1', 'G': 'L', 'N': 'B',
                           'X': '( D ` I0 )', 'Y': '( D ` I )', 'P': PL('P', 6), 'E': LMP_['X4']},
           {'( %s ` I0 ) = %s' % (S3.D, E1): e1, '1 e. NN0': closed(w, ph, '1nn0', '1 e. NN0'), '1 < ( 2 ^ B )': one},
           [('I0', EML, gml), ('I', '( D ` I )', B.gam['( D ` I )'])])
    e, nrm, out2 = renorm(w, ph, B, R, [('K', 'X'), ("I'", ACC0(A1))], K7P)
    assert nrm == DB1, nrm
    Dc = triple_D(R.cur)
    t, C, D, n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, LMP_['X4'], S, e, Dc, DB1))
    t16 = tb16(w, ph, cl, B.bn)
    le = linarith(w, ph, [t16], '%s <_ %s' % (n, T2), closure=cl, atoms=[TB])
    hrle(w, ph, mk['phm'], t, C, D, n, T2, cl.mem(T2, 'NN0'), le, qed=True)
    return w.run()



def tmiexp():
    lab = 'tmiexp'
    ph = cj(TREE_EXP)
    w = W(lab, 'Lean\'s ` exPre_runs ` at the machine: wherever ` exPre np nL snap acc s t nu ` is installed, with ` p ` on ` np ` , '
               '` L ` on ` nL ` and the table on ` acc ` , the DP step runs, ` p ` is consumed, the slot ` 1 mod L ` of the new table '
               'is pushed on ` snap ` and the flag records whether it is empty (~ tmiexpa , ~ tmiexpb , ~ tmilksb , ~ tm2lpk ), '
               'within ` exPreC L N b ` steps.')
    B = Exp(w, ph, TREE_EXP)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    ta = s([], 'tmiexpa', ST_A)
    tb = s([], 'tmiexpb', ST_B)
    t01 = hrseq(w, ph, mk['phm'], ta, tb, CEN9('exp', 'D'), CLN(LMP_['Q1'], S, DA1), CLN(LMP_['X4'], S, DB1), T1, T2)
    SA = B.sa()
    mln = s([closed(w, ph, '1z', '1 e. ZZ'), B.ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ML))
    EML = EWg(ML, '( D ` I0 )')
    gml = B.g(EML, ewg_(w, ph, ML, mln, '( D ` I0 )', B.S0.vals['I0'][2]))
    SB = SA.upd('I0', EML, gml)
    R = B.run(SB)
    G_ = '( encodeNat ` %s )' % ML
    gw = s([mln, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, G_))
    ev = s([mln, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (ph, ML, G_))
    IBW = CC('( inclBool o. %s )' % G_, '( <" 4 "> ++ ( D ` I0 ) )')
    i0v = s([SB.vals['I0'][1], s([ev], 'oveq1d', '( %s -> %s = %s )' % (ph, EML, IBW))], 'eqtrd', '( %s -> ( %s ` I0 ) = %s )' % (ph, SB.D, IBW))
    lrp = s([B.ln], 'nnrpd', '( %s -> L e. RR+ )' % ph)
    mlt = s([closed(w, ph, '1re', '1 e. RR'), lrp, w.inst('modlt')], 'syl2anc', '( %s -> %s < L )' % (ph, ML))
    tn = s([mln, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = %s )' % (ph, G_, ML))
    tlt = s([tn, mlt], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (ph, G_))
    two = s([s([closed(w, ph, '2nn', '2 e. NN'), B.bn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ B ) e. NN )' % ph)], 'nnred',
            '( %s -> ( 2 ^ B ) e. RR )' % ph)
    mlp = s([s([mln], 'nn0red', '( %s -> %s e. RR )' % (ph, ML)), s([B.ln], 'nnred', '( %s -> L e. RR )' % ph), two, mlt, c['L < ( 2 ^ B )']],
            'lttrd', '( %s -> %s < ( 2 ^ B ) )' % (ph, ML))
    glen = s([mln, B.bn, mlp, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` %s ) <_ B )' % (ph, G_))
    cl.leaf('( # ` %s )' % G_, 'NN0', s([gw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, G_)))
    g2b = linarith(w, ph, [glen, cl.ge0('B')], '( # ` %s ) <_ ( 2 x. B )' % G_, closure=cl)
    tb1 = s([s([s([B.ln, B.fn, B.an], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) )' % ph),
                s([B.nn, B.bn, c['F < ( 2 ^ B )']], '3jca', '( %s -> ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) )' % ph), c[TBB('A')]], '3jca',
               '( %s -> ( ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) /\\ %s ) )' % (ph, TBB('A'))),
             w.inst('ttabtbdp')], 'syl', '( %s -> %s )' % (ph, TBB(A1, '( N + 1 )')))
    SL2 = '( %s ` ( toNat ` %s ) )' % (A1, G_)
    ESL2 = '( ( encSlot ` %s ) ++ ( D ` I ) )' % SL2
    slt = s([B.a1t, s([s([gw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, G_))], 'id', '') if False else
             s([gw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, G_)), w.inst('tblfv')], 'syl2anc',
            '( %s -> %s e. ( Word NN0 |_| 1o ) )' % (ph, SL2))
    esw = s([slt, s([s([], 'ttabslotf', "encSlot : ( Word NN0 |_| 1o ) --> Word Gamma'")], 'ffvelcdmi',
                    "( %s e. ( Word NN0 |_| 1o ) -> ( encSlot ` %s ) e. Word Gamma' )" % (SL2, SL2))], 'syl',
            "( %s -> ( encSlot ` %s ) e. Word Gamma' )" % (ph, SL2))
    gsl = B.g(ESL2, wgcat(w, ph, '( encSlot ` %s )' % SL2, '( D ` I )', esw, B.S0.vals['I'][2]))
    B.call(R, 'tmilksb', {'K': "I'", 'J': 'I0', 'I': 'I', "I'": 'I"', 'I"': 'K', 'A': A1, 'L': 'L', 'G': G_, 'N': '( N + 1 )', 'B': 'B',
                          'X': '( <" 0 "> ++ (/) )', 'Y': '( D ` I0 )', 'P': PL('P', 7), 'E': PL('P', 2)},
           {'( %s ` I0 ) = %s' % (SB.D, IBW): i0v, '%s e. Tbl' % A1: B.a1t, 'L e. NN0': B.l0, '%s e. Word 2o' % G_: gw,
            '( N + 1 ) e. NN0': s([B.nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph),
            '( # ` %s ) <_ ( 2 x. B )' % G_: g2b, '( toNat ` %s ) < L' % G_: tlt, TBB(A1, '( N + 1 )'): tb1},
           [('I0', '( D ` I0 )', B.gam['( D ` I0 )']), ('I', ESL2, gsl)])
    # peekKet snap
    V = ESL2
    en = s([slt, w.inst('ttslotn0')], 'syl', '( %s -> ( encSlot ` %s ) =/= (/) )' % (ph, SL2))
    c0 = s([esw, B.S0.vals['I'][2], w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( ( encSlot ` %s ) = (/) /\\ ( D ` I ) = (/) ) ) )' % (ph, V, SL2))
    n1 = s([s([en], 'neneqd', '( %s -> -. ( encSlot ` %s ) = (/) )' % (ph, SL2))], 'intnanrd',
           '( %s -> -. ( ( encSlot ` %s ) = (/) /\\ ( D ` I ) = (/) ) )' % (ph, SL2))
    vn0 = s([s([c0, n1], 'mtbird', '( %s -> -. %s = (/) )' % (ph, V))], 'neqned', '( %s -> %s =/= (/) )' % (ph, V))
    S4 = R.S
    eq, hg, tg = A8.word_split(w, ph, V, S4.vals['I'][2], vn0)
    HD, TL = A8.HD0(V), A8.TL1(V)
    kv = s([S4.vals['I'][1], eq], 'eqtrd', '( %s -> ( %s ` I ) = ( <" %s "> ++ %s ) )' % (ph, S4.D, HD, TL))
    sk = s([slt, B.S0.vals['I'][2], w.inst('ttabslotk')], 'syl2anc', '( %s -> ( %s = 3 <-> %s = ( inr ` (/) ) ) )' % (ph, HD, SL2))
    sle = s([s([tn], 'fveq2d', '( %s -> %s = %s )' % (ph, SL2, SLP))], 'eqeq1d', '( %s -> ( %s = ( inr ` (/) ) <-> %s = ( inr ` (/) ) ) )' % (ph, SL2, SLP))
    ifeq = s([s([sk, sle], 'bitrd', '( %s -> ( %s = 3 <-> %s = ( inr ` (/) ) ) )' % (ph, HD, SLP))], 'ifbid',
             '( %s -> if ( %s = 3 , 1o , (/) ) = if ( %s = ( inr ` (/) ) , 1o , (/) ) )' % (ph, HD, SLP))
    FL = 'if ( %s = ( inr ` (/) ) , 1o , (/) )' % SLP
    pk = A8.peek_iface(w, ph, mk, RDK, HD, hg, ifeq, FL)
    B.call(R, 'tm2lpk', {'A': PL('P', 2), 'E': 'E', 'K': 'I', 'F': RDK, 'Z': HD, 'X': TL, 'N': S, "N'": NFL(FL)},
           {'( %s ` I ) = ( <" %s "> ++ %s )' % (S4.D, HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg, SSS(NFL(FL)): B.ss(NFL(FL)),
            'A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDK, HD, NFL(FL)): pk}, [])
    e, nrm, out2 = renorm(w, ph, B, R, [('K', 'X'), ("I'", ACC0(A1)), ('I0', EML)], K7P)
    e0 = s([B.cr], 'oveq2d', '( %s -> %s = %s )' % (ph, ACC0(A1), ACCW(A1)))
    r2, x2 = w.rewrite(nrm, {SL2: (SLP, s([tn], 'fveq2d', '( %s -> %s = %s )' % (ph, SL2, SLP))), ACC0(A1): (ACCW(A1), e0)}, ph)
    assert x2 == DFIN_EXP, x2
    Dc = triple_D(R.cur)
    t2, C2, D2, n2 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, 'E', NFL(FL), s([e, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, Dc, DFIN_EXP)),
                                                                   Dc, DFIN_EXP))
    t3 = hrseq(w, ph, mk['phm'], t01, t2, CEN9('exp', 'D'), CLN(LMP_['X4'], S, DB1), D2, '( %s + %s )' % (T1, T2), n2)
    NT = '( ( %s + %s ) + %s )' % (T1, T2, n2)
    BND = EXPREC('L', 'N', 'B')
    le = linarith(w, ph, [], '%s <_ %s' % (NT, BND), closure=cl, products=True)
    hrle(w, ph, mk['phm'], t3, CEN9('exp', 'D'), D2, NT, BND, cl.mem(BND, 'NN0'), le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
