"""T9: exSome at the machine (Lean ` exSome_runs ` ) on its installation predicate TMIexs.

  tmiexsa   the prefix ` prodLF snap t np s nu ; mulC nm t s np nu ; moveEntry s nm t ; appendList snap nu t s `
            (~ tmiprlb , ~ tmimulb , ~ tmime , ~ tmilappb )
  tmiexs    exSome_runs: the prefix, ` clear acc ` (~ tm2fclr ), ` dup nL t s ` , ` emptyTbl t acc s ` , ` exTest ` (~ tmiext )

    MM_DB=sorties/t9.mm python3 tools/gen/t9_f_exs.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import num
from t9_c_hdl import EI_TREE, ST_EI

SEL = sys.argv[1:]
LMS = FRAGS['exs'].lmap()
EGY = EWg('G', 'Y')
EFGY = EWg('F', EGY)
FPWGY = EWg(FPW, EGY)
WFP = '( encNatGam ` %s )' % FPW
WUR = ENCL('( W ++ U )', 'R')
TBW = '( TMB ` ( ( ( 2 x. ( ( # ` W ) + 1 ) ) x. B ) + 4 ) )'
T1 = LSUM('( ( ( # ` W ) + 1 ) x. %s )' % TBW, '( TMB ` H )', '( TMB ` H )', '( ( ( # ` W ) + 1 ) x. ( TMB ` B ) )')
DA = UPS('D', ('I', 'Z'), ('K0', FPWGY), ('J0', WUR))
ST_A = '( %s -> %s )' % (cj(TREE_EXS), TRI(CEN9('exs', 'D'), CLN(LMS['Q1'], S, DA), T1))


class Exs(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        s = w.s
        fn, gn, ln = c0['F e. NN0'], c0['G e. NN0'], c0['L e. NN0']
        vw, ww, uw = c0['S e. Word NN0'], c0['W e. Word NN0'], c0['U e. Word NN0']
        xw, x2w, zw, yw, rw = c0[WG('X')], c0[WG("X'")], c0[WG('Z')], c0[WG('Y')], c0[WG('R')]
        egy = ewg_(w, ph, 'G', gn, 'Y', yw)
        eqs = {'K': (ENCL('S', 'X'), enclg(w, ph, 'S', vw, 'X', xw)), 'J': (EWg('L', "X'"), ewg_(w, ph, 'L', ln, "X'", x2w)),
               'I': (ENCL('W', 'Z'), enclg(w, ph, 'W', ww, 'Z', zw)),
               'K0': (EFGY, ewg_(w, ph, 'F', fn, EGY, egy)), 'J0': (ENCL('U', 'R'), enclg(w, ph, 'U', uw, 'R', rw))}
        Base.__init__(self, w, ph, T, K8, 'exs', eqs)
        self.g(EGY, egy)
        self.fn, self.gn, self.ln, self.ww, self.uw = fn, gn, ln, ww, uw
        c = self.c
        self.bn, self.hn = c['B e. NN0'], c['H e. NN0']
        self.pw = s([s([ww, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` W ) e. ( NN0 X. NN0 ) )' % ph), w.inst('xp1st')], 'syl',
                    '( %s -> %s e. NN0 )' % (ph, PRW))
        self.fpw = s([fn, self.pw], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, FPW))
        self.cl = Closure(w, ph, {'B': ('NN0', self.bn), 'H': ('NN0', self.hn), 'L': ('NN0', ln)})
        for b in ('B', 'H'):
            tb = '( TMB ` %s )' % b
            self.cl.leaf(tb, 'NN0', s([s([c['%s e. NN0' % b], w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, tb))], 'nnnn0d',
                                      '( %s -> %s e. NN0 )' % (ph, tb)))
        self.cl.leaf('( # ` W )', 'NN0', s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph))

    def me_bound(self, t, tn, tlt, N='H'):
        """( ph -> ( ( 2 x. ( # ` ( encNatGam ` t ) ) ) + 4 ) <_ ( TMB ` N ) ) from t < 2 ^ N"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        WT = '( encNatGam ` %s )' % t
        LW = '( # ` %s )' % WT
        cl.leaf(LW, 'NN0', s([s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, WT)), w.inst('lencl')], 'syl',
                             '( %s -> %s e. NN0 )' % (ph, LW)))
        nn = self.c['%s e. NN0' % N]
        lw = s([s([tn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` %s ) ) )' % (ph, LW, t)),
                s([tn, nn, tlt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` %s ) ) <_ %s )' % (ph, t, N))],
               'eqbrtrd', '( %s -> %s <_ %s )' % (ph, LW, N))
        l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
        qd = s([nn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
               '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ ( TMB ` %s ) )' % (ph, N, N))
        return nlinarith(w, ph, [lw, qd, cl.ge0(N), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ ( TMB ` %s )' % (LW, N), closure=cl,
                         atoms=[N, LW, '( TMB ` %s )' % N])


def tmiexsa():
    lab = 'tmiexsa'
    ph = cj(TREE_EXS)
    w = W(lab, 'The prefix of Lean\'s ` exSome ` at the machine: ` prodLF snap t np s nu ` (~ tmiprlb ) pushes the product of '
               'the witness ` S ` on ` t ` , ` mulC nm t s np nu ` (~ tmimulb ) and ` moveEntry s nm t ` (~ tmime ) replace '
               '` m ` by ` m * prodL S ` , ` appendList snap nu t s ` (~ tmilappb ) moves ` S ` onto ` used ` .')
    B = Exs(w, ph, TREE_EXS)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    R = B.run()
    EPT = EWg(PRW, '( D ` I0 )')
    gpt = B.g(EPT, ewg_(w, ph, PRW, B.pw, '( D ` I0 )', B.S0.vals['I0'][2]))
    B.call(R, 'tmiprlb', {'K': 'I', 'J': 'I0', 'I': 'K', "I'": 'I"', 'I"': 'J0', 'L': 'W', 'R': 'Z', 'B': 'B',
                          'P': PL('P', 1), 'E': LMS['X1']}, {}, [('I0', EPT, gpt)])
    EFS = EWg(FPW, '( D ` I" )')
    gfs = B.g(EFS, ewg_(w, ph, FPW, B.fpw, '( D ` I" )', B.S0.vals['I"'][2]))
    B.call(R, 'tmimulb', {'K': 'K0', 'J': 'I0', 'I': 'I"', "I'": 'K', 'I"': 'J0', 'F': 'F', 'G': PRW, 'N': 'H', 'X': EGY,
                          'Y': '( D ` I0 )', 'P': PL('P', 2), 'E': LMS['X2']},
           {'%s e. NN0' % PRW: B.pw}, [('I"', EFS, gfs), ('K0', EGY, B.gam[EGY]), ('I0', '( D ` I0 )', B.gam['( D ` I0 )'])])
    gf2 = B.g(FPWGY, ewg_(w, ph, FPW, B.fpw, EGY, B.gam[EGY]))
    B.call(R, 'tmime', {'K': 'I"', 'J': 'K0', 'I': 'I0', 'W': WFP, 'X': '( D ` I" )', 'P': PL('P', 3), 'E': LMS['X3']},
           {WRD(WFP, BITS): engb(w, ph, FPW, B.fpw)}, [('I"', '( D ` I" )', B.gam['( D ` I" )']), ('K0', FPWGY, gf2)])
    gwu = B.g(WUR, enclg(w, ph, '( W ++ U )', s([B.ww, B.uw, w.inst('ccatcl')], 'syl2anc', '( %s -> ( W ++ U ) e. Word NN0 )' % ph),
                         'R', c[WG('R')]))
    B.call(R, 'tmilappb', {'K': 'I', 'J': 'J0', 'I': 'I"', "I'": 'I0', 'L': 'W', 'U': 'U', 'R': 'Z', "R'": 'R', 'B': 'B',
                           'P': PL('P', 4), 'E': LMS['Q1']}, {}, [('I', 'Z', B.gam['Z'] if 'Z' in B.gam else c[WG('Z')]), ('J0', WUR, gwu)])
    cur, out = R.normalize(K8)
    assert out == [('I', 'Z'), ('K0', FPWGY), ('J0', WUR)], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    pc = s([B.ww, w.inst('prodlcost')], 'syl', '( %s -> ( 2nd ` ( ProdL ` W ) ) = ( # ` W ) )' % ph)
    rn, n2 = w.rewrite(n, {'( 2nd ` ( ProdL ` W ) )': ('( # ` W )', pc)}, ph)
    me = B.me_bound(FPW, B.fpw, c['%s < ( 2 ^ H )' % FPW])
    ARG = '( ( ( 2 x. ( ( # ` W ) + 1 ) ) x. B ) + 4 )'
    cl.leaf(TBW, 'NN0', s([s([cl.mem(ARG, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TBW))], 'nnnn0d',
                          '( %s -> %s e. NN0 )' % (ph, TBW)))
    le2 = linarith(w, ph, [me], '%s <_ %s' % (n2, T1), closure=cl, products=True)
    le = s([s([rn], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, T1, n2, T1)), le2], 'mpbird', '( %s -> %s <_ %s )' % (ph, n, T1))
    hrle(w, ph, mk['phm'], t, C, D, n, T1, cl.mem(T1, 'NN0'), le, qed=True)
    return w.run()


def hdl_at(w, ph, mk, k, hdls_st, F):
    """( ph -> F e. ( S ^m ( S X. ( GK |_| 1o ) ) ) ) from ( ph -> F e. HDLS )"""
    s = w.s
    ge = mk['k'][k]['ge']
    d1 = s([ge, w.inst('djueq1')], 'syl', "( %s -> ( %s |_| 1o ) = ( Gamma' |_| 1o ) )" % (ph, GX(k)))
    x1 = s([d1], 'xpeq2d', "( %s -> ( %s X. ( %s |_| 1o ) ) = ( %s X. ( Gamma' |_| 1o ) ) )" % (ph, S, GX(k), S))
    o1 = s([x1], 'oveq2d', '( %s -> %s = %s )' % (ph, HDL(k), HDLS))
    return s([hdls_st, o1], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, F, HDL(k)))


def clear_extra(w, ph, mk, k):
    """the typings and the interface of ~ tm2fclr at readEmpty / !da on stack k"""
    s = w.s
    ei = s([mk['seq'], w.inst('tmcrdempi')], 'syl', '( %s -> %s )' % (ph, cj(EI_TREE)))
    p = parts(w, ph, ei, EI_TREE)
    TYE, TYC = EI_TREE[0]
    ex = {'%s e. %s' % (RDE, HDL(k)): hdl_at(w, ph, mk, k, p[TYE], RDE), TYC: p[TYC]}
    ge = mk['k'][k]['ge']
    body = '( %s ` ( %s ` <. r , ( inl ` z ) >. ) ) = 1o' % (CNDA, RDE)
    rq = s([ge], 'raleqdv', "( %s -> ( A. z e. %s %s <-> A. z e. Gamma' %s ) )" % (ph, GX(k), body, body))
    rq2 = s([rq], 'ralbidv', "( %s -> ( A. r e. %s A. z e. %s %s <-> A. r e. %s A. z e. Gamma' %s ) )" % (ph, S, GX(k), body, S, body))
    IZ = 'A. r e. %s A. z e. %s %s' % (S, GX(k), body)
    ex[IZ] = s([rq2, p[EI_TREE[1]]], 'mpbird', '( %s -> %s )' % (ph, IZ))
    ex[EI_TREE[2]] = p[EI_TREE[2]]
    return ex


def tmiexs():
    lab = 'tmiexs'
    ph = cj(TREE_EXS)
    w = W(lab, 'Lean\'s ` exSome_runs ` at the machine: wherever ` exSome np nL snap acc s t nm nu ` is installed, with the '
               'witness ` S ` on ` snap ` , ` m ` above ` n ` on ` nm ` , the table ` t\' ` on ` acc ` and ` used ` on ` nu ` , '
               '` m ` becomes ` m * prodL S ` , ` used ` becomes ` S ++ used ` , the table is reset to ` emptyTbl ` , ` S ` is '
               'consumed, and the exit test runs (~ tmiexsa , ` clear acc ` by ~ tm2fclr , ~ tmidupb , ~ tmietbb , ~ tmiext ), '
               'within ` exSomeC L N\' b # S bM ` steps.')
    B = Exs(w, ph, TREE_EXS)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    t0 = s([], 'tmiexsa', ST_A)
    # the stacks after the prefix
    SA = B.S0.upd('I', 'Z', B.g('Z', c[WG('Z')]))
    gf2 = B.g(FPWGY, ewg_(w, ph, FPW, B.fpw, EGY, B.gam[EGY]))
    SA = SA.upd('K0', FPWGY, gf2)
    gwu = B.g(WUR, enclg(w, ph, '( W ++ U )', s([B.ww, B.uw, w.inst('ccatcl')], 'syl2anc', '( %s -> ( W ++ U ) e. Word NN0 )' % ph),
                         'R', c[WG('R')]))
    SA = SA.upd('J0', WUR, gwu)
    assert SA.D == DA
    R = B.run(SA)
    ex = clear_extra(w, ph, mk, "I'")
    ex[LAB(LMS['X4'])] = B.ex[LAB(LMS['X4'])] if LAB(LMS['X4']) in B.ex else None
    B.deep('exs', 4)
    ex[LAB(LMS['X4'])] = B.ex[LAB(LMS['X4'])]
    B.call(R, 'tm2fclr', {'A': LMS['Q1'], 'E': LMS['X4'], 'K': "I'", 'F': RDE, 'C': CNDA}, ex,
           [("I'", '(/)', closed(w, ph, 'wrd0', "(/) e. Word Gamma'"))])
    ELT = EWg('L', '( D ` I0 )')
    gl = B.g(ELT, ewg_(w, ph, 'L', B.ln, '( D ` I0 )', B.S0.vals['I0'][2]))
    B.call(R, 'tmidupb', {'K': 'J', 'J': 'I0', 'I': 'I"', 'F': 'L', 'N': 'B', 'X': "X'", 'P': PL('P', 5), 'E': LMS['X5']},
           {}, [('I0', ELT, gl)])
    ACE = CC('( L encTblAsc EmptyTbl )', '( <" 0 "> ++ (/) )')
    ln0 = B.ln
    etw = s([s([ln0, closed(w, ph, 'ttetb0' if False else 'ttetb0', '')], 'id', '') if False else ln0], 'id', '') if False else None
    et = s([ln0, w.inst('ttetb0')], 'syl', '( %s -> ( L encTblAsc EmptyTbl ) = ( 3 repeatS L ) )' % ph)
    g3 = closed(w, ph, 'gamma3', "3 e. Gamma'")
    rw_ = s([g3, ln0, w.inst('repsw')], 'syl2anc', "( %s -> ( 3 repeatS L ) e. Word Gamma' )" % ph)
    etg = s([et, rw_], 'eqeltrd', "( %s -> ( L encTblAsc EmptyTbl ) e. Word Gamma' )" % ph)
    s0 = s([closed(w, ph, 'gamma0', "0 e. Gamma'")], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
    z0g = wgcat(w, ph, '<" 0 ">', '(/)', s0, closed(w, ph, 'wrd0', "(/) e. Word Gamma'"))
    gace = B.g(ACE, wgcat(w, ph, '( L encTblAsc EmptyTbl )', '( <" 0 "> ++ (/) )', etg, z0g))
    B.call(R, 'tmietbb', {'K': 'I0', 'J': "I'", 'I': 'I"', 'L': 'L', 'X': '( D ` I0 )', 'B': 'B', 'P': PL('P', 6), 'E': LMS['X6']},
           {}, [('I0', '( D ` I0 )', B.gam['( D ` I0 )']), ("I'", ACE, gace)])
    K3 = 'if ( %s , ( <" 3 "> ++ %s ) , %s )' % (HITW, ENCL('S', 'X'), ENCL('S', 'X'))
    k3g = s([wgcat(w, ph, '<" 3 ">', ENCL('S', 'X'), s([g3], 's1cld', "( %s -> <\" 3 \"> e. Word Gamma' )" % ph), B.S0.vals['K'][2]),
             B.S0.vals['K'][2]], 'ifcld', "( %s -> %s e. Word Gamma' )" % (ph, K3))
    B.g(K3, k3g)
    FIN = NFLi('( %s \\/ S = (/) )' % HITW)
    B.call(R, 'tmiext', {'F': FPW, 'G': 'G', 'N': 'H', 'S': 'S', 'X': 'X', 'Y': 'Y', 'P': PL('P', 7), 'E': 'E'},
           {'%s e. NN0' % FPW: B.fpw}, [('K', K3, k3g)])
    e, nrm, out2 = renorm(w, ph, B, R, [('I', 'Z'), ('K0', FPWGY), ('J0', WUR)], K8)
    assert out2 == [('K', K3), ('I', 'Z'), ("I'", ACE), ('K0', FPWGY), ('J0', WUR)], out2
    # K3 with ( D ` K ), ACE as ACCW( EmptyTbl )
    kc = s([c['( D ` K ) = %s' % ENCL('S', 'X')]], 'eqcomd', '( %s -> %s = ( D ` K ) )' % (ph, ENCL('S', 'X')))
    cr = s([s0, w.inst('ccatrid')], 'syl', '( %s -> ( <" 0 "> ++ (/) ) = <" 0 "> )' % ph)
    ae = s([cr], 'oveq2d', '( %s -> %s = %s )' % (ph, ACE, ACCW('EmptyTbl')))
    r2, x2 = w.rewrite(nrm, {ENCL('S', 'X'): ('( D ` K )', kc), ACE: (ACCW('EmptyTbl'), ae)}, ph)
    assert x2 == DFIN_EXS, x2
    Dc = triple_D(R.cur)
    deq = s([e, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, Dc, DFIN_EXS))
    t, C, D, n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, 'E', FIN, deq, Dc, DFIN_EXS))
    t2 = hrseq(w, ph, mk['phm'], t0, t, CEN9('exs', 'D'), CLN(LMS['Q1'], S, DA), D, T1, n)
    NT = '( %s + %s )' % (T1, n)
    # the bound: # ( D ` I' ) + 1 <_ L ( N ( B + 1 ) + 1 ) + 2
    AT = '( L encTblAsc A )'
    an = c['A e. Tbl']
    atw = tblw(w, ph, 'A', an, 'L', B.ln)
    la = s([s([c["( D ` I' ) = %s" % ACCW('A')]], 'fveq2d', "( %s -> ( # ` ( D ` I' ) ) = ( # ` %s ) )" % (ph, ACCW('A'))),
            s([atw, w.inst('ccatws1len')], 'syl', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (ph, ACCW('A'), AT))], 'eqtrd',
           "( %s -> ( # ` ( D ` I' ) ) = ( ( # ` %s ) + 1 ) )" % (ph, AT))
    tl = s([s([s([B.ln, an], 'jca', '( %s -> ( L e. NN0 /\\ A e. Tbl ) )' % ph), s([c['N e. NN0'], B.bn], 'jca', '( %s -> ( N e. NN0 /\\ B e. NN0 ) )' % ph),
              c[TBB('A')]], '3jca', '( %s -> ( ( L e. NN0 /\\ A e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 ) /\\ %s ) )' % (ph, TBB('A'))),
            w.inst('ttabtbll')], 'syl', '( %s -> ( # ` %s ) <_ ( L x. ( ( N x. ( B + 1 ) ) + 1 ) ) )' % (ph, AT))
    cl.leaf('( # ` %s )' % AT, 'NN0', s([atw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, AT)))
    cl.leaf("( # ` ( D ` I' ) )", 'NN0', s([B.S0.vals["I'"][2], w.inst('lencl')], 'syl', "( %s -> ( # ` ( D ` I' ) ) e. NN0 )" % ph))
    cl.leaf('N', 'NN0', c['N e. NN0'])
    ARG = '( ( ( 2 x. ( ( # ` W ) + 1 ) ) x. B ) + 4 )'
    cl.leaf(TBW, 'NN0', s([s([cl.mem(ARG, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TBW))], 'nnnn0d',
                          '( %s -> %s e. NN0 )' % (ph, TBW)))
    BND = EXSOMEC('L', 'N', 'B', '( # ` W )', 'H')
    DAI = "( # ` ( %s ` I' ) )" % DA
    dai = s([SA.vals["I'"][1]], 'fveq2d', "( %s -> %s = ( # ` ( D ` I' ) ) )" % (ph, DAI))
    cl.leaf(DAI, 'NN0', s([s([SA.vals["I'"][1], B.S0.vals["I'"][2]], 'eqeltrd', "( %s -> ( %s ` I' ) e. Word Gamma' )" % (ph, DA)),
                           w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, DAI)))
    le = linarith(w, ph, [la, tl, dai], '%s <_ %s' % (NT, BND), closure=cl, products=True)
    hrle(w, ph, mk['phm'], t2, CEN9('exs', 'D'), D, NT, BND, cl.mem(BND, 'NN0'), le, qed=True)
    return w.run()




if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
