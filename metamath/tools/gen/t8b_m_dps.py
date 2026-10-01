"""T8b: dpStepF at the machine (Lean ` dpStepF_runs ` , ` dpStepF_le_B ` ) on its installation predicate TMIdps.

  tmidpsa   the prologue ` dup nL t s ; dup np nL s ; modFrag nL t np snap s acc ` (~ tmidup , ~ tmimodf )
  tmidpsp   ` dup np snap s ; dup nL np s ; setIfNoneF acc np snap s t ; pushNum nL 0 ` after the push of ` bra `
            (~ tmidup , ~ tmisint , ~ tm2fpshn )
  tmidpse   the epilogue ` dropNum nL ; dropNum nL ; dropNum np ` (~ tmidrop , ~ ttrrs , ~ ttaccl )
  tmidpsi   one iteration of the slot loop: ~ tmidpb at the residue and accumulator sequences, the peek
  tmidpst   the frame of the loop
  tmidpsl   ~ tm2fdps assembled, the families as letters P' Z' X'
  tmidps    dpStepF_runs
  tmidpsb   dpStepF_le_B

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_m_dps.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, lineq, nlinarith
from t8b_e_sin import L_
from t7_e_cmp import machine
from t8b_l_seq import PH_RR, QR, ST_RR, PH_AC, ST_ACL, PH_TS

SEL = sys.argv[1:]
ENF = '( encNatGam ` F )'
ENL = '( encNatGam ` L )'
EFX = EWg('F', 'X')
ELY = EWg('L', 'Y')
DA1 = UP('D', 'J', BW(PLW, ELY))
UA = '( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 2 2 x. B ) ) + ; 3 8 )'
UB2 = '( %s + ( ( 4 x. B ) + ; 1 1 ) )' % SETCL
UB3 = '( ( 3 x. B ) + 3 )'
RDESC = '( ( L encTblDesc A ) ++ ( <" 0 "> ++ R ) )'
RASC = '( ( L encTblAsc A ) ++ ( <" 0 "> ++ U ) )'
PRE_P = UP(DA1, 'I', CC('<" 2 ">', '( %s ` I )' % DA1))
AC0W = '( ( L encTblAsc %s ) ++ ( <" 0 "> ++ U ) )' % ACC0
DB2 = UP(UP('D', 'J', CC('<" 4 ">', BW(PLW, ELY))), "I'", AC0W)
NLt = lambda t: BW(RRS(t), BW(PLW, ELY))
ACt = lambda t: '( ( L encTblAsc %s ) ++ ( <" 0 "> ++ U ) )' % ACCS(t)
EP0 = UP(UP(UP('D', 'J', NLt('L')), 'I', 'R'), "I'", ACt('L'))
ST_PA = '( %s -> %s )' % (cj(TREE_DPS), TRI(CEN('dps', 'D'), CLN('( P ` 0 )', S, DA1), UA))
ST_PP = '( %s -> %s )' % (cj(TREE_DPS), TRI(CLN(PL(PL('P', 9), 0), S, PRE_P), CLN('( P ` 2 )', S, DB2), UB2))
ST_PE = '( %s -> %s )' % (cj(TREE_DPS), TRI(CLN(PL(PL('P', 13), 0), S, EP0), CE(DFIN_DPS), UB3))


class Base:
    def __init__(self, w, ph):
        self.w, self.ph = w, ph
        c, mk, ne, ex = hsetup(w, ph, TREE_DPS, K6, 'dps')
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        s = w.s
        self.dd = c[STKD('D')]
        fn, ln, bn, nn = c['F e. NN0'], c['L e. NN'], c['B e. NN0'], c['N e. NN0']
        self.fn, self.ln, self.bn, self.nn = fn, ln, bn, nn
        self.l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
        vals = {k: selfval(w, ph, mk, 'D', self.dd, k) for k in K6}
        xw, yw, rw, uw = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[WRD('R', GAM)], c[WRD('U', GAM)]
        self.efx = ewg(w, ph, 'F', fn, 'X', xw)
        self.ely = ewg(w, ph, 'L', self.l0, 'Y', yw)
        vals['K'] = (EFX, c['( D ` K ) = %s' % EFX], self.efx)
        vals['J'] = (ELY, c['( D ` J ) = %s' % ELY], self.ely)
        rdw = self.tblw('encTblDesc', 'R', rw)
        raw = self.tblw('encTblAsc', 'U', uw)
        vals['I'] = (RDESC, c['( D ` I ) = %s' % RDESC], rdw)
        vals["I'"] = (RASC, c["( D ` I' ) = %s" % RASC], raw)
        self.vals = vals
        self.S0 = Stacks(w, ph, mk, 'D', self.dd, ne, vals)
        self.cl = Closure(w, ph, {'B': ('NN0', bn), 'N': ('NN0', nn), 'L': ('NN', ln), 'F': ('NN0', fn)})
        # the words of p and L
        self.efw = s([fn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
        self.elw = s([self.l0, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` L ) e. Word 2o )' % ph)
        self.fgv = s([fn, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. ( encodeNat ` F ) ) )' % (ph, ENF))
        self.lgv = s([self.l0, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. ( encodeNat ` L ) ) )' % (ph, ENL))
        self.fbits = s([self.fgv, s([self.efw, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. ( encodeNat ` F ) ) e. Word %s )' % (ph, BITS))], 'eqeltrd',
                       '( %s -> %s e. Word %s )' % (ph, ENF, BITS))
        self.lbits = s([self.lgv, s([self.elw, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. ( encodeNat ` L ) ) e. Word %s )' % (ph, BITS))], 'eqeltrd',
                       '( %s -> %s e. Word %s )' % (ph, ENL, BITS))
        self.nfb = s([fn, bn, c['F < ( 2 ^ B )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` F ) ) <_ B )' % ph)
        self.nlb = s([self.l0, bn, c['L < ( 2 ^ B )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` L ) ) <_ B )' % ph)
        # PLW
        rr = s([s([s([ln, fn, bn], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ B e. NN0 ) )' % ph),
                   s([c['F < ( 2 ^ B )'], c['L < ( 2 ^ B )']], 'jca', '( %s -> ( F < ( 2 ^ B ) /\\ L < ( 2 ^ B ) ) )' % ph)], 'jca', '( %s -> %s )' % (ph, PH_RR))],
               'id', '') if False else None
        self.phrr = s([s([ln, fn, bn], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ B e. NN0 ) )' % ph),
                       s([c['F < ( 2 ^ B )'], c['L < ( 2 ^ B )']], 'jca', '( %s -> ( F < ( 2 ^ B ) /\\ L < ( 2 ^ B ) ) )' % ph)], 'jca', '( %s -> %s )' % (ph, PH_RR))
        FM = '( F mod L )'
        self.fmn = s([self.cl.mem('F', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FM))
        nfe = '( # ` ( encodeNat ` F ) )'
        self.nfe = s([self.efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, nfe))
        self.plw = s([s([self.fmn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, FM)), self.nfe, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, PLW))
        self.pll = s([s([s([self.fmn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, FM)), self.nfe, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, PLW, nfe)),
                      self.nfb], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (ph, PLW))

    def tblw(self, op, rest, rw):
        """( ph -> ( ( L op A ) ++ ( <" 0 "> ++ rest ) ) e. Word Gamma' )"""
        w, ph, s, c = self.w, self.ph, self.w.s, self.c
        te = s([s([c['A e. Tbl'], self.l0], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ph), w.inst('tttbles')], 'syl',
               '( %s -> ( ( L encTblAsc A ) = %s /\\ ( L encTblDesc A ) = %s ) )' % (ph, ES('( A |` ( 0 ..^ L ) )'), ES(REV('( A |` ( 0 ..^ L ) )'))))
        tw = s([s([c['A e. Tbl'], self.l0], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ph), w.inst('tttblw')], 'syl',
               '( %s -> ( ( A |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( A |` ( 0 ..^ L ) ) ) = L ) )' % (ph, WSLOT))
        wl = s([tw], 'simpld', '( %s -> ( A |` ( 0 ..^ L ) ) e. %s )' % (ph, WSLOT))
        if op == 'encTblAsc':
            e = s([te], 'simpld', '( %s -> ( L encTblAsc A ) = %s )' % (ph, ES('( A |` ( 0 ..^ L ) )')))
            ww = s([wl, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES('( A |` ( 0 ..^ L ) )')))
        else:
            e = s([te], 'simprd', '( %s -> ( L encTblDesc A ) = %s )' % (ph, ES(REV('( A |` ( 0 ..^ L ) )'))))
            ww = s([s([wl, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REV('( A |` ( 0 ..^ L ) )'), WSLOT)), w.inst('ttsescl')], 'syl',
                   "( %s -> %s e. Word Gamma' )" % (ph, ES(REV('( A |` ( 0 ..^ L ) )'))))
        tw_ = s([e, ww], 'eqeltrd', "( %s -> ( L %s A ) e. Word Gamma' )" % (ph, op))
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        z = wgcat(w, ph, '<" 0 ">', rest, s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph), rw)
        return wgcat(w, ph, '( L %s A )' % op, '( <" 0 "> ++ %s )' % rest, tw_, z)

    def enclen(self, name, gv, ew, bnd):
        """( # ` ( encNatGam ` t ) ) e. NN0 and <_ B"""
        w, ph, s = self.w, self.ph, self.w.s
        EN = '( encNatGam ` %s )' % name
        EW_ = '( encodeNat ` %s )' % name
        ln = s([s([gv], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, EN, EW_)),
                s([ew, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, EW_, EW_))], 'eqtrd',
               '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, EN, EW_))
        le = s([ln, bnd], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (ph, EN))
        self.cl.leaf('( # ` %s )' % EN, 'NN0', s([s([s([self.fn if name == 'F' else self.l0, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EN))],
                                                   'id', '') if False else s([self.fn if name == 'F' else self.l0, w.inst('encnatgamcl')], 'syl',
                                                                              "( %s -> %s e. Word Gamma' )" % (ph, EN)), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, EN)))
        return le


def normalize_full(w, ph, B, R, base_chain, rew=None):
    """R's chain relative to its base plus base_chain normalized over D; whole values rewritten by rew
    (value -> (new, step)) and normalized again.  Returns (raw, step or None, fin, out)"""
    cur, out = R.normalize(K6)
    chi = list(base_chain) + out
    raw = chain_text('D', chi)
    gam = dict(R.gam)
    gam.update({v[0]: v[2] for v in B.vals.values()})
    for k in K6:
        gam['( D ` %s )' % k] = w.s([stkfv(w, ph, 'D', k, B.mk['tv'], B.dd, B.mk['k'][k]['kd']), B.mk['k'][k]['wge']], 'eleqtrd',
                                    "( %s -> ( D ` %s ) e. Word Gamma' )" % (ph, k))
    steps = []
    nst, out2 = stk_normalize(w, ph, B.mk, 'D', B.dd, B.ne, chi, gam, K6)
    if nst is not None:
        steps.append((nst, chain_text('D', out2)))
    if rew:
        rules = {v: rew[v] for k, v in out2 if v in rew}
        if rules:
            r, txt = w.rewrite(chain_text('D', out2), rules, ph)
            out3 = [(k, rew[v][0] if v in rew else v) for k, v in out2]
            assert chain_text('D', out3) == txt, txt
            steps.append((r, txt))
            for v in rules:
                gam[rew[v][0]] = gam.get(rew[v][0]) or gam[v]
            nst2, out4 = stk_normalize(w, ph, B.mk, 'D', B.dd, B.ne, out3, gam, K6)
            if nst2 is not None:
                steps.append((nst2, chain_text('D', out4)))
            out2 = out4
    fin = chain_text('D', out2)
    if not steps:
        return raw, None, fin, out2
    st = steps[0][0]
    for s_, t_ in steps[1:]:
        st = w.s([st, s_], 'eqtrd', '( %s -> %s = %s )' % (ph, raw, t_))
    return raw, st, fin, out2


def tmidpsa():
    ph = cj(TREE_DPS)
    w = W('tmidpsa', 'The prologue of Lean\'s ` dpStepF ` at the machine: ` dup nL t s ; dup np nL s ` (~ tmidup ) and '
                     '` modFrag nL t np snap s acc ` (~ tmimodf ) leave ` p mod L ` as a bit word above ` L ` on ` nL ` .')
    B = Base(w, ph)
    s, c = w.s, B.c
    R = Run(w, ph, B.mk, B.S0, B.ex, c)
    ELI0 = EWg('L', '( D ` I0 )')
    g0 = B.S0.vals['I0'][2]
    R.call('tmidup', {'K': 'J', 'J': 'I0', 'I': 'I"', 'P': PL('P', 6), 'E': PL(PL('P', 7), 0), 'W': ENL, 'X': 'Y'},
           {WRD(ENL, BITS): B.lbits, '( D ` J ) = ( %s ++ ( <" 4 "> ++ Y ) )' % ENL: B.S0.vals['J'][1]},
           [('I0', ELI0, ewg(w, ph, 'L', B.l0, '( D ` I0 )', g0))])
    S1 = R.S
    EFL = EWg('F', ELY)
    R.call('tmidup', {'K': 'K', 'J': 'J', 'I': 'I"', 'P': PL('P', 7), 'E': FRAGS['modf'].entry(PL('P', 8)), 'W': ENF, 'X': 'X'},
           {WRD(ENF, BITS): B.fbits, '( %s ` K ) = ( %s ++ ( <" 4 "> ++ X ) )' % (S1.D, ENF): S1.vals['K'][1]},
           [('J', EFL, ewg(w, ph, 'F', B.fn, ELY, B.ely))])
    S2 = R.S
    pw = s([B.plw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, PLW))
    PLY = BW(PLW, ELY)
    R.call('tmimodf', {'K': 'J', 'J': 'I0', 'I': 'K', "I'": 'I', 'I"': 'I"', 'I0': "I'", 'P': PL('P', 8), 'E': PL('P', 0), 'F': 'F', 'G': 'L', 'N': 'B',
                       'X': ELY, 'Y': '( D ` I0 )'},
           {'( %s ` J ) = %s' % (S2.D, EFL): S2.vals['J'][1], '( %s ` I0 ) = %s' % (S2.D, ELI0): S2.vals['I0'][1], WRD(ELY, GAM): B.ely,
            WRD('( D ` I0 )', GAM): g0},
           [('J', PLY, wgcat(w, ph, '( inclBool o. %s )' % PLW, '( <" 4 "> ++ %s )' % ELY, pw, wg4(w, ph, ELY, B.ely))), ('I0', '( D ` I0 )', g0)])
    raw, st, fin, out = normalize_full(w, ph, B, R, [])
    assert fin == DA1, fin
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    if st is not None:
        t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, PL('P', 0), S, st, raw, fin)) if D != CLN(PL('P', 0), S, fin) else (t, C, D, n)
    cl = B.cl
    lf = B.enclen('F', B.fgv, B.efw, B.nfb)
    ll = B.enclen('L', B.lgv, B.elw, B.nlb)
    NF_, NG_ = '( # ` ( encodeNat ` F ) )', '( # ` ( encodeNat ` L ) )'
    cl.leaf(NF_, 'NN0', B.nfe); cl.leaf(NG_, 'NN0', s([B.elw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NG_)))
    MB = tsub_text(MODB, {'G': 'L'})
    mbx = s([s([s([B.nfe, cl.mem(NG_, 'NN0'), B.bn], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ B e. NN0 ) )' % (ph, NF_, NG_)),
                s([B.nfb, B.nlb], 'jca', '( %s -> ( %s <_ B /\\ %s <_ B ) )' % (ph, NF_, NG_))], 'jca',
               '( %s -> ( ( %s e. NN0 /\\ %s e. NN0 /\\ B e. NN0 ) /\\ ( %s <_ B /\\ %s <_ B ) ) )' % (ph, NF_, NG_, NF_, NG_)), w.inst('ttmodbx')], 'syl',
            '( %s -> %s <_ ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 1 8 x. B ) ) + ; 2 8 ) )' % (ph, MB))
    cl.leaf(MB, 'NN0', cl.mem(MB, 'NN0'))
    BB = '( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) )'
    cl.leaf(BB, 'NN0', cl.mem(BB, 'NN0'))
    le = linarith(w, ph, [lf, ll, mbx], '%s <_ %s' % (n, UA), closure=cl, atoms=[MB, BB])
    hrle(w, ph, B.mk['phm'], t, C, D, n, UA, cl.mem(UA, 'NN0'), le, qed=True)
    return w.run()


def tmidpsp():
    ph = cj(TREE_DPS)
    w = W('tmidpsp', 'The initial write of Lean\'s ` dpStepF ` at the machine: after the push of ` bra ` on the snapshot, '
                     '` dup np snap s ; dup nL np s ` (~ tmidup ) and ` setIfNoneF acc np snap s t ` (~ tmisint ) write '
                     '` [ p ] ` at ` p mod L ` , and ` pushNum nL 0 ` (~ tm2fpshn ) starts the residue.')
    B = Base(w, ph)
    s, c, mk = w.s, B.c, B.mk
    pw = s([B.plw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, PLW))
    PLY = BW(PLW, ELY)
    ply = wgcat(w, ph, '( inclBool o. %s )' % PLW, '( <" 4 "> ++ %s )' % ELY, pw, wg4(w, ph, ELY, B.ely))
    SD1 = B.S0.upd('J', PLY, ply)
    assert SD1.D == DA1
    g2 = closed(w, ph, 'gamma2', "2 e. Gamma'")
    s2 = s([g2], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
    DI1 = '( %s ` I )' % DA1
    di1g = s([SD1.vals['I'][1], SD1.vals['I'][2]], 'eqeltrrd' if False else 'id', '') if False else \
        s([s([SD1.vals['I'][1]], 'eqcomd', '( %s -> %s = %s )' % (ph, RDESC, DI1)), SD1.vals['I'][2]], 'eqeltrrd' if False else 'id', '') if False else None
    di1g = s([SD1.vals['I'][1], SD1.vals['I'][2]], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ph, DI1)) if False else \
        s([SD1.vals['I'][1], SD1.vals['I'][2]], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, DI1))
    V2 = CC('<" 2 ">', DI1)
    SP0 = SD1.upd('I', V2, wgcat(w, ph, '<" 2 ">', DI1, s2, di1g))
    assert SP0.D == PRE_P, SP0.D
    R = Run(w, ph, mk, SP0, B.ex, c)
    E1 = CC(ENF, '( <" 4 "> ++ %s )' % V2)
    R.call('tmidup', {'K': 'K', 'J': 'I', 'I': 'I"', 'P': PL('P', 9), 'E': PL(PL('P', 10), 0), 'W': ENF, 'X': 'X'},
           {WRD(ENF, BITS): B.fbits, '( %s ` K ) = ( %s ++ ( <" 4 "> ++ X ) )' % (PRE_P, ENF): SP0.vals['K'][1]},
           [('I', E1, wgcat(w, ph, ENF, '( <" 4 "> ++ %s )' % V2, s([B.fn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ENF)),
                            wg4(w, ph, V2, SP0.vals['I'][2])))])
    S1 = R.S
    PFX_ = BW(PLW, EFX)
    R.call('tmidup', {'K': 'J', 'J': 'K', 'I': 'I"', 'P': PL('P', 10), 'E': PL(PL(PL('P', 11), 3), 0), 'W': '( inclBool o. %s )' % PLW, 'X': ELY},
           {WRD('( inclBool o. %s )' % PLW, BITS): s([B.plw, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, PLW, BITS)),
            WRD(ELY, GAM): B.ely, '( %s ` J ) = %s' % (S1.D, PLY): S1.vals['J'][1]},
           [('K', PFX_, wgcat(w, ph, '( inclBool o. %s )' % PLW, '( <" 4 "> ++ %s )' % EFX, pw, wg4(w, ph, EFX, B.efx)))])
    S2 = R.S
    # ( S2 ` I ) = ( encList ` <" F "> ) ++ RDESC
    s1f = s([B.fn], 's1cld', '( %s -> <" F "> e. Word NN0 )' % ph)
    s0 = closed(w, ph, 'wrd0', '(/) e. Word NN0')
    cons = s([B.fn, s0, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" F "> ++ (/) ) ) = ( %s ++ ( <" 4 "> ++ ( encList ` (/) ) ) ) )' % (ph, ENF))
    crid = s([s1f, w.inst('ccatrid')], 'syl', '( %s -> ( <" F "> ++ (/) ) = <" F "> )' % ph)
    e0 = closed(w, ph, 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')
    ec = s([s([s([crid], 'fveq2d', '( %s -> ( encList ` ( <" F "> ++ (/) ) ) = ( encList ` <" F "> ) )' % ph), cons], 'eqtr3d',
              '( %s -> ( encList ` <" F "> ) = ( %s ++ ( <" 4 "> ++ ( encList ` (/) ) ) ) )' % (ph, ENF)),
            s([s([e0], 'oveq2d', '( %s -> ( <" 4 "> ++ ( encList ` (/) ) ) = ( <" 4 "> ++ <" 2 "> ) )' % ph)], 'oveq2d',
              '( %s -> ( %s ++ ( <" 4 "> ++ ( encList ` (/) ) ) ) = ( %s ++ ( <" 4 "> ++ <" 2 "> ) ) )' % (ph, ENF, ENF))], 'eqtrd',
           '( %s -> ( encList ` <" F "> ) = ( %s ++ ( <" 4 "> ++ <" 2 "> ) ) )' % (ph, ENF))
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    s4 = s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    efg = s([B.fn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ENF))
    rdw = B.vals['I'][2]
    a1 = s([ec], 'oveq1d', '( %s -> ( ( encList ` <" F "> ) ++ %s ) = ( ( %s ++ ( <" 4 "> ++ <" 2 "> ) ) ++ %s ) )' % (ph, RDESC, ENF, RDESC))
    a2 = s([efg, s([s4, s2, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ <\" 2 \"> ) e. Word Gamma' )" % ph), rdw, w.inst('ccatass')], 'syl3anc',
           '( %s -> ( ( %s ++ ( <" 4 "> ++ <" 2 "> ) ) ++ %s ) = ( %s ++ ( ( <" 4 "> ++ <" 2 "> ) ++ %s ) ) )' % (ph, ENF, RDESC, ENF, RDESC))
    a3 = s([s([s4, s2, rdw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ <" 2 "> ) ++ %s ) = ( <" 4 "> ++ ( <" 2 "> ++ %s ) ) )' % (ph, RDESC, RDESC))], 'oveq2d',
           '( %s -> ( %s ++ ( ( <" 4 "> ++ <" 2 "> ) ++ %s ) ) = ( %s ++ ( <" 4 "> ++ ( <" 2 "> ++ %s ) ) ) )' % (ph, ENF, RDESC, ENF, RDESC))
    el = s([s([a1, a2], 'eqtrd', '( %s -> ( ( encList ` <" F "> ) ++ %s ) = ( %s ++ ( ( <" 4 "> ++ <" 2 "> ) ++ %s ) ) )' % (ph, RDESC, ENF, RDESC)), a3], 'eqtrd',
           '( %s -> ( ( encList ` <" F "> ) ++ %s ) = ( %s ++ ( <" 4 "> ++ ( <" 2 "> ++ %s ) ) ) )' % (ph, RDESC, ENF, RDESC))
    r_, x_ = w.rewrite(E1, {DI1: (RDESC, SD1.vals['I'][1])}, ph)
    si = s([s([S2.vals['I'][1], r_], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, S2.D, x_)), el], 'eqtr4d',
           '( %s -> ( %s ` I ) = ( ( encList ` <" F "> ) ++ %s ) )' % (ph, S2.D, RDESC))
    # the write
    cl = B.cl
    N1 = '( N + 1 )'
    B2 = '( 2 x. B )'
    tbm = s([s([s([B.nn, cl.mem(N1, 'NN0'), linarith(w, ph, [], 'N <_ %s' % N1, closure=cl)], '3jca', '( %s -> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (ph, N1, N1)),
                c[TBB('A')]], 'jca', '( %s -> ( ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) /\\ %s ) )' % (ph, N1, N1, TBB('A'))),
             w.inst('ttabtbbm')], 'syl', '( %s -> %s )' % (ph, TBB('A', N1)))
    s1l = s([s([s([], 's1len', '( # ` <" F "> ) = 1')], 'a1i', '( %s -> ( # ` <" F "> ) = 1 )' % ph), linarith(w, ph, [cl.ge0('N')], '1 <_ %s' % N1, closure=cl)],
            'eqbrtrd', '( %s -> ( # ` <" F "> ) <_ %s )' % (ph, N1))
    fv_ = s([B.fn], 'elexd', '( %s -> F e. _V )' % ph)
    sr = s([fv_, w.inst('s1rn')], 'syl', '( %s -> ran <" F "> = { F } )' % ph)
    rsg = s([fv_, s([s([], 'breq1', '( a = F -> ( a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')], 'ralsng', '( F e. _V -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')],
            'syl', '( %s -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )' % ph)
    rq = s([sr, w.inst('raleq')], 'syl', '( %s -> ( A. a e. ran <" F "> a < ( 2 ^ B ) <-> A. a e. { F } a < ( 2 ^ B ) ) )' % ph)
    rf = s([s([c['F < ( 2 ^ B )'], rsg], 'mpbird', '( %s -> A. a e. { F } a < ( 2 ^ B ) )' % ph), rq], 'mpbird', '( %s -> A. a e. ran <" F "> a < ( 2 ^ B ) )' % ph)
    FM = '( F mod L )'
    from t8b_l_seq import ST_RR as _unused
    tpl = s([B.fmn, B.nfe, tonat_pl(w, ph, B), w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ph, PLW, FM))
    fml = s([s([B.fn], 'nn0red', '( %s -> F e. RR )' % ph), s([B.ln, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % ph), w.inst('modlt')], 'syl2anc',
            '( %s -> %s < L )' % (ph, FM))
    tpll = s([tpl, fml], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (ph, PLW))
    cl.leaf('( # ` %s )' % PLW, 'NN0', s([B.plw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, PLW)))
    pl2 = linarith(w, ph, [B.pll, cl.ge0('B')], '( # ` %s ) <_ %s' % (PLW, B2), closure=cl)
    ACW = '( ( L encTblAsc ( ( A SetIfNone ( toNat ` %s ) ) ` <" F "> ) ) ++ ( <" 0 "> ++ U ) )' % PLW
    exs = {"( %s ` I' ) = %s" % (S2.D, RASC): S2.vals["I'"][1], '( %s ` K ) = %s' % (S2.D, PFX_): S2.vals['K'][1],
           '( %s ` I ) = ( ( encList ` <" F "> ) ++ %s )' % (S2.D, RDESC): si, '%s e. Word 2o' % PLW: B.plw, '<" F "> e. Word NN0': s1f,
           'L e. NN0': B.l0, WRD(EFX, GAM): B.efx, WRD('( <" 0 "> ++ U )', GAM): wg0(w, ph, c[WRD('U', GAM)]), WRD(RDESC, GAM): rdw,
           '%s e. NN0' % N1: cl.mem(N1, 'NN0'), '%s e. NN0' % B2: cl.mem(B2, 'NN0'), '( # ` %s ) <_ %s' % (PLW, B2): pl2,
           '( toNat ` %s ) < L' % PLW: tpll, TBB('A', N1): tbm, '( # ` <" F "> ) <_ %s' % N1: s1l, 'A. a e. ran <" F "> a < ( 2 ^ B )': rf}
    acw = acc_w(w, ph, B, c, s1f)
    R.call('tmisint', {'K': "I'", 'J': 'K', 'I': 'I', "I'": 'I"', 'I"': 'I0', 'P': PL('P', 11), 'E': PL('P', 1), 'A': 'A', 'G': PLW, 'W': '<" F ">',
                       'X': '( <" 0 "> ++ U )', 'Y': EFX, 'R': RDESC, 'N': N1, 'H': B2}, exs,
           [("I'", ACW, acw), ('K', EFX, B.efx), ('I', RDESC, rdw)])
    S3 = R.S
    kJ = mk['k']['J']
    NLP = CC('<" 4 ">', PLY)
    R.call('tm2fpshn', {'A': PL('P', 1), 'E': PL('P', 2), 'K': 'J', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('J'): s([g4, kJ['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('J')))},
           [('J', NLP, wg4(w, ph, PLY, ply))])
    rew = {EFX: ('( D ` K )', s([c['( D ` K ) = %s' % EFX]], 'eqcomd', '( %s -> %s = ( D ` K ) )' % (ph, EFX))),
           RDESC: ('( D ` I )', s([c['( D ` I ) = %s' % RDESC]], 'eqcomd', '( %s -> %s = ( D ` I ) )' % (ph, RDESC)))}
    raw, st, fin, out = normalize_full(w, ph, B, R, [('J', PLY), ('I', V2)], rew)
    assert out == [('J', NLP), ("I'", ACW)], out
    r2, x2 = w.rewrite(fin, {'( toNat ` %s )' % PLW: (FM, tpl)}, ph)
    assert x2 == DB2, x2
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    assert D == CLN(PL('P', 2), S, raw), (D, raw)
    fe = s([st, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, raw, DB2))
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, PL('P', 2), S, fe, raw, DB2))
    # the bound
    lf = B.enclen('F', B.fgv, B.efw, B.nfb)
    bl = s([B.plw, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, PLW, PLW))
    cl.leaf('( # ` ( inclBool o. %s ) )' % PLW, 'NN0', s([pw, w.inst('lencl')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) e. NN0 )' % (ph, PLW)))
    TPN = '( toNat ` %s )' % PLW
    tpn = s([B.plw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TPN))
    SJ = SETC(TPN, N1, B2)
    sm = s([s([s([tpn, B.l0, s([s([tpn], 'nn0red', '( %s -> %s e. RR )' % (ph, TPN)), s([B.l0], 'nn0red', '( %s -> L e. RR )' % ph), tpll], 'ltled',
                                  '( %s -> %s <_ L )' % (ph, TPN))], '3jca', '( %s -> ( %s e. NN0 /\\ L e. NN0 /\\ %s <_ L ) )' % (ph, TPN, TPN)),
               s([cl.mem(N1, 'NN0'), B.bn, cl.mem(B2, 'NN0')], '3jca', '( %s -> ( %s e. NN0 /\\ B e. NN0 /\\ %s e. NN0 ) )' % (ph, N1, B2))], 'jca',
              '( %s -> ( ( %s e. NN0 /\\ L e. NN0 /\\ %s <_ L ) /\\ ( %s e. NN0 /\\ B e. NN0 /\\ %s e. NN0 ) ) )' % (ph, TPN, TPN, N1, B2)), w.inst('ttabsetm')], 'syl',
           '( %s -> %s <_ %s )' % (ph, SJ, SETCL))
    cl.leaf(TPN, 'NN0', tpn)
    cl.leaf(SJ, 'NN0', cl.mem(SJ, 'NN0'))
    cl.leaf(SETCL, 'NN0', cl.mem(SETCL, 'NN0'))
    le = linarith(w, ph, [lf, bl, B.pll, sm], '%s <_ %s' % (n, UB2), closure=cl, atoms=[SJ, SETCL])
    hrle(w, ph, mk['phm'], t, C, D, n, UB2, cl.mem(UB2, 'NN0'), le, qed=True)
    return w.run()


def wg0(w, ph, uw):
    g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
    return wgcat(w, ph, '<" 0 ">', 'U', w.s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph), uw)


def tonat_pl(w, ph, B):
    """( ph -> ( F mod L ) < ( 2 ^ ( # ` ( encodeNat ` F ) ) ) )"""
    s = w.s
    NFE_ = '( # ` ( encodeNat ` F ) )'
    FM = '( F mod L )'
    cl = Closure(w, ph, {'L': ('NN', B.ln), 'F': ('NN0', B.fn)})
    fq = '( |_ ` ( F / L ) )'
    fqn = s([B.fn, B.ln, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, fq))
    cl.leaf(fq, 'NN0', fqn)
    cl.leaf(FM, 'NN0', B.fmn)
    cl.leaf(NFE_, 'NN0', B.nfe)
    mv = s([s([B.fn], 'nn0red', '( %s -> F e. RR )' % ph), s([B.ln, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % ph), w.inst('modvalr')], 'syl2anc',
           '( %s -> %s = ( F - ( %s x. L ) ) )' % (ph, FM, fq))
    mle = nlinarith(w, ph, [mv, cl.ge0(fq), cl.ge0('L')], '%s <_ F' % FM, closure=cl, atoms=[fq, FM])
    tfe = s([B.fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)
    tl = s([tfe, s([B.efw, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ph, NFE_))], 'eqbrtrrd', '( %s -> F < ( 2 ^ %s ) )' % (ph, NFE_))
    P2 = '( 2 ^ %s )' % NFE_
    cl.leaf(P2, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), B.nfe, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, P2)))
    return linarith(w, ph, [mle, tl], '%s < %s' % (FM, P2), closure=cl)


def acc_w(w, ph, B, c, s1f):
    s = w.s
    TT = '( ( A SetIfNone ( toNat ` %s ) ) ` <" F "> )' % PLW
    tn = s([B.plw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, PLW))
    at = s([s([c['A e. Tbl'], tn], 'jca', '( %s -> ( A e. Tbl /\\ ( toNat ` %s ) e. NN0 ) )' % (ph, PLW)), s1f, w.inst('setifnonecl')], 'syl2anc',
           '( %s -> %s e. Tbl )' % (ph, TT))
    te = s([s([at, B.l0], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (ph, TT)), w.inst('tttbles')], 'syl',
           '( %s -> ( ( L encTblAsc %s ) = %s /\\ ( L encTblDesc %s ) = %s ) )' % (ph, TT, ES('( %s |` ( 0 ..^ L ) )' % TT), TT, ES(REV('( %s |` ( 0 ..^ L ) )' % TT))))
    tw = s([s([at, B.l0], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (ph, TT)), w.inst('tttblw')], 'syl',
           '( %s -> ( ( %s |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( %s |` ( 0 ..^ L ) ) ) = L ) )' % (ph, TT, WSLOT, TT))
    esw = s([s([tw], 'simpld', '( %s -> ( %s |` ( 0 ..^ L ) ) e. %s )' % (ph, TT, WSLOT)), w.inst('ttsescl')], 'syl',
            "( %s -> %s e. Word Gamma' )" % (ph, ES('( %s |` ( 0 ..^ L ) )' % TT)))
    eaw = s([s([te], 'simpld', '( %s -> ( L encTblAsc %s ) = %s )' % (ph, TT, ES('( %s |` ( 0 ..^ L ) )' % TT))), esw], 'eqeltrd',
            "( %s -> ( L encTblAsc %s ) e. Word Gamma' )" % (ph, TT))
    return wgcat(w, ph, '( L encTblAsc %s )' % TT, '( <" 0 "> ++ U )', eaw, wg0(w, ph, c[WRD('U', GAM)]))


def rr_facts(w, ph, B, t, tfz):
    """ttrrs at t: word, value, length"""
    s = w.s
    q = s([s([B.phrr, tfz], 'jca', '( %s -> ( %s /\\ %s e. ( 0 ... L ) ) )' % (ph, PH_RR, t)), w.inst('ttrrs')], 'syl', '( %s -> %s )' % (ph, QR(t)))
    return (s([q], 'simp1d', '( %s -> %s e. Word 2o )' % (ph, RRS(t))), s([q], 'simp2d', '( %s -> ( toNat ` %s ) = ( ( ( L - %s ) x. F ) mod L ) )' % (ph, RRS(t), t)),
            s([q], 'simp3d', '( %s -> ( # ` %s ) <_ B )' % (ph, RRS(t))))


def acc_facts(w, ph, B, t, tfz):
    from t8b_l_seq import QA
    s = w.s
    c = B.c
    pac = s([s([B.ln, B.fn, c['A e. Tbl']], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) )' % ph),
             s([B.nn, B.bn, c['F < ( 2 ^ B )']], '3jca', '( %s -> ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) )' % ph), c[TBB('A')]], '3jca',
            '( %s -> %s )' % (ph, PH_AC))
    q = s([s([pac, tfz], 'jca', '( %s -> ( %s /\\ %s e. ( 0 ... L ) ) )' % (ph, PH_AC, t)), w.inst('ttaccs')], 'syl', '( %s -> %s )' % (ph, QA(t)))
    return pac, q


def tbl_w(w, ph, B, T_, tt):
    """( ph -> ( ( L encTblAsc T_ ) ++ ( <" 0 "> ++ U ) ) e. Word Gamma' ) from tt : T_ e. Tbl"""
    s = w.s
    te = s([s([tt, B.l0], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (ph, T_)), w.inst('tttbles')], 'syl',
           '( %s -> ( ( L encTblAsc %s ) = %s /\\ ( L encTblDesc %s ) = %s ) )' % (ph, T_, ES('( %s |` ( 0 ..^ L ) )' % T_), T_, ES(REV('( %s |` ( 0 ..^ L ) )' % T_))))
    tw = s([s([tt, B.l0], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (ph, T_)), w.inst('tttblw')], 'syl',
           '( %s -> ( ( %s |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( %s |` ( 0 ..^ L ) ) ) = L ) )' % (ph, T_, WSLOT, T_))
    esw = s([s([tw], 'simpld', '( %s -> ( %s |` ( 0 ..^ L ) ) e. %s )' % (ph, T_, WSLOT)), w.inst('ttsescl')], 'syl',
            "( %s -> %s e. Word Gamma' )" % (ph, ES('( %s |` ( 0 ..^ L ) )' % T_)))
    eaw = s([s([te], 'simpld', '( %s -> ( L encTblAsc %s ) = %s )' % (ph, T_, ES('( %s |` ( 0 ..^ L ) )' % T_))), esw], 'eqeltrd',
            "( %s -> ( L encTblAsc %s ) e. Word Gamma' )" % (ph, T_))
    return wgcat(w, ph, '( L encTblAsc %s )' % T_, '( <" 0 "> ++ U )', eaw, wg0(w, ph, B.c[WRD('U', GAM)]))


def tmidpse():
    ph = cj(TREE_DPS)
    w = W('tmidpse', 'The epilogue of Lean\'s ` dpStepF ` at the machine: ` dropNum nL ` twice and ` dropNum np ` '
                     '(~ tmidrop ) remove the residue, ` p mod L ` and ` p ` ; the accumulator is the DP step\'s table '
                     '(~ ttaccl ).')
    B = Base(w, ph)
    s, c, mk = w.s, B.c, B.mk
    lfz = s([B.l0, w.inst('nn0fz0')], 'sylib', '( %s -> L e. ( 0 ... L ) )' % ph)
    rrw, rrv, rrl = rr_facts(w, ph, B, 'L', lfz)
    pac, qa = acc_facts(w, ph, B, 'L', lfz)
    alt = s([qa], 'simp1d', '( %s -> %s e. Tbl )' % (ph, ACCS('L')))
    pw = s([B.plw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, PLW))
    PLY = BW(PLW, ELY)
    ply = wgcat(w, ph, '( inclBool o. %s )' % PLW, '( <" 4 "> ++ %s )' % ELY, pw, wg4(w, ph, ELY, B.ely))
    rbw = s([rrw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, RRS('L')))
    nlw = wgcat(w, ph, '( inclBool o. %s )' % RRS('L'), '( <" 4 "> ++ %s )' % PLY, rbw, wg4(w, ph, PLY, ply))
    acw = tbl_w(w, ph, B, ACCS('L'), alt)
    SE = B.S0.upd('J', NLt('L'), nlw).upd('I', 'R', c[WRD('R', GAM)]).upd("I'", ACt('L'), acw)
    assert SE.D == EP0
    kk = mk['k']
    def drop(Sc, k, Wd, X, wb, xg, P_, E_):
        V = CC(Wd, '( <" 4 "> ++ %s )' % X)
        ex = dict(B.ex)
        ex.update({STKD(Sc.D): Sc.memb, WRD(X, GAM): xg, WRD(Wd, BITS): wb})
        t, cc = inst(w, ph, 'tmidrop', {'K': k, 'P': P_, 'E': E_, 'D': Sc.D, 'W': Wd, 'X': X}, Bld(w, ph, c, ex))
        C_, D_, n_ = triple_parts(cc)
        vq = Sc.vals[k][1]
        assert Sc.vals[k][0] == V, (Sc.vals[k][0], V)
        u = upidv(w, ph, Sc.D, k, V, vq, mk['tv'], Sc.memb, kk[k]['kd'])
        t, C_, D_, n_ = hrrw(w, ph, t, C_, D_, n_, ceq=clneq(w, ph, PL(P_, 0), S, u, UP(Sc.D, k, V), Sc.D))
        return t, C_, D_, n_, Sc.upd(k, X, xg)
    rbb = s([rrw, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, RRS('L'), BITS))
    pbb = s([B.plw, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, PLW, BITS))
    t1, C1, D1, n1, S1 = drop(SE, 'J', '( inclBool o. %s )' % RRS('L'), PLY, rbb, ply, PL('P', 13), PL(PL('P', 14), 0))
    t2, C2, D2, n2, S2 = drop(S1, 'J', '( inclBool o. %s )' % PLW, ELY, pbb, B.ely, PL('P', 14), PL(PL('P', 15), 0))
    t3, C3, D3, n3, S3 = drop(S2, 'K', ENF, 'X', B.fbits, c[WRD('X', GAM)], PL('P', 15), 'E')
    t = hrseq(w, ph, mk['phm'], t1, t2, C1, D1, D2, n1, n2)
    t = hrseq(w, ph, mk['phm'], t, t3, C1, D2, D3, '( %s + %s )' % (n1, n2), n3)
    n = '( ( %s + %s ) + %s )' % (n1, n2, n3)
    chain = [('J', NLt('L')), ('I', 'R'), ("I'", ACt('L')), ('J', PLY), ('J', ELY), ('K', 'X')]
    assert D3 == CLN('E', S, chain_text('D', chain)), D3
    gam = {NLt('L'): nlw, 'R': c[WRD('R', GAM)], ACt('L'): acw, PLY: ply, ELY: B.ely, 'X': c[WRD('X', GAM)]}
    nst, out = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chain, gam, K6)
    assert out == [('K', 'X'), ('J', ELY), ('I', 'R'), ("I'", ACt('L'))], out
    dj = s([c['( D ` J ) = %s' % ELY]], 'eqcomd', '( %s -> %s = ( D ` J ) )' % (ph, ELY))
    acl = s([pac, w.inst('ttaccl')], 'syl', '( %s -> ( 1st ` ( ( L DpStep F ) ` A ) ) = %s )' % (ph, ACCS('L')))
    r1, x1 = w.rewrite(chain_text('D', out), {ELY: ('( D ` J )', dj), ACCS('L'): ('( 1st ` ( ( L DpStep F ) ` A ) )', s([acl], 'eqcomd',
                        '( %s -> %s = ( 1st ` ( ( L DpStep F ) ` A ) ) )' % (ph, ACCS('L'))))}, ph)
    out2 = [('K', 'X'), ('J', '( D ` J )'), ('I', 'R'), ("I'", '( ( L encTblAsc ( 1st ` ( ( L DpStep F ) ` A ) ) ) ++ ( <" 0 "> ++ U ) )')]
    assert x1 == chain_text('D', out2), x1
    gam['( D ` J )'] = s([stkfv(w, ph, 'D', 'J', mk['tv'], B.dd, kk['J']['kd']), kk['J']['wge']], 'eleqtrd', "( %s -> ( D ` J ) e. Word Gamma' )" % ph)
    FA = '( ( L encTblAsc ( 1st ` ( ( L DpStep F ) ` A ) ) ) ++ ( <" 0 "> ++ U ) )'
    gam[FA] = s([s([s([acl], 'eqcomd', '( %s -> %s = ( 1st ` ( ( L DpStep F ) ` A ) ) )' % (ph, ACCS('L')))], 'id', '') if False else None], 'id', '') if False else None
    gam[FA] = s([s([s([acl], 'oveq2d', '( %s -> ( L encTblAsc ( 1st ` ( ( L DpStep F ) ` A ) ) ) = ( L encTblAsc %s ) )' % (ph, ACCS('L')))], 'oveq1d',
                   '( %s -> %s = %s )' % (ph, FA, ACt('L'))), acw], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, FA))
    nst2, out3 = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, out2, gam, K6)
    assert chain_text('D', out3) == DFIN_DPS, chain_text('D', out3)
    fe = s([s([nst, r1], 'eqtrd', '( %s -> %s = %s )' % (ph, chain_text('D', chain), x1)), nst2], 'eqtrd', '( %s -> %s = %s )' % (ph, chain_text('D', chain), DFIN_DPS))
    t, C, D, n = hrrw(w, ph, t, C1, D3, n, deq=clneq(w, ph, 'E', S, fe, chain_text('D', chain), DFIN_DPS))
    cl = B.cl
    lf = B.enclen('F', B.fgv, B.efw, B.nfb)
    cl.leaf('( # ` %s )' % RRS('L'), 'NN0', s([rrw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, RRS('L'))))
    cl.leaf('( # ` %s )' % PLW, 'NN0', s([B.plw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, PLW)))
    hy = [lf, B.pll, rrl]
    for Wd, ww in (('( inclBool o. %s )' % RRS('L'), rrw), ('( inclBool o. %s )' % PLW, B.plw)):
        hy.append(s([ww, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, Wd, Wd[len('( inclBool o. '):-2])))
        cl.leaf('( # ` %s )' % Wd, 'NN0', s([s([ww, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, Wd, BITS)), w.inst('lencl')], 'syl',
                                           '( %s -> ( # ` %s ) e. NN0 )' % (ph, Wd)))
    le = linarith(w, ph, hy, '%s <_ %s' % (n, UB3), closure=cl)
    hrle(w, ph, mk['phm'], t, C, D, n, UB3, cl.mem(UB3, 'NN0'), le, qed=True)
    return w.run()


# ============================================================ the slot loop (tm2fdps)
from t7lib import famval, fam_unpack, fam_pack, mval
from t8a_f_wup import find, cnfl_m
WLr = '( reverse ` ( A |` ( 0 ..^ L ) ) )'
R_ = '( # ` %s )' % WLr
Z0R = '( <" 0 "> ++ R )'
SN = lambda t: CC(ES(DROP(WLr, t)), Z0R)
PDBd = lambda t: UP(UP(UP('D', 'J', NLt(t)), 'I', SN(t)), "I'", ACt(t))
PDFd = '( j e. NN0 |-> %s )' % PDBd('j')
ZDFd = '( j e. NN0 |-> %s )' % HD0(SN('j'))
XDFd = '( j e. NN0 |-> %s )' % TL1(SN('j'))
NCDd = lambda h, t: '( TMfl ` %s ) = if ( %s = %s , 1o , (/) )' % (h, t, R_)
NFd = '( j e. NN0 |-> { h e. TMSt | %s } )' % NCDd('h', 'j')
N1Cd = '( NN0 X. { %s } )' % S
FAMEQd = ("P' = %s" % PDFd, "Z' = %s" % ZDFd, "X' = %s" % XDFd)
T_Ld = (TREE_DPS, FAMEQd)
PHd = cj(T_Ld)
PSId = '( %s /\\ i e. ( 0 ..^ %s ) )' % (PHd, R_)
EPR = UP(PL('P', 0), 'I', 'x') if False else None
GMd = dict(FRAGS['dps'].lmap())
GMd.update({'K': 'I', 'F': RDBL, 'C0': CNFL, 'F"': PID, 'Y': '2', 'R': R_, "T'": DPBC, 'N': NFd, 'N1': N1Cd, 'P': "P'", 'Z': "Z'", 'X': "X'",
            'O': S, "O'": S, 'O"': S, "N'": S, 'N0': S, 'D': 'D', "D'": DA1, 'D0': DFIN_DPS, 'U': UA, "U'": UB2, 'U"': UB3})
_LAd, _LCd = split_imp(stmt('tm2fdps'))
LTREEd = tsub(parse_conj(_LAd), GMd)
LCONCLd = tsub_text(_LCd, GMd)
LPERd = find(LTREEd, lambda t: t.startswith('A. i e. ( 0 ..^ '))[0]
LBODYd = LPERd[len('A. i e. ( 0 ..^ %s ) ' % R_):]
LTYPd = find(LTREEd, lambda t: t.startswith('A. i e. ( 0 ... %s ) ( ( ( j e. NN0' % R_))[0]
LPKDd = find(LTREEd, lambda t: t.startswith("A. i e. ( 0 ... %s ) ( ( ( P' ` i ) ` I )" % R_))[0]
LEXITd = 'A. m e. ( %s ` %s ) -. ( %s ` m ) = 1o' % (NFd, R_, CNFL)
LPK0d = "A. r e. %s ( %s ` <. r , ( inl ` ( Z' ` 0 ) ) >. ) e. ( %s ` 0 )" % (S, RDBL, NFd)
LPOPd = "A. r e. ( %s ` %s ) ( %s ` <. r , ( inl ` ( Z' ` %s ) ) >. ) e. %s" % (NFd, R_, PID, R_, S)
for _t in (LEXITd, LPK0d, LPOPd):
    assert find(LTREEd, lambda t, _t=_t: t == _t), _t
FRAMEd = ((LTYPd, LPKDd), (LEXITd, LPK0d, LPOPd))


class Fd:
    """facts under ph (dpStepF's antecedent with the family equations, possibly extended)"""
    def __init__(self, w, ph):
        self.w, self.ph = w, ph
        root = None if ph == PHd else w.s([], 'simpl', '( %s -> %s )' % (ph, PHd))
        c = Ctx(w, ph, T_Ld, root=root) if root is not None else Ctx(w, ph, T_Ld)
        mk = machine(w, ph, c, K6)
        ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
        base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        base.update(unfold_all(w, ph, c[FRAGS['dps'].pred()], 'dps', K6, 'P', 'E', rec=False))
        f = FRAGS['dps']; lm = f.lmap()
        for j, (fn, cks, en, exn) in enumerate(f.children):
            P_ = PL('P', f.slot(j))
            pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
            base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
        for s_ in K6:
            base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K6):
            for b in K6[i_ + 1:]:
                base['%s =/= %s' % (a, b)] = ne(a, b)
                base['%s =/= %s' % (b, a)] = ne(b, a)
        ex = dict(base)
        ex.update(H.handler_extra(w, ph, mk, H.IFACE))
        hi = w.s([mk['seq'], w.inst('tmctbhi')], 'syl', '( %s -> %s )' % (ph, cj(HI_TREE)))
        ex.update(parts(w, ph, hi, HI_TREE))
        FLT = (('TMcar e. ( 2o ^m ( 2nd ` T ) )', 'TMda e. ( 2o ^m ( 2nd ` T ) )'),
               ('TMdb e. ( 2o ^m ( 2nd ` T ) )', 'TMfl e. ( 2o ^m ( 2nd ` T ) )'))
        fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ph, cj(FLT)))
        ex.update(parts(w, ph, fl, FLT))
        for n in ('0', '2', '3', '4'):
            ex["%s e. Gamma'" % n] = closed(w, ph, 'gamma%s' % n, "%s e. Gamma'" % n)
        ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        B = Base.__new__(Base)
        B.w, B.ph, B.c, B.mk, B.ne, B.ex = w, ph, c, mk, ne, ex
        self.B = B
        Base_init_rest(B)
        s = w.s
        at = c['A e. Tbl']
        tw = s([s([at, B.l0], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ph), w.inst('tttblw')], 'syl',
               '( %s -> ( ( A |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( A |` ( 0 ..^ L ) ) ) = L ) )' % (ph, WSLOT))
        self.wlw = s([tw], 'simpld', '( %s -> ( A |` ( 0 ..^ L ) ) e. %s )' % (ph, WSLOT))
        self.wll = s([tw], 'simprd', '( %s -> ( # ` ( A |` ( 0 ..^ L ) ) ) = L )' % ph)
        self.wrw = s([self.wlw, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, WLr, WSLOT))
        self.rl = s([s([self.wlw, w.inst('revlen')], 'syl', '( %s -> %s = ( # ` ( A |` ( 0 ..^ L ) ) ) )' % (ph, R_)), self.wll], 'eqtrd', '( %s -> %s = L )' % (ph, R_))
        self.rn = s([self.rl, B.l0], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, R_))
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        self.s0 = s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        self.zrw = wgcat(w, ph, '<" 0 ">', 'R', self.s0, c[WRD('R', GAM)])
        self.memo = {}

    def ifz(self, t, tfz):
        return self.w.s([tfz, self.w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (self.ph, t))

    def tl(self, t, tfz):
        """( ph -> t e. ( 0 ... L ) )"""
        return self.w.s([tfz, s_fzeq(self.w, self.ph, self.rl)], 'eleqtrd', '( %s -> %s e. ( 0 ... L ) )' % (self.ph, t))

    def words(self, t, tfz):
        key = ('w', t)
        if key in self.memo:
            return self.memo[key]
        w, ph, s, B = self.w, self.ph, self.w.s, self.B
        dr = s([self.wrw, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DROP(WLr, t), WSLOT))
        ed = s([dr, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(DROP(WLr, t))))
        snw = s([ed, self.zrw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, SN(t)))
        tlz = self.tl(t, tfz)
        rrw, rrv, rrl = rr_facts(w, ph, B, t, tlz)
        pac, qa = acc_facts(w, ph, B, t, tlz)
        alt = s([qa], 'simp1d', '( %s -> %s e. Tbl )' % (ph, ACCS(t)))
        pw = s([B.plw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, PLW))
        PLY = BW(PLW, ELY)
        ply = wgcat(w, ph, '( inclBool o. %s )' % PLW, '( <" 4 "> ++ %s )' % ELY, pw, wg4(w, ph, ELY, B.ely))
        rbw = s([rrw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, RRS(t)))
        nlw = wgcat(w, ph, '( inclBool o. %s )' % RRS(t), '( <" 4 "> ++ %s )' % PLY, rbw, wg4(w, ph, PLY, ply))
        acw = tbl_w(w, ph, B, ACCS(t), alt)
        self.memo[key] = dict(snw=snw, ed=ed, rrw=rrw, rrv=rrv, rrl=rrl, qa=qa, alt=alt, nlw=nlw, acw=acw, ply=ply, tlz=tlz)
        return self.memo[key]

    def stacks(self, t, tfz):
        key = ('s', t)
        if key in self.memo:
            return self.memo[key]
        W_ = self.words(t, tfz)
        St = self.B.S0.upd('J', NLt(t), W_['nlw']).upd('I', SN(t), W_['snw']).upd("I'", ACt(t), W_['acw'])
        assert St.D == PDBd(t)
        self.memo[key] = St
        return St

    def pdb(self, t, tfz):
        key = ('p', t)
        if key in self.memo:
            return self.memo[key]
        w, ph = self.w, self.ph
        St = self.stacks(t, tfz)
        tn = self.ifz(t, tfz)
        v = mval(w, ph, 'j', 'NN0', PDBd, t, tn, w.s([St.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PDBd(t))))
        e = w.s([self.c["P' = %s" % PDFd]], 'fveq1d', "( %s -> ( P' ` %s ) = ( %s ` %s ) )" % (ph, t, PDFd, t))
        r = w.s([e, v], 'eqtrd', "( %s -> ( P' ` %s ) = %s )" % (ph, t, PDBd(t)))
        self.memo[key] = (r, St)
        return r, St

    def fam(self, letter, F, X_of, t, tfz, xex):
        w, ph = self.w, self.ph
        tn = self.ifz(t, tfz)
        v = mval(w, ph, 'j', 'NN0', X_of, t, tn, xex)
        e = w.s([self.c['%s = %s' % (letter, F)]], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, letter, t, F, t))
        return w.s([e, v], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, letter, t, X_of(t)))

    def vn0(self, t, tfz):
        w, ph = self.w, self.ph
        W_ = self.words(t, tfz)
        c0 = w.s([W_['ed'], self.zrw, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( %s = (/) /\\ %s = (/) ) ) )' % (ph, SN(t), ES(DROP(WLr, t)), Z0R))
        c1 = w.s([self.s0, self.c[WRD('R', GAM)], w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( <" 0 "> = (/) /\\ R = (/) ) ) )' % (ph, Z0R))
        n0 = closed(w, ph, 's1nz', '<" 0 "> =/= (/)')
        n1 = w.s([w.s([n0], 'neneqd', '( %s -> -. <" 0 "> = (/) )' % ph)], 'intnanrd', '( %s -> -. ( <" 0 "> = (/) /\\ R = (/) ) )' % ph)
        n2 = w.s([c1, n1], 'mtbird', '( %s -> -. %s = (/) )' % (ph, Z0R))
        n3 = w.s([n2], 'intnand', '( %s -> -. ( %s = (/) /\\ %s = (/) ) )' % (ph, ES(DROP(WLr, t)), Z0R))
        n4 = w.s([c0, n3], 'mtbird', '( %s -> -. %s = (/) )' % (ph, SN(t)))
        return w.s([n4], 'neqned', '( %s -> %s =/= (/) )' % (ph, SN(t)))

    def zx(self, t, tfz):
        w, ph = self.w, self.ph
        W_ = self.words(t, tfz)
        eq, hg, tg = word_split(w, ph, SN(t), W_['snw'], self.vn0(t, tfz))
        z = self.fam("Z'", ZDFd, lambda s_: HD0(SN(s_)), t, tfz, w.s([hg], 'elexd', '( %s -> %s e. _V )' % (ph, HD0(SN(t)))))
        x = self.fam("X'", XDFd, lambda s_: TL1(SN(s_)), t, tfz, w.s([tg], 'elexd', '( %s -> %s e. _V )' % (ph, TL1(SN(t)))))
        return z, x, eq, hg, tg

    def zflag(self, t, tfz):
        w, ph = self.w, self.ph
        z, x, eq, hg, tg = self.zx(t, tfz)
        hd = w.s([self.wrw, self.c[WRD('R', GAM)], tfz, w.inst('ttseshd')], 'syl3anc', '( %s -> ( %s = 0 <-> %s = %s ) )' % (ph, HD0(SN(t)), t, R_))
        e1 = w.s([z], 'eqeq1d', "( %s -> ( ( Z' ` %s ) = 0 <-> %s = 0 ) )" % (ph, t, HD0(SN(t))))
        e2 = w.s([e1, hd], 'bitrd', "( %s -> ( ( Z' ` %s ) = 0 <-> %s = %s ) )" % (ph, t, t, R_))
        ifq = w.s([e2], 'ifbid', "( %s -> if ( ( Z' ` %s ) = 0 , 1o , (/) ) = if ( %s = %s , 1o , (/) ) )" % (ph, t, t, R_))
        zg = w.s([z, hg], 'eqeltrd', "( %s -> ( Z' ` %s ) e. Gamma' )" % (ph, t))
        return ifq, zg

    def peek_to_nf(self, Z, zg, ifq, t, tn, DOM, dss):
        w, ph, mk = self.w, self.ph, self.mk
        a = '( %s /\\ r e. %s )' % (ph, DOM)
        L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))
        rs = w.s([L(dss), w.s([], 'simpr', '( %s -> r e. %s )' % (a, DOM))], 'sseldd', '( %s -> r e. %s )' % (a, S))
        rr = w.s([rs, L(mk['seq'])], 'eleqtrd', '( %s -> r e. TMSt )' % a)
        N = '( %s ` <. r , ( inl ` %s ) >. )' % (RDBL, Z)
        m = w.s([rr, L(zg), w.inst('tmcrdblkc')], 'syl2anc', '( %s -> %s e. %s )' % (a, N, HCLS(Z, BLANK)))
        idh = w.s([], 'id', '( h = %s -> h = %s )' % (N, N))
        cond = lambda s_: '( TMfl ` %s ) = if ( %s = 0 , 1o , (/) )' % (s_, Z)
        cg, new = w.wcongr(cond('h'), {'h': N}, 'h = %s' % N, {'h': idh})
        el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (N, HCLS(Z, BLANK), N, cond(N)))
        both = w.s([m, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (a, N, cond(N)))
        nm = w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (a, N))
        f2 = w.s([w.s([both], 'simprd', '( %s -> %s )' % (a, cond(N))), L(ifq)], 'eqtrd', '( %s -> %s )' % (a, NCDd(N, t)))
        p = fam_pack(w, a, NCDd, t, L(tn), N, nm, f2)
        return w.s([p], 'ralrimiva', '( %s -> A. r e. %s %s e. ( %s ` %s ) )' % (ph, DOM, N, NFd, t))

    def nfss(self, t, tn):
        w, ph = self.w, self.ph
        fv = famval(w, ph, NCDd, t, tn)
        rab = '{ h e. TMSt | %s }' % NCDd('h', t)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % rab)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, rab))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, rab, S))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ %s )' % (ph, NFd, t, S))


def s_fzeq(w, ph, rl):
    return w.s([rl], 'oveq2d', '( %s -> ( 0 ... %s ) = ( 0 ... L ) )' % (ph, R_))


def Base_init_rest(B):
    """the part of Base.__init__ after hsetup (for a Base built over another antecedent)"""
    w, ph, c, mk, ne = B.w, B.ph, B.c, B.mk, B.ne
    s = w.s
    B.dd = c[STKD('D')]
    fn, ln, bn, nn = c['F e. NN0'], c['L e. NN'], c['B e. NN0'], c['N e. NN0']
    B.fn, B.ln, B.bn, B.nn = fn, ln, bn, nn
    B.l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    vals = {k: selfval(w, ph, mk, 'D', B.dd, k) for k in K6}
    xw, yw, rw, uw = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[WRD('R', GAM)], c[WRD('U', GAM)]
    B.efx = ewg(w, ph, 'F', fn, 'X', xw)
    B.ely = ewg(w, ph, 'L', B.l0, 'Y', yw)
    vals['K'] = (EFX, c['( D ` K ) = %s' % EFX], B.efx)
    vals['J'] = (ELY, c['( D ` J ) = %s' % ELY], B.ely)
    rdw = B.tblw('encTblDesc', 'R', rw)
    raw = B.tblw('encTblAsc', 'U', uw)
    vals['I'] = (RDESC, c['( D ` I ) = %s' % RDESC], rdw)
    vals["I'"] = (RASC, c["( D ` I' ) = %s" % RASC], raw)
    B.vals = vals
    B.S0 = Stacks(w, ph, mk, 'D', B.dd, ne, vals)
    B.cl = Closure(w, ph, {'B': ('NN0', bn), 'N': ('NN0', nn), 'L': ('NN', ln), 'F': ('NN0', fn)})
    B.efw = s([fn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    B.elw = s([B.l0, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` L ) e. Word 2o )' % ph)
    B.nfb = s([fn, bn, c['F < ( 2 ^ B )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` F ) ) <_ B )' % ph)
    B.phrr = s([s([ln, fn, bn], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ B e. NN0 ) )' % ph),
                s([c['F < ( 2 ^ B )'], c['L < ( 2 ^ B )']], 'jca', '( %s -> ( F < ( 2 ^ B ) /\\ L < ( 2 ^ B ) ) )' % ph)], 'jca', '( %s -> %s )' % (ph, PH_RR))
    FM = '( F mod L )'
    B.fmn = s([B.cl.mem('F', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FM))
    nfe = '( # ` ( encodeNat ` F ) )'
    B.nfe = s([B.efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, nfe))
    B.plw = s([s([B.fmn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, FM)), B.nfe, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, PLW))
    B.pll = s([s([s([B.fmn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, FM)), B.nfe, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, PLW, nfe)),
               B.nfb], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (ph, PLW))


def sb_from_tbb(w, ph, M, mn, tb, O, oeq):
    """( ph -> SB( O ) ) from TBB( A ) at M (mn : M e. NN0) and oeq : ( ph -> O = ( A ` M ) )"""
    s = w.s
    AM = '( A ` %s )' % M
    idd = s([], 'id', '( d = %s -> d = %s )' % (M, M))
    from t8b_l_seq import SBQ
    cgd, newd = w.wcongr(SBQ('( A ` d )'), {'d': M}, 'd = %s' % M, {'d': idd})
    rsp = s([cgd], 'rspcv', '( %s e. NN0 -> ( %s -> %s ) )' % (M, TBB('A'), SBQ(AM)))
    sq = s([mn, tb, rsp], 'sylc', '( %s -> %s )' % (ph, SBQ(AM)))
    X = '( 2nd ` %s )' % AM
    cb = s([s([], 'breq1', '( q = a -> ( q < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
           '( A. q e. ran %s q < ( 2 ^ B ) <-> A. a e. ran %s a < ( 2 ^ B ) )' % (X, X))
    an = s([cb], 'anbi2i', '( ( ( # ` %s ) <_ N /\\ A. q e. ran %s q < ( 2 ^ B ) ) <-> ( ( # ` %s ) <_ N /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (X, X, X, X))
    im = s([an], 'imbi2i', '( %s <-> %s )' % (SBQ(AM), SB(AM)))
    sa = s([sq, im], 'sylib', '( %s -> %s )' % (ph, SB(AM)))
    idn = s([], 'id', '( %s = %s -> %s = %s )' % (O, AM, O, AM))
    cg2, new2 = w.wcongr(SB(O), {}, '%s = %s' % (O, AM), {}, rules={O: (AM, idn)})
    assert new2 == SB(AM), new2
    return s([sa, s([oeq, cg2], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, SB(O), SB(AM)))], 'mpbird', '( %s -> %s )' % (ph, SB(O)))


def tmidpsi():
    lab = 'tmidpsi'
    w = W(lab, 'One iteration of Lean\'s ` dpStepF ` slot loop at the machine (the ` hb ` of ` forSlots_runs ` at '
               '` DpInv ` ): the test ` !flag ` holds while slots are left, ` dpBodyF ` (~ tmidpb ) at the residue '
               '` RR_i ` and the accumulator ` accSeq i ` (~ ttrrs , ~ ttaccs ) takes the snapshot\'s slot ` L - 1 - i ` '
               'and leaves ` RR_( i + 1 ) ` and ` accSeq ( i + 1 ) ` , and the peek of ` blank ` sets the flag to '
               '` decide ( i + 1 = L ) ` .')
    ps = PSId
    f = Fd(w, ps)
    c, mk, B = f.c, f.mk, f.B
    s = w.s
    ii = s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (ps, R_))
    inn = s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ifz = s([ii, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (ps, R_))
    I1 = '( i + 1 )'
    i1fz = s([ii, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ps, I1, R_))
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    ilt = s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ps, R_))
    ir = s([inn], 'nn0red', '( %s -> i e. RR )' % ps)
    ine = s([s([ir, ilt], 'ltned', '( %s -> i =/= %s )' % (ps, R_))], 'neneqd', '( %s -> -. i = %s )' % (ps, R_))
    NI = '( %s ` i )' % NFd
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm_, mc = fam_unpack(w, pm, NCDd, 'i', Lm(inn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    f0 = s([mc, s([Lm(ine)], 'iffalsed', '( %s -> if ( i = %s , 1o , (/) ) = (/) )' % (pm, R_))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    ht = s([cnfl_m(w, pm, 'm', mm_, '(/)', f0)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNFL))
    n1v = s([s([s([], 'fvex', '%s e. _V' % S)], 'a1i', '( %s -> %s e. _V )' % (ps, S)), inn, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` i ) = %s )' % (ps, N1Cd, S))
    n1s = s([n1v, f.ex[SSS(S)]], 'eqsstrd', '( %s -> ( %s ` i ) C_ %s )' % (ps, N1Cd, S))
    # the data at i
    pi, Si = f.pdb('i', ifz)
    Wi = f.words('i', ifz)
    W1 = f.words(I1, i1fz)
    rlL = f.rl
    io = s([ii, s([rlL], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ L ) )' % (ps, R_))], 'eleqtrd', '( %s -> i e. ( 0 ..^ L ) )' % ps)
    O_ = '( %s ` i )' % WLr
    ol = s([f.wrw, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (ps, O_, SLOT))
    drp = s([f.wrw, ii, w.inst('ttsesdrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ps, ES(DROP(WLr, 'i')), ESL(O_), ES(DROP(WLr, I1))))
    eo = s([ol, s([s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi', "( %s e. %s -> %s e. Word Gamma' )" % (O_, SLOT, ESL(O_)))],
           'syl', "( %s -> %s e. Word Gamma' )" % (ps, ESL(O_)))
    va = s([drp], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (ps, SN('i'), ESL(O_), ES(DROP(WLr, I1)), Z0R))
    vb = s([eo, W1['ed'], f.zrw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ %s ) )' % (ps, ESL(O_), ES(DROP(WLr, I1)), Z0R, ESL(O_), SN(I1)))
    vv = s([va, vb], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ps, SN('i'), ESL(O_), SN(I1)))
    dI = s([Si.vals['I'][1], vv], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ++ %s ) )' % (ps, PDBd('i'), ESL(O_), SN(I1)))
    # O = ( A ` ( L - ( i + 1 ) ) )
    WLt = '( A |` ( 0 ..^ L ) )'
    rv = s([f.wlw, s([ii, s([s([f.wlw, w.inst('revlen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ps, R_, WLt))], 'oveq2d',
                                '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` %s ) ) )' % (ps, R_, WLt))], 'eleqtrd', '( %s -> i e. ( 0 ..^ ( # ` %s ) ) )' % (ps, WLt)),
            w.inst('revfv')], 'syl2anc', '( %s -> %s = ( %s ` ( ( ( # ` %s ) - 1 ) - i ) ) )' % (ps, O_, WLt, WLt))
    M1 = '( L - %s )' % I1
    cl = Closure(w, ps, {'L': ('NN', B.ln), 'i': ('NN0', inn)})
    ix = lineq(w, ps, '( ( ( # ` %s ) - 1 ) - i )' % WLt, M1, hyps=[f.wll], closure=cl) if False else None
    ixr, ixn = w.rewrite('( ( ( # ` %s ) - 1 ) - i )' % WLt, {'( # ` %s )' % WLt: ('L', f.wll)}, ps)
    ix2 = lineq(w, ps, ixn, M1, closure=cl)
    ixe = s([ixr, ix2], 'eqtrd', '( %s -> ( ( ( # ` %s ) - 1 ) - i ) = %s )' % (ps, WLt, M1))
    lz = s([B.l0], 'nn0zd', '( %s -> L e. ZZ )' % ps)
    ltl = s([ilt, rlL], 'breqtrd', '( %s -> i < L )' % ps)
    i1l = s([ltl, s([s([inn], 'nn0zd', '( %s -> i e. ZZ )' % ps), lz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < L <-> %s <_ L ) )' % (ps, I1))], 'mpbid',
            '( %s -> %s <_ L )' % (ps, I1))
    mn = s([i1l, s([s([i1n], 'nn0zd', '( %s -> %s e. ZZ )' % (ps, I1)), lz, w.inst('znn0sub')], 'syl2anc', '( %s -> ( %s <_ L <-> %s e. NN0 ) )' % (ps, I1, M1))],
           'mpbid', '( %s -> %s e. NN0 )' % (ps, M1))
    mo = s([s([s([mn, lz, linarith(w, ps, [s([inn], 'nn0ge0d', '( %s -> 0 <_ i )' % ps)], '%s < L' % M1, closure=cl)], 'id', '') if False else None], 'id', '') if False else None],
           'id', '') if False else None
    ml = linarith(w, ps, [s([inn], 'nn0ge0d', '( %s -> 0 <_ i )' % ps)], '%s < L' % M1, closure=cl)
    mo = s([s([mn, lz, ml], '3jca', '( %s -> ( %s e. NN0 /\\ L e. ZZ /\\ %s < L ) )' % (ps, M1, M1)), w.inst('elfzo0z')], 'sylibr', '( %s -> %s e. ( 0 ..^ L ) )' % (ps, M1))
    fr = s([mo, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( A ` %s ) )' % (ps, WLt, M1, M1))
    oeq = s([s([rv, s([ixe], 'fveq2d', '( %s -> ( %s ` ( ( ( # ` %s ) - 1 ) - i ) ) = ( %s ` %s ) )' % (ps, WLt, WLt, WLt, M1))], 'eqtrd',
               '( %s -> %s = ( %s ` %s ) )' % (ps, O_, WLt, M1)), fr], 'eqtrd', '( %s -> %s = ( A ` %s ) )' % (ps, O_, M1))
    sbo = sb_from_tbb(w, ps, M1, mn, c[TBB('A')], O_, oeq)
    # the body: tmidpb at PDB( i )
    B2 = '( 2 x. B )'
    cl.leaf('B', 'NN0', B.bn)
    cl.leaf('( # ` %s )' % RRS('i'), 'NN0', s([Wi['rrw'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, RRS('i'))))
    cl.leaf('( # ` %s )' % PLW, 'NN0', s([B.plw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, PLW)))
    g2b = linarith(w, ps, [Wi['rrl'], cl.ge0('B')], '( # ` %s ) <_ %s' % (RRS('i'), B2), closure=cl)
    q2b = linarith(w, ps, [B.pll, cl.ge0('B')], '( # ` %s ) <_ %s' % (PLW, B2), closure=cl)
    lp = s([B.ln, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % ps)
    MX = '( ( L - i ) x. F )'
    mxr = s([s([s([B.l0, inn], 'id', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
    cl.leaf('F', 'NN0', B.fn)
    gl = s([Wi['rrv'], s([cl.mem(MX, 'RR'), lp, w.inst('modlt')], 'syl2anc', '( %s -> ( %s mod L ) < L )' % (ps, MX))], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (ps, RRS('i')))
    from t8b_m_dps import tonat_pl
    FM = '( F mod L )'
    tpl = s([B.fmn, B.nfe, tonat_pl(w, ps, B), w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ps, PLW, FM))
    ql = s([tpl, s([s([B.fn], 'nn0red', '( %s -> F e. RR )' % ps), lp, w.inst('modlt')], 'syl2anc', '( %s -> %s < L )' % (ps, FM))], 'eqbrtrd',
           '( %s -> ( toNat ` %s ) < L )' % (ps, PLW))
    U0 = '( <" 0 "> ++ U )'
    tbi = s([Wi['qa']], 'simp2d', '( %s -> %s )' % (ps, TBB(ACCS('i'), '( N + 1 )')))
    exb = dict(f.ex)
    exb.update({STKD(PDBd('i')): Si.memb, '( %s ` K ) = %s' % (PDBd('i'), EFX): Si.vals['K'][1], '( %s ` J ) = %s' % (PDBd('i'), NLt('i')): Si.vals['J'][1],
                '( %s ` I ) = ( %s ++ %s )' % (PDBd('i'), ESL(O_), SN(I1)): dI, "( %s ` I' ) = %s" % (PDBd('i'), ACt('i')): Si.vals["I'"][1],
                '%s e. Tbl' % ACCS('i'): Wi['alt'], '%s e. Word 2o' % RRS('i'): Wi['rrw'], '%s e. Word 2o' % PLW: B.plw, '%s e. %s' % (O_, SLOT): ol,
                WRD(SN(I1), GAM): W1['snw'], WRD(U0, GAM): wg0(w, ps, c[WRD('U', GAM)]), '( toNat ` %s ) < L' % RRS('i'): gl, '( toNat ` %s ) < L' % PLW: ql,
                '( # ` %s ) <_ %s' % (RRS('i'), B2): g2b, '( # ` %s ) <_ %s' % (PLW, B2): q2b, SB(O_): sbo, TBB(ACCS('i'), '( N + 1 )'): tbi})
    tb, ccb = inst(w, ps, 'tmidpb', {'P': PL('P', 12), 'E': PL('P', 4), 'D': PDBd('i'), 'C': ACCS('i'), 'G': RRS('i'), 'Q': PLW, 'O': O_, 'Z': SN(I1), 'U': U0},
                   Bld(w, ps, c, exb))
    Cb, Db, nb = triple_parts(ccb)
    assert nb == DPBC, nb
    RWD_ = tsub_text(RWD, {'G': RRS('i'), 'Q': PLW})
    ACCP_ = tsub_text(ACCP, {'C': ACCS('i'), 'G': RRS('i'), 'Q': PLW, 'O': O_})
    ACW_ = CC('( L encTblAsc %s )' % ACCP_, U0)
    chain = [('J', NLt('i')), ('I', SN('i')), ("I'", ACt('i')), ('J', BW(RWD_, BW(PLW, ELY))), ('I', SN(I1)), ("I'", ACW_)]
    assert Db == CLN(PL('P', 4), S, chain_text('D', chain)), Db
    # RWD_ = RRS( i + 1 ) , ACCP_ = ACCS( i + 1 )
    from t8b_l_seq import seq_step2, OPAX
    sq = seq_step2(w, ps, OPR, G1R, 'i', inn, 'ttreswv', '( ( %s e. Word 2o /\\ %s e. Word 2o ) /\\ ( %s e. Word 2o /\\ %%s e. NN0 ) )' % (PLW, ELW, RRS('i')),
                   [s([B.plw, B.elw], 'jca', '( %s -> ( %s e. Word 2o /\\ %s e. Word 2o ) )' % (ps, PLW, ELW)), Wi['rrw']], RWD_, lambda t: 'if ( %s = 0 , (/) , %s )' % (t, t))
    c3 = s([B.ln, B.fn, c['A e. Tbl']], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) )' % ps)
    sa = seq_step2(w, ps, OPA, G2A, 'i', inn, 'ttaccov', '( ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) /\\ ( %s e. Tbl /\\ %%s e. NN0 ) )' % ACCS('i'),
                   [c3, Wi['alt']], lambda Y: OPAX('A', 'L', 'F', ACCS('i'), Y), lambda t: 'if ( %s = 0 , %s , %s )' % (t, ACC0, t))
    OPV = OPAX('A', 'L', 'F', ACCS('i'), I1)
    tv1 = s([s([s([sq], 'eqcomd', '( %s -> %s = %s )' % (ps, RWD_, RRS(I1)))], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ps, RWD_, RRS(I1))), W1['rrv']],
            'eqtrd', '( %s -> ( toNat ` %s ) = ( ( ( L - %s ) x. F ) mod L ) )' % (ps, RWD_, I1))
    ra, xa = w.rewrite(ACCP_, {O_: ('( A ` %s )' % M1, oeq), '( toNat ` %s )' % RWD_: ('( ( ( L - %s ) x. F ) mod L )' % I1, tv1)}, ps)
    assert xa == OPV, (xa, OPV)
    ae = s([ra, s([sa], 'eqcomd', '( %s -> %s = %s )' % (ps, OPV, ACCS(I1)))], 'eqtrd', '( %s -> %s = %s )' % (ps, ACCP_, ACCS(I1)))
    gam = {NLt('i'): Wi['nlw'], SN('i'): Wi['snw'], ACt('i'): Wi['acw'], SN(I1): W1['snw']}
    r1, x1 = w.rewrite(chain_text('D', chain), {RWD_: (RRS(I1), s([sq], 'eqcomd', '( %s -> %s = %s )' % (ps, RWD_, RRS(I1)))), ACCP_: (ACCS(I1), ae)}, ps)
    ch2 = [('J', NLt('i')), ('I', SN('i')), ("I'", ACt('i')), ('J', NLt(I1)), ('I', SN(I1)), ("I'", ACt(I1))]
    assert x1 == chain_text('D', ch2), x1
    gam.update({NLt(I1): W1['nlw'], ACt(I1): W1['acw']})
    nst, out = stk_normalize(w, ps, mk, 'D', B.dd, f.ne, ch2, gam, K6)
    assert chain_text('D', out) == PDBd(I1), chain_text('D', out)
    p1, S1_ = f.pdb(I1, i1fz)
    fin = s([s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (ps, chain_text('D', chain), PDBd(I1))), p1], 'eqtr4d', "( %s -> %s = ( P' ` %s ) )" % (ps, chain_text('D', chain), I1))
    E4 = PL('P', 4)
    deq1 = clneq(w, ps, E4, S, fin, chain_text('D', chain), "( P' ` %s )" % I1)
    deq2 = clnneq(w, ps, E4, s([n1v], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, S, N1Cd)), S, '( %s ` i )' % N1Cd, "( P' ` %s )" % I1)
    deq = s([deq1, deq2], 'eqtrd', '( %s -> %s = %s )' % (ps, Db, CLN(E4, '( %s ` i )' % N1Cd, "( P' ` %s )" % I1)))
    B0 = FRAGS['dpb'].entry(PL('P', 12))
    nss = f.nfss('i', inn)
    t1 = hrssc(w, ps, mk['phm'], tb, Cb, Db, nb, CLN(B0, NI, PDBd('i')), clnss(w, ps, B0, NI, S, PDBd('i'), nss))
    ceq = clneq(w, ps, B0, NI, s([pi], 'eqcomd', "( %s -> %s = ( P' ` i ) )" % (ps, PDBd('i'))), PDBd('i'), "( P' ` i )")
    t2, C2, D2, n2 = hrrw(w, ps, t1, CLN(B0, NI, PDBd('i')), Db, nb, ceq=ceq, deq=deq)
    ifq, zg = f.zflag(I1, i1fz)
    pk = f.peek_to_nf("( Z' ` %s )" % I1, zg, ifq, I1, i1n, '( %s ` i )' % N1Cd, n1s)
    body = TRI(C2, D2, n2)
    got = cj(((HT(NI, CNFL), SSS('( %s ` i )' % N1Cd)), (body, 'A. r e. ( %s ` i ) ( %s ` <. r , ( inl ` ( Z\' ` %s ) ) >. ) e. ( %s ` %s )'
                                                        % (N1Cd, RDBL, I1, NFd, I1))))
    assert got == LBODYd, '\nGOT  %s\nWANT %s' % (got, LBODYd)
    a1 = s([ht, n1s], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, HT(NI, CNFL), SSS('( %s ` i )' % N1Cd)))
    a2 = s([t2, pk], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, body, concl(w, ps, pk)))
    w.qed([a1, a2], 'jca', '( %s -> %s )' % (ps, LBODYd))
    return w.run()


ST_Td = '( %s -> %s )' % (PHd, cj(FRAMEd))


def tmidpst():
    lab = 'tmidpst'
    w = W(lab, 'The frame of Lean\'s ` dpStepF ` slot loop at the machine: the invariant\'s classes and stacks and the '
               'peeked letter over ` 0 ... L ` , the test ` !flag ` failing at ` L ` , the first peek of ` blank ` and the '
               'final ` popTop snap ` .')
    ps = PHd
    f = Fd(w, ps)
    s, mk = w.s, f.mk
    pt = '( %s /\\ i e. ( 0 ... %s ) )' % (ps, R_)
    g = Fd(w, pt)
    ifz = s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (pt, R_))
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    pi, Si = g.pdb('i', ifz)
    mem = s([pi, Si.memb], 'eqeltrd', "( %s -> ( P' ` i ) e. %s )" % (pt, STK_T))
    ty = s([g.nfss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYPd[len('A. i e. ( 0 ... %s ) ' % R_):]))
    typ = s([ty], 'ralrimiva', '( %s -> %s )' % (ps, LTYPd))
    k1 = s([s([pi], 'fveq1d', "( %s -> ( ( P' ` i ) ` I ) = ( %s ` I ) )" % (pt, PDBd('i'))), Si.vals['I'][1]], 'eqtrd',
           "( %s -> ( ( P' ` i ) ` I ) = %s )" % (pt, SN('i')))
    z, x, eq, hg, tg = g.zx('i', ifz)
    k2 = s([k1, eq], 'eqtrd', "( %s -> ( ( P' ` i ) ` I ) = ( <\" %s \"> ++ %s ) )" % (pt, HD0(SN('i')), TL1(SN('i'))))
    rz = s([s([z], 's1eqd', "( %s -> <\" ( Z' ` i ) \"> = <\" %s \"> )" % (pt, HD0(SN('i')))), x], 'oveq12d',
           "( %s -> ( <\" ( Z' ` i ) \"> ++ ( X' ` i ) ) = ( <\" %s \"> ++ %s ) )" % (pt, HD0(SN('i')), TL1(SN('i'))))
    k3 = s([k2, rz], 'eqtr4d', "( %s -> ( ( P' ` i ) ` I ) = ( <\" ( Z' ` i ) \"> ++ ( X' ` i ) ) )" % pt)
    zg = s([z, hg], 'eqeltrd', "( %s -> ( Z' ` i ) e. Gamma' )" % pt)
    xg = s([x, tg], 'eqeltrd', "( %s -> ( X' ` i ) e. Word Gamma' )" % pt)
    pk = s([k3, zg, xg], '3jca', '( %s -> %s )' % (pt, LPKDd[len('A. i e. ( 0 ... %s ) ' % R_):]))
    pkd = s([pk], 'ralrimiva', '( %s -> %s )' % (ps, LPKDd))
    NR = '( %s ` %s )' % (NFd, R_)
    pm = '( %s /\\ m e. %s )' % (ps, NR)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm_, mc = fam_unpack(w, pm, NCDd, R_, Lm(f.rn), 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NR)))
    f1 = s([mc, s([s([], 'eqidd', '( %s -> %s = %s )' % (pm, R_, R_))], 'iftrued', '( %s -> if ( %s = %s , 1o , (/) ) = 1o )' % (pm, R_, R_))],
           'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    c0 = cnfl_m(w, pm, 'm', mm_, '1o', f1)
    exi = s([not1o(w, pm, c0, CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXITd))
    z0 = s([f.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, R_))
    ifq0, zg0 = f.zflag('0', z0)
    pk0 = f.peek_to_nf("( Z' ` 0 )", zg0, ifq0, '0', closed(w, ps, '0nn0', '0 e. NN0'), S, f.ex[SSS(S)])
    rfz = s([f.rn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, R_, R_))
    ifqr, zgr = f.zflag(R_, rfz)
    pop = pop_iface(w, ps, mk, NR, f.nfss(R_, f.rn), "( Z' ` %s )" % R_, zgr)
    a1 = s([typ, pkd], 'jca', '( %s -> ( %s /\\ %s ) )' % (ps, LTYPd, LPKDd))
    a2 = s([exi, pk0, pop], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ps, LEXITd, LPK0d, LPOPd))
    w.qed([a1, a2], 'jca', ST_Td)
    return w.run()


ST_Ld = '( %s -> %s )' % (PHd, LCONCLd)


def tmidpsl():
    lab = 'tmidpsl'
    w = W(lab, 'Lean\'s ` dpStepF ` at the machine with the invariant\'s families as letters: ~ tm2fdps with the prologue '
               '~ tmidpsa , the initial write ~ tmidpsp , the body ~ tmidpsi , the frame ~ tmidpst and the epilogue ~ tmidpse .')
    ps = PHd
    f = Fd(w, ps)
    c, mk, B, s = f.c, f.mk, f.B, w.s
    ex = dict(f.ex)
    fr = s([], 'tmidpst', ST_Td)
    ex.update(parts(w, ps, fr, FRAMEd))
    ex['%s e. NN0' % R_] = f.rn
    cl = B.cl
    for b in (DPBC, UA, UB2, UB3):
        ex['%s e. NN0' % b] = cl.mem(b, 'NN0')
    bi = s([], 'tmidpsi', '( %s -> %s )' % (PSId, LBODYd))
    ex[LPERd] = s([bi], 'ralrimiva', '( %s -> %s )' % (ps, LPERd))
    TR = lambda n: '( %s -> %s )' % (cj(TREE_DPS), n)
    L0 = lambda st, txt: s([st], 'adantr', '( %s -> %s )' % (ps, txt))
    ta = L0(s([], 'tmidpsa', ST_PA), ST_PA.split(' -> ', 1)[1][:-2] if False else TRI(CEN('dps', 'D'), CLN('( P ` 0 )', S, DA1), UA))
    ex[TRI(CEN('dps', 'D'), CLN('( P ` 0 )', S, DA1), UA)] = ta
    pw = s([B.plw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ps, PLW))
    PLY = BW(PLW, ELY)
    ply = wgcat(w, ps, '( inclBool o. %s )' % PLW, '( <" 4 "> ++ %s )' % ELY, pw, wg4(w, ps, ELY, B.ely))
    SD1 = B.S0.upd('J', PLY, ply)
    ex[STKD(DA1)] = SD1.memb
    # the initial write, onto ( P' ` 0 )
    tp = L0(s([], 'tmidpsp', ST_PP), TRI(CLN(PL(PL('P', 9), 0), S, PRE_P), CLN('( P ` 2 )', S, DB2), UB2))
    z0 = s([f.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, R_))
    p0, S0_ = f.pdb('0', z0)
    W0 = f.words('0', z0)
    from t7lib import mval
    s1 = s([closed(w, ps, '0z', '0 e. ZZ'), w.inst('seq1')], 'syl', '( %s -> %s = ( %s ` 0 ) )' % (ps, RRS('0'), G1R))
    X0r = lambda t: 'if ( %s = 0 , (/) , %s )' % (t, t)
    ax0 = s([closed(w, ps, '0ex', '(/) e. _V'), closed(w, ps, 'c0ex', '0 e. _V')], 'ifcld', '( %s -> %s e. _V )' % (ps, X0r('0')))
    g0 = mval(w, ps, 'k', 'NN0', X0r, '0', closed(w, ps, '0nn0', '0 e. NN0'), ax0)
    i0 = s([s([], 'eqidd', '( %s -> 0 = 0 )' % ps)], 'iftrued', '( %s -> %s = (/) )' % (ps, X0r('0')))
    r0 = s([s([s1, g0], 'eqtrd', '( %s -> %s = %s )' % (ps, RRS('0'), X0r('0'))), i0], 'eqtrd', '( %s -> %s = (/) )' % (ps, RRS('0')))
    s1a = s([closed(w, ps, '0z', '0 e. ZZ'), w.inst('seq1')], 'syl', '( %s -> %s = ( %s ` 0 ) )' % (ps, ACCS('0'), G2A))
    X0a = lambda t: 'if ( %s = 0 , %s , %s )' % (t, ACC0, t)
    axa = s([s([s([], 'fvex', '%s e. _V' % ACC0)], 'a1i', '( %s -> %s e. _V )' % (ps, ACC0)), closed(w, ps, 'c0ex', '0 e. _V')], 'ifcld', '( %s -> %s e. _V )' % (ps, X0a('0')))
    ga = mval(w, ps, 'k', 'NN0', X0a, '0', closed(w, ps, '0nn0', '0 e. NN0'), axa)
    ia = s([s([], 'eqidd', '( %s -> 0 = 0 )' % ps)], 'iftrued', '( %s -> %s = %s )' % (ps, X0a('0'), ACC0))
    ra = s([s([s1a, ga], 'eqtrd', '( %s -> %s = %s )' % (ps, ACCS('0'), X0a('0'))), ia], 'eqtrd', '( %s -> %s = %s )' % (ps, ACCS('0'), ACC0))
    ib0 = s([s([r0], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. (/) ) )' % (ps, RRS('0'))), closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd',
            '( %s -> ( inclBool o. %s ) = (/) )' % (ps, RRS('0')))
    PL4 = '( <" 4 "> ++ %s )' % PLY
    nl0 = s([s([ib0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, NLt('0'), PL4)), s([wg4(w, ps, PLY, ply), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, PL4, PL4))],
            'eqtrd', '( %s -> %s = %s )' % (ps, NLt('0'), PL4))
    d0 = s([f.wrw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = %s )' % (ps, DROP(WLr, '0'), WLr))
    te = s([s([c['A e. Tbl'], B.l0], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ps), w.inst('tttbles')], 'syl',
           '( %s -> ( ( L encTblAsc A ) = %s /\\ ( L encTblDesc A ) = %s ) )' % (ps, ES('( A |` ( 0 ..^ L ) )'), ES(WLr)))
    ed = s([te], 'simprd', '( %s -> ( L encTblDesc A ) = %s )' % (ps, ES(WLr)))
    sn0 = s([s([s([d0], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP(WLr, '0')), ES(WLr))), ed], 'eqtr4d', '( %s -> %s = ( L encTblDesc A ) )' % (ps, ES(DROP(WLr, '0'))))],
            'oveq1d', '( %s -> %s = %s )' % (ps, SN('0'), RDESC))
    sn0d = s([sn0, s([c['( D ` I ) = %s' % RDESC]], 'eqcomd', '( %s -> %s = ( D ` I ) )' % (ps, RDESC))], 'eqtrd', '( %s -> %s = ( D ` I ) )' % (ps, SN('0')))
    ac0 = s([s([ra], 'oveq2d', '( %s -> ( L encTblAsc %s ) = ( L encTblAsc %s ) )' % (ps, ACCS('0'), ACC0))], 'oveq1d', '( %s -> %s = %s )' % (ps, ACt('0'), AC0W))
    r1, x1 = w.rewrite(PDBd('0'), {NLt('0'): (PL4, nl0), SN('0'): ('( D ` I )', sn0d), ACt('0'): (AC0W, ac0)}, ps)
    ch = [('J', PL4), ('I', '( D ` I )'), ("I'", AC0W)]
    assert x1 == chain_text('D', ch), x1
    gam = {PL4: wg4(w, ps, PLY, ply), '( D ` I )': B.vals['I'][2] if False else s([stkfv(w, ps, 'D', 'I', mk['tv'], B.dd, mk['k']['I']['kd']), mk['k']['I']['wge']], 'eleqtrd',
                                                                                  "( %s -> ( D ` I ) e. Word Gamma' )" % ps),
           AC0W: s([ac0, W0['acw']], 'eqeltrrd' if False else 'id', '') if False else s([s([ac0], 'eqcomd', '( %s -> %s = %s )' % (ps, AC0W, ACt('0'))), W0['acw']], 'eqeltrd',
                                                                                         "( %s -> %s e. Word Gamma' )" % (ps, AC0W))}
    nst, out = stk_normalize(w, ps, mk, 'D', B.dd, f.ne, ch, gam, K6)
    assert chain_text('D', out) == DB2, chain_text('D', out)
    pe = s([s([p0, r1], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ps, x1)), nst], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ps, DB2))
    tp, _, _, _ = hrrw(w, ps, tp, CLN(PL(PL('P', 9), 0), S, PRE_P), CLN('( P ` 2 )', S, DB2), UB2,
                       deq=clneq(w, ps, '( P ` 2 )', S, s([pe], 'eqcomd', "( %s -> %s = ( P' ` 0 ) )" % (ps, DB2)), DB2, "( P' ` 0 )"))
    ex[TRI(CLN(PL(PL('P', 9), 0), S, PRE_P), CLN('( P ` 2 )', S, "( P' ` 0 )"), UB2)] = tp
    # the epilogue from UPD( ( P' ` R ) , I , ( X' ` R ) )
    rfz = s([f.rn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, R_, R_))
    pr, SR = f.pdb(R_, rfz)
    z, x, eqz, hg, tg = f.zx(R_, rfz)
    sw = closed(w, ps, 'swrd00', '( %s substr <. %s , %s >. ) = (/)' % (WLr, R_, R_))
    esr = s([s([s([sw], 'fveq2d', '( %s -> %s = %s )' % (ps, ES(DROP(WLr, R_)), ES('(/)'))), closed(w, ps, 'ttses0', A8.ST_ES0)], 'eqtrd',
               '( %s -> %s = (/) )' % (ps, ES(DROP(WLr, R_))))], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, SN(R_), Z0R))
    snr = s([esr, s([f.zrw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, Z0R, Z0R))], 'eqtrd', '( %s -> %s = %s )' % (ps, SN(R_), Z0R))
    r4, x4 = w.rewrite(TL1(SN(R_)), {SN(R_): (Z0R, snr)}, ps)
    n1 = closed(w, ps, 's1len', '( # ` <" 0 "> ) = 1')
    cln = s([f.s0, c[WRD('R', GAM)], w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" 0 "> ) + ( # ` R ) ) )' % (ps, Z0R))
    o1 = s([s([n1], 'eqcomd', '( %s -> 1 = ( # ` <" 0 "> ) )' % ps), cln], 'opeq12d', '( %s -> <. 1 , ( # ` %s ) >. = <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` R ) ) >. )' % (ps, Z0R))
    o2 = s([o1], 'oveq2d', '( %s -> %s = ( %s substr <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` R ) ) >. ) )' % (ps, TL1(Z0R), Z0R))
    s2 = s([f.s0, c[WRD('R', GAM)], w.inst('swrdccat2')], 'syl2anc', '( %s -> ( %s substr <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` R ) ) >. ) = R )' % (ps, Z0R))
    tx = s([s([r4, o2], 'eqtrd', '( %s -> %s = ( %s substr <. ( # ` <" 0 "> ) , ( ( # ` <" 0 "> ) + ( # ` R ) ) >. ) )' % (ps, TL1(SN(R_)), Z0R)), s2], 'eqtrd',
           '( %s -> %s = R )' % (ps, TL1(SN(R_))))
    xr = s([x, tx], 'eqtrd', "( %s -> ( X' ` %s ) = R )" % (ps, R_))
    PRE_E = UP("( P' ` %s )" % R_, 'I', "( X' ` %s )" % R_)
    r5, x5 = w.rewrite(PRE_E, {"( P' ` %s )" % R_: (PDBd(R_), pr), "( X' ` %s )" % R_: ('R', xr)}, ps)
    WR = f.words(R_, rfz)
    ch5 = [('J', NLt(R_)), ('I', SN(R_)), ("I'", ACt(R_)), ('I', 'R')]
    assert x5 == chain_text('D', ch5), x5
    gam5 = {NLt(R_): WR['nlw'], SN(R_): WR['snw'], ACt(R_): WR['acw'], 'R': c[WRD('R', GAM)]}
    nst5, out5 = stk_normalize(w, ps, mk, 'D', B.dd, f.ne, ch5, gam5, K6)
    r6, x6 = w.rewrite(chain_text('D', out5), {R_: ('L', f.rl)}, ps)
    assert x6 == EP0, x6
    pe5 = s([s([r5, nst5], 'eqtrd', '( %s -> %s = %s )' % (ps, PRE_E, chain_text('D', out5))), r6], 'eqtrd', '( %s -> %s = %s )' % (ps, PRE_E, EP0))
    te_ = L0(s([], 'tmidpse', ST_PE), TRI(CLN(PL(PL('P', 13), 0), S, EP0), CE(DFIN_DPS), UB3))
    E13 = PL(PL('P', 13), 0)
    te_, _, _, _ = hrrw(w, ps, te_, CLN(E13, S, EP0), CE(DFIN_DPS), UB3, ceq=clneq(w, ps, E13, S, s([pe5], 'eqcomd', '( %s -> %s = %s )' % (ps, EP0, PRE_E)), EP0, PRE_E))
    ex[TRI(CLN(E13, S, PRE_E), CE(DFIN_DPS), UB3)] = te_
    ex["2 e. Gamma'"] = closed(w, ps, 'gamma2', "2 e. Gamma'")
    # the body's entry label: dpBodyF -> resStep -> moveEntry, one level each
    P12, P4 = PL('P', 12), PL('P', 4)
    lmd = FRAGS['dpb'].lmap(P12, P4)
    prr = FRAGS['rst'].pred(['J', 'K', 'I"', 'I0'], 'T', 'M', PL(P12, 3), lmd['Q0'])
    ex.update(unfold_all(w, ps, ex[prr], 'rst', ['J', 'K', 'I"', 'I0'], PL(P12, 3), lmd['Q0'], rec=False))
    lmr = FRAGS['rst'].lmap(PL(P12, 3), lmd['Q0'])
    prm = FRAGS['me'].pred(['J', 'K', 'I"'], 'T', 'M', PL(PL(P12, 3), 1), lmr['X1'])
    ex.update(unfold_all(w, ps, ex[prm], 'me', ['J', 'K', 'I"'], PL(PL(P12, 3), 1), lmr['X1'], rec=False))
    st = Bld(w, ps, f.c, ex)(LTREEd)
    w.qed([st, w.inst('tm2fdps')], 'syl', ST_Ld)
    return w.run()


def tmidps():
    lab = 'tmidps'
    ps = cj(TREE_DPS)
    w = W(lab, 'Lean\'s ` dpStepF_runs ` at the machine: wherever ` dpStepF np nL snap acc s t ` is installed, with ` p ` on '
               '` np ` , ` L ` on ` nL ` , the descending snapshot of the table ` A ` on ` snap ` and the ascending table on '
               '` acc ` ( ` TblBounded ` , ` p , L < 2 ^ b ` ), ` acc ` gets the table of ` Alg.dpStep L p A ` , ` p ` and the '
               'snapshot are consumed, every other stack restored, within ` dpC L N b ` steps (~ tmidpsl at the families of '
               '` DpInv ` , ~ ttdpcx ).')
    c = Ctx(w, ps, TREE_DPS)
    s = w.s
    eqs = {'%s = %s' % (F_, F_): closed(w, ps, 'eqid', '%s = %s' % (F_, F_)) for F_ in (PDFd, ZDFd, XDFd)}
    t, cc = inst(w, ps, 'tmidpsl', {"P'": PDFd, "Z'": ZDFd, "X'": XDFd}, Bld(w, ps, c, eqs))
    Ca, Da, na = triple_parts(cc)
    at, ln = c['A e. Tbl'], c['L e. NN']
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ps)
    tw = s([s([at, l0], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ps), w.inst('tttblw')], 'syl',
           '( %s -> ( ( A |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( A |` ( 0 ..^ L ) ) ) = L ) )' % (ps, WSLOT))
    wlw = s([tw], 'simpld', '( %s -> ( A |` ( 0 ..^ L ) ) e. %s )' % (ps, WSLOT))
    rl = s([s([wlw, w.inst('revlen')], 'syl', '( %s -> %s = ( # ` ( A |` ( 0 ..^ L ) ) ) )' % (ps, R_)), s([tw], 'simprd', '( %s -> ( # ` ( A |` ( 0 ..^ L ) ) ) = L )' % ps)],
           'eqtrd', '( %s -> %s = L )' % (ps, R_))
    n1eq, n1t = w.rewrite(na, {R_: ('L', rl)}, ps)
    cl = Closure(w, ps, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'L': ('NN', ln)})
    Z_ = '( L x. ( %s + 2 ) )' % DPBC
    le = s([s([c['B e. NN0'], cl.mem(SETCL, 'NN0'), cl.mem(Z_, 'NN0')], '3jca', '( %s -> ( B e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ps, SETCL, Z_)),
            w.inst('ttdpcx')], 'syl', '( %s -> %s <_ %s )' % (ps, n1t, DPC))
    t2, C2, D2, n2 = hrrw(w, ps, t, Ca, Da, na, neq=n1eq)
    mk = machine(w, ps, c, K6)
    hrle(w, ps, mk['phm'], t2, C2, D2, n2, DPC, cl.mem(DPC, 'NN0'), le, qed=True)
    return w.run()


def tmidpsb():
    lab = 'tmidpsb'
    ps = cj(TREE_DPS)
    w = W(lab, 'Lean\'s ` dpStepF_le_B ` at the machine: ~ tmidps within ` ( L + 1 ) ^ 2 ( N + 2 ) B b ` steps (~ ttabdpc ).')
    c = Ctx(w, ps, TREE_DPS)
    s = w.s
    t, cc = inst(w, ps, 'tmidps', {}, Bld(w, ps, c, {}))
    Ca, Da, na = triple_parts(cc)
    ln, nn, bn = c['L e. NN'], c['N e. NN0'], c['B e. NN0']
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ps)
    le = s([s([l0, nn, bn], '3jca', '( %s -> ( L e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) )' % ps), w.inst('ttabdpc')], 'syl', '( %s -> %s <_ %s )' % (ps, DPC, BLB2))
    cl = Closure(w, ps, {'N': ('NN0', nn), 'B': ('NN0', bn), 'L': ('NN', ln)})
    tb = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ps)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ps)
    cl.leaf('( TMB ` B )', 'NN0', tb)
    mk = machine(w, ps, c, K6)
    hrle(w, ps, mk['phm'], t, Ca, Da, na, BLB2, cl.mem(BLB2, 'NN0'), le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
