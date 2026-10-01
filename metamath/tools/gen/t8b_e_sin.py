"""T8b: setIfNoneF and lookupSlot at the machine (Lean ` setIfNoneF_runs ` , ` lookupSlot_runs ` )
on their installation predicates TMIsin, TMIlks.

  tmisin   ~ tm2fsin once per case of the slot ` ( L ` jn ) ` (none: pop and ~ tmimvs of the
           witness; some: ~ tmidpl ), the walks ~ tmiwdn , ~ tmiwup
  tmilks   ~ tm2flks (none: push ket; some: ~ tmilcpyn )

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_e_sin.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, lineq, nlinarith
from t8a_e_slot import disj_leaf, stkcl

SEL = sys.argv[1:]
NONE_ = '( inr ` (/) )'
O_ = '( L ` %s )' % JN
DR1 = DROP('L', '( %s + 1 )' % JN)
REST = CC(ES(DR1), 'X')
REVP = REV(PFX('L', JN))
V2 = CC(ES(REVP), '( <" 0 "> ++ ( D ` I" ) )')
V_ = CC(ES(DROP('L', JN)), 'X')
VP = CC(ESL(O_), REST)
UW = '( <" %s "> ++ %s )' % (FILL, DR1)
X4 = CC(ES(UW), 'X')
T1_SIN = SLOTC
TDL = '( ( ( # ` W ) x. ( B + 3 ) ) + 3 )'
T1_LKS = '( ( N x. ( ( 6 x. B ) + ; 1 7 ) ) + 9 )'
W2 = '( 2nd ` %s )' % O_


def L_(w, pc, ph, st):
    return w.s([st], 'adantr', '( %s -> %s )' % (pc, concl(w, ph, st)))


class Com:
    """the facts shared by both cases, under ph"""
    def __init__(self, w, ph, T, fname):
        self.w, self.ph, self.fname = w, ph, fname
        c, mk, ne, ex = hsetup(w, ph, T, K5, fname)
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        s = w.s
        lw, gw, xw, yw, dd = c['L e. %s' % WSLOT], c['G e. Word 2o'], c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
        self.lw, self.xw, self.dd = lw, xw, dd
        jnn = s([gw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, JN))
        ln = s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
        lz = s([ln], 'nn0zd', '( %s -> ( # ` L ) e. ZZ )' % ph)
        jlt = c['%s < ( # ` L )' % JN]
        j3 = s([jnn, lz, jlt], '3jca', '( %s -> ( %s e. NN0 /\\ ( # ` L ) e. ZZ /\\ %s < ( # ` L ) ) )' % (ph, JN, JN))
        jo = s([j3, w.inst('elfzo0z')], 'sylibr', '( %s -> %s e. ( 0 ..^ ( # ` L ) ) )' % (ph, JN))
        jfz = s([jo, w.inst('elfzofz')], 'syl', '( %s -> %s e. ( 0 ... ( # ` L ) ) )' % (ph, JN))
        self.jnn, self.jo, self.jfz = jnn, jo, jfz
        # the walkDown triple
        m_w = {'K': 'K', 'J': 'J', 'I': "I'", "I'": 'I"', 'P': PL('P', 3), 'E': PL('P', 0)}
        t1, cc1 = inst(w, ph, 'tmiwdn', m_w, Bld(w, ph, c, ex))
        Ca1, Da1, n1 = triple_parts(cc1)
        # typings
        swr = lambda X, st: s([st, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, X, WSLOT))
        esc = lambda X, st: s([st, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(X)))
        edr = esc(DROP('L', JN), swr(DROP('L', JN), lw))
        vw = s([edr, xw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, V_))
        pf = s([lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, PFX('L', JN), WSLOT))
        rp = s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REVP, WSLOT))
        self.pf, self.rp = pf, rp
        erp = esc(REVP, rp)
        g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
        s0 = s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
        vals = {k: selfval(w, ph, mk, 'D', dd, k) for k in K5}
        S0 = Stacks(w, ph, mk, 'D', dd, ne, vals)
        self.S0 = S0
        z0x = s([s0, vals['I"'][2], w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 0 \"> ++ ( D ` I\" ) ) e. Word Gamma' )" % ph)
        v2g = s([erp, z0x, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, V2))
        SW = S0.upd('K', V_, vw).upd('J', 'Y', yw).upd('I"', V2, v2g)
        assert Da1 == CLN(PL('P', 0), S, SW.D), Da1
        self.SW, self.t1, self.Ca1, self.n1 = SW, t1, Ca1, n1
        self.gam = {V_: vw, 'Y': yw, V2: v2g, '( D ` I )': vals['I'][2], '( D ` I" )': vals['I"'][2], 'X': xw}
        # the slot at jn and the rest
        ol = s([lw, jo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, O_, SLOT))
        eo = s([ol, s([s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi',
                      "( %s e. %s -> %s e. Word Gamma' )" % (O_, SLOT, ESL(O_)))], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ESL(O_)))
        dr1 = swr(DR1, lw)
        edr1 = esc(DR1, dr1)
        restw = s([edr1, xw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, REST))
        esd = s([lw, jo, w.inst('ttsesdrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES(DROP('L', JN)), ESL(O_), ES(DR1)))
        va = s([esd], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ X ) )' % (ph, V_, ESL(O_), ES(DR1)))
        vb = s([eo, edr1, xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ X ) = %s )' % (ph, ESL(O_), ES(DR1), VP))
        vvp = s([va, vb], 'eqtrd', '( %s -> %s = %s )' % (ph, V_, VP))
        self.dwk = s([SW.vals['K'][1], vvp], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, SW.D, VP))
        self.ol, self.eo, self.dr1, self.edr1, self.restw, self.vvp = ol, eo, dr1, edr1, restw, vvp
        self.vpw = s([eo, restw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, VP))
        self.sv = s([ol, w.inst('ttabslotv')], 'syl', '( %s -> %s = if ( %s = %s , <" 3 "> , ( encList ` %s ) ) )' % (ph, ESL(O_), O_, NONE_, W2))
        self.cl = Closure(w, ph, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'H': ('NN0', c['H e. NN0'])})
        self.cl.leaf(JN, 'NN0', jnn)

    def walkup(self, NU, SNU, U, uw, P6, post_rw):
        """the walkUp triple from C( A' , S , NU ) to C( E , S , FIN ); NU's I" value V2 and K value ES( U ) ++ X"""
        w, ph, c, mk = self.w, self.ph, self.c, self.mk
        s = w.s
        ex = dict(self.ex)
        # slot bounds of the reversed prefix
        r1 = s([self.pf, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (ph, REVP, PFX('L', JN)))
        pr = s([self.lw, self.jfz, w.inst('pfxres')], 'syl2anc', '( %s -> %s = ( L |` ( 0 ..^ %s ) ) )' % (ph, PFX('L', JN), JN))
        r2a = s([pr], 'rneqd', '( %s -> ran %s = ran ( L |` ( 0 ..^ %s ) ) )' % (ph, PFX('L', JN), JN))
        r2b = s([s([], 'rnresss', 'ran ( L |` ( 0 ..^ %s ) ) C_ ran L' % JN)], 'a1i', '( %s -> ran ( L |` ( 0 ..^ %s ) ) C_ ran L )' % (ph, JN))
        r2 = s([r2a, r2b], 'eqsstrd', '( %s -> ran %s C_ ran L )' % (ph, PFX('L', JN)))
        r3 = s([r1, r2], 'sstrd', '( %s -> ran %s C_ ran L )' % (ph, REVP))
        RSBP = 'A. o e. ran %s %s' % (REVP, SB('o'))
        ex[RSBP] = s([r3, c[RSB], w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ph, RSBP))
        ex[STKD(NU)] = SNU.memb
        ex['%s e. %s' % (REVP, WSLOT)] = self.rp
        ex['%s e. %s' % (U, WSLOT)] = uw
        ex["( %s ` I\" ) = %s" % (NU, V2)] = SNU.vals['I"'][1]
        ex["( %s ` K ) = %s" % (NU, CC(ES(U), 'X'))] = SNU.vals['K'][1]
        ex["( D ` I\" ) e. Word Gamma'"] = self.S0.vals['I"'][2]
        m_u = {'K': 'K', 'J': 'J', 'I': "I'", "I'": 'I"', 'P': P6, 'E': 'E', 'D': NU, 'L': REVP, 'U': U,
               'X': '( D ` I" )', 'Y': 'X'}
        t, cc = inst(w, ph, 'tmiwup', m_u, Bld(w, ph, c, ex))
        Ca, Da, n = triple_parts(cc)
        return t, Ca, Da, n

    def final_eq(self, chain, X5, X5to, x5eq, order):
        """normalize a chain whose last K value X5 is rewritten to X5to"""
        w, ph = self.w, self.ph
        raw = chain_text('D', chain)
        r, new = w.rewrite(raw, {X5: (X5to, x5eq)}, ph)
        ch2 = [(k, X5to if v == X5 else v) for k, v in chain]
        assert new == chain_text('D', ch2), new
        st, out = stk_normalize(w, ph, self.mk, 'D', self.dd, self.ne, ch2, self.gam, order)
        fin = chain_text('D', out)
        if st is None:
            return r, fin
        return w.s([r, st], 'eqtrd', '( %s -> %s = %s )' % (ph, raw, fin)), fin


def cases_and_generic(w, ph, com, generic, m0, case_fn, T, ex0):
    """instantiate the generic once per case of O = none; combine by pm2.61dne"""
    outs = []
    for cond in ('%s = %s' % (O_, NONE_), '%s =/= %s' % (O_, NONE_)):
        pc = '( %s /\\ %s )' % (ph, cond)
        cpc = Ctx(w, pc, (T, cond))
        m = dict(m0)
        exc = case_fn(pc, cond, m, cpc)
        bld = LazyBld(w, pc, ph, cpc, dict(com.ex, **ex0), exc)
        t, cc = inst(w, pc, generic, m, bld)
        outs.append((w.s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, cc)), cc))
    assert outs[0][1] == outs[1][1], (outs[0][1], outs[1][1])
    cc = outs[0][1]
    return w.s([outs[0][0], outs[1][0]], 'pm2.61dne', '( %s -> %s )' % (ph, cc)), cc


class LazyBld(Bld):
    """a Builder under pc whose extra leaves from ph are lifted by adantr on demand"""
    def __init__(self, w, pc, ph, ctx, phex, pcex):
        Bld.__init__(self, w, pc, ctx, pcex)
        self.ph0, self.phex = ph, phex

    def __call__(self, tree):
        key = cj(tree)
        if key in self.known:
            return self.known[key]
        if key in self.phex:
            st = L_(self.w, self.ph, self.ph0, self.phex[key])
            self.known[key] = st
            return st
        return Bld.__call__(self, tree)


def dk_none(w, pc, com):
    """( pc -> ( encSlot ` O ) = <" 3 "> ) and ( pc -> ( DW ` K ) = ( <" 3 "> ++ REST ) )"""
    cs = w.s([], 'simpr', '( %s -> %s = %s )' % (pc, O_, NONE_))
    it = w.s([cs], 'iftrued', '( %s -> if ( %s = %s , <" 3 "> , ( encList ` %s ) ) = <" 3 "> )' % (pc, O_, NONE_, W2))
    e3 = w.s([L_(w, pc, com.ph, com.sv), it], 'eqtrd', '( %s -> %s = <" 3 "> )' % (pc, ESL(O_)))
    dk = w.s([L_(w, pc, com.ph, com.dwk), w.s([e3], 'oveq1d', '( %s -> %s = ( <" 3 "> ++ %s ) )' % (pc, VP, REST))], 'eqtrd',
             '( %s -> ( %s ` K ) = ( <" 3 "> ++ %s ) )' % (pc, com.SW.D, REST))
    return cs, e3, dk


def peek_some(w, pc, com, mk):
    """case some: the split of VP, the flag, the peek interface"""
    ph = com.ph
    en = w.s([L_(w, pc, ph, com.ol), w.inst('ttslotn0')], 'syl', '( %s -> %s =/= (/) )' % (pc, ESL(O_)))
    c0 = w.s([L_(w, pc, ph, com.eo), L_(w, pc, ph, com.restw), w.inst('ccat0')], 'syl2anc',
             '( %s -> ( %s = (/) <-> ( %s = (/) /\\ %s = (/) ) ) )' % (pc, VP, ESL(O_), REST))
    n1 = w.s([w.s([en], 'neneqd', '( %s -> -. %s = (/) )' % (pc, ESL(O_)))], 'intnanrd', '( %s -> -. ( %s = (/) /\\ %s = (/) ) )' % (pc, ESL(O_), REST))
    vn0 = w.s([w.s([c0, n1], 'mtbird', '( %s -> -. %s = (/) )' % (pc, VP))], 'neqned', '( %s -> %s =/= (/) )' % (pc, VP))
    eqV, hg, tg = word_split(w, pc, VP, L_(w, pc, ph, com.vpw), vn0)
    Z, X = HD0(VP), TL1(VP)
    dk = w.s([L_(w, pc, ph, com.dwk), eqV], 'eqtrd', '( %s -> ( %s ` K ) = ( <" %s "> ++ %s ) )' % (pc, com.SW.D, Z, X))
    sk = w.s([L_(w, pc, ph, com.ol), L_(w, pc, ph, com.restw), w.inst('ttabslotk')], 'syl2anc', '( %s -> ( %s = 3 <-> %s = %s ) )' % (pc, Z, O_, NONE_))
    cs = w.s([], 'simpr', '( %s -> %s =/= %s )' % (pc, O_, NONE_))
    nn = w.s([cs], 'neneqd', '( %s -> -. %s = %s )' % (pc, O_, NONE_))
    nz = w.s([sk, nn], 'mtbird', '( %s -> -. %s = 3 )' % (pc, Z))
    ifq = w.s([nz], 'iffalsed', '( %s -> if ( %s = 3 , 1o , (/) ) = (/) )' % (pc, Z))
    pk = peek_iface(w, pc, mk, RDK, Z, hg, ifq, '(/)')
    itf = w.s([nn], 'iffalsed', '( %s -> if ( %s = %s , <" 3 "> , ( encList ` %s ) ) = ( encList ` %s ) )' % (pc, O_, NONE_, W2, W2))
    enc = w.s([L_(w, pc, ph, com.sv), itf], 'eqtrd', '( %s -> %s = ( encList ` %s ) )' % (pc, ESL(O_), W2))
    return Z, X, dk, hg, tg, pk, nn, enc


def fill_facts(w, ph, com, fillcl):
    """UW typing, ES( UW ) = ESL( FILL ) ++ ES( DR1 ), X4 = ESL( FILL ) ++ REST"""
    s = w.s
    s1 = s([fillcl], 's1cld', '( %s -> <" %s "> e. %s )' % (ph, FILL, WSLOT))
    uw = s([s1, com.dr1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, UW, WSLOT))
    ec = s([s1, com.dr1, w.inst('ttsesccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES(UW), ES('<" %s ">' % FILL), ES(DR1)))
    e1 = s([fillcl, w.inst('ttsess1')], 'syl', '( %s -> %s = %s )' % (ph, ES('<" %s ">' % FILL), ESL(FILL)))
    r, new = w.rewrite(ES(UW), {ES('<" %s ">' % FILL): (ESL(FILL), e1)}, ph) if False else (None, None)
    e2 = s([ec, s([e1], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, ES('<" %s ">' % FILL), ES(DR1), ESL(FILL), ES(DR1)))],
           'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES(UW), ESL(FILL), ES(DR1)))
    efw = s([fillcl, s([s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi',
                       "( %s e. %s -> %s e. Word Gamma' )" % (FILL, SLOT, ESL(FILL)))], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ESL(FILL)))
    x1 = s([e2], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ X ) )' % (ph, X4, ESL(FILL), ES(DR1)))
    x2 = s([efw, com.edr1, com.xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ X ) = ( %s ++ %s ) )' % (ph, ESL(FILL), ES(DR1), ESL(FILL), REST))
    x4 = s([x1, x2], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ph, X4, ESL(FILL), REST))
    x4w = s([s([uw, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(UW))), com.xw, w.inst('ccatcl')], 'syl2anc',
            "( %s -> %s e. Word Gamma' )" % (ph, X4))
    return uw, x4, x4w


def fill_case(w, pc, ph, com, x4, val, valeq):
    """( pc -> ( ( encSlot ` val ) ++ REST ) = X4 ) from valeq : ( pc -> FILL = val )"""
    e = w.s([w.s([valeq], 'fveq2d', '( %s -> %s = %s )' % (pc, ESL(FILL), ESL(val)))], 'oveq1d',
            '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (pc, ESL(FILL), REST, ESL(val), REST))
    return w.s([L_(w, pc, ph, x4), e], 'eqtr2d' if False else 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (pc, X4, ESL(val), REST))


def tmisin():
    lab = 'tmisin'
    ph = cj(TREE_SIN)
    w = W(lab, 'Lean\'s ` setIfNoneF_runs ` at the machine: wherever ` setIfNoneF tbl j w s scr ` is installed, the '
               'slot ` jn = toNat js ` of the slot list ` L ` on ` tbl ` is filled with the witness ` W ` on ` w ` if it is '
               'empty ( Lean\'s ` setSlotL ` , written ` take ++ fillSlot :: drop ` ), the index on ` j ` and the witness '
               'are consumed, every other stack restored, within ` setC jn N b m ` steps (~ tm2fsin with ~ tmiwdn , '
               '~ tmimvs / ~ tmidpl , ~ tmiwup ).')
    com = Com(w, ph, TREE_SIN, 'sin')
    c, mk, s = com.c, com.mk, w.s
    wn, rw = c['W e. Word NN0'], c[WRD('R', GAM)]
    dI = c['( D ` I ) = ( ( encList ` W ) ++ R )']
    com.gam['R'] = rw
    # FILL e. SLOT
    iw = s([wn, w.inst('djulcl')], 'syl', '( %s -> ( inl ` W ) e. %s )' % (ph, SLOT))
    fillcl = s([iw, com.ol], 'ifcld', '( %s -> %s e. %s )' % (ph, FILL, SLOT))
    uw, x4, x4w = fill_facts(w, ph, com, fillcl)
    com.gam[X4] = x4w
    # NU and the walkUp
    SW = com.SW
    SNU = SW.upd('K', X4, x4w).upd('I', 'R', rw)
    chainNU = [('K', V_), ('J', 'Y'), ('I"', V2), ('K', X4), ('I', 'R')]
    stn, outn = stk_normalize(w, ph, mk, 'D', com.dd, com.ne, chainNU, com.gam, K5)
    NU = chain_text('D', outn)
    assert outn == [('K', X4), ('J', 'Y'), ('I', 'R'), ('I"', V2)], outn
    SNU = com.S0.upd('K', X4, x4w).upd('J', 'Y', c[WRD('Y', GAM)]).upd('I', 'R', rw).upd('I"', V2, com.gam[V2])
    assert SNU.D == NU
    tu, Cu, Du, nu = com.walkup(NU, SNU, UW, uw, PL('P', 6), None)
    # the walkUp's post: [ NU chain , K : X5 , I" : ( D ` I" ) ]
    X5 = CC(ES('( %s ++ %s )' % (REV(REVP), UW)), 'X')
    X5to = CC(ES(SSL), 'X')
    rr = s([com.pf, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, REV(REVP), PFX('L', JN)))
    x5e = s([s([s([rr], 'oveq1d', '( %s -> ( %s ++ %s ) = %s )' % (ph, REV(REVP), UW, SSL))], 'fveq2d',
                '( %s -> %s = %s )' % (ph, ES('( %s ++ %s )' % (REV(REVP), UW)), ES(SSL)))], 'oveq1d', '( %s -> %s = %s )' % (ph, X5, X5to))
    ssw = s([com.pf, uw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, SSL, WSLOT))
    com.gam[X5to] = s([s([ssw, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ES(SSL))), com.xw, w.inst('ccatcl')],
                      'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, X5to))
    fe, fin = com.final_eq(outn + [('K', X5), ('I"', '( D ` I" )')], X5, X5to, x5e, K5)
    assert fin == DFIN_SIN, fin
    tu, Cu, Du, nu = hrrw(w, ph, tu, Cu, Du, nu, deq=clneq(w, ph, 'E', S, fe, chain_text('D', outn + [('K', X5), ('I"', '( D ` I" )')]), DFIN_SIN))
    # the bounds
    cl = com.cl
    cl.leaf('( # ` W )', 'NN0', s([wn, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph))
    ex0 = {}
    ex0['%s e. NN0' % T1_SIN] = cl.mem(T1_SIN, 'NN0')
    ex0['%s e. NN0' % TDL] = cl.mem(TDL, 'NN0')
    ex0['%s <_ ( %s + 1 )' % (TDL, T1_SIN)] = nlinarith(w, ph, [c['( # ` W ) <_ N'], cl.ge0('B'), cl.ge0('( # ` W )')],
                                                       '%s <_ ( %s + 1 )' % (TDL, T1_SIN), closure=cl)
    ex0['%s e. NN0' % com.n1] = cl.mem(com.n1, 'NN0')
    LR = '( # ` %s )' % REVP
    cl.leaf(LR, 'NN0', s([com.rp, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LR)))
    ex0['%s e. NN0' % nu] = cl.mem(nu, 'NN0')
    ex0[TRI(com.Ca1, CLN(PL('P', 0), S, SW.D), com.n1)] = com.t1
    ex0[TRI(Cu, Du, nu)] = tu
    ex0[STKD(SW.D)] = SW.memb
    ex0[SSS(NFL('1o'))] = nfl_ss(w, ph, mk, '1o')
    ex0[SSS(NFL('(/)'))] = nfl_ss(w, ph, mk, '(/)')
    lm = FRAGS['sin'].lmap()
    m0 = dict(lm)
    m0.update({'K': 'K', 'F': RDK, 'C': 'TMfl', "F'": PID, "D'": SW.D, 'U': com.n1, "U'": nu, 'T1': T1_SIN, 'T"': TDL,
               'N1': S, 'N0': S, "N'": S, 'N': S, 'D': 'D', 'O': S, 'D0': DFIN_SIN, 'D"': NU})

    def case_fn(pc, cond, m, cpc):
        ex = {}
        mkp = lift_mk(w, pc, ph, mk)
        if cond.startswith(O_ + ' = '):
            cs, e3, dk = dk_none(w, pc, com)
            m.update({'Z': '3', 'X': REST, 'N"': NFL('1o')})
            ex['( %s ` K ) = ( <" 3 "> ++ %s )' % (SW.D, REST)] = dk
            ex[WRD(REST, GAM)] = L_(w, pc, ph, com.restw)
            ifq = w.s([w.s([], 'eqidd', '( %s -> 3 = 3 )' % pc)], 'iftrued', '( %s -> if ( 3 = 3 , 1o , (/) ) = 1o )' % pc)
            ex['A. r e. %s ( %s ` <. r , ( inl ` 3 ) >. ) e. %s' % (S, RDK, NFL('1o'))] = peek_iface(w, pc, mkp, RDK, '3', L_(w, pc, ph, com.ex["3 e. Gamma'"]), ifq, '1o')
            ht = ht_nfl(w, pc, '1o')
            nss = L_(w, pc, ph, ex0[SSS(NFL('1o'))])
            pop = pop_iface(w, pc, mkp, NFL('1o'), nss, '3', L_(w, pc, ph, com.ex["3 e. Gamma'"]))
            # moveSlot of ( inl ` W ) from w onto tbl at Dc = UPD( DW , K , REST )
            Sc = SW.upd('K', REST, com.restw)
            Dc = Sc.D
            iwv = L_(w, pc, ph, s([wn], 'elexd', '( %s -> W e. _V )' % ph))
            i2 = s([iwv, w.inst('2ndinl')], 'syl', '( %s -> ( 2nd ` ( inl ` W ) ) = W )' % pc)
            inr = s([iwv, w.inst('tmcinlne')], 'syl', '( %s -> -. ( inl ` W ) = %s )' % (pc, NONE_))
            iwc = L_(w, pc, ph, iw)
            svw = s([iwc, w.inst('ttabslotv')], 'syl', '( %s -> %s = if ( ( inl ` W ) = %s , <" 3 "> , ( encList ` ( 2nd ` ( inl ` W ) ) ) ) )'
                    % (pc, ESL('( inl ` W )'), NONE_))
            if2 = s([inr], 'iffalsed', '( %s -> if ( ( inl ` W ) = %s , <" 3 "> , ( encList ` ( 2nd ` ( inl ` W ) ) ) ) = ( encList ` ( 2nd ` ( inl ` W ) ) ) )'
                    % (pc, NONE_))
            e2 = s([i2], 'fveq2d', '( %s -> ( encList ` ( 2nd ` ( inl ` W ) ) ) = ( encList ` W ) )' % pc)
            esw = s([s([svw, if2], 'eqtrd', '( %s -> %s = ( encList ` ( 2nd ` ( inl ` W ) ) ) )' % (pc, ESL('( inl ` W )'))), e2], 'eqtrd',
                    '( %s -> %s = ( encList ` W ) )' % (pc, ESL('( inl ` W )')))
            dci = s([L_(w, pc, ph, Sc.vals['I'][1]), L_(w, pc, ph, dI)], 'eqtrd', '( %s -> ( %s ` I ) = ( ( encList ` W ) ++ R ) )' % (pc, Dc))
            dci2 = s([dci, s([esw], 'oveq1d', '( %s -> ( %s ++ R ) = ( ( encList ` W ) ++ R ) )' % (pc, ESL('( inl ` W )')))], 'eqtr4d',
                     '( %s -> ( %s ` I ) = ( %s ++ R ) )' % (pc, Dc, ESL('( inl ` W )')))
            l2 = s([s([i2], 'fveq2d', '( %s -> ( # ` ( 2nd ` ( inl ` W ) ) ) = ( # ` W ) )' % pc), L_(w, pc, ph, c['( # ` W ) <_ N'])], 'eqbrtrd',
                   '( %s -> ( # ` ( 2nd ` ( inl ` W ) ) ) <_ N )' % pc)
            rq = s([s([i2], 'rneqd', '( %s -> ran ( 2nd ` ( inl ` W ) ) = ran W )' % pc), w.inst('raleq')], 'syl',
                   '( %s -> ( A. a e. ran ( 2nd ` ( inl ` W ) ) a < ( 2 ^ B ) <-> A. a e. ran W a < ( 2 ^ B ) ) )' % pc)
            r2 = s([L_(w, pc, ph, c['A. a e. ran W a < ( 2 ^ B )']), rq], 'mpbird', '( %s -> A. a e. ran ( 2nd ` ( inl ` W ) ) a < ( 2 ^ B ) )' % pc)
            cj2 = s([l2, r2], 'jca', '( %s -> ( ( # ` ( 2nd ` ( inl ` W ) ) ) <_ N /\\ A. a e. ran ( 2nd ` ( inl ` W ) ) a < ( 2 ^ B ) ) )' % pc)
            sbw = s([cj2], 'a1d', '( %s -> %s )' % (pc, SB('( inl ` W )')))
            exm = {STKD(Dc): L_(w, pc, ph, Sc.memb), '( inl ` W ) e. %s' % SLOT: iwc, '( %s ` I ) = ( %s ++ R )' % (Dc, ESL('( inl ` W )')): dci2,
                   SB('( inl ` W )'): sbw}
            MV = {'K': 'I', 'J': 'K', 'I': "I'", "I'": 'J', 'P': PL('P', 4), 'E': PL(PL('P', 6), 0), 'D': Dc, 'O': '( inl ` W )', 'R': 'R'}
            tm, ccm = inst(w, pc, 'tmimvs', MV, LazyBld(w, pc, ph, cpc, dict(com.ex, **ex0), exm))
            Cm, Dm, nm = triple_parts(ccm)
            EWc = CC(ESL('( inl ` W )'), '( %s ` K )' % Dc)
            assert Dm == CLN(PL(PL('P', 6), 0), S, UP(UP(Dc, 'I', 'R'), 'K', EWc)), Dm
            # post -> NU
            dck = L_(w, pc, ph, Sc.vals['K'][1])
            fromK = CC(ESL('( inl ` W )'), REST)
            r1, x1 = w.rewrite(UP(UP(Dc, 'I', 'R'), 'K', EWc), {'( %s ` K )' % Dc: (REST, dck)}, pc)
            chain = [('K', V_), ('J', 'Y'), ('I"', V2), ('K', REST), ('I', 'R'), ('K', fromK)]
            assert x1 == chain_text('D', chain), x1
            filleq = s([cs], 'iftrued', '( %s -> %s = ( inl ` W ) )' % (pc, FILL))
            fk = fill_case(w, pc, ph, com, x4, '( inl ` W )', filleq)
            fkr = s([fk], 'eqcomd', '( %s -> %s = %s )' % (pc, fromK, X4))
            gam = dict(com.gam)
            gam[REST] = L_(w, pc, ph, com.restw)
            gam[fromK] = s([L_(w, pc, ph, x4w), fk], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (pc, fromK))
            gam = {k: (L_(w, pc, ph, v) if k not in (REST, fromK) else v) for k, v in gam.items()}
            mkc = lift_mk(w, pc, ph, mk)
            r2_, x2 = w.rewrite(x1, {fromK: (X4, fkr)}, pc)
            ch2 = [(k, X4 if v == fromK else v) for k, v in chain]
            nst, out = stk_normalize(w, pc, mkc, 'D', L_(w, pc, ph, com.dd), lambda a, b: L_(w, pc, ph, com.ne(a, b)), ch2, gam, K5)
            assert chain_text('D', out) == NU, chain_text('D', out)
            de = s([s([r1, r2_], 'eqtrd', '( %s -> %s = %s )' % (pc, UP(UP(Dc, 'I', 'R'), 'K', EWc), x2)), nst], 'eqtrd',
                   '( %s -> %s = %s )' % (pc, UP(UP(Dc, 'I', 'R'), 'K', EWc), NU))
            tm2, Cm2, Dm2, nm2 = hrrw(w, pc, tm, Cm, Dm, nm, deq=clneq(w, pc, PL(PL('P', 6), 0), S, de, UP(UP(Dc, 'I', 'R'), 'K', EWc), NU))
            d, d1, d2 = disj_leaf('tm2fsin', m)
            dj1 = s([ht, pop, tm2], '3jca', '( %s -> %s )' % (pc, d1))
            ex[d] = s([dj1], 'orcd', '( %s -> %s )' % (pc, d))
        else:
            Z, X, dk, hg, tg, pk, nn, enc = peek_some(w, pc, com, mkp)
            m.update({'Z': Z, 'X': X, 'N"': NFL('(/)')})
            ex['( %s ` K ) = ( <" %s "> ++ %s )' % (SW.D, Z, X)] = dk
            ex["%s e. Gamma'" % Z] = hg
            ex[WRD(X, GAM)] = tg
            ex['A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDK, Z, NFL('(/)'))] = pk
            htf = ht_nfl(w, pc, '(/)')
            # dropList w at DW
            dwi = s([L_(w, pc, ph, SW.vals['I'][1]), L_(w, pc, ph, dI)], 'eqtrd', '( %s -> ( %s ` I ) = ( ( encList ` W ) ++ R ) )' % (pc, SW.D))
            exd = {STKD(SW.D): L_(w, pc, ph, SW.memb), '( %s ` I ) = ( ( encList ` W ) ++ R )' % SW.D: dwi}
            DP = {'K': 'I', 'P': PL('P', 5), 'E': PL(PL('P', 6), 0), 'D': SW.D, 'L': 'W', 'R': 'R'}
            td, ccd = inst(w, pc, 'tmidpl', DP, LazyBld(w, pc, ph, cpc, dict(com.ex, **ex0), exd))
            Cd, Dd, nd = triple_parts(ccd)
            E0 = PL(PL('P', 5), 0)
            nss = L_(w, pc, ph, ex0[SSS(NFL('(/)'))])
            td = hrssc(w, pc, mk_phm(w, pc, ph, mk), td, Cd, Dd, nd, CLN(E0, NFL('(/)'), SW.D), clnss(w, pc, E0, NFL('(/)'), S, SW.D, nss))
            Cd = CLN(E0, NFL('(/)'), SW.D)
            chain = [('K', V_), ('J', 'Y'), ('I"', V2), ('I', 'R')]
            assert Dd == CLN(PL(PL('P', 6), 0), S, chain_text('D', chain)), Dd
            filleq = s([nn], 'iffalsed', '( %s -> %s = %s )' % (pc, FILL, O_))
            fk = fill_case(w, pc, ph, com, x4, O_, filleq)
            vx = s([L_(w, pc, ph, com.vvp), fk], 'eqtr4d', '( %s -> %s = %s )' % (pc, V_, X4))
            gam = {k: L_(w, pc, ph, v) for k, v in com.gam.items()}
            mkc = lift_mk(w, pc, ph, mk)
            r1, x1 = w.rewrite(chain_text('D', chain), {V_: (X4, vx)}, pc)
            ch2 = [(k, X4 if v == V_ else v) for k, v in chain]
            nst, out = stk_normalize(w, pc, mkc, 'D', L_(w, pc, ph, com.dd), lambda a, b: L_(w, pc, ph, com.ne(a, b)), ch2, gam, K5)
            assert chain_text('D', out) == NU
            de = s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (pc, chain_text('D', chain), NU))
            td2, Cd2, Dd2, nd2 = hrrw(w, pc, td, Cd, Dd, nd, deq=clneq(w, pc, PL(PL('P', 6), 0), S, de, chain_text('D', chain), NU))
            d, d1, d2 = disj_leaf('tm2fsin', m)
            dj2 = s([htf, td2], 'jca', '( %s -> %s )' % (pc, d2))
            ex[d] = s([dj2], 'olcd', '( %s -> %s )' % (pc, d))
        return ex

    t, cc = cases_and_generic(w, ph, com, 'tm2fsin', m0, case_fn, TREE_SIN, ex0)
    C, D, n = triple_parts(cc)
    # the bound: rewrite # REVP to jn, then setC
    rl = s([com.pf, w.inst('revlen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ph, LR, PFX('L', JN)))
    pl = s([com.lw, com.jfz, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, PFX('L', JN), JN))
    lrj = s([rl, pl], 'eqtrd', '( %s -> %s = %s )' % (ph, LR, JN))
    n1eq, n1t = w.rewrite(n, {LR: (JN, lrj)}, ph)
    j3 = s([com.jnn, cl.mem(SLOTC, 'NN0'), c['H e. NN0']], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ H e. NN0 ) )' % (ph, JN, SLOTC))
    n2eq = s([j3, w.inst('ttsetcx')], 'syl', '( %s -> %s = %s )' % (ph, n1t, SETC(JN, 'N', 'H')))
    neq = s([n1eq, n2eq], 'eqtrd', '( %s -> %s = %s )' % (ph, n, SETC(JN, 'N', 'H')))
    hrrw(w, ph, t, C, D, n, neq=neq, qed=True)
    return w.run()



def tmilks():
    lab = 'tmilks'
    ph = cj(TREE_LKS)
    w = W(lab, 'Lean\'s ` lookupSlot_runs ` at the machine: wherever ` lookupSlot tbl j w s scr ` is installed, a copy '
               'of slot ` jn = toNat js ` of the slot list ` L ` on ` tbl ` is pushed on ` w ` , the index on ` j ` is '
               'consumed, ` tbl ` and every other stack restored, within ` lookC jn N b m ` steps (~ tm2flks with '
               '~ tmiwdn , ` ket ` pushed / ~ tmilcpyn , ~ tmiwup ).')
    com = Com(w, ph, TREE_LKS, 'lks')
    c, mk, s = com.c, com.mk, w.s
    SW = com.SW
    EI = CC(ESL(O_), '( D ` I )')
    eiw = s([com.eo, com.S0.vals['I'][2], w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, EI))
    com.gam[EI] = eiw
    com.gam['( D ` K )'] = com.S0.vals['K'][2]
    SNU = com.S0.upd('K', V_, com.gam[V_]).upd('J', 'Y', c[WRD('Y', GAM)]).upd('I', EI, eiw).upd('I"', V2, com.gam[V2])
    NU = SNU.D
    DRJ = DROP('L', JN)
    dw = s([com.lw, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DRJ, WSLOT))
    tu, Cu, Du, nu = com.walkup(NU, SNU, DRJ, dw, PL('P', 5), None)
    X5 = CC(ES('( %s ++ %s )' % (REV(REVP), DRJ)), 'X')
    rr = s([com.pf, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, REV(REVP), PFX('L', JN)))
    pc_ = s([com.lw, com.jfz, w.inst('pfxcctswrd')], 'syl2anc', '( %s -> ( %s ++ %s ) = L )' % (ph, PFX('L', JN), DRJ))
    e1 = s([s([rr], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, REV(REVP), DRJ, PFX('L', JN), DRJ)), pc_], 'eqtrd',
           '( %s -> ( %s ++ %s ) = L )' % (ph, REV(REVP), DRJ))
    e2 = s([s([e1], 'fveq2d', '( %s -> %s = %s )' % (ph, ES('( %s ++ %s )' % (REV(REVP), DRJ)), ES('L')))], 'oveq1d',
           '( %s -> %s = ( %s ++ X ) )' % (ph, X5, ES('L')))
    x5e = s([e2, c['( D ` K ) = ( %s ++ X )' % ES('L')]], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (ph, X5))
    ch = [('K', V_), ('J', 'Y'), ('I', EI), ('I"', V2), ('K', X5), ('I"', '( D ` I" )')]
    fe, fin = com.final_eq(ch, X5, '( D ` K )', x5e, K5)
    assert fin == DFIN_LKS, fin
    tu, Cu, Du, nu = hrrw(w, ph, tu, Cu, Du, nu, deq=clneq(w, ph, 'E', S, fe, chain_text('D', ch), DFIN_LKS))
    cl = com.cl
    LR = '( # ` %s )' % REVP
    cl.leaf(LR, 'NN0', s([com.rp, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LR)))
    ex0 = {'%s e. NN0' % T1_LKS: cl.mem(T1_LKS, 'NN0'), '%s e. NN0' % com.n1: cl.mem(com.n1, 'NN0'), '%s e. NN0' % nu: cl.mem(nu, 'NN0'),
           '1 <_ %s' % T1_LKS: nlinarith(w, ph, [cl.ge0('N'), cl.ge0('B')], '1 <_ %s' % T1_LKS, closure=cl),
           TRI(com.Ca1, CLN(PL('P', 0), S, SW.D), com.n1): com.t1, STKD(SW.D): SW.memb,
           SSS(NFL('1o')): nfl_ss(w, ph, mk, '1o'), SSS(NFL('(/)')): nfl_ss(w, ph, mk, '(/)'), STKD(NU): SNU.memb}
    m0 = dict(FRAGS['lks'].lmap())
    m0.update({'K': 'K', 'J': 'I', 'F': RDK, 'C': 'TMfl', 'Y': KET, "D'": SW.D, 'U': com.n1, "U'": nu, 'T1': T1_LKS,
               'N1': S, "N'": S, 'N': S, 'D': 'D', 'O': S, 'D0': DFIN_LKS})

    def case_fn(pc, cond, m, cpc):
        ex = {}
        mkp = lift_mk(w, pc, ph, mk)
        g3 = L_(w, pc, ph, com.ex["3 e. Gamma'"])
        if cond.startswith(O_ + ' = '):
            cs, e3, dk = dk_none(w, pc, com)
            DN = UP(SW.D, 'I', CC('<" 3 ">', '( %s ` I )' % SW.D))
            m.update({'Z': '3', 'X': REST, 'N"': NFL('1o'), 'D"': DN})
            ex['( %s ` K ) = ( <" 3 "> ++ %s )' % (SW.D, REST)] = dk
            ex[WRD(REST, GAM)] = L_(w, pc, ph, com.restw)
            ifq = s([s([], 'eqidd', '( %s -> 3 = 3 )' % pc)], 'iftrued', '( %s -> if ( 3 = 3 , 1o , (/) ) = 1o )' % pc)
            ex['A. r e. %s ( %s ` <. r , ( inl ` 3 ) >. ) e. %s' % (S, RDK, NFL('1o'))] = peek_iface(w, pc, mkp, RDK, '3', g3, ifq, '1o')
            # DN = NU
            r1, x1 = w.rewrite(DN, {'( %s ` I )' % SW.D: ('( D ` I )', L_(w, pc, ph, SW.vals['I'][1])),
                                    '<" 3 ">': (ESL(O_), s([e3], 'eqcomd', '( %s -> <" 3 "> = %s )' % (pc, ESL(O_))))}, pc)
            ch = [('K', V_), ('J', 'Y'), ('I"', V2), ('I', EI)]
            assert x1 == chain_text('D', ch), x1
            gam = {k: L_(w, pc, ph, v) for k, v in com.gam.items()}
            nst, out = stk_normalize(w, pc, mkp, 'D', L_(w, pc, ph, com.dd), lambda a, b: L_(w, pc, ph, com.ne(a, b)), ch, gam, K5)
            assert chain_text('D', out) == NU
            dq = s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (pc, DN, NU))
            A5 = PL(PL('P', 5), 0)
            ex[STKD(DN)] = s([dq, L_(w, pc, ph, SNU.memb)], 'eqeltrd', '( %s -> %s e. %s )' % (pc, DN, STK_T))
            ceq = clneq(w, pc, A5, S, s([dq], 'eqcomd', '( %s -> %s = %s )' % (pc, NU, DN)), NU, DN)
            tuc, Cuc, Duc, nuc = hrrw(w, pc, L_(w, pc, ph, tu), Cu, Du, nu, ceq=ceq)
            ex[TRI(Cuc, Duc, nuc)] = tuc
            d, d1, d2 = disj_leaf('tm2flks', m)
            dj1 = s([ht_nfl(w, pc, '1o'), L_(w, pc, ph, ex0[SSS(NFL('1o'))]), s([], 'eqidd', '( %s -> %s = %s )' % (pc, DN, DN))],
                    '3jca', '( %s -> %s )' % (pc, d1))
            ex[d] = s([dj1], 'orcd', '( %s -> %s )' % (pc, d))
        else:
            Z, X, dk, hg, tg, pk, nn, enc = peek_some(w, pc, com, mkp)
            m.update({'Z': Z, 'X': X, 'N"': NFL('(/)'), 'D"': NU})
            ex['( %s ` K ) = ( <" %s "> ++ %s )' % (SW.D, Z, X)] = dk
            ex["%s e. Gamma'" % Z] = hg
            ex[WRD(X, GAM)] = tg
            ex['A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDK, Z, NFL('(/)'))] = pk
            ex[TRI(Cu, Du, nu)] = L_(w, pc, ph, tu)
            # the slot bound of O
            lr = L_(w, pc, ph, s([com.lw, com.jo, w.inst('algranfv')], 'syl2anc', '( %s -> %s e. ran L )' % (ph, O_)))
            ido = s([], 'id', '( o = %s -> o = %s )' % (O_, O_))
            cg, new = w.wcongr(SB('o'), {'o': O_}, 'o = %s' % O_, {'o': ido})
            rsp = s([cg], 'rspcv', '( %s e. ran L -> ( %s -> %s ) )' % (O_, RSB, SB(O_)))
            sbo = s([lr, L_(w, pc, ph, c[RSB]), rsp], 'sylc', '( %s -> %s )' % (pc, SB(O_)))
            cs = s([], 'simpr', '( %s -> %s =/= %s )' % (pc, O_, NONE_))
            both = s([cs, sbo], 'mpd', '( %s -> ( ( # ` %s ) <_ N /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (pc, W2, W2))
            w2le = s([both], 'simpld', '( %s -> ( # ` %s ) <_ N )' % (pc, W2))
            w2r = s([both], 'simprd', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (pc, W2))
            w2w = s([L_(w, pc, ph, com.ol), w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, W2))
            dkl = s([L_(w, pc, ph, com.dwk), s([enc], 'oveq1d', '( %s -> %s = ( ( encList ` %s ) ++ %s ) )' % (pc, VP, W2, REST))], 'eqtrd',
                    '( %s -> ( %s ` K ) = ( ( encList ` %s ) ++ %s ) )' % (pc, SW.D, W2, REST))
            exc = {STKD(SW.D): L_(w, pc, ph, SW.memb), '( %s ` K ) = ( ( encList ` %s ) ++ %s )' % (SW.D, W2, REST): dkl,
                   '%s e. Word NN0' % W2: w2w, 'A. a e. ran %s a < ( 2 ^ B )' % W2: w2r, WRD(REST, GAM): L_(w, pc, ph, com.restw)}
            CP = {'K': 'K', 'J': 'I', 'I': "I'", "I'": 'J', 'P': PL('P', 4), 'E': PL(PL('P', 5), 0), 'D': SW.D, 'L': W2, 'R': REST}
            tc, ccc = inst(w, pc, 'tmilcpyn', CP, LazyBld(w, pc, ph, cpc, dict(com.ex, **ex0), exc))
            Cc, Dc, nc = triple_parts(ccc)
            E0 = PL(PL('P', 4), 0)
            nss = L_(w, pc, ph, ex0[SSS(NFL('(/)'))])
            tc = hrssc(w, pc, mkp['phm'], tc, Cc, Dc, nc, CLN(E0, NFL('(/)'), SW.D), clnss(w, pc, E0, NFL('(/)'), S, SW.D, nss))
            Cc = CLN(E0, NFL('(/)'), SW.D)
            EW2 = CC('( encList ` %s )' % W2, '( %s ` I )' % SW.D)
            assert Dc == CLN(PL(PL('P', 5), 0), S, UP(SW.D, 'I', EW2)), Dc
            r1, x1 = w.rewrite(UP(SW.D, 'I', EW2), {'( %s ` I )' % SW.D: ('( D ` I )', L_(w, pc, ph, SW.vals['I'][1])),
                                                    '( encList ` %s )' % W2: (ESL(O_), s([enc], 'eqcomd', '( %s -> ( encList ` %s ) = %s )' % (pc, W2, ESL(O_))))}, pc)
            ch = [('K', V_), ('J', 'Y'), ('I"', V2), ('I', EI)]
            assert x1 == chain_text('D', ch), x1
            gam = {k: L_(w, pc, ph, v) for k, v in com.gam.items()}
            nst, out = stk_normalize(w, pc, mkp, 'D', L_(w, pc, ph, com.dd), lambda a, b: L_(w, pc, ph, com.ne(a, b)), ch, gam, K5)
            assert chain_text('D', out) == NU
            dq = s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (pc, UP(SW.D, 'I', EW2), NU))
            tc, Cc, Dc, nc = hrrw(w, pc, tc, Cc, Dc, nc, deq=clneq(w, pc, PL(PL('P', 5), 0), S, dq, UP(SW.D, 'I', EW2), NU))
            clp = Closure(w, pc, {'N': ('NN0', L_(w, pc, ph, c['N e. NN0'])), 'B': ('NN0', L_(w, pc, ph, c['B e. NN0']))})
            clp.leaf('( # ` %s )' % W2, 'NN0', s([w2w, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, W2)))
            le = nlinarith(w, pc, [w2le, clp.ge0('B')], '%s <_ %s' % (nc, T1_LKS), closure=clp)
            tc = hrle(w, pc, mkp['phm'], tc, Cc, Dc, nc, T1_LKS, clp.mem(T1_LKS, 'NN0'), le)
            d, d1, d2 = disj_leaf('tm2flks', m)
            dj2 = s([ht_nfl(w, pc, '(/)'), tc], 'jca', '( %s -> %s )' % (pc, d2))
            ex[d] = s([dj2], 'olcd', '( %s -> %s )' % (pc, d))
        return ex

    t, cc = cases_and_generic(w, ph, com, 'tm2flks', m0, case_fn, TREE_LKS, ex0)
    C, D, n = triple_parts(cc)
    rl = s([com.pf, w.inst('revlen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ph, LR, PFX('L', JN)))
    pl = s([com.lw, com.jfz, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, PFX('L', JN), JN))
    lrj = s([rl, pl], 'eqtrd', '( %s -> %s = %s )' % (ph, LR, JN))
    n1eq, n1t = w.rewrite(n, {LR: (JN, lrj)}, ph)
    CN = '( N x. ( ( 6 x. B ) + ; 1 7 ) )'
    j3 = s([com.jnn, s([cl.mem(SLOTC, 'NN0'), cl.mem(CN, 'NN0')], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, SLOTC, CN)), c['H e. NN0']],
           '3jca', '( %s -> ( %s e. NN0 /\\ ( %s e. NN0 /\\ %s e. NN0 ) /\\ H e. NN0 ) )' % (ph, JN, SLOTC, CN))
    n2eq = s([j3, w.inst('ttlookcx')], 'syl', '( %s -> %s = %s )' % (ph, n1t, LOOKC(JN, 'H')))
    neq = s([n1eq, n2eq], 'eqtrd', '( %s -> %s = %s )' % (ph, n, LOOKC(JN, 'H')))
    hrrw(w, ph, t, C, D, n, neq=neq, qed=True)
    return w.run()

def lift_mk(w, pc, ph, mk):
    """the machine facts under pc"""
    out = {'phm': L_(w, pc, ph, mk['phm']), 'tv': L_(w, pc, ph, mk['tv']), 'seq': L_(w, pc, ph, mk['seq']), 'k': {}}
    for k, d in mk['k'].items():
        out['k'][k] = {kk: L_(w, pc, ph, v) for kk, v in d.items() if kk in ('kd', 'wge')}
    return out


def mk_phm(w, pc, ph, mk):
    return L_(w, pc, ph, mk['phm'])


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
