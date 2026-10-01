"""T7c: the Lists B forms at the concrete machine (TM/Lists.lean ` revList ` ,
` appendList ` , ` copyList ` , ` listLen ` ) on installation predicates.

  defs        append the syntax and df- of TMIlrev TMIlapp TMIlcpy TMIllen
  tmcrdbraf   the peek handler ` readBra ` (df-tmrdbra) as a function
  tmcrdbrav   its value
  tmclhi      the list interface of T6's generic forms at the concrete handlers
  tmilrevu tmilappu tmilcpyu tmillenu   the unfolding theorems
  tmilrevn tmilappn tmilcpyn   ` revList_correct ` , ` appendList_correct ` , ` copyList_correct `
  tmilrevb tmilappb tmilcpyb   ` revList_le_B ` , ` appendList_le_B ` , ` copyList_le_B `
  tmillen     ` listLen_runs ` (entries as bit words, the count below 2 ^ B)
  tmillenb    ` listLen_le_B `

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_h_lst.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *
from t7_e_cmp import lamty, cis_ty
from cl import Closure
import lin
from lin import linarith

lin.FASTPATH = True
SEL = sys.argv[1:]

S = '( 2nd ` T )'
BU = '( ( { 1 } X. 2o ) u. { 4 } )'
CNFL = CNOT('fl')
IFB = lambda o: 'if ( %s = ( inl ` 2 ) , 1o , (/) )' % o
NB = lambda z: NVF('TMrdBra', 'r', z)
NA = lambda z: NVF('TMrdA', 'r', z)
HDLS = "( ( 2nd ` T ) ^m ( ( 2nd ` T ) X. ( Gamma' |_| 1o ) ) )"
BRAV = lambda v, o: MK(*([FLD(f, v) for f in ORDER[:6]] + [IFB(o)]))

RB1 = 'A. r e. %s A. z e. %s ( %s e. %s /\\ ( %s ` %s ) = 1o )' % (S, BU, NB('z'), S, CNFL, NB('z'))
RB2 = 'A. r e. %s ( %s e. %s /\\ -. ( %s ` %s ) = 1o )' % (S, NB('2'), S, CNFL, NB('2'))
MV1 = 'A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ %s e. %s )' % (S, BITS, CIS, NA('z'), PBR, NA('z'), NA('z'), S)
MV2 = 'A. r e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (S, CIS, NA('4'), NA('4'), S)
POPI = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (S, PID, S)
DUP1 = 'A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ ( %s ` %s ) = z )' % (S, BITS, CIS, NA('z'), PBR, NA('z'), PBR, NA('z'))
DUP2 = 'A. r e. %s -. ( %s ` %s ) = 1o' % (S, CIS, NA('4'))
IFACE = ((RB1, RB2), (MV1, MV2), (POPI, (DUP1, DUP2)))
ST_LHI = '( %s -> %s )' % (SEQ, cj(IFACE))
ST_BRAF = 'TMrdBra e. %s' % HDLC
ST_BRAV = '( ( V e. TMSt /\\ O e. %s ) -> ( TMrdBra ` <. V , O >. ) = %s )' % (OPT, BRAV('V', 'O'))

# the concrete handlers for T6's generic letters
HM = {'F': 'TMrdBra', 'C': CNFL, "F'": 'TMrdA', "C'": CIS, 'P': PBR, 'F"': PID, 'N': S, "N'": S}
HMX = {'tm2lcpyb2g': {'G': 'TMrdA', "P'": PBR, 'O': PBR}, 'tm2lcpyng': {'G': 'TMrdA', "P'": PBR, 'O': PBR}}


def hm(generic):
    m = dict(HM); m.update(HMX.get(generic, {}))
    return m


def own_prog(generic):
    """the program equations and the label letters of a generic Lists statement, handlers concrete"""
    ante, _ = split_imp(stmt(generic))
    eqs, labs = [], []
    def go(t):
        if isinstance(t, str):
            if t.startswith('( M ` '):
                if t not in eqs:
                    eqs.append(t)
            elif t.endswith(' e. ( 2nd ` ( 1st ` T ) )') and len(t.split()) == 7:
                l = t.split()[0]
                if l not in labs:
                    labs.append(l)
            return
        for x in t:
            go(x)
    go(parse_conj(ante))
    eqs = [tsub_text(e, hm(generic)) for e in eqs]
    return eqs, labs


def register(name, const, generic, ks, order, children, lean):
    eqs, labs = own_prog(generic)
    byl = {e.split()[3]: e for e in eqs}
    own = [l for l in order]
    assert set(own) == set(byl), (sorted(own), sorted(byl))
    prog = grp([byl[l] for l in own])
    labt = grp([LAB(l) for l in own] + [LAB('E')])
    return comp(name, const, ks, own, 'E', prog, labt, lean, children)


K3 = ['K', 'J', 'I']
K4 = ['K', 'J', 'I', "I'"]
REVL = ['P0', 'P1', 'A', "A'", 'A"', "B'", 'B"', "Q'", "E'"]
register('lrev', 'TMIlrev', 'tm2lrevb', K3, REVL, [],
         "` revList x y s = pushSym y bra ; forEntries x ( moveEntry x y s ) ; popTop x ` "
         "(moveEntry's two moveNum inline)")
register('lapp', 'TMIlapp', 'tm2lappb', K4, REVL + ['H"', 'A0', 'C0', 'B0', 'D0', 'E0', 'F0', 'G0'], [],
         "` appendList x y z s = revList x z s ; moveEntries z y s ` (stacks ` K J I' I ` ; "
         "the parameter order ` x y s z ` )")
register('lcpy', 'TMIlcpy', 'tm2lcpyb2g', K4,
         REVL + ['H"', 'I"', 'J"', 'A0', 'C0', 'G0', 'B0', 'D0', 'E0', 'F0', 'H0', 'I0', 'J0', 'K0', 'L0'], [],
         "` copyList x y s z = revList x z s ; pushSym x bra ; pushSym y bra ; "
         "forEntries z ( moveEntry z x s ; dup x y s ) ; popTop z `")
register('llen', 'TMIllen', 'tm2llen', K4,
         ['P0', 'Q0', 'P1', 'A', "A'", 'A"', "B'", 'B"', "Q'", "E'", 'H"', 'J"', 'A0', 'C0', 'G0', 'B0', 'D0', 'E0', 'F0'],
         [('inc', ['J', 'I'], 'H0', 'C0')],
         "` listLen x y s z = pushNum y 0 ; revList x z s ; pushSym x bra ; "
         "forEntries z ( moveEntry z x s ; incr y s ) ; popTop z `")


def defs():
    import t7b_a_defs as AD
    AD.main(['lrev', 'lapp', 'lcpy', 'llen'])


def unf(name):
    import t7b_b_unf as UF
    return UF.unf(name)


# ------------------------------------------------------------ the handler readBra
def tmcrdbraf():
    lab = 'tmcrdbraf'
    w = W(lab, 'The handler ` readBra ` is a function on the states and the peeked symbols (Lean: its type '
               '` St -> Option Gamma\' -> St ` ).')
    ph = '( v e. TMSt /\\ o e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> v e. TMSt )' % ph)
    cl = st_comps(w, ph, 'v', vv)
    ifc = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFB('o'))
    comps = [FLD(f, 'v') for f in ORDER[:6]] + [IFB('o')]
    cls = [cl[f] for f in ORDER[:6]] + [w.s([ifc], 'a1i', '( %s -> %s e. 2o )' % (ph, IFB('o')))]
    mem, _ = tuple_facts(w, ph, comps, cls)
    B = BRAV('v', 'o')
    ral = w.s([mem], 'rgen2', 'A. v e. TMSt A. o e. %s %s e. TMSt' % (OPT, B))
    d = w.s([], 'df-tmrdbra', 'TMrdBra = ( v e. TMSt , o e. %s |-> %s )' % (OPT, B))
    fm = w.s([d], 'fmpo', '( A. v e. TMSt A. o e. %s %s e. TMSt <-> TMrdBra : ( TMSt X. %s ) --> TMSt )' % (OPT, B, OPT))
    ff = w.s([ral, fm], 'mpbi', 'TMrdBra : ( TMSt X. %s ) --> TMSt' % OPT)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ov = w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.s([], '1oex', '1o e. _V'), w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xv = w.s([sv, ov, w.inst('xpexg')], 'mp2an', '( TMSt X. %s ) e. _V' % OPT)
    em = w.s([sv, xv, w.inst('elmapg')], 'mp2an', '( TMrdBra e. %s <-> TMrdBra : ( TMSt X. %s ) --> TMSt )' % (HDLC, OPT))
    w.qed([ff, em], 'mpbir', ST_BRAF)
    return w.run()


def tmcrdbrav():
    lab = 'tmcrdbrav'
    w = W(lab, 'Value of ` readBra ` : the flag records whether the peeked symbol is ` some bra ` '
               '(Lean ` readBra ` , ` flag := decide ( o = some Gamma\'.bra ) ` ).')
    ph = '( V e. TMSt /\\ O e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    oo = w.s([], 'simpr', '( %s -> O e. %s )' % (ph, OPT))
    B = BRAV('v', 'o'); BV = BRAV('V', 'O')
    ante = '( v = V /\\ o = O )'
    ev = w.s([], 'simpl', '( %s -> v = V )' % ante)
    eo = w.s([], 'simpr', '( %s -> o = O )' % ante)
    cg, nb = w.congr(B, {'v': 'V', 'o': 'O'}, ante, {'v': ev, 'o': eo})
    assert nb == BV, nb
    d = w.s([], 'df-tmrdbra', 'TMrdBra = ( v e. TMSt , o e. %s |-> %s )' % (OPT, B))
    bx = w.s([], 'opex', '%s e. _V' % BV)
    bxa = w.s([bx], 'a1i', '( %s -> %s e. _V )' % (ph, BV))
    j = w.s([vv, oo, bxa], '3jca', '( %s -> ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) )' % (ph, OPT, BV))
    ovi = w.s([cg, d], 'ovmpoga', '( ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) -> ( V TMrdBra O ) = %s )' % (OPT, BV, BV))
    ov = w.s([j, ovi], 'syl', '( %s -> ( V TMrdBra O ) = %s )' % (ph, BV))
    dov = w.s([], 'df-ov', '( V TMrdBra O ) = ( TMrdBra ` <. V , O >. )')
    dova = w.s([dov], 'a1i', '( %s -> ( V TMrdBra O ) = ( TMrdBra ` <. V , O >. ) )' % ph)
    w.qed([dova, ov], 'eqtr3d', ST_BRAV)
    return w.run()


# ------------------------------------------------------------ the interface
def bra_val(w, a, r, rr, O, oo):
    """the value of readBra at ( r , O ): dict val/mem/fields"""
    N = '( TMrdBra ` <. %s , %s >. )' % (r, O)
    comps = [FLD(f, r) for f in ORDER[:6]] + [IFB(O)]
    val = w.s([rr, oo, w.inst('tmcrdbrav')], 'syl2anc', '( %s -> %s = %s )' % (a, N, MK(*comps)))
    cl = st_comps(w, a, r, rr)
    ifc = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFB(O))
    cls = [cl[f] for f in ORDER[:6]] + [w.s([ifc], 'a1i', '( %s -> %s e. 2o )' % (a, IFB(O)))]
    mem, vals = tuple_facts(w, a, comps, cls)
    import t7lib
    return t7lib._transport(w, a, N, val, mem, vals, comps)


def cnfl_val(w, a, nv, N, flv, flstep):
    """( a -> ( CNFL ` N ) = 1o / (/) ) from flstep : ( a -> ( TMfl ` N ) = flv ) (flv (/) or 1o)"""
    X_of = lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    xex = ifex_closed(w, a, '( TMfl ` %s ) = 1o' % N, '(/)', '1o', z0, o1)
    v = lamval(w, a, X_of, N, nv['mem'], xex)
    if flv == '1o':
        it = w.s([flstep], 'iftrued', '( %s -> %s = (/) )' % (a, X_of(N)))
        return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = (/) )' % (a, CNFL, N))
    n0 = w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
    e = w.s([flstep], 'eqeq1d', '( %s -> ( ( TMfl ` %s ) = 1o <-> (/) = 1o ) )' % (a, N))
    nn = w.s([e, w.s([n0], 'a1i', '( %s -> -. (/) = 1o )' % a)], 'mtbird', '( %s -> -. ( TMfl ` %s ) = 1o )' % (a, N))
    it = w.s([nn], 'iffalsed', '( %s -> %s = 1o )' % (a, X_of(N)))
    return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = 1o )' % (a, CNFL, N))


def tmclhi():
    lab = 'tmclhi'
    ph = SEQ
    w = W(lab, 'The list interface of T6\'s generic ` revList ` , ` appendList ` , ` copyList ` , ` listLen ` '
               'at the concrete handlers over all states: ` readBra ` then ` !flag ` goes on at a bit or the '
               'terminator and stops at ` bra ` , the movers ` readA ` , ` ra.isSome ` , ` bit ( bitOf ra ) ` '
               '(~ tmcmvi ), the pop ` fun v _ => v ` .')
    # --- readBra on a bit or the terminator
    a1 = '( %s /\\ r e. %s )' % (ph, S)
    a2 = '( %s /\\ z e. %s )' % (a1, BU)
    r2 = w.s([w.s([], 'simplr', '( %s -> r e. %s )' % (a2, S)), w.s([], 'simpll', '( %s -> %s )' % (a2, SEQ))], 'eleqtrd',
             '( %s -> r e. TMSt )' % a2)
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (a2, BU))
    bug = w.s([w.s([], 'tm2lbits', "%s C_ Gamma'" % BITS), w.s([w.s([], 'gamma4', "4 e. Gamma'"), w.inst('snssi')], 'ax-mp', "{ 4 } C_ Gamma'")],
              'unssi', "%s C_ Gamma'" % BU)
    zg = w.s([w.s([bug], 'a1i', "( %s -> %s C_ Gamma' )" % (a2, BU)), zz], 'sseldd', "( %s -> z e. Gamma' )" % a2)
    oz = w.s([zg, w.inst('djulcl')], 'syl', '( %s -> ( inl ` z ) e. %s )' % (a2, OPT))
    nv = bra_val(w, a2, 'r', r2, '( inl ` z )', oz)
    N = NB('z')
    # -. 2 e. BU
    n2b = w.s([w.s([], '2re', '2 e. RR'), w.inst('tmcnbits')], 'ax-mp', '-. 2 e. %s' % BITS)
    n24 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '2lt4', '2 < 4')], 'ltneii', '2 =/= 4')], 'neii', '-. 2 = 4')
    e24 = w.s([w.s([], '2ex', '2 e. _V'), w.inst('elsng')], 'ax-mp', '( 2 e. { 4 } <-> 2 = 4 )')
    n2s = w.s([n24, e24], 'mtbir', '-. 2 e. { 4 }')
    nor = w.s([n2b, n2s], 'pm3.2i', '( -. 2 e. %s /\\ -. 2 e. { 4 } )' % BITS)
    io = w.s([], 'ioran', '( -. ( 2 e. %s \\/ 2 e. { 4 } ) <-> ( -. 2 e. %s /\\ -. 2 e. { 4 } ) )' % (BITS, BITS))
    nor2 = w.s([nor, io], 'mpbir', '-. ( 2 e. %s \\/ 2 e. { 4 } )' % BITS)
    eu = w.s([], 'elun', '( 2 e. %s <-> ( 2 e. %s \\/ 2 e. { 4 } ) )' % (BU, BITS))
    n2u = w.s([nor2, eu], 'mtbir', '-. 2 e. %s' % BU)
    zne = w.s([zz, w.s([n2u], 'a1i', '( %s -> -. 2 e. %s )' % (a2, BU)), w.inst('nelne2')], 'syl2anc', '( %s -> z =/= 2 )' % a2)
    zn2 = w.s([zne], 'neneqd', '( %s -> -. z = 2 )' % a2)
    i11 = w.s([w.s([zg], 'elexd', '( %s -> z e. _V )' % a2), closed(w, a2, '2ex', '2 e. _V'), w.inst('tmcinl11')], 'syl2anc',
              '( %s -> ( ( inl ` z ) = ( inl ` 2 ) <-> z = 2 ) )' % a2)
    nin = w.s([i11, zn2], 'mtbird', '( %s -> -. ( inl ` z ) = ( inl ` 2 ) )' % a2)
    ifz = w.s([nin], 'iffalsed', '( %s -> %s = (/) )' % (a2, IFB('( inl ` z )')))
    fl0 = w.s([nv['fields']['fl'], ifz], 'eqtrd', '( %s -> ( TMfl ` %s ) = (/) )' % (a2, N))
    cv = cnfl_val(w, a2, nv, N, '(/)', fl0)
    sq2 = w.s([w.s([], 'simpll', '( %s -> %s )' % (a2, SEQ))], 'eqcomd', '( %s -> TMSt = %s )' % (a2, S))
    ms = w.s([nv['mem'], sq2], 'eleqtrd', '( %s -> %s e. %s )' % (a2, N, S))
    b1 = w.s([ms, cv], 'jca', '( %s -> ( %s e. %s /\\ ( %s ` %s ) = 1o ) )' % (a2, N, S, CNFL, N))
    b1r = w.s([b1], 'ralrimiva', '( %s -> A. z e. %s ( %s e. %s /\\ ( %s ` %s ) = 1o ) )' % (a1, BU, N, S, CNFL, N))
    rb1 = w.s([b1r], 'ralrimiva', '( %s -> %s )' % (ph, RB1))
    # --- readBra on bra
    rr1 = w.s([w.s([], 'simpr', '( %s -> r e. %s )' % (a1, S)), w.s([], 'simpl', '( %s -> %s )' % (a1, SEQ))], 'eleqtrd',
              '( %s -> r e. TMSt )' % a1)
    g2 = closed(w, a1, 'gamma2', "2 e. Gamma'")
    o2 = w.s([g2, w.inst('djulcl')], 'syl', '( %s -> ( inl ` 2 ) e. %s )' % (a1, OPT))
    nv2 = bra_val(w, a1, 'r', rr1, '( inl ` 2 )', o2)
    N2 = NB('2')
    if2 = w.s([w.s([], 'eqidd', '( %s -> ( inl ` 2 ) = ( inl ` 2 ) )' % a1)], 'iftrued', '( %s -> %s = 1o )' % (a1, IFB('( inl ` 2 )')))
    fl1 = w.s([nv2['fields']['fl'], if2], 'eqtrd', '( %s -> ( TMfl ` %s ) = 1o )' % (a1, N2))
    cv2 = cnfl_val(w, a1, nv2, N2, '1o', fl1)
    ncv2 = not1o(w, a1, cv2, CNFL, N2)
    sq1 = w.s([w.s([], 'simpl', '( %s -> %s )' % (a1, SEQ))], 'eqcomd', '( %s -> TMSt = %s )' % (a1, S))
    ms2 = w.s([nv2['mem'], sq1], 'eleqtrd', '( %s -> %s e. %s )' % (a1, N2, S))
    b2 = w.s([ms2, ncv2], 'jca', '( %s -> ( %s e. %s /\\ -. ( %s ` %s ) = 1o ) )' % (a1, N2, S, CNFL, N2))
    rb2 = w.s([b2], 'ralrimiva', '( %s -> %s )' % (ph, RB2))
    rbs = w.s([rb1, rb2], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, RB1, RB2))
    # --- the movers on a bit
    a3 = '( %s /\\ z e. %s )' % (a1, BITS)
    r3 = w.s([w.s([], 'simplr', '( %s -> r e. %s )' % (a3, S)), w.s([], 'simpll', '( %s -> %s )' % (a3, SEQ))], 'eleqtrd',
             '( %s -> r e. TMSt )' % a3)
    z3 = w.s([], 'simpr', '( %s -> z e. %s )' % (a3, BITS))
    nva = rd_bit(w, a3, 'A', 'r', 'z', r3, z3)
    NAz = NA('z')
    ci, civ = cis_val(w, a3, nva, NAz)
    assert civ == '1o'
    pb = pbr_val(w, a3, nva, NAz, 'z', z3)
    sq3 = w.s([w.s([], 'simpll', '( %s -> %s )' % (a3, SEQ))], 'eqcomd', '( %s -> TMSt = %s )' % (a3, S))
    ma = w.s([nva['mem'], sq3], 'eleqtrd', '( %s -> %s e. %s )' % (a3, NAz, S))
    m1 = w.s([ci, pb, ma], '3jca', '( %s -> ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ %s e. %s ) )' % (a3, CIS, NAz, PBR, NAz, NAz, S))
    m1r = w.s([m1], 'ralrimiva', '( %s -> A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ %s e. %s ) )'
              % (a1, BITS, CIS, NAz, PBR, NAz, NAz, S))
    mv1 = w.s([m1r], 'ralrimiva', '( %s -> %s )' % (ph, MV1))
    d1 = w.s([ci, pb, pb], '3jca', '( %s -> ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ ( %s ` %s ) = z ) )' % (a3, CIS, NAz, PBR, NAz, PBR, NAz))
    d1r = w.s([d1], 'ralrimiva', '( %s -> A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ ( %s ` %s ) = z ) )'
              % (a1, BITS, CIS, NAz, PBR, NAz, PBR, NAz))
    dup1 = w.s([d1r], 'ralrimiva', '( %s -> %s )' % (ph, DUP1))
    # --- the movers on the terminator
    nv4 = rd_comma(w, a1, 'A', 'r', rr1)
    NA4 = NA('4')
    c4, c4v = cis_val(w, a1, nv4, NA4)
    assert c4v == '(/)'
    nc4 = not1o(w, a1, c4, CIS, NA4)
    m4 = w.s([nv4['mem'], sq1], 'eleqtrd', '( %s -> %s e. %s )' % (a1, NA4, S))
    mv2b = w.s([nc4, m4], 'jca', '( %s -> ( -. ( %s ` %s ) = 1o /\\ %s e. %s ) )' % (a1, CIS, NA4, NA4, S))
    mv2 = w.s([mv2b], 'ralrimiva', '( %s -> %s )' % (ph, MV2))
    dup2 = w.s([nc4], 'ralrimiva', '( %s -> %s )' % (ph, DUP2))
    mvs = w.s([mv1, mv2], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, MV1, MV2))
    # --- the pop fun v _ => v
    OP2 = '<. r , ( inl ` 2 ) >.'
    ox = w.s([rr1, o2], 'opelxpd', '( %s -> %s e. ( TMSt X. %s ) )' % (a1, OP2, OPT))
    fr = w.s([ox, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( 1st ` %s ) )' % (a1, PID, OP2, OP2))
    f1 = w.s([rr1, o2, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = r )' % (a1, OP2))
    pv = w.s([fr, f1], 'eqtrd', '( %s -> ( %s ` %s ) = r )' % (a1, PID, OP2))
    pm = w.s([pv, w.s([], 'simpr', '( %s -> r e. %s )' % (a1, S))], 'eqeltrd', '( %s -> ( %s ` %s ) e. %s )' % (a1, PID, OP2, S))
    popi = w.s([pm], 'ralrimiva', '( %s -> %s )' % (ph, POPI))
    dups = w.s([dup1, dup2], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, DUP1, DUP2))
    pd = w.s([popi, dups], 'jca', '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (ph, POPI, DUP1, DUP2))
    w.qed([rbs, mvs, pd], '3jca', ST_LHI)
    return w.run()


# ------------------------------------------------------------ the installed forms
DATA_R = ((STKD('D'), '( D ` K ) = ( ( encList ` L ) ++ R )'), ('L e. Word NN0', WRD('R', GAM)),
          ('B e. NN0', 'A. a e. ran L a < ( 2 ^ B )'))
DATA_A = ((STKD('D'), ('( D ` K ) = ( ( encList ` L ) ++ R )', "( D ` J ) = ( ( encList ` U ) ++ R' )")),
          (('L e. Word NN0', 'U e. Word NN0'), (WRD('R', GAM), WRD("R'", GAM))),
          ('B e. NN0', 'A. a e. ran L a < ( 2 ^ B )'))
DATA_LB = ((STKD('D'), '( D ` K ) = ( ( encListB ` L ) ++ R )'), ('L e. Word Word ( { 1 } X. 2o )', WRD('R', GAM)),
           ('B e. NN0', 'A. w e. ran L ( # ` w ) <_ B', '( # ` L ) < ( 2 ^ B )'))
DATA_LN = ((STKD('D'), '( D ` K ) = ( ( encList ` L ) ++ R )'), ('L e. Word NN0', WRD('R', GAM)),
           ('B e. NN0', 'A. a e. ran L a < ( 2 ^ B )', '( # ` L ) < ( 2 ^ B )'))


def TREE(fname, ks, data):
    return ((T_PHM7, FRAGS[fname].pred()), (idx_tree(ks), dist_tree(ks)), data)


BLB = '( ( ( # ` L ) + 1 ) x. ( TMB ` B ) )'
QFAM = '( j e. ( 0 ... ( # ` L ) ) |-> ( ( encNatGam ` j ) ++ <" 4 "> ) )'
YINC = '( ( 2 x. B ) + 3 )'
BLEN = '( ( ( # ` L ) x. ( ( ( 4 x. B ) + %s ) + ; 1 2 ) ) + 9 )' % YINC
EWL = EW('( # ` L )', '( D ` J )')
CONCL = {
    'tmilrevb': TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP(UP('D', 'K', 'R'), 'J', '( ( encList ` ( reverse ` L ) ) ++ ( D ` J ) )')), BLB),
    'tmilappb': TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP(UP('D', 'K', 'R'), 'J', "( ( encList ` ( L ++ U ) ) ++ R' )")), BLB),
    'tmilcpyb': TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP('D', 'J', '( ( encList ` L ) ++ ( D ` J ) )')), BLB),
    'tmillen': TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP('D', 'J', EWL)), BLEN),
    'tmillenb': TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP('D', 'J', EWL)), BLB),
}
BREV = '( ( ( # ` L ) x. ( ( 2 x. B ) + 6 ) ) + 4 )'
BAPP = '( ( ( # ` L ) x. ( ( 4 x. B ) + ; 1 2 ) ) + 7 )'
BCPY = '( ( ( # ` L ) x. ( ( 6 x. B ) + ; 1 7 ) ) + 9 )'
for lb, bn in (('rev', BREV), ('app', BAPP), ('cpy', BCPY)):
    CONCL['tmil%sn' % lb] = CONCL['tmil%sb' % lb].replace(', %s >.' % BLB, ', %s >.' % bn)
    assert CONCL['tmil%sn' % lb] != CONCL['tmil%sb' % lb]
TREES = {'tmilrevn': TREE('lrev', K3, DATA_R), 'tmilappn': TREE('lapp', K4, DATA_A), 'tmilcpyn': TREE('lcpy', K4, DATA_R),
         'tmilrevb': TREE('lrev', K3, DATA_R), 'tmilappb': TREE('lapp', K4, DATA_A), 'tmilcpyb': TREE('lcpy', K4, DATA_R),
         'tmillen': TREE('llen', K4, DATA_LB), 'tmillenb': TREE('llen', K4, DATA_LN)}
STMTS = {l: '( %s -> %s )' % (cj(TREES[l]), CONCL[l]) for l in CONCL}
STMTS.update({'tmcrdbraf': ST_BRAF, 'tmcrdbrav': ST_BRAV, 'tmclhi': ST_LHI})


def handler_extra(w, ps, mk, iface):
    """the handler typings at the generic alphabet and the interface leaves"""
    seqr = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = %s )' % (ps, S))
    x1 = w.s([seqr], 'xpeq1d', "( %s -> ( TMSt X. ( Gamma' |_| 1o ) ) = ( %s X. ( Gamma' |_| 1o ) ) )" % (ps, S))
    e3 = w.s([seqr, x1], 'oveq12d', '( %s -> %s = %s )' % (ps, HDLC, HDLS))
    def ty(name, lem):
        return w.s([closed(w, ps, lem, '%s e. %s' % (name, HDLC)), e3], 'eleqtrd', '( %s -> %s e. %s )' % (ps, name, HDLS))
    X_of = lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t
    bcl = w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    cnty = lamty(w, ps, mk, CNFL, X_of, '2o', w.s([], '2oex', '2o e. _V'), bcl)
    PX = lambda t: '<. 1 , ( bitOf ` ( TMra ` %s ) ) >.' % t
    b1 = w.s([], 'tmcracl', '( u e. TMSt -> ( TMra ` u ) e. ( 2o |_| 1o ) )')
    b2 = w.s([b1, w.inst('bitofcl')], 'syl', '( u e. TMSt -> ( bitOf ` ( TMra ` u ) ) e. 2o )')
    b3 = w.s([b2, w.inst('bitgamma')], 'syl', "( u e. TMSt -> %s e. Gamma' )" % PX('u'))
    pbty = lamty(w, ps, mk, PBR, PX, GAM, w.s([], 'gammaex', "Gamma' e. _V"), b3)
    ex = {'TMrdBra e. %s' % HDLS: ty('TMrdBra', 'tmcrdbraf'), 'TMrdA e. %s' % HDLS: ty('TMrdA', 'tmcrdaf'),
          '%s e. %s' % (PID, HDLS): ty(PID, 'tmcpidf'),
          '%s e. ( 2o ^m %s )' % (CNFL, S): cnty, '%s e. ( 2o ^m %s )' % (CIS, S): cis_ty(w, ps, mk),
          "%s e. ( Gamma' ^m %s )" % (PBR, S): pbty,
          '%s C_ %s' % (S, S): closed(w, ps, 'ssid', '%s C_ %s' % (S, S))}
    hi = w.s([mk['seq'], w.inst('tmclhi')], 'syl', '( %s -> %s )' % (ps, cj(IFACE)))
    def walk(t, st):
        if isinstance(t, str):
            ex[t] = st; return
        ex[cj(t)] = st
        if len(t) == 2:
            walk(t[0], w.s([st], 'simpld', '( %s -> %s )' % (ps, cj(t[0]))))
            walk(t[1], w.s([st], 'simprd', '( %s -> %s )' % (ps, cj(t[1]))))
        else:
            for i, x in enumerate(t):
                walk(x, w.s([st, w.inst('simp%d' % (i + 1))], 'syl', '( %s -> %s )' % (ps, cj(x))))
    walk(IFACE, hi)
    return ex


def lab_map(fname):
    m = FRAGS[fname].lmap()
    return m


def installed(lab, fname, generic, ks, desc, m_more=None):
    T = TREES[lab]
    ps = cj(T)
    w = W(lab, desc)
    c, mk, ne, base = setup(w, ps, T, ks, pred=FRAGS[fname].pred(), fname=fname)
    ex = dict(base)
    ex.update(handler_extra(w, ps, mk, IFACE))
    m = hm(generic); m.update(lab_map(fname))
    if m_more:
        m.update(m_more(w, ps, c, mk, ex))
    t, cc = inst(w, ps, generic, m, Bld(w, ps, c, ex))
    return w, ps, c, mk, ex, t, cc


def simple_b(lab, fname, generic, ks, desc):
    w, ps, c, mk, ex, t, cc = installed(lab, fname, generic, ks, desc)
    assert cc == CONCL[lab], '\nGOT  %s\nWANT %s' % (cc, CONCL[lab])
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


def tmilrevb():
    return simple_b('tmilrevb', 'lrev', 'tm2lrevb', K3,
                    'Lean\'s ` revList_le_B ` at the machine: wherever ` revList x y s ` is installed, from any state '
                    'with the list ` ( encList ` L ) ` of numbers below ` 2 ^ B ` on ` x ` it leaves the rest on ` x ` '
                    'and pushes the reversed list on ` y ` (~ tm2lrevb at the concrete handlers, ~ tmclhi ).')


def tmilappb():
    return simple_b('tmilappb', 'lapp', 'tm2lappb', K4,
                    'Lean\'s ` appendList_le_B ` at the machine: ` appendList x y z s ` ( ` x y z s = K J I\' I ` ) '
                    'puts the list of ` x ` in front of the list of ` y ` (~ tm2lappb at the concrete handlers, ~ tmclhi ).')


def tmilcpyb():
    return simple_b('tmilcpyb', 'lcpy', 'tm2lcpyb2g', K4,
                    'Lean\'s ` copyList_le_B ` at the machine: ` copyList x y s z ` pushes a copy of the list of '
                    '` x ` on ` y ` and restores every other stack (~ tm2lcpyb2g at the concrete handlers, ~ tmclhi ).')


def tmilrevn():
    return simple_b('tmilrevn', 'lrev', 'tm2lrevn', K3,
                    'Lean\'s ` revList_correct ` at the machine: ~ tmilrevb with Lean\'s exact bound '
                    '(~ tm2lrevn at the concrete handlers, ~ tmclhi ).')


def tmilappn():
    return simple_b('tmilappn', 'lapp', 'tm2lappn', K4,
                    'Lean\'s ` appendList_correct ` at the machine: ~ tmilappb with Lean\'s exact bound '
                    '(~ tm2lappn at the concrete handlers, ~ tmclhi ).')


def tmilcpyn():
    return simple_b('tmilcpyn', 'lcpy', 'tm2lcpyng', K4,
                    'Lean\'s ` copyList_correct ` at the machine: ~ tmilcpyb with Lean\'s exact bound '
                    '(~ tm2lcpyng at the concrete handlers, ~ tmclhi ).')


# ------------------------------------------------------------ listLen
def QV(t):
    return '( %s ` %s )' % (QFAM, t)


def qval(w, a, t, tfz, tn):
    """( a -> ( QFAM ` t ) = ( ( encNatGam ` t ) ++ <" 4 "> ) ) ; tfz : t e. ( 0 ... ( # ` L ) ), tn : t e. NN0"""
    X_of = lambda s: '( ( encNatGam ` %s ) ++ <" 4 "> )' % s
    idj = w.s([], 'id', '( j = %s -> j = %s )' % (t, t))
    cg, new = w.congr(X_of('j'), {'j': t}, 'j = %s' % t, {'j': idj})
    assert new == X_of(t), new
    g4 = closed(w, a, 'gamma4', "4 e. Gamma'")
    s4 = w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % a)
    ec = w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` %s ) e. Word Gamma' )" % (a, t))
    xc = w.s([ec, s4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (a, X_of(t)))
    xv = w.s([xc], 'elexd', '( %s -> %s e. _V )' % (a, X_of(t)))
    fe = w.s([], 'eqid', '%s = %s' % (QFAM, QFAM))
    g = w.s([cg, fe], 'fvmptg', '( ( %s e. ( 0 ... ( # ` L ) ) /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (t, X_of(t), QFAM, t, X_of(t)))
    return w.s([tfz, xv, g], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (a, QFAM, t, X_of(t))), ec, s4


def len_more(w, ps, c, mk, ex):
    """the counter family Q, its typing and start, the budget Y and the discharged incr hypothesis"""
    FL = FRAGS['llen']
    lm = FL.lmap()
    PLn = PL('P', FL.slot(0))
    C0m = lm['C0']
    ll = c['L e. Word Word ( { 1 } X. 2o )']
    bb = c['B e. NN0']
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ps)
    # Q : ( 0 ... # L ) --> Word Gamma'
    aj = '( %s /\\ j e. ( 0 ... ( # ` L ) ) )' % ps
    jn = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... ( # ` L ) ) )' % aj), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % aj)
    ecj = w.s([jn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` j ) e. Word Gamma' )" % aj)
    s4j = w.s([closed(w, aj, 'gamma4', "4 e. Gamma'")], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % aj)
    bj = w.s([ecj, s4j, w.inst('ccatcl')], 'syl2anc', "( %s -> ( ( encNatGam ` j ) ++ <\" 4 \"> ) e. Word Gamma' )" % aj)
    qf = w.s([bj, w.s([], 'eqid', '%s = %s' % (QFAM, QFAM))], 'fmptd', "( %s -> %s : ( 0 ... ( # ` L ) ) --> Word Gamma' )" % (ps, QFAM))
    # ( Q ` 0 ) = <" 4 ">
    z0 = w.s([nl, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... ( # ` L ) ) )' % ps)
    q0, ec0, s40 = qval(w, ps, '0', z0, closed(w, ps, '0nn0', '0 e. NN0'))
    e0 = w.s([closed(w, ps, '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ps)
    e0b = w.s([closed(w, ps, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ps)
    e0c = closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')
    e0d = w.s([w.s([e0, e0b], 'eqtrd', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. (/) ) )' % ps), e0c], 'eqtrd', '( %s -> ( encNatGam ` 0 ) = (/) )' % ps)
    e0e = w.s([e0d], 'oveq1d', '( %s -> ( ( encNatGam ` 0 ) ++ <" 4 "> ) = ( (/) ++ <" 4 "> ) )' % ps)
    e0f = w.s([s40, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ <" 4 "> ) = <" 4 "> )' % ps)
    q0v = w.s([q0, w.s([e0e, e0f], 'eqtrd', '( %s -> ( ( encNatGam ` 0 ) ++ <" 4 "> ) = <" 4 "> )' % ps)], 'eqtrd',
              '( %s -> ( %s ` 0 ) = <" 4 "> )' % (ps, QFAM))
    # Y e. NN0
    cl = Closure(w, ps, {'B': ('NN0', bb)})
    yn = cl.mem(YINC, 'NN0')
    # the incr hypothesis
    KL = 'k e. ( 0 ..^ ( # ` L ) )'
    a1 = '( %s /\\ %s )' % (ps, KL)
    a2 = '( %s /\\ d e. ( TM2Stk ` T ) )' % a1
    HJ = '( d ` J ) = ( %s ++ ( D ` J ) )' % QV('k')
    a3 = '( %s /\\ %s )' % (a2, HJ)
    lift = lambda st, f: w.s([st], 'ad3antrrr', '( %s -> %s )' % (a3, f))
    kin = w.s([], 'simpllr', '( %s -> %s )' % (a3, KL))
    dd = w.s([], 'simplr', '( %s -> d e. ( TM2Stk ` T ) )' % a3)
    hj = w.s([], 'simpr', '( %s -> %s )' % (a3, HJ))
    kn = w.s([kin, w.inst('elfzonn0')], 'syl', '( %s -> k e. NN0 )' % a3)
    kfz = w.s([kin, w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... ( # ` L ) ) )' % a3)
    k1fz = w.s([kin, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. ( 0 ... ( # ` L ) ) )' % a3)
    k1n = w.s([k1fz, w.inst('elfznn0')], 'syl', '( %s -> ( k + 1 ) e. NN0 )' % a3)
    qk, eck, s4k = qval(w, a3, 'k', kfz, kn)
    tv3 = lift(mk['tv'], 'T e. V')
    dk = lift(ex[STKD('D')] if STKD('D') in ex else c[STKD('D')], STKD('D'))
    jd = lift(mk['k']['J']['kd'], 'J e. %s' % DG)
    djg = w.s([stkfv(w, a3, 'D', 'J', tv3, dk, jd), lift(mk['k']['J']['wge'], "Word %s = Word Gamma'" % GX('J'))], 'eleqtrd',
              "( %s -> ( D ` J ) e. Word Gamma' )" % a3)
    ENCK = '( encodeNat ` k )'
    v1 = w.s([qk], 'oveq1d', '( %s -> ( %s ++ ( D ` J ) ) = ( ( ( encNatGam ` k ) ++ <" 4 "> ) ++ ( D ` J ) ) )' % (a3, QV('k')))
    v2 = w.s([eck, s4k, djg, w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( ( encNatGam ` k ) ++ <" 4 "> ) ++ ( D ` J ) ) = ( ( encNatGam ` k ) ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % a3)
    v3 = w.s([w.s([kn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` k ) = ( inclBool o. %s ) )' % (a3, ENCK))], 'oveq1d',
             '( %s -> ( ( encNatGam ` k ) ++ ( <" 4 "> ++ ( D ` J ) ) ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (a3, ENCK))
    DJK = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ ( D ` J ) ) )' % ENCK
    e12 = w.s([v1, v2], 'eqtrd', '( %s -> ( %s ++ ( D ` J ) ) = ( ( encNatGam ` k ) ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (a3, QV('k')))
    e123 = w.s([e12, v3], 'eqtrd', '( %s -> ( %s ++ ( D ` J ) ) = %s )' % (a3, QV('k'), DJK))
    hj3 = w.s([hj, e123], 'eqtrd', '( %s -> ( d ` J ) = %s )' % (a3, DJK))
    # tmiincs at K := J , J := I
    un = unfold_all(w, ps, c[FL.pred()], 'llen', K4, 'P', 'E', rec=False)
    INCP = 'TMIinc J I T M %s %s' % (PLn, C0m)
    ui = unfold_all(w, ps, un[INCP], 'inc', ['J', 'I'], PLn, C0m, rec=False)
    H0T = '( %s ` 0 ) e. ( 2nd ` ( 1st ` T ) )' % PLn
    ex[H0T] = ui[H0T]
    ekw = w.s([kn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (a3, ENCK))
    ext = {INCP: lift(un[INCP], INCP), PHM: lift(mk['phm'], PHM), GEQ: lift(mk['geq'], GEQ), SEQ: lift(mk['seq'], SEQ),
           'J e. ( 0 ..^ 8 )': lift(c['J e. ( 0 ..^ 8 )'], 'J e. ( 0 ..^ 8 )'),
           'I e. ( 0 ..^ 8 )': lift(c['I e. ( 0 ..^ 8 )'], 'I e. ( 0 ..^ 8 )'),
           'J =/= I': lift(c['J =/= I'], 'J =/= I'),
           '%s e. Word 2o' % ENCK: ekw, "( D ` J ) e. Word Gamma'": djg, 'd e. ( TM2Stk ` T )': dd,
           '( d ` J ) = %s' % DJK: hj3}
    ext['T e. V'] = tv3
    ext[MTY] = lift(mk['mt'], MTY)
    c3 = Ctx(w, a3, (((TREES['tmillen'], KL), 'd e. ( TM2Stk ` T )'), HJ))
    tinc, cinc = inst(w, a3, 'tmiincs', {'K': 'J', 'J': 'I', 'P': PLn, 'E': C0m, 'L': ENCK, 'X': '( D ` J )', 'D': 'd'},
                      Bld(w, a3, c3, ext))
    Ci, Di, ni = triple_parts(cinc)
    V1 = '( ( inclBool o. ( incBits ` %s ) ) ++ ( <" 4 "> ++ ( D ` J ) ) )' % ENCK
    V2 = '( %s ++ ( D ` J ) )' % QV('( k + 1 )')
    E1 = '( encodeNat ` ( k + 1 ) )'
    f1 = w.s([w.s([kn, w.inst('encnatsuc')], 'syl', '( %s -> %s = ( incBits ` %s ) )' % (a3, E1, ENCK))], 'eqcomd',
             '( %s -> ( incBits ` %s ) = %s )' % (a3, ENCK, E1))
    f2 = w.s([f1], 'coeq2d', '( %s -> ( inclBool o. ( incBits ` %s ) ) = ( inclBool o. %s ) )' % (a3, ENCK, E1))
    f3 = w.s([w.s([k1n, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` ( k + 1 ) ) = ( inclBool o. %s ) )' % (a3, E1))], 'eqcomd',
             '( %s -> ( inclBool o. %s ) = ( encNatGam ` ( k + 1 ) ) )' % (a3, E1))
    f23 = w.s([f2, f3], 'eqtrd', '( %s -> ( inclBool o. ( incBits ` %s ) ) = ( encNatGam ` ( k + 1 ) ) )' % (a3, ENCK))
    g1 = w.s([f23], 'oveq1d', '( %s -> %s = ( ( encNatGam ` ( k + 1 ) ) ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (a3, V1))
    qk1, eck1, s4k1 = qval(w, a3, '( k + 1 )', k1fz, k1n)
    g2 = w.s([eck1, s4k1, djg, w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( ( encNatGam ` ( k + 1 ) ) ++ <" 4 "> ) ++ ( D ` J ) ) = ( ( encNatGam ` ( k + 1 ) ) ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % a3)
    g3 = w.s([qk1], 'oveq1d', '( %s -> %s = ( ( ( encNatGam ` ( k + 1 ) ) ++ <" 4 "> ) ++ ( D ` J ) ) )' % (a3, V2))
    g23 = w.s([g3, g2], 'eqtrd', '( %s -> %s = ( ( encNatGam ` ( k + 1 ) ) ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (a3, V2))
    vv = w.s([g1, g23], 'eqtr4d', '( %s -> %s = %s )' % (a3, V1, V2))
    Di2 = CLN(C0m, S, UP('d', 'J', V2))
    ue = upeq(w, a3, 'd', 'J', vv, V1, V2)
    deq = clneq(w, a3, C0m, S, ue, UP('d', 'J', V1), UP('d', 'J', V2))
    t2, Ci2, Dn, n2 = hrrw(w, a3, tinc, Ci, Di, ni, deq=deq)
    assert Dn == Di2, (Dn, Di2)
    # the budget
    NK = '( # ` %s )' % ENCK
    bb3 = lift(bb, 'B e. NN0')
    nl3 = lift(nl, '( # ` L ) e. NN0')
    kl = w.s([kin, w.inst('elfzolt2')], 'syl', '( %s -> k < ( # ` L ) )' % a3)
    ltp = lift(c['( # ` L ) < ( 2 ^ B )'], '( # ` L ) < ( 2 ^ B )')
    p2 = w.s([closed(w, a3, '2nn0', '2 e. NN0'), bb3, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ B ) e. NN0 )' % a3)
    kp = w.s([w.s([kn], 'nn0red', '( %s -> k e. RR )' % a3), w.s([nl3], 'nn0red', '( %s -> ( # ` L ) e. RR )' % a3),
              w.s([p2], 'nn0red', '( %s -> ( 2 ^ B ) e. RR )' % a3), kl, ltp], 'lttrd', '( %s -> k < ( 2 ^ B ) )' % a3)
    klb = w.s([kn, bb3, kp, w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ B )' % (a3, NK))
    nkn = w.s([ekw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (a3, NK))
    cl3 = Closure(w, a3, {'B': ('NN0', bb3), NK: ('NN0', nkn)})
    cl3.atom(NK)
    le = linarith(w, a3, [klb], '%s <_ %s' % (ni, YINC), closure=cl3)
    yn3 = cl3.mem(YINC, 'NN0')
    t3 = hrle(w, a3, lift(mk['phm'], PHM), t2, Ci2, Dn, ni, YINC, yn3, le)
    HT = TRI(Ci2, Dn, YINC)
    tx = w.s([t3], 'ex', '( %s -> ( %s -> %s ) )' % (a2, HJ, HT))
    tr1 = w.s([tx], 'ralrimiva', '( %s -> A. d e. ( TM2Stk ` T ) ( %s -> %s ) )' % (a1, HJ, HT))
    hinc = 'A. k e. ( 0 ..^ ( # ` L ) ) A. d e. ( TM2Stk ` T ) ( %s -> %s )' % (HJ, HT)
    ex[hinc] = w.s([tr1], 'ralrimiva', '( %s -> %s )' % (ps, hinc))
    ex["%s : ( 0 ... ( # ` L ) ) --> Word Gamma'" % QFAM] = qf
    ex['( %s ` 0 ) = <" 4 ">' % QFAM] = q0v
    ex['%s e. NN0' % YINC] = yn
    return {'Q': QFAM, 'Y': YINC}


def tmillen():
    lab = 'tmillen'
    w, ps, c, mk, ex, t, cc = installed(lab, 'llen', 'tm2llen', K4,
        'Lean\'s ` listLen_runs ` at the machine: wherever ` listLen x y s z ` is installed, from any state with the '
        'list ` ( encListB ` L ) ` (entries of at most ` B ` bits, fewer than ` 2 ^ B ` of them) on ` x ` it pushes '
        'the count on ` y ` and restores every other stack (~ tm2llen at the concrete handlers, the counter the '
        'installed ` incr ` , ~ tmiincs ).', m_more=len_more)
    C0, D0, n0 = triple_parts(cc)
    QL = QV('( # ` L )')
    ll = c['L e. Word Word ( { 1 } X. 2o )']
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ps)
    nfz = w.s([nl, w.inst('nn0fz0')], 'sylib', '( %s -> ( # ` L ) e. ( 0 ... ( # ` L ) ) )' % ps)
    q, ecl, s4l = qval(w, ps, '( # ` L )', nfz, nl)
    dd = c[STKD('D')]
    djg = w.s([stkfv(w, ps, 'D', 'J', mk['tv'], dd, mk['k']['J']['kd']), mk['k']['J']['wge']], 'eleqtrd',
              "( %s -> ( D ` J ) e. Word Gamma' )" % ps)
    a = w.s([q], 'oveq1d', '( %s -> ( %s ++ ( D ` J ) ) = ( ( ( encNatGam ` ( # ` L ) ) ++ <" 4 "> ) ++ ( D ` J ) ) )' % (ps, QL))
    b = w.s([ecl, s4l, djg, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( encNatGam ` ( # ` L ) ) ++ <" 4 "> ) ++ ( D ` J ) ) = %s )' % (ps, EWL))
    ab = w.s([a, b], 'eqtrd', '( %s -> ( %s ++ ( D ` J ) ) = %s )' % (ps, QL, EWL))
    V1 = '( %s ++ ( D ` J ) )' % QL
    ue = upeq(w, ps, 'D', 'J', ab, V1, EWL)
    deq = clneq(w, ps, 'E', S, ue, UP('D', 'J', V1), UP('D', 'J', EWL))
    _, C2, D2, n2 = hrrw(w, ps, t, C0, D0, n0, deq=deq, qed=True)
    assert TRI(C2, D2, n2) == CONCL[lab], '\nGOT  %s\nWANT %s' % (TRI(C2, D2, n2), CONCL[lab])
    return w.run()


def tmillenb():
    lab = 'tmillenb'
    T = TREES[lab]
    ps = cj(T)
    w = W(lab, 'Lean\'s ` listLen_le_B ` at the machine: ` listLen x y s z ` on the list ` ( encList ` L ) ` of '
               'numbers below ` 2 ^ B ` , fewer than ` 2 ^ B ` of them, runs within ` ( ( # ` L ) + 1 ) x. ( TMB ` B ) ` '
               '(~ tmillen at ` ( encNatGam o. L ) ` , ~ tm2llistb ).')
    c = Ctx(w, ps, T)
    phm = c[PHM]
    ll = c['L e. Word NN0']; bb = c['B e. NN0']; ha = c['A. a e. ran L a < ( 2 ^ B )']
    EL = '( encNatGam o. L )'
    ef = w.s([], 'tm2lbitf', 'encNatGam : NN0 --> Word ( { 1 } X. 2o )')
    efa = w.s([ef], 'a1i', '( %s -> encNatGam : NN0 --> Word ( { 1 } X. 2o ) )' % ps)
    elc = w.s([ll, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (ps, EL))
    eq = w.s([ll, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` L ) = ( encListB ` %s ) )' % (ps, EL))
    bw = w.s([ll, bb, ha, w.inst('tm2lrnenc')], 'syl3anc', '( %s -> A. w e. ran %s ( # ` w ) <_ B )' % (ps, EL))
    ln = w.s([ll, efa, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` L ) )' % (ps, EL))
    dk = c['( D ` K ) = ( ( encList ` L ) ++ R )']
    dk2 = w.s([dk, w.s([eq], 'oveq1d', '( %s -> ( ( encList ` L ) ++ R ) = ( ( encListB ` %s ) ++ R ) )' % (ps, EL))], 'eqtrd',
              '( %s -> ( D ` K ) = ( ( encListB ` %s ) ++ R ) )' % (ps, EL))
    lt = w.s([ln, c['( # ` L ) < ( 2 ^ B )']], 'eqbrtrd', '( %s -> ( # ` %s ) < ( 2 ^ B ) )' % (ps, EL))
    ex = {'%s e. Word Word ( { 1 } X. 2o )' % EL: elc, '( D ` K ) = ( ( encListB ` %s ) ++ R )' % EL: dk2,
          'A. w e. ran %s ( # ` w ) <_ B' % EL: bw, '( # ` %s ) < ( 2 ^ B )' % EL: lt}
    t, cc = inst(w, ps, 'tmillen', {'L': EL}, Bld(w, ps, c, ex))
    C0, D0, n0 = triple_parts(cc)
    deq, D1 = w.rewrite(D0, {'( # ` %s )' % EL: ('( # ` L )', ln)}, ps)
    neq, n1 = w.rewrite(n0, {'( # ` %s )' % EL: ('( # ` L )', ln)}, ps)
    t1, C1, D1b, n1b = hrrw(w, ps, t, C0, D0, n0, deq=deq, neq=neq)
    assert n1b == BLEN, n1b
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ps)
    from t6b_c_nlvl import bform
    bform(w, ps, phm, t1, C1, D1b, BLEN, nl, bb, '( ( ( 4 x. B ) + %s ) + ; 1 2 )' % YINC, '9')
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        if l in ('tmilrevu', 'tmilappu', 'tmilcpyu', 'tmillenu'):
            unf(l[3:-1])
        else:
            globals()[l]()
