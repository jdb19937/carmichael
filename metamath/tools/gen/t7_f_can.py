"""T7: canonNum at the machine (blueprint D6): the two cases on the value,
their join, and canonNum_le_B; the two word lemmas on inclBool."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

EL = '( encodeNat ` ( toNat ` L ) )'
IBE = '( inclBool o. %s )' % EL
WP = '( reverse ` %s )' % IBE
NZ = '( ( # ` L ) - ( # ` %s ) )' % EL
W0 = '( <. 1 , (/) >. repeatS %s )' % NZ
TN = '( toNat ` L )'


def tmcinclf():
    w = W('tmcinclf', 'The inclusion of the bits in the alphabet lands in the bit letters.')
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V')
    s1 = w.s([one, w.inst('snidg')], 'ax-mp', '1 e. { 1 }')
    s1a = w.s([s1], 'a1i', '( b e. 2o -> 1 e. { 1 } )')
    idb = w.s([], 'id', '( b e. 2o -> b e. 2o )')
    op = w.s([s1a, idb], 'opelxpd', '( b e. 2o -> <. 1 , b >. e. %s )' % BITS)
    d = w.s([], 'df-inclbool', 'inclBool = ( b e. 2o |-> <. 1 , b >. )')
    w.qed([d, op], 'fmpti', 'inclBool : 2o --> %s' % BITS)
    return w.run()


def tmcibw():
    w = W('tmcibw', 'The machine word of a bit word is a word over the bit letters (Lean ` bits l ` ).')
    ph = 'L e. Word 2o'
    f = closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS)
    ll = w.s([], 'id', '( %s -> L e. Word 2o )' % ph)
    w.qed([ll, f, w.inst('wrdco')], 'syl2anc', '( %s -> ( inclBool o. L ) e. Word %s )' % (ph, BITS))
    return w.run()


def gid_id(w, ph, X, xb):
    """( ph -> ( GID o. X ) = X ) from xb : X e. Word BITS"""
    f = w.s([xb, w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> %s )' % (ph, X, X, BITS))
    rn = w.s([f, w.inst('frn')], 'syl', '( %s -> ran %s C_ %s )' % (ph, X, BITS))
    c1 = w.s([rn, w.inst('cores')], 'syl', '( %s -> ( %s o. %s ) = ( _I o. %s ) )' % (ph, GID, X, X))
    rl = w.s([f, w.inst('frel')], 'syl', '( %s -> Rel %s )' % (ph, X))
    c2 = w.s([rl, w.inst('coi2')], 'syl', '( %s -> ( _I o. %s ) = %s )' % (ph, X, X))
    return w.s([c1, c2], 'eqtrd', '( %s -> ( %s o. %s ) = %s )' % (ph, GID, X, X))


def cancase(pos):
    lab = 'tmccanp' if pos else 'tmccan0'
    tree = TREE_CANP if pos else TREE_CAN0
    ph = cj(tree)
    w = W(lab, '` canonNum x s ` at the machine, the value %s: ~ tm2fcan with the handlers ` readA ` , '
               '` ra.isSome ` , ` bitOf ra ` , the strip test ` ra = some false ` and the identity pop, the '
               'letter map the identity on the bits; the reversed word\'s decomposition by ~ bwstriprevg and '
               'the stop letter %s (blueprint D6).' % (('positive', '` <. 1 , 1o >. ` by ~ bwstripfst') if pos
                                                      else ('zero', 'the terminator ` 4 ` (~ encnat0 )')))
    c = Ctx(w, ph, tree)
    mk = machine(w, ph, c, ['K', 'J'])
    ll, xg, dd = c[WRD('L', '2o')], c[WRD('X', GAM)], c[STKD('D')]
    case = c['( toNat ` L ) e. NN' if pos else '( toNat ` L ) = 0']
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    tn = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TN))
    el = w.s([tn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EL))
    ibl = w.s([ll, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. L ) e. Word %s )' % (ph, BITS))
    ibe = w.s([el, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IBE, BITS))
    wp = w.s([ibe, w.inst('revcl')], 'syl', '( %s -> %s e. Word %s )' % (ph, WP, BITS))
    bs = closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS)
    wbss = closed(w, ph, 'tm2lwbss', '%s C_ %s' % (WB, WG))
    wpg = w.s([wbss, wp], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, WP))
    # the decomposition
    gi = gid_id(w, ph, '( inclBool o. L )', ibl)
    rg = w.s([gi], 'fveq2d', '( %s -> ( reverse ` ( %s o. ( inclBool o. L ) ) ) = ( reverse ` ( inclBool o. L ) ) )' % (ph, GID))
    sr = w.s([ll, w.inst('bwstriprevg')], 'syl', '( %s -> ( reverse ` ( inclBool o. L ) ) = ( %s ++ %s ) )' % (ph, W0, WP))
    dec = w.s([rg, sr], 'eqtrd', '( %s -> ( reverse ` ( %s o. ( inclBool o. L ) ) ) = ( %s ++ %s ) )' % (ph, GID, W0, WP))
    # W0 e. Word B0
    b0e = w.s([w.s([], 'opex', '%s e. _V' % BIT0), w.inst('snidg')], 'ax-mp', '%s e. %s' % (BIT0, B0))
    b0a = w.s([b0e], 'a1i', '( %s -> %s e. %s )' % (ph, BIT0, B0))
    lel = w.s([el, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, EL))
    lll = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    sl = w.s([ll, w.inst('bwstriplen')], 'syl', '( %s -> ( # ` %s ) <_ ( # ` L ) )' % (ph, EL))
    ns = w.s([lel, lll, w.inst('nn0sub')], 'syl2anc', '( %s -> ( ( # ` %s ) <_ ( # ` L ) <-> %s e. NN0 ) )' % (ph, EL, NZ))
    nz = w.s([ns, sl], 'mpbid', '( %s -> %s e. NN0 )' % (ph, NZ))
    w0 = w.s([b0a, nz, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, W0, B0))
    b0ss = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V'), w.inst('snidg')], 'ax-mp', '1 e. { 1 }'),
                w.s([], '0el2o', '(/) e. 2o'), w.inst('opelxpi')], 'mp2an', '%s e. %s' % (BIT0, BITS))
    b0s = w.s([w.s([b0ss, w.inst('snssi')], 'ax-mp', '%s C_ %s' % (B0, BITS))], 'a1i', '( %s -> %s C_ %s )' % (ph, B0, BITS))
    gf = closed(w, ph, 'f1oi', '%s : %s -1-1-onto-> %s' % (GID, BITS, BITS))
    gf2 = w.s([gf, w.inst('f1of')], 'syl', '( %s -> %s : %s --> %s )' % (ph, GID, BITS, BITS))
    # the stop letter
    if pos:
        YP = BIT1
        TL = '( %s substr <. 1 , ( # ` %s ) >. )' % (WP, WP)
        XP = '( %s ++ <" 4 "> )' % TL
        f0 = w.s([case, w.inst('bwstripfst')], 'syl', '( %s -> ( %s ` 0 ) = %s )' % (ph, WP, BIT1))
        pe = '( %s /\\ %s = (/) )' % (ph, WP)
        e1 = w.s([], 'fveq1', '( %s = (/) -> ( %s ` 0 ) = ( (/) ` 0 ) )' % (WP, WP))
        e1a = w.s([e1], 'adantl', '( %s -> ( %s ` 0 ) = ( (/) ` 0 ) )' % (pe, WP))
        e2 = closed(w, pe, '0fv', '( (/) ` 0 ) = (/)')
        e3 = w.s([e1a, e2], 'eqtrd', '( %s -> ( %s ` 0 ) = (/) )' % (pe, WP))
        f0a = w.s([f0], 'adantr', '( %s -> ( %s ` 0 ) = %s )' % (pe, WP, BIT1))
        e4 = w.s([f0a, e3], 'eqtr3d', '( %s -> %s = (/) )' % (pe, BIT1))
        one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V')
        nz1 = w.s([one, w.s([], '1oex', '1o e. _V')], 'opnzi', '%s =/= (/)' % BIT1)
        nz1b = w.s([nz1, w.s([], 'df-ne', '( %s =/= (/) <-> -. %s = (/) )' % (BIT1, BIT1))], 'mpbi', '-. %s = (/)' % BIT1)
        nz1a = w.s([nz1b], 'a1i', '( %s -> -. %s = (/) )' % (ph, BIT1))
        wpn = w.s([e4, nz1a], 'mtand', '( %s -> -. %s = (/) )' % (ph, WP))
        wpne = w.s([wpn], 'neqned', '( %s -> %s =/= (/) )' % (ph, WP))
        hd = w.s([wpg, wpne, w.inst('wrdhdtl')], 'syl2anc', '( %s -> %s = ( <" ( %s ` 0 ) "> ++ %s ) )' % (ph, WP, WP, TL))
        s0 = w.s([f0], 's1eqd', '( %s -> <" ( %s ` 0 ) "> = <" %s "> )' % (ph, WP, BIT1))
        s0b = w.s([s0], 'oveq1d', '( %s -> ( <" ( %s ` 0 ) "> ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, WP, TL, BIT1, TL))
        hd2 = w.s([hd, s0b], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, WP, BIT1, TL))
        hd3 = w.s([hd2], 'oveq1d', '( %s -> ( %s ++ <" 4 "> ) = ( ( <" %s "> ++ %s ) ++ <" 4 "> ) )' % (ph, WP, BIT1, TL))
        y1g = closed(w, ph, '1oel2o', '1o e. 2o')
        y1 = w.s([y1g, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT1))
        s1y = w.s([y1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT1))
        tlg = w.s([wpg, w.inst('swrdcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, TL))
        s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
        asc = w.s([s1y, tlg, s4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ <" 4 "> ) = ( <" %s "> ++ %s ) )' % (ph, BIT1, TL, BIT1, XP))
        stop = w.s([hd3, asc], 'eqtrd', '( %s -> ( %s ++ <" 4 "> ) = ( <" %s "> ++ %s ) )' % (ph, WP, BIT1, XP))
        xpg = w.s([tlg, s4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, XP))
        ypg = y1
        # Y' =/= <. 1 , (/) >.
        o = w.s([one, w.s([], '1oex', '1o e. _V'), w.inst('opthg')], 'mp2an', '( %s = %s <-> ( 1 = 1 /\\ 1o = (/) ) )' % (BIT1, BIT0))
        n10 = w.s([w.s([], '1n0', '1o =/= (/)'), w.s([], 'df-ne', '( 1o =/= (/) <-> -. 1o = (/) )')], 'mpbi', '-. 1o = (/)')
        n2 = w.s([n10], 'intnan', '-. ( 1 = 1 /\\ 1o = (/) )')
        n3 = w.s([o, n2], 'mtbir', '-. %s = %s' % (BIT1, BIT0))
        ne = w.s([n3, w.s([], 'df-ne', '( %s =/= %s <-> -. %s = %s )' % (BIT1, BIT0, BIT1, BIT0))], 'mpbir', '%s =/= %s' % (BIT1, BIT0))
        nea = w.s([ne], 'a1i', '( %s -> %s =/= %s )' % (ph, BIT1, BIT0))
    else:
        YP = '4'
        XP = '(/)'
        e0 = w.s([case], 'fveq2d', '( %s -> %s = ( encodeNat ` 0 ) )' % (ph, EL))
        e0b = w.s([e0, closed(w, ph, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'eqtrd', '( %s -> %s = (/) )' % (ph, EL))
        e1 = w.s([e0b], 'coeq2d', '( %s -> %s = ( inclBool o. (/) ) )' % (ph, IBE))
        e1b = w.s([e1, closed(w, ph, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd', '( %s -> %s = (/) )' % (ph, IBE))
        e2 = w.s([e1b], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ph, WP))
        e2b = w.s([e2, closed(w, ph, 'rev0', '( reverse ` (/) ) = (/)')], 'eqtrd', '( %s -> %s = (/) )' % (ph, WP))
        e3 = w.s([e2b], 'oveq1d', '( %s -> ( %s ++ <" 4 "> ) = ( (/) ++ <" 4 "> ) )' % (ph, WP))
        s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
        e4 = w.s([s4, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ <" 4 "> ) = <" 4 "> )' % ph)
        e5 = w.s([s4, w.inst('ccatrid')], 'syl', '( %s -> ( <" 4 "> ++ (/) ) = <" 4 "> )' % ph)
        stop = w.s([w.s([e3, e4], 'eqtrd', '( %s -> ( %s ++ <" 4 "> ) = <" 4 "> )' % (ph, WP)), e5], 'eqtr4d',
                   '( %s -> ( %s ++ <" 4 "> ) = ( <" 4 "> ++ (/) ) )' % (ph, WP))
        xpg = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
        ypg = g4
        r4 = closed(w, ph, '4re', '4 e. RR')
        z2 = closed(w, ph, '0el2o', '(/) e. 2o')
        n3 = w.s([r4, z2, w.inst('tmcnbit')], 'syl2anc', '( %s -> -. 4 = %s )' % (ph, BIT0))
        nea = w.s([n3], 'neqned', '( %s -> 4 =/= %s )' % (ph, BIT0))
    # the interfaces
    mving = w.s([], 'tmcmving', ST_MVING)
    hcg = w.s([mving], 'simpli', ST_MVING.split(' /\\ A. m e. ')[0][2:])
    heg = w.s([mving], 'simpri', 'A. m e. ' + ST_MVING.split(' /\\ A. m e. ')[1][:-2])
    hcga = w.s([hcg], 'a1i', '( %s -> %s )' % (ph, formula(w, hcg)))
    hega = w.s([heg], 'a1i', '( %s -> %s )' % (ph, formula(w, heg)))
    spj = w.s([ypg, nea], 'jca', "( %s -> ( %s e. Gamma' /\\ %s =/= %s ) )" % (ph, YP, YP, BIT0))
    spi = w.s([spj, w.inst('tmcspi')], 'syl', '( %s -> %s )' % (ph, ST_SPI.split(' -> ', 1)[1][:-2].replace(NVA('m', 'Y'), NVA('m', YP))))
    sp1 = w.s([spi], 'simpld', '( %s -> %s )' % (ph, ST_SPI.split(' -> ( ', 1)[1].split(' /\\ A. m e. ')[0]))
    sp2 = w.s([spi], 'simprd', '( %s -> A. m e. %s )' % (ph, ST_SPI.split(' /\\ A. m e. ')[1][:-4].replace(NVA('m', 'Y'), NVA('m', YP))))
    nss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPC))
    nss2 = w.s([nss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPC))
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    cra_b = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', 'if ( ( TMra ` u ) = ( inl ` (/) ) , 1o , (/) ) e. 2o')
    craty = lamty(w, ph, mk, CRA0, lambda t: 'if ( ( TMra ` %s ) = ( inl ` (/) ) , 1o , (/) )' % t, '2o', w.s([], '2oex', '2o e. _V'), cra_b)
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], CTY(CIS): cis_ty(w, ph, mk), CTY(CRA0): craty,
             leaf(hcga): hcga, leaf(hega): hega, leaf(sp1): sp1, leaf(sp2): sp2, leaf(nss2): nss2,
             leaf(dec): dec, leaf(stop): stop, WRD(W0, B0): w0, WRD(WP, BITS): wp, '%s C_ %s' % (B0, BITS): b0s,
             leaf(gf2): gf2, WRD('( inclBool o. L )', BITS): ibl}
    for k in ['K', 'J']:
        K = mk['k'][k]
        extra['%s e. %s' % (k, DG)] = K['kd']
        extra[RTY('TMrdA', k)] = K['hdl']['TMrdA']
        extra[RTY(PID, k)] = K['hdl'][PID]
        extra[PTY(PBR, k)] = pbr_ty(w, ph, mk, k)
        extra['%s C_ %s' % (BITS, GX(k))] = bitsgk(w, ph, mk, k)
        extra['4 e. %s' % GX(k)] = letgk(w, ph, mk, '4', k, g4)
    extra[WRD('X', GK)] = togk(w, ph, mk, 'X', 'K', xg)
    extra['%s e. %s' % (YP, GJ)] = letgk(w, ph, mk, YP, 'J', ypg)
    extra[WRD(XP, GJ)] = togk(w, ph, mk, XP, 'J', xpg)
    bld = Builder(w, ph, c, extra)
    m = {'F': 'TMrdA', "F'": 'TMrdA', 'F"': PID, 'C': CIS, "C'": CRA0, 'P': PBR, 'B': BITS, 'B0': B0, 'G': GID,
         'Y': '4', "Y'": YP, "X'": XP, 'W': '( inclBool o. L )', 'W0': W0, "W'": WP, 'N': NPC}
    ante, concl = split_imp(stmt('tm2fcan'))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl, m)
    tri = w.s([st, w.inst('tm2fcan')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1, n1 = triple_parts(c2)
    # rewrite the postcondition and the bound
    gw = gid_id(w, ph, WP, wp)
    r1 = w.s([gw], 'fveq2d', '( %s -> ( reverse ` ( %s o. %s ) ) = ( reverse ` %s ) )' % (ph, GID, WP, WP))
    ibeg = w.s([wbss, ibe], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, IBE))
    r2 = w.s([ibeg, w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = %s )' % (ph, WP, IBE))
    r3 = w.s([tn, w.inst('encnatgamval')], 'syl', '( %s -> %s = %s )' % (ph, ENL, IBE))
    r4 = w.s([w.s([r1, r2], 'eqtrd', '( %s -> ( reverse ` ( %s o. %s ) ) = %s )' % (ph, GID, WP, IBE)), r3], 'eqtr4d',
             '( %s -> ( reverse ` ( %s o. %s ) ) = %s )' % (ph, GID, WP, ENL))
    r5 = w.s([r4], 'oveq1d', '( %s -> ( ( reverse ` ( %s o. %s ) ) ++ %s ) = ( %s ++ %s ) )' % (ph, GID, WP, YX4, ENL, YX4))
    ue = upeq(w, ph, 'D', 'K', r5, '( ( reverse ` ( %s o. %s ) ) ++ %s )' % (GID, WP, YX4), CC(ENL, YX4))
    deq = clneq(w, ph, 'E', NPC, ue, UP('D', 'K', '( ( reverse ` ( %s o. %s ) ) ++ %s )' % (GID, WP, YX4)), UP('D', 'K', CC(ENL, YX4)))
    ln = w.s([ll, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. L ) ) = ( # ` L ) )' % ph)
    ln2 = w.s([ln], 'oveq2d', '( %s -> ( 2 x. ( # ` ( inclBool o. L ) ) ) = ( 2 x. ( # ` L ) ) )' % ph)
    ln3 = w.s([ln2], 'oveq1d', '( %s -> ( ( 2 x. ( # ` ( inclBool o. L ) ) ) + 5 ) = ( ( 2 x. ( # ` L ) ) + 5 ) )' % ph)
    _, C2, D2, n2 = hrrw(w, ph, tri, C1, D1, n1, deq=deq, neq=ln3, qed=True)
    assert TRI(C2, D2, n2) == CONCL_CAN, (TRI(C2, D2, n2), CONCL_CAN)
    return w.run()


def tmccan():
    lab = 'tmccan'
    ph = cj(TREE_CAN)
    w = W(lab, '` canonNum x s ` at the machine: the top bit word of ` K ` is replaced by the canonical word of '
               'its value, ` flag ` , ` cmp ` , ` carry ` are preserved, in ` 2 |L| + 5 ` steps (Lean '
               '` canonNum_runs ` , whose bound is ` 3 |l| + 5 ` ).  The join of ~ tmccan0 and ~ tmccanp .')
    c = Ctx(w, ph, TREE_CAN)
    ll = c[WRD('L', '2o')]
    tn = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TN))
    e = w.s([], 'elnn0', '( %s e. NN0 <-> ( %s e. NN \\/ %s = 0 ) )' % (TN, TN, TN))
    d = w.s([tn, e], 'sylib', '( %s -> ( %s e. NN \\/ %s = 0 ) )' % (ph, TN, TN))
    p = w.s([], 'tmccanp', '( %s -> %s )' % (cj(TREE_CANP), CONCL_CAN))
    z = w.s([], 'tmccan0', '( %s -> %s )' % (cj(TREE_CAN0), CONCL_CAN))
    w.qed([p, z, d], 'mpjaodan', '( %s -> %s )' % (ph, CONCL_CAN))
    return w.run()


def tmccanb():
    lab = 'tmccanb'
    ph = cj(TREE_CANB)
    w = W(lab, '` canonNum_le_B ` : ~ tmccan within the budget ` ( TMB ` B ) ` for a word of at most ` B ` bits '
               '(Lean: ` le_B_of_le_linear ` ; here ~ tmblin at ` 3 ` ).')
    c = Ctx(w, ph, TREE_CANB)
    phm = c[PHM]
    inner = c[cj(TREE_CAN)]
    tri = w.s([inner, w.inst('tmccan')], 'syl', '( %s -> %s )' % (ph, CONCL_CAN))
    C1, D1, n1 = triple_parts(CONCL_CAN)
    ll, bb, lb = c[WRD('L', '2o')], c['B e. NN0'], c['( # ` L ) <_ B']
    lll = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    three = closed(w, ph, '3nn0', '3 e. NN0')
    le3 = closed(w, ph, '3le64' if False else 'tmc3le64', None) if False else None
    l64 = w.s([], 'eqid', '1 = 1') if False else None
    # 3 <_ 64 by num.py's closed comparison
    import num
    le = num.le_lit(w, '3', '; 6 4') if hasattr(num, 'le_lit') else None
    lea = w.s([le], 'a1i', '( %s -> 3 <_ ; 6 4 )' % ph)
    j = w.s([bb, three, lea], '3jca', '( %s -> ( B e. NN0 /\\ 3 e. NN0 /\\ 3 <_ ; 6 4 ) )' % ph)
    tl = w.s([j, w.inst('tmblin')], 'syl', '( %s -> ( 3 x. ( B + 2 ) ) <_ ( TMB ` B ) )' % ph)
    tb = w.s([bb, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)
    tb0 = w.s([tb], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
    b0 = w.s([bb], 'nn0ge0d', '( %s -> 0 <_ B )' % ph)
    bound(w, ph, phm, tri, C1, D1, n1, '( TMB ` B )', {'( # ` L )': lll, 'B': bb, '( TMB ` B )': tb0}, hyps=[lb, tl, b0], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tmcinclf'): tmcinclf()
    if want('tmcibw'): tmcibw()
    if want('tmccan0'): cancase(False)
    if want('tmccanp'): cancase(True)
    if want('tmccan'): tmccan()
    if want('tmccanb'): tmccanb()
