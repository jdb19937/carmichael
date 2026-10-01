"""T7: ` incr y s ` at the machine (Lean ` incr_runs ` ): the increment of a
run of ones (T4 ~ incbitscons1 by induction), the two cases on the stop
letter (a zero bit, the terminator) as instances of ~ tm2fincr , and their
join.

    MM_DB=sorties/t7.mm python3 tools/gen/t7_s_inc.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7inc import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty, ral_S
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

FACC = dict(car='TMcar', ra='TMra', rb='TMrb', da='TMda', db='TMdb', cmp='TMcmp', fl='TMfl')


def S_(l):
    return dict(STMTS7)[l]


def tmcinc1():
    lab = 'tmcinc1'
    w = W(lab, 'Incrementing a run of ones followed by a word turns the run into zeros and increments the word '
               '(Lean ` incBits ` on ` true :: l ` , iterated).')
    PS = lambda x: '( incBits ` ( ( 1o repeatS %s ) ++ M ) ) = ( ( (/) repeatS %s ) ++ ( incBits ` M ) )' % (x, x)
    hyps = []
    for nm, x in [('0', '0'), ('y', 'y'), ('y1', '( y + 1 )'), ('C', 'C')]:
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (x, x))
        cg, new = w.wcongr(PS('x'), {'x': x}, 'x = %s' % x, {'x': idx})
        assert new == PS(x), new
        hyps.append(cg)
    ph = 'M e. Word 2o'
    # base
    z = w.s([], '0ex', '(/) e. _V'); o = w.s([], '1oex', '1o e. _V')
    r1 = w.s([o, w.inst('repsw0')], 'ax-mp', '( 1o repeatS 0 ) = (/)')
    r0 = w.s([z, w.inst('repsw0')], 'ax-mp', '( (/) repeatS 0 ) = (/)')
    mm = w.s([], 'id', '( %s -> M e. Word 2o )' % ph)
    b1 = w.s([w.s([r1], 'oveq1i', '( ( 1o repeatS 0 ) ++ M ) = ( (/) ++ M )'), w.s([mm, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ M ) = M )' % ph)], 'eqtrid',
             '( %s -> ( ( 1o repeatS 0 ) ++ M ) = M )' % ph)
    b2 = w.s([b1], 'fveq2d', '( %s -> ( incBits ` ( ( 1o repeatS 0 ) ++ M ) ) = ( incBits ` M ) )' % ph)
    ib = w.s([mm, w.inst('incbitscl')], 'syl', '( %s -> ( incBits ` M ) e. Word 2o )' % ph)
    b3 = w.s([w.s([r0], 'oveq1i', '( ( (/) repeatS 0 ) ++ ( incBits ` M ) ) = ( (/) ++ ( incBits ` M ) )'),
              w.s([ib, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( incBits ` M ) ) = ( incBits ` M ) )' % ph)], 'eqtrid',
             '( %s -> ( ( (/) repeatS 0 ) ++ ( incBits ` M ) ) = ( incBits ` M ) )' % ph)
    base = w.s([b2, b3], 'eqtr4d', '( %s -> %s )' % (ph, PS('0')))
    # step
    ps = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (ph, PS('y'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (ps, PS('y')))
    yn = w.s([], 'simplr', '( %s -> y e. NN0 )' % ps)
    mw = w.s([], 'simpll', '( %s -> M e. Word 2o )' % ps)
    def rep1(S, sv, bb):
        """( ps -> ( S repeatS ( y + 1 ) ) = ( <" S "> ++ ( S repeatS y ) ) )"""
        one = closed(w, ps, '1nn0', '1 e. NN0')
        svp = w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ps, S))
        rc = w.s([svp, one, yn, w.inst('repswccat')], 'syl3anc', '( %s -> ( ( %s repeatS 1 ) ++ ( %s repeatS y ) ) = ( %s repeatS ( 1 + y ) ) )' % (ps, S, S, S))
        r1_ = w.s([svp, w.inst('repsw1')], 'syl', '( %s -> ( %s repeatS 1 ) = <" %s "> )' % (ps, S, S))
        r1b = w.s([r1_], 'oveq1d', '( %s -> ( ( %s repeatS 1 ) ++ ( %s repeatS y ) ) = ( <" %s "> ++ ( %s repeatS y ) ) )' % (ps, S, S, S, S))
        ic = w.s([w.s([yn], 'nn0cnd', '( %s -> y e. CC )' % ps), closed(w, ps, 'ax-1cn', '1 e. CC')], 'addcomd', '( %s -> ( y + 1 ) = ( 1 + y ) )' % ps)
        rr = w.s([ic], 'oveq2d', '( %s -> ( %s repeatS ( y + 1 ) ) = ( %s repeatS ( 1 + y ) ) )' % (ps, S, S))
        return w.s([rr, w.s([rc, r1b], 'eqtr3d', '( %s -> ( %s repeatS ( 1 + y ) ) = ( <" %s "> ++ ( %s repeatS y ) ) )' % (ps, S, S, S))], 'eqtrd',
                   '( %s -> ( %s repeatS ( y + 1 ) ) = ( <" %s "> ++ ( %s repeatS y ) ) )' % (ps, S, S, S))
    e1 = rep1('1o', o, '1oel2o')
    e0 = rep1('(/)', z, '0el2o')
    b1o = closed(w, ps, '1oel2o', '1o e. 2o'); b0o = closed(w, ps, '0el2o', '(/) e. 2o')
    R1 = '( 1o repeatS y )'; R0 = '( (/) repeatS y )'
    r1w = w.s([b1o, yn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, R1))
    r0w = w.s([b0o, yn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, R0))
    s1 = w.s([b1o], 's1cld', '( %s -> <" 1o "> e. Word 2o )' % ps)
    s0 = w.s([b0o], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ps)
    a1 = w.s([e1], 'oveq1d', '( %s -> ( ( 1o repeatS ( y + 1 ) ) ++ M ) = ( ( <" 1o "> ++ %s ) ++ M ) )' % (ps, R1))
    a2 = w.s([s1, r1w, mw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 1o "> ++ %s ) ++ M ) = ( <" 1o "> ++ ( %s ++ M ) ) )' % (ps, R1, R1))
    a3 = w.s([w.s([a1, a2], 'eqtrd', '( %s -> ( ( 1o repeatS ( y + 1 ) ) ++ M ) = ( <" 1o "> ++ ( %s ++ M ) ) )' % (ps, R1))], 'fveq2d',
             '( %s -> ( incBits ` ( ( 1o repeatS ( y + 1 ) ) ++ M ) ) = ( incBits ` ( <" 1o "> ++ ( %s ++ M ) ) ) )' % (ps, R1))
    rm = w.s([r1w, mw, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ M ) e. Word 2o )' % (ps, R1))
    a4 = w.s([rm, w.inst('incbitscons1')], 'syl', '( %s -> ( incBits ` ( <" 1o "> ++ ( %s ++ M ) ) ) = ( <" (/) "> ++ ( incBits ` ( %s ++ M ) ) ) )' % (ps, R1, R1))
    a5 = w.s([ih], 'oveq2d', '( %s -> ( <" (/) "> ++ ( incBits ` ( %s ++ M ) ) ) = ( <" (/) "> ++ ( %s ++ ( incBits ` M ) ) ) )' % (ps, R1, R0))
    ibw = w.s([mw, w.inst('incbitscl')], 'syl', '( %s -> ( incBits ` M ) e. Word 2o )' % ps)
    a6 = w.s([s0, r0w, ibw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" (/) "> ++ %s ) ++ ( incBits ` M ) ) = ( <" (/) "> ++ ( %s ++ ( incBits ` M ) ) ) )' % (ps, R0, R0))
    a7 = w.s([e0], 'oveq1d', '( %s -> ( ( (/) repeatS ( y + 1 ) ) ++ ( incBits ` M ) ) = ( ( <" (/) "> ++ %s ) ++ ( incBits ` M ) ) )' % (ps, R0))
    rhs = w.s([a7, a6], 'eqtrd', '( %s -> ( ( (/) repeatS ( y + 1 ) ) ++ ( incBits ` M ) ) = ( <" (/) "> ++ ( %s ++ ( incBits ` M ) ) ) )' % (ps, R0))
    lhs = w.s([w.s([a3, a4], 'eqtrd', '( %s -> ( incBits ` ( ( 1o repeatS ( y + 1 ) ) ++ M ) ) = ( <" (/) "> ++ ( incBits ` ( %s ++ M ) ) ) )' % (ps, R1)), a5], 'eqtrd',
              '( %s -> ( incBits ` ( ( 1o repeatS ( y + 1 ) ) ++ M ) ) = ( <" (/) "> ++ ( %s ++ ( incBits ` M ) ) ) )' % (ps, R0))
    step = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (ps, PS('( y + 1 )')))
    w.qed(hyps + [base, step], 'nn0indd', S_('tmcinc1'))
    return w.run()


def sn_in(w, ph, A, aex):
    """( ph -> A e. { A } )"""
    return w.s([w.s([aex, w.inst('snidg')], 'ax-mp', '%s e. { %s }' % (A, A))], 'a1i', '( %s -> %s e. { %s } )' % (ph, A, A))


def inccase(pos):
    lab = 'tmcincp' if pos else 'tmcinct'
    CASE = '%s =/= (/)' % RR_ if pos else '%s = (/)' % RR_
    tree = (TREE_INC, CASE)
    ph = cj(tree)
    w = W(lab, '` incr y s ` at the machine, the carry run %s: ~ tm2fincr with ` readA ` , the tests '
               '` ra = some true ` , ` ra = some false ` , the constant pushes, the mover\'s handlers; the run of ones '
               'is ` carries ` (T4 ~ bwcarriesdec ).' % ('stopped by a zero bit' if pos else 'running into the terminator'))
    c = Ctx(w, ph, tree)
    mk = machine(w, ph, c, ['K', 'J'])
    seq = mk['seq']
    ll, xg, dd = c[WRD('L', '2o')], c[WRD('X', GAM)], c[STKD('D')]
    dk = c[DATA_CAN[1]]
    case = c[CASE]
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    b0o = closed(w, ph, '0el2o', '(/) e. 2o'); b1o = closed(w, ph, '1oel2o', '1o e. 2o')
    g0 = w.s([b0o, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT0))
    g1 = w.s([b1o, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT1))
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V')
    s1a = w.s([w.s([one, w.inst('snidg')], 'ax-mp', '1 e. { 1 }')], 'a1i', '( %s -> 1 e. { 1 } )' % ph)
    bit0s = w.s([s1a, b0o], 'opelxpd', '( %s -> %s e. %s )' % (ph, BIT0, BITS))
    bit1s = w.s([s1a, b1o], 'opelxpd', '( %s -> %s e. %s )' % (ph, BIT1, BITS))
    cn = w.s([ll, w.inst('carriescl')], 'syl', '( %s -> %s e. NN0 )' % (ph, CAR))
    R1c = '( 1o repeatS %s )' % CAR
    r1w = w.s([b1o, cn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, R1c))
    rrw = w.s([ll, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, RR_))
    dec = w.s([ll, w.inst('bwcarriesdec1')], 'syl', '( %s -> L = ( %s ++ %s ) )' % (ph, R1c, RR_))
    ifl = closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS)
    ibl1 = w.s([dec], 'coeq2d', '( %s -> ( inclBool o. L ) = ( inclBool o. ( %s ++ %s ) ) )' % (ph, R1c, RR_))
    ibl2 = w.s([r1w, rrw, w.inst('bwmapccat')], 'syl2anc', '( %s -> ( inclBool o. ( %s ++ %s ) ) = ( %s ++ ( inclBool o. %s ) ) )' % (ph, R1c, RR_, WI, RR_))
    ibl = w.s([ibl1, ibl2], 'eqtrd', '( %s -> ( inclBool o. L ) = ( %s ++ ( inclBool o. %s ) ) )' % (ph, WI, RR_))
    wib = w.s([r1w, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WI, BITS))
    bs = closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS)
    wbss = closed(w, ph, 'tm2lwbss', '%s C_ %s' % (WB, WG))
    wig = w.s([wbss, wib], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, WI))
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    x4 = w.s([s4, xg, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    if pos:
        f0 = w.s([ll, case, w.inst('bwcarriesdec2')], 'syl2anc', '( %s -> ( %s ` 0 ) = (/) )' % (ph, RR_))
        hd = w.s([rrw, case, w.inst('wrdhdtl')], 'syl2anc', '( %s -> %s = ( <" ( %s ` 0 ) "> ++ %s ) )' % (ph, RR_, RR_, RP_))
        hd2 = w.s([hd, w.s([w.s([f0], 's1eqd', '( %s -> <" ( %s ` 0 ) "> = <" (/) "> )' % (ph, RR_))], 'oveq1d',
                           '( %s -> ( <" ( %s ` 0 ) "> ++ %s ) = ( <" (/) "> ++ %s ) )' % (ph, RR_, RP_, RP_))], 'eqtrd', '( %s -> %s = ( <" (/) "> ++ %s ) )' % (ph, RR_, RP_))
        rpw = w.s([rrw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, RP_))
        irr = w.s([w.s([hd2], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. ( <" (/) "> ++ %s ) ) )' % (ph, RR_, RP_)),
                   w.s([b0o, rpw, w.inst('bwmapcons')], 'syl2anc', '( %s -> ( inclBool o. ( <" (/) "> ++ %s ) ) = ( <" %s "> ++ ( inclBool o. %s ) ) )' % (ph, RP_, BIT0, RP_))],
                  'eqtrd', '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ ( inclBool o. %s ) ) )' % (ph, RR_, BIT0, RP_))
        IRP = '( inclBool o. %s )' % RP_
        irpg = w.s([rpw, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IRP))
        s0g = w.s([g0], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT0))
        l1 = w.s([ibl, w.s([irr], 'oveq2d', '( %s -> ( %s ++ ( inclBool o. %s ) ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WI, RR_, WI, BIT0, IRP))], 'eqtrd',
                 '( %s -> ( inclBool o. L ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WI, BIT0, IRP))
        l2 = w.s([l1], 'oveq1d', '( %s -> ( ( inclBool o. L ) ++ %s ) = ( ( %s ++ ( <" %s "> ++ %s ) ) ++ %s ) )' % (ph, YX4, WI, BIT0, IRP, YX4))
        a1 = w.s([wig, wg_(w, ph, '<" %s ">' % BIT0, IRP, s0g, irpg), x4, w.inst('ccatass')], 'syl3anc',
                 '( %s -> ( ( %s ++ ( <" %s "> ++ %s ) ) ++ %s ) = ( %s ++ ( ( <" %s "> ++ %s ) ++ %s ) ) )' % (ph, WI, BIT0, IRP, YX4, WI, BIT0, IRP, YX4))
        a2 = w.s([s0g, irpg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, BIT0, IRP, YX4, BIT0, XFP))
        a3 = w.s([a1, w.s([a2], 'oveq2d', '( %s -> ( %s ++ ( ( <" %s "> ++ %s ) ++ %s ) ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WI, BIT0, IRP, YX4, WI, BIT0, XFP))],
                 'eqtrd', '( %s -> ( ( %s ++ ( <" %s "> ++ %s ) ) ++ %s ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WI, BIT0, IRP, YX4, WI, BIT0, XFP))
        DK = w.s([dk, w.s([l2, a3], 'eqtrd', '( %s -> ( ( inclBool o. L ) ++ %s ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, YX4, WI, BIT0, XFP))], 'eqtrd',
                 '( %s -> ( D ` K ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WI, BIT0, XFP))
        Z, XF, Z0 = BIT0, XFP, Z0P
        xfg = wg_(w, ph, IRP, YX4, irpg, x4)
        zg = g0
    else:
        irr = w.s([w.s([case], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. (/) ) )' % (ph, RR_)), closed(w, ph, 'bwmap0', '( inclBool o. (/) ) = (/)')],
                  'eqtrd', '( %s -> ( inclBool o. %s ) = (/) )' % (ph, RR_))
        l1 = w.s([ibl, w.s([irr], 'oveq2d', '( %s -> ( %s ++ ( inclBool o. %s ) ) = ( %s ++ (/) ) )' % (ph, WI, RR_, WI))], 'eqtrd', '( %s -> ( inclBool o. L ) = ( %s ++ (/) ) )' % (ph, WI))
        l1b = w.s([l1, w.s([wig, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, WI, WI))], 'eqtrd', '( %s -> ( inclBool o. L ) = %s )' % (ph, WI))
        DK = w.s([dk, w.s([l1b], 'oveq1d', '( %s -> ( ( inclBool o. L ) ++ %s ) = ( %s ++ %s ) )' % (ph, YX4, WI, YX4))], 'eqtrd',
                 '( %s -> ( D ` K ) = ( %s ++ %s ) )' % (ph, WI, YX4))
        Z, XF, Z0 = '4', 'X', Z0T
        xfg = xg
        zg = g4
    # W = <. 1 , 1o >. repeatS c , a word over { <. 1 , 1o >. }
    rs = w.s([b1o, cn, ifl, w.inst('repsco')], 'syl3anc', '( %s -> %s = ( ( inclBool ` 1o ) repeatS %s ) )' % (ph, WI, CAR))
    ib1 = w.s([b1o, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = %s )' % (ph, BIT1))
    wrep = w.s([rs, w.s([ib1], 'oveq1d', '( %s -> ( ( inclBool ` 1o ) repeatS %s ) = ( %s repeatS %s ) )' % (ph, CAR, BIT1, CAR))], 'eqtrd',
               '( %s -> %s = ( %s repeatS %s ) )' % (ph, WI, BIT1, CAR))
    b1in = sn_in(w, ph, BIT1, w.s([], 'opex', '%s e. _V' % BIT1))
    b0in = sn_in(w, ph, BIT0, w.s([], 'opex', '%s e. _V' % BIT0))
    wb1 = w.s([wrep, w.s([b1in, cn, w.inst('repsw')], 'syl2anc', '( %s -> ( %s repeatS %s ) e. Word %s )' % (ph, BIT1, CAR, B1S))], 'eqeltrd',
              '( %s -> %s e. Word %s )' % (ph, WI, B1S))
    # interfaces
    NV_ = lambda r, z: NVA(r, z)
    p2 = '( %s /\\ ( r e. %s /\\ z e. %s ) )' % (ph, NPC, B1S)
    rin = w.s([], 'simprl', '( %s -> r e. %s )' % (p2, NPC))
    zin = w.s([], 'simprr', '( %s -> z e. %s )' % (p2, B1S))
    zeq = w.s([zin, w.inst('elsni')], 'syl', '( %s -> z = %s )' % (p2, BIT1))
    zz = w.s([zeq, w.s([bit1s], 'adantr', '( %s -> %s e. %s )' % (p2, BIT1, BITS))], 'eqeltrd', '( %s -> z e. %s )' % (p2, BITS))
    rr, fl, cm, ca = np_out(w, p2, 'r', rin)
    nv = rd_bit(w, p2, 'A', 'r', 'z', rr, zz)
    N2 = NV_('r', 'z')
    o2 = w.s([w.s([one, w.s([], '1oex', '1o e. _V'), w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = 1o' % BIT1)], 'a1i', '( %s -> ( 2nd ` %s ) = 1o )' % (p2, BIT1))
    z2 = w.s([w.s([zeq], 'fveq2d', '( %s -> ( 2nd ` z ) = ( 2nd ` %s ) )' % (p2, BIT1)), o2], 'eqtrd', '( %s -> ( 2nd ` z ) = 1o )' % p2)
    ra1 = w.s([nv['fields']['ra'], w.s([z2], 'fveq2d', '( %s -> ( inl ` ( 2nd ` z ) ) = ( inl ` 1o ) )' % p2)], 'eqtrd', '( %s -> ( TMra ` %s ) = ( inl ` 1o ) )' % (p2, N2))
    c1, _ = cra_val(w, p2, nv, N2, '1o', ra1)
    seq2 = w.s([seq], 'adantr', '( %s -> %s )' % (p2, SEQ))
    n2s = w.s([nv['mem'], seq2], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p2, N2))
    p0 = w.s([w.s([bit0s], 'adantr', '( %s -> %s e. %s )' % (p2, BIT0, BITS)), n2s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (p2, CB0, N2, BIT0))
    gz = w.s([w.s([bit0s], 'adantr', '( %s -> %s e. %s )' % (p2, BIT0, BITS)), zin, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` z ) = %s )' % (p2, GINC, BIT0))
    pg = w.s([p0, gz], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` z ) )' % (p2, CB0, N2, GINC))
    kp = np_keep(w, p2, nv, N2, fl, cm, ca)
    IA = w.s([w.s([c1, pg, kp], '3jca', '( %s -> ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = ( %s ` z ) /\\ %s e. %s ) )' % (p2, CRAEQ('1o'), N2, CB0, N2, GINC, N2, NPC))],
             'ralrimivva', '( %s -> A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = ( %s ` z ) /\\ %s e. %s ) )' % (ph, NPC, B1S, CRAEQ('1o'), N2, CB0, N2, GINC, N2, NPC))
    mvin = w.s([], 'tmcmvin', ST_MVIN)
    MV1 = ST_MVIN[2:].split(' /\\ A. r e. %s ( -. ' % NPC)[0]
    mv1 = w.s([mvin], 'simpli', MV1)
    mv2 = w.s([mvin], 'simpri', ST_MVIN[len('( ' + MV1 + ' /\\ '):-2])
    BODYZ = MV1.split(' A. z e. %s ' % BITS, 1)[1]
    b0ss = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V'), w.inst('snidg')], 'ax-mp', '1 e. { 1 }'),
                w.s([], '0el2o', '(/) e. 2o'), w.inst('opelxpi')], 'mp2an', '%s e. %s' % (BIT0, BITS))
    b0sub = w.s([b0ss, w.inst('snssi')], 'ax-mp', '%s C_ %s' % (B0, BITS))
    sr = w.s([b0sub, w.inst('ssralv')], 'ax-mp', '( A. z e. %s %s -> A. z e. %s %s )' % (BITS, BODYZ, B0, BODYZ))
    sr2 = w.s([sr], 'ralimi', '( A. r e. %s A. z e. %s %s -> A. r e. %s A. z e. %s %s )' % (NPC, BITS, BODYZ, NPC, B0, BODYZ))
    mvB = w.s([mv1, sr2], 'ax-mp', 'A. r e. %s A. z e. %s %s' % (NPC, B0, BODYZ))
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], leaf(IA): IA}
    for st in (mvB, mv2):
        a = w.s([st], 'a1i', '( %s -> %s )' % (ph, formula(w, st)))
        extra[leaf(a)] = a
    # the stop disjunction
    p3 = '( %s /\\ m e. %s )' % (ph, NPC)
    mm = w.s([], 'simpr', '( %s -> m e. %s )' % (p3, NPC))
    mr, mfl, mcm, mca = np_out(w, p3, 'm', mm)
    seq3 = w.s([seq], 'adantr', '( %s -> %s )' % (p3, SEQ))
    n01 = w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
    if pos:
        nv3 = rd_bit(w, p3, 'A', 'm', BIT0, mr, w.s([bit0s], 'adantr', '( %s -> %s e. %s )' % (p3, BIT0, BITS)))
        N3 = NV_('m', BIT0)
        o20 = w.s([w.s([one, w.s([], '0ex', '(/) e. _V'), w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = (/)' % BIT0)], 'a1i', '( %s -> ( 2nd ` %s ) = (/) )' % (p3, BIT0))
        ra0 = w.s([nv3['fields']['ra'], w.s([o20], 'fveq2d', '( %s -> ( inl ` ( 2nd ` %s ) ) = ( inl ` (/) ) )' % (p3, BIT0))], 'eqtrd', '( %s -> ( TMra ` %s ) = ( inl ` (/) ) )' % (p3, N3))
        inj = w.s([w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'), w.inst('tmcinl11')], 'mp2an', '( ( inl ` (/) ) = ( inl ` 1o ) <-> (/) = 1o )')
        ni = w.s([inj, n01], 'mtbir', '-. ( inl ` (/) ) = ( inl ` 1o )')
        dn = w.s([w.s([ra0], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = ( inl ` 1o ) <-> ( inl ` (/) ) = ( inl ` 1o ) ) )' % (p3, N3)),
                  w.s([ni], 'a1i', '( %s -> -. ( inl ` (/) ) = ( inl ` 1o ) )' % p3)], 'mtbird', '( %s -> -. ( TMra ` %s ) = ( inl ` 1o ) )' % (p3, N3))
        cA, _ = cra_val(w, p3, nv3, N3, '1o', dn)
        tA = not1o(w, p3, cA, CRAEQ('1o'), N3)
        tB, _ = cra_val(w, p3, nv3, N3, '(/)', ra0)
        n3s = w.s([nv3['mem'], seq3], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p3, N3))
        pb1 = w.s([w.s([bit1s], 'adantr', '( %s -> %s e. %s )' % (p3, BIT1, BITS)), n3s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (p3, CB1, N3, BIT1))
        kp3 = np_keep(w, p3, nv3, N3, mfl, mcm, mca)
        BODY = '( -. ( %s ` %s ) = 1o /\\ ( %s ` %s ) = 1o /\\ ( ( %s ` %s ) = %s /\\ %s e. %s ) )' % (CRAEQ('1o'), N3, CRAEQ('(/)'), N3, CB1, N3, BIT1, N3, NPC)
        bd = w.s([tA, tB, w.s([pb1, kp3], 'jca', '( %s -> ( ( %s ` %s ) = %s /\\ %s e. %s ) )' % (p3, CB1, N3, BIT1, N3, NPC))], '3jca', '( %s -> %s )' % (p3, BODY))
        ral = w.s([bd], 'ralrimiva', '( %s -> A. m e. %s %s )' % (ph, NPC, BODY))
        zq = w.s([], 'eqidd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, Z0, BIT1, XF))
        dj = w.s([ral, zq], 'jca', '( %s -> ( A. m e. %s %s /\\ %s = ( <" %s "> ++ %s ) ) )' % (ph, NPC, BODY, Z0, BIT1, XF))
        DISJ = cj(tsub(T_FINC[2][2], INC_MAP(True)))
        LEFT = formula(w, dj)[len('( %s -> ' % ph):-2]
        disj = w.s([dj], 'orcd', '( %s -> %s )' % (ph, DISJ))
    else:
        nv3 = rd_comma(w, p3, 'A', 'm', mr)
        N3 = NV_('m', '4')
        ran = nv3['fields']['ra']
        def nra(b):
            ne = w.s([w.s([], '0ex' if b == '(/)' else '1oex', '%s e. _V' % b), w.inst('tmcinlne')], 'ax-mp', '-. ( inl ` %s ) = ( inr ` (/) )' % b)
            ne2 = w.s([ne], 'eqcoms' if False else 'nesymi' if False else 'con2bii' if False else 'eqcom' if False else None, None) if False else None
            dn = w.s([w.s([ran], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = ( inl ` %s ) <-> ( inr ` (/) ) = ( inl ` %s ) ) )' % (p3, N3, b, b)),
                      w.s([w.s([ne, w.s([], 'eqcom', '( ( inr ` (/) ) = ( inl ` %s ) <-> ( inl ` %s ) = ( inr ` (/) ) )' % (b, b))], 'mtbir', '-. ( inr ` (/) ) = ( inl ` %s )' % b)],
                          'a1i', '( %s -> -. ( inr ` (/) ) = ( inl ` %s ) )' % (p3, b))], 'mtbird', '( %s -> -. ( TMra ` %s ) = ( inl ` %s ) )' % (p3, N3, b))
            cv, _ = cra_val(w, p3, nv3, N3, b, dn)
            return not1o(w, p3, cv, CRAEQ(b), N3)
        tA, tB = nra('1o'), nra('(/)')
        n3s = w.s([nv3['mem'], seq3], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p3, N3))
        pb1 = w.s([w.s([bit1s], 'adantr', '( %s -> %s e. %s )' % (p3, BIT1, BITS)), n3s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (p3, CB1, N3, BIT1))
        p4 = w.s([closed(w, p3, '4re', '4 e. RR'), n3s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = 4 )' % (p3, C4S, N3))
        kp3 = np_keep(w, p3, nv3, N3, mfl, mcm, mca)
        BODY = ('( ( -. ( %s ` %s ) = 1o /\\ -. ( %s ` %s ) = 1o ) /\\ ( ( ( %s ` %s ) = %s /\\ ( %s ` %s ) = 4 ) /\\ %s e. %s ) )'
                % (CRAEQ('1o'), N3, CRAEQ('(/)'), N3, CB1, N3, BIT1, C4S, N3, N3, NPC))
        bd = w.s([w.s([tA, tB], 'jca', '( %s -> %s )' % (p3, cj(parse_conj(BODY)[0]))),
                  w.s([w.s([pb1, p4], 'jca', '( %s -> ( ( %s ` %s ) = %s /\\ ( %s ` %s ) = 4 ) )' % (p3, CB1, N3, BIT1, C4S, N3)), kp3], 'jca',
                      '( %s -> %s )' % (p3, cj(parse_conj(BODY)[1])))], 'jca', '( %s -> %s )' % (p3, BODY))
        ral = w.s([bd], 'ralrimiva', '( %s -> A. m e. %s %s )' % (ph, NPC, BODY))
        zq = w.s([], 'eqidd', '( %s -> %s = ( <" %s "> ++ ( <" 4 "> ++ X ) ) )' % (ph, Z0, BIT1))
        dj = w.s([ral, zq], 'jca', '( %s -> ( A. m e. %s %s /\\ %s = ( <" %s "> ++ ( <" 4 "> ++ X ) ) ) )' % (ph, NPC, BODY, Z0, BIT1))
        DISJ = cj(tsub(T_FINC[2][2], INC_MAP(False)))
        disj = w.s([dj], 'olcd', '( %s -> %s )' % (ph, DISJ))
    extra[DISJ] = disj
    # typings and letters
    craty = lambda b: lamty(w, ph, mk, CRAEQ(b), lambda t: 'if ( ( TMra ` %s ) = ( inl ` %s ) , 1o , (/) )' % (t, b), '2o', w.s([], '2oex', '2o e. _V'),
                               w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', 'if ( ( TMra ` u ) = ( inl ` %s ) , 1o , (/) ) e. 2o' % b))
    extra[CTY(CRAEQ('1o'))] = craty('1o')
    extra[CTY(CRAEQ('(/)'))] = craty('(/)')
    extra[CTY(CIS)] = cis_ty(w, ph, mk)
    for k in ['K', 'J']:
        extra['%s e. %s' % (k, DG)] = mk['k'][k]['kd']
        extra[RTY('TMrdA', k)] = mk['k'][k]['hdl']['TMrdA']
    b0J = letgk(w, ph, mk, BIT0, 'J', g0)
    b0K = letgk(w, ph, mk, BIT0, 'K', g0)
    b1K = letgk(w, ph, mk, BIT1, 'K', g1)
    g4K = letgk(w, ph, mk, '4', 'K', g4)
    extra[PTY(CB0, 'J')] = constfty(w, ph, BIT0, GX('J'), b0J)
    extra[PTY(CB1, 'K')] = constfty(w, ph, BIT1, GX('K'), b1K)
    extra[PTY(C4S, 'K')] = constfty(w, ph, '4', GX('K'), g4K)
    extra[PTY(PBR, 'K')] = pbr_ty(w, ph, mk, 'K')
    extra['%s C_ %s' % (B1S, GX('K'))] = w.s([b1K], 'snssd', '( %s -> %s C_ %s )' % (ph, B1S, GX('K')))
    extra['%s C_ %s' % (B0, GX('K'))] = w.s([b0K], 'snssd', '( %s -> %s C_ %s )' % (ph, B0, GX('K')))
    extra['%s C_ %s' % (B0, GX('J'))] = w.s([b0J], 'snssd', '( %s -> %s C_ %s )' % (ph, B0, GX('J')))
    extra['%s : %s --> %s' % (GINC, B1S, B0)] = closed(w, ph, 'fconst', '%s : %s --> %s' % (GINC, B1S, B0))
    extra['4 e. %s' % GX('J')] = letgk(w, ph, mk, '4', 'J', g4)
    extra['%s e. %s' % (Z, GX('K'))] = letgk(w, ph, mk, Z, 'K', zg)
    extra['%s e. %s' % (BIT1, GX('K'))] = b1K
    extra['4 e. %s' % GX('K')] = g4K
    extra[WRD(WI, B1S)] = wb1
    extra[WRD(XF, GX('K'))] = togk(w, ph, mk, XF, 'K', xfg)
    extra['( D ` K ) = ( %s ++ ( <" %s "> ++ %s ) )' % (WI, Z, XF)] = DK
    nss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPC))
    extra['%s C_ ( 2nd ` T )' % NPC] = w.s([nss, seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPC))
    bld = Builder(w, ph, c, extra)
    M_ = INC_MAP(pos)
    ante, concl = split_imp(stmt('tm2fincr'))
    st = bld(tsub(parse_conj(ante), M_))
    c2 = tsub_text(concl, M_)
    tri = w.s([st, w.inst('tm2fincr')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1, n1 = triple_parts(c2)
    # the result word
    gw1 = w.s([wrep], 'coeq2d', '( %s -> ( %s o. %s ) = ( %s o. ( %s repeatS %s ) ) )' % (ph, GINC, WI, GINC, BIT1, CAR))
    gw2 = w.s([b1in, cn, extra['%s : %s --> %s' % (GINC, B1S, B0)], w.inst('repsco')], 'syl3anc',
              '( %s -> ( %s o. ( %s repeatS %s ) ) = ( ( %s ` %s ) repeatS %s ) )' % (ph, GINC, BIT1, CAR, GINC, BIT1, CAR))
    gv = w.s([bit0s, b1in, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, GINC, BIT1, BIT0))
    REP0 = '( %s repeatS %s )' % (BIT0, CAR)
    gw = w.s([w.s([gw1, gw2], 'eqtrd', '( %s -> ( %s o. %s ) = ( ( %s ` %s ) repeatS %s ) )' % (ph, GINC, WI, GINC, BIT1, CAR)),
              w.s([gv], 'oveq1d', '( %s -> ( ( %s ` %s ) repeatS %s ) = %s )' % (ph, GINC, BIT1, CAR, REP0))], 'eqtrd', '( %s -> ( %s o. %s ) = %s )' % (ph, GINC, WI, REP0))
    R0c = '( (/) repeatS %s )' % CAR
    r0w = w.s([b0o, cn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, R0c))
    i0 = w.s([w.s([b0o, cn, ifl, w.inst('repsco')], 'syl3anc', '( %s -> ( inclBool o. %s ) = ( ( inclBool ` (/) ) repeatS %s ) )' % (ph, R0c, CAR)),
              w.s([w.s([b0o, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ph, BIT0))], 'oveq1d',
                  '( %s -> ( ( inclBool ` (/) ) repeatS %s ) = %s )' % (ph, CAR, REP0))], 'eqtrd', '( %s -> ( inclBool o. %s ) = %s )' % (ph, R0c, REP0))
    ib1s = w.s([w.s([b1o, w.s([ifl], 'a1i', '( %s -> inclBool : 2o --> %s )' % (ph, BITS)) if False else ifl, w.inst('s1co')], 'syl2anc',
                    '( %s -> ( inclBool o. <" 1o "> ) = <" ( inclBool ` 1o ) "> )' % ph), w.s([ib1], 's1eqd', '( %s -> <" ( inclBool ` 1o ) "> = <" %s "> )' % (ph, BIT1))],
               'eqtrd', '( %s -> ( inclBool o. <" 1o "> ) = <" %s "> )' % (ph, BIT1))
    tinc = w.s([w.s([rrw, cn], 'jca', '( %s -> ( %s e. Word 2o /\\ %s e. NN0 ) )' % (ph, RR_, CAR)), w.inst('tmcinc1')], 'syl',
               '( %s -> ( incBits ` ( %s ++ %s ) ) = ( %s ++ ( incBits ` %s ) ) )' % (ph, R1c, RR_, R0c, RR_))
    ie = w.s([w.s([dec], 'fveq2d', '( %s -> ( incBits ` L ) = ( incBits ` ( %s ++ %s ) ) )' % (ph, R1c, RR_)), tinc], 'eqtrd',
             '( %s -> ( incBits ` L ) = ( %s ++ ( incBits ` %s ) ) )' % (ph, R0c, RR_))
    s1b = w.s([b1o], 's1cld', '( %s -> <" 1o "> e. Word 2o )' % ph)
    s1g = w.s([g1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT1))
    rep0g = w.s([r0w, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, R0c))
    rep0g2 = w.s([i0, rep0g], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ph, REP0))
    if pos:
        ir = w.s([w.s([hd2], 'fveq2d', '( %s -> ( incBits ` %s ) = ( incBits ` ( <" (/) "> ++ %s ) ) )' % (ph, RR_, RP_)),
                  w.s([rpw, w.inst('incbitscons0')], 'syl', '( %s -> ( incBits ` ( <" (/) "> ++ %s ) ) = ( <" 1o "> ++ %s ) )' % (ph, RP_, RP_))], 'eqtrd',
                 '( %s -> ( incBits ` %s ) = ( <" 1o "> ++ %s ) )' % (ph, RR_, RP_))
        TAIL = '( <" 1o "> ++ %s )' % RP_
        tw = w.s([s1b, rpw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, TAIL))
        tmap = w.s([b1o, rpw, w.inst('bwmapcons')], 'syl2anc', '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ ( inclBool o. %s ) ) )' % (ph, TAIL, BIT1, RP_))
        TM = '( <" %s "> ++ %s )' % (BIT1, IRP)
        tmg = wg_(w, ph, '<" %s ">' % BIT1, IRP, s1g, irpg)
    else:
        ir = w.s([w.s([case], 'fveq2d', '( %s -> ( incBits ` %s ) = ( incBits ` (/) ) )' % (ph, RR_)), closed(w, ph, 'incbitsnil', '( incBits ` (/) ) = <" 1o ">')],
                 'eqtrd', '( %s -> ( incBits ` %s ) = <" 1o "> )' % (ph, RR_))
        TAIL = '<" 1o ">'
        tw = s1b
        tmap = ib1s
        TM = '<" %s ">' % BIT1
        tmg = s1g
    ie2 = w.s([ie, w.s([ir], 'oveq2d', '( %s -> ( %s ++ ( incBits ` %s ) ) = ( %s ++ %s ) )' % (ph, R0c, RR_, R0c, TAIL))], 'eqtrd',
              '( %s -> ( incBits ` L ) = ( %s ++ %s ) )' % (ph, R0c, TAIL))
    im = w.s([w.s([ie2], 'coeq2d', '( %s -> ( inclBool o. ( incBits ` L ) ) = ( inclBool o. ( %s ++ %s ) ) )' % (ph, R0c, TAIL)),
              w.s([r0w, tw, w.inst('bwmapccat')], 'syl2anc', '( %s -> ( inclBool o. ( %s ++ %s ) ) = ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) )' % (ph, R0c, TAIL, R0c, TAIL))],
             'eqtrd', '( %s -> ( inclBool o. ( incBits ` L ) ) = ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) )' % (ph, R0c, TAIL))
    im2 = w.s([im, w.s([i0, tmap], 'oveq12d', '( %s -> ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) = ( %s ++ %s ) )' % (ph, R0c, TAIL, REP0, TM))], 'eqtrd',
              '( %s -> ( inclBool o. ( incBits ` L ) ) = ( %s ++ %s ) )' % (ph, REP0, TM))
    im3 = w.s([im2], 'oveq1d', '( %s -> ( ( inclBool o. ( incBits ` L ) ) ++ %s ) = ( ( %s ++ %s ) ++ %s ) )' % (ph, YX4, REP0, TM, YX4))
    as1 = w.s([rep0g2, tmg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (ph, REP0, TM, YX4, REP0, TM, YX4))
    if pos:
        as2 = w.s([s1g, irpg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ %s ) = %s )' % (ph, TM, YX4, Z0P))
    else:
        as2 = w.s([], 'eqidd', '( %s -> ( %s ++ %s ) = %s )' % (ph, TM, YX4, Z0T))
    as3 = w.s([as1, w.s([as2], 'oveq2d', '( %s -> ( %s ++ ( %s ++ %s ) ) = ( %s ++ %s ) )' % (ph, REP0, TM, YX4, REP0, Z0))], 'eqtrd',
              '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ %s ) )' % (ph, REP0, TM, YX4, REP0, Z0))
    fin = w.s([w.s([im3, as3], 'eqtrd', '( %s -> ( ( inclBool o. ( incBits ` L ) ) ++ %s ) = ( %s ++ %s ) )' % (ph, YX4, REP0, Z0)),
               w.s([gw], 'oveq1d', '( %s -> ( ( %s o. %s ) ++ %s ) = ( %s ++ %s ) )' % (ph, GINC, WI, Z0, REP0, Z0))], 'eqtr4d',
              '( %s -> ( ( inclBool o. ( incBits ` L ) ) ++ %s ) = ( ( %s o. %s ) ++ %s ) )' % (ph, YX4, GINC, WI, Z0))
    OLDV = '( ( %s o. %s ) ++ %s )' % (GINC, WI, Z0)
    NEWV = CC("( inclBool o. ( incBits ` L ) )", YX4)
    ue = upeq(w, ph, 'D', 'K', w.s([fin], 'eqcomd', '( %s -> %s = %s )' % (ph, OLDV, NEWV)), OLDV, NEWV)
    deq = clneq(w, ph, 'E', NPC, ue, UP('D', 'K', OLDV), UP('D', 'K', NEWV))
    t2, C2, D2, n2 = hrrw(w, ph, tri, C1, D1, n1, deq=deq)
    # the bound: |W| = carries <_ |L|
    wl = w.s([r1w, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, WI, R1c))
    rl = w.s([closed(w, ph, '1oex', '1o e. _V'), cn, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, R1c, CAR))
    cle = w.s([ll, w.inst('carriesle')], 'syl', '( %s -> %s <_ ( # ` L ) )' % (ph, CAR))
    lw0 = w.s([wib, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, WI))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    leaves = {'( # ` %s )' % WI: lw0, '( # ` %s )' % R1c: w.s([r1w, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, R1c)), CAR: cn, '( # ` L )': la}
    bound(w, ph, mk['phm'], t2, C2, D2, n2, '( ( 2 x. ( # ` L ) ) + 3 )', leaves, hyps=[wl, rl, cle], qed=True)
    return w.run()


def wg_(w, ph, A, B, a, b):
    return w.s([a, b, w.inst('ccatcl')], 'syl2anc', "( %s -> ( %s ++ %s ) e. Word Gamma' )" % (ph, A, B))


def tmcincp():
    return inccase(True)


def tmcinct():
    return inccase(False)


def tmcincr():
    lab = 'tmcincr'
    ph = cj(TREE_INC)
    w = W(lab, '` incr y s ` at the machine (Lean ` incr_runs ` ): the top number of ` y ` is incremented in place; '
               '` flag ` , ` cmp ` , ` carry ` are preserved; in ` 2 |l| + 3 ` steps.  The join of ~ tmcincp and ~ tmcinct .')
    RN = '%s = (/)' % RR_
    p = w.s([], 'tmcincp', '( ( %s /\\ %s =/= (/) ) -> %s )' % (ph, RR_, CONCL_INC))
    t = w.s([], 'tmcinct', '( ( %s /\\ %s ) -> %s )' % (ph, RN, CONCL_INC))
    pn = '( %s /\\ -. %s )' % (ph, RN)
    ne = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (pn, RN))], 'neqned', '( %s -> %s =/= (/) )' % (pn, RR_))
    p2 = w.s([w.s([], 'simpl', '( %s -> %s )' % (pn, ph)), ne, p], 'syl2anc', '( %s -> %s )' % (pn, CONCL_INC))
    w.qed([t, p2], 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_INC))
    return w.run()


if __name__ == '__main__':
    for l in ['tmcinc1', 'tmcincp', 'tmcinct', 'tmcincr']:
        if want(l) and l in globals(): globals()[l]()
