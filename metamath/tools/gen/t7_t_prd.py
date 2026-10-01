"""T7: ` predNum x s ` at the machine (Lean ` predNum_runs ` ): the decrement
of a run of zeros (T4 ~ predbitscons0 by induction), the three cases on what
follows the run as instances of ~ tm2fprdn , and their join.

    MM_DB=sorties/t7.mm python3 tools/gen/t7_t_prd.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7prd import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty, ral_S
from t7_l_addx import flty
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def S_(l):
    return dict(STMTS7)[l]


def split_or3(text):
    toks = text.split()
    d = 0; cuts = []
    for i, t in enumerate(toks[1:-1], 1):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        elif t == '\\/' and d == 0:
            cuts.append(i)
    assert len(cuts) == 2, text[:200]
    a, b = cuts
    return ' '.join(toks[1:a]), ' '.join(toks[a + 1:b]), ' '.join(toks[b + 1:-1])


def wg_(w, ph, A, B, a, b):
    return w.s([a, b, w.inst('ccatcl')], 'syl2anc', "( %s -> ( %s ++ %s ) e. Word Gamma' )" % (ph, A, B))


def sn_in(w, ph, A, aex):
    return w.s([w.s([aex, w.inst('snidg')], 'ax-mp', '%s e. { %s }' % (A, A))], 'a1i', '( %s -> %s e. { %s } )' % (ph, A, A))


def tmcprdi():
    lab = 'tmcprdi'
    w = W(lab, 'Decrementing a run of zeros followed by a word turns the run into ones and decrements the word '
               '(Lean ` predBits ` on ` false :: l ` , iterated).')
    PS = lambda x: '( predBits ` ( ( (/) repeatS %s ) ++ M ) ) = ( ( 1o repeatS %s ) ++ ( predBits ` M ) )' % (x, x)
    hyps = []
    for x in ['0', 'y', '( y + 1 )', 'C']:
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (x, x))
        cg, new = w.wcongr(PS('x'), {'x': x}, 'x = %s' % x, {'x': idx})
        hyps.append(cg)
    ph = 'M e. Word 2o'
    z = w.s([], '0ex', '(/) e. _V'); o = w.s([], '1oex', '1o e. _V')
    r1 = w.s([o, w.inst('repsw0')], 'ax-mp', '( 1o repeatS 0 ) = (/)')
    r0 = w.s([z, w.inst('repsw0')], 'ax-mp', '( (/) repeatS 0 ) = (/)')
    mm = w.s([], 'id', '( %s -> M e. Word 2o )' % ph)
    b1 = w.s([w.s([r0], 'oveq1i', '( ( (/) repeatS 0 ) ++ M ) = ( (/) ++ M )'), w.s([mm, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ M ) = M )' % ph)], 'eqtrid',
             '( %s -> ( ( (/) repeatS 0 ) ++ M ) = M )' % ph)
    b2 = w.s([b1], 'fveq2d', '( %s -> ( predBits ` ( ( (/) repeatS 0 ) ++ M ) ) = ( predBits ` M ) )' % ph)
    ib = w.s([mm, w.inst('predbitscl')], 'syl', '( %s -> ( predBits ` M ) e. Word 2o )' % ph)
    b3 = w.s([w.s([r1], 'oveq1i', '( ( 1o repeatS 0 ) ++ ( predBits ` M ) ) = ( (/) ++ ( predBits ` M ) )'),
              w.s([ib, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( predBits ` M ) ) = ( predBits ` M ) )' % ph)], 'eqtrid',
             '( %s -> ( ( 1o repeatS 0 ) ++ ( predBits ` M ) ) = ( predBits ` M ) )' % ph)
    base = w.s([b2, b3], 'eqtr4d', '( %s -> %s )' % (ph, PS('0')))
    ps = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (ph, PS('y'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (ps, PS('y')))
    yn = w.s([], 'simplr', '( %s -> y e. NN0 )' % ps)
    mw = w.s([], 'simpll', '( %s -> M e. Word 2o )' % ps)
    def rep1(S, sv):
        one = closed(w, ps, '1nn0', '1 e. NN0')
        svp = w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ps, S))
        rc = w.s([svp, one, yn, w.inst('repswccat')], 'syl3anc', '( %s -> ( ( %s repeatS 1 ) ++ ( %s repeatS y ) ) = ( %s repeatS ( 1 + y ) ) )' % (ps, S, S, S))
        r1_ = w.s([svp, w.inst('repsw1')], 'syl', '( %s -> ( %s repeatS 1 ) = <" %s "> )' % (ps, S, S))
        r1b = w.s([r1_], 'oveq1d', '( %s -> ( ( %s repeatS 1 ) ++ ( %s repeatS y ) ) = ( <" %s "> ++ ( %s repeatS y ) ) )' % (ps, S, S, S, S))
        ic = w.s([w.s([yn], 'nn0cnd', '( %s -> y e. CC )' % ps), closed(w, ps, 'ax-1cn', '1 e. CC')], 'addcomd', '( %s -> ( y + 1 ) = ( 1 + y ) )' % ps)
        rr = w.s([ic], 'oveq2d', '( %s -> ( %s repeatS ( y + 1 ) ) = ( %s repeatS ( 1 + y ) ) )' % (ps, S, S))
        return w.s([rr, w.s([rc, r1b], 'eqtr3d', '( %s -> ( %s repeatS ( 1 + y ) ) = ( <" %s "> ++ ( %s repeatS y ) ) )' % (ps, S, S, S))], 'eqtrd',
                   '( %s -> ( %s repeatS ( y + 1 ) ) = ( <" %s "> ++ ( %s repeatS y ) ) )' % (ps, S, S, S))
    e0 = rep1('(/)', z)
    e1 = rep1('1o', o)
    b1o = closed(w, ps, '1oel2o', '1o e. 2o'); b0o = closed(w, ps, '0el2o', '(/) e. 2o')
    R0 = '( (/) repeatS y )'; R1 = '( 1o repeatS y )'
    r0w = w.s([b0o, yn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, R0))
    r1w = w.s([b1o, yn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, R1))
    s0 = w.s([b0o], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ps)
    s1 = w.s([b1o], 's1cld', '( %s -> <" 1o "> e. Word 2o )' % ps)
    a1 = w.s([e0], 'oveq1d', '( %s -> ( ( (/) repeatS ( y + 1 ) ) ++ M ) = ( ( <" (/) "> ++ %s ) ++ M ) )' % (ps, R0))
    a2 = w.s([s0, r0w, mw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" (/) "> ++ %s ) ++ M ) = ( <" (/) "> ++ ( %s ++ M ) ) )' % (ps, R0, R0))
    a3 = w.s([w.s([a1, a2], 'eqtrd', '( %s -> ( ( (/) repeatS ( y + 1 ) ) ++ M ) = ( <" (/) "> ++ ( %s ++ M ) ) )' % (ps, R0))], 'fveq2d',
             '( %s -> ( predBits ` ( ( (/) repeatS ( y + 1 ) ) ++ M ) ) = ( predBits ` ( <" (/) "> ++ ( %s ++ M ) ) ) )' % (ps, R0))
    rm = w.s([r0w, mw, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ M ) e. Word 2o )' % (ps, R0))
    a4 = w.s([rm, w.inst('predbitscons0')], 'syl', '( %s -> ( predBits ` ( <" (/) "> ++ ( %s ++ M ) ) ) = ( <" 1o "> ++ ( predBits ` ( %s ++ M ) ) ) )' % (ps, R0, R0))
    a5 = w.s([ih], 'oveq2d', '( %s -> ( <" 1o "> ++ ( predBits ` ( %s ++ M ) ) ) = ( <" 1o "> ++ ( %s ++ ( predBits ` M ) ) ) )' % (ps, R0, R1))
    pbw = w.s([mw, w.inst('predbitscl')], 'syl', '( %s -> ( predBits ` M ) e. Word 2o )' % ps)
    a6 = w.s([s1, r1w, pbw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 1o "> ++ %s ) ++ ( predBits ` M ) ) = ( <" 1o "> ++ ( %s ++ ( predBits ` M ) ) ) )' % (ps, R1, R1))
    a7 = w.s([e1], 'oveq1d', '( %s -> ( ( 1o repeatS ( y + 1 ) ) ++ ( predBits ` M ) ) = ( ( <" 1o "> ++ %s ) ++ ( predBits ` M ) ) )' % (ps, R1))
    rhs = w.s([a7, a6], 'eqtrd', '( %s -> ( ( 1o repeatS ( y + 1 ) ) ++ ( predBits ` M ) ) = ( <" 1o "> ++ ( %s ++ ( predBits ` M ) ) ) )' % (ps, R1))
    lhs = w.s([w.s([a3, a4], 'eqtrd', '( %s -> ( predBits ` ( ( (/) repeatS ( y + 1 ) ) ++ M ) ) = ( <" 1o "> ++ ( predBits ` ( %s ++ M ) ) ) )' % (ps, R0)), a5], 'eqtrd',
              '( %s -> ( predBits ` ( ( (/) repeatS ( y + 1 ) ) ++ M ) ) = ( <" 1o "> ++ ( %s ++ ( predBits ` M ) ) ) )' % (ps, R1))
    step = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (ps, PS('( y + 1 )')))
    w.qed(hyps + [base, step], 'nn0indd', S_('tmcprdi'))
    return w.run()


def prdcase(k):
    lab = 'tmcprd%d' % k
    CASE = PRD_CASES[k]
    tree = (TREE_PRD, CASE)
    ph = cj(tree)
    desc = ['the word is all zeros (the run meets the terminator)', 'the run is followed by the top bit only',
            'the run is followed by a one bit and more bits'][k]
    w = W(lab, '` predNum x s ` at the machine, %s: ~ tm2fprdn with ` readA ` , the tests ` ra = some false ` , '
               '` ra = some true ` , the peek ` readEnd ` and its test ` db ` , the constant pushes, the mover\'s '
               'handlers; the run of zeros is ` borrows ` (T4 ~ bwborrowsdec ).' % desc)
    c = Ctx(w, ph, tree)
    mk = machine(w, ph, c, ['K', 'J'])
    seq = mk['seq']
    ll, xg, dd = c[WRD('L', '2o')], c[WRD('X', GAM)], c[STKD('D')]
    dk = c[DATA_CAN[1]]
    M_ = PRD_MAP(k)
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    b0o = closed(w, ph, '0el2o', '(/) e. 2o'); b1o = closed(w, ph, '1oel2o', '1o e. 2o')
    g0 = w.s([b0o, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT0))
    g1 = w.s([b1o, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT1))
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V')
    s1a = w.s([w.s([one, w.inst('snidg')], 'ax-mp', '1 e. { 1 }')], 'a1i', '( %s -> 1 e. { 1 } )' % ph)
    bit0s = w.s([s1a, b0o], 'opelxpd', '( %s -> %s e. %s )' % (ph, BIT0, BITS))
    bit1s = w.s([s1a, b1o], 'opelxpd', '( %s -> %s e. %s )' % (ph, BIT1, BITS))
    bn = w.s([ll, w.inst('borrowscl')], 'syl', '( %s -> %s e. NN0 )' % (ph, BOR))
    R0c = '( (/) repeatS %s )' % BOR
    R1c = '( 1o repeatS %s )' % BOR
    r0w = w.s([b0o, bn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, R0c))
    r1w = w.s([b1o, bn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, R1c))
    rrw = w.s([ll, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, RRB))
    dec = w.s([ll, w.inst('bwborrowsdec1')], 'syl', '( %s -> L = ( %s ++ %s ) )' % (ph, R0c, RRB))
    ifl = closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS)
    ibl = w.s([w.s([dec], 'coeq2d', '( %s -> ( inclBool o. L ) = ( inclBool o. ( %s ++ %s ) ) )' % (ph, R0c, RRB)),
               w.s([r0w, rrw, w.inst('bwmapccat')], 'syl2anc', '( %s -> ( inclBool o. ( %s ++ %s ) ) = ( %s ++ ( inclBool o. %s ) ) )' % (ph, R0c, RRB, WB0, RRB))],
              'eqtrd', '( %s -> ( inclBool o. L ) = ( %s ++ ( inclBool o. %s ) ) )' % (ph, WB0, RRB))
    wib = w.s([r0w, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WB0, BITS))
    wbss = closed(w, ph, 'tm2lwbss', '%s C_ %s' % (WB, WG))
    wig = w.s([wbss, wib], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, WB0))
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    x4 = w.s([s4, xg, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    s1g = w.s([g1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT1))
    s0g = w.s([g0], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT0))
    cz = c[CASE] if k == 0 else c[CASE[0]]
    # the decomposition of the stack and the value of predBits
    if k == 0:
        irr = w.s([w.s([cz], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. (/) ) )' % (ph, RRB)), closed(w, ph, 'bwmap0', '( inclBool o. (/) ) = (/)')],
                  'eqtrd', '( %s -> ( inclBool o. %s ) = (/) )' % (ph, RRB))
        l1 = w.s([w.s([ibl, w.s([irr], 'oveq2d', '( %s -> ( %s ++ ( inclBool o. %s ) ) = ( %s ++ (/) ) )' % (ph, WB0, RRB, WB0))], 'eqtrd', '( %s -> ( inclBool o. L ) = ( %s ++ (/) ) )' % (ph, WB0)),
                  w.s([wig, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, WB0, WB0))], 'eqtrd', '( %s -> ( inclBool o. L ) = %s )' % (ph, WB0))
        DK = w.s([dk, w.s([l1], 'oveq1d', '( %s -> ( ( inclBool o. L ) ++ %s ) = ( %s ++ %s ) )' % (ph, YX4, WB0, YX4))], 'eqtrd', '( %s -> ( D ` K ) = ( %s ++ %s ) )' % (ph, WB0, YX4))
        pr = w.s([w.s([cz], 'fveq2d', '( %s -> ( predBits ` %s ) = ( predBits ` (/) ) )' % (ph, RRB)), closed(w, ph, 'predbitsnil', '( predBits ` (/) ) = (/)')],
                 'eqtrd', '( %s -> ( predBits ` %s ) = (/) )' % (ph, RRB))
        TAILW, TAILG, tailw, tailg = '(/)', '(/)', closed(w, ph, 'wrd0', '(/) e. Word 2o'), None
        ZX = YX4
    else:
        cp = c[CASE[1]]
        f0 = w.s([ll, cz, w.inst('bwborrowsdec2')], 'syl2anc', '( %s -> ( %s ` 0 ) = 1o )' % (ph, RRB))
        hd = w.s([rrw, cz, w.inst('wrdhdtl')], 'syl2anc', '( %s -> %s = ( <" ( %s ` 0 ) "> ++ %s ) )' % (ph, RRB, RRB, RPB))
        hd2 = w.s([hd, w.s([w.s([f0], 's1eqd', '( %s -> <" ( %s ` 0 ) "> = <" 1o "> )' % (ph, RRB))], 'oveq1d',
                           '( %s -> ( <" ( %s ` 0 ) "> ++ %s ) = ( <" 1o "> ++ %s ) )' % (ph, RRB, RPB, RPB))], 'eqtrd', '( %s -> %s = ( <" 1o "> ++ %s ) )' % (ph, RRB, RPB))
        rpw = w.s([rrw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, RPB))
        IRP = '( inclBool o. %s )' % RPB
        irr = w.s([w.s([hd2], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. ( <" 1o "> ++ %s ) ) )' % (ph, RRB, RPB)),
                   w.s([b1o, rpw, w.inst('bwmapcons')], 'syl2anc', '( %s -> ( inclBool o. ( <" 1o "> ++ %s ) ) = ( <" %s "> ++ %s ) )' % (ph, RPB, BIT1, IRP))],
                  'eqtrd', '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ %s ) )' % (ph, RRB, BIT1, IRP))
        irpg = w.s([rpw, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IRP))
        l1 = w.s([ibl, w.s([irr], 'oveq2d', '( %s -> ( %s ++ ( inclBool o. %s ) ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, RRB, WB0, BIT1, IRP))], 'eqtrd',
                 '( %s -> ( inclBool o. L ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, BIT1, IRP))
        l2 = w.s([l1], 'oveq1d', '( %s -> ( ( inclBool o. L ) ++ %s ) = ( ( %s ++ ( <" %s "> ++ %s ) ) ++ %s ) )' % (ph, YX4, WB0, BIT1, IRP, YX4))
        a1 = w.s([wig, wg_(w, ph, '<" %s ">' % BIT1, IRP, s1g, irpg), x4, w.inst('ccatass')], 'syl3anc',
                 '( %s -> ( ( %s ++ ( <" %s "> ++ %s ) ) ++ %s ) = ( %s ++ ( ( <" %s "> ++ %s ) ++ %s ) ) )' % (ph, WB0, BIT1, IRP, YX4, WB0, BIT1, IRP, YX4))
        a2 = w.s([s1g, irpg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, BIT1, IRP, YX4, BIT1, XP2))
        a3 = w.s([a1, w.s([a2], 'oveq2d', '( %s -> ( %s ++ ( ( <" %s "> ++ %s ) ++ %s ) ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, BIT1, IRP, YX4, WB0, BIT1, XP2))],
                 'eqtrd', '( %s -> ( ( %s ++ ( <" %s "> ++ %s ) ) ++ %s ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, BIT1, IRP, YX4, WB0, BIT1, XP2))
        DK0 = w.s([dk, w.s([l2, a3], 'eqtrd', '( %s -> ( ( inclBool o. L ) ++ %s ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, YX4, WB0, BIT1, XP2))], 'eqtrd',
                  '( %s -> ( D ` K ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, BIT1, XP2))
        if k == 1:
            irp0 = w.s([w.s([cp], 'coeq2d', '( %s -> %s = ( inclBool o. (/) ) )' % (ph, IRP)), closed(w, ph, 'bwmap0', '( inclBool o. (/) ) = (/)')],
                       'eqtrd', '( %s -> %s = (/) )' % (ph, IRP))
            xp0 = w.s([w.s([irp0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ph, XP2, YX4)), w.s([x4, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, YX4, YX4))],
                      'eqtrd', '( %s -> %s = %s )' % (ph, XP2, YX4))
            DK = w.s([DK0, w.s([w.s([xp0], 'oveq2d', '( %s -> ( <" %s "> ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, BIT1, XP2, BIT1, YX4))], 'oveq2d',
                               '( %s -> ( %s ++ ( <" %s "> ++ %s ) ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, BIT1, XP2, WB0, BIT1, YX4))], 'eqtrd',
                     '( %s -> ( D ` K ) = ( %s ++ ( <" %s "> ++ %s ) ) )' % (ph, WB0, BIT1, YX4))
            rr1 = w.s([hd2, w.s([cp], 'oveq2d', '( %s -> ( <" 1o "> ++ %s ) = ( <" 1o "> ++ (/) ) )' % (ph, RPB))], 'eqtrd', '( %s -> %s = ( <" 1o "> ++ (/) ) )' % (ph, RRB))
            rr2 = w.s([rr1, w.s([w.s([b1o], 's1cld', '( %s -> <" 1o "> e. Word 2o )' % ph), w.inst('ccatrid')], 'syl', '( %s -> ( <" 1o "> ++ (/) ) = <" 1o "> )' % ph)],
                      'eqtrd', '( %s -> %s = <" 1o "> )' % (ph, RRB))
            pr = w.s([w.s([rr2], 'fveq2d', '( %s -> ( predBits ` %s ) = ( predBits ` <" 1o "> ) )' % (ph, RRB)),
                      closed(w, ph, 'predbits1', '( predBits ` <" 1o "> ) = (/)')], 'eqtrd', '( %s -> ( predBits ` %s ) = (/) )' % (ph, RRB))
            TAILW, tailw = '(/)', closed(w, ph, 'wrd0', '(/) e. Word 2o')
            ZX = YX4
        else:
            f0p = None
            hdp = w.s([rpw, cp, w.inst('wrdhdtl')], 'syl2anc', '( %s -> %s = ( <" ( %s ` 0 ) "> ++ %s ) )' % (ph, RPB, RPB, RQB))
            lt0 = w.s([rpw, cp, w.inst('hashgt0' if False else 'lennncl')], 'syl2anc', '( %s -> ( # ` %s ) e. NN )' % (ph, RPB))
            z0f = w.s([lt0, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` %s ) ) )' % (ph, RPB))
            rp0 = w.s([rpw, z0f, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( %s ` 0 ) e. 2o )' % (ph, RPB))
            rqw = w.s([rpw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, RQB))
            IRQ = '( inclBool o. %s )' % RQB
            irqg = w.s([rqw, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IRQ))
            ip = w.s([w.s([hdp], 'coeq2d', '( %s -> %s = ( inclBool o. ( <" ( %s ` 0 ) "> ++ %s ) ) )' % (ph, IRP, RPB, RQB)),
                      w.s([rp0, rqw, w.inst('bwmapcons')], 'syl2anc', '( %s -> ( inclBool o. ( <" ( %s ` 0 ) "> ++ %s ) ) = ( <" %s "> ++ %s ) )' % (ph, RPB, RQB, ZQ, IRQ))],
                     'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, IRP, ZQ, IRQ))
            gq = w.s([rp0, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, ZQ))
            sqg = w.s([gq], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, ZQ))
            xpe = w.s([w.s([ip], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ %s ) ++ %s ) )' % (ph, XP2, ZQ, IRQ, YX4)),
                       w.s([sqg, irqg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, ZQ, IRQ, YX4, ZQ, XQ))],
                      'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, XP2, ZQ, XQ))
            DK = DK0
            B_ = '( %s ` 0 )' % RPB
            pr0 = w.s([hd2, w.s([hdp], 'oveq2d', '( %s -> ( <" 1o "> ++ %s ) = ( <" 1o "> ++ ( <" %s "> ++ %s ) ) )' % (ph, RPB, B_, RQB))], 'eqtrd',
                      '( %s -> %s = ( <" 1o "> ++ ( <" %s "> ++ %s ) ) )' % (ph, RRB, B_, RQB))
            pr = w.s([w.s([pr0], 'fveq2d', '( %s -> ( predBits ` %s ) = ( predBits ` ( <" 1o "> ++ ( <" %s "> ++ %s ) ) ) )' % (ph, RRB, B_, RQB)),
                      w.s([rp0, rqw, w.inst('predbitscons1')], 'syl2anc', '( %s -> ( predBits ` ( <" 1o "> ++ ( <" %s "> ++ %s ) ) ) = ( <" (/) "> ++ ( <" %s "> ++ %s ) ) )' % (ph, B_, RQB, B_, RQB))],
                     'eqtrd', '( %s -> ( predBits ` %s ) = ( <" (/) "> ++ ( <" %s "> ++ %s ) ) )' % (ph, RRB, B_, RQB))
            TAILW = '( <" (/) "> ++ ( <" %s "> ++ %s ) )' % (B_, RQB)
            tailw = w.s([w.s([b0o], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ph), w.s([w.s([rp0], 's1cld', '( %s -> <" %s "> e. Word 2o )' % (ph, B_)), rqw, w.inst('ccatcl')], 'syl2anc',
                        '( %s -> ( <" %s "> ++ %s ) e. Word 2o )' % (ph, B_, RQB)), w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, TAILW))
            ZX = XP2
    # W = <. 1 , (/) >. repeatS b , over { <. 1 , (/) >. }
    REP0 = '( %s repeatS %s )' % (BIT0, BOR)
    REP1 = '( %s repeatS %s )' % (BIT1, BOR)
    ib0 = w.s([b0o, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ph, BIT0))
    ib1 = w.s([b1o, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = %s )' % (ph, BIT1))
    wrep = w.s([w.s([b0o, bn, ifl, w.inst('repsco')], 'syl3anc', '( %s -> %s = ( ( inclBool ` (/) ) repeatS %s ) )' % (ph, WB0, BOR)),
                w.s([ib0], 'oveq1d', '( %s -> ( ( inclBool ` (/) ) repeatS %s ) = %s )' % (ph, BOR, REP0))], 'eqtrd', '( %s -> %s = %s )' % (ph, WB0, REP0))
    b0in = sn_in(w, ph, BIT0, w.s([], 'opex', '%s e. _V' % BIT0))
    b1in = sn_in(w, ph, BIT1, w.s([], 'opex', '%s e. _V' % BIT1))
    wb0 = w.s([wrep, w.s([b0in, bn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, REP0, B0))], 'eqeltrd', '( %s -> %s e. Word %s )' % (ph, WB0, B0))
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    # interfaces
    p2 = '( %s /\\ ( r e. %s /\\ z e. %s ) )' % (ph, NPC, B0)
    rin = w.s([], 'simprl', '( %s -> r e. %s )' % (p2, NPC))
    zin = w.s([], 'simprr', '( %s -> z e. %s )' % (p2, B0))
    zeq = w.s([zin, w.inst('elsni')], 'syl', '( %s -> z = %s )' % (p2, BIT0))
    zz = w.s([zeq, w.s([bit0s], 'adantr', '( %s -> %s e. %s )' % (p2, BIT0, BITS))], 'eqeltrd', '( %s -> z e. %s )' % (p2, BITS))
    rr, fl, cm, ca = np_out(w, p2, 'r', rin)
    nv = rd_bit(w, p2, 'A', 'r', 'z', rr, zz)
    N2 = NVA('r', 'z')
    o2 = w.s([w.s([one, w.s([], '0ex', '(/) e. _V'), w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = (/)' % BIT0)], 'a1i', '( %s -> ( 2nd ` %s ) = (/) )' % (p2, BIT0))
    z2 = w.s([w.s([zeq], 'fveq2d', '( %s -> ( 2nd ` z ) = ( 2nd ` %s ) )' % (p2, BIT0)), o2], 'eqtrd', '( %s -> ( 2nd ` z ) = (/) )' % p2)
    ra0 = w.s([nv['fields']['ra'], w.s([z2], 'fveq2d', '( %s -> ( inl ` ( 2nd ` z ) ) = ( inl ` (/) ) )' % p2)], 'eqtrd', '( %s -> ( TMra ` %s ) = ( inl ` (/) ) )' % (p2, N2))
    c1, _ = cra_val(w, p2, nv, N2, '(/)', ra0)
    seq2 = w.s([seq], 'adantr', '( %s -> %s )' % (p2, SEQ))
    n2s = w.s([nv['mem'], seq2], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p2, N2))
    pv = w.s([w.s([bit1s], 'adantr', '( %s -> %s e. %s )' % (p2, BIT1, BITS)), n2s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (p2, CB1, N2, BIT1))
    gz = w.s([w.s([bit1s], 'adantr', '( %s -> %s e. %s )' % (p2, BIT1, BITS)), zin, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` z ) = %s )' % (p2, GPRD, BIT1))
    pg = w.s([pv, gz], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` z ) )' % (p2, CB1, N2, GPRD))
    kp = np_keep(w, p2, nv, N2, fl, cm, ca)
    IA = w.s([w.s([c1, pg, kp], '3jca', '( %s -> ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = ( %s ` z ) /\\ %s e. %s ) )' % (p2, CRAEQ('(/)'), N2, CB1, N2, GPRD, N2, NPC))],
             'ralrimivva', '( %s -> A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = ( %s ` z ) /\\ %s e. %s ) )' % (ph, NPC, B0, CRAEQ('(/)'), N2, CB1, N2, GPRD, N2, NPC))
    mvin = w.s([], 'tmcmvin', ST_MVIN)
    MV1 = ST_MVIN[2:].split(' /\\ A. r e. %s ( -. ' % NPC)[0]
    mv1 = w.s([mvin], 'simpli', MV1)
    mv2 = w.s([mvin], 'simpri', ST_MVIN[len('( ' + MV1 + ' /\\ '):-2])
    BODYZ = MV1.split(' A. z e. %s ' % BITS, 1)[1]
    b1ss = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V'), w.inst('snidg')], 'ax-mp', '1 e. { 1 }'),
                w.s([], '1oel2o', '1o e. 2o'), w.inst('opelxpi')], 'mp2an', '%s e. %s' % (BIT1, BITS))
    b1sub = w.s([b1ss, w.inst('snssi')], 'ax-mp', '%s C_ %s' % (B1S, BITS))
    sr = w.s([b1sub, w.inst('ssralv')], 'ax-mp', '( A. z e. %s %s -> A. z e. %s %s )' % (BITS, BODYZ, B1S, BODYZ))
    sr2 = w.s([sr], 'ralimi', '( A. r e. %s A. z e. %s %s -> A. r e. %s A. z e. %s %s )' % (NPC, BITS, BODYZ, NPC, B1S, BODYZ))
    mvB = w.s([mv1, sr2], 'ax-mp', 'A. r e. %s A. z e. %s %s' % (NPC, B1S, BODYZ))
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], leaf(IA): IA}
    for st in (mvB, mv2):
        a = w.s([st], 'a1i', '( %s -> %s )' % (ph, formula(w, st)))
        extra[leaf(a)] = a
    # the three-way dispatch at the stop letter
    DISJ = cj(tsub(T_FPRD[2][2], M_))
    D1, D2, D3 = split_or3(DISJ)
    p3 = '( %s /\\ m e. %s )' % (ph, NPC)
    mm = w.s([], 'simpr', '( %s -> m e. %s )' % (p3, NPC))
    mr, mfl, mcm, mca = np_out(w, p3, 'm', mm)
    seq3 = w.s([seq], 'adantr', '( %s -> %s )' % (p3, SEQ))
    n01 = w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
    if k == 0:
        nv3 = rd_comma(w, p3, 'A', 'm', mr)
        N3 = NVA('m', '4')
        ran = nv3['fields']['ra']
        def nra(b):
            ne = w.s([w.s([], '0ex' if b == '(/)' else '1oex', '%s e. _V' % b), w.inst('tmcinlne')], 'ax-mp', '-. ( inl ` %s ) = ( inr ` (/) )' % b)
            dn = w.s([w.s([ran], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = ( inl ` %s ) <-> ( inr ` (/) ) = ( inl ` %s ) ) )' % (p3, N3, b, b)),
                      w.s([w.s([ne, w.s([], 'eqcom', '( ( inr ` (/) ) = ( inl ` %s ) <-> ( inl ` %s ) = ( inr ` (/) ) )' % (b, b))], 'mtbir', '-. ( inr ` (/) ) = ( inl ` %s )' % b)],
                          'a1i', '( %s -> -. ( inr ` (/) ) = ( inl ` %s ) )' % (p3, b))], 'mtbird', '( %s -> -. ( TMra ` %s ) = ( inl ` %s ) )' % (p3, N3, b))
            cv, _ = cra_val(w, p3, nv3, N3, b, dn)
            return not1o(w, p3, cv, CRAEQ(b), N3)
        tA, tB = nra('(/)'), nra('1o')
        n3s = w.s([nv3['mem'], seq3], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p3, N3))
        p4 = w.s([closed(w, p3, '4re', '4 e. RR'), n3s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = 4 )' % (p3, C4S, N3))
        kp3 = np_keep(w, p3, nv3, N3, mfl, mcm, mca)
        TD = parse_conj(D3)
        BODY = cj(TD[0]).split(' m e. %s ' % NPC, 1)[1]
        bd = w.s([tA, tB, w.s([p4, kp3], 'jca', '( %s -> ( ( %s ` %s ) = 4 /\\ %s e. %s ) )' % (p3, C4S, N3, N3, NPC))], '3jca', '( %s -> %s )' % (p3, BODY))
        ral = w.s([bd], 'ralrimiva', '( %s -> %s )' % (ph, cj(TD[0])))
        dj = w.s([ral, w.s([], 'eqidd', '( %s -> %s )' % (ph, cj(TD[1])))], 'jca', '( %s -> %s )' % (ph, D3))
        disj = w.s([dj], '3mix3d', '( %s -> %s )' % (ph, DISJ))
    else:
        nv3 = rd_bit(w, p3, 'A', 'm', BIT1, mr, w.s([bit1s], 'adantr', '( %s -> %s e. %s )' % (p3, BIT1, BITS)))
        N3 = NVA('m', BIT1)
        o21 = w.s([w.s([one, w.s([], '1oex', '1o e. _V'), w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = 1o' % BIT1)], 'a1i', '( %s -> ( 2nd ` %s ) = 1o )' % (p3, BIT1))
        ra1 = w.s([nv3['fields']['ra'], w.s([o21], 'fveq2d', '( %s -> ( inl ` ( 2nd ` %s ) ) = ( inl ` 1o ) )' % (p3, BIT1))], 'eqtrd', '( %s -> ( TMra ` %s ) = ( inl ` 1o ) )' % (p3, N3))
        inj = w.s([w.s([], '1oex', '1o e. _V'), w.s([], '0ex', '(/) e. _V'), w.inst('tmcinl11')], 'mp2an', '( ( inl ` 1o ) = ( inl ` (/) ) <-> 1o = (/) )')
        n10 = w.s([w.s([], '1n0', '1o =/= (/)'), w.s([], 'df-ne', '( 1o =/= (/) <-> -. 1o = (/) )')], 'mpbi', '-. 1o = (/)')
        ni = w.s([inj, n10], 'mtbir', '-. ( inl ` 1o ) = ( inl ` (/) )')
        dn = w.s([w.s([ra1], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = ( inl ` (/) ) <-> ( inl ` 1o ) = ( inl ` (/) ) ) )' % (p3, N3)),
                  w.s([ni], 'a1i', '( %s -> -. ( inl ` 1o ) = ( inl ` (/) ) )' % p3)], 'mtbird', '( %s -> -. ( TMra ` %s ) = ( inl ` (/) ) )' % (p3, N3))
        cA, _ = cra_val(w, p3, nv3, N3, '(/)', dn)
        tA = not1o(w, p3, cA, CRAEQ('(/)'), N3)
        tB, _ = cra_val(w, p3, nv3, N3, '1o', ra1)
        ZP = M_["Z'"]
        if k == 1:
            nvE = rd_comma(w, p3, 'End', N3, nv3['mem'])
        else:
            gq3 = w.s([gq], 'adantr', "( %s -> %s e. Gamma' )" % (p3, ZQ))
            zqb = w.s([w.s([s1a, rp0], 'opelxpd', '( %s -> %s e. %s )' % (ph, ZQ, BITS))], 'adantr', '( %s -> %s e. %s )' % (p3, ZQ, BITS))
            nvE = rd_bit(w, p3, 'End', N3, ZQ, nv3['mem'], zqb)
        NE = '( TMrdEnd ` <. %s , ( inl ` %s ) >. )' % (N3, ZP)
        dbv = nvE['fields']['db']
        # keep the class through the peek: fl cmp car of NE = those of N3 = those of m
        f_ = lambda fld, st: w.s([nvE['fields'][fld], nv3['fields'][fld], st], 'eqtrd' if False else '3eqtrd', None) if False else None
        fe = {}
        for fld, st, Q in [('fl', mfl, 'O'), ('cmp', mcm, 'Q'), ('car', mca, 'R')]:
            A_ = {'fl': 'TMfl', 'cmp': 'TMcmp', 'car': 'TMcar'}[fld]
            e1 = w.s([nvE['fields'][fld], nv3['fields'][fld]], 'eqtrd', '( %s -> ( %s ` %s ) = ( %s ` m ) )' % (p3, A_, NE, A_))
            fe[fld] = w.s([e1, st], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (p3, A_, NE, Q))
        kpE = np_in(w, p3, NE, nvE['mem'], fe['fl'], fe['cmp'], fe['car'])
        if k == 1:
            TD = parse_conj(D1)
            BODY = cj(TD[1]).split(' m e. %s ' % NPC, 1)[1]
            bd = w.s([w.s([tA, tB], 'jca', '( %s -> ( -. ( %s ` %s ) = 1o /\\ ( %s ` %s ) = 1o ) )' % (p3, CRAEQ('(/)'), N3, CRAEQ('1o'), N3)),
                      w.s([dbv, kpE], 'jca', '( %s -> ( ( TMdb ` %s ) = 1o /\\ %s e. %s ) )' % (p3, NE, NE, NPC))], 'jca', '( %s -> %s )' % (p3, BODY))
            ral = w.s([bd], 'ralrimiva', '( %s -> %s )' % (ph, cj(TD[1])))
            dj = w.s([w.s([], 'eqidd', '( %s -> %s )' % (ph, cj(TD[0]))), ral, w.s([], 'eqidd', '( %s -> %s )' % (ph, cj(TD[2])))], '3jca', '( %s -> %s )' % (ph, D1))
            disj = w.s([dj], '3mix1d', '( %s -> %s )' % (ph, DISJ))
        else:
            TD = parse_conj(D2)
            BODY = cj(TD[1]).split(' m e. %s ' % NPC, 1)[1]
            dbn = not1o(w, p3, dbv, 'TMdb', NE)
            nEs = w.s([nvE['mem'], seq3], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p3, NE))
            pz = w.s([w.s([bit0s], 'adantr', '( %s -> %s e. %s )' % (p3, BIT0, BITS)), nEs, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (p3, CB0, NE, BIT0))
            bd = w.s([w.s([tA, tB], 'jca', '( %s -> ( -. ( %s ` %s ) = 1o /\\ ( %s ` %s ) = 1o ) )' % (p3, CRAEQ('(/)'), N3, CRAEQ('1o'), N3)),
                      w.s([dbn, w.s([pz, kpE], 'jca', '( %s -> ( ( %s ` %s ) = %s /\\ %s e. %s ) )' % (p3, CB0, NE, BIT0, NE, NPC))], 'jca',
                          '( %s -> ( -. ( TMdb ` %s ) = 1o /\\ ( ( %s ` %s ) = %s /\\ %s e. %s ) ) )' % (p3, NE, CB0, NE, BIT0, NE, NPC))],
                     'jca', '( %s -> %s )' % (p3, BODY))
            ral = w.s([bd], 'ralrimiva', '( %s -> %s )' % (ph, cj(TD[1])))
            dj = w.s([xpe, ral, w.s([], 'eqidd', '( %s -> %s )' % (ph, cj(TD[2])))], '3jca', '( %s -> %s )' % (ph, D2))
            disj = w.s([dj], '3mix2d', '( %s -> %s )' % (ph, DISJ))
    extra[DISJ] = disj
    # typings and letters
    craty = lambda b: lamty(w, ph, mk, CRAEQ(b), lambda t: 'if ( ( TMra ` %s ) = ( inl ` %s ) , 1o , (/) )' % (t, b), '2o', w.s([], '2oex', '2o e. _V'),
                               w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', 'if ( ( TMra ` u ) = ( inl ` %s ) , 1o , (/) ) e. 2o' % b))
    extra[CTY(CRAEQ('1o'))] = craty('1o')
    extra[CTY(CRAEQ('(/)'))] = craty('(/)')
    extra[CTY(CIS)] = cis_ty(w, ph, mk)
    ft = flty(w, ph, mk)
    extra[CTY('TMdb')] = ft['TMdb e. ( 2o ^m ( 2nd ` T ) )']
    for kk in ['K', 'J']:
        extra['%s e. %s' % (kk, DG)] = mk['k'][kk]['kd']
        extra[RTY('TMrdA', kk)] = mk['k'][kk]['hdl']['TMrdA']
    extra[RTY('TMrdEnd', 'K')] = mk['k']['K']['hdl']['TMrdEnd']
    b1J = letgk(w, ph, mk, BIT1, 'J', g1)
    b1K = letgk(w, ph, mk, BIT1, 'K', g1)
    b0K = letgk(w, ph, mk, BIT0, 'K', g0)
    g4K = letgk(w, ph, mk, '4', 'K', g4)
    extra[PTY(CB1, 'J')] = constfty(w, ph, BIT1, GX('J'), b1J)
    extra[PTY(CB0, 'K')] = constfty(w, ph, BIT0, GX('K'), b0K)
    extra[PTY(C4S, 'K')] = constfty(w, ph, '4', GX('K'), g4K)
    extra[PTY(PBR, 'K')] = pbr_ty(w, ph, mk, 'K')
    extra['%s C_ %s' % (B0, GX('K'))] = w.s([b0K], 'snssd', '( %s -> %s C_ %s )' % (ph, B0, GX('K')))
    extra['%s C_ %s' % (B1S, GX('K'))] = w.s([b1K], 'snssd', '( %s -> %s C_ %s )' % (ph, B1S, GX('K')))
    extra['%s C_ %s' % (B1S, GX('J'))] = w.s([b1J], 'snssd', '( %s -> %s C_ %s )' % (ph, B1S, GX('J')))
    extra['%s : %s --> %s' % (GPRD, B0, B1S)] = closed(w, ph, 'fconst', '%s : %s --> %s' % (GPRD, B0, B1S))
    extra['4 e. %s' % GX('J')] = letgk(w, ph, mk, '4', 'J', g4)
    extra['4 e. %s' % GX('K')] = g4K
    extra['%s e. %s' % (BIT1, GX('K'))] = b1K
    extra['%s e. %s' % (BIT0, GX('K'))] = b0K
    if k == 2:
        extra['%s e. %s' % (ZQ, GX('K'))] = letgk(w, ph, mk, ZQ, 'K', gq)
        extra[WRD(XQ, GX('K'))] = togk(w, ph, mk, XQ, 'K', wg_(w, ph, IRQ, YX4, irqg, x4))
        extra[WRD(XP2, GX('K'))] = togk(w, ph, mk, XP2, 'K', wg_(w, ph, IRP, YX4, irpg, x4))
    extra[WRD('X', GX('K'))] = togk(w, ph, mk, 'X', 'K', xg)
    extra[WRD(YX4, GX('K'))] = togk(w, ph, mk, YX4, 'K', x4)
    extra[WRD(WB0, B0)] = wb0
    extra['( D ` K ) = ( %s ++ ( <" %s "> ++ %s ) )' % (WB0, M_['Z'], M_['X'])] = DK
    nss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPC))
    extra['%s C_ ( 2nd ` T )' % NPC] = w.s([nss, seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPC))
    bld = Builder(w, ph, c, extra)
    ante, concl = split_imp(stmt('tm2fprdn'))
    st = bld(tsub(parse_conj(ante), M_))
    c2 = tsub_text(concl, M_)
    tri = w.s([st, w.inst('tm2fprdn')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1_, n1 = triple_parts(c2)
    # the result word: ( G o. W ) ++ Z0 = ( inclBool o. ( predBits ` L ) ) ++ ( <" 4 "> ++ X )
    gf = extra['%s : %s --> %s' % (GPRD, B0, B1S)]
    gw1 = w.s([wrep], 'coeq2d', '( %s -> ( %s o. %s ) = ( %s o. %s ) )' % (ph, GPRD, WB0, GPRD, REP0))
    gw2 = w.s([b0in, bn, gf, w.inst('repsco')], 'syl3anc', '( %s -> ( %s o. %s ) = ( ( %s ` %s ) repeatS %s ) )' % (ph, GPRD, REP0, GPRD, BIT0, BOR))
    gv = w.s([bit1s, b0in, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, GPRD, BIT0, BIT1))
    gw = w.s([w.s([gw1, gw2], 'eqtrd', '( %s -> ( %s o. %s ) = ( ( %s ` %s ) repeatS %s ) )' % (ph, GPRD, WB0, GPRD, BIT0, BOR)),
              w.s([gv], 'oveq1d', '( %s -> ( ( %s ` %s ) repeatS %s ) = %s )' % (ph, GPRD, BIT0, BOR, REP1))], 'eqtrd', '( %s -> ( %s o. %s ) = %s )' % (ph, GPRD, WB0, REP1))
    i1 = w.s([w.s([b1o, bn, ifl, w.inst('repsco')], 'syl3anc', '( %s -> ( inclBool o. %s ) = ( ( inclBool ` 1o ) repeatS %s ) )' % (ph, R1c, BOR)),
              w.s([ib1], 'oveq1d', '( %s -> ( ( inclBool ` 1o ) repeatS %s ) = %s )' % (ph, BOR, REP1))], 'eqtrd', '( %s -> ( inclBool o. %s ) = %s )' % (ph, R1c, REP1))
    tpr = w.s([w.s([rrw, bn], 'jca', '( %s -> ( %s e. Word 2o /\\ %s e. NN0 ) )' % (ph, RRB, BOR)), w.inst('tmcprdi')], 'syl',
              '( %s -> ( predBits ` ( %s ++ %s ) ) = ( %s ++ ( predBits ` %s ) ) )' % (ph, R0c, RRB, R1c, RRB))
    pe = w.s([w.s([dec], 'fveq2d', '( %s -> ( predBits ` L ) = ( predBits ` ( %s ++ %s ) ) )' % (ph, R0c, RRB)), tpr], 'eqtrd',
             '( %s -> ( predBits ` L ) = ( %s ++ ( predBits ` %s ) ) )' % (ph, R1c, RRB))
    pe2 = w.s([pe, w.s([pr], 'oveq2d', '( %s -> ( %s ++ ( predBits ` %s ) ) = ( %s ++ %s ) )' % (ph, R1c, RRB, R1c, TAILW))], 'eqtrd',
              '( %s -> ( predBits ` L ) = ( %s ++ %s ) )' % (ph, R1c, TAILW))
    im = w.s([w.s([pe2], 'coeq2d', '( %s -> ( inclBool o. ( predBits ` L ) ) = ( inclBool o. ( %s ++ %s ) ) )' % (ph, R1c, TAILW)),
              w.s([r1w, tailw, w.inst('bwmapccat')], 'syl2anc', '( %s -> ( inclBool o. ( %s ++ %s ) ) = ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) )' % (ph, R1c, TAILW, R1c, TAILW))],
             'eqtrd', '( %s -> ( inclBool o. ( predBits ` L ) ) = ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) )' % (ph, R1c, TAILW))
    rep1g = w.s([i1, w.s([r1w, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, R1c))], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ph, REP1))
    if k in (0, 1):
        it = closed(w, ph, 'bwmap0', '( inclBool o. (/) ) = (/)')
        im2 = w.s([im, w.s([i1, it], 'oveq12d', '( %s -> ( ( inclBool o. %s ) ++ ( inclBool o. (/) ) ) = ( %s ++ (/) ) )' % (ph, R1c, REP1))], 'eqtrd',
                  '( %s -> ( inclBool o. ( predBits ` L ) ) = ( %s ++ (/) ) )' % (ph, REP1))
        im3 = w.s([im2, w.s([rep1g, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, REP1, REP1))], 'eqtrd', '( %s -> ( inclBool o. ( predBits ` L ) ) = %s )' % (ph, REP1))
        fin0 = w.s([im3], 'oveq1d', '( %s -> ( ( inclBool o. ( predBits ` L ) ) ++ %s ) = ( %s ++ %s ) )' % (ph, YX4, REP1, YX4))
        Z0 = M_['Z0']
        assert Z0 == YX4
    else:
        B_ = '( %s ` 0 )' % RPB
        TMW = '( <" %s "> ++ ( <" %s "> ++ %s ) )' % (BIT0, ZQ, IRQ)
        tm = w.s([w.s([b0o, w.s([w.s([rp0], 's1cld', '( %s -> <" %s "> e. Word 2o )' % (ph, B_)), rqw, w.inst('ccatcl')], 'syl2anc',
                                   '( %s -> ( <" %s "> ++ %s ) e. Word 2o )' % (ph, B_, RQB)), w.inst('bwmapcons')], 'syl2anc',
                      '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ ( inclBool o. ( <" %s "> ++ %s ) ) ) )' % (ph, TAILW, BIT0, B_, RQB)),
                  w.s([w.s([rp0, rqw, w.inst('bwmapcons')], 'syl2anc', '( %s -> ( inclBool o. ( <" %s "> ++ %s ) ) = ( <" %s "> ++ %s ) )' % (ph, B_, RQB, ZQ, IRQ))], 'oveq2d',
                      '( %s -> ( <" %s "> ++ ( inclBool o. ( <" %s "> ++ %s ) ) ) = %s )' % (ph, BIT0, B_, RQB, TMW))], 'eqtrd', '( %s -> ( inclBool o. %s ) = %s )' % (ph, TAILW, TMW))
        im2 = w.s([im, w.s([i1, tm], 'oveq12d', '( %s -> ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) = ( %s ++ %s ) )' % (ph, R1c, TAILW, REP1, TMW))], 'eqtrd',
                  '( %s -> ( inclBool o. ( predBits ` L ) ) = ( %s ++ %s ) )' % (ph, REP1, TMW))
        tmg = wg_(w, ph, '<" %s ">' % BIT0, '( <" %s "> ++ %s )' % (ZQ, IRQ), s0g, wg_(w, ph, '<" %s ">' % ZQ, IRQ, sqg, irqg))
        f1 = w.s([im2], 'oveq1d', '( %s -> ( ( inclBool o. ( predBits ` L ) ) ++ %s ) = ( ( %s ++ %s ) ++ %s ) )' % (ph, YX4, REP1, TMW, YX4))
        f2 = w.s([rep1g, tmg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (ph, REP1, TMW, YX4, REP1, TMW, YX4))
        Z0 = M_['Z0']
        # ( TMW ++ YX4 ) = Z0 = <" BIT0 "> ++ ( <" ZQ "> ++ XQ )
        f3a = w.s([s0g, wg_(w, ph, '<" %s ">' % ZQ, IRQ, sqg, irqg), x4, w.inst('ccatass')], 'syl3anc',
                  '( %s -> ( %s ++ %s ) = ( <" %s "> ++ ( ( <" %s "> ++ %s ) ++ %s ) ) )' % (ph, TMW, YX4, BIT0, ZQ, IRQ, YX4))
        f3b = w.s([w.s([sqg, irqg, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, ZQ, IRQ, YX4, ZQ, XQ))], 'oveq2d',
                  '( %s -> ( <" %s "> ++ ( ( <" %s "> ++ %s ) ++ %s ) ) = %s )' % (ph, BIT0, ZQ, IRQ, YX4, Z0))
        f3 = w.s([f3a, f3b], 'eqtrd', '( %s -> ( %s ++ %s ) = %s )' % (ph, TMW, YX4, Z0))
        fin0 = w.s([w.s([f1, f2], 'eqtrd', '( %s -> ( ( inclBool o. ( predBits ` L ) ) ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (ph, YX4, REP1, TMW, YX4)),
                    w.s([f3], 'oveq2d', '( %s -> ( %s ++ ( %s ++ %s ) ) = ( %s ++ %s ) )' % (ph, REP1, TMW, YX4, REP1, Z0))], 'eqtrd',
                   '( %s -> ( ( inclBool o. ( predBits ` L ) ) ++ %s ) = ( %s ++ %s ) )' % (ph, YX4, REP1, Z0))
    fin = w.s([fin0, w.s([gw], 'oveq1d', '( %s -> ( ( %s o. %s ) ++ %s ) = ( %s ++ %s ) )' % (ph, GPRD, WB0, Z0, REP1, Z0))], 'eqtr4d',
              '( %s -> ( ( inclBool o. ( predBits ` L ) ) ++ %s ) = ( ( %s o. %s ) ++ %s ) )' % (ph, YX4, GPRD, WB0, Z0))
    OLDV = '( ( %s o. %s ) ++ %s )' % (GPRD, WB0, Z0)
    NEWV = CC("( inclBool o. ( predBits ` L ) )", YX4)
    ue = upeq(w, ph, 'D', 'K', w.s([fin], 'eqcomd', '( %s -> %s = %s )' % (ph, OLDV, NEWV)), OLDV, NEWV)
    deq = clneq(w, ph, 'E', NPC, ue, UP('D', 'K', OLDV), UP('D', 'K', NEWV))
    t2, C2, D2, n2 = hrrw(w, ph, tri, C1, D1_, n1, deq=deq)
    wl = w.s([r0w, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, WB0, R0c))
    rl = w.s([closed(w, ph, '0ex', '(/) e. _V'), bn, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, R0c, BOR))
    ble = w.s([ll, w.inst('borrowsle')], 'syl', '( %s -> %s <_ ( # ` L ) )' % (ph, BOR))
    lw0 = w.s([wib, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, WB0))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    leaves = {'( # ` %s )' % WB0: lw0, '( # ` %s )' % R0c: w.s([r0w, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, R0c)), BOR: bn, '( # ` L )': la}
    bound(w, ph, mk['phm'], t2, C2, D2, n2, '( ( 2 x. ( # ` L ) ) + 3 )', leaves, hyps=[wl, rl, ble], qed=True)
    return w.run()


def tmcprd0():
    return prdcase(0)


def tmcprd1():
    return prdcase(1)


def tmcprd2():
    return prdcase(2)


def tmcprdn():
    lab = 'tmcprdn'
    ph = cj(TREE_PRD)
    w = W(lab, '` predNum x s ` at the machine (Lean ` predNum_runs ` ): the top number of ` x ` is decremented in '
               'place (` predBits ` ; ` 0 ` goes to the all-ones word of its length, Lean\'s truncation being the '
               'consumer\'s); ` flag ` , ` cmp ` , ` carry ` are preserved; in ` 2 |l| + 3 ` steps.  The join of '
               '~ tmcprd0 , ~ tmcprd1 , ~ tmcprd2 .')
    A0 = '%s = (/)' % RRB
    A1 = '%s = (/)' % RPB
    t0 = w.s([], 'tmcprd0', '( ( %s /\\ %s ) -> %s )' % (ph, A0, CONCL_PRD))
    t1 = w.s([], 'tmcprd1', '( ( %s /\\ ( %s =/= (/) /\\ %s ) ) -> %s )' % (ph, RRB, A1, CONCL_PRD))
    t2 = w.s([], 'tmcprd2', '( ( %s /\\ ( %s =/= (/) /\\ %s =/= (/) ) ) -> %s )' % (ph, RRB, RPB, CONCL_PRD))
    pn = '( %s /\\ -. %s )' % (ph, A0)
    ne = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (pn, A0))], 'neqned', '( %s -> %s =/= (/) )' % (pn, RRB))
    q1 = '( %s /\\ %s )' % (pn, A1)
    u1 = w.s([w.s([], 'simpll', '( %s -> %s )' % (q1, ph)), w.s([w.s([ne], 'adantr', '( %s -> %s =/= (/) )' % (q1, RRB)), w.s([], 'simpr', '( %s -> %s )' % (q1, A1))], 'jca',
              '( %s -> ( %s =/= (/) /\\ %s ) )' % (q1, RRB, A1)), t1], 'syl2anc', '( %s -> %s )' % (q1, CONCL_PRD))
    q2 = '( %s /\\ -. %s )' % (pn, A1)
    u2 = w.s([w.s([], 'simpll', '( %s -> %s )' % (q2, ph)), w.s([w.s([ne], 'adantr', '( %s -> %s =/= (/) )' % (q2, RRB)),
              w.s([w.s([], 'simpr', '( %s -> -. %s )' % (q2, A1))], 'neqned', '( %s -> %s =/= (/) )' % (q2, RPB))], 'jca',
              '( %s -> ( %s =/= (/) /\\ %s =/= (/) ) )' % (q2, RRB, RPB)), t2], 'syl2anc', '( %s -> %s )' % (q2, CONCL_PRD))
    un = w.s([u1, u2], 'pm2.61dan', '( %s -> %s )' % (pn, CONCL_PRD))
    w.qed([t0, un], 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_PRD))
    return w.run()


if __name__ == '__main__':
    for l in ['tmcprdi', 'tmcprd0', 'tmcprd1', 'tmcprd2', 'tmcprdn']:
        if want(l) and l in globals(): globals()[l]()
