"""T11: the list arithmetic of the scan half (PrimList.lean, Steps23.lean facts), by word induction
(tools/a4alib.py ` family ` , ~ algwrdi ).

  mulallsnoc   ` mulAll q ( l ++ [ r ] ) = mulAll q l ++ [ r q ] ` (Lean ` mulAll_fst ` , ` List.map_append ` )

    MM_DB=sorties/t11.mm python3 tools/gen/t11_a_arith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


CSV = '( <" P "> ++ V )'
WN = '( Word NN0 X. NN0 )'
STMTS = {}

# ======================================================================= mulAll of a word with one more entry
QR = '( Q e. NN0 /\\ R e. NN0 )'
MAS = lambda s: '( 1st ` ( Q MulAll ( %s ++ <" R "> ) ) )' % s
MA1 = lambda s: '( 1st ` ( Q MulAll %s ) )' % s
RQ = '<" ( R x. Q ) ">'
PHI_MS = '( %s -> %s = ( %s ++ %s ) )' % (QR, MAS('s'), MA1('s'), RQ)


def _b(w, goal):
    A = QR
    qn = w.s([], 'simpl', '( %s -> Q e. NN0 )' % A)
    rn = w.s([], 'simpr', '( %s -> R e. NN0 )' % A)
    r1 = w.s([w.s([rn, w.inst('s1cl')], 'syl', '( %s -> <" R "> e. Word NN0 )' % A), w.inst('ccatlid')], 'syl',
             '( %s -> ( (/) ++ <" R "> ) = <" R "> )' % A)
    r2 = w.s([w.s([rn, w.inst('s1cl')], 'syl', '( %s -> <" R "> e. Word NN0 )' % A), w.inst('ccatrid')], 'syl',
             '( %s -> ( <" R "> ++ (/) ) = <" R "> )' % A)
    e1 = w.s([r1, w.s([r2], 'eqcomd', '( %s -> <" R "> = ( <" R "> ++ (/) ) )' % A)], 'eqtrd',
             '( %s -> ( (/) ++ <" R "> ) = ( <" R "> ++ (/) ) )' % A)
    e2 = w.s([e1], 'oveq2d', '( %s -> ( Q MulAll ( (/) ++ <" R "> ) ) = ( Q MulAll ( <" R "> ++ (/) ) ) )' % A)
    w0 = w.s([w.s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % A)
    cs = w.s([w.s([qn, rn], 'jca', '( %s -> ( Q e. NN0 /\\ R e. NN0 ) )' % A), w0, w.inst('mulallcs')], 'syl2anc',
             '( %s -> ( Q MulAll ( <" R "> ++ (/) ) ) = <. ( %s ++ %s ) , ( ( 2nd ` ( Q MulAll (/) ) ) + 1 ) >. )'
             % (A, RQ, MA1('(/)')))
    m0 = w.s([qn, w.inst('mulall0')], 'syl', '( %s -> ( Q MulAll (/) ) = <. (/) , 0 >. )' % A)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    z2 = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    p0 = projeq(w, A, '( Q MulAll (/) )', m0, '(/)', '0', z, z2, 1)
    cl = w.s([qn, w0, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll (/) ) e. %s )' % (A, WN))
    a1, b1 = paircl(w, A, '( Q MulAll (/) )', cl, 'Word NN0', 'NN0')
    rqn = w.s([rn, qn], 'nn0mulcld', '( %s -> ( R x. Q ) e. NN0 )' % A)
    s1 = w.s([rqn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (A, RQ))
    xa = w.s([s1, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. Word NN0 )' % (A, RQ, MA1('(/)')))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll (/) ) ) + 1 ) e. NN0 )' % A)
    p1 = projeq(w, A, '( Q MulAll ( <" R "> ++ (/) ) )', cs, '( %s ++ %s )' % (RQ, MA1('(/)')),
                '( ( 2nd ` ( Q MulAll (/) ) ) + 1 )', xa, xb, 1)
    l1 = w.s([w.s([e2], 'fveq2d', '( %s -> %s = ( 1st ` ( Q MulAll ( <" R "> ++ (/) ) ) ) )' % (A, MAS('(/)'))), p1], 'eqtrd',
             '( %s -> %s = ( %s ++ %s ) )' % (A, MAS('(/)'), RQ, MA1('(/)')))
    # both sides equal RQ
    c1 = w.s([p0], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ (/) ) )' % (A, RQ, MA1('(/)'), RQ))
    c2 = w.s([s1, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (A, RQ, RQ))
    lhs = w.s([w.s([l1, c1], 'eqtrd', '( %s -> %s = ( %s ++ (/) ) )' % (A, MAS('(/)'), RQ)), c2], 'eqtrd',
              '( %s -> %s = %s )' % (A, MAS('(/)'), RQ))
    d1 = w.s([p0], 'oveq1d', '( %s -> ( %s ++ %s ) = ( (/) ++ %s ) )' % (A, MA1('(/)'), RQ, RQ))
    d2 = w.s([s1, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (A, RQ, RQ))
    rhs = w.s([d1, d2], 'eqtrd', '( %s -> ( %s ++ %s ) = %s )' % (A, MA1('(/)'), RQ, RQ))
    w.qed([lhs, rhs], 'eqtr4d', goal)


def _s(w, A, ih, co):
    A2 = '( %s /\\ %s )' % (A, QR)
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qr = w.s([], 'simpr', '( %s -> %s )' % (A2, QR))
    qn = w.s([qr], 'simpld', '( %s -> Q e. NN0 )' % A2)
    rn = w.s([qr], 'simprd', '( %s -> R e. NN0 )' % A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), qr], 'mpd', '( %s -> %s = ( %s ++ %s ) )' % (A2, MAS('V'), MA1('V'), RQ))
    sp = w.s([pn, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A2)
    sr = w.s([rn, w.inst('s1cl')], 'syl', '( %s -> <" R "> e. Word NN0 )' % A2)
    VR = '( V ++ <" R "> )'
    vr = w.s([vs, sr, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, VR))
    ass = w.s([sp, vs, sr, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ <" R "> ) = ( <" P "> ++ %s ) )' % (A2, CSV, VR))
    qp = w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2)
    PQ = '<" ( P x. Q ) ">'
    cs1 = w.s([qp, vr, w.inst('mulallcs')], 'syl2anc',
              '( %s -> ( Q MulAll ( <" P "> ++ %s ) ) = <. ( %s ++ %s ) , ( ( 2nd ` ( Q MulAll %s ) ) + 1 ) >. )'
              % (A2, VR, PQ, MA1(VR), VR))
    cl1 = w.s([qn, vr, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll %s ) e. %s )' % (A2, VR, WN))
    a1, b1 = paircl(w, A2, '( Q MulAll %s )' % VR, cl1, 'Word NN0', 'NN0')
    pqn = w.s([pn, qn], 'nn0mulcld', '( %s -> ( P x. Q ) e. NN0 )' % A2)
    s1 = w.s([pqn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (A2, PQ))
    xa = w.s([s1, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. Word NN0 )' % (A2, PQ, MA1(VR)))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll %s ) ) + 1 ) e. NN0 )' % (A2, VR))
    p1 = projeq(w, A2, '( Q MulAll ( <" P "> ++ %s ) )' % VR, cs1, '( %s ++ %s )' % (PQ, MA1(VR)),
                '( ( 2nd ` ( Q MulAll %s ) ) + 1 )' % VR, xa, xb, 1)
    l1 = w.s([w.s([w.s([ass], 'oveq2d', '( %s -> ( Q MulAll ( %s ++ <" R "> ) ) = ( Q MulAll ( <" P "> ++ %s ) ) )' % (A2, CSV, VR))],
                  'fveq2d', '( %s -> %s = ( 1st ` ( Q MulAll ( <" P "> ++ %s ) ) ) )' % (A2, MAS(CSV), VR)), p1], 'eqtrd',
             '( %s -> %s = ( %s ++ %s ) )' % (A2, MAS(CSV), PQ, MA1(VR)))
    l2 = w.s([ihs], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (A2, PQ, MA1(VR), PQ, MA1('V'), RQ))
    clv = w.s([qn, vs, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll V ) e. %s )' % (A2, WN))
    av, bv = paircl(w, A2, '( Q MulAll V )', clv, 'Word NN0', 'NN0')
    rqn = w.s([rn, qn], 'nn0mulcld', '( %s -> ( R x. Q ) e. NN0 )' % A2)
    srq = w.s([rqn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (A2, RQ))
    l3 = w.s([s1, av, srq, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ ( %s ++ %s ) ) )'
             % (A2, PQ, MA1('V'), RQ, PQ, MA1('V'), RQ))
    lhs = w.s([w.s([l1, l2], 'eqtrd', '( %s -> %s = ( %s ++ ( %s ++ %s ) ) )' % (A2, MAS(CSV), PQ, MA1('V'), RQ)), l3], 'eqtr4d',
              '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (A2, MAS(CSV), PQ, MA1('V'), RQ))
    cs2 = w.s([qp, vs, w.inst('mulallcs')], 'syl2anc',
              '( %s -> ( Q MulAll %s ) = <. ( %s ++ %s ) , ( ( 2nd ` ( Q MulAll V ) ) + 1 ) >. )' % (A2, CSV, PQ, MA1('V')))
    xa2 = w.s([s1, av, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. Word NN0 )' % (A2, PQ, MA1('V')))
    xb2 = w.s([bv, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll V ) ) + 1 ) e. NN0 )' % A2)
    p2 = projeq(w, A2, '( Q MulAll %s )' % CSV, cs2, '( %s ++ %s )' % (PQ, MA1('V')), '( ( 2nd ` ( Q MulAll V ) ) + 1 )', xa2, xb2, 1)
    rhs = w.s([p2], 'oveq1d', '( %s -> ( %s ++ %s ) = ( ( %s ++ %s ) ++ %s ) )' % (A2, MA1(CSV), RQ, PQ, MA1('V'), RQ))
    w.qed([w.s([lhs, rhs], 'eqtr4d', '( %s -> %s = ( %s ++ %s ) )' % (A2, MAS(CSV), MA1(CSV), RQ))], 'ex', '( %s -> %s )' % (A, co))


def _f_ms(w, st, phit):
    T = '( ( Q e. NN0 /\\ R e. NN0 ) /\\ S e. Word NN0 )'
    sw = w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T)
    a = w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit))
    w.qed([w.s([], 'simpl', '( %s -> %s )' % (T, QR)), a], 'mpd', '( %s -> %s = ( %s ++ %s ) )' % (T, MAS('S'), MA1('S'), RQ))


STMTS['mulallsnoc'] = '( ( ( Q e. NN0 /\\ R e. NN0 ) /\\ S e. Word NN0 ) -> %s = ( %s ++ %s ) )' % (MAS('S'), MA1('S'), RQ)

# ======================================================================= mulAll commutes with reverse
MR = lambda s: '( 1st ` ( Q MulAll ( reverse ` %s ) ) )' % s
RMA = lambda s: '( reverse ` ( 1st ` ( Q MulAll %s ) ) )' % s
PHI_MR = '( Q e. NN0 -> %s = %s )' % (MR('s'), RMA('s'))


def _b_mr(w, goal):
    A = 'Q e. NN0'
    r0 = w.s([w.s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % A)
    m0 = w.s([], 'mulall0', '( %s -> ( Q MulAll (/) ) = <. (/) , 0 >. )' % A)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    z2 = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    p0 = projeq(w, A, '( Q MulAll (/) )', m0, '(/)', '0', z, z2, 1)
    l = w.s([w.s([w.s([r0], 'oveq2d', '( %s -> ( Q MulAll ( reverse ` (/) ) ) = ( Q MulAll (/) ) )' % A)], 'fveq2d',
                 '( %s -> %s = ( 1st ` ( Q MulAll (/) ) ) )' % (A, MR('(/)'))), p0], 'eqtrd', '( %s -> %s = (/) )' % (A, MR('(/)')))
    r = w.s([w.s([p0], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (A, RMA('(/)'))), r0], 'eqtrd', '( %s -> %s = (/) )' % (A, RMA('(/)')))
    w.qed([l, r], 'eqtr4d', goal)


def _s_mr(w, A, ih, co):
    A2 = '( %s /\\ Q e. NN0 )' % A
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qn = w.s([], 'simpr', '( %s -> Q e. NN0 )' % A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), qn], 'mpd', '( %s -> %s = %s )' % (A2, MR('V'), RMA('V')))
    sp = w.s([pn, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A2)
    rv = w.s([vs, w.inst('revcl')], 'syl', '( %s -> ( reverse ` V ) e. Word NN0 )' % A2)
    r1 = w.s([sp, vs, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` %s ) = ( ( reverse ` V ) ++ ( reverse ` <" P "> ) ) )' % (A2, CSV))
    r2 = w.s([r1, w.s([w.s([w.s([], 'revs1', '( reverse ` <" P "> ) = <" P ">')], 'a1i', '( %s -> ( reverse ` <" P "> ) = <" P "> )' % A2)],
                      'oveq2d', '( %s -> ( ( reverse ` V ) ++ ( reverse ` <" P "> ) ) = ( ( reverse ` V ) ++ <" P "> ) )' % A2)], 'eqtrd',
             '( %s -> ( reverse ` %s ) = ( ( reverse ` V ) ++ <" P "> ) )' % (A2, CSV))
    sn = w.s([w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), rv, w.inst('mulallsnoc')], 'syl2anc',
             '( %s -> ( 1st ` ( Q MulAll ( ( reverse ` V ) ++ <" P "> ) ) ) = ( %s ++ <" ( P x. Q ) "> ) )' % (A2, MR('V')))
    l1 = w.s([w.s([w.s([r2], 'oveq2d', '( %s -> ( Q MulAll ( reverse ` %s ) ) = ( Q MulAll ( ( reverse ` V ) ++ <" P "> ) ) )' % (A2, CSV))],
                  'fveq2d', '( %s -> %s = ( 1st ` ( Q MulAll ( ( reverse ` V ) ++ <" P "> ) ) ) )' % (A2, MR(CSV))), sn], 'eqtrd',
             '( %s -> %s = ( %s ++ <" ( P x. Q ) "> ) )' % (A2, MR(CSV), MR('V')))
    l2 = w.s([l1, w.s([ihs], 'oveq1d', '( %s -> ( %s ++ <" ( P x. Q ) "> ) = ( %s ++ <" ( P x. Q ) "> ) )' % (A2, MR('V'), RMA('V')))], 'eqtrd',
             '( %s -> %s = ( %s ++ <" ( P x. Q ) "> ) )' % (A2, MR(CSV), RMA('V')))
    # the right side
    MV = '( 1st ` ( Q MulAll V ) )'
    PQ = '<" ( P x. Q ) ">'
    cs = w.s([w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('mulallcs')], 'syl2anc',
             '( %s -> ( Q MulAll %s ) = <. ( %s ++ %s ) , ( ( 2nd ` ( Q MulAll V ) ) + 1 ) >. )' % (A2, CSV, PQ, MV))
    cl = w.s([qn, vs, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll V ) e. %s )' % (A2, WN))
    a1, b1 = paircl(w, A2, '( Q MulAll V )', cl, 'Word NN0', 'NN0')
    pqn = w.s([pn, qn], 'nn0mulcld', '( %s -> ( P x. Q ) e. NN0 )' % A2)
    s1 = w.s([pqn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (A2, PQ))
    xa = w.s([s1, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. Word NN0 )' % (A2, PQ, MV))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll V ) ) + 1 ) e. NN0 )' % A2)
    p1 = projeq(w, A2, '( Q MulAll %s )' % CSV, cs, '( %s ++ %s )' % (PQ, MV), '( ( 2nd ` ( Q MulAll V ) ) + 1 )', xa, xb, 1)
    q1 = w.s([s1, a1, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ %s ) ) = ( ( reverse ` %s ) ++ ( reverse ` %s ) ) )' % (A2, PQ, MV, MV, PQ))
    q2 = w.s([q1, w.s([w.s([w.s([], 'revs1', '( reverse ` %s ) = %s' % (PQ, PQ))], 'a1i', '( %s -> ( reverse ` %s ) = %s )' % (A2, PQ, PQ))],
                      'oveq2d', '( %s -> ( ( reverse ` %s ) ++ ( reverse ` %s ) ) = ( ( reverse ` %s ) ++ %s ) )' % (A2, MV, PQ, MV, PQ))], 'eqtrd',
             '( %s -> ( reverse ` ( %s ++ %s ) ) = ( %s ++ %s ) )' % (A2, PQ, MV, RMA('V'), PQ))
    rr = w.s([w.s([p1], 'fveq2d', '( %s -> %s = ( reverse ` ( %s ++ %s ) ) )' % (A2, RMA(CSV), PQ, MV)), q2], 'eqtrd',
             '( %s -> %s = ( %s ++ %s ) )' % (A2, RMA(CSV), RMA('V'), PQ))
    w.qed([w.s([l2, rr], 'eqtr4d', '( %s -> %s = %s )' % (A2, MR(CSV), RMA(CSV)))], 'ex', '( %s -> %s )' % (A, co))


def _f_mr(w, st, phit):
    T = '( Q e. NN0 /\\ S e. Word NN0 )'
    sw = w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T)
    a = w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit))
    w.qed([w.s([], 'simpl', '( %s -> Q e. NN0 )' % T), a], 'mpd', '( %s -> %s = %s )' % (T, MR('S'), RMA('S')))


STMTS['mulallrev'] = '( ( Q e. NN0 /\\ S e. Word NN0 ) -> %s = %s )' % (MR('S'), RMA('S'))

# ======================================================================= the exact cost of divisorsOf
DOF = lambda s: '( DivisorsOf ` %s )' % s
PHI_DC = '( ( 2nd ` %s ) + 1 ) = ( 2 ^ ( # ` s ) )' % DOF('s')


def _b_dc(w, goal):
    e1 = w.s([w.s([], 'divisorsof0', '%s = <. <" 1 "> , 0 >.' % DOF('(/)'))], 'fveq2i', '( 2nd ` %s ) = ( 2nd ` <. <" 1 "> , 0 >. )' % DOF('(/)'))
    e2 = w.s([w.s([w.s([], 's1cli', '<" 1 "> e. Word _V')], 'elexi', '<" 1 "> e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. <" 1 "> , 0 >. ) = 0')
    e3 = w.s([w.s([e1, e2], 'eqtri', '( 2nd ` %s ) = 0' % DOF('(/)'))], 'oveq1i', '( ( 2nd ` %s ) + 1 ) = ( 0 + 1 )' % DOF('(/)'))
    e4 = w.s([e3, w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'eqtri', '( ( 2nd ` %s ) + 1 ) = 1' % DOF('(/)'))
    f1 = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'oveq2i', '( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 )')
    f2 = w.s([f1, w.s([], 'exp0', '') if False else w.s([w.s([], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')], 'eqtri', '( 2 ^ ( # ` (/) ) ) = 1')
    w.qed([e4, f2], 'eqtr4i', goal)


def _s_dc(w, A, ih, co):
    vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    DV = '( 1st ` %s )' % DOF('V')
    MV = '( P MulAll %s )' % DV
    cs = w.s([pn, vs, w.inst('divisorsofcs')], 'syl2anc', '( %s -> %s = <. ( %s ++ ( 1st ` %s ) ) , ( ( 2nd ` %s ) + ( 2nd ` %s ) ) >. )'
             % (A, DOF(CSV), DV, MV, DOF('V'), MV))
    cl = w.s([vs, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. %s )' % (A, DOF('V'), WN))
    a1, b1 = paircl(w, A, DOF('V'), cl, 'Word NN0', 'NN0')
    clm = w.s([pn, a1, w.inst('mulallcl')], 'syl2anc', '( %s -> %s e. %s )' % (A, MV, WN))
    a2, b2 = paircl(w, A, MV, clm, 'Word NN0', 'NN0')
    xa = w.s([a1, a2, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ ( 1st ` %s ) ) e. Word NN0 )' % (A, DV, MV))
    xb = w.s([b1, b2], 'nn0addcld', '( %s -> ( ( 2nd ` %s ) + ( 2nd ` %s ) ) e. NN0 )' % (A, DOF('V'), MV))
    p2 = projeq(w, A, DOF(CSV), cs, '( %s ++ ( 1st ` %s ) )' % (DV, MV), '( ( 2nd ` %s ) + ( 2nd ` %s ) )' % (DOF('V'), MV), xa, xb, 2)
    mc = w.s([pn, a1, w.inst('mulallcost')], 'syl2anc', '( %s -> ( 2nd ` %s ) = ( # ` %s ) )' % (A, MV, DV))
    dl = w.s([vs, w.inst('divisorsoflen')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` V ) ) )' % (A, DV))
    c2 = w.s([mc, dl], 'eqtrd', '( %s -> ( 2nd ` %s ) = ( 2 ^ ( # ` V ) ) )' % (A, MV))
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A, CSV))
    from lin import lineq
    from cl import Closure
    cl_ = Closure(w, A, {})
    cl_.leaf('( 2nd ` %s )' % DOF('V'), 'NN0', b1)
    cl_.leaf('( 2nd ` %s )' % MV, 'NN0', b2)
    cl_.leaf('( 2 ^ ( # ` V ) )', 'NN0', w.s([w.s([], '2nn0' if False else '2nn0', '2 e. NN0') if False else
                                                 w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A),
                                                 w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A)], 'nn0expcld',
                                                '( %s -> ( 2 ^ ( # ` V ) ) e. NN0 )' % A))
    ex1 = w.s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A), w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A)],
              'expp1d', '( %s -> ( 2 ^ ( ( # ` V ) + 1 ) ) = ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % A)
    e = lineq(w, A, '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (DOF('V'), MV), '( ( 2 ^ ( # ` V ) ) x. 2 )',
              hyps=[ihs, c2], closure=cl_, atoms=['( 2nd ` %s )' % DOF('V'), '( 2nd ` %s )' % MV, '( 2 ^ ( # ` V ) )'], products=True)
    l = w.s([w.s([p2], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) )' % (A, DOF(CSV), DOF('V'), MV)), e], 'eqtrd',
            '( %s -> ( ( 2nd ` %s ) + 1 ) = ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % (A, DOF(CSV)))
    r = w.s([w.s([lc], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = ( 2 ^ ( ( # ` V ) + 1 ) ) )' % (A, CSV)), ex1], 'eqtrd',
            '( %s -> ( 2 ^ ( # ` %s ) ) = ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % (A, CSV))
    w.qed([l, r], 'eqtr4d', '( %s -> %s )' % (A, co))


STMTS['divisorsofcsteq'] = '( S e. Word NN0 -> %s )' % subst(PHI_DC, 's', 'S')

if __name__ == '__main__':
    family(run, 'mulallsnoc', PHI_MS, _b, _s, finish=_f_ms,
           desc='mulAll of a list with one more entry: the products with one more product (Lean ` mulAll_fst ` , ` List.map_append ` ).',
           only=only or ['-'])
    family(run, 'mulallrev', PHI_MR, _b_mr, _s_mr, finish=_f_mr,
           desc='mulAll commutes with reverse (Lean ` mulAll_fst ` , ` List.map_reverse ` ).', only=only or ['-'])
    family(run, 'divisorsofcsteq', PHI_DC, _b_dc, _s_dc,
           desc='The exact cost of divisorsOf: ` ( divisorsOf Q ).2 + 1 = 2 ^ # Q ` (Lean ` divisorsOf_snd ` ).', only=only or ['-'])
