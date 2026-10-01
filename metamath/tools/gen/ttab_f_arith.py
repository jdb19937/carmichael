"""T-TAB: the budget arithmetic of Table.lean's ` _le_B ` wrappers at the N level
(blueprint D7): ~ ttabsetm (` setC_mono_left `), ~ ttabsetle (` setC_le ` at
` N + 1 ` , ` m = 2 b ` : Lean's ` h1 ` in ` dpC_le `), ~ ttablkb
(` lookC_le_B `), ~ ttabcpb (` copyC_le_B `), ~ ttabdpc (` dpC_le `)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from cl import Closure
from lin import linarith, nlinarith, lineq

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def ge0(w, ph, c, X):
    return w.s([c.mem(X, 'NN0')], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, X))


def lemul1(w, ph, c, A, B, C, le):
    """( ph -> ( A x. C ) <_ ( B x. C ) ) from le : ( ph -> A <_ B ), C a nonnegative closure term"""
    return w.s([c.mem(A, 'RR'), c.mem(B, 'RR'), c.mem(C, 'RR'), ge0(w, ph, c, C), le], 'lemul1ad',
               '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A, C, B, C))


def lemul2(w, ph, c, A, B, C, le):
    """( ph -> ( C x. A ) <_ ( C x. B ) ) from le : ( ph -> A <_ B ), C a nonnegative closure term"""
    return w.s([c.mem(A, 'RR'), c.mem(B, 'RR'), c.mem(C, 'RR'), ge0(w, ph, c, C), le], 'lemul2ad',
               '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, C, A, C, B))


def ttabsetm():
    lab = 'ttabsetm'
    ph = "( ( J e. NN0 /\\ J' e. NN0 /\\ J <_ J' ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ M e. NN0 ) )"
    w = W(lab, 'The step bound ` setC j N b m ` of ` setIfNoneF ` (TM/Table.lean) is monotone in the index ` j ` .  '
               'Lean: ` setC_mono_left ` .')
    c0 = Ctx(w, ph, (("J e. NN0", "J' e. NN0", "J <_ J'"), ('N e. NN0', 'B e. NN0', 'M e. NN0')))
    c = Closure(w, ph, leaves={x: c0['%s e. NN0' % x] for x in ('J', "J'", 'N', 'B', 'M')})
    X = '( ( ( 2 x. %s ) + ( 4 x. M ) ) + ; 1 1 )' % SLOT()
    jx = lemul1(w, ph, c, 'J', "J'", X, c0["J <_ J'"])
    linarith(w, ph, [jx], '%s <_ %s' % (SETC('J', 'N', 'B', 'M'), SETC("J'", 'N', 'B', 'M')), closure=c, name='qed',
             atoms=['( J x. %s )' % X, "( J' x. %s )" % X])
    return w.run()


def base(w, lab, ph, names):
    c0 = Ctx(w, ph, tuple('%s e. NN0' % x for x in names))
    c = Closure(w, ph, leaves={x: c0['%s e. NN0' % x] for x in names})
    return c0, c


def distr(w, ph, c, J, A, W_):
    """( ph -> ( ( ( J + 1 ) x. A ) x. W_ ) = ( ( J x. ( A x. W_ ) ) + ( A x. W_ ) ) )"""
    jc, ac, wc = c.mem(J, 'CC'), c.mem(A, 'CC'), c.mem(W_, 'CC')
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % ph)
    J1 = '( %s + 1 )' % J
    j1c = w.s([jc, onea], 'addcld', '( %s -> %s e. CC )' % (ph, J1))
    AW = '( %s x. %s )' % (A, W_)
    awc = w.s([ac, wc], 'mulcld', '( %s -> %s e. CC )' % (ph, AW))
    e1 = w.s([j1c, ac, wc], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. %s ) )' % (ph, J1, A, W_, J1, AW))
    e2 = w.s([jc, onea, awc], 'adddird', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) + ( 1 x. %s ) ) )' % (ph, J1, AW, J, AW, AW))
    e3 = w.s([awc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (ph, AW, AW))
    e4 = w.s([e3], 'oveq2d', '( %s -> ( ( %s x. %s ) + ( 1 x. %s ) ) = ( ( %s x. %s ) + %s ) )' % (ph, J, AW, AW, J, AW, AW))
    e5 = w.s([e1, e2], 'eqtrd', '( %s -> ( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) + ( 1 x. %s ) ) )' % (ph, J1, A, W_, J, AW, AW))
    return w.s([e5, e4], 'eqtrd', '( %s -> ( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) + %s ) )' % (ph, J1, A, W_, J, AW, AW))


def ttabsetle():
    lab = 'ttabsetle'
    ph = '( J e. NN0 /\\ N e. NN0 /\\ B e. NN0 )'
    w = W(lab, 'The step bound of ` setIfNoneF ` at ` N + 1 ` entries per slot and index length ` 2 b ` (TM/Table.lean): '
               '` setC j ( N + 1 ) b ( 2 b ) <_ ( j + 1 ) ( N + 2 ) ( 16 b + 49 ) ` .  Lean: ` setC_le ` followed by the '
               'step ` h1 ` of ` dpC_le ` .')
    c0, c = base(w, lab, ph, ('J', 'N', 'B'))
    N1, M2 = '( N + 1 )', '( 2 x. B )'
    X = '( ( ( 2 x. %s ) + ( 4 x. %s ) ) + ; 1 1 )' % (SLOT(N1, 'B'), M2)
    Q = '( ( N + 2 ) x. ( ( ; 1 6 x. B ) + ; 4 9 ) )'
    g = [ge0(w, ph, c, v) for v in ('J', 'N', 'B')]
    nb = ge0(w, ph, c, '( N x. B )')
    h1 = linarith(w, ph, g + [nb], '%s <_ %s' % (X, Q), closure=c, products=True)
    h2 = lemul2(w, ph, c, X, Q, 'J', h1)
    h3 = linarith(w, ph, g + [nb], '( ( %s + ( 3 x. %s ) ) + ; 1 4 ) <_ %s' % (SLOT(N1, 'B'), M2, Q), closure=c, products=True)
    RHS = '( ( ( J + 1 ) x. ( N + 2 ) ) x. ( ( ; 1 6 x. B ) + ; 4 9 ) )'
    eq = distr(w, ph, c, 'J', '( N + 2 )', '( ( ; 1 6 x. B ) + ; 4 9 )')
    linarith(w, ph, [h2, h3, eq], '%s <_ %s' % (SETC('J', N1, 'B', M2), RHS),
             closure=c, name='qed', atoms=['( J x. %s )' % X, '( J x. %s )' % Q, Q, RHS, '( %s x. ( ( 4 x. B ) + ; 1 2 ) )' % N1])
    return w.run()


def tmblin64(w, ph, c, bnn):
    """( ph -> ( ; 6 4 x. ( B + 2 ) ) <_ ( TMB ` B ) )"""
    six4 = w.s([], '6nn0', '6 e. NN0'); f4 = w.s([], '4nn0', '4 e. NN0')
    d64 = w.s([six4, f4], 'deccl', '; 6 4 e. NN0')
    d64a = w.s([d64], 'a1i', '( %s -> ; 6 4 e. NN0 )' % ph)
    le = w.s([d64], 'nn0rei', '; 6 4 e. RR')
    lea = w.s([w.s([le], 'leidi', '; 6 4 <_ ; 6 4')], 'a1i', '( %s -> ; 6 4 <_ ; 6 4 )' % ph)
    return w.s([bnn, d64a, lea, w.inst('tmblin')], 'syl3anc', '( %s -> ( ; 6 4 x. ( B + 2 ) ) <_ ( TMB ` B ) )' % ph)


def ttablkb_cpb(kind):
    lk = kind == 'lk'
    lab = 'ttablkb' if lk else 'ttabcpb'
    J = 'J' if lk else 'L'
    ph = '( %s e. NN0 /\\ N e. NN0 /\\ B e. NN0 )' % J
    if lk:
        desc = ('The step bound of ` lookupSlot ` at index length ` 2 b ` (TM/Table.lean) within the budget: '
                '` lookC j N b ( 2 b ) <_ ( j + 1 ) ( N + 2 ) B b ` .  Lean: ` lookC_le_B ` .')
    else:
        desc = ('The step bound of ` copyTbl ` (TM/Table.lean) within the budget: ` copyC L N b <_ ( L + 1 ) ( N + 2 ) B b ` .  '
                'Lean: ` copyC_le_B ` .')
    w = W(lab, desc)
    c0, c = base(w, lab, ph, (J, 'N', 'B'))
    tb = '( TMB ` B )'
    g = [ge0(w, ph, c, v) for v in (J, 'N', 'B')]
    nb = ge0(w, ph, c, '( N x. B )')
    L64 = '( ; 6 4 x. ( B + 2 ) )'
    t0 = tmblin64(w, ph, c, c0['B e. NN0'])
    tbn = w.s([c0['B e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, tb))
    tbr = w.s([tbn], 'nnred', '( %s -> %s e. RR )' % (ph, tb))
    c.leaf(tb, 'NN', tbn)
    n2 = c.mem('( N + 2 )', 'RR'); n2g = ge0(w, ph, c, '( N + 2 )')
    l64r = c.mem(L64, 'RR')
    t1 = w.s([l64r, tbr, n2, n2g, t0], 'lemul2ad', '( %s -> ( ( N + 2 ) x. %s ) <_ ( ( N + 2 ) x. %s ) )' % (ph, L64, tb))
    Q = '( ( N + 2 ) x. %s )' % tb
    Q64 = '( ( N + 2 ) x. %s )' % L64
    if lk:
        X = '( ( ( 2 x. %s ) + ( 4 x. ( 2 x. B ) ) ) + ; 1 1 )' % SLOT()
        REST = '( ( ( N x. ( ( 6 x. B ) + ; 1 7 ) ) + ( 3 x. ( 2 x. B ) ) ) + ; 2 2 )'
        GOAL = LOOKC('J', 'N', 'B', '( 2 x. B )')
    else:
        X = '( ( ( N x. ( ( 6 x. B ) + ; 1 7 ) ) + ( 2 x. %s ) ) + ; 1 5 )' % SLOT()
        REST = '8'
        GOAL = COPYC('L', 'N', 'B')
    h1 = linarith(w, ph, g + [nb], '%s <_ %s' % (X, Q64), closure=c, products=True)
    h1b = w.s([h1, t1], 'letrd', '( %s -> %s <_ %s )' % (ph, X, Q)) if False else None
    xr, q64r = c.mem(X, 'RR'), c.mem(Q64, 'RR')
    qr = w.s([n2, tbr], 'remulcld', '( %s -> %s e. RR )' % (ph, Q))
    h1b = w.s([xr, q64r, qr, h1, t1], 'letrd', '( %s -> %s <_ %s )' % (ph, X, Q))
    jr, jg = c.mem(J, 'RR'), ge0(w, ph, c, J)
    h2 = w.s([xr, qr, jr, jg, h1b], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, J, X, J, Q))
    h3 = linarith(w, ph, g + [nb], '%s <_ %s' % (REST, Q64), closure=c, products=True)
    RHS = '( ( ( %s + 1 ) x. ( N + 2 ) ) x. %s )' % (J, tb)
    eq = distr(w, ph, c, J, '( N + 2 )', tb)
    at = ['( %s x. %s )' % (J, X), '( %s x. %s )' % (J, Q), Q, Q64, RHS, tb]
    if lk:
        at.append('( N x. ( ( 6 x. B ) + ; 1 7 ) )')
    linarith(w, ph, [h2, h3, t1, eq], '%s <_ %s' % (GOAL, RHS), closure=c, name='qed', atoms=at)
    return w.run()


def ttabdpc():
    lab = 'ttabdpc'
    ph = '( L e. NN0 /\\ N e. NN0 /\\ B e. NN0 )'
    w = W(lab, 'The step bound of ` dpStepF ` (TM/Table.lean) within the budget: ` dpC L N b <_ ( L + 1 ) ^ 2 ( N + 2 ) B b ` , '
               'from ~ ttabsetle , ` 1 <_ ( L + 1 ) ( N + 2 ) ` , the quadratic bounds ` b ( 46 b + 60 ) + 49 b + 113 <_ 64 ( b + 2 ) ^ 2 ` '
               'and ` 72 b + 118 <_ 64 ( b + 2 ) ^ 2 ` , and ~ tmbquad .  Lean: ` dpC_le ` .')
    c0, c = base(w, lab, ph, ('L', 'N', 'B'))
    tb = '( TMB ` B )'
    tbn = w.s([c0['B e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, tb))
    c.leaf(tb, 'NN', tbn)
    N1, M2 = '( N + 1 )', '( 2 x. B )'
    SC = SETC('L', N1, 'B', M2)
    P = '( ( L + 1 ) x. ( N + 2 ) )'
    PRE = '( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 3 3 x. B ) ) + ; 6 4 )'
    DPB = DPBODYC('L', 'N', 'B')
    X16, X56, X72 = '( ( ; 1 6 x. B ) + ; 4 9 )', '( ( ; 5 6 x. B ) + ; 6 9 )', '( ( ; 7 2 x. B ) + ; ; 1 1 8 )'
    W2 = '( ; 6 4 x. ( ( B + 2 ) x. ( B + 2 ) ) )'
    PX = lambda X: '( %s x. %s )' % (P, X)
    g = {v: ge0(w, ph, c, v) for v in ('L', 'N', 'B')}
    # e1: setC L ( N + 1 ) b ( 2 b ) <_ P ( 16 b + 49 )
    e1 = w.s([c0['L e. NN0'], c0['N e. NN0'], c0['B e. NN0'], w.inst('ttabsetle')], 'syl3anc',
             '( %s -> %s <_ %s )' % (ph, SC, PX(X16)))
    scn = c.mem(SC, 'NN0'); c.leaf(SC, 'NN0', scn)
    # s2: 1 <_ P
    s2 = linarith(w, ph, [g['L'], g['N'], ge0(w, ph, c, '( L x. N )')], '1 <_ %s' % P, closure=c, products=True)
    s3 = lemul1(w, ph, c, '1', P, X56, s2)
    s4 = lemul1(w, ph, c, '1', P, PRE, s2)
    # e2: dpBodyC + 2 <_ P ( 72 b + 118 )
    x72 = lineq(w, ph, '( %s + %s )' % (X56, X16), X72, closure=c)
    pc_, x56c, x16c = c.mem(P, 'CC'), c.mem(X56, 'CC'), c.mem(X16, 'CC')
    dd = w.s([pc_, x56c, x16c], 'adddid', '( %s -> ( %s x. ( %s + %s ) ) = ( %s + %s ) )' % (ph, P, X56, X16, PX(X56), PX(X16)))
    dd2 = w.s([x72], 'oveq2d', '( %s -> ( %s x. ( %s + %s ) ) = %s )' % (ph, P, X56, X16, PX(X72)))
    dd3 = w.s([dd2, dd], 'eqtr3d', '( %s -> %s = ( %s + %s ) )' % (ph, PX(X72), PX(X56), PX(X16)))
    A1 = [PX(X56), PX(X16), PX(X72), SC]
    e2 = linarith(w, ph, [s3, e1, dd3], '( %s + 2 ) <_ %s' % (DPB, PX(X72)), closure=c, atoms=A1)
    e3 = lemul2(w, ph, c, '( %s + 2 )' % DPB, PX(X72), 'L', e2)
    # the quadratic bounds
    bb = ge0(w, ph, c, '( B x. B )')
    e5 = linarith(w, ph, [g['B'], bb], '( %s + %s ) <_ %s' % (PRE, X16, W2), closure=c, products=True)
    e6 = linarith(w, ph, [g['B'], bb], '%s <_ %s' % (X72, W2), closure=c, products=True)
    e7 = lemul2(w, ph, c, '( %s + %s )' % (PRE, X16), W2, P, e5)
    prec = c.mem(PRE, 'CC')
    e7q = w.s([pc_, prec, x16c], 'adddid', '( %s -> ( %s x. ( %s + %s ) ) = ( %s + %s ) )' % (ph, P, PRE, X16, PX(PRE), PX(X16)))
    e8 = lemul2(w, ph, c, X72, W2, P, e6)
    e9 = lemul2(w, ph, c, PX(X72), PX(W2), 'L', e8)
    Y1 = '( %s + ( L x. %s ) )' % (PX(W2), PX(W2))
    BPRE = '( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) )'
    A2 = [BPRE, SC, '( L x. ( %s + 2 ) )' % DPB, PX(PRE), PX(X16), '( %s x. ( %s + %s ) )' % (P, PRE, X16), PX(W2),
          '( L x. %s )' % PX(X72), '( L x. %s )' % PX(W2)]
    f1 = linarith(w, ph, [s4, e1, e3, e7q, e7, e9], '%s <_ %s' % (DPC('L', 'N', 'B'), Y1), closure=c, atoms=A2)
    # Y1 = ( ( ( L + 1 ) ^ 2 ) x. ( N + 2 ) ) x. W2
    d1 = distr(w, ph, c, 'L', P, W2)
    L1 = '( L + 1 )'
    d1c = w.s([d1, w.s([c.mem('( L x. %s )' % PX(W2), 'CC'), c.mem(PX(W2), 'CC')], 'addcomd',
                         '( %s -> ( ( L x. %s ) + %s ) = %s )' % (ph, PX(W2), PX(W2), Y1))], 'eqtrd',
              '( %s -> ( ( %s x. %s ) x. %s ) = %s )' % (ph, L1, P, W2, Y1))
    l1c, n2c = c.mem(L1, 'CC'), c.mem('( N + 2 )', 'CC')
    m1 = w.s([l1c, l1c, n2c], 'mulassd', '( %s -> ( ( %s x. %s ) x. ( N + 2 ) ) = ( %s x. %s ) )' % (ph, L1, L1, L1, P))
    sq = w.s([l1c], 'sqvald', '( %s -> ( %s ^ 2 ) = ( %s x. %s ) )' % (ph, L1, L1, L1))
    m2 = w.s([sq], 'oveq1d', '( %s -> ( ( %s ^ 2 ) x. ( N + 2 ) ) = ( ( %s x. %s ) x. ( N + 2 ) ) )' % (ph, L1, L1, L1))
    m3 = w.s([m2, m1], 'eqtrd', '( %s -> ( ( %s ^ 2 ) x. ( N + 2 ) ) = ( %s x. %s ) )' % (ph, L1, L1, P))
    Q2 = '( ( %s ^ 2 ) x. ( N + 2 ) )' % L1
    m4 = w.s([m3], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) x. %s ) )' % (ph, Q2, W2, L1, P, W2))
    m5 = w.s([m4, d1c], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (ph, Q2, W2, Y1))
    # W2 <_ TMB
    s64 = w.s([w.s([], '6nn0', '6 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '; 6 4 e. NN0')
    tq = w.s([c0['B e. NN0'], w.s([s64], 'a1i', '( %s -> ; 6 4 e. NN0 )' % ph),
              w.s([w.s([w.s([s64], 'nn0rei', '; 6 4 e. RR')], 'leidi', '; 6 4 <_ ; 6 4')], 'a1i', '( %s -> ; 6 4 <_ ; 6 4 )' % ph),
              w.inst('tmbquad')], 'syl3anc', '( %s -> ( ; 6 4 x. ( ( B + 2 ) ^ 2 ) ) <_ %s )' % (ph, tb))
    b2c = c.mem('( B + 2 )', 'CC')
    sqb = w.s([b2c], 'sqvald', '( %s -> ( ( B + 2 ) ^ 2 ) = ( ( B + 2 ) x. ( B + 2 ) ) )' % ph)
    sqb2 = w.s([sqb], 'oveq2d', '( %s -> ( ; 6 4 x. ( ( B + 2 ) ^ 2 ) ) = %s )' % (ph, W2))
    wt = w.s([sqb2, tq], 'eqbrtrrd', '( %s -> %s <_ %s )' % (ph, W2, tb))
    f4 = lemul2(w, ph, c, W2, tb, Q2, wt)
    y1r, q2wr, tr = c.mem(Y1, 'RR'), c.mem('( %s x. %s )' % (Q2, W2), 'RR'), c.mem('( %s x. %s )' % (Q2, tb), 'RR')
    f2 = w.s([m5, f4], 'eqbrtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (ph, Y1, Q2, tb))
    w.qed([c.mem(DPC('L', 'N', 'B'), 'RR'), y1r, tr, f1, f2], 'letrd', '( %s -> %s <_ ( %s x. %s ) )' % (ph, DPC('L', 'N', 'B'), Q2, tb))
    return w.run()


if __name__ == '__main__':
    if want('ttabdpc'): ttabdpc()
    if want('ttabsetm'): ttabsetm()
    if want('ttabsetle'): ttabsetle()
    if want('ttablkb'): ttablkb_cpb('lk')
    if want('ttabcpb'): ttablkb_cpb('cp')
