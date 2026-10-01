"""T9: the budget lemmas of Step4.lean ( ` exPreC_le ` , ` exSomeC_le ` ).

  tmexprec    Lean ` exPreC_le ` : ` exPreC L N b + 1 <_ 7 exY L Nb X `
  tmexsomec   Lean ` exSomeC_le ` : ` exSomeC L ( N + 1 ) b sl bM <_ 13 exY L Nb X `

    MM_DB=sorties/t9.mm python3 tools/gen/t9_k_arith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import num

SEL = sys.argv[1:]
EXY = '( ( ( ( L + 1 ) ^ 2 ) x. ( H + 2 ) ) x. ( TMB ` Q ) )'
T_PC = (('L e. NN0', 'N e. NN0', 'H e. NN0'), ('B e. NN0', 'Q e. NN0'), ('( N + 1 ) <_ H', 'B <_ Q'))
ST_PC = '( %s -> ( %s + 1 ) <_ ( 7 x. %s ) )' % (cj(T_PC), EXPREC('L', 'N', 'B'), EXY)
T_SC = (('L e. NN0', 'N e. NN0', 'H e. NN0'), ('B e. NN0', 'O e. NN0', 'Q e. NN0'),
        (('S e. NN0', 'S <_ ( N + 1 )'), ('( N + 1 ) <_ H', 'B <_ Q'), ('O <_ Q', '( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q')))
ST_SC = '( %s -> %s <_ ( ; 1 3 x. %s ) )' % (cj(T_SC), EXSOMEC('L', '( N + 1 )', 'B', 'S', 'O'), EXY)


class Ar:
    def __init__(self, w, ph, T, nn0s):
        self.w, self.ph = w, ph
        self.c = c = Ctx(w, ph, T)
        self.cl = Closure(w, ph, {v: ('NN0', c['%s e. NN0' % v]) for v in nn0s})
        s = w.s
        for v in nn0s:
            pass

    def tmb(self, b, bn=None):
        """( TMB ` b ) as an NN0 leaf"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        T = '( TMB ` %s )' % b
        if T not in getattr(cl, '_t9tmb', set()):
            bn = bn or cl.mem(b, 'NN0')
            cl.leaf(T, 'NN0', s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, T))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, T)))
            cl._t9tmb = getattr(cl, '_t9tmb', set()) | {T}
        return T

    def mono(self, b, q, ble):
        """( ph -> ( TMB ` b ) <_ ( TMB ` q ) )"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        return s([cl.mem(b, 'NN0'), cl.mem(q, 'NN0'), ble, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` %s ) <_ ( TMB ` %s ) )' % (ph, b, q))

    def mul12(self, A, B, C, D, ab, cd):
        """( ph -> ( A x. C ) <_ ( B x. D ) ) for nonneg A C"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        return s([cl.mem(A, 'RR'), cl.mem(B, 'RR'), cl.mem(C, 'RR'), cl.mem(D, 'RR'), cl.ge0(A), cl.ge0(C), ab, cd], 'lemul12ad',
                 '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A, C, B, D))

    def l1l2(self):
        """( ph -> ( L + 1 ) <_ ( ( L + 1 ) ^ 2 ) )"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        L1, L2 = '( L + 1 )', '( ( L + 1 ) ^ 2 )'
        sq = s([cl.mem(L1, 'CC')], 'sqvald', '( %s -> %s = ( %s x. %s ) )' % (ph, L2, L1, L1))
        one = linarith(w, ph, [cl.ge0('L')], '1 <_ %s' % L1, closure=cl)
        m = self.mul12('1', L1, L1, L1, one, s([cl.mem(L1, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (ph, L1, L1)))
        return linarith(w, ph, [m, sq], '%s <_ %s' % (L1, L2), closure=cl, atoms=[L1, L2, '( %s x. %s )' % (L1, L1)])

    def t16(self, b):
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        T = self.tmb(b)
        l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
        qd = s([cl.mem(b, 'NN0'), closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
               '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, b, T))
        return qd, nlinarith(w, ph, [qd, cl.ge0(b)], '( %s + 2 ) <_ %s' % (b, T), closure=cl, atoms=[b, T])


def exy_facts(A):
    """EXY >= TMB Q , EXY >= 16"""
    w, ph, s, cl = A.w, A.ph, A.w.s, A.cl
    TQ = A.tmb('Q')
    L2H = '( ( ( L + 1 ) ^ 2 ) x. ( H + 2 ) )'
    one = nlinarith(w, ph, [cl.ge0('L'), cl.ge0('H')], '1 <_ %s' % L2H, closure=cl) if False else None
    l1 = linarith(w, ph, [cl.ge0('L')], '1 <_ ( L + 1 )', closure=cl)
    l2 = A.mul12('1', '( L + 1 )', '1', '( L + 1 )', l1, l1)
    sq = s([cl.mem('( L + 1 )', 'CC')], 'sqvald', '( %s -> ( ( L + 1 ) ^ 2 ) = ( ( L + 1 ) x. ( L + 1 ) ) )' % ph)
    l2b = linarith(w, ph, [l2, sq], '1 <_ ( ( L + 1 ) ^ 2 )', closure=cl, atoms=['( ( L + 1 ) ^ 2 )', '( ( L + 1 ) x. ( L + 1 ) )'])
    h2 = linarith(w, ph, [cl.ge0('H')], '1 <_ ( H + 2 )', closure=cl)
    lh = A.mul12('1', '( ( L + 1 ) ^ 2 )', '1', '( H + 2 )', l2b, h2)
    lh1 = linarith(w, ph, [lh], '1 <_ %s' % L2H, closure=cl, atoms=[L2H])
    ey = A.mul12('1', L2H, TQ, TQ, lh1, s([cl.mem(TQ, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (ph, TQ, TQ)))
    eyq = linarith(w, ph, [ey], '%s <_ %s' % (TQ, EXY), closure=cl, atoms=[TQ, EXY])
    return eyq, lh1, l2b


def tmexprec():
    lab = 'tmexprec'
    ph = cj(T_PC)
    w = W(lab, 'Lean\'s ` exPreC_le ` : the budget of ` exPre ` plus one is at most ` 7 exY L Nb X ` when ` N + 1 <_ Nb ` and '
               '` b <_ X ` .')
    s = w.s
    A = Ar(w, ph, T_PC, ['L', 'N', 'H', 'B', 'Q'])
    c, cl = A.c, A.cl
    TB, TQ = A.tmb('B'), A.tmb('Q')
    mono = A.mono('B', 'Q', c['B <_ Q'])
    eyq, lh1, _ = exy_facts(A)
    ll = A.l1l2()
    L1, L2 = '( L + 1 )', '( ( L + 1 ) ^ 2 )'
    n2 = linarith(w, ph, [c['( N + 1 ) <_ H']], '( N + 2 ) <_ ( H + 2 )', closure=cl)
    n3 = linarith(w, ph, [c['( N + 1 ) <_ H']], '( ( N + 1 ) + 2 ) <_ ( H + 2 )', closure=cl)
    a1 = A.mul12(L1, L2, '( N + 2 )', '( H + 2 )', ll, n2)
    t1 = A.mul12('( %s x. ( N + 2 ) )' % L1, '( %s x. ( H + 2 ) )' % L2, TB, TQ, a1, mono)
    a2 = A.mul12(L2, L2, '( N + 2 )', '( H + 2 )', s([cl.mem(L2, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (ph, L2, L2)), n2)
    t2 = A.mul12('( %s x. ( N + 2 ) )' % L2, '( %s x. ( H + 2 ) )' % L2, TB, TQ, a2, mono)
    a6 = A.mul12(L1, L2, '( ( N + 1 ) + 2 )', '( H + 2 )', ll, n3)
    t6 = A.mul12('( %s x. ( ( N + 1 ) + 2 ) )' % L1, '( %s x. ( H + 2 ) )' % L2, TB, TQ, a6, mono)
    _, q16 = A.t16('Q')
    T1 = '( ( %s x. ( N + 2 ) ) x. %s )' % (L1, TB)
    T2 = '( ( %s x. ( N + 2 ) ) x. %s )' % (L2, TB)
    T6 = '( ( %s x. ( ( N + 1 ) + 2 ) ) x. %s )' % (L1, TB)
    le = linarith(w, ph, [t1, t2, t6, mono, eyq, q16, cl.ge0('Q')], '( %s + 1 ) <_ ( 7 x. %s )' % (EXPREC('L', 'N', 'B'), EXY), closure=cl,
                  atoms=[T1, T2, T6, TB, TQ, EXY])
    qed_as(w, le, ST_PC)
    return w.run()


def tmexsomec():
    lab = 'tmexsomec'
    ph = cj(T_SC)
    w = W(lab, 'Lean\'s ` exSomeC_le ` : the budget of ` exSome ` after a DP step (table bound ` N + 1 ` , witness of length '
               '` sl <_ N + 1 ` ) is at most ` 13 exY L Nb X ` when ` N + 1 <_ Nb ` , ` b , bM <_ X ` and ` 2 ( Nb + 2 ) b + 4 <_ X ` .')
    s = w.s
    A = Ar(w, ph, T_SC, ['L', 'N', 'H', 'B', 'O', 'Q', 'S'])
    c, cl = A.c, A.cl
    TB, TQ, TO = A.tmb('B'), A.tmb('Q'), A.tmb('O')
    ARG = '( ( ( 2 x. ( S + 1 ) ) x. B ) + 4 )'
    TA = A.tmb(ARG)
    L1, L2 = '( L + 1 )', '( ( L + 1 ) ^ 2 )'
    L2H = '( %s x. ( H + 2 ) )' % L2
    mb = A.mono('B', 'Q', c['B <_ Q'])
    mo = A.mono('O', 'Q', c['O <_ Q'])
    sb = A.mul12('( 2 x. ( S + 1 ) )', '( 2 x. ( H + 2 ) )', 'B', 'B',
                 linarith(w, ph, [c['S <_ ( N + 1 )'], c['( N + 1 ) <_ H']], '( 2 x. ( S + 1 ) ) <_ ( 2 x. ( H + 2 ) )', closure=cl),
                 s([cl.mem('B', 'RR')], 'leidd', '( %s -> B <_ B )' % ph))
    ale = linarith(w, ph, [sb, c['( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q']], '%s <_ Q' % ARG, closure=cl,
                   atoms=['( ( 2 x. ( S + 1 ) ) x. B )', '( ( 2 x. ( H + 2 ) ) x. B )'])
    ma = A.mono(ARG, 'Q', ale)
    eyq, lh1, l2ge1 = exy_facts(A)
    ll = A.l1l2()
    # ( S + 1 ) <_ L2H
    s1h = linarith(w, ph, [c['S <_ ( N + 1 )'], c['( N + 1 ) <_ H']], '( S + 1 ) <_ ( H + 2 )', closure=cl)
    sh = A.mul12('1', L2, '( S + 1 )', '( H + 2 )', l2ge1, s1h)
    shl = linarith(w, ph, [sh], '( S + 1 ) <_ %s' % L2H, closure=cl, atoms=[L2H])
    hh = A.mul12('( S + 1 )', L2H, TA, TQ, shl, ma)
    hi = A.mul12('( S + 1 )', L2H, TB, TQ, shl, mb)
    # ( L + 1 ) <_ L2H
    lhh = A.mul12(L1, L2, '1', '( H + 2 )', ll, linarith(w, ph, [cl.ge0('H')], '1 <_ ( H + 2 )', closure=cl))
    lhl = linarith(w, ph, [lhh], '%s <_ %s' % (L1, L2H), closure=cl, atoms=[L2H])
    hk = A.mul12(L1, L2H, TB, TQ, lhl, mb)
    # hj : L ( ( N + 1 ) ( B + 1 ) + 1 ) + 2 <_ EXY
    qb, b2 = A.t16('B')
    b2q = linarith(w, ph, [b2, mb], '( B + 2 ) <_ %s' % TQ, closure=cl, atoms=[TB, TQ])
    n3 = linarith(w, ph, [c['( N + 1 ) <_ H']], '( ( N + 1 ) + 2 ) <_ ( H + 2 )', closure=cl)
    X_ = '( ( ( N + 1 ) x. ( B + 1 ) ) + 1 )'
    Y_ = '( ( ( N + 1 ) + 2 ) x. ( B + 2 ) )'
    xy = linarith(w, ph, [cl.ge0('N'), cl.ge0('B')], '%s <_ %s' % (X_, Y_), closure=cl, products=True)
    y6 = A.mul12('3', '( ( N + 1 ) + 2 )', '2', '( B + 2 )', linarith(w, ph, [cl.ge0('N')], '3 <_ ( ( N + 1 ) + 2 )', closure=cl),
                 linarith(w, ph, [cl.ge0('B')], '2 <_ ( B + 2 )', closure=cl))
    lxy = s([cl.mem(X_, 'RR'), cl.mem(Y_, 'RR'), cl.mem('L', 'RR'), cl.ge0('L'), xy], 'lemul2ad', '( %s -> ( L x. %s ) <_ ( L x. %s ) )' % (ph, X_, Y_))
    dd = s([cl.mem('L', 'CC'), closed(w, ph, 'ax-1cn', '1 e. CC'), cl.mem(Y_, 'CC')], 'adddird',
           '( %s -> ( ( L + 1 ) x. %s ) = ( ( L x. %s ) + ( 1 x. %s ) ) )' % (ph, Y_, Y_, Y_))
    d1 = s([cl.mem(Y_, 'CC')], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (ph, Y_, Y_))
    HQ = '( ( H + 2 ) x. %s )' % TQ
    yq = A.mul12('( ( N + 1 ) + 2 )', '( H + 2 )', '( B + 2 )', TQ, n3, b2q)
    D_ = A.mul12(L1, L2, Y_, HQ, ll, yq)
    ma_ = s([cl.mem(L2, 'CC'), cl.mem('( H + 2 )', 'CC'), cl.mem(TQ, 'CC')], 'mulassd', '( %s -> %s = ( %s x. %s ) )' % (ph, EXY, L2, HQ))
    J = '( ( L x. ( ( ( N + 1 ) x. ( B + 1 ) ) + 1 ) ) + 2 )'
    six = s([s([s([], '3t2e6', '( 3 x. 2 ) = 6')], 'a1i', '( %s -> ( 3 x. 2 ) = 6 )' % ph), y6], 'eqbrtrrd', '( %s -> 6 <_ %s )' % (ph, Y_))
    LY1 = '( ( L + 1 ) x. %s )' % Y_
    j1 = linarith(w, ph, [lxy, dd, d1, six], '%s <_ %s' % (J, LY1), closure=cl,
                  atoms=['( L x. %s )' % X_, '( L x. %s )' % Y_, Y_, '( 1 x. %s )' % Y_, LY1])
    D2 = s([D_, s([ma_], 'eqcomd', '( %s -> ( %s x. %s ) = %s )' % (ph, L2, HQ, EXY))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, LY1, EXY))
    hj = s([cl.mem(J, 'RR'), cl.mem(LY1, 'RR'), cl.mem(EXY, 'RR'), j1, D2], 'letrd', '( %s -> %s <_ %s )' % (ph, J, EXY))
    # the sum
    HH = '( ( S + 1 ) x. %s )' % TA
    HI = '( ( S + 1 ) x. %s )' % TB
    HK = '( %s x. %s )' % (L1, TB)
    qdq, q16 = A.t16('Q')
    s16 = nlinarith(w, ph, [qdq, cl.ge0('Q')], '; 1 6 <_ %s' % TQ, closure=cl, atoms=['Q', TQ])
    le = linarith(w, ph, [hh, hi, hk, hj, mo, mb, eyq, s16, cl.ge0('Q')], '%s <_ ( ; 1 3 x. %s )' % (EXSOMEC('L', '( N + 1 )', 'B', 'S', 'O'), EXY),
                  closure=cl, atoms=[HH, HI, HK, J, TB, TO, TQ, EXY])
    qed_as(w, le, ST_SC)
    return w.run()


STMTS = {'tmexprec': ST_PC, 'tmexsomec': ST_SC}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
