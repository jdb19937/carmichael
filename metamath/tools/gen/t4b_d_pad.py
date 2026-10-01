"""Sortie T4b, group D: the remaining Lean clauses of addBits, subBits,
subBorrow, cmpBits (T4-blueprint 3.6, T4b-blueprint 1.4): the fold-shift
lemmas, the cons clauses of subBits/subBorrow/cmpBits, the padding lemmas and
the padded clauses."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4blib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


FSET = '~P ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) )'
SH = lambda A, X: '( ( bToNat ` %s ) + ( 2 x. %s ) )' % (A, X)
PAD = lambda W: '( %s ++ <" (/) "> )' % W
VALS = {
    'addBits': lambda X, Y, C: '( ( %s bwrd %s ) ++ ( addCarry ` if ( ( 2 ^ %s ) <_ %s , 1o , (/) ) ) )' % (SUM(X, Y, C), MAX(X, Y), MAX(X, Y), SUM(X, Y, C)),
    'subBits': lambda X, Y, C: '( %s bwrd %s )' % (DIF(X, Y, C), MAX(X, Y)),
    'subBorrow': lambda X, Y, C: 'if ( ( toNat ` %s ) < ( ( toNat ` %s ) + ( bToNat ` %s ) ) , 1o , (/) )' % (X, Y, C),
    'cmpBits': lambda X, Y, C: 'if ( ( toNat ` %s ) = ( toNat ` %s ) , %s , ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) )' % (X, Y, C, X, Y),
}
VALREF = {'addBits': 'addbitsval', 'subBits': 'subbitsval', 'subBorrow': 'subborrowval', 'cmpBits': 'cmpbitsval'}
KINDC = {'addBits': '2o', 'subBits': '2o', 'subBorrow': '2o', 'cmpBits': '3o'}
HASMAX = {'addBits': True, 'subBits': True, 'subBorrow': False, 'cmpBits': False}
CONSRHS = {
    'addBits': lambda A, B, C, X, Y: '( <" %s "> ++ ( ( %s addBits %s ) ` %s ) )' % (OP3(A, 'sumBit', B, C), X, Y, OP3(A, 'majBit', B, C)),
    'subBits': lambda A, B, C, X, Y: '( <" %s "> ++ ( ( %s subBits %s ) ` %s ) )' % (OP3(A, 'sumBit', B, C), X, Y, OP3(A, 'borrow', B, C)),
    'subBorrow': lambda A, B, C, X, Y: '( ( %s subBorrow %s ) ` %s )' % (X, Y, OP3(A, 'borrow', B, C)),
    'cmpBits': lambda A, B, C, X, Y: '( ( %s cmpBits %s ) ` %s )' % (X, Y, OP3(A, 'cmpStep', B, C)),
}
CONSREF = {'addBits': 'addbitscons', 'subBits': 'subbitscons', 'subBorrow': 'subborrowcons', 'cmpBits': 'cmpbitscons'}
PADREF = {'addBits': ('addbitspad', 'addbitspad2'), 'subBits': ('subbitspad', 'subbitspad2'),
          'subBorrow': ('subborrowpad', 'subborrowpad2'), 'cmpBits': ('cmpbitspad', 'cmpbitspad2')}


def snoclen(w, cl, ante, Y):
    """( ante -> ( # ` ( Y ++ <" (/) "> ) ) = ( ( # ` Y ) + 1 ) )"""
    YP = PAD(Y)
    l = w.s([cl.mem(Y, 'Word 2o'), cl.mem('<" (/) ">', 'Word 2o'), w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` <" (/) "> ) ) )' % (ante, YP, Y))
    s1 = w.s([num.closed(w, [], 's1len', '( # ` <" (/) "> ) = 1')], 'a1i', '( %s -> ( # ` <" (/) "> ) = 1 )' % ante)
    o = w.s([s1], 'oveq2d', '( %s -> ( ( # ` %s ) + ( # ` <" (/) "> ) ) = ( ( # ` %s ) + 1 ) )' % (ante, Y, Y))
    return w.s([l, o], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (ante, YP, Y))


def bit_is(w, cl, ante, A, X, memA, I='0'):
    """( ante -> BIT( SH(A,X) , 0 ) = A ) for A e. 2o, X e. ZZ"""
    S = SH(A, X)
    bb = w.s([memA, cl.mem(X, 'ZZ'), w.inst('bwbit0')], 'syl2anc', '( %s -> ( 0 e. ( bits ` %s ) <-> %s = 1o ) )' % (ante, S, A))
    bi2 = w.s([bb], 'bicomd', '( %s -> ( %s = 1o <-> 0 e. ( bits ` %s ) ) )' % (ante, A, S))
    st = bool_from_bi(w, ante, A, '0 e. ( bits ` %s )' % S, bi2, memA)
    return w.s([st], 'eqcomd', '( %s -> %s = %s )' % (ante, BIT(S, '0'), A))


if __name__ == '__main__':
    if want('bwbitp1'):
        A = '( B e. 2o /\\ M e. ZZ /\\ I e. NN0 )'
        w = W('bwbitp1', 'Bit I + 1 of a number with a letter prepended is bit I of the number.')
        b = w.s([], 'simp1', '( %s -> B e. 2o )' % A); m = w.s([], 'simp2', '( %s -> M e. ZZ )' % A); i = w.s([], 'simp3', '( %s -> I e. NN0 )' % A)
        cl = Cl(w, A, {'B': ('2o', b), 'M': ('ZZ', m), 'I': ('NN0', i)})
        S = SH('B', 'M'); I1 = '( I + 1 )'
        def body(a2, eq, v):
            c2 = subcl(w, cl, A, a2)
            f = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` B ) = ( bToNat ` %s ) )' % (a2, v))
            lit = {'(/)': 'bwbn0', '1o': 'bwbn1'}[v]; val = {'(/)': '0', '1o': '1'}[v]
            f2 = w.s([f, w.s([num.closed(w, [], lit, '( bToNat ` %s ) = %s' % (v, val))], 'a1i', '( %s -> ( bToNat ` %s ) = %s )' % (a2, v, val))], 'eqtrd', '( %s -> ( bToNat ` B ) = %s )' % (a2, val))
            o = w.s([f2], 'oveq1d', '( %s -> %s = ( %s + ( 2 x. M ) ) )' % (a2, S, val))
            if v == '(/)':
                z = w.s([c2.mem('( 2 x. M )', 'CC')], 'addlidd', '( %s -> ( 0 + ( 2 x. M ) ) = ( 2 x. M ) )' % a2)
                TGT = '( 2 x. M )'; ref = 'bitsp1e'
            else:
                z = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % a2), c2.mem('( 2 x. M )', 'CC')], 'addcomd', '( %s -> ( 1 + ( 2 x. M ) ) = ( ( 2 x. M ) + 1 ) )' % a2)
                TGT = '( ( 2 x. M ) + 1 )'; ref = 'bitsp1o'
            o2 = w.s([o, z], 'eqtrd', '( %s -> %s = %s )' % (a2, S, TGT))
            e = w.s([o2], 'fveq2d', '( %s -> ( bits ` %s ) = ( bits ` %s ) )' % (a2, S, TGT))
            e2 = w.s([e], 'eleq2d', '( %s -> ( %s e. ( bits ` %s ) <-> %s e. ( bits ` %s ) ) )' % (a2, I1, S, I1, TGT))
            bp = w.s([lift(w, m, a2), lift(w, i, a2), w.inst(ref)], 'syl2anc', '( %s -> ( %s e. ( bits ` %s ) <-> I e. ( bits ` M ) ) )' % (a2, I1, TGT))
            return w.s([e2, bp], 'bitrd', '( %s -> ( %s e. ( bits ` %s ) <-> I e. ( bits ` M ) ) )' % (a2, I1, S))
        st = cases2o(w, A, 'B', b, body, '( %s e. ( bits ` %s ) <-> I e. ( bits ` M ) )' % (I1, S))
        promote(w, st); w.run()

    def foldshift(label, F, kindC, kindXY, clref, desc):
        AZ0 = '( ( A e. 2o /\\ B e. 2o /\\ C e. %s ) /\\ ( X e. %s /\\ Y e. %s ) )' % (kindC, kindXY, kindXY)
        w = W(label, desc)
        SA = SH('A', 'X'); SB = SH('B', 'Y'); CP = OP3('A', F, 'B', 'C')
        FP = lambda I: FOLD(F, SA, SB, 'C', I); FQ = lambda I: FOLD(F, 'X', 'Y', CP, I)
        P = lambda I: '%s = %s' % (FP('( %s + 1 )' % I), FQ(I))
        x0 = w.s([], 'id', '( x = 0 -> x = 0 )'); h1, _ = w.wcongr(P('x'), {'x': '0'}, 'x = 0', {'x': x0})
        xy = w.s([], 'id', '( x = y -> x = y )'); h2, _ = w.wcongr(P('x'), {'x': 'y'}, 'x = y', {'x': xy})
        xy1 = w.s([], 'id', '( x = ( y + 1 ) -> x = ( y + 1 ) )'); h3, _ = w.wcongr(P('x'), {'x': '( y + 1 )'}, 'x = ( y + 1 )', {'x': xy1})
        xI = w.s([], 'id', '( x = I -> x = I )'); h4, _ = w.wcongr(P('x'), {'x': 'I'}, 'x = I', {'x': xI})
        a = w.s([], 'simpl1', '( %s -> A e. 2o )' % AZ0); b = w.s([], 'simpl2', '( %s -> B e. 2o )' % AZ0); c = w.s([], 'simpl3', '( %s -> C e. %s )' % (AZ0, kindC))
        x = w.s([], 'simprl', '( %s -> X e. %s )' % (AZ0, kindXY)); y = w.s([], 'simprr', '( %s -> Y e. %s )' % (AZ0, kindXY))
        cl0 = Cl(w, AZ0, {'A': ('2o', a), 'B': ('2o', b), 'C': (kindC, c), 'X': (kindXY, x), 'Y': (kindXY, y)})
        fsd = w.s([num.closed(w, [], F + 'fs' if F != 'cmpStep' else 'cmpstepfs', '%s e. %s' % (F, FSET))], 'a1i', '( %s -> %s e. %s )' % (AZ0, F, FSET))
        c3 = cl0.mem('C', '3o'); cp3 = cl0.mem(CP, '3o')
        saz = cl0.mem(SA, 'ZZ'); sbz = cl0.mem(SB, 'ZZ'); xz = cl0.mem('X', 'ZZ'); yz = cl0.mem('Y', 'ZZ')
        af = w.s([w.s([saz, sbz], 'jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ ) )' % (AZ0, SA, SB)), w.s([fsd, c3], 'jca', '( %s -> ( %s e. %s /\\ C e. 3o ) )' % (AZ0, F, FSET))], 'jca', '( %s -> ( ( %s e. ZZ /\\ %s e. ZZ ) /\\ ( %s e. %s /\\ C e. 3o ) ) )' % (AZ0, SA, SB, F, FSET))
        afq = w.s([w.s([xz, yz], 'jca', '( %s -> ( X e. ZZ /\\ Y e. ZZ ) )' % AZ0), w.s([fsd, cp3], 'jca', '( %s -> ( %s e. %s /\\ %s e. 3o ) )' % (AZ0, F, FSET, CP))], 'jca', '( %s -> ( ( X e. ZZ /\\ Y e. ZZ ) /\\ ( %s e. %s /\\ %s e. 3o ) ) )' % (AZ0, F, FSET, CP))
        # base
        f0 = w.s([af, w.inst('bwfold0')], 'syl', '( %s -> %s = C )' % (AZ0, FP('0')))
        l0 = w.s([f0, c3], 'eqeltrd', '( %s -> %s e. 3o )' % (AZ0, FP('0')))
        zn = w.s([num.closed(w, [], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % AZ0)
        j0 = w.s([zn, l0], 'jca', '( %s -> ( 0 e. NN0 /\\ %s e. 3o ) )' % (AZ0, FP('0')))
        p1 = w.s([af, j0, w.inst('bwfoldp1')], 'syl2anc', '( %s -> %s = ( ( %s %s %s ) ` %s ) )' % (AZ0, FP('( 0 + 1 )'), BIT(SA, '0'), F, BIT(SB, '0'), FP('0')))
        ba = bit_is(w, cl0, AZ0, 'A', 'X', a); bb = bit_is(w, cl0, AZ0, 'B', 'Y', b)
        o = w.s([ba, bb], 'oveq12d', '( %s -> ( %s %s %s ) = ( A %s B ) )' % (AZ0, BIT(SA, '0'), F, BIT(SB, '0'), F))
        f1 = w.s([o, f0], 'fveq12d', '( %s -> ( ( %s %s %s ) ` %s ) = %s )' % (AZ0, BIT(SA, '0'), F, BIT(SB, '0'), FP('0'), CP))
        lhs0 = w.s([p1, f1], 'eqtrd', '( %s -> %s = %s )' % (AZ0, FP('( 0 + 1 )'), CP))
        q0 = w.s([afq, w.inst('bwfold0')], 'syl', '( %s -> %s = %s )' % (AZ0, FQ('0'), CP))
        base_ = w.s([lhs0, q0], 'eqtr4d', '( %s -> %s )' % (AZ0, P('0')))
        # step
        AY = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (AZ0, P('y'))
        ih = w.s([], 'simpr', '( %s -> %s )' % (AY, P('y'))); yn = w.s([], 'simplr', '( %s -> y e. NN0 )' % AY); az = w.s([], 'simpll', '( %s -> %s )' % (AY, AZ0))
        cly = Cl(w, AY, {'A': ('2o', lift(w, a, AY)), 'B': ('2o', lift(w, b, AY)), 'C': (kindC, lift(w, c, AY)), 'X': (kindXY, lift(w, x, AY)), 'Y': (kindXY, lift(w, y, AY)), 'y': ('NN0', yn)})
        Y1 = '( y + 1 )'; y1n = cly.mem(Y1, 'NN0')
        kx = 'ZZ' if F == 'borrow' else 'NN0'
        jl = w.s([cly.mem(SA, kx), cly.mem(SB, kx), lift(w, c, AY)], '3jca', '( %s -> ( %s e. %s /\\ %s e. %s /\\ C e. %s ) )' % (AY, SA, kx, SB, kx, kindC))
        lv = w.s([jl, y1n, w.inst(clref)], 'syl2anc', '( %s -> %s e. %s )' % (AY, FP(Y1), '2o' if F == 'borrow' else '3o'))
        if F == 'borrow':
            ss = w.s([num.closed(w, [], 'bw2oss3o', '2o C_ 3o')], 'a1i', '( %s -> 2o C_ 3o )' % AY)
            lv3 = w.s([ss, lv], 'sseldd', '( %s -> %s e. 3o )' % (AY, FP(Y1)))
        else:
            lv3 = lv
        aff = w.s([az, af], 'syl', '( %s -> ( ( %s e. ZZ /\\ %s e. ZZ ) /\\ ( %s e. %s /\\ C e. 3o ) ) )' % (AY, SA, SB, F, FSET))
        jy = w.s([y1n, lv3], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. 3o ) )' % (AY, Y1, FP(Y1)))
        p1 = w.s([aff, jy, w.inst('bwfoldp1')], 'syl2anc', '( %s -> %s = ( ( %s %s %s ) ` %s ) )' % (AY, FP('( %s + 1 )' % Y1), BIT(SA, Y1), F, BIT(SB, Y1), FP(Y1)))
        bpa = w.s([lift(w, a, AY), cly.mem('X', 'ZZ'), yn, w.inst('bwbitp1')], 'syl3anc', '( %s -> ( %s e. ( bits ` %s ) <-> y e. ( bits ` X ) ) )' % (AY, Y1, SA))
        bpb = w.s([lift(w, b, AY), cly.mem('Y', 'ZZ'), yn, w.inst('bwbitp1')], 'syl3anc', '( %s -> ( %s e. ( bits ` %s ) <-> y e. ( bits ` Y ) ) )' % (AY, Y1, SB))
        ia = w.s([bpa], 'ifbid', '( %s -> %s = %s )' % (AY, BIT(SA, Y1), BIT('X', 'y'))); ib = w.s([bpb], 'ifbid', '( %s -> %s = %s )' % (AY, BIT(SB, Y1), BIT('Y', 'y')))
        o = w.s([ia, ib], 'oveq12d', '( %s -> ( %s %s %s ) = ( %s %s %s ) )' % (AY, BIT(SA, Y1), F, BIT(SB, Y1), BIT('X', 'y'), F, BIT('Y', 'y')))
        f = w.s([o, ih], 'fveq12d', '( %s -> ( ( %s %s %s ) ` %s ) = ( ( %s %s %s ) ` %s ) )' % (AY, BIT(SA, Y1), F, BIT(SB, Y1), FP(Y1), BIT('X', 'y'), F, BIT('Y', 'y'), FQ('y')))
        jq = w.s([cly.mem('X', kx), cly.mem('Y', kx), cly.mem(CP, '2o' if F == 'borrow' else '3o')], '3jca', '( %s -> ( X e. %s /\\ Y e. %s /\\ %s e. %s ) )' % (AY, kx, kx, CP, '2o' if F == 'borrow' else '3o'))
        lq = w.s([jq, yn, w.inst(clref)], 'syl2anc', '( %s -> %s e. %s )' % (AY, FQ('y'), '2o' if F == 'borrow' else '3o'))
        if F == 'borrow':
            lq3 = w.s([ss, lq], 'sseldd', '( %s -> %s e. 3o )' % (AY, FQ('y')))
        else:
            lq3 = lq
        afqq = w.s([az, afq], 'syl', '( %s -> ( ( X e. ZZ /\\ Y e. ZZ ) /\\ ( %s e. %s /\\ %s e. 3o ) ) )' % (AY, F, FSET, CP))
        jyq = w.s([yn, lq3], 'jca', '( %s -> ( y e. NN0 /\\ %s e. 3o ) )' % (AY, FQ('y')))
        q1 = w.s([afqq, jyq, w.inst('bwfoldp1')], 'syl2anc', '( %s -> %s = ( ( %s %s %s ) ` %s ) )' % (AY, FQ(Y1), BIT('X', 'y'), F, BIT('Y', 'y'), FQ('y')))
        step = w.s([p1, f, q1], '3eqtr4d', '( %s -> %s )' % (AY, P(Y1)))
        st = w.s([h1, h2, h3, h4, base_, step], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (AZ0, P('I')))
        promote(w, st); w.run()

    if want('bwborrowshift'):
        foldshift('bwborrowshift', 'borrow', '2o', 'ZZ', 'bwborrowcl', 'The borrow fold of two numbers with a letter prepended, one position up, is the borrow fold of the numbers from the borrow of the two letters.')
    if want('bwcmpfshift'):
        foldshift('bwcmpfshift', 'cmpStep', '3o', 'NN0', 'bwcmpfcl', 'The verdict fold of two numbers with a letter prepended, one position up, is the verdict fold of the numbers from the verdict on the two letters (Lean: cmpStep_shift).')

    A5 = '( ( A e. 2o /\\ B e. 2o /\\ C e. 2o ) /\\ ( X e. Word 2o /\\ Y e. Word 2o ) )'
    A5o = '( ( A e. 2o /\\ B e. 2o /\\ C e. 3o ) /\\ ( X e. Word 2o /\\ Y e. Word 2o ) )'

    def cons_common(w, ante, kindC):
        a = w.s([], 'simpl1', '( %s -> A e. 2o )' % ante); b = w.s([], 'simpl2', '( %s -> B e. 2o )' % ante); c = w.s([], 'simpl3', '( %s -> C e. %s )' % (ante, kindC))
        x = w.s([], 'simprl', '( %s -> X e. Word 2o )' % ante); y = w.s([], 'simprr', '( %s -> Y e. Word 2o )' % ante)
        cl = Cl(w, ante, {'A': ('2o', a), 'B': ('2o', b), 'C': (kindC, c), 'X': ('Word 2o', x), 'Y': ('Word 2o', y)})
        XA = CONS('A', 'X'); YB = CONS('B', 'Y')
        ta = w.s([a, x, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = %s )' % (ante, XA, SH('A', TN('X'))))
        tb = w.s([b, y, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = %s )' % (ante, YB, SH('B', TN('Y'))))
        lx2 = conslen(w, cl, ante, 'A', 'X'); ly2 = conslen(w, cl, ante, 'B', 'Y')
        N1 = MAX(XA, YB); Nm = MAX('X', 'Y')
        # N1 = Nm + 1 : rewrite lengths to ( 1 + # ) form for bwmaxp1
        ac1 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ante), cl.mem(LEN('X'), 'CC')], 'addcomd', '( %s -> ( 1 + ( # ` X ) ) = ( ( # ` X ) + 1 ) )' % ante)
        ac2 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ante), cl.mem(LEN('Y'), 'CC')], 'addcomd', '( %s -> ( 1 + ( # ` Y ) ) = ( ( # ` Y ) + 1 ) )' % ante)
        lx3 = w.s([lx2, ac1], 'eqtr4d', '( %s -> ( # ` %s ) = ( 1 + ( # ` X ) ) )' % (ante, XA)); ly3 = w.s([ly2, ac2], 'eqtr4d', '( %s -> ( # ` %s ) = ( 1 + ( # ` Y ) ) )' % (ante, YB))
        st1, N1b = w.rewrite(N1, {LEN(XA): ('( 1 + ( # ` X ) )', lx3), LEN(YB): ('( 1 + ( # ` Y ) )', ly3)}, ante)
        mp = w.s([cl.mem(LEN('X'), 'NN0'), cl.mem(LEN('Y'), 'NN0'), w.inst('bwmaxp1')], 'syl2anc', '( %s -> %s = ( 1 + %s ) )' % (ante, N1b, Nm))
        com = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ante), cl.mem(Nm, 'CC')], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (ante, Nm, Nm))
        neq = w.s([st1, mp, com], '3eqtrd', '( %s -> %s = ( %s + 1 ) )' % (ante, N1, Nm))
        return cl, a, b, c, x, y, XA, YB, ta, tb, N1, Nm, neq

    if want('subbitscons'):
        w = W('subbitscons', 'Lean clause 4 of subBits: the difference of two words with a letter prepended is the sum bit followed by the difference of the tails with the borrow bit as borrow-in.')
        cl, a, b, c, x, y, XA, YB, ta, tb, N1, Nm, neq = cons_common(w, A5, '2o')
        s_ = OP3('A', 'sumBit', 'B', 'C'); b_ = OP3('A', 'borrow', 'B', 'C')
        ss = cl.mem(s_, '2o'); bb = cl.mem(b_, '2o')
        v1 = w.s([cl.mem(XA, 'Word 2o'), cl.mem(YB, 'Word 2o'), c, w.inst('subbitsval')], 'syl3anc', '( %s -> ( ( %s subBits %s ) ` C ) = %s )' % (A5, XA, YB, VALS['subBits'](XA, YB, 'C')))
        v2 = w.s([x, y, bb, w.inst('subbitsval')], 'syl3anc', '( %s -> ( ( X subBits Y ) ` %s ) = %s )' % (A5, b_, VALS['subBits']('X', 'Y', b_)))
        fs = w.s([a, b, c, w.inst('bwfullsub')], 'syl3anc', '( %s -> ( ( ( bToNat ` A ) - ( bToNat ` B ) ) - ( bToNat ` C ) ) = ( ( bToNat ` %s ) - ( 2 x. ( bToNat ` %s ) ) ) )' % (A5, s_, b_))
        for E in ('( toNat ` X )', '( toNat ` Y )', '( bToNat ` A )', '( bToNat ` B )', '( bToNat ` C )', '( bToNat ` %s )' % s_, '( bToNat ` %s )' % b_, '( toNat ` %s )' % XA, '( toNat ` %s )' % YB):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        D1 = DIF(XA, YB, 'C'); Dm = DIF('X', 'Y', b_)
        SF = '( ( bToNat ` %s ) + ( 2 x. %s ) )' % (s_, Dm)
        seq = lineq(w, A5, D1, SF, hyps=[ta, tb, fs], closure=cl)
        bw1 = w.s([seq, neq], 'oveq12d', '( %s -> %s = %s )' % (A5, BWRD(D1, N1), BWRD(SF, '( %s + 1 )' % Nm)))
        bc = w.s([cl.mem(SF, 'ZZ'), cl.mem(Nm, 'NN0'), w.inst('bwrdcons')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (A5, BWRD(SF, '( %s + 1 )' % Nm), BIT(SF, '0'), BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm)))
        dmz = cl.mem(Dm, 'ZZ')
        b0 = w.s([ss, dmz, w.inst('bwbit0')], 'syl2anc', '( %s -> ( 0 e. ( bits ` %s ) <-> %s = 1o ) )' % (A5, SF, s_))
        b0r = w.s([b0], 'bicomd', '( %s -> ( %s = 1o <-> 0 e. ( bits ` %s ) ) )' % (A5, s_, SF))
        sb = bool_from_bi(w, A5, s_, '0 e. ( bits ` %s )' % SF, b0r, ss)
        se2 = w.s([w.s([sb], 's1eqd', '( %s -> <" %s "> = <" %s "> )' % (A5, s_, BIT(SF, '0')))], 'eqcomd', '( %s -> <" %s "> = <" %s "> )' % (A5, BIT(SF, '0'), s_))
        fh = w.s([ss, dmz, w.inst('bwflhalf')], 'syl2anc', '( %s -> ( |_ ` ( %s / 2 ) ) = %s )' % (A5, SF, Dm))
        fh2 = w.s([fh], 'oveq1d', '( %s -> %s = %s )' % (A5, BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm), BWRD(Dm, Nm)))
        fh3 = w.s([fh2, v2], 'eqtr4d', '( %s -> %s = ( ( X subBits Y ) ` %s ) )' % (A5, BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm), b_))
        cc = w.s([se2, fh3], 'oveq12d', '( %s -> ( <" %s "> ++ %s ) = ( <" %s "> ++ ( ( X subBits Y ) ` %s ) ) )' % (A5, BIT(SF, '0'), BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm), s_, b_))
        c1 = w.s([v1, bw1, bc], '3eqtrd', '( %s -> ( ( %s subBits %s ) ` C ) = ( <" %s "> ++ %s ) )' % (A5, XA, YB, BIT(SF, '0'), BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm)))
        w.qed([c1, cc], 'eqtrd', '( %s -> ( ( %s subBits %s ) ` C ) = %s )' % (A5, XA, YB, CONSRHS['subBits']('A', 'B', 'C', 'X', 'Y'))); w.run()

    def foldcons(label, F, G, kindC, foldref, shiftref, desc):
        """the cons clause of G (subBorrow / cmpBits) from its fold form and the shift lemma of F"""
        ante = A5 if kindC == '2o' else A5o
        w = W(label, desc)
        cl, a, b, c, x, y, XA, YB, ta, tb, N1, Nm, neq = cons_common(w, ante, kindC)
        CP = OP3('A', F, 'B', 'C'); cpk = cl.mem(CP, kindC)
        tX = TN('X'); tY = TN('Y')
        v1 = w.s([cl.mem(XA, 'Word 2o'), cl.mem(YB, 'Word 2o'), c, w.inst(foldref)], 'syl3anc', '( %s -> ( ( %s %s %s ) ` C ) = %s )' % (ante, XA, G, YB, FOLD(F, TN(XA), TN(YB), 'C', N1)))
        st, new = w.rewrite(FOLD(F, TN(XA), TN(YB), 'C', N1), {TN(XA): (SH('A', tX), ta), TN(YB): (SH('B', tY), tb), N1: ('( %s + 1 )' % Nm, neq)}, ante)
        assert new == FOLD(F, SH('A', tX), SH('B', tY), 'C', '( %s + 1 )' % Nm), new
        kx = 'ZZ' if F == 'borrow' else 'NN0'
        j1 = w.s([w.s([a, b, c], '3jca', '( %s -> ( A e. 2o /\\ B e. 2o /\\ C e. %s ) )' % (ante, kindC)), w.s([cl.mem(tX, kx), cl.mem(tY, kx)], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ante, tX, kx, tY, kx))], 'jca',
                 '( %s -> ( ( A e. 2o /\\ B e. 2o /\\ C e. %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) )' % (ante, kindC, tX, kx, tY, kx))
        sh = w.s([j1, cl.mem(Nm, 'NN0'), w.inst(shiftref)], 'syl2anc', '( %s -> %s = %s )' % (ante, FOLD(F, SH('A', tX), SH('B', tY), 'C', '( %s + 1 )' % Nm), FOLD(F, tX, tY, CP, Nm)))
        v2 = w.s([x, y, cpk, w.inst(foldref)], 'syl3anc', '( %s -> ( ( X %s Y ) ` %s ) = %s )' % (ante, G, CP, FOLD(F, tX, tY, CP, Nm)))
        c1 = w.s([v1, st, sh], '3eqtrd', '( %s -> ( ( %s %s %s ) ` C ) = %s )' % (ante, XA, G, YB, FOLD(F, tX, tY, CP, Nm)))
        w.qed([c1, v2], 'eqtr4d', '( %s -> ( ( %s %s %s ) ` C ) = %s )' % (ante, XA, G, YB, CONSRHS[G]('A', 'B', 'C', 'X', 'Y'))); w.run()

    if want('subborrowcons'):
        foldcons('subborrowcons', 'borrow', 'subBorrow', '2o', 'subborrowfold', 'bwborrowshift', 'Lean clause 4 of subBorrow: the borrow-out of two words with a letter prepended is the borrow-out of the tails from the borrow of the two letters.')
    if want('cmpbitscons'):
        foldcons('cmpbitscons', 'cmpStep', 'cmpBits', '3o', 'cmpbitsfold', 'bwcmpfshift', 'Lean clause 4 of cmpBits: the verdict on two words with a letter prepended is the verdict on the tails from the verdict on the two letters.')

    # ---- padding
    if want('tonatpad'):
        AY = 'Y e. Word 2o'
        w = W('tonatpad', 'A false letter appended does not change the value of a bit word.')
        y = w.s([], 'id', '( %s -> Y e. Word 2o )' % AY)
        cl = Cl(w, AY, {'Y': ('Word 2o', y)})
        z = w.s([num.closed(w, [], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % AY)
        ts = w.s([y, z, w.inst('tonatsnoc')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( toNat ` Y ) + ( ( bToNat ` (/) ) x. ( 2 ^ ( # ` Y ) ) ) ) )' % (AY, PAD('Y')))
        b0 = w.s([num.closed(w, [], 'bwbn0', '( bToNat ` (/) ) = 0')], 'a1i', '( %s -> ( bToNat ` (/) ) = 0 )' % AY)
        o = w.s([b0], 'oveq1d', '( %s -> ( ( bToNat ` (/) ) x. ( 2 ^ ( # ` Y ) ) ) = ( 0 x. ( 2 ^ ( # ` Y ) ) ) )' % AY)
        m = w.s([cl.mem(P2(LEN('Y')), 'CC')], 'mul02d', '( %s -> ( 0 x. ( 2 ^ ( # ` Y ) ) ) = 0 )' % AY)
        o2 = w.s([w.s([o, m], 'eqtrd', '( %s -> ( ( bToNat ` (/) ) x. ( 2 ^ ( # ` Y ) ) ) = 0 )' % AY)], 'oveq2d', '( %s -> ( ( toNat ` Y ) + ( ( bToNat ` (/) ) x. ( 2 ^ ( # ` Y ) ) ) ) = ( ( toNat ` Y ) + 0 ) )' % AY)
        a0 = w.s([cl.mem(TN('Y'), 'CC')], 'addridd', '( %s -> ( ( toNat ` Y ) + 0 ) = ( toNat ` Y ) )' % AY)
        w.qed([ts, o2, a0], '3eqtrd', '( %s -> ( toNat ` %s ) = ( toNat ` Y ) )' % (AY, PAD('Y'))); w.run()
    A3 = '( X e. Word 2o /\\ Y e. Word 2o /\\ ( # ` Y ) < ( # ` X ) )'
    A3b = '( X e. Word 2o /\\ Y e. Word 2o /\\ ( # ` X ) < ( # ` Y ) )'
    if want('bwmaxpad'):
        w = W('bwmaxpad', 'Padding the shorter word does not change the larger length.')
        x = w.s([], 'simp1', '( %s -> X e. Word 2o )' % A3); y = w.s([], 'simp2', '( %s -> Y e. Word 2o )' % A3); lt = w.s([], 'simp3', '( %s -> ( # ` Y ) < ( # ` X ) )' % A3)
        cl = Cl(w, A3, {'X': ('Word 2o', x), 'Y': ('Word 2o', y)})
        HX = LEN('X'); HY = LEN('Y'); HY1 = '( %s + 1 )' % HY
        ln = snoclen(w, cl, A3, 'Y')
        st, cur = w.rewrite(MAX('X', PAD('Y')), {LEN(PAD('Y')): (HY1, ln)}, A3)
        assert cur == 'if ( %s <_ %s , %s , %s )' % (HX, HY1, HY1, HX), cur
        nl = w.s([cl.mem(HY, 'RR'), cl.mem(HX, 'RR')], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (A3, HY, HX, HX, HY))
        nle = w.s([lt, nl], 'mpbid', '( %s -> -. %s <_ %s )' % (A3, HX, HY))
        ir = w.s([nle], 'iffalsed', '( %s -> %s = %s )' % (A3, MAX('X', 'Y'), HX))
        zl = w.s([cl.mem(HY, 'ZZ'), cl.mem(HX, 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ %s ) )' % (A3, HY, HX, HY1, HX))
        le = w.s([lt, zl], 'mpbid', '( %s -> %s <_ %s )' % (A3, HY1, HX))
        cond = '%s <_ %s' % (HX, HY1)
        def bt(a1, h1):
            i = w.s([h1], 'iftrued', '( %s -> %s = %s )' % (a1, cur, HY1))
            t3 = w.s([lift(w, cl.mem(HX, 'RR'), a1), lift(w, cl.mem(HY1, 'RR'), a1), w.inst('letri3')], 'syl2anc', '( %s -> ( %s = %s <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (a1, HX, HY1, HX, HY1, HY1, HX))
            j = w.s([h1, lift(w, le, a1)], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (a1, HX, HY1, HY1, HX))
            e = w.s([j, t3], 'mpbird', '( %s -> %s = %s )' % (a1, HX, HY1))
            return w.s([i, e], 'eqtr4d', '( %s -> %s = %s )' % (a1, cur, HX))
        def bf(a2, h2):
            return w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, cur, HX))
        c = cases_if(w, A3, cond, bt, bf, '%s = %s' % (cur, HX))
        l = w.s([st, c], 'eqtrd', '( %s -> %s = %s )' % (A3, MAX('X', PAD('Y')), HX))
        w.qed([l, ir], 'eqtr4d', '( %s -> %s = %s )' % (A3, MAX('X', PAD('Y')), MAX('X', 'Y'))); w.run()
    if want('bwmaxpad2'):
        w = W('bwmaxpad2', 'Padding the shorter word does not change the larger length (mirror).')
        x = w.s([], 'simp1', '( %s -> X e. Word 2o )' % A3b); y = w.s([], 'simp2', '( %s -> Y e. Word 2o )' % A3b); lt = w.s([], 'simp3', '( %s -> ( # ` X ) < ( # ` Y ) )' % A3b)
        cl = Cl(w, A3b, {'X': ('Word 2o', x), 'Y': ('Word 2o', y)})
        HX = LEN('X'); HY = LEN('Y'); HX1 = '( %s + 1 )' % HX
        ln = snoclen(w, cl, A3b, 'X')
        st, cur = w.rewrite(MAX(PAD('X'), 'Y'), {LEN(PAD('X')): (HX1, ln)}, A3b)
        assert cur == 'if ( %s <_ %s , %s , %s )' % (HX1, HY, HY, HX1), cur
        zl = w.s([cl.mem(HX, 'ZZ'), cl.mem(HY, 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ %s ) )' % (A3b, HX, HY, HX1, HY))
        le = w.s([lt, zl], 'mpbid', '( %s -> %s <_ %s )' % (A3b, HX1, HY))
        i1 = w.s([le], 'iftrued', '( %s -> %s = %s )' % (A3b, cur, HY))
        le2 = w.s([cl.mem(HX, 'RR'), cl.mem(HY, 'RR'), lt], 'ltled', '( %s -> %s <_ %s )' % (A3b, HX, HY))
        i2 = w.s([le2], 'iftrued', '( %s -> %s = %s )' % (A3b, MAX('X', 'Y'), HY))
        l = w.s([st, i1], 'eqtrd', '( %s -> %s = %s )' % (A3b, MAX(PAD('X'), 'Y'), HY))
        w.qed([l, i2], 'eqtr4d', '( %s -> %s = %s )' % (A3b, MAX(PAD('X'), 'Y'), MAX('X', 'Y'))); w.run()

    def pad(label, F, side, desc):
        kindC = KINDC[F]; hasmax = HASMAX[F]
        base = '( X e. Word 2o /\\ Y e. Word 2o /\\ C e. %s )' % kindC
        if hasmax:
            ante = '( %s /\\ %s )' % (base, '( # ` Y ) < ( # ` X )' if side == 1 else '( # ` X ) < ( # ` Y )')
            x = w_ = None
        w = W(label, desc)
        if hasmax:
            x = w.s([], 'simpl1', '( %s -> X e. Word 2o )' % ante); y = w.s([], 'simpl2', '( %s -> Y e. Word 2o )' % ante); c = w.s([], 'simpl3', '( %s -> C e. %s )' % (ante, kindC))
            lt = w.s([], 'simpr', '( %s -> %s )' % (ante, '( # ` Y ) < ( # ` X )' if side == 1 else '( # ` X ) < ( # ` Y )'))
        else:
            ante = base
            x = w.s([], 'simp1', '( %s -> X e. Word 2o )' % ante); y = w.s([], 'simp2', '( %s -> Y e. Word 2o )' % ante); c = w.s([], 'simp3', '( %s -> C e. %s )' % (ante, kindC))
        cl = Cl(w, ante, {'X': ('Word 2o', x), 'Y': ('Word 2o', y), 'C': (kindC, c)})
        Wp = PAD('Y') if side == 1 else PAD('X')
        Xp, Yp = ('X', Wp) if side == 1 else (Wp, 'Y')
        VAL = VALS[F]
        v = w.s([x, y, c, w.inst(VALREF[F])], 'syl3anc', '( %s -> ( ( X %s Y ) ` C ) = %s )' % (ante, F, VAL('X', 'Y', 'C')))
        vp = w.s([cl.mem(Xp, 'Word 2o'), cl.mem(Yp, 'Word 2o'), c, w.inst(VALREF[F])], 'syl3anc', '( %s -> ( ( %s %s %s ) ` C ) = %s )' % (ante, Xp, F, Yp, VAL(Xp, Yp, 'C')))
        W0 = 'Y' if side == 1 else 'X'
        tp = w.s([cl.mem(W0, 'Word 2o'), w.inst('tonatpad')], 'syl', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ante, Wp, W0))
        rules = {TN(Wp): (TN(W0), tp)}
        if hasmax:
            mx = w.s([x, y, lt, w.inst('bwmaxpad' if side == 1 else 'bwmaxpad2')], 'syl3anc', '( %s -> %s = %s )' % (ante, MAX(Xp, Yp), MAX('X', 'Y')))
            rules[MAX(Xp, Yp)] = (MAX('X', 'Y'), mx)
        st, new = w.rewrite(VAL(Xp, Yp, 'C'), rules, ante)
        assert new == VAL('X', 'Y', 'C'), new
        vp2 = w.s([vp, st], 'eqtrd', '( %s -> ( ( %s %s %s ) ` C ) = %s )' % (ante, Xp, F, Yp, VAL('X', 'Y', 'C')))
        w.qed([v, vp2], 'eqtr4d', '( %s -> ( ( X %s Y ) ` C ) = ( ( %s %s %s ) ` C ) )' % (ante, F, Xp, F, Yp)); w.run()

    for F in ('addBits', 'subBits', 'subBorrow', 'cmpBits'):
        l1, l2 = PADREF[F]
        if want(l1):
            pad(l1, F, 1, 'Padding the second operand of %s with a false letter does not change the result%s.' % (F, ' when it is the shorter' if HASMAX[F] else ''))
        if want(l2):
            pad(l2, F, 2, 'Padding the first operand of %s with a false letter does not change the result%s.' % (F, ' when it is the shorter' if HASMAX[F] else ''))

    def padcons(label, F, side, desc):
        kindC = KINDC[F]; hasmax = HASMAX[F]
        L = 'A' if side == 1 else 'B'; Wd = 'X' if side == 1 else 'Y'
        ante = '( ( %s e. 2o /\\ C e. %s ) /\\ %s e. Word 2o )' % (L, kindC, Wd)
        w = W(label, desc)
        lt_ = w.s([], 'simpll', '( %s -> %s e. 2o )' % (ante, L)); c = w.s([], 'simplr', '( %s -> C e. %s )' % (ante, kindC)); wd = w.s([], 'simpr', '( %s -> %s e. Word 2o )' % (ante, Wd))
        cl = Cl(w, ante, {L: ('2o', lt_), 'C': (kindC, c), Wd: ('Word 2o', wd)})
        WA = CONS(L, Wd)
        Xa, Ya = (WA, '(/)') if side == 1 else ('(/)', WA)
        LHS = '( ( %s %s %s ) ` C )' % (Xa, F, Ya)
        hyps = [cl.mem(Xa, 'Word 2o'), cl.mem(Ya, 'Word 2o'), c]
        if hasmax:
            ln = conslen(w, cl, ante, L, Wd)
            h0 = w.s([num.closed(w, [], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ante)
            gt = w.s([cl.mem(LEN(Wd), 'NN0'), w.inst('nn0p1gt0')], 'syl', '( %s -> 0 < ( ( # ` %s ) + 1 ) )' % (ante, Wd))
            gt2 = w.s([gt, ln], 'breqtrrd', '( %s -> 0 < ( # ` %s ) )' % (ante, WA))
            gt3 = w.s([h0, gt2], 'eqbrtrd', '( %s -> ( # ` (/) ) < ( # ` %s ) )' % (ante, WA))
            j = w.s(hyps, '3jca', '( %s -> ( %s e. Word 2o /\\ %s e. Word 2o /\\ C e. %s ) )' % (ante, Xa, Ya, kindC))
            pd = w.s([j, gt3, w.inst(PADREF[F][side - 1])], 'syl2anc', '( %s -> %s = ( ( %s %s %s ) ` C ) )' % (ante, LHS, PAD(Xa) if side == 2 else Xa, F, PAD(Ya) if side == 1 else Ya))
        else:
            pd = w.s(hyps + [w.inst(PADREF[F][side - 1])], 'syl3anc', '( %s -> %s = ( ( %s %s %s ) ` C ) )' % (ante, LHS, PAD(Xa) if side == 2 else Xa, F, PAD(Ya) if side == 1 else Ya))
        s1w = w.s([cl.mem('<" (/) ">', 'Word 2o')], 'id', '( %s -> <" (/) "> e. Word 2o )' % ante) if False else cl.mem('<" (/) ">', 'Word 2o')
        e1 = w.s([s1w, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ <" (/) "> ) = <" (/) "> )' % ante)
        e2 = w.s([w.s([s1w, w.inst('ccatrid')], 'syl', '( %s -> ( <" (/) "> ++ (/) ) = <" (/) "> )' % ante)], 'eqcomd', '( %s -> <" (/) "> = ( <" (/) "> ++ (/) ) )' % ante)
        e = w.s([e1, e2], 'eqtrd', '( %s -> ( (/) ++ <" (/) "> ) = ( <" (/) "> ++ (/) ) )' % ante)
        if side == 1:
            o = w.s([e], 'oveq2d', '( %s -> ( %s %s ( (/) ++ <" (/) "> ) ) = ( %s %s ( <" (/) "> ++ (/) ) ) )' % (ante, WA, F, WA, F))
            f = w.s([o], 'fveq1d', '( %s -> ( ( %s %s ( (/) ++ <" (/) "> ) ) ` C ) = ( ( %s %s ( <" (/) "> ++ (/) ) ) ` C ) )' % (ante, WA, F, WA, F))
            Xc, Yc, Ac, Bc, Xt, Yt = WA, CONS('(/)', '(/)'), L, '(/)', Wd, '(/)'
        else:
            o = w.s([e], 'oveq1d', '( %s -> ( ( (/) ++ <" (/) "> ) %s %s ) = ( ( <" (/) "> ++ (/) ) %s %s ) )' % (ante, F, WA, F, WA))
            f = w.s([o], 'fveq1d', '( %s -> ( ( ( (/) ++ <" (/) "> ) %s %s ) ` C ) = ( ( ( <" (/) "> ++ (/) ) %s %s ) ` C ) )' % (ante, F, WA, F, WA))
            Xc, Yc, Ac, Bc, Xt, Yt = CONS('(/)', '(/)'), WA, '(/)', L, '(/)', Wd
        zero = cl.mem('(/)', '2o'); w0 = cl.mem('(/)', 'Word 2o')
        ja = w.s([cl.mem(Ac, '2o'), cl.mem(Bc, '2o'), c], '3jca', '( %s -> ( %s e. 2o /\\ %s e. 2o /\\ C e. %s ) )' % (ante, Ac, Bc, kindC))
        jb = w.s([cl.mem(Xt, 'Word 2o'), cl.mem(Yt, 'Word 2o')], 'jca', '( %s -> ( %s e. Word 2o /\\ %s e. Word 2o ) )' % (ante, Xt, Yt))
        cons = w.s([ja, jb, w.inst(CONSREF[F])], 'syl2anc', '( %s -> ( ( %s %s %s ) ` C ) = %s )' % (ante, Xc, F, Yc, CONSRHS[F](Ac, Bc, 'C', Xt, Yt)))
        w.qed([pd, f, cons], '3eqtrd', '( %s -> %s = %s )' % (ante, LHS, CONSRHS[F](Ac, Bc, 'C', Xt, Yt))); w.run()

    for F, (l1, l2) in (('addBits', ('addbitscons1', 'addbitscons2')), ('subBits', ('subbitscons1', 'subbitscons2')),
                        ('subBorrow', ('subborrowcons1', 'subborrowcons2')), ('cmpBits', ('cmpbitscons1', 'cmpbitscons2'))):
        if want(l1):
            padcons(l1, F, 1, 'Lean clause 2 of %s: the second operand is empty.' % F)
        if want(l2):
            padcons(l2, F, 2, 'Lean clause 3 of %s: the first operand is empty.' % F)
