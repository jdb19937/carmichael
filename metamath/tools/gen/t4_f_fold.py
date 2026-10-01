"""Sortie T4, group F: the fold bwFold, its value and step, the step functions in its domain, and the digit-position lemmas (T4-blueprint 3.5)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


FSET = '~P ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) )'
STEP = lambda A, B, F: '( u e. 3o , k e. NN0 |-> ( ( %s %s %s ) ` u ) )' % (BIT(A, 'k'), F, BIT(B, 'k'))
INNER = lambda A, B: '( f e. %s , c e. 3o |-> ( c AlgRec %s ) )' % (FSET, STEP(A, B, 'f'))
OUTER = '( a e. ZZ , b e. ZZ |-> %s )' % INNER('a', 'b')
AF = '( ( A e. ZZ /\\ B e. ZZ ) /\\ ( F e. %s /\\ C e. 3o ) )' % FSET
LEV = lambda I: FOLD('F', 'A', 'B', 'C', I)


def clF(w, ante=AF):
    a = w.s([], 'simpll', '( %s -> A e. ZZ )' % ante); b = w.s([], 'simplr', '( %s -> B e. ZZ )' % ante)
    f = w.s([], 'simprl', '( %s -> F e. %s )' % (ante, FSET)); c = w.s([], 'simprr', '( %s -> C e. 3o )' % ante)
    cl = Cl(w, ante, {'A': ('ZZ', a), 'B': ('ZZ', b), 'F': (FSET, f), 'C': ('3o', c)})
    return cl


if __name__ == '__main__':
    if want('bwfsex'):
        w = W('bwfsex', 'The domain of the step functions of bwFold is a set.')
        t = w.s([], '2oex', '2o e. _V'); th = w.s([], 'bw3oex', '3o e. _V')
        x2 = w.s([t, t, w.inst('xpexg')], 'mp2an', '( 2o X. 2o ) e. _V'); x3 = w.s([th, th, w.inst('xpexg')], 'mp2an', '( 3o X. 3o ) e. _V')
        p3 = w.s([x3], 'pwex', '~P ( 3o X. 3o ) e. _V')
        xx = w.s([x2, p3, w.inst('xpexg')], 'mp2an', '( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) ) e. _V')
        w.qed([xx], 'pwex', '%s e. _V' % FSET); w.run()
    CLOSED[(FSET, '_V')] = 'bwfsex'

    if want('bwfoldval'):
        w = W('bwfoldval', 'Value of bwFold: the fold of the step function F over the digit positions of A and B from C, as a recursion on the position (df-algrec).')
        cl = clF(w)
        st1, v1 = mpoov(w, cl, OUTER, 'A', 'B', defref='df-bwfold', F='bwFold')
        assert v1 == INNER('A', 'B'), v1
        o = w.s([st1], 'oveqd', '( %s -> ( F ( A bwFold B ) C ) = ( F %s C ) )' % (AF, v1))
        st2, v2 = mpoov(w, cl, v1, 'F', 'C')
        assert v2 == '( C AlgRec %s )' % STEP('A', 'B', 'F'), v2
        w.qed([o, st2], 'eqtrd', '( %s -> ( F ( A bwFold B ) C ) = %s )' % (AF, v2)); w.run()

    if want('bwfold0'):
        w = W('bwfold0', 'The fold at position 0 is the start value.')
        cl = clF(w)
        v = w.s([], 'bwfoldval', '( %s -> ( F ( A bwFold B ) C ) = ( C AlgRec %s ) )' % (AF, STEP('A', 'B', 'F')))
        f = w.s([v], 'fveq1d', '( %s -> %s = ( ( C AlgRec %s ) ` 0 ) )' % (AF, LEV('0'), STEP('A', 'B', 'F')))
        cx = cl.mem('C', '_V'); sx = cl.mem(STEP('A', 'B', 'F'), '_V')
        a0 = w.s([cx, sx, w.inst('algrec0')], 'syl2anc', '( %s -> ( ( C AlgRec %s ) ` 0 ) = C )' % (AF, STEP('A', 'B', 'F')))
        w.qed([f, a0], 'eqtrd', '( %s -> %s = C )' % (AF, LEV('0'))); w.run()

    if want('bwfoldp1'):
        A2 = '( %s /\\ ( I e. NN0 /\\ %s e. 3o ) )' % (AF, LEV('I'))
        w = W('bwfoldp1', 'The fold at position I + 1 is the step function applied to the two digits at I and the fold at I.')
        base = w.s([], 'simpl', '( %s -> %s )' % (A2, AF)); i = w.s([], 'simprl', '( %s -> I e. NN0 )' % A2); lv = w.s([], 'simprr', '( %s -> %s e. 3o )' % (A2, LEV('I')))
        cl = Cl(w, A2, {'I': ('NN0', i), LEV('I'): ('3o', lv)})
        for x, k in (('A', 'ZZ'), ('B', 'ZZ'), ('F', FSET), ('C', '3o')):
            cl.have(x, k, lift(w, clF(w).__dict__['memo'][(x, k)], A2)) if False else None
        a = w.s([base], 'simplld', '( %s -> A e. ZZ )' % A2); b = w.s([base], 'simplrd', '( %s -> B e. ZZ )' % A2)
        f = w.s([base], 'simprld', '( %s -> F e. %s )' % (A2, FSET)); c = w.s([base], 'simprrd', '( %s -> C e. 3o )' % A2)
        cl.have('A', 'ZZ', a); cl.have('B', 'ZZ', b); cl.have('F', FSET, f); cl.have('C', '3o', c)
        S = STEP('A', 'B', 'F')
        v = w.s([base, w.inst('bwfoldval')], 'syl', '( %s -> ( F ( A bwFold B ) C ) = ( C AlgRec %s ) )' % (A2, S))
        f1 = w.s([v], 'fveq1d', '( %s -> %s = ( ( C AlgRec %s ) ` ( I + 1 ) ) )' % (A2, LEV('( I + 1 )'), S))
        cx = cl.mem('C', '_V'); sx = cl.mem(S, '_V')
        p1 = w.s([cx, sx, i, w.inst('algrecp1')], 'syl3anc', '( %s -> ( ( C AlgRec %s ) ` ( I + 1 ) ) = ( ( ( C AlgRec %s ) ` I ) %s I ) )' % (A2, S, S, S))
        fI = w.s([v], 'fveq1d', '( %s -> %s = ( ( C AlgRec %s ) ` I ) )' % (A2, LEV('I'), S))
        o = w.s([fI], 'oveq1d', '( %s -> ( %s %s I ) = ( ( ( C AlgRec %s ) ` I ) %s I ) )' % (A2, LEV('I'), S, S, S))
        st, val = mpoov(w, cl, S, LEV('I'), 'I')
        assert val == '( ( %s F %s ) ` %s )' % (BIT('A', 'I'), BIT('B', 'I'), LEV('I')), val
        e = w.s([o, st], 'eqtr3d', '( %s -> ( ( ( C AlgRec %s ) ` I ) %s I ) = %s )' % (A2, S, S, val))
        w.qed([f1, p1, e], '3eqtrd', '( %s -> %s = %s )' % (A2, LEV('( I + 1 )'), val)); w.run()

    # ---- the step functions are in the domain
    for lab, const, dlab, K, V in (('majfs', 'majBit', 'df-majbit', '2o', '2o'), ('borrowfs', 'borrow', 'df-borrow', '2o', '2o'), ('cmpstepfs', 'cmpStep', 'df-cmpstep', '3o', '3o')):
        if not want(lab):
            continue
        w = W(lab, '%s is a step function of bwFold.' % const)
        body = tm.defbody(dlab)
        mpt = body.split('|-> ', 1)[1].rsplit(' )', 1)[0]
        IF = mpt.split('|-> ', 1)[1].rsplit(' )', 1)[0]
        a2 = '( a e. 2o /\\ b e. 2o )'; a3 = '( %s /\\ c e. %s )' % (a2, K)
        cl3 = Cl(w, a3, {'a': ('2o', w.s([], 'simpll', '( %s -> a e. 2o )' % a3)), 'b': ('2o', w.s([], 'simplr', '( %s -> b e. 2o )' % a3)), 'c': (K, w.s([], 'simpr', '( %s -> c e. %s )' % (a3, K)))})
        m = cl3.mem(IF, V)
        e = w.s([], 'eqid', '%s = %s' % (mpt, mpt))
        fm = w.s([m, e], 'fmptd', '( %s -> %s : %s --> %s )' % (a2, mpt, K, V))
        ss = w.s([fm, w.inst('fssxp')], 'syl', '( %s -> %s C_ ( %s X. %s ) )' % (a2, mpt, K, V))
        s3 = w.s([], 'bw2oss3o', '2o C_ 3o'); sid = w.s([], 'ssid', '3o C_ 3o')
        sk = s3 if K == '2o' else sid; sv = s3 if V == '2o' else sid
        xs = w.s([sk, sv, w.inst('xpss12')], 'mp2an', '( %s X. %s ) C_ ( 3o X. 3o )' % (K, V)); xsd = w.s([xs], 'a1i', '( %s -> ( %s X. %s ) C_ ( 3o X. 3o ) )' % (a2, K, V))
        ss2 = w.s([ss, xsd], 'sstrd', '( %s -> %s C_ ( 3o X. 3o ) )' % (a2, mpt))
        th = w.s([], 'bw3oex', '3o e. _V'); x3 = w.s([th, th, w.inst('xpexg')], 'mp2an', '( 3o X. 3o ) e. _V')
        pw = w.s([x3, w.inst('elpw2g')], 'ax-mp', '( %s e. ~P ( 3o X. 3o ) <-> %s C_ ( 3o X. 3o ) )' % (mpt, mpt))
        el = w.s([ss2, pw], 'sylibr', '( %s -> %s e. ~P ( 3o X. 3o ) )' % (a2, mpt))
        rg = w.s([el], 'rgen2', 'A. a e. 2o A. b e. 2o %s e. ~P ( 3o X. 3o )' % mpt)
        d = w.s([], dlab, '%s = %s' % (const, body))
        fo = w.s([d], 'fmpo', '( A. a e. 2o A. b e. 2o %s e. ~P ( 3o X. 3o ) <-> %s : ( 2o X. 2o ) --> ~P ( 3o X. 3o ) )' % (mpt, const))
        ff = w.s([rg, fo], 'mpbi', '%s : ( 2o X. 2o ) --> ~P ( 3o X. 3o )' % const)
        fs = w.s([ff, w.inst('fssxp')], 'ax-mp', '%s C_ ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) )' % const)
        t = w.s([], '2oex', '2o e. _V'); x2 = w.s([t, t, w.inst('xpexg')], 'mp2an', '( 2o X. 2o ) e. _V'); p3 = w.s([x3], 'pwex', '~P ( 3o X. 3o ) e. _V')
        xx = w.s([x2, p3, w.inst('xpexg')], 'mp2an', '( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) ) e. _V')
        pw2 = w.s([xx, w.inst('elpw2g')], 'ax-mp', '( %s e. %s <-> %s C_ ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) ) )' % (const, FSET, const))
        w.qed([fs, pw2], 'mpbir', '%s e. %s' % (const, FSET)); w.run()

    # ---- bwifbn, bwmodp1, bwbn11
    if want('bwifbn'):
        w = W('bwifbn', 'A digit weight as a product: if ( ph , 2 ^ I , 0 ) is 2 ^ I times the value of the Boolean of ph.')
        AI = 'I e. NN0'
        cl = Cl(w, AI, {'I': ('NN0', w.s([], 'id', '( %s -> I e. NN0 )' % AI))})
        pc = cl.mem('( 2 ^ I )', 'CC')
        L = 'if ( ph , ( 2 ^ I ) , 0 )'; R = '( ( 2 ^ I ) x. ( bToNat ` if ( ph , 1o , (/) ) ) )'
        a1 = '( %s /\\ ph )' % AI; h1 = w.s([], 'simpr', '( %s -> ph )' % a1)
        l1 = w.s([h1], 'iftrued', '( %s -> %s = ( 2 ^ I ) )' % (a1, L))
        b1 = w.s([h1], 'iftrued', '( %s -> if ( ph , 1o , (/) ) = 1o )' % a1); f1 = w.s([b1], 'fveq2d', '( %s -> ( bToNat ` if ( ph , 1o , (/) ) ) = ( bToNat ` 1o ) )' % a1)
        c1 = w.s([], 'bwbn1', '( bToNat ` 1o ) = 1'); f1b = w.s([f1, c1], 'eqtrdi', '( %s -> ( bToNat ` if ( ph , 1o , (/) ) ) = 1 )' % a1)
        o1 = w.s([f1b], 'oveq2d', '( %s -> %s = ( ( 2 ^ I ) x. 1 ) )' % (a1, R)); m1 = w.s([lift(w, pc, a1)], 'mulridd', '( %s -> ( ( 2 ^ I ) x. 1 ) = ( 2 ^ I ) )' % a1)
        r1 = w.s([o1, m1], 'eqtrd', '( %s -> %s = ( 2 ^ I ) )' % (a1, R))
        e1 = w.s([l1, r1], 'eqtr4d', '( %s -> %s = %s )' % (a1, L, R))
        a2 = '( %s /\\ -. ph )' % AI; h2 = w.s([], 'simpr', '( %s -> -. ph )' % a2)
        l2 = w.s([h2], 'iffalsed', '( %s -> %s = 0 )' % (a2, L))
        b2 = w.s([h2], 'iffalsed', '( %s -> if ( ph , 1o , (/) ) = (/) )' % a2); f2 = w.s([b2], 'fveq2d', '( %s -> ( bToNat ` if ( ph , 1o , (/) ) ) = ( bToNat ` (/) ) )' % a2)
        c2 = w.s([], 'bwbn0', '( bToNat ` (/) ) = 0'); f2b = w.s([f2, c2], 'eqtrdi', '( %s -> ( bToNat ` if ( ph , 1o , (/) ) ) = 0 )' % a2)
        o2 = w.s([f2b], 'oveq2d', '( %s -> %s = ( ( 2 ^ I ) x. 0 ) )' % (a2, R)); m2 = w.s([lift(w, pc, a2)], 'mul01d', '( %s -> ( ( 2 ^ I ) x. 0 ) = 0 )' % a2)
        r2 = w.s([o2, m2], 'eqtrd', '( %s -> %s = 0 )' % (a2, R))
        e2 = w.s([l2, r2], 'eqtr4d', '( %s -> %s = %s )' % (a2, L, R))
        w.qed([e1, e2], 'pm2.61dan', '( %s -> %s = %s )' % (AI, L, R)); w.run()
    if want('bwmodp1'):
        AZ = '( A e. ZZ /\\ I e. NN0 )'
        w = W('bwmodp1', 'The residue modulo 2 ^ ( I + 1 ) is the residue modulo 2 ^ I plus the I-th digit at its weight.')
        a = w.s([], 'simpl', '( %s -> A e. ZZ )' % AZ); i = w.s([], 'simpr', '( %s -> I e. NN0 )' % AZ)
        il = w.s([], 'bitsinv1lem', '( %s -> ( A mod ( 2 ^ ( I + 1 ) ) ) = ( ( A mod ( 2 ^ I ) ) + if ( I e. ( bits ` A ) , ( 2 ^ I ) , 0 ) ) )' % AZ)
        b = w.s([i, w.inst('bwifbn')], 'syl', '( %s -> if ( I e. ( bits ` A ) , ( 2 ^ I ) , 0 ) = ( ( 2 ^ I ) x. ( bToNat ` %s ) ) )' % (AZ, BIT('A', 'I')))
        o = w.s([b], 'oveq2d', '( %s -> ( ( A mod ( 2 ^ I ) ) + if ( I e. ( bits ` A ) , ( 2 ^ I ) , 0 ) ) = ( ( A mod ( 2 ^ I ) ) + ( ( 2 ^ I ) x. ( bToNat ` %s ) ) ) )' % (AZ, BIT('A', 'I')))
        w.qed([il, o], 'eqtrd', '( %s -> ( A mod ( 2 ^ ( I + 1 ) ) ) = ( ( A mod ( 2 ^ I ) ) + ( ( 2 ^ I ) x. ( bToNat ` %s ) ) ) )' % (AZ, BIT('A', 'I'))); w.run()
    if want('bwbn11'):
        A2 = '( X e. 2o /\\ Y e. 2o )'
        w = W('bwbn11', 'The value of a Boolean determines it.')
        x = w.s([], 'simpl', '( %s -> X e. 2o )' % A2); y = w.s([], 'simpr', '( %s -> Y e. 2o )' % A2)
        fw = w.s([], 'fveq2', '( X = Y -> ( bToNat ` X ) = ( bToNat ` Y ) )'); fwd = w.s([fw], 'a1i', '( %s -> ( X = Y -> ( bToNat ` X ) = ( bToNat ` Y ) ) )' % A2)
        a3 = '( %s /\\ ( bToNat ` X ) = ( bToNat ` Y ) )' % A2
        h = w.s([], 'simpr', '( %s -> ( bToNat ` X ) = ( bToNat ` Y ) )' % a3)
        bx = w.s([lift(w, x, a3), w.inst('bwbneq1')], 'syl', '( %s -> ( ( bToNat ` X ) = 1 <-> X = 1o ) )' % a3)
        by = w.s([lift(w, y, a3), w.inst('bwbneq1')], 'syl', '( %s -> ( ( bToNat ` Y ) = 1 <-> Y = 1o ) )' % a3)
        e = w.s([h], 'eqeq1d', '( %s -> ( ( bToNat ` X ) = 1 <-> ( bToNat ` Y ) = 1 ) )' % a3)
        bi = w.s([e, by], 'bitrd', '( %s -> ( ( bToNat ` X ) = 1 <-> Y = 1o ) )' % a3)
        bi2 = w.s([bx, bi], 'bitr3d', '( %s -> ( X = 1o <-> Y = 1o ) )' % a3)
        # both Booleans: X = if(X=1o) and Y = if(Y=1o)
        xb = bool_from_bi(w, a3, 'X', 'X = 1o', w.s([], 'biidd', '( %s -> ( X = 1o <-> X = 1o ) )' % a3), lift(w, x, a3))
        yb = bool_from_bi(w, a3, 'Y', 'Y = 1o', w.s([], 'biidd', '( %s -> ( Y = 1o <-> Y = 1o ) )' % a3), lift(w, y, a3))
        ib = w.s([bi2], 'ifbid', '( %s -> if ( X = 1o , 1o , (/) ) = if ( Y = 1o , 1o , (/) ) )' % a3)
        eq = w.s([xb, ib, yb], '3eqtr4d', '( %s -> X = Y )' % a3)
        bk = w.s([eq], 'ex', '( %s -> ( ( bToNat ` X ) = ( bToNat ` Y ) -> X = Y ) )' % A2)
        w.qed([bk, fwd], 'impbid', '( %s -> ( ( bToNat ` X ) = ( bToNat ` Y ) <-> X = Y ) )' % A2); w.run()
