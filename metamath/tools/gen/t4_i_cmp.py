"""Sortie T4, group I: the comparison verdict position by position, and the closed form of the cmpStep fold (T4-blueprint 3.5)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AN0 = '( A e. NN0 /\\ B e. NN0 /\\ C e. 3o )'
AN = '( %s /\\ I e. NN0 )' % AN0
MA = lambda I: '( A mod ( 2 ^ %s ) )' % I
MB = lambda I: '( B mod ( 2 ^ %s ) )' % I
VI = lambda I: 'if ( %s = %s , C , ( %s Ncmp %s ) )' % (MA(I), MB(I), MA(I), MB(I))
VER = lambda I: FOLD('cmpStep', 'A', 'B', 'C', I)
PK = '( 2 ^ I )'; I1 = '( I + 1 )'
a_ = BIT('A', 'I'); b_ = BIT('B', 'I')
FSET = '~P ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) )'


def base(w, ante=AN):
    a = w.s([], 'simpl1', '( %s -> A e. NN0 )' % ante); b = w.s([], 'simpl2', '( %s -> B e. NN0 )' % ante)
    c = w.s([], 'simpl3', '( %s -> C e. 3o )' % ante); i = w.s([], 'simpr', '( %s -> I e. NN0 )' % ante)
    return Cl(w, ante, {'A': ('NN0', a), 'B': ('NN0', b), 'C': ('3o', c), 'I': ('NN0', i)})


if __name__ == '__main__':
    if want('ncmpbi'):
        A4 = '( ( A e. NN0 /\\ B e. NN0 ) /\\ ( D e. NN0 /\\ E e. NN0 ) )'
        w = W('ncmpbi', 'Ncmp depends only on the order of its arguments.')
        A5 = '( %s /\\ ( ( A = B <-> D = E ) /\\ ( A < B <-> D < E ) ) )' % A4
        ab = w.s([], 'simpll', '( %s -> ( A e. NN0 /\\ B e. NN0 ) )' % A5); de = w.s([], 'simplr', '( %s -> ( D e. NN0 /\\ E e. NN0 ) )' % A5)
        he = w.s([], 'simprl', '( %s -> ( A = B <-> D = E ) )' % A5); hl = w.s([], 'simprr', '( %s -> ( A < B <-> D < E ) )' % A5)
        v1 = w.s([ab, w.inst('ncmpval')], 'syl', '( %s -> ( A Ncmp B ) = if ( A = B , 1o , if ( A < B , (/) , 2o ) ) )' % A5)
        v2 = w.s([de, w.inst('ncmpval')], 'syl', '( %s -> ( D Ncmp E ) = if ( D = E , 1o , if ( D < E , (/) , 2o ) ) )' % A5)
        i1 = w.s([hl], 'ifbid', '( %s -> if ( A < B , (/) , 2o ) = if ( D < E , (/) , 2o ) )' % A5)
        i2 = w.s([he, i1], 'ifbieq2d', '( %s -> if ( A = B , 1o , if ( A < B , (/) , 2o ) ) = if ( D = E , 1o , if ( D < E , (/) , 2o ) ) )' % A5)
        e = w.s([v1, i2, v2], '3eqtr4d', '( %s -> ( A Ncmp B ) = ( D Ncmp E ) )' % A5)
        w.qed([e], 'ex', '( %s -> ( ( ( A = B <-> D = E ) /\\ ( A < B <-> D < E ) ) -> ( A Ncmp B ) = ( D Ncmp E ) ) )' % A4); w.run()

    if want('bwcmplem'):
        w = W('bwcmplem', 'Lemma for the verdict: the verdict on the low I + 1 bits is the comparator step on the two digits at I and the verdict on the low I bits.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR'))
        for E in (MA('I'), MB('I'), MA(I1), MB(I1)):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        pa = w.s([cl.mem('A', 'ZZ'), cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AN, MA(I1), MA('I'), PK, a_))
        pb = w.s([cl.mem('B', 'ZZ'), cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AN, MB(I1), MB('I'), PK, b_))
        lta = w.s([cl.mem('A', 'RR'), cl.mem(PK, 'RR+'), w.inst('modlt')], 'syl2anc', '( %s -> %s < %s )' % (AN, MA('I'), PK))
        ltb = w.s([cl.mem('B', 'RR'), cl.mem(PK, 'RR+'), w.inst('modlt')], 'syl2anc', '( %s -> %s < %s )' % (AN, MB('I'), PK))
        vi3 = cl.mem(VI('I'), '3o')
        cs = w.s([cl.mem(a_, '2o'), cl.mem(b_, '2o'), vi3, w.inst('cmpstepval')], 'syl3anc', '( %s -> ( ( %s cmpStep %s ) ` %s ) = if ( %s = %s , %s , if ( %s = 1o , 2o , (/) ) ) )' % (AN, a_, b_, VI('I'), a_, b_, VI('I'), a_))
        concl = '%s = ( ( %s cmpStep %s ) ` %s )' % (VI(I1), a_, b_, VI('I'))
        ma2 = w.s([cl.mem('A', 'NN0'), cl.mem('B', 'NN0')], 'jca', '( %s -> ( A e. NN0 /\\ B e. NN0 ) )' % AN) if False else None
        def prodv(a2, K, eq, v):
            f = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` %s ) )' % (a2, K, v))
            c = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, '1' if v == '1o' else '0'))
            f2 = w.s([f, c], 'eqtrdi', '( %s -> ( bToNat ` %s ) = %s )' % (a2, K, '1' if v == '1o' else '0'))
            PR = '( %s x. ( bToNat ` %s ) )' % (PK, K)
            o = w.s([f2], 'oveq2d', '( %s -> %s = ( %s x. %s ) )' % (a2, PR, PK, '1' if v == '1o' else '0'))
            pcc = lift(w, cl.mem(PK, 'CC'), a2)
            if v == '1o':
                m = w.s([pcc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (a2, PK, PK)); return w.s([o, m], 'eqtrd', '( %s -> %s = %s )' % (a2, PR, PK))
            m = w.s([pcc], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (a2, PK)); return w.s([o, m], 'eqtrd', '( %s -> %s = 0 )' % (a2, PR))

        def bodyA(aA, eqA, va):
            cA = Cl(w, aA, {}); cA.parent = cl
            def bodyB(aB, eqB, vb):
                c2 = Cl(w, aB, {}); c2.parent = cA
                for E in (PK, MA('I'), MB('I'), MA(I1), MB(I1)):
                    c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), aB))
                pa2 = lift(w, pa, aB); pb2 = lift(w, pb, aB)
                pva = prodv(aB, a_, lift(w, eqA, aB), va); pvb = prodv(aB, b_, eqB, vb)
                cs2 = lift(w, cs, aB)
                n1 = w.s([], '1n0', '1o =/= (/)')
                if va == vb:
                    ab = w.s([lift(w, eqA, aB), eqB], 'eqtr4d', '( %s -> %s = %s )' % (aB, a_, b_))
                    it = w.s([ab], 'iftrued', '( %s -> if ( %s = %s , %s , if ( %s = 1o , 2o , (/) ) ) = %s )' % (aB, a_, b_, VI('I'), a_, VI('I')))
                    rhs = w.s([cs2, it], 'eqtrd', '( %s -> ( ( %s cmpStep %s ) ` %s ) = %s )' % (aB, a_, b_, VI('I'), VI('I')))
                    d1 = lineq(w, aB, '( %s - %s )' % (MA(I1), MB(I1)), '( %s - %s )' % (MA('I'), MB('I')), hyps=[pa2, pb2, pva, pvb], closure=c2)
                    d2 = lineq(w, aB, '( %s - %s )' % (MB(I1), MA(I1)), '( %s - %s )' % (MB('I'), MA('I')), hyps=[pa2, pb2, pva, pvb], closure=c2)
                    ca1 = c2.mem(MA(I1), 'CC'); cb1 = c2.mem(MB(I1), 'CC'); ca = c2.mem(MA('I'), 'CC'); cb = c2.mem(MB('I'), 'CC')
                    s1 = w.s([ca1, cb1, w.inst('subeq0')], 'syl2anc', '( %s -> ( ( %s - %s ) = 0 <-> %s = %s ) )' % (aB, MA(I1), MB(I1), MA(I1), MB(I1)))
                    s2 = w.s([ca, cb, w.inst('subeq0')], 'syl2anc', '( %s -> ( ( %s - %s ) = 0 <-> %s = %s ) )' % (aB, MA('I'), MB('I'), MA('I'), MB('I')))
                    e1 = w.s([d1], 'eqeq1d', '( %s -> ( ( %s - %s ) = 0 <-> ( %s - %s ) = 0 ) )' % (aB, MA(I1), MB(I1), MA('I'), MB('I')))
                    beq = w.s([s1, e1, s2], '3bitr3d', '( %s -> ( %s = %s <-> %s = %s ) )' % (aB, MA(I1), MB(I1), MA('I'), MB('I')))
                    ra1 = c2.mem(MA(I1), 'RR'); rb1 = c2.mem(MB(I1), 'RR'); ra = c2.mem(MA('I'), 'RR'); rb = c2.mem(MB('I'), 'RR')
                    p1 = w.s([ra1, rb1, w.inst('posdif')], 'syl2anc', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (aB, MA(I1), MB(I1), MB(I1), MA(I1)))
                    p2 = w.s([ra, rb, w.inst('posdif')], 'syl2anc', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (aB, MA('I'), MB('I'), MB('I'), MA('I')))
                    l1 = w.s([d2], 'breq2d', '( %s -> ( 0 < ( %s - %s ) <-> 0 < ( %s - %s ) ) )' % (aB, MB(I1), MA(I1), MB('I'), MA('I')))
                    blt = w.s([p1, l1, p2], '3bitr4d', '( %s -> ( %s < %s <-> %s < %s ) )' % (aB, MA(I1), MB(I1), MA('I'), MB('I')))
                    na1 = c2.mem(MA(I1), 'NN0'); nb1 = c2.mem(MB(I1), 'NN0'); na = c2.mem(MA('I'), 'NN0'); nb = c2.mem(MB('I'), 'NN0')
                    j1 = w.s([na1, nb1], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (aB, MA(I1), MB(I1))); j2 = w.s([na, nb], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (aB, MA('I'), MB('I')))
                    j3 = w.s([beq, blt], 'jca', '( %s -> ( ( %s = %s <-> %s = %s ) /\\ ( %s < %s <-> %s < %s ) ) )' % (aB, MA(I1), MB(I1), MA('I'), MB('I'), MA(I1), MB(I1), MA('I'), MB('I')))
                    nc = w.s([j1, j2, w.inst('ncmpbi')], 'syl2anc', '( %s -> ( ( ( %s = %s <-> %s = %s ) /\\ ( %s < %s <-> %s < %s ) ) -> ( %s Ncmp %s ) = ( %s Ncmp %s ) ) )' % (aB, MA(I1), MB(I1), MA('I'), MB('I'), MA(I1), MB(I1), MA('I'), MB('I'), MA(I1), MB(I1), MA('I'), MB('I')))
                    nce = w.s([j3, nc], 'mpd', '( %s -> ( %s Ncmp %s ) = ( %s Ncmp %s ) )' % (aB, MA(I1), MB(I1), MA('I'), MB('I')))
                    lhs = w.s([beq, nce], 'ifbieq2d', '( %s -> %s = %s )' % (aB, VI(I1), VI('I')))
                    return w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (aB, concl))
                # a =/= b
                if va == '1o':
                    nab = w.s([n1], 'a1i', '( %s -> 1o =/= (/) )' % aB)
                    ne = w.s([lift(w, eqA, aB), eqB, nab], '3netr4d' if False else 'eqnetrd', '') if False else None
                    ne0 = w.s([lift(w, eqA, aB), nab], 'eqnetrd', '( %s -> %s =/= (/) )' % (aB, a_))
                    ne = w.s([ne0, eqB], 'neeqtrrd', '( %s -> %s =/= %s )' % (aB, a_, b_))
                    tgt = '2o'; g = linarith(w, aB, [pa2, pb2, pva, pvb, lift(w, ltb, aB), lift(w, cl.ge0(MA('I')), aB)], '%s < %s' % (MB(I1), MA(I1)), closure=c2)
                    i2 = w.s([lift(w, eqA, aB)], 'iftrued', '( %s -> if ( %s = 1o , 2o , (/) ) = 2o )' % (aB, a_))
                else:
                    nab = w.s([n1], 'nesymi', '-. (/) = 1o'); nabd = w.s([nab], 'a1i', '( %s -> -. (/) = 1o )' % aB)
                    eq1 = w.s([lift(w, eqA, aB), eqB], 'eqeq12d', '( %s -> ( %s = %s <-> (/) = 1o ) )' % (aB, a_, b_))
                    nq = w.s([nabd, eq1], 'mtbird', '( %s -> -. %s = %s )' % (aB, a_, b_))
                    ne = w.s([nq], 'neqned', '( %s -> %s =/= %s )' % (aB, a_, b_))
                    tgt = '(/)'; g = linarith(w, aB, [pa2, pb2, pva, pvb, lift(w, lta, aB), lift(w, cl.ge0(MB('I')), aB)], '%s < %s' % (MA(I1), MB(I1)), closure=c2)
                    ea = w.s([lift(w, eqA, aB)], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (aB, a_))
                    nea = w.s([nabd, ea], 'mtbird', '( %s -> -. %s = 1o )' % (aB, a_))
                    i2 = w.s([nea], 'iffalsed', '( %s -> if ( %s = 1o , 2o , (/) ) = (/) )' % (aB, a_))
                nq2 = w.s([ne], 'neneqd', '( %s -> -. %s = %s )' % (aB, a_, b_))
                i1 = w.s([nq2], 'iffalsed', '( %s -> if ( %s = %s , %s , if ( %s = 1o , 2o , (/) ) ) = if ( %s = 1o , 2o , (/) ) )' % (aB, a_, b_, VI('I'), a_, a_))
                rhs = w.s([cs2, i1, i2], '3eqtrd', '( %s -> ( ( %s cmpStep %s ) ` %s ) = %s )' % (aB, a_, b_, VI('I'), tgt))
                na1 = c2.mem(MA(I1), 'NN0'); nb1 = c2.mem(MB(I1), 'NN0')
                if va == '1o':
                    nc = w.s([na1, nb1, w.inst('ncmpgt')], 'syl2anc', '( %s -> ( ( %s Ncmp %s ) = 2o <-> %s < %s ) )' % (aB, MA(I1), MB(I1), MB(I1), MA(I1)))
                    lt2 = g
                    ne2 = w.s([c2.mem(MB(I1), 'RR'), g], 'ltned', '( %s -> %s =/= %s )' % (aB, MB(I1), MA(I1))); ne3 = w.s([ne2], 'necomd', '( %s -> %s =/= %s )' % (aB, MA(I1), MB(I1)))
                else:
                    nc = w.s([na1, nb1, w.inst('ncmplt')], 'syl2anc', '( %s -> ( ( %s Ncmp %s ) = (/) <-> %s < %s ) )' % (aB, MA(I1), MB(I1), MA(I1), MB(I1)))
                    ne3 = w.s([c2.mem(MA(I1), 'RR'), g], 'ltned', '( %s -> %s =/= %s )' % (aB, MA(I1), MB(I1)))
                ncv = w.s([g, nc], 'mpbird', '( %s -> ( %s Ncmp %s ) = %s )' % (aB, MA(I1), MB(I1), tgt))
                nq3 = w.s([ne3], 'neneqd', '( %s -> -. %s = %s )' % (aB, MA(I1), MB(I1)))
                ifl = w.s([nq3], 'iffalsed', '( %s -> %s = ( %s Ncmp %s ) )' % (aB, VI(I1), MA(I1), MB(I1)))
                lhs = w.s([ifl, ncv], 'eqtrd', '( %s -> %s = %s )' % (aB, VI(I1), tgt))
                return w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (aB, concl))
            return cases2o(w, aA, b_, lift(w, cl.mem(b_, '2o'), aA), bodyB, concl)
        st = cases2o(w, AN, a_, cl.mem(a_, '2o'), bodyA, concl); promote(w, st); w.run()

    if want('bwcmpf'):
        w = W('bwcmpf', 'The cmpStep fold is the comparison: the verdict after the I low bits is the start value when the low bits agree, else their comparison.')
        P = lambda I: '%s = %s' % (VER(I), VI(I))
        x0 = w.s([], 'id', '( x = 0 -> x = 0 )'); h1, _ = w.wcongr(P('x'), {'x': '0'}, 'x = 0', {'x': x0})
        xy = w.s([], 'id', '( x = y -> x = y )'); h2, _ = w.wcongr(P('x'), {'x': 'y'}, 'x = y', {'x': xy})
        xy1 = w.s([], 'id', '( x = ( y + 1 ) -> x = ( y + 1 ) )'); h3, _ = w.wcongr(P('x'), {'x': '( y + 1 )'}, 'x = ( y + 1 )', {'x': xy1})
        xI = w.s([], 'id', '( x = I -> x = I )'); h4, _ = w.wcongr(P('x'), {'x': 'I'}, 'x = I', {'x': xI})
        a = w.s([], 'simp1', '( %s -> A e. NN0 )' % AN0); b = w.s([], 'simp2', '( %s -> B e. NN0 )' % AN0); c = w.s([], 'simp3', '( %s -> C e. 3o )' % AN0)
        cl0 = Cl(w, AN0, {'A': ('NN0', a), 'B': ('NN0', b), 'C': ('3o', c)})
        az = cl0.mem('A', 'ZZ'); bz = cl0.mem('B', 'ZZ')
        fs = w.s([], 'cmpstepfs', 'cmpStep e. %s' % FSET); fsd = w.s([fs], 'a1i', '( %s -> cmpStep e. %s )' % (AN0, FSET))
        jab = w.s([az, bz], 'jca', '( %s -> ( A e. ZZ /\\ B e. ZZ ) )' % AN0); jfc = w.s([fsd, c], 'jca', '( %s -> ( cmpStep e. %s /\\ C e. 3o ) )' % (AN0, FSET))
        af = w.s([jab, jfc], 'jca', '( %s -> ( ( A e. ZZ /\\ B e. ZZ ) /\\ ( cmpStep e. %s /\\ C e. 3o ) ) )' % (AN0, FSET))
        f0 = w.s([af, w.inst('bwfold0')], 'syl', '( %s -> %s = C )' % (AN0, VER('0')))
        ma0 = w.s([az, w.inst('zmod10')], 'syl', '( %s -> ( A mod 1 ) = 0 )' % AN0); mb0 = w.s([bz, w.inst('zmod10')], 'syl', '( %s -> ( B mod 1 ) = 0 )' % AN0)
        tc = w.s([], '2cn', '2 e. CC'); e0 = w.s([tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % AN0)
        oa = w.s([e0d], 'oveq2d', '( %s -> ( A mod ( 2 ^ 0 ) ) = ( A mod 1 ) )' % AN0); oa2 = w.s([oa, ma0], 'eqtrd', '( %s -> ( A mod ( 2 ^ 0 ) ) = 0 )' % AN0)
        ob = w.s([e0d], 'oveq2d', '( %s -> ( B mod ( 2 ^ 0 ) ) = ( B mod 1 ) )' % AN0); ob2 = w.s([ob, mb0], 'eqtrd', '( %s -> ( B mod ( 2 ^ 0 ) ) = 0 )' % AN0)
        eq0 = w.s([oa2, ob2], 'eqtr4d', '( %s -> %s = %s )' % (AN0, MA('0'), MB('0')))
        k0 = w.s([eq0], 'iftrued', '( %s -> %s = C )' % (AN0, VI('0')))
        base_ = w.s([f0, k0], 'eqtr4d', '( %s -> %s )' % (AN0, P('0')))
        AY = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (AN0, P('y'))
        ih = w.s([], 'simpr', '( %s -> %s )' % (AY, P('y'))); yn = w.s([], 'simplr', '( %s -> y e. NN0 )' % AY); an = w.s([], 'simpll', '( %s -> %s )' % (AY, AN0))
        any_ = w.s([an, yn], 'jca', '( %s -> ( %s /\\ y e. NN0 ) )' % (AY, AN0))
        cly = Cl(w, AY, {'A': ('NN0', lift(w, a, AY)), 'B': ('NN0', lift(w, b, AY)), 'C': ('3o', lift(w, c, AY)), 'y': ('NN0', yn)})
        ky3 = cly.mem(VI('y'), '3o')
        lv3 = w.s([ih, ky3], 'eqeltrd', '( %s -> %s e. 3o )' % (AY, VER('y')))
        aff = w.s([an, af], 'syl', '( %s -> ( ( A e. ZZ /\\ B e. ZZ ) /\\ ( cmpStep e. %s /\\ C e. 3o ) ) )' % (AY, FSET))
        jy = w.s([yn, lv3], 'jca', '( %s -> ( y e. NN0 /\\ %s e. 3o ) )' % (AY, VER('y')))
        p1 = w.s([aff, jy, w.inst('bwfoldp1')], 'syl2anc', '( %s -> %s = ( ( %s cmpStep %s ) ` %s ) )' % (AY, VER('( y + 1 )'), BIT('A', 'y'), BIT('B', 'y'), VER('y')))
        f = w.s([ih], 'fveq2d', '( %s -> ( ( %s cmpStep %s ) ` %s ) = ( ( %s cmpStep %s ) ` %s ) )' % (AY, BIT('A', 'y'), BIT('B', 'y'), VER('y'), BIT('A', 'y'), BIT('B', 'y'), VI('y')))
        l4 = w.s([any_, w.inst('bwcmplem')], 'syl', '( %s -> %s = ( ( %s cmpStep %s ) ` %s ) )' % (AY, VI('( y + 1 )'), BIT('A', 'y'), BIT('B', 'y'), VI('y')))
        step = w.s([p1, f, l4], '3eqtr4d', '( %s -> %s )' % (AY, P('( y + 1 )')))
        st = w.s([h1, h2, h3, h4, base_, step], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (AN0, P('I')))
        promote(w, st); w.run()

    if want('bwcmpfcl'):
        w = W('bwcmpfcl', 'The verdict is an ordering.')
        cl = base(w)
        v = w.s([], 'bwcmpf', '( %s -> %s = %s )' % (AN, VER('I'), VI('I'))); m = cl.mem(VI('I'), '3o')
        w.qed([v, m], 'eqeltrd', '( %s -> %s e. 3o )' % (AN, VER('I'))); w.run()
    if want('bwcmpfp1'):
        w = W('bwcmpfp1', 'The verdict after I + 1 bits is the comparator step on the two digits at I and the verdict after I bits (the recursive form, unconditionally; Lean: cmpStep_shift).')
        cl = base(w)
        i1 = cl.mem(I1, 'NN0'); an0 = w.s([], 'simpl', '( %s -> %s )' % (AN, AN0))
        v1 = w.s([an0, i1, w.inst('bwcmpf')], 'syl2anc', '( %s -> %s = %s )' % (AN, VER(I1), VI(I1)))
        l4 = w.s([], 'bwcmplem', '( %s -> %s = ( ( %s cmpStep %s ) ` %s ) )' % (AN, VI(I1), a_, b_, VI('I')))
        v0 = w.s([], 'bwcmpf', '( %s -> %s = %s )' % (AN, VER('I'), VI('I')))
        f = w.s([v0], 'fveq2d', '( %s -> ( ( %s cmpStep %s ) ` %s ) = ( ( %s cmpStep %s ) ` %s ) )' % (AN, a_, b_, VER('I'), a_, b_, VI('I')))
        e = w.s([v1, l4], 'eqtrd', '( %s -> %s = ( ( %s cmpStep %s ) ` %s ) )' % (AN, VER(I1), a_, b_, VI('I')))
        w.qed([e, f], 'eqtr4d', '( %s -> %s = ( ( %s cmpStep %s ) ` %s ) )' % (AN, VER(I1), a_, b_, VER('I'))); w.run()
