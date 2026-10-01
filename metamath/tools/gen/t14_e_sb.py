"""Sortie T14 (b): the typing of the search cost (srchcstl, srchcst) and the step bound in the
window (sbexpb, sbexpbev; Lean: searchBound_ExpB).  MM_DB=sorties/t14.mm python3 tools/gen/t14_e_sb.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *

VP = "V'"
P1 = "<. ( inr ` (/) ) , ( ( 2nd ` R ) + 1 ) >."
P2 = "<. ( inr ` (/) ) , ( C' + ( 2nd ` J ) ) >."
P3 = "<. ( inr ` (/) ) , ( ( C' + ( 2nd ` J ) ) + ( 2nd ` X' ) ) >."
FST4 = "if ( ( 1st ` Q' ) = 1o , ( inl ` <. F , A >. ) , ( inr ` (/) ) )"
C4 = "( ( ( C' + ( 2nd ` J ) ) + ( 2nd ` X' ) ) + ( 2nd ` Q' ) )"
P4 = "<. %s , %s >." % (FST4, C4)
IF3 = "if ( ( 1st ` X' ) = ( inr ` (/) ) , %s , %s )" % (P3, P4)
IF2 = "if ( ( 1st ` J ) = ( inr ` (/) ) , %s , %s )" % (P2, IF3)
IF1 = "if ( I < U , %s , %s )" % (P1, IF2)
T = '( _V X. NN0 )'


# ------------------------------------------------------------------ srchcstl
DJ = '( ( NN0 X. Word NN0 ) |_| 1o )'
DJT = '( %s X. NN0 )' % DJ


def srchcstl():
    return srch_l('srchcstl', 'The search cost is a natural number, at the letters of searchval (every branch of the '
                  'search value carries a cost in NN0; Lean: the type of Alg.search).', False)


def srchtypl():
    return srch_l('srchtypl', 'The search value is an Option of a pair ( number , word ) with a natural cost, at the letters '
                  'of searchval (Lean: Alg.search : ... -> Option ( N x List N ) x N).', True)


def srch_l(label, desc, typed):
    w = W(label, desc)
    T = DJT if typed else '( _V X. NN0 )'
    FX = DJ if typed else '_V'
    A = LET13
    pj = Proj(w, A)
    sv = w.s([], 't13srcv', '( %s -> ( %s Search N ) = %s )' % (A, VP, IF1))
    import t14lib
    assert t14lib._SV13 == "( %s Search N ) = %s" % (VP, IF1), t14lib._SV13[:300]
    ty = w.s([], 't13srcty', '( %s -> %s )' % (A, ante_of(dbstmt('t13srcty'))[1]))
    tyb = [proj(w, A, ty, i) for i in range(3)]
    r2 = proj(w, A, tyb[0], 1)            # ( 2nd ` R ) e. NN0
    ire = proj(w, A, tyb[0], 2)           # I e. NN0
    cp = proj(w, A, tyb[2], 1)            # C' e. NN0
    j2 = proj(w, A, tyb[2], 2)            # ( 2nd ` J ) e. NN0
    ln0 = proj(w, A, tyb[1], 1)           # L e. NN0
    fv = w.s([w.s([], '0lt1o', '(/) e. 1o'), w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. %s' % DJ) if typed else \
        w.s([], 'fvex', '( inr ` (/) ) e. _V')

    # branch 1
    A1 = '( %s /\\ I < U )' % A
    b1c = w.s([w.s([r2], 'adantr', '( %s -> ( 2nd ` R ) e. NN0 )' % A1), w.inst('peano2nn0')], 'syl',
              '( %s -> ( ( 2nd ` R ) + 1 ) e. NN0 )' % A1)
    b1 = w.s([w.s([fv], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (A1, FX)), b1c, w.inst('opelxpi')], 'syl2anc',
             '( %s -> %s e. %s )' % (A1, P1, T))
    # level 2
    A2 = '( %s /\\ -. I < U )' % A
    A21 = '( %s /\\ ( 1st ` J ) = ( inr ` (/) ) )' % A2
    cjA = w.s([w.s([cp, j2, w.inst('nn0addcl')], 'syl2anc', "( %s -> ( C' + ( 2nd ` J ) ) e. NN0 )" % A)], 'adantr',
              "( %s -> ( C' + ( 2nd ` J ) ) e. NN0 )" % A2)
    b2 = w.s([w.s([fv], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (A21, FX)),
              w.s([cjA], 'adantr', "( %s -> ( C' + ( 2nd ` J ) ) e. NN0 )" % A21), w.inst('opelxpi')], 'syl2anc',
             '( %s -> %s e. %s )' % (A21, P2, T))
    # level 3: 1 <_ L and the typing of X'
    A3 = '( %s /\\ -. ( 1st ` J ) = ( inr ` (/) ) )' % A2
    pj3 = Proj(w, A3)
    cl3 = Closure(w, A3, {'Z': ('NN', lift(w, pj('Z e. NN'), A3)), 'U': ('NN0', lift(w, pj('U e. NN0'), A3)),
                          'I': ('NN0', lift(w, ire, A3))})
    ule = w.s([cl3.mem('U', 'RR'), cl3.mem('I', 'RR'), w.s([], 'simplr', '( %s -> -. I < U )' % A3)], 'nltled',
              '( %s -> U <_ I )' % A3)
    B = BZ_('Z'); BP = '( ( ( 5 x. ( ( U x. %s ) + 1 ) ) + 2 ) + %s )' % (B, B)
    two = w.s([w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i',
              '( %s -> 2 e. ( ZZ>= ` 2 ) )' % A3)
    zlt = w.s([two, cl3.mem('Z', 'NN'), w.inst('nloglt')], 'syl2anc', '( %s -> Z < ( 2 ^ %s ) )' % (A3, B))
    cl3.atom(NL('Z'))
    bbp = linarith(w, A3, [cl3.ge0('( 5 x. ( ( U x. %s ) + 1 ) )' % B)], '%s <_ %s' % (B, BP), closure=cl3)
    bp2 = linarith(w, A3, [cl3.ge0(B)], '( ( 5 x. ( ( U x. %s ) + 1 ) ) + 2 ) <_ %s' % (B, BP), closure=cl3)
    LETQ = ante_of(dbstmt('t13srcq'))[0]
    qa = LETQ.split(' ) /\\ ( ( U <_ I')[0][2:] + ' )'      # the typing and the first equations
    # build t13srcq's antecedent: its first conjunct from A3, then the extra facts
    first = ante_of(dbstmt('t13srcq'))[0]
    f1 = conjs(first)[0]
    typ = lift(w, pj('( ( Z e. NN /\\ G e. NN0 /\\ Y e. NN ) /\\ ( U e. NN0 /\\ O e. NN0 /\\ N e. NN0 ) )'), A3)
    eqs = lift(w, pj(conjs(conjs(LET13)[1])[0]), A3)
    part1 = cj(w, A3, [typ, eqs])
    assert fof(w, part1, A3) == f1, (fof(w, part1, A3)[:200], f1[:200])
    q = w.s([cj(w, A3, [part1, cj(w, A3, [cj(w, A3, [ule, zlt]), cj(w, A3, [cl3.mem(B, 'NN0'), cl3.mem(BP, 'NN0')]),
                                                  cj(w, A3, [bbp, bp2])])]), w.inst('t13srcq')], 'syl',
            '( %s -> %s )' % (A3, ante_of(dbstmt('t13srcq'))[1].replace(' B ', ' %s ' % B).replace("B'", BP)
                              .replace('( B + 1 )', '( %s + 1 )' % B).replace('x. B )', 'x. %s )' % B)))
    l1 = proj(w, A3, proj(w, A3, q, 1), 1)                 # 1 <_ L
    jne = w.s([w.s([], 'simpr', '( %s -> -. ( 1st ` J ) = ( inr ` (/) ) )' % A3)], 'neqned',
              '( %s -> ( 1st ` J ) =/= ( inr ` (/) ) )' % A3)
    sm = w.s([cj(w, A3, [lift(w, w.s([], 'id', '( %s -> %s )' % (A, A)), A3), cj(w, A3, [jne, l1])]), w.inst('t13srcsm')],
             'syl', '( %s -> %s )' % (A3, ante_of(dbstmt('t13srcsm'))[1]))
    xt = proj(w, A3, proj(w, A3, sm, 1), 0)                # X' e. ( ... ) X. NN0
    x2 = proj(w, A3, proj(w, A3, sm, 1), 1)                # ( 2nd ` X' ) e. NN0
    c3 = w.s([lift(w, cjA, A3), x2, w.inst('nn0addcl')], 'syl2anc',
             "( %s -> ( ( C' + ( 2nd ` J ) ) + ( 2nd ` X' ) ) e. NN0 )" % A3)
    A31 = "( %s /\\ ( 1st ` X' ) = ( inr ` (/) ) )" % A3
    b3 = w.s([w.s([fv], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (A31, FX)),
              w.s([c3], 'adantr', "( %s -> ( ( C' + ( 2nd ` J ) ) + ( 2nd ` X' ) ) e. NN0 )" % A31), w.inst('opelxpi')],
             'syl2anc', '( %s -> %s e. %s )' % (A31, P3, T))
    A32 = "( %s /\\ -. ( 1st ` X' ) = ( inr ` (/) ) )" % A3
    xne = w.s([w.s([], 'simpr', "( %s -> -. ( 1st ` X' ) = ( inr ` (/) ) )" % A32)], 'neqned',
              "( %s -> ( 1st ` X' ) =/= ( inr ` (/) ) )" % A32)
    pay = w.s([w.s([xt], 'adantr', "( %s -> X' e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )" % A32), xne], 'a5pay',
              "( %s -> ( ( 1st ` ( 2nd ` ( 1st ` X' ) ) ) e. NN0 /\\ ( 2nd ` ( 2nd ` ( 1st ` X' ) ) ) e. Word NN0 ) )" % A32)
    feq = lift(w, pj("F = ( 1st ` ( 2nd ` ( 1st ` X' ) ) )"), A32)
    aeq = lift(w, pj("A = ( 2nd ` ( 2nd ` ( 1st ` X' ) ) )"), A32)
    fn = w.s([feq, proj(w, A32, pay, 0)], 'eqeltrd', '( %s -> F e. NN0 )' % A32)
    aw = w.s([aeq, proj(w, A32, pay, 1)], 'eqeltrd', '( %s -> A e. Word NN0 )' % A32)
    vc = w.s([fn, aw, w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % A32)
    qeq = lift(w, pj("Q' = ( F Verify A )"), A32)
    vq = w.s([qeq, vc], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % A32)
    q2 = w.s([vq, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` Q' ) e. NN0 )" % A32)
    c4 = w.s([w.s([c3], 'adantr', "( %s -> ( ( C' + ( 2nd ` J ) ) + ( 2nd ` X' ) ) e. NN0 )" % A32), q2,
              w.inst('nn0addcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A32, C4))
    if typed:
        pr = w.s([fn, aw, w.inst('opelxpi')], 'syl2anc', '( %s -> <. F , A >. e. ( NN0 X. Word NN0 ) )' % A32)
        il = w.s([pr, w.inst('djulcl')], 'syl', '( %s -> ( inl ` <. F , A >. ) e. %s )' % (A32, DJ))
        iex = w.s([il, w.s([fv], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (A32, DJ)), w.inst('ifcl')], 'syl2anc',
                  '( %s -> %s e. %s )' % (A32, FST4, DJ))
    else:
        iex = w.s([w.s([w.s([], 'fvex', '( inl ` <. F , A >. ) e. _V'), fv], 'ifex', '%s e. _V' % FST4)], 'a1i',
                  '( %s -> %s e. _V )' % (A32, FST4))
    b4 = w.s([iex, c4, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. %s )' % (A32, P4, T))
    i3 = w.s([b3, b4], 'ifclda', '( %s -> %s e. %s )' % (A3, IF3, T))
    i2 = w.s([b2, i3], 'ifclda', '( %s -> %s e. %s )' % (A2, IF2, T))
    i1 = w.s([b1, i2], 'ifclda', '( %s -> %s e. %s )' % (A, IF1, T))
    if typed:
        w.qed([sv, i1], 'eqeltrd', '( %s -> ( %s Search N ) e. %s )' % (A, VP, T))
    else:
        se = w.s([sv, i1], 'eqeltrd', '( %s -> ( %s Search N ) e. %s )' % (A, VP, T))
        w.qed([se, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( %s Search N ) ) e. NN0 )' % (A, VP))
    return run(w)


def prove_tree(w, A, text, leaf):
    """( A -> text ) for a conjunction tree, leaves by leaf(t) -> step"""
    t = ' '.join(text.split())
    if t.startswith('( ') and ('/\\' in t):
        try:
            ps = conjs(t)
        except Exception:
            ps = None
        if ps and len(ps) in (2, 3):
            return cj(w, A, [prove_tree(w, A, p, leaf) for p in ps])
    return leaf(t)


# ------------------------------------------------------------------ srchcst
def srch_v(label, desc, typed):
    from tm import sub
    w = W(label, desc)
    A = '( V e. Scales /\\ N e. NN0 )'
    pj = Proj(w, A)
    st = w.s([pj('V e. Scales'), w.inst('scalestup')], 'syl', '( %s -> %s )' % (A, ante_of(dbstmt('scalestup'))[1]))
    Z, G, Y, U, O = PZ('V'), PZ99('V'), PY('V'), PT('V'), PTH('V')
    m = {'Z': Z, 'G': G, 'Y': Y, 'U': U, 'O': O}
    defs = [('R', '( ( Z Reservoir G ) ` Y )'), ('I', '( # ` ( 1st ` R ) )'), ('Q', '( ( 1st ` R ) substr <. ( I - U ) , I >. )'),
            ('L', '( 1st ` ( ProdL ` Q ) )'), ('X', '( L ^ 5 )'), ("C'", "( ( ( ( 2nd ` R ) + U ) + ( 2nd ` ( ProdL ` Q ) ) ) + 2 )"),
            ('J', '( ( ( ( ( Q Scan X ) ` Z ) ` O ) ` 1 ) ` X )'), ("J'", '( 1st ` ( 2nd ` ( 1st ` J ) ) )'),
            ('W', '( 2nd ` ( 2nd ` ( 1st ` J ) ) )'), ("X'", "( ( L Extract N ) ` W )"),
            ('F', "( 1st ` ( 2nd ` ( 1st ` X' ) ) )"), ('A', "( 2nd ` ( 2nd ` ( 1st ` X' ) ) )"),
            ("Q'", '( F Verify A )'), ("V'", '<. <. <. Z , G >. , <. Y , U >. >. , O >.')]
    for k, d in defs:
        m[k] = sub(d, m)
    LETs = sub(LET13, m)
    typ = cj(w, A, [cj(w, A, [proj(w, A, proj(w, A, st, 0), 0), proj(w, A, proj(w, A, st, 0), 1),
                              proj(w, A, proj(w, A, st, 1), 0)]),
                    cj(w, A, [proj(w, A, proj(w, A, st, 1), 1), proj(w, A, proj(w, A, st, 2), 0), pj('N e. NN0')])])

    def leaf(t):
        l, r = t.split(' = ', 1) if ' = ' in t else (None, None)
        assert l is not None and ' '.join(l.split()) == ' '.join(r.split()), t[:200]
        return w.s([], 'eqidd', '( %s -> %s )' % (A, t))
    parts = conjs(LETs)
    assert fof(w, typ, A) == parts[0], (fof(w, typ, A)[:150], parts[0][:150])
    h = cj(w, A, [typ, prove_tree(w, A, parts[1], leaf)])
    if typed:
        c = w.s([h, w.inst('srchtypl')], 'syl', '( %s -> ( %s Search N ) e. %s )' % (A, m["V'"], DJT))
    else:
        c = w.s([h, w.inst('srchcstl')], 'syl', '( %s -> ( 2nd ` ( %s Search N ) ) e. NN0 )' % (A, m["V'"]))
    veq = proj(w, A, proj(w, A, st, 2), 1)
    e1 = w.s([veq], 'oveq1d', '( %s -> ( V Search N ) = ( %s Search N ) )' % (A, m["V'"]))
    if typed:
        w.qed([e1, c], 'eqeltrd', '( %s -> ( V Search N ) e. %s )' % (A, DJT))
        return run(w)
    e2 = w.s([e1], 'fveq2d', '( %s -> ( 2nd ` ( V Search N ) ) = ( 2nd ` ( %s Search N ) ) )' % (A, m["V'"]))
    w.qed([e2, c], 'eqeltrd', '( %s -> ( 2nd ` ( V Search N ) ) e. NN0 )' % A)
    return run(w)


def srchcst():
    return srch_v('srchcst', 'The search cost is a natural number for every tuple of scales (Lean: Alg.search returns a '
                  'natural cost).', False)


def srchtyp():
    return srch_v('srchtyp', 'The search value at a tuple of scales is an Option of a pair ( number , word ) with a '
                  'natural cost (Lean: the type of Alg.search).', True)


# ------------------------------------------------------------------ srchgetd
def srchgetd():
    w = W('srchgetd', 'The value the machine outputs, getD ( 0 , [] ) of the search, is a pair of a number and a word '
                      '(Lean: searchFun n : N x List N).')
    A = '( V e. Scales /\\ N e. NN0 )'
    SE = '( V Search N )'
    ty = w.s([w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('srchtyp')], 'syl', '( %s -> %s e. %s )' % (A, SE, DJT))
    f1 = w.s([ty, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` %s ) e. %s )' % (A, SE, DJ))
    A1 = '( %s /\\ ( 1st ` %s ) = ( inr ` (/) ) )' % (A, SE)
    z = w.s([w.s([w.s([], '0nn0', '0 e. NN0'), w.s([], 'wrd0', '(/) e. Word NN0'), w.inst('opelxpi')], 'mp2an',
                 '<. 0 , (/) >. e. ( NN0 X. Word NN0 )')], 'a1i', '( %s -> <. 0 , (/) >. e. ( NN0 X. Word NN0 ) )' % A1)
    A2 = '( %s /\\ -. ( 1st ` %s ) = ( inr ` (/) ) )' % (A, SE)
    ne = w.s([w.s([], 'simpr', '( %s -> -. ( 1st ` %s ) = ( inr ` (/) ) )' % (A2, SE))], 'neqned',
             '( %s -> ( 1st ` %s ) =/= ( inr ` (/) ) )' % (A2, SE))
    dj = w.s([w.s([w.s([f1], 'adantr', '( %s -> ( 1st ` %s ) e. %s )' % (A2, SE, DJ)), ne], 'jca',
                  '( %s -> ( ( 1st ` %s ) e. %s /\\ ( 1st ` %s ) =/= ( inr ` (/) ) ) )' % (A2, SE, DJ, SE)),
              w.inst('algdjun')], 'syl',
             '( %s -> ( ( 2nd ` ( 1st ` %s ) ) e. ( NN0 X. Word NN0 ) /\\ ( 1st ` %s ) = ( inl ` ( 2nd ` ( 1st ` %s ) ) ) ) )'
             % (A2, SE, SE, SE))
    p = w.s([dj], 'simpld', '( %s -> ( 2nd ` ( 1st ` %s ) ) e. ( NN0 X. Word NN0 ) )' % (A2, SE))
    w.qed([z, p], 'ifclda', '( %s -> %s e. ( NN0 X. Word NN0 ) )' % (A, GETDV))
    return run(w)


class Kit:
    """chains of the ExpB kit under the antecedent A at the real M (text Mt)"""
    def __init__(self, w, A, cl, Mt, m1, m0):
        self.w, self.A, self.cl, self.M = w, A, cl, Mt
        self.mre = cl.mem(Mt, 'RR'); self.m1 = m1; self.m0 = m0

    def f(self, x):
        return '( %s -> %s )' % (self.A, x)

    def num(self, text):
        return linarith(self.w, self.A, [], text, closure=self.cl)

    def con(self, a, K, ale):
        cl = self.cl
        return self.w.s([self.mre, self.m1, cl.mem(K, 'RR'), cl.ge0(K), cl.mem(a, 'RR'), ale], 'xbcon',
                        self.f(XB(a, K, self.M)))

    def lin2(self, a, K, ale):
        cl = self.cl
        km = linarith(self.w, self.A, [self.m1big], '%s <_ %s' % (K, self.M), closure=cl)
        return self.w.s([self.mre, self.m1, cl.mem(K, 'RR'), cl.ge0(K), km, cl.mem(a, 'RR'), ale], 'xblin2',
                        self.f(XB(a, '2', self.M)))

    def two(self, T, C, tle):
        cl = self.cl
        return self.w.s([self.mre, cl.mem(C, 'RR'), cl.mem(T, 'NN0'), tle], 'xb2pow', self.f(XB('( 2 ^ %s )' % T, C, self.M)))

    def mul(self, a, b, C, D, F, sa, sb):
        cl = self.cl
        return self.w.s([self.mre, self.m0, cl.mem(C, 'RR'), cl.mem(D, 'RR'), cl.mem(F, 'RR'),
                         self.num('( %s + %s ) <_ %s' % (C, D, F)), cl.mem(a, 'RR'), cl.ge0(a), cl.mem(b, 'RR'), cl.ge0(b),
                         sa, sb], 'xbmul', self.f(XB('( %s x. %s )' % (a, b), F, self.M)))

    def add(self, a, b, C, D, G, F, sa, sb):
        cl = self.cl
        return self.w.s([self.mre, self.m1, cl.mem(C, 'RR'), cl.mem(D, 'RR'), cl.mem(G, 'RR'), cl.mem(F, 'RR'),
                         self.num('%s <_ %s' % (C, G)), self.num('%s <_ %s' % (D, G)), self.num('( %s + 1 ) <_ %s' % (G, F)),
                         cl.mem(a, 'RR'), cl.mem(b, 'RR'), sa, sb], 'xbadd', self.f(XB('( %s + %s )' % (a, b), F, self.M)))

    def pow(self, a, N, C, F, sa):
        cl = self.cl
        return self.w.s([self.mre, self.m0, cl.mem(C, 'RR'), cl.mem(F, 'RR'), cl.mem(N, 'NN0'),
                         self.num('( %s x. %s ) <_ %s' % (N, C, F)), cl.mem(a, 'RR'), cl.ge0(a), sa], 'xbpow',
                        self.f(XB('( %s ^ %s )' % (a, N), F, self.M)))

    def tmb(self, b, C, F, sb):
        cl = self.cl
        return self.w.s([self.mre, self.m1, cl.mem(C, 'RR'), cl.ge0(C), cl.mem(F, 'RR'),
                         self.num('( ( 3 x. %s ) + ; 1 1 ) <_ %s' % (C, F)), cl.mem(b, 'NN0'), sb], 'xbtmb',
                        self.f(XB('( TMB ` %s )' % b, F, self.M)))


def rel(w, A, lab, parts, concl):
    return use(w, A, lab, parts, concl)


# ------------------------------------------------------------------ sbexpb
def sbexpb():
    from tm import sub
    import importlib
    two_pow_le4 = importlib.import_module('t14_c_sc').two_pow_le4
    w = W('sbexpb', 'The machine step bound in the window: searchBound + 1 <_ exp ( 2000 ell2 n ell3 n ) once '
                    'ell2 n >= 200, ell3 n >= 12, log ( 37 C + K + 5 ) <_ ell3 n and the algorithmic cost is at most '
                    'exp ( 100 ell2 n ell3 n ) (Lean: searchBound_ExpB, pointwise).')
    A = STMTS14['sbexpb'].split(' -> ')[0][2:]
    pj = Proj(w, A)
    nuz = pj('N e. ( ZZ>= ` 3 )')
    nnn = w.s([nuz, w.inst('eluz3nn')], 'syl', '( %s -> N e. NN )' % A)
    cl = Closure(w, A, {'N': ('NN', nnn), 'C': [('NN0', pj('C e. NN0'))], 'K': ('NN', pj('K e. NN'))})
    l2, l3, lN = L2('N'), L3('N'), LOG('N')
    h200 = pj('; ; 2 0 0 <_ %s' % l2); h12 = pj('; 1 2 <_ %s' % l3); c1000 = pj('; ; ; 1 0 0 0 <_ C')
    hA = pj('( log ` %s ) <_ %s' % (ACON, l3)); hc = pj(COST('N'))
    import t14_d_win as dw
    lNrp, lN3, ef2, v2 = dw.logn_facts(w, A, cl, nnn, nuz, h200, l2, lN)
    cl.have(l2, 'RR+', w.s([cl.mem(l2, 'RR'), linarith(w, A, [h200], '0 < %s' % l2, closure=cl)], 'elrpd',
                           '( %s -> %s e. RR+ )' % (A, l2)))
    v3 = w.s([cl.mem('N', 'NN0'), w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, l3, l2))
    l3re = w.s([v3, cl.mem('( log ` %s )' % l2, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A, l3))
    cl.have(l3, 'RR', l3re); cl.atom(l3)
    cl.have(l3, 'RR+', w.s([l3re, linarith(w, A, [h12], '0 < %s' % l3, closure=cl)], 'elrpd', '( %s -> %s e. RR+ )' % (A, l3)))
    SCN = SC('C', 'K', 'N')
    Z, W9, Y, T, TH = PZ(SCN), PZ99(SCN), PY(SCN), PT(SCN), PTH(SCN)
    # the window
    win = use(w, A, 'sctmwin', [pj(CK), [nuz, h200, linarith(w, A, [h12], '3 <_ %s' % l3, closure=cl)]], WIN('C', 'K', 'N'))
    msc = proj(w, A, win, 0); iw = proj(w, A, proj(w, A, win, 1), 0); thb = proj(w, A, proj(w, A, win, 1), 1)
    thlo, thhi = proj(w, A, thb, 0), proj(w, A, thb, 1)
    stup = w.s([msc, w.inst('scalestup')], 'syl', '( %s -> %s )' % (A, sub(ante_of(dbstmt('scalestup'))[1], {'V': SCN})))
    znn = proj(w, A, proj(w, A, stup, 0), 0); wn0 = proj(w, A, proj(w, A, stup, 0), 1)
    ynn = proj(w, A, proj(w, A, stup, 1), 0); tn0 = proj(w, A, proj(w, A, stup, 1), 1)
    thn0 = proj(w, A, proj(w, A, stup, 2), 0)
    for x, k, s_ in ((Z, 'NN', znn), (W9, 'NN0', wn0), (Y, 'NN', ynn), (T, 'NN0', tn0), (TH, 'NN0', thn0)):
        cl.have(x, k, s_); cl.atom(x)
    cst = w.s([cj(w, A, [msc, cl.mem('N', 'NN0')]), w.inst('srchcst')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (A, SE_()))
    CO = '( 2nd ` %s )' % SE_()
    cl.have(CO, 'NN0', cst); cl.atom(CO)
    # unfold the window
    AA = '<. <. C , ( 1 / K ) >. , N >.'; BB = '( 1st ` %s )' % SCN
    body = sub(ante_of(dbstmt('inwinbr'))[1], {'A': AA, 'B': BB})
    ib = w.s([w.s([w.s([], 'opex', '%s e. _V' % AA)], 'a1i', '( %s -> %s e. _V )' % (A, AA)),
              w.s([w.s([], 'fvex', '%s e. _V' % BB)], 'a1i', '( %s -> %s e. _V )' % (A, BB)), w.inst('inwinbr')], 'syl2anc',
             '( %s -> %s )' % (A, body))
    bd = w.s([iw, ib], 'mpbid', '( %s -> %s )' % (A, conjs_iff(body)[1]))
    CE = '<. C , ( 1 / K ) >.'
    o1 = w.s([w.s([w.s([], 'opex', '%s e. _V' % CE)], 'a1i', '( %s -> %s e. _V )' % (A, CE)), cl.mem('N', 'NN0'), w.inst('op1stg')],
             'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (A, AA, CE))
    o2 = w.s([w.s([w.s([], 'opex', '%s e. _V' % CE)], 'a1i', '( %s -> %s e. _V )' % (A, CE)), cl.mem('N', 'NN0'), w.inst('op2ndg')],
             'syl2anc', '( %s -> ( 2nd ` %s ) = N )' % (A, AA))
    o3 = w.s([cl.mem('C', 'NN0'), cl.mem('( 1 / K )', 'RR'), w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = C )' % (A, CE))
    o4 = w.s([cl.mem('C', 'NN0'), cl.mem('( 1 / K )', 'RR'), w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = ( 1 / K ) )' % (A, CE))
    r1 = w.s([w.s([o1], 'fveq2d', '( %s -> ( 1st ` ( 1st ` %s ) ) = ( 1st ` %s ) )' % (A, AA, CE)), o3], 'eqtrd',
             '( %s -> ( 1st ` ( 1st ` %s ) ) = C )' % (A, AA))
    r2 = w.s([w.s([o1], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` %s ) )' % (A, AA, CE)), o4], 'eqtrd',
             '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 1 / K ) )' % (A, AA))
    rules = {'( 1st ` ( 1st ` %s ) )' % AA: ('C', r1), '( 2nd ` ( 1st ` %s ) )' % AA: ('( 1 / K )', r2),
             '( 2nd ` %s )' % AA: ('N', o2)}
    rw, body2 = w.wcongr(conjs_iff(body)[1], {}, A, {}, rules=rules)
    bd2 = w.s([bd, rw], 'mpbid', '( %s -> %s )' % (A, body2))
    core = proj(w, A, bd2, 1)
    zz = proj(w, A, proj(w, A, core, 0), 0); ww = proj(w, A, proj(w, A, core, 0), 1)
    yy = proj(w, A, proj(w, A, core, 1), 0); tt = proj(w, A, proj(w, A, core, 1), 1)
    zhi = proj(w, A, zz, 1); whi = proj(w, A, ww, 1); yhi = proj(w, A, yy, 1); thi = proj(w, A, tt, 1)
    # M and its size
    Mt = MM('N')
    m2400 = nlinarith(w, A, [h200, h12], '; ; ; 2 4 0 0 <_ %s' % Mt, closure=cl)
    m1 = linarith(w, A, [m2400], '1 <_ %s' % Mt, closure=cl); m0 = linarith(w, A, [m2400], '0 <_ %s' % Mt, closure=cl)
    kit = Kit(w, A, cl, Mt, m1, m0); kit.m1big = m2400
    # z-bounds of w and y
    z1 = w.s([cl.mem(Z, 'NN'), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (A, Z))
    zr = cl.mem(Z, 'RR')
    zc = '( %s ^c %s )' % (Z, C99); zk = '( %s ^c ( 1 - ( 1 / K ) ) )' % (Z,)
    z1c = w.s([cl.mem(Z, 'CC')], 'cxp1d', '( %s -> ( %s ^c 1 ) = %s )' % (A, Z, Z))
    p99 = use(w, A, 'cxplea', [[zr, z1], [cl.mem(C99, 'RR'), cl.mem('1', 'RR')], linarith(w, A, [], '%s <_ 1' % C99, closure=cl)],
              '%s <_ ( %s ^c 1 )' % (zc, Z))
    rk0 = w.s([pj('K e. NN'), w.inst('nnrecgt0')], 'syl', '( %s -> 0 < ( 1 / K ) )' % A)
    rkre = cl.mem('( 1 / K )', 'RR'); cl.atom('( 1 / K )')
    pk = use(w, A, 'cxplea', [[zr, z1], [cl.mem('( 1 - ( 1 / K ) )', 'RR'), cl.mem('1', 'RR')],
                               linarith(w, A, [rk0], '( 1 - ( 1 / K ) ) <_ 1', closure=cl)], '%s <_ ( %s ^c 1 )' % (zk, Z))
    for x in (zc, zk, '( %s ^c 1 )' % Z):
        cl.atom(x)
    cl.have(zc, 'RR', w.s([w.s([cl.mem(Z, 'RR+'), cl.mem(C99, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, zc))], 'rpred', '( %s -> %s e. RR )' % (A, zc)))
    cl.have(zk, 'RR', w.s([w.s([cl.mem(Z, 'RR+'), cl.mem('( 1 - ( 1 / K ) )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, zk))], 'rpred', '( %s -> %s e. RR )' % (A, zk)))
    cl.have('( %s ^c 1 )' % Z, 'RR', w.s([z1c, zr], 'eqeltrd', '( %s -> ( %s ^c 1 ) e. RR )' % (A, Z)))
    w4 = linarith(w, A, [whi, p99, z1c], '%s <_ ( 4 x. %s )' % (W9, Z), closure=cl)
    y4 = linarith(w, A, [yhi, pk, z1c], '%s <_ ( 4 x. %s )' % (Y, Z), closure=cl)
    # the sum S and its logarithm
    S = '( ( ( ( ( %s + %s ) + %s ) + %s ) + C ) + K )' % (Z, W9, Y, T)
    CL = '( ( C x. %s ) x. %s )' % (l2, l3)
    l3ge = linarith(w, A, [h12], '1 <_ %s' % l3, closure=cl)
    l2M = nlinarith(w, A, [h200, l3ge], '%s <_ %s' % (l2, Mt), closure=cl)
    sS = nlinarith(w, A, [zhi, w4, y4, thi, l2M, m1, cl.ge0('C'), cl.ge0('K'), c1000], '%s <_ ( %s x. %s )' % (S, ACON, Mt),
                   closure=cl)
    s1 = linarith(w, A, [z1, cl.ge0(W9), cl.ge0(Y), cl.ge0(T), cl.ge0('C'), cl.ge0('K')], '1 <_ %s' % S, closure=cl)
    snn = w.s([w.s([cl.mem(S, 'NN0'), s1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (A, S, S)),
               w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (S, S, S))], 'a1i',
                   '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A, S, S, S))], 'mpbird', '( %s -> %s e. NN )' % (A, S))
    cl.have(S, 'NN', snn)
    AM = '( %s x. %s )' % (ACON, Mt)
    amrp = cl.mem(AM, 'RR+')
    lS = dw.logmono(w, A, cl, S, AM, sS)
    lm1 = w.s([cl.mem(ACON, 'RR+'), cl.mem(Mt, 'RR+')], 'relogmuld', '( %s -> ( log ` %s ) = ( ( log ` %s ) + ( log ` %s ) ) )' % (A, AM, ACON, Mt))
    lm2 = w.s([cl.mem(l2, 'RR+'), cl.mem(l3, 'RR+')], 'relogmuld', '( %s -> ( log ` %s ) = ( ( log ` %s ) + ( log ` %s ) ) )' % (A, Mt, l2, l3))
    ll3 = w.s([l3re, l3ge, w.inst('extrwlogle')], 'syl2anc', '( %s -> ( log ` %s ) <_ ( %s - 1 ) )' % (A, l3, l3))
    for x in ('( log ` %s )' % S, '( log ` %s )' % AM, '( log ` %s )' % ACON, '( log ` %s )' % Mt, '( log ` %s )' % l2,
              '( log ` %s )' % l3):
        cl.atom(x)
    logS = linarith(w, A, [lS, lm1, lm2, ll3, v3, hA], '( log ` %s ) <_ ( 3 x. %s )' % (S, l3), closure=cl)
    nS = w.s([snn, w.inst('nlog2log')], 'syl', '( %s -> ( 2 Nlog %s ) <_ ( 2 x. ( log ` %s ) ) )' % (A, S, S))
    cl.atom(NL(S))
    bs = '( ( 2 Nlog %s ) + 2 )' % S
    bs7 = linarith(w, A, [nS, logS, h12], '%s <_ ( 7 x. %s )' % (bs, l3), closure=cl)
    # T bs + 1 <_ 36 M
    tbs = w.s([cl.mem(T, 'RR'), cl.mem('( 5 x. %s )' % l2, 'RR'), cl.mem(bs, 'RR'), cl.mem('( 7 x. %s )' % l3, 'RR'),
               cl.ge0(T), cl.ge0(bs), thi, bs7], 'lemul12ad', '( %s -> ( %s x. %s ) <_ ( ( 5 x. %s ) x. ( 7 x. %s ) ) )' % (A, T, bs, l2, l3))
    TB = '( ( %s x. %s ) + 1 )' % (T, bs)
    tb36 = nlinarith(w, A, [tbs, m1], '%s <_ ( ; 3 6 x. %s )' % (TB, Mt), closure=cl)
    # theta >= 3 , N + theta <_ N theta
    lc = '( %s ^c %s )' % (lN, C65)
    lN1 = linarith(w, A, [lN3], '1 <_ %s' % lN, closure=cl)
    c1 = use(w, A, 'cxplea', [[cl.mem(lN, 'RR'), lN1], [cl.mem('1', 'RR'), cl.mem(C65, 'RR')],
                              linarith(w, A, [], '1 <_ %s' % C65, closure=cl)], '( %s ^c 1 ) <_ %s' % (lN, lc))
    c2 = w.s([cl.mem(lN, 'CC')], 'cxp1d', '( %s -> ( %s ^c 1 ) = %s )' % (A, lN, lN))
    for x in (lc, '( %s ^c 1 )' % lN):
        cl.atom(x)
    cl.have(lc, 'RR', w.s([w.s([cl.mem(lN, 'RR+'), cl.mem(C65, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, lc))], 'rpred', '( %s -> %s e. RR )' % (A, lc)))
    cl.have('( %s ^c 1 )' % lN, 'RR', w.s([c2, cl.mem(lN, 'RR')], 'eqeltrd', '( %s -> ( %s ^c 1 ) e. RR )' % (A, lN)))
    th3 = linarith(w, A, [thlo, c1, c2, lN3], '3 <_ %s' % TH, closure=cl)
    n3 = w.s([nuz, w.inst('eluzle')], 'syl', '( %s -> 3 <_ N )' % A)
    NT = '( N + %s )' % TH; NxT = '( N x. %s )' % TH
    ntle = nlinarith(w, A, [n3, th3], '%s <_ %s' % (NT, NxT), closure=cl)
    nt1 = linarith(w, A, [n3, th3], '1 <_ %s' % NT, closure=cl)
    ntnn = w.s([w.s([cl.mem(NT, 'NN0'), nt1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (A, NT, NT)),
                w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (NT, NT, NT))], 'a1i',
                    '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A, NT, NT, NT))], 'mpbird', '( %s -> %s e. NN )' % (A, NT))
    cl.have(NT, 'NN', ntnn)
    th0 = linarith(w, A, [th3], '0 < %s' % TH, closure=cl)
    cl.have(TH, 'RR+', w.s([cl.mem(TH, 'RR'), th0], 'elrpd', '( %s -> %s e. RR+ )' % (A, TH)))
    nlb = w.s([ntnn, w.inst('nlog2log')], 'syl', '( %s -> ( 2 Nlog %s ) <_ ( 2 x. ( log ` %s ) ) )' % (A, NT, NT))
    cl.atom(NL(NT))
    g1 = dw.logmono(w, A, cl, NT, NxT, ntle)
    g2 = w.s([cl.mem('N', 'RR+'), cl.mem(TH, 'RR+')], 'relogmuld', '( %s -> ( log ` %s ) = ( %s + ( log ` %s ) ) )' % (A, NxT, lN, TH))
    T16 = '( ; 1 6 x. %s )' % lc
    g3 = dw.logmono(w, A, cl, TH, T16, thhi)
    g4 = w.s([cl.mem('; 1 6', 'RR+'), cl.mem(lc, 'RR+')], 'relogmuld', '( %s -> ( log ` %s ) = ( ( log ` ; 1 6 ) + ( log ` %s ) ) )' % (A, T16, lc))
    g5 = w.s([lNrp, cl.mem(C65, 'RR')], 'logcxpd', '( %s -> ( log ` %s ) = ( %s x. ( log ` %s ) ) )' % (A, lc, C65, lN))
    two = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A)
    g6 = w.s([two, cl.mem('4', 'ZZ'), w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( 2 ^ 4 ) ) = ( 4 x. ( log ` 2 ) ) )' % A)
    g7 = w.s([w.s([w.s([], '2exp4', '( 2 ^ 4 ) = ; 1 6')], 'a1i', '( %s -> ( 2 ^ 4 ) = ; 1 6 )' % A)], 'fveq2d',
             '( %s -> ( log ` ( 2 ^ 4 ) ) = ( log ` ; 1 6 ) )' % A)
    g8 = w.s([w.s([], 'log2le1', '( log ` 2 ) < 1')], 'a1i', '( %s -> ( log ` 2 ) < 1 )' % A)
    for x in ('( log ` %s )' % NT, '( log ` %s )' % NxT, '( log ` %s )' % TH, '( log ` %s )' % T16, '( log ` ; 1 6 )',
              '( log ` %s )' % lc, '( log ` %s )' % lN, '( log ` ( 2 ^ 4 ) )', '( log ` 2 )'):
        cl.atom(x)
    cl.have('( log ` 2 )', 'RR', w.s([two, w.inst('relogcl')], 'syl', '( %s -> ( log ` 2 ) e. RR )' % A))
    bn = '( %s + 1 )' % NL(NT)
    REST = '( ( 3 x. %s ) + 9 )' % l2
    E1 = '( 2 x. %s )' % lN
    bnb = linarith(w, A, [nlb, g1, g2, g3, g4, g5, g6, g7, g8, v2, h200], '%s <_ ( %s + %s )' % (bn, E1, REST), closure=cl)
    # the chain
    M_ = Mt
    one = kit.con('1', '1', linarith(w, A, [], '1 <_ 1', closure=cl))
    e100 = w.s([cl.mem('; ; 1 0 0', 'CC'), cl.mem(l2, 'CC'), cl.mem(l3, 'CC')], 'mulassd',
               '( %s -> ( ( ; ; 1 0 0 x. %s ) x. %s ) = ( ; ; 1 0 0 x. %s ) )' % (A, l2, l3, M_))
    cst100 = w.s([hc, w.s([e100], 'fveq2d', '( %s -> ( exp ` ( ( ; ; 1 0 0 x. %s ) x. %s ) ) = %s )' % (A, l2, l3, EXP('; ; 1 0 0', M_)))],
                 'breqtrd', '( %s -> %s )' % (A, XB(CO, '; ; 1 0 0', M_)))
    k_c1 = kit.add(CO, '1', '; ; 1 0 0', '1', '; ; 1 0 0', '; ; 1 0 1', cst100, one)
    p1 = kit.two(TB, '; 3 6', tb36)
    P1 = '( 2 ^ %s )' % TB
    p2 = kit.pow(P1, '2', '; 3 6', '; 7 2', p1)
    tM = nlinarith(w, A, [thi, h12, h200], '%s <_ ( 1 x. %s )' % (T, M_), closure=cl)
    q1 = kit.two(T, '1', tM)
    q2 = kit.con('2', '2', linarith(w, A, [], '2 <_ 2', closure=cl))
    PT2 = '( ( 2 ^ %s ) + 2 )' % T
    q3 = kit.add('( 2 ^ %s )' % T, '2', '1', '2', '2', '3', q1, q2)
    R1 = '( ( %s ^ 2 ) x. %s )' % (P1, PT2)
    r1 = kit.mul('( %s ^ 2 )' % P1, PT2, '; 7 2', '3', '; 7 5', p2, q3)
    U1 = '( ; ; 1 1 1 x. ( %s + 1 ) )' % T
    u1 = kit.lin2(U1, '; ; 1 1 2', nlinarith(w, A, [tM, m2400], '%s <_ ( ; ; 1 1 2 x. %s )' % (U1, M_), closure=cl))
    t16 = kit.two('4', '4', linarith(w, A, [m1], '4 <_ ( 4 x. %s )' % M_, closure=cl))
    v16 = w.s([w.s([], '2exp4', '( 2 ^ 4 ) = ; 1 6')], 'a1i', '( %s -> ( 2 ^ 4 ) = ; 1 6 )' % A)
    c13 = linarith(w, A, [t16, v16], XB('; 1 3', '4', M_), closure=cl, atoms=[EXP('4', M_), '( 2 ^ 4 )'])
    U2 = '( ; 1 3 x. %s )' % PT2
    u2 = kit.mul('; 1 3', PT2, '4', '3', '7', c13, q3)
    UU = '( %s + %s )' % (U1, U2)
    u = kit.add(U1, U2, '2', '7', '7', '8', u1, u2)
    B1A = '( ( 5 x. %s ) + %s )' % (TB, bs)
    b1a = kit.lin2(B1A, '; ; 1 9 0', nlinarith(w, A, [tb36, bs7, l2M, h200, h12], '%s <_ ( ; ; 1 9 0 x. %s )' % (B1A, M_), closure=cl))
    xbn = w.s([cl.mem(bn, 'RR'), cl.mem('( %s + %s )' % (E1, REST), 'RR'), cl.mem(EXP('4', M_), 'RR'), bnb,
               bn_chain(w, A, cl, kit, lN, E1, REST, ef2, l2M, h200, h12, M_)], 'letrd', '( %s -> %s )' % (A, XB(bn, '4', M_)))
    B1B = '( %s + %s )' % (B1A, bn)
    b1b = kit.add(B1A, bn, '2', '4', '4', '5', b1a, xbn)
    B1 = '( %s + 1 )' % B1B
    b1 = kit.add(B1B, '1', '5', '1', '5', '6', b1b, one)
    UB = '( %s x. %s )' % (UU, B1)
    ub = kit.mul(UU, B1, '8', '6', '; 1 4', u, b1)
    T4 = '( 4 x. %s )' % T
    t4 = kit.lin2(T4, '; 2 0', nlinarith(w, A, [thi, l2M], '%s <_ ( ; 2 0 x. %s )' % (T4, M_), closure=cl))
    X1 = '( %s + %s )' % (UB, T4)
    x1 = kit.add(UB, T4, '; 1 4', '2', '; 1 4', '; 1 5', ub, t4)
    c200 = kit.lin2('; ; 2 0 0', '; ; 2 0 0', linarith(w, A, [m1], '; ; 2 0 0 <_ ( ; ; 2 0 0 x. %s )' % M_, closure=cl))
    X0 = '( %s + ; ; 2 0 0 )' % X1
    x0 = kit.add(X1, '; ; 2 0 0', '; 1 5', '2', '; 1 5', '; 1 6', x1, c200)
    cl.have('( TMB ` %s )' % X0, 'NN', w.s([cl.mem(X0, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` %s ) e. NN )' % (A, X0)))
    cl.atom('( TMB ` %s )' % X0)
    tm = kit.tmb(X0, '; 1 6', '; 5 9', x0)
    S1 = '( %s x. ( TMB ` %s ) )' % (R1, X0)
    s1_ = kit.mul(R1, '( TMB ` %s )' % X0, '; 7 5', '; 5 9', '; ; 1 3 4', r1, tm)
    t11 = kit.two('; 1 1', '; 1 1', linarith(w, A, [m1], '; 1 1 <_ ( ; 1 1 x. %s )' % M_, closure=cl))
    v11 = w.s([w.s([], '2exp11', '( 2 ^ ; 1 1 ) = ; ; ; 2 0 4 8')], 'a1i', '( %s -> ( 2 ^ ; 1 1 ) = ; ; ; 2 0 4 8 )' % A)
    c300 = linarith(w, A, [t11, v11], XB('; ; 3 0 0', '; 1 1', M_), closure=cl, atoms=[EXP('; 1 1', M_), '( 2 ^ ; 1 1 )'])
    SP = '( ; ; 3 0 0 x. %s )' % S1
    sp = kit.mul('; ; 3 0 0', S1, '; 1 1', '; ; 1 3 4', '; ; 1 4 5', c300, s1_)
    SB = '( ( %s + 1 ) x. %s )' % (CO, SP)
    assert SB == SBOUND(), (SB[:300], SBOUND()[:300])
    sb = kit.mul('( %s + 1 )' % CO, SP, '; ; 1 0 1', '; ; 1 4 5', '; ; 2 4 6', k_c1, sp)
    fin = kit.add(SB, '1', '; ; 2 4 6', '1', '; ; 2 4 6', '; ; ; 2 0 0 0', sb, one)
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
    return run(w)


def bn_chain(w, A, cl, kit, lN, E1, REST, ef2, l2M, h200, h12, M_):
    """( A -> ( ( 2 x. log N ) + REST ) <_ exp ( 4 M ) )"""
    l2 = L2('N')
    bi = w.s([cl.mem(l2, 'RR'), cl.mem('( 1 x. %s )' % M_, 'RR'), w.inst('efle')], 'syl2anc',
             '( %s -> ( %s <_ ( 1 x. %s ) <-> ( exp ` %s ) <_ %s ) )' % (A, l2, M_, l2, EXP('1', M_)))
    e = w.s([linarith(w, A, [l2M], '%s <_ ( 1 x. %s )' % (l2, M_), closure=cl), bi], 'mpbid',
            '( %s -> ( exp ` %s ) <_ %s )' % (A, l2, EXP('1', M_)))
    ln1 = w.s([ef2, e], 'eqbrtrrd', '( %s -> %s )' % (A, XB(lN, '1', M_)))
    c2 = kit.con('2', '2', linarith(w, A, [], '2 <_ 2', closure=cl))
    m = kit.mul('2', lN, '2', '1', '3', c2, ln1)
    r = kit.lin2(REST, '; 1 2', nlinarith(w, A, [h200, h12], '%s <_ ( ; 1 2 x. %s )' % (REST, M_), closure=cl))
    return kit.add(E1, REST, '3', '2', '3', '4', m, r)


# ------------------------------------------------------------------ sbexpbev
def sbexpbev():
    import t14_d_win as dw
    w = W('sbexpbev', 'Eventually the machine step bound searchBound + 1 is at most exp ( 2000 ell2 n ell3 n ), given '
                      'the algorithmic cost bound exp ( 100 ell2 n ell3 n ) eventually (Lean: searchBound_ExpB).')
    A = STMTS14['sbexpbev'].split(' -> E. m')[0][2:]
    EV = dw.EV
    a, b, c = 'n e. ( ZZ>= ` 3 )', '; ; 2 0 0 <_ %s' % L2('n'), '; 1 2 <_ %s' % L3('n')
    d = '( log ` %s ) <_ %s' % (ACON, L3('n')); e = COST('n')
    ab = '( %s /\\ %s )' % (a, b); abc = '( %s /\\ %s )' % (ab, c); abcd = '( %s /\\ %s )' % (abc, d)
    P = '( %s /\\ %s )' % (abcd, e)
    R = '( 1 <_ %s /\\ ; ; ; 2 4 0 0 <_ %s /\\ %s )' % (L2('n'), MM('n'), SBX('n'))
    e0 = dw.ev_n3(w)
    e2 = dw.evge(w, 'ell2ge', '; ; 2 0 0', L2('n'))
    e3 = dw.evge(w, 'ell3ge', '; 1 2', L3('n'))
    j1 = w.s([w.s([e0, e2], 'pm3.2i', '( %s /\\ %s )' % (EV(a), EV(b))), w.inst('extrwevan')], 'ax-mp', EV(ab))
    j2 = w.s([w.s([j1, e3], 'pm3.2i', '( %s /\\ %s )' % (EV(ab), EV(c))), w.inst('extrwevan')], 'ax-mp', EV(abc))
    pc = Proj(w, CK)
    clk = Closure(w, CK, {'C': ('NN0', pc('C e. NN0')), 'K': ('NN', pc('K e. NN'))})
    lre = w.s([clk.mem(ACON, 'RR+'), w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (CK, ACON))
    ea = w.s([lre, w.inst('ell3ge')], 'syl', '( %s -> %s )' % (CK, EV(d)))
    pa = Proj(w, A)
    j3 = w.s([cj(w, A, [w.s([j2], 'a1i', '( %s -> %s )' % (A, EV(abc))), lift(w, ea, A)]), w.inst('extrwevan')], 'syl',
             '( %s -> %s )' % (A, EV(abcd)))
    j4 = w.s([cj(w, A, [j3, pa(EV(e))]), w.inst('extrwevan')], 'syl', '( %s -> %s )' % (A, EV(P)))
    # pointwise, under CK only
    B = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (CK, P)
    pb = Proj(w, B)
    h = cj(w, B, [pb(CK), cj(w, B, [pb(a), pb(b), pb(c)]), cj(w, B, [pb(d), pb(e)])])
    sx = w.s([h, w.inst('sbexpb')], 'syl', '( %s -> %s )' % (B, SBX('n')))
    # 1 <_ ell2 n from 200 <_ ell2 n
    t1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % B)
    t200 = w.s([num.fact(w, '; ; 2 0 0', 'RR')], 'a1i', '( %s -> ; ; 2 0 0 e. RR )' % B)
    l2c = w.s([w.s([pb(a), w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % B),
               w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (B, L2('n')))
    le = w.s([t1, t200, l2c, w.s([num.le_lit(w, '1', '; ; 2 0 0')], 'a1i', '( %s -> 1 <_ ; ; 2 0 0 )' % B), pb(b)],
             'letrd', '( %s -> 1 <_ %s )' % (B, L2('n')))
    cm = Closure(w, B, {})
    cm.have(L2('n'), 'RR', l2c); cm.atom(L2('n'))
    cm.have(L3('n'), 'RR', w.s([pb(a), w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (B, L3('n')))); cm.atom(L3('n'))
    m24 = nlinarith(w, B, [pb(b), pb(c)], '; ; ; 2 4 0 0 <_ %s' % MM('n'), closure=cm)
    r = w.s([le, m24, sx], '3jca', '( %s -> %s )' % (B, R))
    r2 = w.s([r], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (CK, P, R))
    r3 = w.s([r2], 'ralrimiva', '( %s -> A. n e. NN0 ( %s -> %s ) )' % (CK, P, R))
    j5 = w.s([j4, lift(w, r3, A)], 'jca', '( %s -> ( %s /\\ A. n e. NN0 ( %s -> %s ) ) )' % (A, EV(P), P, R))
    w.qed([j5, w.inst('extrwevim')], 'syl', '( %s -> %s )' % (A, EV(R)))
    return run(w)


def conjs_iff(t):
    """( P <-> Q ) -> (P, Q) at top level"""
    from cl import split_sep
    toks = t.split()
    assert toks[0] == '(' and toks[-1] == ')'
    parts = split_sep(toks[1:-1], ('<->',))
    parts = [p if isinstance(p, str) else ' '.join(p) for p in parts]
    assert len(parts) == 2, t[:100]
    return parts


if __name__ == '__main__':
    for f in (srchcstl, srchcst, srchtypl, srchtyp, srchgetd, sbexpb, sbexpbev):
        if want(f.__name__):
            f()
