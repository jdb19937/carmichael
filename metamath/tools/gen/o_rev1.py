import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
PP = lambda u, v: '{ <. (/) , %s >. , <. 1o , %s >. }' % (u, v)
TWO = '{ (/) , 1o }'

def ne01(w):
    a = w.s([], '1n0', '1o =/= (/)'); return w.s([a], 'necomi', '(/) =/= 1o')
def sets01(w):
    z = w.s([], '0ex', '(/) e. _V'); o = w.s([], '1oex', '1o e. _V'); return z, o, w.s([z, o], 'pm3.2i', '( (/) e. _V /\\ 1o e. _V )')
def ppfn(w, A, ust, wst, U, V):
    """( A -> PP(U,V) Fn { (/) , 1o } ) from ( A -> U e. _V ), ( A -> V e. _V )"""
    z, o, zo = sets01(w); zo2 = w.s([zo], 'a1i', '( %s -> ( (/) e. _V /\\ 1o e. _V ) )' % A)
    uw = w.s([ust, wst], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A, U, V))
    n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
    i = w.inst('fnprg'); return w.s([zo2, uw, n2, i], 'syl3anc', '( %s -> %s Fn %s )' % (A, PP(U, V), TWO))
def ppv0(w, A, ust, U, V):
    z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
    n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
    i = w.inst('fvpr1g'); return w.s([z2, ust, n2, i], 'syl3anc', '( %s -> ( %s ` (/) ) = %s )' % (A, PP(U, V), U))
def ppv1(w, A, wst, U, V):
    o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
    n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
    i = w.inst('fvpr2g'); return w.s([o2, wst, n2, i], 'syl3anc', '( %s -> ( %s ` 1o ) = %s )' % (A, PP(U, V), V))
def eq_on_2o(w, A, F, Gc, fnF, fnG, vF0, vG0, vF1, vG1, U0, U1):
    """( A -> F = G ) from Fn steps and value steps ( A -> ( F ` (/) ) = U0 ) etc."""
    i = w.inst('eqfnfv'); e = w.s([fnF, fnG, i], 'syl2anc', '( %s -> ( %s = %s <-> A. i e. %s ( %s ` i ) = ( %s ` i ) ) )' % (A, F, Gc, TWO, F, Gc))
    l0 = w.s([], 'id', '( i = (/) -> i = (/) )'); c0, _ = w.wcongr('( %s ` i ) = ( %s ` i )' % (F, Gc), {'i': '(/)'}, 'i = (/)', {'i': l0})
    l1 = w.s([], 'id', '( i = 1o -> i = 1o )'); c1, _ = w.wcongr('( %s ` i ) = ( %s ` i )' % (F, Gc), {'i': '1o'}, 'i = 1o', {'i': l1})
    z, o, zo = sets01(w)
    r = w.s([c0, c1], 'ralprg', '( ( (/) e. _V /\\ 1o e. _V ) -> ( A. i e. %s ( %s ` i ) = ( %s ` i ) <-> ( ( %s ` (/) ) = ( %s ` (/) ) /\\ ( %s ` 1o ) = ( %s ` 1o ) ) ) )' % (TWO, F, Gc, F, Gc, F, Gc))
    r2 = w.s([zo, r], 'ax-mp', '( A. i e. %s ( %s ` i ) = ( %s ` i ) <-> ( ( %s ` (/) ) = ( %s ` (/) ) /\\ ( %s ` 1o ) = ( %s ` 1o ) ) )' % (TWO, F, Gc, F, Gc, F, Gc))
    p0 = w.s([vF0, vG0], 'eqtr4d', '( %s -> ( %s ` (/) ) = ( %s ` (/) ) )' % (A, F, Gc)); p1 = w.s([vF1, vG1], 'eqtr4d', '( %s -> ( %s ` 1o ) = ( %s ` 1o ) )' % (A, F, Gc))
    pj = w.s([p0, p1], 'jca', '( %s -> ( ( %s ` (/) ) = ( %s ` (/) ) /\\ ( %s ` 1o ) = ( %s ` 1o ) ) )' % (A, F, Gc, F, Gc))
    ral = w.s([pj, r2], 'sylibr', '( %s -> A. i e. %s ( %s ` i ) = ( %s ` i ) )' % (A, TWO, F, Gc))
    return w.s([ral, e], 'mpbird', '( %s -> %s = %s )' % (A, F, Gc))

# ---- ppupd0 / ppupd1
for label, idx, desc in (('ppupd0', 0, 'Updating the first of two stacks (Lean\'s Function.update at k0).'), ('ppupd1', 1, 'Updating the second of two stacks (Lean\'s Function.update at k1).')):
    w = W(label, desc)
    A = '( U e. V /\\ W e. X /\\ Y e. Z )'
    ust = w.s([w.s([], 'simp1', '( %s -> U e. V )' % A)], 'elexd', '( %s -> U e. _V )' % A)
    wst = w.s([w.s([], 'simp2', '( %s -> W e. X )' % A)], 'elexd', '( %s -> W e. _V )' % A)
    yst = w.s([w.s([], 'simp3', '( %s -> Y e. Z )' % A)], 'elexd', '( %s -> Y e. _V )' % A)
    P = PP('U', 'W'); K = '(/)' if idx == 0 else '1o'; OTHER = '1o' if idx == 0 else '(/)'
    RES = PP('Y', 'W') if idx == 0 else PP('U', 'Y')
    LHS = '( ( %s |` ( 2o \\ { %s } ) ) u. { <. %s , Y >. } )' % (P, K, K)
    LHSP = '( { <. %s , Y >. } u. ( %s |` ( 2o \\ { %s } ) ) )' % (K, P, K)
    uc = w.s([], 'uncom', '%s = %s' % (LHS, LHSP))
    # Fn of LHSP: 2o \ { K } = { OTHER }
    d1 = w.s([], 'df2o3', '2o = %s' % TWO); d2 = w.s([d1], 'difeq1i', '( 2o \\ { %s } ) = ( %s \\ { %s } )' % (K, TWO, K))
    n = ne01(w)
    d3i = w.inst('difprsn1' if idx == 0 else 'difprsn2'); d3 = w.s([n, d3i], 'ax-mp', '( %s \\ { %s } ) = { %s }' % (TWO, K, OTHER))
    d4 = w.s([d2, d3], 'eqtri', '( 2o \\ { %s } ) = { %s }' % (K, OTHER))
    fn = ppfn(w, A, ust, wst, 'U', 'W')
    ss = w.s([], 'snsspr2' if idx == 0 else 'snsspr1', '{ %s } C_ %s' % (OTHER, TWO)); ss2 = w.s([ss], 'a1i', '( %s -> { %s } C_ %s )' % (A, OTHER, TWO))
    fr = w.s([fn, ss2, w.inst('fnssres')], 'syl2anc', '( %s -> ( %s |` { %s } ) Fn { %s } )' % (A, P, OTHER, OTHER))
    d5 = w.s([d4], 'reseq2i', '( %s |` ( 2o \\ { %s } ) ) = ( %s |` { %s } )' % (P, K, P, OTHER))
    d6 = w.s([d5], 'fneq1i', '( ( %s |` ( 2o \\ { %s } ) ) Fn { %s } <-> ( %s |` { %s } ) Fn { %s } )' % (P, K, OTHER, P, OTHER, OTHER))
    fr2 = w.s([fr, d6], 'sylibr', '( %s -> ( %s |` ( 2o \\ { %s } ) ) Fn { %s } )' % (A, P, K, OTHER))
    kst = w.s([], '0ex' if idx == 0 else '1oex', '%s e. _V' % K); kst2 = w.s([kst], 'a1i', '( %s -> %s e. _V )' % (A, K))
    fs = w.s([kst2, yst, w.inst('fnsng')], 'syl2anc', '( %s -> { <. %s , Y >. } Fn { %s } )' % (A, K, K))
    nk = w.s([n], 'necomi', '1o =/= (/)') if idx == 0 else n   # need K =/= OTHER
    if idx == 0:
        nk = ne01(w)   # (/) =/= 1o
    else:
        nk = w.s([], '1n0', '1o =/= (/)')
    dj = w.s([nk, w.inst('disjsn2')], 'ax-mp', '( { %s } i^i { %s } ) = (/)' % (K, OTHER)); dj2 = w.s([dj], 'a1i', '( %s -> ( { %s } i^i { %s } ) = (/) )' % (A, K, OTHER))
    fu = w.s([fs, fr2, dj2, w.inst('fnun')], 'syl21anc', '( %s -> %s Fn ( { %s } u. { %s } ) )' % (A, LHSP, K, OTHER))
    pr = w.s([], 'df-pr', '{ %s , %s } = ( { %s } u. { %s } )' % (K, OTHER, K, OTHER))
    if idx == 0:
        pr2 = pr; prt = TWO
    else:
        pc = w.s([], 'prcom', '{ 1o , (/) } = %s' % TWO); pr2 = w.s([pc, pr], 'eqtr3i', '%s = ( { 1o } u. { (/) } )' % TWO)
    fe = w.s([pr2], 'fneq2i', '( %s Fn %s <-> %s Fn ( { %s } u. { %s } ) )' % (LHSP, TWO, LHSP, K, OTHER))
    fu2 = w.s([fu, fe], 'sylibr', '( %s -> %s Fn %s )' % (A, LHSP, TWO))
    fnR = ppfn(w, A, yst if idx == 0 else ust, wst if idx == 0 else yst, 'Y' if idx == 0 else 'U', 'W' if idx == 0 else 'Y')
    # values of LHSP
    e0 = w.s([], 'eqid', '%s = %s' % (LHSP, LHSP))
    vK = w.s([kst2, yst, e0], 'fvsnun1', '( %s -> ( %s ` %s ) = Y )' % (A, LHSP, K))
    ost = w.s([], '1oex' if idx == 0 else '0ex', '%s e. _V' % OTHER)
    oin = w.s([ost, w.inst('prid2g' if idx == 0 else 'prid1g')], 'ax-mp', '%s e. %s' % (OTHER, TWO))
    oin2 = w.s([d1], 'eleq2i', '( %s e. 2o <-> %s e. %s )' % (OTHER, OTHER, TWO)); oin3 = w.s([oin, oin2], 'mpbir', '%s e. 2o' % OTHER)
    ed = w.s([], 'eldifsn', '( %s e. ( 2o \\ { %s } ) <-> ( %s e. 2o /\\ %s =/= %s ) )' % (OTHER, K, OTHER, OTHER, K))
    nok = w.s([], '1n0', '1o =/= (/)') if idx == 0 else ne01(w)
    od = w.s([oin3, nok, ed], 'mpbir2an', '%s e. ( 2o \\ { %s } )' % (OTHER, K)); od2 = w.s([od], 'a1i', '( %s -> %s e. ( 2o \\ { %s } ) )' % (A, OTHER, K))
    vO = w.s([kst2, yst, e0, od2], 'fvsnun2', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A, LHSP, OTHER, P, OTHER))
    vP = ppv1(w, A, wst, 'U', 'W') if idx == 0 else ppv0(w, A, ust, 'U', 'W')
    vO2 = w.s([vO, vP], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (A, LHSP, OTHER, 'W' if idx == 0 else 'U'))
    if idx == 0:
        vF0, vF1 = vK, vO2; vG0 = ppv0(w, A, yst, 'Y', 'W'); vG1 = ppv1(w, A, wst, 'Y', 'W'); U0, U1 = 'Y', 'W'
    else:
        vF0, vF1 = vO2, vK; vG0 = ppv0(w, A, ust, 'U', 'Y'); vG1 = ppv1(w, A, yst, 'U', 'Y'); U0, U1 = 'U', 'Y'
    eq = eq_on_2o(w, A, LHSP, RES, fu2, fnR, vF0, vG0, vF1, vG1, U0, U1)
    w.qed([uc, eq], 'eqtrid', '( %s -> %s = %s )' % (A, LHS, RES))
    run(w)

# ---- stk2pp0 / stk2pp1
for label, idx, desc in (('stk2pp0', 0, 'The initial stacks of a two-stack machine as a pair of pairs.'), ('stk2pp1', 1, 'The halting stacks of a two-stack machine as a pair of pairs.')):
    w = W(label, desc)
    A = 'U e. V'
    K = '(/)' if idx == 0 else '1o'
    MP = '( k e. %s |-> if ( k = %s , U , (/) ) )' % (TWO, K)
    RES = PP('U', '(/)') if idx == 0 else PP('(/)', 'U')
    ust = w.s([], 'elex', '( U e. V -> U e. _V )')
    z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
    ie = w.s([ust, z2, w.inst('ifexg')], 'syl2anc', '( %s -> if ( k = %s , U , (/) ) e. _V )' % (A, K))
    ie2 = w.s([ie], 'adantr', '( ( %s /\\ k e. %s ) -> if ( k = %s , U , (/) ) e. _V )' % (A, TWO, K))
    fn = w.s([ie2], 'fnmptd', '( %s -> %s Fn %s )' % (A, MP, TWO))
    fnR = ppfn(w, A, ust if idx == 0 else z2, z2 if idx == 0 else ust, 'U' if idx == 0 else '(/)', '(/)' if idx == 0 else 'U')
    e0 = w.s([], 'eqid', '%s = %s' % (MP, MP))
    def mpval(at):
        l = w.s([], 'id', '( k = %s -> k = %s )' % (at, at)); c, body = w.congr('if ( k = %s , U , (/) )' % K, {'k': at}, 'k = %s' % at, {'k': l})
        f = w.s([c, e0], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (at, TWO, body, MP, at, body))
        st = w.s([], '0ex' if at == '(/)' else '1oex', '%s e. _V' % at)
        m = w.s([st, w.inst('prid1g' if at == '(/)' else 'prid2g')], 'ax-mp', '%s e. %s' % (at, TWO)); m2 = w.s([m], 'a1i', '( %s -> %s e. %s )' % (A, at, TWO))
        bx = w.s([ust, z2, w.inst('ifexg')], 'syl2anc', '( %s -> %s e. _V )' % (A, body))
        f2 = w.s([m2, bx, f], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (A, MP, at, body))
        # evaluate body
        if at == K:
            ev, res = evaluate(w, A, body, {})
        else:
            ne = w.s([], '1n0', '1o =/= (/)') if at == '1o' else ne01(w)
            ne2 = w.s([ne], 'a1i', '( %s -> %s =/= %s )' % (A, at, K)); ne3 = w.s([ne2], 'neneqd', '( %s -> -. %s = %s )' % (A, at, K))
            ev, res = evaluate(w, A, body, {}, ifrules={'%s = %s' % (at, K): (False, ne3)})
        return w.s([f2, ev], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (A, MP, at, res)), res
    vF0, r0 = mpval('(/)'); vF1, r1 = mpval('1o')
    if idx == 0:
        assert (r0, r1) == ('U', '(/)'); vG0 = ppv0(w, A, ust, 'U', '(/)'); vG1 = ppv1(w, A, z2, 'U', '(/)')
    else:
        assert (r0, r1) == ('(/)', 'U'); vG0 = ppv0(w, A, z2, '(/)', 'U'); vG1 = ppv1(w, A, ust, '(/)', 'U')
    eq = eq_on_2o(w, A, MP, RES, fn, fnR, vF0, vG0, vF1, vG1, r0, r1)
    w.lines[-1] = 'qed' + w.lines[-1][len(eq):]
    run(w)
