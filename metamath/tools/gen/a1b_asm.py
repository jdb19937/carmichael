#!/usr/bin/env python3
"""Sortie A1b: the assembly of Algorithm.lean (scalesOf, costPieces, search).
MM_DB=sorties/a1b.mm python3 tools/gen/a1b_asm.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import (W, Cl, defapply, conjsteps, promote_qed, applied_text, W0)

SC_ARGS = [('C', 'RR'), ('E', 'RR'), ('N', 'NN0')]
CP_ARGS = [('Z', 'NN0'), ('Y', 'NN0'), ('T', 'NN0'), ('L', 'NN0'),
           ('X', 'NN0'), ('K', 'NN0'), ('P', 'NN0'), ('S', 'NN0')]
NN0T = '( ( ( NN0 X. NN0 ) X. ( NN0 X. NN0 ) ) X. NN0 )'


def scalesofval():
    w = W('scalesofval', 'The value of ~ df-scalesof .  Lean: scalesOf.')
    parts = ['%s e. %s' % (v, t) for v, t in SC_ARGS]
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for v, t in SC_ARGS:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-scalesof', 'ScalesOf', ['C', 'E', 'N'])
    promote_qed(w, st)
    return w


def scalesofcl():
    args = [('C', 'RR'), ('E', 'RR'), ('N', '( ZZ>= ` 3 )')]
    w = W('scalesofcl', 'The scales of step 1 are five nonnegative integers.  '
                        'Membership in ~ df-scales itself, which ~ df-search needs, '
                        'asks in addition for ` 1 <_ z ` and ` 1 <_ y `, which A5 reads '
                        'off the window: ~ scalesofsc .')
    parts = ['%s e. %s' % (v, t) for v, t in args]
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for v, t in args:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    nn0 = w.s([w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ante), hs['N e. ( ZZ>= ` 3 )'],
               w.s([], 'eluznn0', '( ( 3 e. NN0 /\\ N e. ( ZZ>= ` 3 ) ) -> N e. NN0 )')],
              'syl2anc', '( %s -> N e. NN0 )' % ante)
    cl.have('N', 'NN0', nn0)
    st, val = defapply(w, cl, 'df-scalesof', 'ScalesOf', ['C', 'E', 'N'])
    # the five components
    zs = w.s([hs['C e. RR'], hs['N e. ( ZZ>= ` 3 )'],
              w.s([], 'zscalecl', '( ( C e. RR /\\ N e. ( ZZ>= ` 3 ) ) -> ( C zscale N ) e. NN0 )')],
             'syl2anc', '( %s -> ( C zscale N ) e. NN0 )' % ante)
    cl.have('( C zscale N )', 'NN0', zs)
    ys = w.s([hs['C e. RR'], hs['N e. ( ZZ>= ` 3 )'], hs['E e. RR'],
              w.s([], 'yscaleecl', '( ( C e. RR /\\ N e. ( ZZ>= ` 3 ) /\\ E e. RR ) -> '
                                   '( ( C yscaleE N ) ` E ) e. NN0 )')],
             'syl3anc', '( %s -> ( ( C yscaleE N ) ` E ) e. NN0 )' % ante)
    cl.have('( ( C yscaleE N ) ` E )', 'NN0', ys)
    ts = w.s([w.s([hs['N e. ( ZZ>= ` 3 )'], w.s([], 'uzuzle23', '( N e. ( ZZ>= ` 3 ) -> N e. ( ZZ>= ` 2 ) )')],
                  'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % ante),
              w.s([], 'tscalecl', '( N e. ( ZZ>= ` 2 ) -> ( Tscale ` N ) e. NN0 )')],
             'syl', '( %s -> ( Tscale ` N ) e. NN0 )' % ante)
    cl.have('( Tscale ` N )', 'NN0', ts)
    # ( log ` N ) e. RR, from 3 <_ N
    nre = w.s([nn0], 'nn0red', '( %s -> N e. RR )' % ante)
    n3 = w.s([hs['N e. ( ZZ>= ` 3 )'], w.s([], 'eluzle', '( N e. ( ZZ>= ` 3 ) -> 3 <_ N )')],
             'syl', '( %s -> 3 <_ N )' % ante)
    one = w.s([], '1red', '( %s -> 1 e. RR )' % ante)
    thr = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % ante)
    l13 = w.s([], '1lt3', '1 < 3')
    l13d = w.s([l13], 'a1i', '( %s -> 1 < 3 )' % ante)
    l1n = w.s([one, thr, nre, l13d, n3], 'ltletrd', '( %s -> 1 < N )' % ante)
    lg = w.s([nre, l1n, w.s([], 'rplogcl', '( ( N e. RR /\\ 1 < N ) -> ( log ` N ) e. RR+ )')],
             'syl2anc', '( %s -> ( log ` N ) e. RR+ )' % ante)
    lgr = w.s([lg], 'rpred', '( %s -> ( log ` N ) e. RR )' % ante)
    lg0 = w.s([lg], 'rpge0d', '( %s -> 0 <_ ( log ` N ) )' % ante)
    cl.have('( log ` N )', 'RR', lgr)
    cl.memo[('( log ` N )', 'ge0')] = lg0
    mm = cl.mem(val, NN0T)
    w.qed([st, mm], 'eqeltrd', '( %s -> ( ( C ScalesOf E ) ` N ) e. %s )' % (ante, NN0T))
    return w


def costpiecesval():
    w = W('costpiecesval', 'The value of ~ df-costpieces .  Lean: costPieces.')
    parts = ['%s e. %s' % (v, t) for v, t in CP_ARGS]
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for v, t in CP_ARGS:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-costpieces', 'CostPieces', [v for v, _ in CP_ARGS])
    promote_qed(w, st)
    return w


def costpiecescl():
    w = W('costpiecescl', 'The operation budget is a nonnegative integer.')
    parts = ['%s e. %s' % (v, t) for v, t in CP_ARGS]
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for v, t in CP_ARGS:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-costpieces', 'CostPieces', [v for v, _ in CP_ARGS])
    mm = cl.mem(val, 'NN0')
    w.qed([st, mm], 'eqeltrd', '( %s -> %s e. NN0 )'
          % (ante, applied_text('CostPieces', [v for v, _ in CP_ARGS])))
    return w


BUILD = {'scalesofval': scalesofval, 'scalesofcl': scalesofcl,
         'costpiecesval': costpiecesval, 'costpiecescl': costpiecescl}
ORDER = ['scalesofval', 'scalesofcl', 'costpiecesval', 'costpiecescl']



SC = '<. <. <. Z , W >. , <. Y , T >. >. , H >.'
TYPES = [('Z', 'NN'), ('W', 'NN0'), ('Y', 'NN'), ('T', 'NN0'), ('H', 'NN0'), ('N', 'NN0')]
LETS = [('R', '( ( Z Reservoir W ) ` Y )'),
        ('I', '( # ` ( 1st ` R ) )'),
        ('Q', '( ( 1st ` R ) substr <. ( I - T ) , I >. )'),
        ('G', '( ProdL ` Q )'),
        ('A', '( 1st ` G )'),
        ('C', '( ( ( ( 2nd ` R ) + T ) + ( 2nd ` G ) ) + 2 )'),
        ('J', '( ( ( ( ( Q Scan ( A ^ 5 ) ) ` Z ) ` H ) ` 1 ) ` ( A ^ 5 ) )'),
        ('P', '( 2nd ` ( 2nd ` ( 1st ` J ) ) )'),
        ('X', '( ( A Extract N ) ` P )'),
        ('U', '( ( 1st ` ( 2nd ` ( 1st ` X ) ) ) Verify ( 2nd ` ( 2nd ` ( 1st ` X ) ) ) )')]


def _findlet(expr):
    """the innermost ( ( v e. _V |-> BODY ) ` ARG ) subterm, or None"""
    found = []

    def visit(n):
        if found:
            return
        if n.kind == 'fv' and n.kids[0].kind == 'mpt' and n.kids[0].kids[0].text() == '_V':
            found.append(n)
            return
        for k in n.kids:
            visit(k)
    visit(L._c.parse(expr))
    return found[0] if found else None


def searchval():
    w = W('searchval', 'The value of ~ df-search , with the ten intermediates of Lean\'s '
                       'let bindings as class variables fixed by the antecedent: ` R ` is '
                       'res, ` I ` is len, ` Q ` is Q, ` G ` is Lp, ` A ` is L, ` C ` is '
                       'c2, ` J ` is s3, ` P ` is the pool list of the some (_, P) '
                       'pattern, ` X ` is ex and ` U ` is v.  This is the shape '
                       'AlgBudget.search_success consumes.')
    parts = ['%s e. %s' % (v, t) for v, t in TYPES] + ['%s = %s' % (v, r) for v, r in LETS]
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for v, t in TYPES:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    argmap = {}
    for v, r in LETS:
        eq = hs['%s = %s' % (v, r)]
        rv = w.s([eq], 'eqcomd', '( %s -> %s = %s )' % (ante, r, v))
        ex = cl.mem(r, '_V')
        cl.have(v, '_V', w.s([eq, ex], 'eqeltrd', '( %s -> %s e. _V )' % (ante, v)))
        argmap[r] = (v, rv)
    st, val = defapply(w, cl, 'df-search', 'Search', [SC, 'N'])
    call = '( %s Search N )' % SC
    rs, val2 = L.reduceops(w, cl, val)
    if rs is not None:
        st = w.s([st, rs], 'eqtrd', '( %s -> %s = %s )' % (ante, call, val2))
        val = val2
    while True:
        node = _findlet(val)
        if node is None:
            break
        term = node.text()
        mpt = node.kids[0].text()
        arg = node.kids[1].text()
        assert arg in argmap, arg
        cv, rv = argmap[arg]
        e1 = w.s([rv], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ante, mpt, arg, mpt, cv))
        e2, bv = L.mptfv(w, cl, mpt, cv)
        stq = w.s([e1, e2], 'eqtrd', '( %s -> %s = %s )' % (ante, term, bv))
        st, val = L._rwchain(w, ante, call, st, val, {term: (bv, stq)})
    promote_qed(w, st)
    return w


BUILD['searchval'] = searchval
ORDER.append('searchval')


def scalesofsc():
    args = [('C', 'RR'), ('E', 'RR'), ('N', '( ZZ>= ` 3 )')]
    w = W('scalesofsc', 'The scales of step 1 are a member of ~ df-scales once the '
                        'reservoir bound ` z ` and the smoothness bound ` y ` are at '
                        'least ` 1 `, which is what ~ df-search asks of its first '
                        'argument.  A5 reads the two inequalities off the window.')
    parts = ['%s e. %s' % (v, t) for v, t in args]
    parts += ['1 <_ ( C zscale N )', '1 <_ ( ( C yscaleE N ) ` E )']
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for v, t in args:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    zs = w.s([hs['C e. RR'], hs['N e. ( ZZ>= ` 3 )'],
              w.s([], 'zscalecl', '( ( C e. RR /\\ N e. ( ZZ>= ` 3 ) ) -> ( C zscale N ) e. NN0 )')],
             'syl2anc', '( %s -> ( C zscale N ) e. NN0 )' % ante)
    ys = w.s([hs['C e. RR'], hs['N e. ( ZZ>= ` 3 )'], hs['E e. RR'],
              w.s([], 'yscaleecl', '( ( C e. RR /\\ N e. ( ZZ>= ` 3 ) /\\ E e. RR ) -> '
                                   '( ( C yscaleE N ) ` E ) e. NN0 )')],
             'syl3anc', '( %s -> ( ( C yscaleE N ) ` E ) e. NN0 )' % ante)
    znn = w.s([w.s([zs, hs['1 <_ ( C zscale N )']], 'jca',
                   '( %s -> ( ( C zscale N ) e. NN0 /\\ 1 <_ ( C zscale N ) ) )' % ante),
               w.s([], 'elnnnn0c', '( ( C zscale N ) e. NN <-> ( ( C zscale N ) e. NN0 /\\ 1 <_ ( C zscale N ) ) )')],
              'sylibr', '( %s -> ( C zscale N ) e. NN )' % ante)
    ynn = w.s([w.s([ys, hs['1 <_ ( ( C yscaleE N ) ` E )']], 'jca',
                   '( %s -> ( ( ( C yscaleE N ) ` E ) e. NN0 /\\ 1 <_ ( ( C yscaleE N ) ` E ) ) )' % ante),
               w.s([], 'elnnnn0c', '( ( ( C yscaleE N ) ` E ) e. NN <-> ( ( ( C yscaleE N ) ` E ) e. NN0 /\\ '
                                   '1 <_ ( ( C yscaleE N ) ` E ) ) )')],
              'sylibr', '( %s -> ( ( C yscaleE N ) ` E ) e. NN )' % ante)
    cl.have('( C zscale N )', 'NN', znn)
    cl.have('( ( C yscaleE N ) ` E )', 'NN', ynn)
    nn0 = w.s([w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ante),
               hs['N e. ( ZZ>= ` 3 )'],
               w.s([], 'eluznn0', '( ( 3 e. NN0 /\\ N e. ( ZZ>= ` 3 ) ) -> N e. NN0 )')],
              'syl2anc', '( %s -> N e. NN0 )' % ante)
    cl.have('N', 'NN0', nn0)
    ts = w.s([w.s([hs['N e. ( ZZ>= ` 3 )'], w.s([], 'uzuzle23', '( N e. ( ZZ>= ` 3 ) -> N e. ( ZZ>= ` 2 ) )')],
                  'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % ante),
              w.s([], 'tscalecl', '( N e. ( ZZ>= ` 2 ) -> ( Tscale ` N ) e. NN0 )')],
             'syl', '( %s -> ( Tscale ` N ) e. NN0 )' % ante)
    cl.have('( Tscale ` N )', 'NN0', ts)
    nre = w.s([nn0], 'nn0red', '( %s -> N e. RR )' % ante)
    n3 = w.s([hs['N e. ( ZZ>= ` 3 )'], w.s([], 'eluzle', '( N e. ( ZZ>= ` 3 ) -> 3 <_ N )')],
             'syl', '( %s -> 3 <_ N )' % ante)
    one = w.s([], '1red', '( %s -> 1 e. RR )' % ante)
    thr = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % ante)
    l13d = w.s([w.s([], '1lt3', '1 < 3')], 'a1i', '( %s -> 1 < 3 )' % ante)
    l1n = w.s([one, thr, nre, l13d, n3], 'ltletrd', '( %s -> 1 < N )' % ante)
    lg = w.s([nre, l1n, w.s([], 'rplogcl', '( ( N e. RR /\\ 1 < N ) -> ( log ` N ) e. RR+ )')],
             'syl2anc', '( %s -> ( log ` N ) e. RR+ )' % ante)
    cl.have('( log ` N )', 'RR', w.s([lg], 'rpred', '( %s -> ( log ` N ) e. RR )' % ante))
    cl.memo[('( log ` N )', 'ge0')] = w.s([lg], 'rpge0d', '( %s -> 0 <_ ( log ` N ) )' % ante)
    st, val = defapply(w, cl, 'df-scalesof', 'ScalesOf', ['C', 'E', 'N'])
    mm = cl.mem(val, 'Scales')
    w.qed([st, mm], 'eqeltrd', '( %s -> ( ( C ScalesOf E ) ` N ) e. Scales )' % ante)
    return w


BUILD['scalesofsc'] = scalesofsc
ORDER.insert(2, 'scalesofsc')


if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
