"""Sortie A4c, batch 3c: dpGo persistence, nonemptiness and the hit."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

QU = [('a', 'Tbl'), ('c', 'NN0')]
X = ACC('a')

def lift(w, st, frm, to, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (to, f))

# ================================================================= dpgopers
BODY = '( ( a ` c ) =/= %s -> ( ( 1st ` %s ) ` c ) = ( a ` c ) )' % (NONE, DG('f', 'a'))

def _b(w, ctx, goal):
    A = ctx.A
    inner = '( %s /\\ a e. Tbl )' % DPO
    z = w.s([], 'simpl', '( %s -> %s )' % (A, inner))
    v = w.s([z, w.inst('dpgo0')], 'syl', '( %s -> %s = <. a , 0 >. )' % (A, DG('0', 'a')))
    aex = w.s([ctx.v[0]], 'elexd', '( %s -> a e. _V )' % A)
    zex = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    p1 = prj(w, A, DG('0', 'a'), v, 'a', '0', 1, aex=aex, bex=zex)
    e = w.s([p1], 'fveq1d', '( %s -> ( ( 1st ` %s ) ` c ) = ( a ` c ) )' % (A, DG('0', 'a')))
    return w.s([e], 'a1d', '( %s -> %s )' % (A, goal))

def _s(w, ctx, goal):
    A = ctx.A
    U = '( %s /\\ ( a ` c ) =/= %s )' % (A, NONE)
    out = lift(w, ctx.out, A, U, DPO)
    fst = lift(w, ctx.fuel, A, U, 'F e. NN0')
    ast = lift(w, ctx.v[0], A, U, 'a e. Tbl')
    cst = lift(w, ctx.v[1], A, U, 'c e. NN0')
    ih = lift(w, ctx.ih, A, U, _ihf(ctx))
    hyp = w.s([], 'simpr', '( %s -> ( a ` c ) =/= %s )' % (U, NONE))
    ex2 = w.s([cst, hyp], 'jca', '( %s -> ( c e. NN0 /\\ ( a ` c ) =/= %s ) )' % (U, NONE))
    xcl = w.s([w.s([out, w.s([fst, ast], 'jca', '( %s -> ( F e. NN0 /\\ a e. Tbl ) )' % U)], 'jca',
                   '( %s -> ( %s /\\ ( F e. NN0 /\\ a e. Tbl ) ) )' % (U, DPO)), w.inst('dpgoacl')], 'syl',
              '( %s -> %s e. Tbl )' % (U, X))
    xeq = dp_lem(w, U, 'dpgoace', out, fst, ast, 'a', ex2,
                 '( c e. NN0 /\\ ( a ` c ) =/= %s )' % NONE, '( %s ` c ) = ( a ` c )' % X)
    xnn = w.s([xeq, hyp], 'eqnetrd', '( %s -> ( %s ` c ) =/= %s )' % (U, X, NONE))
    r = ctx.rn
    ihb = subst(subst(BODY, 'f', 'F'), 'a', r[0])
    ihb = subst(ihb, 'c', r[1])
    ihx, _ = instn(w, U, ih, [(r[0], 'Tbl'), (r[1], 'NN0')], ihb, [X, 'c'], [xcl, cst])
    got = w.s([ihx, xnn], 'mpd', '( %s -> ( ( 1st ` %s ) ` c ) = ( %s ` c ) )' % (U, DG('F', X), X))
    val = dp_p1(w, ctx)
    p1 = prj(w, A, DG('( F + 1 )', 'a'), val, '( 1st ` %s )' % DG('F', X), '( ( 2nd ` %s ) + 1 )' % DG('F', X), 1)
    e = w.s([w.s([w.s([p1], 'adantr', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (U, DG('( F + 1 )', 'a'), DG('F', X)))], 'fveq1d',
                 '( %s -> ( ( 1st ` %s ) ` c ) = ( ( 1st ` %s ) ` c ) )' % (U, DG('( F + 1 )', 'a'), DG('F', X))),
             w.s([got, xeq], 'eqtrd', '( %s -> ( ( 1st ` %s ) ` c ) = ( a ` c ) )' % (U, DG('F', X)))], 'eqtrd',
             '( %s -> ( ( 1st ` %s ) ` c ) = ( a ` c ) )' % (U, DG('( F + 1 )', 'a')))
    return w.s([e], 'ex', '( %s -> %s )' % (A, goal))

def _ihf(ctx):
    return ctx.ihf

def _i(w):
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (DPO, NONE)
    dpo = w.s([], 'simp1', '( %s -> %s )' % (A, DPO))
    ff = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)], 'simpld', '( %s -> F e. NN0 )' % A)
    aa = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)], 'simprd', '( %s -> A e. Tbl )' % A)
    cc = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (A, NONE))], 'simpld', '( %s -> C e. NN0 )' % A)
    nn = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (A, NONE))], 'simprd',
             '( %s -> ( A ` C ) =/= %s )' % (A, NONE))
    PH = qphi(DPO, QU, subst(BODY, 'f', 'F'))
    ral = w.s([w.s([ff, w.inst('dpgopersl')], 'syl', '( %s -> %s )' % (A, PH)), dpo], 'mpd',
              '( %s -> %s )' % (A, quantify(QU, ['a', 'c'], subst(BODY, 'f', 'F'))))
    st, bd = instn(w, A, ral, QU, subst(BODY, 'f', 'F'), ['A', 'C'], [aa, cc])
    fin = w.s([st, nn], 'mpd', '( %s -> ( ( 1st ` %s ) ` C ) = ( A ` C ) )' % (A, DG('F', 'A')))
    w.lines[-1] = w.lines[-1].replace('%s:' % fin, 'qed:', 1)

qfuel(run, 'dpgopers', DPO, QU, BODY, _b, _s, instfn=_i, only=only,
      desc='Entries of the dpGo accumulator persist (Lean: dpGo_persist).')
