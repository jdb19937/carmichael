"""Sortie A4c, batch 3: the dpGo loop (Lean: AlgExtract.dpGo_*)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

NONE = '( inr ` (/) )'
DPO = '( ( L e. NN /\\ P e. NN0 ) /\\ T e. Tbl )'
DG = lambda f, a: '( ( ( ( L DpGo P ) ` T ) ` %s ) ` %s )' % (f, a)
MOD = '( ( F x. P ) mod L )'
CSW = '( <" P "> ++ ( 2nd ` ( T ` F ) ) )'
ACC = lambda a: 'if ( ( T ` F ) = %s , %s , ( ( %s SetIfNone %s ) ` %s ) )' % (NONE, a, a, MOD, CSW)

# ------------------------------------------------------------------ dpgoacl
if not only or 'dpgoacl' in only:
    w = W('dpgoacl', 'The accumulator the dpGo body hands to the recursive call is a table.')
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) )' % DPO
    ll = w.s([w.s([], 'simpll', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([], 'simpll', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simprd', '( %s -> P e. NN0 )' % A)
    tt = w.s([], 'simplr', '( %s -> T e. Tbl )' % A)
    ff = w.s([], 'simprl', '( %s -> F e. NN0 )' % A)
    aa = w.s([], 'simprr', '( %s -> A e. Tbl )' % A)
    B = '( %s /\\ -. ( T ` F ) = %s )' % (A, NONE)
    ne = w.s([w.s([], 'simpr', '( %s -> -. ( T ` F ) = %s )' % (B, NONE)), w.inst('neqned')], 'syl',
             '( %s -> ( T ` F ) =/= %s )' % (B, NONE))
    pay = w.s([w.s([w.s([w.s([tt], 'adantr', '( %s -> T e. Tbl )' % B), w.s([ff], 'adantr', '( %s -> F e. NN0 )' % B)], 'jca',
                        '( %s -> ( T e. Tbl /\\ F e. NN0 ) )' % B), ne], 'jca',
                   '( %s -> ( ( T e. Tbl /\\ F e. NN0 ) /\\ ( T ` F ) =/= %s ) )' % (B, NONE)), w.inst('tblpay')], 'syl',
              '( %s -> ( ( 2nd ` ( T ` F ) ) e. Word NN0 /\\ ( T ` F ) = ( inl ` ( 2nd ` ( T ` F ) ) ) ) )' % B)
    s1c = w.s([w.s([pp], 'adantr', '( %s -> P e. NN0 )' % B), w.inst('s1cl')], 'syl',
               '( %s -> <" P "> e. Word NN0 )' % B)
    wcl = w.s([s1c, w.s([pay], 'simpld', '( %s -> ( 2nd ` ( T ` F ) ) e. Word NN0 )' % B)], 'jca',
              '( %s -> ( <" P "> e. Word NN0 /\\ ( 2nd ` ( T ` F ) ) e. Word NN0 ) )' % B)
    wcl2 = w.s([wcl, w.inst('ccatcl')], 'syl', None)
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> %s e. Word NN0 )' % (B, CSW)
    mz = w.s([w.s([w.s([w.s([ff], 'adantr', '( %s -> F e. NN0 )' % B)], 'nn0zd', '( %s -> F e. ZZ )' % B),
                   w.s([w.s([pp], 'adantr', '( %s -> P e. NN0 )' % B)], 'nn0zd', '( %s -> P e. ZZ )' % B)], 'zmulcld',
                  '( %s -> ( F x. P ) e. ZZ )' % B), w.s([ll], 'adantr', '( %s -> L e. NN )' % B), w.inst('zmodcl')], 'syl2anc',
              '( %s -> %s e. NN0 )' % (B, MOD))
    scl = w.s([w.s([w.s([w.s([aa], 'adantr', '( %s -> A e. Tbl )' % B), mz], 'jca',
                        '( %s -> ( A e. Tbl /\\ %s e. NN0 ) )' % (B, MOD)), wcl2], 'jca',
                   '( %s -> ( ( A e. Tbl /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (B, MOD, CSW)), w.inst('setifnonecl')], 'syl',
              '( %s -> ( ( A SetIfNone %s ) ` %s ) e. Tbl )' % (B, MOD, CSW))
    c2 = w.s([w.s([w.s([], 'simpr', '( %s -> -. ( T ` F ) = %s )' % (B, NONE))], 'iffalsed',
                  '( %s -> %s = ( ( A SetIfNone %s ) ` %s ) )' % (B, ACC('A'), MOD, CSW)), scl], 'eqeltrd',
             '( %s -> %s e. Tbl )' % (B, ACC('A')))
    C = '( %s /\\ ( T ` F ) = %s )' % (A, NONE)
    c1 = w.s([w.s([w.s([], 'simpr', '( %s -> ( T ` F ) = %s )' % (C, NONE))], 'iftrued',
                  '( %s -> %s = A )' % (C, ACC('A'))),
              w.s([aa], 'adantr', '( %s -> A e. Tbl )' % C)], 'eqeltrd', '( %s -> %s e. Tbl )' % (C, ACC('A')))
    w.qed([c1, c2], 'pm2.61dan', '( %s -> %s e. Tbl )' % (A, ACC('A')))
    run(w)

def inst1(w, ante, ih, var, dom, bodyv, repl, clstep, out=None):
    """instantiate ( ante -> A. var e. dom bodyv ) at var := repl"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, repl, var, repl))
    st, new = w.wcongr(bodyv, {var: repl}, '%s = %s' % (var, repl), {var: idst})
    assert new == subst(bodyv, var, repl), '\n%s\n%s' % (new, subst(bodyv, var, repl))
    return w.s([st, ih, clstep], 'rspcdva', '( %s -> %s )' % (ante, new)), new

def accl(w, ctx, a='a'):
    """( ctx.A -> ACC( a ) e. Tbl )"""
    return w.s([w.s([ctx.out, w.s([ctx.fuel, ctx.v[0]], 'jca', '( %s -> ( F e. NN0 /\\ %s e. Tbl ) )' % (ctx.A, a))], 'jca',
                    '( %s -> ( %s /\\ ( F e. NN0 /\\ %s e. Tbl ) ) )' % (ctx.A, DPO, a)), w.inst('dpgoacl')], 'syl',
               '( %s -> %s e. Tbl )' % (ctx.A, ACC(a)))

def dgp1(w, ctx, a='a'):
    """( ctx.A -> DG( F + 1 , a ) = <. ( 1st ` DG( F , X ) ) , ( ( 2nd ` DG( F , X ) ) + 1 ) >. )"""
    X = ACC(a)
    return w.s([w.s([ctx.out, ctx.fuel], 'jca', '( %s -> ( %s /\\ F e. NN0 ) )' % (ctx.A, DPO)), ctx.v[0],
                w.inst('dpgop1')], 'syl2anc',
               '( %s -> %s = <. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >. )' % (ctx.A, DG('( F + 1 )', a), DG('F', X), DG('F', X)))

def prj2(w, ante, expr, valstep, A, B):
    """( ante -> ( 2nd ` expr ) = B ) from valstep : ( ante -> expr = <. A , B >. ),
    with A and B classes proved to be sets by fvex/ovex"""
    aex = w.s([w.s([], 'fvex', '%s e. _V' % A)], 'a1i', '( %s -> %s e. _V )' % (ante, A))
    bex = w.s([w.s([], 'ovex', '%s e. _V' % B)], 'a1i', '( %s -> %s e. _V )' % (ante, B))
    e1 = w.s([valstep], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (ante, expr, A, B))
    e2 = w.s([aex, bex, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ante, A, B, B))
    return w.s([e1, e2], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (ante, expr, B))

def prj1(w, ante, expr, valstep, A, B):
    aex = w.s([w.s([], 'fvex', '%s e. _V' % A)], 'a1i', '( %s -> %s e. _V )' % (ante, A))
    bex = w.s([w.s([], 'ovex', '%s e. _V' % B)], 'a1i', '( %s -> %s e. _V )' % (ante, B))
    e1 = w.s([valstep], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ante, expr, A, B))
    e2 = w.s([aex, bex, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ante, A, B, A))
    return w.s([e1, e2], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ante, expr, A))

# ------------------------------------------------------------------ dpgocost
BODY = '( 2nd ` %s ) = f' % DG('f', 'a')
def _b(w, ctx, goal):
    v = w.s([], 'dpgo0', '( %s -> %s = <. a , 0 >. )' % (ctx.A, DG('0', 'a')))
    aex = w.s([ctx.v[0]], 'elexd', '( %s -> a e. _V )' % ctx.A)
    zex = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ctx.A)
    e1 = w.s([v], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. a , 0 >. ) )' % (ctx.A, DG('0', 'a')))
    e2 = w.s([aex, zex, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. a , 0 >. ) = 0 )' % ctx.A)
    return w.s([e1, e2], 'eqtrd', '( %s -> %s )' % (ctx.A, goal))

def _s(w, ctx, goal):
    X = ACC('a')
    val = dgp1(w, ctx)
    p2 = prj2(w, ctx.A, DG('( F + 1 )', 'a'), val, '( 1st ` %s )' % DG('F', X), '( ( 2nd ` %s ) + 1 )' % DG('F', X))
    xcl = accl(w, ctx)
    rv = ctx.rn[0]
    ihx, _ = inst1(w, ctx.A, ctx.ih, rv, 'Tbl', '( 2nd ` %s ) = F' % DG('F', rv), X, xcl)
    return w.s([p2, w.s([ihx], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( F + 1 ) )' % (ctx.A, DG('F', X)))], 'eqtrd',
               '( %s -> %s )' % (ctx.A, goal))

def _i(w):
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) )' % DPO
    ral = w.s([w.s([], 'simprl', '( %s -> F e. NN0 )' % A), w.inst('dpgocostl')], 'syl',
              '( %s -> %s )' % (A, qphi(DPO, [('a', 'Tbl')], subst(BODY, 'f', 'F'))))
    r2 = w.s([ral, w.s([], 'simpl', '( %s -> %s )' % (A, DPO))], 'mpd',
             '( %s -> A. a e. Tbl ( 2nd ` %s ) = F )' % (A, DG('F', 'a')))
    st, new = inst1(w, A, r2, 'a', 'Tbl', '( 2nd ` %s ) = F' % DG('F', 'a'), 'A',
                    w.s([], 'simprr', '( %s -> A e. Tbl )' % A))
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)

qfuel(run, 'dpgocost', DPO, [('a', 'Tbl')], BODY, _b, _s, instfn=_i, only=only,
      desc='The dpGo loop charges one unit per residue (Lean: dpGo_cost).')
