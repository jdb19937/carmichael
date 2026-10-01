"""Sortie A4c, batch 3e: the case analysis of a dpGo result (Lean: dpGo_cases)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

XA = ACC('a')
QU = [('a', 'Tbl'), ('c', 'NN0')]
EN = lambda f, a: '( ( 1st ` %s ) ` c )' % DG(f, a)
def RB(v, tgt):
    return '( ( ( T ` %s ) =/= %s /\\ c = ( ( %s x. P ) mod L ) ) /\\ ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` %s ) ) ) )' % (v, NONE, v, tgt, v)
def DISJ(f, a):
    return '( ( a ` c ) = %s \\/ E. r e. ( 0 ..^ %s ) %s )' % (EN(f, a), f, RB('r', EN(f, a)))
BODY = '( %s =/= %s -> %s )' % (EN('f', 'a'), NONE, DISJ('f', 'a'))

def _inner(w, bF):
    """rename the inner bound r of the induction hypothesis to x"""
    Y = EN('F', 'a')
    idst = w.s([], 'id', '( r = x -> r = x )')
    st, new = w.wcongr(RB('r', Y), {'r': 'x'}, 'r = x', {'r': idst})
    assert new == RB('x', Y), '\n%s\n%s' % (new, RB('x', Y))
    cb = w.s([st], 'cbvrexv', '( E. r e. ( 0 ..^ F ) %s <-> E. x e. ( 0 ..^ F ) %s )' % (RB('r', Y), RB('x', Y)))
    D0 = '( ( a ` c ) = %s \\/ E. r e. ( 0 ..^ F ) %s )' % (Y, RB('r', Y))
    D1 = '( ( a ` c ) = %s \\/ E. x e. ( 0 ..^ F ) %s )' % (Y, RB('x', Y))
    o = w.s([cb], 'orbi2i', '( %s <-> %s )' % (D0, D1))
    B0 = '( %s =/= %s -> %s )' % (Y, NONE, D0)
    B1 = '( %s =/= %s -> %s )' % (Y, NONE, D1)
    return w.s([o], 'imbi2i', '( %s <-> %s )' % (B0, B1)), B1

def _b(w, ctx, goal):
    A = ctx.A
    inner = '( %s /\\ a e. Tbl )' % DPO
    z = w.s([], 'simpl', '( %s -> %s )' % (A, inner))
    v = w.s([z, w.inst('dpgo0')], 'syl', '( %s -> %s = <. a , 0 >. )' % (A, DG('0', 'a')))
    aex = w.s([ctx.v[0]], 'elexd', '( %s -> a e. _V )' % A)
    zex = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    p1 = prj(w, A, DG('0', 'a'), v, 'a', '0', 1, aex=aex, bex=zex)
    e = w.s([w.s([p1], 'fveq1d', '( %s -> ( ( 1st ` %s ) ` c ) = ( a ` c ) )' % (A, DG('0', 'a')))], 'eqcomd',
            '( %s -> ( a ` c ) = %s )' % (A, EN('0', 'a')))
    return w.s([w.s([e], 'orcd', '( %s -> %s )' % (A, DISJ('0', 'a')))], 'a1d', '( %s -> %s )' % (A, goal))

def _s(w, ctx, goal):
    A = ctx.A
    Y = EN('F', XA)
    Z = EN('( F + 1 )', 'a')
    GOAL = DISJ('( F + 1 )', 'a')
    U = '( %s /\\ %s =/= %s )' % (A, Z, NONE)
    lf = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    out = lf(ctx.out, DPO); fst = lf(ctx.fuel, 'F e. NN0'); ast = lf(ctx.v[0], 'a e. Tbl'); cst = lf(ctx.v[1], 'c e. NN0')
    ih = lf(ctx.ih, ctx.ihf)
    hyp = w.s([], 'simpr', '( %s -> %s =/= %s )' % (U, Z, NONE))
    xcl = w.s([w.s([out, w.s([fst, ast], 'jca', '( %s -> ( F e. NN0 /\\ a e. Tbl ) )' % U)], 'jca',
                   '( %s -> ( %s /\\ ( F e. NN0 /\\ a e. Tbl ) ) )' % (U, DPO)), w.inst('dpgoacl')], 'syl',
              '( %s -> %s e. Tbl )' % (U, XA))
    val = dp_p1(w, ctx)
    p1 = prj(w, A, DG('( F + 1 )', 'a'), val, '( 1st ` %s )' % DG('F', XA), '( ( 2nd ` %s ) + 1 )' % DG('F', XA), 1)
    zy = w.s([w.s([p1], 'adantr', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (U, DG('( F + 1 )', 'a'), DG('F', XA)))],
             'fveq1d', '( %s -> %s = %s )' % (U, Z, Y))
    ynn = w.s([w.s([zy], 'eqcomd', '( %s -> %s = %s )' % (U, Y, Z)), hyp], 'eqnetrd', '( %s -> %s =/= %s )' % (U, Y, NONE))
    # the induction hypothesis at ( XA , c ), its inner bound variable being x
    r = ctx.rn
    ihb = subst(subst('( %s =/= %s -> ( ( a ` c ) = %s \\/ E. x e. ( 0 ..^ F ) %s ) )'
                      % (EN('F', 'a'), NONE, EN('F', 'a'), RB('x', EN('F', 'a'))), 'a', r[0]), 'c', r[1])
    ihx, bd = instn(w, U, ih, [(r[0], 'Tbl'), (r[1], 'NN0')], ihb, [XA, 'c'], [xcl, cst])
    D1 = '( ( %s ` c ) = %s \\/ E. x e. ( 0 ..^ F ) %s )' % (XA, Y, RB('x', Y))
    D2 = '( ( %s ` c ) = %s \\/ E. r e. ( 0 ..^ F ) %s )' % (XA, Y, RB('r', Y))
    dd = w.s([ihx, ynn], 'mpd', '( %s -> %s )' % (U, D1))
    idst2 = w.s([], 'id', '( x = r -> x = r )')
    sb2, new2 = w.wcongr(RB('x', Y), {'x': 'r'}, 'x = r', {'x': idst2})
    assert new2 == RB('r', Y), '\n%s\n%s' % (new2, RB('r', Y))
    cbv = w.s([sb2], 'cbvrexv', '( E. x e. ( 0 ..^ F ) %s <-> E. r e. ( 0 ..^ F ) %s )' % (RB('x', Y), RB('r', Y)))
    dd2 = w.s([dd, w.s([w.s([cbv], 'orbi2i', '( %s <-> %s )' % (D1, D2))], 'a1i', '( %s -> ( %s <-> %s ) )' % (U, D1, D2))],
              'mpbid', '( %s -> %s )' % (U, D2))
    # ---------------------------------------------------------- left disjunct
    L = '( %s /\\ ( %s ` c ) = %s )' % (U, XA, Y)
    lfl = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L, f))
    xe = w.s([], 'simpr', '( %s -> ( %s ` c ) = %s )' % (L, XA, Y))
    xnn = w.s([xe, lfl(ynn, '%s =/= %s' % (Y, NONE))], 'eqnetrd', '( %s -> ( %s ` c ) =/= %s )' % (L, XA, NONE))
    cas = dp_lem(w, L, 'dpgoacc', lfl(out, DPO), lfl(fst, 'F e. NN0'), lfl(ast, 'a e. Tbl'), 'a',
                 w.s([lfl(cst, 'c e. NN0'), xnn], 'jca', '( %s -> ( c e. NN0 /\\ ( %s ` c ) =/= %s ) )' % (L, XA, NONE)),
                 '( c e. NN0 /\\ ( %s ` c ) =/= %s )' % (XA, NONE),
                 '( ( a ` c ) = ( %s ` c ) \\/ ( ( ( T ` F ) =/= %s /\\ c = %s ) /\\ ( 2nd ` ( %s ` c ) ) = %s ) )'
                 % (XA, NONE, MOD, XA, CSW))
    zyL = lfl(zy, '%s = %s' % (Z, Y))
    #   the old entry
    LL = '( %s /\\ ( a ` c ) = ( %s ` c ) )' % (L, XA)
    ll = w.s([w.s([w.s([], 'simpr', '( %s -> ( a ` c ) = ( %s ` c ) )' % (LL, XA)),
                   w.s([xe], 'adantr', '( %s -> ( %s ` c ) = %s )' % (LL, XA, Y))], 'eqtrd',
                  '( %s -> ( a ` c ) = %s )' % (LL, Y)),
              w.s([zyL], 'adantr', '( %s -> %s = %s )' % (LL, Z, Y))], 'eqtr4d', '( %s -> ( a ` c ) = %s )' % (LL, Z))
    llo = w.s([ll], 'orcd', '( %s -> %s )' % (LL, GOAL))
    #   the new entry, witnessed by r := F
    RH = '( ( ( T ` F ) =/= %s /\\ c = %s ) /\\ ( 2nd ` ( %s ` c ) ) = %s )' % (NONE, MOD, XA, CSW)
    LR = '( %s /\\ %s )' % (L, RH)
    fLR = w.s([lfl(fst, 'F e. NN0')], 'adantr', '( %s -> F e. NN0 )' % LR)
    f1n = w.s([fLR, w.inst('nn0p1nn')], 'syl', '( %s -> ( F + 1 ) e. NN )' % LR)
    flt = w.s([w.s([fLR], 'nn0red', '( %s -> F e. RR )' % LR)], 'ltp1d', '( %s -> F < ( F + 1 ) )' % LR)
    fzo = w.s([w.s([fLR, f1n, flt], '3jca', '( %s -> ( F e. NN0 /\\ ( F + 1 ) e. NN /\\ F < ( F + 1 ) ) )' % LR),
               w.s([w.s([], 'elfzo0', '( F e. ( 0 ..^ ( F + 1 ) ) <-> ( F e. NN0 /\\ ( F + 1 ) e. NN /\\ F < ( F + 1 ) ) )')],
                   'a1i', '( %s -> ( F e. ( 0 ..^ ( F + 1 ) ) <-> ( F e. NN0 /\\ ( F + 1 ) e. NN /\\ F < ( F + 1 ) ) ) )' % LR)],
              'mpbird', '( %s -> F e. ( 0 ..^ ( F + 1 ) ) )' % LR)
    zx = w.s([w.s([zyL], 'adantr', '( %s -> %s = %s )' % (LR, Z, Y)),
              w.s([w.s([xe], 'adantr', '( %s -> ( %s ` c ) = %s )' % (LR, XA, Y))], 'eqcomd',
                  '( %s -> %s = ( %s ` c ) )' % (LR, Y, XA))], 'eqtrd', '( %s -> %s = ( %s ` c ) )' % (LR, Z, XA))
    rh = w.s([], 'simpr', '( %s -> %s )' % (LR, RH))
    hbody = w.s([w.s([rh], 'simpld', '( %s -> ( ( T ` F ) =/= %s /\\ c = %s ) )' % (LR, NONE, MOD)),
                 w.s([w.s([zx], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` ( %s ` c ) ) )' % (LR, Z, XA)),
                      w.s([rh], 'simprd', '( %s -> ( 2nd ` ( %s ` c ) ) = %s )' % (LR, XA, CSW))], 'eqtrd',
                     '( %s -> ( 2nd ` %s ) = %s )' % (LR, Z, CSW))], 'jca', '( %s -> %s )' % (LR, RB('F', Z)))
    idst = w.s([], 'id', '( r = F -> r = F )')
    sb, new = w.wcongr(RB('r', Z), {'r': 'F'}, 'r = F', {'r': idst})
    assert new == RB('F', Z), '\n%s\n%s' % (new, RB('F', Z))
    rspc = w.s([sb], 'rspcev', '( ( F e. ( 0 ..^ ( F + 1 ) ) /\\ %s ) -> E. r e. ( 0 ..^ ( F + 1 ) ) %s )' % (RB('F', Z), RB('r', Z)))
    rex = w.s([w.s([fzo, hbody], 'jca', '( %s -> ( F e. ( 0 ..^ ( F + 1 ) ) /\\ %s ) )' % (LR, RB('F', Z))), rspc], 'syl',
              '( %s -> E. r e. ( 0 ..^ ( F + 1 ) ) %s )' % (LR, RB('r', Z)))
    lro = w.s([rex], 'olcd', '( %s -> %s )' % (LR, GOAL))
    lall = w.s([cas, w.s([llo], 'ex', '( %s -> ( ( a ` c ) = ( %s ` c ) -> %s ) )' % (L, XA, GOAL)),
                w.s([lro], 'ex', '( %s -> ( %s -> %s ) )' % (L, RH, GOAL))], 'mpjaod', '( %s -> %s )' % (L, GOAL))
    imp1 = w.s([lall], 'ex', '( %s -> ( ( %s ` c ) = %s -> %s ) )' % (U, XA, Y, GOAL))
    # ---------------------------------------------------------- right disjunct
    bi = w.s([w.s([w.s([zy], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (U, Z, Y))], 'eqcomd',
                  '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (U, Y, Z))], 'eqeq1d',
             '( %s -> ( ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) <-> ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) ) )'
             % (U, Y, Z))
    bi2 = w.s([bi], 'anbi2d', '( %s -> ( %s <-> %s ) )' % (U, RB('r', Y), RB('r', Z)))
    rim = w.s([w.s([bi2], 'biimpd', '( %s -> ( %s -> %s ) )' % (U, RB('r', Y), RB('r', Z)))], 'reximdv',
              '( %s -> ( E. r e. ( 0 ..^ F ) %s -> E. r e. ( 0 ..^ F ) %s ) )' % (U, RB('r', Y), RB('r', Z)))
    fz = w.s([w.s([fst], 'nn0zd', '( %s -> F e. ZZ )' % U), w.inst('uzid')], 'syl', '( %s -> F e. ( ZZ>= ` F ) )' % U)
    fz2 = w.s([fz, w.inst('peano2uz')], 'syl', '( %s -> ( F + 1 ) e. ( ZZ>= ` F ) )' % U)
    ss = w.s([fz2, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ F ) C_ ( 0 ..^ ( F + 1 ) ) )' % U)
    wid = w.s([ss, w.inst('ssrexv')], 'syl',
              '( %s -> ( E. r e. ( 0 ..^ F ) %s -> E. r e. ( 0 ..^ ( F + 1 ) ) %s ) )' % (U, RB('r', Z), RB('r', Z)))
    ch = w.s([rim, wid], 'syld', '( %s -> ( E. r e. ( 0 ..^ F ) %s -> E. r e. ( 0 ..^ ( F + 1 ) ) %s ) )' % (U, RB('r', Y), RB('r', Z)))
    imp2 = w.s([ch, w.s([], 'olc', '( E. r e. ( 0 ..^ ( F + 1 ) ) %s -> %s )' % (RB('r', Z), GOAL))], 'syl6',
               '( %s -> ( E. r e. ( 0 ..^ F ) %s -> %s ) )' % (U, RB('r', Y), GOAL))
    fin = w.s([dd2, imp1, imp2], 'mpjaod', '( %s -> %s )' % (U, GOAL))
    return w.s([fin], 'ex', '( %s -> %s )' % (A, goal))


def _i(w):
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( C e. NN0 /\\ ( ( 1st ` %s ) ` C ) =/= %s ) )' % (DPO, DG('F', 'A'), NONE)
    dpo = w.s([], 'simp1', '( %s -> %s )' % (A, DPO))
    ff = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)], 'simpld', '( %s -> F e. NN0 )' % A)
    aa = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)], 'simprd', '( %s -> A e. Tbl )' % A)
    cc = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( ( 1st ` %s ) ` C ) =/= %s ) )' % (A, DG('F', 'A'), NONE))], 'simpld',
             '( %s -> C e. NN0 )' % A)
    nn = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( ( 1st ` %s ) ` C ) =/= %s ) )' % (A, DG('F', 'A'), NONE))], 'simprd',
             '( %s -> ( ( 1st ` %s ) ` C ) =/= %s )' % (A, DG('F', 'A'), NONE))
    PH = qphi(DPO, QU, subst(BODY, 'f', 'F'))
    ral = w.s([w.s([ff, w.inst('dpgocasesl')], 'syl', '( %s -> %s )' % (A, PH)), dpo], 'mpd',
              '( %s -> %s )' % (A, quantify(QU, ['a', 'c'], subst(BODY, 'f', 'F'))))
    st, bd = instn(w, A, ral, QU, subst(BODY, 'f', 'F'), ['A', 'C'], [aa, cc])
    fin = w.s([st, nn], 'mpd', '( %s -> %s )' % (A, subst(subst(DISJ('F', 'a'), 'a', 'A'), 'c', 'C')))
    w.lines[-1] = w.lines[-1].replace('%s:' % fin, 'qed:', 1)

qfuel(run, 'dpgocases', DPO, QU, BODY, _b, _s, instfn=_i, only=only, innerfn=_inner,
      desc='Every nonempty entry of a dpGo result is old or a propagated one (Lean: dpGo_cases).')
