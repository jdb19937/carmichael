"""Helpers for sortie A4a: the two induction principles of the algorithm's
loops (induction on a word by prepending, induction on a fuel) as worksheet
builders on top of tools/tm.py's W, plus the small expression shorthands."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__))
import a1lib
from tm import *

W0 = 'Word NN0'
NONE = '( inr ` (/) )'

def SQ(a): return '( Nfloor ` ( sqrt ` %s ) )' % a
def LG(a): return '( 2 Nlog %s )' % a
def F1(x): return '( 1st ` %s )' % x
def F2(x): return '( 2nd ` %s )' % x
def PRD(x, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, x, x, i)
def CS(p, v): return '( <" %s "> ++ %s )' % (p, v)


def subst(text, var, repl):
    """token substitution of a single set/class variable"""
    return ' '.join(repl if t == var else t for t in text.split())


def wrdind(w, phi, target, baselab, steplab, svar='s', alpha='NN0', a='a', b='b', prods=()):
    """( target e. Word alpha -> phi[target/svar] ), by algwrdi.

    baselab proves  |- phi[(/)/svar]
    steplab proves  |- ( ( V e. Word alpha /\\ P e. alpha /\\ phi[V/svar] ) -> phi[( <" P "> ++ V )/svar] )
    Returns (step name, phi[target/svar])."""
    RAB = '{ %s e. Word %s | %s }' % (svar, alpha, phi)
    def cong(repl):
        ANTE = '%s = %s' % (svar, repl)
        idst = w.s([], 'id', '( %s -> %s )' % (ANTE, ANTE))
        rules = prodrules(w, phi, svar, repl, ANTE, idst, prods)
        st, new = w.wcongr(phi, {svar: repl}, ANTE, {svar: idst}, rules=rules or None)
        assert new == subst(phi, svar, repl), 'congruence text mismatch:\n%s\n%s' % (new, subst(phi, svar, repl))
        return st, new
    # base
    cg0, phi0 = cong('(/)')
    er0 = w.s([cg0], 'elrab', '( (/) e. %s <-> ( (/) e. Word %s /\\ %s ) )' % (RAB, alpha, phi0))
    w0 = w.s([], 'wrd0', '(/) e. Word %s' % alpha)
    b0 = w.s([], baselab, phi0)
    e0 = w.s([er0, w.s([w0, b0], 'pm3.2i', '( (/) e. Word %s /\\ %s )' % (alpha, phi0))], 'mpbir', '(/) e. %s' % RAB)
    # step
    CSA = '( <" %s "> ++ %s )' % (b, a)
    cga, phia = cong(a)
    cgb, phib = cong(CSA)
    era = w.s([cga], 'elrab', '( %s e. %s <-> ( %s e. Word %s /\\ %s ) )' % (a, RAB, a, alpha, phia))
    erb = w.s([cgb], 'elrab', '( %s e. %s <-> ( %s e. Word %s /\\ %s ) )' % (CSA, RAB, CSA, alpha, phib))
    ANT = '( %s e. Word %s /\\ %s e. %s )' % (a, alpha, b, alpha)
    U = '( %s /\\ %s e. %s )' % (ANT, a, RAB)
    aw = w.s([], 'simpll', '( %s -> %s e. Word %s )' % (U, a, alpha))
    bn = w.s([], 'simplr', '( %s -> %s e. %s )' % (U, b, alpha))
    arab = w.s([], 'simpr', '( %s -> %s e. %s )' % (U, a, RAB))
    pa = w.s([w.s([arab, w.s([era], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. Word %s /\\ %s ) ) )' % (U, a, RAB, a, alpha, phia))], 'mpbid',
                  '( %s -> ( %s e. Word %s /\\ %s ) )' % (U, a, alpha, phia))], 'simprd', '( %s -> %s )' % (U, phia))
    stp = w.s([], steplab, '( ( %s e. Word %s /\\ %s e. %s /\\ %s ) -> %s )' % (a, alpha, b, alpha, phia, phib))
    pb = w.s([w.s([aw, bn, pa], '3jca', '( %s -> ( %s e. Word %s /\\ %s e. %s /\\ %s ) )' % (U, a, alpha, b, alpha, phia)),
              w.s([stp], 'a1i', '( %s -> ( ( %s e. Word %s /\\ %s e. %s /\\ %s ) -> %s ) )' % (U, a, alpha, b, alpha, phia, phib))], 'mpd',
             '( %s -> %s )' % (U, phib))
    s1c = w.s([bn, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word %s )' % (U, b, alpha))
    ccw = w.s([s1c, aw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (U, CSA, alpha))
    inb = w.s([w.s([erb], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. Word %s /\\ %s ) ) )' % (U, CSA, RAB, CSA, alpha, phib)),
               w.s([ccw, pb], 'jca', '( %s -> ( %s e. Word %s /\\ %s ) )' % (U, CSA, alpha, phib))], 'mpbird',
              '( %s -> %s e. %s )' % (U, CSA, RAB))
    imp = w.s([inb], 'ex', '( %s -> ( %s e. %s -> %s e. %s ) )' % (ANT, a, RAB, CSA, RAB))
    gen = w.s([imp], 'rgen2', 'A. %s e. Word %s A. %s e. %s ( %s e. %s -> %s e. %s )' % (a, alpha, b, alpha, a, RAB, CSA, RAB))
    conj = w.s([e0, gen], 'pm3.2i', '( (/) e. %s /\\ A. %s e. Word %s A. %s e. %s ( %s e. %s -> %s e. %s ) )' % (RAB, a, alpha, b, alpha, a, RAB, CSA, RAB))
    ind = w.s([conj, w.inst('algwrdi')], 'mpan', '( %s e. Word %s -> %s e. %s )' % (target, alpha, target, RAB))
    cgt, phit = cong(target)
    ert = w.s([cgt], 'elrab', '( %s e. %s <-> ( %s e. Word %s /\\ %s ) )' % (target, RAB, target, alpha, phit))
    out = w.s([w.s([ind, w.s([ert], 'biimpi', '( %s e. %s -> ( %s e. Word %s /\\ %s ) )' % (target, RAB, target, alpha, phit))], 'syl',
                   '( %s e. Word %s -> ( %s e. Word %s /\\ %s ) )' % (target, alpha, target, alpha, phit))], 'simprd',
              '( %s e. Word %s -> %s )' % (target, alpha, phit))
    return out, phit


def fuelind(w, phi, target, baselab, steplab, fvar='f', y='y', x='x', prods=()):
    """( target e. NN0 -> phi[target/fvar] ), by nn0ind.

    baselab proves |- phi[0/fvar];
    steplab proves |- ( ( F e. NN0 /\\ phi[F/fvar] ) -> phi[( F + 1 )/fvar] ).
    Returns (step name, phi[target/fvar])."""
    px = subst(phi, fvar, x)
    prx = [subst(e, fvar, x) for e in prods]
    def cong(repl):
        ANTE = '%s = %s' % (x, repl)
        idst = w.s([], 'id', '( %s -> %s )' % (ANTE, ANTE))
        rules = prodrules(w, px, x, repl, ANTE, idst, prx)
        st, new = w.wcongr(px, {x: repl}, ANTE, {x: idst}, rules=rules or None)
        assert new == subst(px, x, repl), 'congruence text mismatch:\n%s\n%s' % (new, subst(px, x, repl))
        return st, new
    c0, p0 = cong('0')
    cy, py = cong(y)
    cy1, py1 = cong('( %s + 1 )' % y)
    ct, pt = cong(target)
    b0 = w.s([], baselab, p0)
    stp = w.s([], steplab, '( ( %s e. NN0 /\\ %s ) -> %s )' % (y, py, py1))
    st6 = w.s([stp], 'ex', '( %s e. NN0 -> ( %s -> %s ) )' % (y, py, py1))
    out = w.s([c0, cy, cy1, ct, b0, st6], 'nn0ind', '( %s e. NN0 -> %s )' % (target, pt))
    return out, pt


def rweq(w, ante, expr, old, new, eqstep):
    """( ante -> expr = expr[old:=new] ), via the closed congruence under
    ( old = new ) so that a bound variable of expr in `ante` costs nothing."""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (old, new, old, new))
    st, ne = w.congr(expr, {}, '%s = %s' % (old, new), {}, rules={old: (new, idst)})
    out = w.s([eqstep, st], 'syl', '( %s -> %s = %s )' % (ante, expr, ne))
    return out, ne


def rwbi(w, ante, expr, old, new, eqstep):
    """( ante -> ( expr <-> expr[old:=new] ) ) for a wff expr, same trick."""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (old, new, old, new))
    st, ne = w.wcongr(expr, {}, '%s = %s' % (old, new), {}, rules={old: (new, idst)})
    out = w.s([eqstep, st], 'syl', '( %s -> ( %s <-> %s ) )' % (ante, expr, ne))
    return out, ne


def prdeq(w, ante, ax, bx, eqstep, i='i'):
    """( ante -> PRD( ax ) = PRD( bx ) ) from eqstep : ( ante -> ax = bx ),
    through the closed antecedent ( ax = bx ) so that a bound i in `ante`
    costs nothing."""
    E = '%s = %s' % (ax, bx)
    idst = w.s([], 'id', '( %s -> %s )' % (E, E))
    e1 = w.s([idst], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (E, ax, bx))
    e2 = w.s([e1], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ ( # ` %s ) ) )' % (E, ax, bx))
    e3 = w.s([w.s([idst], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (E, ax, i, bx, i))], 'adantr',
             '( ( %s /\\ %s e. ( 0 ..^ ( # ` %s ) ) ) -> ( %s ` %s ) = ( %s ` %s ) )' % (E, i, ax, ax, i, bx, i))
    e4 = w.s([e2, e3], 'prodeq12dv', '( %s -> %s = %s )' % (E, PRD(ax, i), PRD(bx, i)))
    return w.s([eqstep, e4], 'syl', '( %s -> %s = %s )' % (ante, PRD(ax, i), PRD(bx, i)))


def prodrules(w, phi, svar, repl, ante, idst, prods, i='i'):
    """rewrite rules for every PRD( x ) subterm of phi whose word x contains
    svar: tools/congr.py's prod congruence emits prodeq2dv/prodeq12dv with the
    wrong hypothesis shape, so each product is rewritten here instead."""
    rules = {}
    for ax in prods:
        if svar not in ax.split():
            continue
        est, bx = w.congr(ax, {svar: repl}, ante, {svar: idst})
        if est is None:
            continue
        rules[PRD(ax, i)] = (PRD(bx, i), prdeq(w, ante, ax, bx, est, i))
    return rules


def projeq(w, ante, xexpr, valstep, a, b, acl, bcl, k=1):
    """( ante -> ( 1st|2nd ` xexpr ) = a|b ) from valstep : ( ante -> xexpr = <. a , b >. )
    and closure steps acl : ( ante -> a e. ... ), bcl : ( ante -> b e. ... )."""
    lab = 'op1stg' if k == 1 else 'op2ndg'
    tag = '1st' if k == 1 else '2nd'
    res = a if k == 1 else b
    e1 = w.s([valstep], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` <. %s , %s >. ) )' % (ante, tag, xexpr, tag, a, b))
    e2 = w.s([acl, bcl, w.inst(lab)], 'syl2anc', '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, tag, a, b, res))
    return w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ante, tag, xexpr, res))


def zne1o(w, ante):
    """( ante -> -. (/) = 1o )"""
    n1 = w.s([], '1n0', '1o =/= (/)')
    n2 = w.s([n1], 'necomi', '(/) =/= 1o')
    n3 = w.s([n2, w.inst('neneq')], 'ax-mp', '-. (/) = 1o')
    return w.s([n3], 'a1i', '( %s -> -. (/) = 1o )' % ante)


def paircl(w, ante, xexpr, clstep, A, B):
    """( ante -> ( 1st ` xexpr ) e. A ) and ( ante -> ( 2nd ` xexpr ) e. B )"""
    a = w.s([clstep, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` %s ) e. %s )' % (ante, xexpr, A))
    b = w.s([clstep, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. %s )' % (ante, xexpr, B))
    return a, b


def ifproj(w, ante, xexpr, valstep, cond, thenexpr, elseexpr):
    """from valstep : ( ante -> xexpr = if ( cond , thenexpr , elseexpr ) ),
    the two branch equations ( ante /\\ cond -> xexpr = thenexpr ) and
    ( ante /\\ -. cond -> xexpr = elseexpr )."""
    IF = 'if ( %s , %s , %s )' % (cond, thenexpr, elseexpr)
    T = '( %s /\\ %s )' % (ante, cond)
    F = '( %s /\\ -. %s )' % (ante, cond)
    vt = w.s([valstep], 'adantr', '( %s -> %s = %s )' % (T, xexpr, IF))
    it = w.s([w.s([], 'simpr', '( %s -> %s )' % (T, cond))], 'iftrued', '( %s -> %s = %s )' % (T, IF, thenexpr))
    st = w.s([vt, it], 'eqtrd', '( %s -> %s = %s )' % (T, xexpr, thenexpr))
    vf = w.s([valstep], 'adantr', '( %s -> %s = %s )' % (F, xexpr, IF))
    if_ = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (F, cond))], 'iffalsed', '( %s -> %s = %s )' % (F, IF, elseexpr))
    sf = w.s([vf, if_], 'eqtrd', '( %s -> %s = %s )' % (F, xexpr, elseexpr))
    return st, sf


def family(runner, label, phi, basefn, stepfn, target='S', prods=(), desc='', bdesc='', sdesc='', finish=None, only=()):
    """base theorem `label`b, step theorem `label`s, assembly `label`, by algwrdi."""
    CSV = '( <" P "> ++ V )'
    ok = True
    if not only or label + 'b' in only:
        wb = W(label + 'b', bdesc or ('Base of the induction for ' + label + '.'))
        basefn(wb, subst(phi, 's', '(/)'))
        ok = runner(wb) and ok
    if not only or label + 's' in only:
        A = '( V e. Word NN0 /\\ P e. NN0 /\\ %s )' % subst(phi, 's', 'V')
        w2 = W(label + 's', sdesc or ('Step of the induction for ' + label + '.'))
        stepfn(w2, A, subst(phi, 's', 'V'), subst(phi, 's', CSV))
        ok = runner(w2) and ok
    if not only or label in only:
        wa = W(label, desc)
        st, phit = wrdind(wa, phi, target, label + 'b', label + 's', prods=prods)
        if finish is None:
            wa.lines[-1] = wa.lines[-1].replace('%s:' % st, 'qed:', 1)
        else:
            finish(wa, st, phit)
        ok = runner(wa) and ok
    return ok


def ralcons(w, ante, var, bodyq, bodyP, tail, rcstep, pexstep, sbstep):
    """( ante -> ( A. var e. ran ( <" P "> ++ tail ) bodyq <-> ( bodyP /\\ A. var e. ran tail bodyq ) ) ),
    from rcstep : ( ante -> ran ( <" P "> ++ tail ) = ( { P } u. ran tail ) ), pexstep : ( ante -> P e. _V )
    and sbstep : ( var = P -> ( bodyq <-> bodyP ) )."""
    cs = '( <" P "> ++ %s )' % tail
    RA = lambda x: 'A. %s e. %s %s' % (var, x, bodyq)
    u = w.s([w.s([rcstep], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (ante, RA('ran ' + cs), RA('( { P } u. ran %s )' % tail))),
             w.s([w.s([], 'ralunb', '( %s <-> ( %s /\\ %s ) )' % (RA('( { P } u. ran %s )' % tail), RA('{ P }'), RA('ran ' + tail)))], 'a1i',
                 '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ante, RA('( { P } u. ran %s )' % tail), RA('{ P }'), RA('ran ' + tail)))], 'bitrd',
            '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ante, RA('ran ' + cs), RA('{ P }'), RA('ran ' + tail)))
    rs0 = w.s([sbstep], 'ralsng', '( P e. _V -> ( %s <-> %s ) )' % (RA('{ P }'), bodyP))
    rs = w.s([pexstep, rs0], 'syl', '( %s -> ( %s <-> %s ) )' % (ante, RA('{ P }'), bodyP))
    out = w.s([u, w.s([rs], 'anbi1d', '( %s -> ( ( %s /\\ %s ) <-> ( %s /\\ %s ) ) )' % (ante, RA('{ P }'), RA('ran ' + tail), bodyP, RA('ran ' + tail)))],
              'bitrd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ante, RA('ran ' + cs), bodyP, RA('ran ' + tail)))
    return out, rs
