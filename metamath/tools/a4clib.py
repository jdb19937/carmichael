"""Helpers for sortie A4c: fuel and word inductions whose induction property
quantifies the arguments the recursion changes (the DP accumulator, the
residue, the running product, the used list, the table).  The renaming of
the induction hypothesis's bound variables (M2-HANDOFF trap 1) is done in
the driver, so a callback never sees it."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from a4alib import *


POOL = 'zyxwvutsrqponmlkjihgfedcba'


def freshvars(k, texts):
    """k single-letter set variables not occurring as a token in any of texts
    (tools/congr.py recognises only single letters as variables)"""
    used = set()
    for t in texts:
        used |= set(t.split())
    out = []
    for ch in POOL:
        if len(out) == k:
            break
        if ch not in used:
            out.append(ch)
    assert len(out) == k, 'no fresh variables left'
    return out


def quantify(quants, names, body):
    b = body
    for i in range(len(quants) - 1, -1, -1):
        b = 'A. %s e. %s %s' % (names[i], quants[i][1], b)
    return b


def qphi(out, quants, body):
    return '( %s -> %s )' % (out, quantify(quants, [q[0] for q in quants], body))


def qren(w, quants, rnames, body):
    """closed step proving ( IHD <-> IHC ), IHC the fully renamed IHD."""
    k = len(quants)
    names = [q[0] for q in quants]
    def sub_from(j, text):
        t = text
        for i in range(j, k):
            t = subst(t, names[i], rnames[i])
        return t
    def wff(j):
        return quantify(quants, [names[i] if i < j else rnames[i] for i in range(k)], sub_from(j, body))
    acc = None
    for j in range(k - 1, -1, -1):
        R = sub_from(j + 1, body)
        for i in range(k - 1, j, -1):
            R = 'A. %s e. %s %s' % (rnames[i], quants[i][1], R)
        Rp = subst(R, names[j], rnames[j])
        ante = '%s = %s' % (names[j], rnames[j])
        idst = w.s([], 'id', '( %s -> %s )' % (ante, ante))
        st, new = w.wcongr(R, {names[j]: rnames[j]}, ante, {names[j]: idst})
        assert new == Rp, 'rename mismatch:\n%s\n%s' % (new, Rp)
        lhs = 'A. %s e. %s %s' % (names[j], quants[j][1], R)
        rhs = 'A. %s e. %s %s' % (rnames[j], quants[j][1], Rp)
        cur = w.s([st], 'cbvralvw', '( %s <-> %s )' % (lhs, rhs))
        for i in range(j - 1, -1, -1):
            lhs = 'A. %s e. %s %s' % (names[i], quants[i][1], lhs)
            rhs = 'A. %s e. %s %s' % (names[i], quants[i][1], rhs)
            cur = w.s([cur], 'ralbii', '( %s <-> %s )' % (lhs, rhs))
        acc = cur if acc is None else w.s([acc, cur], 'bitri', '( %s <-> %s )' % (wff(k), wff(j)))
    return acc, wff(k), wff(0)


class Ctx:
    """the accessors a callback needs: the antecedent, the outer typing, the
    induction hypothesis, and one step per quantified variable"""
    def __init__(self, ante, out, ih, vars):
        self.A = ante; self.out = out; self.ih = ih; self.v = vars


def _chainante(base, quants, names):
    a = base
    outs = []
    for i, (v, d) in enumerate(quants):
        a = '( %s /\\ %s e. %s )' % (a, names[i], d)
        outs.append(a)
    return a, outs


def _accessors(w, base, quants, names, basesteps):
    """build the nested antecedent ( ( base /\\ v1 e. D1 ) /\\ ... ) and
    lift every step of basesteps plus the membership steps to the full one."""
    k = len(quants)
    full, levels = _chainante(base, quants, names)
    def lift(st, frm, formula):
        """adantr st from antecedent `frm` up to the full antecedent"""
        cur = st; curante = frm
        idx = 0 if frm == base else levels.index(frm) + 1
        for j in range(idx, k):
            nxt = levels[j]
            cur = w.s([cur], 'adantr', '( %s -> %s )' % (nxt, formula))
            curante = nxt
        return cur
    lifted = [lift(st, base, f) for st, f in basesteps]
    vsteps = []
    for i in range(k):
        f = '%s e. %s' % (names[i], quants[i][1])
        st = w.s([], 'simpr', '( %s -> %s )' % (levels[i], f))
        vsteps.append(lift(st, levels[i], f))
    return full, lifted, vsteps


def qfuel(run, label, out, quants, body, basefn, stepfn, instfn=None, target='F',
          rnames=None, fvar='f', desc='', only=(), prods=(), innerfn=None):
    """nn0ind on `fvar` with induction property ( out -> A. v1 e. D1 ... body ).

    basefn(w, ctx, goal)      proves ( ctx.A -> body[fvar:=0] )
    stepfn(w, ctx, goal)      proves ( ctx.A -> body[fvar:=( F + 1 )] ),
                              ctx.ih being ( ctx.A -> IHC ) with renamed binders
    instfn(w) (optional)      writes the instance theorem `label`
    """
    k = len(quants)
    names = [q[0] for q in quants]
    if rnames is None:
        rnames = freshvars(k, [out, body] + [q[0] for q in quants] + [q[1] for q in quants])
    PHI = lambda f: qphi(out, quants, subst(body, fvar, f))
    ok = True
    # ------------------------------------------------------------- base
    if not only or label + 'b' in only:
        w = W(label + 'b', 'Base of the induction for ' + label + '.')
        bd = subst(body, fvar, '0')
        full, lifted, vsteps = _accessors(w, out, quants, names, [])
        outst = _outstep(w, out, quants, names)
        ctx = Ctx(full, outst, None, vsteps)
        ctx.rn = rnames
        last = basefn(w, ctx, bd)
        _close(w, last, full, out, quants, names, bd, PHI('0'), top=True)
        ok = run(w) and ok
    # ------------------------------------------------------------- step
    if not only or label + 's' in only:
        w = W(label + 's', 'Step of the induction for ' + label + '.')
        bF = subst(body, fvar, target)
        bF1 = subst(body, fvar, '( %s + 1 )' % target)
        if innerfn is None:
            ren, IHD, IHC = qren(w, quants, rnames, bF)
        else:
            st0, bF2 = innerfn(w, bF)
            lhs, rhs, cur = bF, bF2, st0
            for i in range(k - 1, -1, -1):
                lhs = 'A. %s e. %s %s' % (names[i], quants[i][1], lhs)
                rhs = 'A. %s e. %s %s' % (names[i], quants[i][1], rhs)
                cur = w.s([cur], 'ralbii', '( %s <-> %s )' % (lhs, rhs))
            ren2, IHDmid, IHC = qren(w, quants, rnames, bF2)
            IHD = quantify(quants, names, bF)
            ren = w.s([cur, ren2], 'bitri', '( %s <-> %s )' % (IHD, IHC))
        A = '( %s e. NN0 /\\ ( %s -> %s ) )' % (target, out, IHD)
        AC = '( %s e. NN0 /\\ ( %s -> %s ) )' % (target, out, IHC)
        conv = w.s([w.s([], 'simpl', '( %s -> %s e. NN0 )' % (A, target)),
                    w.s([w.s([], 'simpr', '( %s -> ( %s -> %s ) )' % (A, out, IHD)),
                         w.s([w.s([ren], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd',
                             '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))], 'syld',
                        '( %s -> ( %s -> %s ) )' % (A, out, IHC))], 'jca', '( %s -> %s )' % (A, AC))
        B1 = '( %s /\\ %s )' % (AC, out)
        full, lifted, vsteps = _accessors(w, B1, quants, names,
                                          [(w.s([], 'simpr', '( %s -> %s )' % (B1, out)), out),
                                           (w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (B1, AC)), ], 'simprd',
                                                     '( %s -> ( %s -> %s ) )' % (B1, out, IHC)),
                                                 w.s([], 'simpr', '( %s -> %s )' % (B1, out))], 'mpd',
                                                '( %s -> %s )' % (B1, IHC)), IHC),
                                           (w.s([w.s([], 'simpl', '( %s -> %s )' % (B1, AC))], 'simpld',
                                                '( %s -> %s e. NN0 )' % (B1, target)), '%s e. NN0' % target)])
        ctx = Ctx(full, lifted[0], lifted[1], vsteps)
        ctx.fuel = lifted[2]
        ctx.rn = rnames
        ctx.ihf = IHC
        last = stepfn(w, ctx, bF1)
        cl = _close(w, last, full, B1, quants, names, bF1, None, top=False)
        ex = w.s([cl], 'ex', '( %s -> %s )' % (AC, PHI('( %s + 1 )' % target)))
        w.qed([conv, ex], 'syl', '( %s -> %s )' % (A, PHI('( %s + 1 )' % target)))
        ok = run(w) and ok
    # ------------------------------------------------------------- assembly
    if not only or label + 'l' in only:
        w = W(label + 'l', 'The induction for ' + label + ', as nn0ind delivers it.')
        ph = PHI(fvar)
        iy, ix = freshvars(2, [ph, target, fvar])
        st, pt = fuelind(w, ph, target, label + 'b', label + 's', fvar=fvar, y=iy, x=ix, prods=prods)
        w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
        ok = run(w) and ok
    if instfn is not None and (not only or label in only):
        w = W(label, desc)
        instfn(w)
        ok = run(w) and ok
    return ok


def _outstep(w, out, quants, names):
    """( full antecedent -> out ) for the base worksheet"""
    k = len(quants)
    cur = w.s([], 'id', '( %s -> %s )' % (out, out))
    a = out
    for i in range(k):
        a = '( %s /\\ %s e. %s )' % (a, names[i], quants[i][1])
        cur = w.s([cur], 'adantr', '( %s -> %s )' % (a, out))
    return cur


def _close(w, last, full, base, quants, names, bd, phi, top):
    """k ralrimiva steps from ( full -> bd ) back to ( base -> A. ... bd )"""
    k = len(quants)
    _, levels = _chainante(base, quants, names)
    cur = last
    body = bd
    for i in range(k - 1, -1, -1):
        ante = levels[i - 1] if i > 0 else base
        body = 'A. %s e. %s %s' % (names[i], quants[i][1], body)
        cur = w.s([cur], 'ralrimiva', '( %s -> %s )' % (ante, body))
    if top:
        w.lines[-1] = w.lines[-1].replace('%s:' % cur, 'qed:', 1)
        w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ' + phi
    return cur


# ---------------------------------------------------------------- instantiation
def inst1(w, ante, ih, var, dom, bodyv, repl, clstep, concl=None):
    """from ih : ( ante -> A. var e. dom bodyv ) and clstep : ( ante -> repl e. dom ),
    the instance ( ante -> bodyv[var:=repl] )"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, repl, var, repl))
    st, new = w.wcongr(bodyv, {var: repl}, '%s = %s' % (var, repl), {var: idst})
    want = subst(bodyv, var, repl)
    assert new == want, 'instance mismatch:\n%s\n%s' % (new, want)
    return w.s([st, ih, clstep], 'rspcdva', '( %s -> %s )' % (ante, new)), new


def instn(w, ante, ih, quants, body, repls, clsteps):
    """instantiate a nest A. v1 e. D1 ... A. vk e. Dk body at v1 := repls[0], ..."""
    k = len(quants)
    cur = ih
    bd = body
    for i in range(k):
        inner = bd
        for j in range(k - 1, i, -1):
            inner = 'A. %s e. %s %s' % (quants[j][0], quants[j][1], inner)
        cur, inner2 = inst1(w, ante, cur, quants[i][0], quants[i][1], inner, repls[i], clsteps[i])
        bd = subst(bd, quants[i][0], repls[i])
    return cur, bd


# ---------------------------------------------------------------- projections
def prj(w, ante, expr, valstep, A, B, k, aex=None, bex=None):
    lab = 'op1stg' if k == 1 else 'op2ndg'
    tag = '1st' if k == 1 else '2nd'
    res = A if k == 1 else B
    if aex is None:
        aex = w.s([w.s([], 'fvex', '%s e. _V' % A)], 'a1i', '( %s -> %s e. _V )' % (ante, A))
    if bex is None:
        bex = w.s([w.s([], 'ovex', '%s e. _V' % B)], 'a1i', '( %s -> %s e. _V )' % (ante, B))
    e1 = w.s([valstep], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` <. %s , %s >. ) )' % (ante, tag, expr, tag, A, B))
    e2 = w.s([aex, bex, w.inst(lab)], 'syl2anc', '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, tag, A, B, res))
    return w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ante, tag, expr, res))


# ---------------------------------------------------------------- the dpGo body
NONE = '( inr ` (/) )'
DPO = '( ( L e. NN /\\ P e. NN0 ) /\\ T e. Tbl )'
MOD = '( ( F x. P ) mod L )'
CSW = '( <" P "> ++ ( 2nd ` ( T ` F ) ) )'
def DG(f, a): return '( ( ( ( L DpGo P ) ` T ) ` %s ) ` %s )' % (f, a)
def ACC(a): return 'if ( ( T ` F ) = %s , %s , ( ( %s SetIfNone %s ) ` %s ) )' % (NONE, a, a, MOD, CSW)


def dp_accl(w, ctx, a='a'):
    return w.s([w.s([ctx.out, w.s([ctx.fuel, ctx.v[0]], 'jca', '( %s -> ( F e. NN0 /\\ %s e. Tbl ) )' % (ctx.A, a))], 'jca',
                    '( %s -> ( %s /\\ ( F e. NN0 /\\ %s e. Tbl ) ) )' % (ctx.A, DPO, a)), w.inst('dpgoacl')], 'syl',
               '( %s -> %s e. Tbl )' % (ctx.A, ACC(a)))


def dp_p1(w, ctx, a='a'):
    X = ACC(a)
    return w.s([w.s([ctx.out, ctx.fuel], 'jca', '( %s -> ( %s /\\ F e. NN0 ) )' % (ctx.A, DPO)), ctx.v[0],
                w.inst('dpgop1')], 'syl2anc',
               '( %s -> %s = <. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >. )' % (ctx.A, DG('( F + 1 )', a), DG('F', X), DG('F', X)))


def dp_lem(w, ante, lab, outst, fst, ast, a, extrast, extraf, concl):
    """apply one of dpgoace / dpgoacnn / dpgoacself / dpgoacc, whose antecedent is
    ( DPO /\\ ( F e. NN0 /\\ a e. Tbl ) /\\ extraf )"""
    j = w.s([outst, w.s([fst, ast], 'jca', '( %s -> ( F e. NN0 /\\ %s e. Tbl ) )' % (ante, a)), extrast], '3jca',
            '( %s -> ( %s /\\ ( F e. NN0 /\\ %s e. Tbl ) /\\ %s ) )' % (ante, DPO, a, extraf))
    return w.s([j, w.inst(lab)], 'syl', '( %s -> %s )' % (ante, concl))


# ------------------------------------------------------- the three DP invariants
def TS(l, t, e, d='d', i='i'):
    TE = '( 2nd ` ( %s ` %s ) )' % (t, d)
    return ("A. %s e. NN0 ( ( %s ` %s ) =/= %s -> ( ( %s =/= (/) /\\ Fun `' %s ) /\\ ( ran %s C_ ran %s /\\ ( %s mod %s ) = %s ) ) )"
            % (d, t, d, NONE, TE, TE, TE, e, PRD(TE, i), l, d))


def TB(t, k, d='d'):
    TE = '( 2nd ` ( %s ` %s ) )' % (t, d)
    return 'A. %s e. NN0 ( ( %s ` %s ) =/= %s -> ( # ` %s ) <_ %s )' % (d, t, d, NONE, TE, k)


def TC(l, t, e, s='s', q='q'):
    return ('A. %s e. ~P ran %s ( %s =/= (/) -> ( %s ` ( prod_ %s e. %s %s mod %s ) ) =/= %s )'
            % (s, e, s, t, q, s, q, l, NONE))


def ralconv(w, dom, old, new, body):
    """closed ( A. new e. dom body[old:=new] <-> A. old e. dom body )"""
    bn = subst(body, old, new)
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (new, old, new, old))
    st, nb = w.wcongr(bn, {new: old}, '%s = %s' % (new, old), {new: idst})
    assert nb == body, 'ralconv mismatch:\n%s\n%s' % (nb, body)
    return w.s([st], 'cbvralv', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (new, dom, bn, old, dom, body))


def rwbi2(w, ante, expr, old, new, eqstep, i='i'):
    """( ante -> ( expr <-> expr[old:=new] ) ) from eqstep : ( ante -> old = new ),
    with the product subterm rewritten by hand (tools/congr.py's prod congruence
    emits the wrong hypothesis shape)"""
    E = '%s = %s' % (old, new)
    idst = w.s([], 'id', '( %s -> %s )' % (E, E))
    rules = {old: (new, idst)}
    if PRD(old, i) in expr:
        rules[PRD(old, i)] = (PRD(new, i), prdeq(w, E, old, new, idst, i))
    st, ne = w.wcongr(expr, {}, E, {}, rules=rules)
    out = w.s([eqstep, st], 'syl', '( %s -> ( %s <-> %s ) )' % (ante, expr, ne))
    return out, ne


def qwrd(run, label, out, quants, body, basefn, stepfn, instfn=None, target='W',
         svar='s', rnames=None, desc='', only=(), prods=(), innerfn=None, alpha='NN0'):
    """algwrdi induction on `svar` with induction property
    ( out -> A. v1 e. D1 ... A. vk e. Dk body ).

    basefn(w, ctx, goal)  proves ( ctx.A -> body[svar:=(/)] )
    stepfn(w, ctx, goal)  proves ( ctx.A -> body[svar:=( <" P "> ++ V )] ),
                          ctx.ih being the renamed induction hypothesis,
                          ctx.wrd and ctx.let the typing of V and P
    """
    k = len(quants)
    names = [q[0] for q in quants]
    if rnames is None:
        rnames = freshvars(k, [out, body] + names + [q[1] for q in quants] + ['P', 'V', svar, target])
    PHI = lambda t: qphi(out, quants, subst(body, svar, t))
    CSV = '( <" P "> ++ V )'

    def _b(w, goal):
        bd = subst(body, svar, '(/)')
        full, lifted, vsteps = _accessors(w, out, quants, names, [])
        outst = _outstep(w, out, quants, names)
        ctx = Ctx(full, outst, None, vsteps); ctx.rn = rnames
        last = basefn(w, ctx, bd)
        _close(w, last, full, out, quants, names, bd, PHI('(/)'), top=True)

    def _s(w, A, ih, co):
        bV = subst(body, svar, 'V')
        bC = subst(body, svar, CSV)
        if innerfn is None:
            ren, IHD, IHC = qren(w, quants, rnames, bV)
        else:
            st0, bV2 = innerfn(w, bV)
            lhs, rhs, cur = bV, bV2, st0
            for i in range(k - 1, -1, -1):
                lhs = 'A. %s e. %s %s' % (names[i], quants[i][1], lhs)
                rhs = 'A. %s e. %s %s' % (names[i], quants[i][1], rhs)
                cur = w.s([cur], 'ralbii', '( %s <-> %s )' % (lhs, rhs))
            ren2, IHDmid, IHC = qren(w, quants, rnames, bV2)
            IHD = quantify(quants, names, bV)
            ren = w.s([cur, ren2], 'bitri', '( %s <-> %s )' % (IHD, IHC))
        AC = '( V e. Word %s /\\ P e. %s /\\ ( %s -> %s ) )' % (alpha, alpha, out, IHC)
        conv = w.s([w.s([], 'simp1', '( %s -> V e. Word %s )' % (A, alpha)),
                    w.s([], 'simp2', '( %s -> P e. %s )' % (A, alpha)),
                    w.s([w.s([], 'simp3', '( %s -> ( %s -> %s ) )' % (A, out, IHD)),
                         w.s([w.s([ren], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd',
                             '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))], 'syld',
                        '( %s -> ( %s -> %s ) )' % (A, out, IHC))], '3jca', '( %s -> %s )' % (A, AC))
        B1 = '( %s /\\ %s )' % (AC, out)
        base = [(w.s([], 'simpr', '( %s -> %s )' % (B1, out)), out),
                (w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (B1, AC))], 'simp3d',
                          '( %s -> ( %s -> %s ) )' % (B1, out, IHC)),
                      w.s([], 'simpr', '( %s -> %s )' % (B1, out))], 'mpd', '( %s -> %s )' % (B1, IHC)), IHC),
                (w.s([w.s([], 'simpl', '( %s -> %s )' % (B1, AC))], 'simp1d', '( %s -> V e. Word %s )' % (B1, alpha)),
                 'V e. Word %s' % alpha),
                (w.s([w.s([], 'simpl', '( %s -> %s )' % (B1, AC))], 'simp2d', '( %s -> P e. %s )' % (B1, alpha)),
                 'P e. %s' % alpha)]
        full, lifted, vsteps = _accessors(w, B1, quants, names, base)
        ctx = Ctx(full, lifted[0], lifted[1], vsteps)
        ctx.wrd = lifted[2]; ctx.let = lifted[3]; ctx.rn = rnames; ctx.ihf = IHC
        last = stepfn(w, ctx, bC)
        cl = _close(w, last, full, B1, quants, names, bC, None, top=False)
        ex = w.s([cl], 'ex', '( %s -> %s )' % (AC, PHI(CSV)))
        w.qed([conv, ex], 'syl', '( %s -> %s )' % (A, PHI(CSV)))

    ok = family2(run, label, PHI(svar), _b, _s, target=target, prods=prods, desc=desc,
                 bdesc='Base of the induction for ' + label + '.',
                 sdesc='Step of the induction for ' + label + '.',
                 only=only, svar=svar, alpha=alpha)
    if instfn is not None and (not only or label + 'i' in only):
        w = W(label + 'i', 'The instance of ' + label + ' a consumer uses.')
        instfn(w)
        ok = run(w) and ok
    return ok


def lnest(w, ante, items):
    """left-nested conjunction: items is a list of (step, formula) pairs"""
    st, f = items[0]
    for s2, f2 in items[1:]:
        nf = '( %s /\\ %s )' % (f, f2)
        st = w.s([st, s2], 'jca', '( %s -> %s )' % (ante, nf))
        f = nf
    return st, f


def family2(runner, label, phi, basefn, stepfn, target='S', prods=(), desc='', bdesc='', sdesc='',
            only=(), svar='s', alpha='NN0'):
    """tools/a4alib.py's `family` with the induction variable a parameter"""
    CSV = '( <" P "> ++ V )'
    ok = True
    if not only or label + 'b' in only:
        wb = W(label + 'b', bdesc or ('Base of the induction for ' + label + '.'))
        basefn(wb, subst(phi, svar, '(/)'))
        ok = runner(wb) and ok
    if not only or label + 's' in only:
        A = '( V e. Word %s /\\ P e. %s /\\ %s )' % (alpha, alpha, subst(phi, svar, 'V'))
        w2 = W(label + 's', sdesc or ('Step of the induction for ' + label + '.'))
        stepfn(w2, A, subst(phi, svar, 'V'), subst(phi, svar, CSV))
        ok = runner(w2) and ok
    if not only or label in only:
        wa = W(label, desc)
        st, phit = wrdind(wa, phi, target, label + 'b', label + 's', svar=svar, alpha=alpha, prods=prods)
        wa.lines[-1] = wa.lines[-1].replace('%s:' % st, 'qed:', 1)
        ok = runner(wa) and ok
    return ok
