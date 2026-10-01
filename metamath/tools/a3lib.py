"""Sortie A3 helpers: the findcard2s induction template over a finite set, and
small worksheet idioms shared by the a3_* generators."""
import a1lib  # parser extensions (prod_, restricted abstractions, decimals)
from tm import W


def fcard2(w, prop, target, base, step, x='x', y='y', z='z'):
    """findcard2s: from |- prop((/)) and |- ( ( y e. Fin /\\ -. z e. y ) ->
    ( prop(y) -> prop(( y u. { z } )) ) ) conclude ( target e. Fin -> prop(target) ).
    prop is a callable taking the set expression as text."""
    subs = []
    for tgt in ['(/)', y, '( %s u. { %s } )' % (y, z), target]:
        idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, tgt, x, tgt))
        st, new = w.wcongr(prop(x), {x: tgt}, '%s = %s' % (x, tgt), {x: idst})
        assert new == prop(tgt), (new, prop(tgt))
        subs.append(st)
    return w.s(subs + [base, step], 'findcard2s', '( %s e. Fin -> %s )' % (target, prop(target)))


def ihcombine(w, G, ANT, ANTy, IH, D, step_i, step_ii):
    """The findcard2s step, with the induction hypothesis kept out of the
    antecedent of every bound-variable-sensitive step: from
    ( ( G /\\ ANT ) -> ANTy ) and ( ( G /\\ ANT ) -> ( IH -> D ) ) conclude
    ( G -> ( ( ANTy -> IH ) -> ( ANT -> D ) ) ), i.e. findcard2s.6 for the
    property ( ANTy -> IH )."""
    X = '( %s /\\ %s )' % (G, ANT)
    CH = '( %s -> %s )' % (ANTy, IH)
    p27 = w.s([], 'pm2.27', '( %s -> ( %s -> %s ) )' % (ANTy, CH, IH))
    iii = w.s([step_i, p27], 'syl', '( %s -> ( %s -> %s ) )' % (X, CH, IH))
    iv = w.s([iii, step_ii], 'syld', '( %s -> ( %s -> %s ) )' % (X, CH, D))
    e1 = w.s([iv], 'ex', '( %s -> ( %s -> ( %s -> %s ) ) )' % (G, ANT, CH, D))
    return w.s([e1], 'com23', '( %s -> ( %s -> ( %s -> %s ) ) )' % (G, CH, ANT, D))


FPP = '( ~P Prime i^i Fin )'
FP0 = '( ~P NN0 i^i Fin )'


def fpp(w, ante, phstep, Q='Q'):
    """from ( ante -> Q e. ( ~P Prime i^i Fin ) ): Q C_ Prime, Q e. Fin,
    Q e. ( ~P NN0 i^i Fin )"""
    b = w.s([phstep, w.inst('elfpw')], 'sylib', '( %s -> ( %s C_ Prime /\\ %s e. Fin ) )' % (ante, Q, Q))
    ss = w.s([b], 'simpld', '( %s -> %s C_ Prime )' % (ante, Q))
    fin = w.s([b], 'simprd', '( %s -> %s e. Fin )' % (ante, Q))
    p1 = w.s([], 'prmssnn', 'Prime C_ NN')
    p2 = w.s([], 'nnssnn0', 'NN C_ NN0')
    p3 = w.s([w.s([p1, p2], 'sstri', 'Prime C_ NN0')], 'a1i', '( %s -> Prime C_ NN0 )' % ante)
    s0 = w.s([ss, p3], 'sstrd', '( %s -> %s C_ NN0 )' % (ante, Q))
    f0 = w.s([w.s([s0, fin], 'jca', '( %s -> ( %s C_ NN0 /\\ %s e. Fin ) )' % (ante, Q, Q)), w.inst('elfpw')], 'sylibr', '( %s -> %s e. %s )' % (ante, Q, FP0))
    return ss, fin, f0


def lmodprod(w, ante, f0step, Q='Q'):
    """( ante -> ( Lmod ` Q ) = prod_ j e. Q j ) from ( ante -> Q e. ( ~P NN0 i^i Fin ) )"""
    v = w.s([f0step, w.inst('lmodqval')], 'syl', '( %s -> ( Lmod ` %s ) = prod_ q e. %s q )' % (ante, Q, Q))
    cb = w.s([w.s([], 'id', '( q = j -> q = j )')], 'cbvprodv', 'prod_ q e. %s q = prod_ j e. %s j' % (Q, Q))
    return w.s([v, w.s([cb], 'a1i', '( %s -> prod_ q e. %s q = prod_ j e. %s j )' % (ante, Q, Q))], 'eqtrd', '( %s -> ( Lmod ` %s ) = prod_ j e. %s j )' % (ante, Q, Q))


def memdvds(w, ante, Q, fin, ss, elstep, var='q'):
    """( ante -> var || prod_ j e. Q j ) for var e. Q, Q a finite set of primes;
    ante must not contain the bound variable j"""
    D = '( %s \\ { %s } )' % (Q, var)
    A = '( %s /\\ j e. %s )' % (ante, Q)
    AD = '( %s /\\ j e. %s )' % (ante, D)
    ssa = w.s([ss], 'adantr', '( %s -> %s C_ Prime )' % (A, Q))
    jel = w.s([], 'simpr', '( %s -> j e. %s )' % (A, Q))
    jp = w.s([ssa, jel], 'sseldd', '( %s -> j e. Prime )' % A)
    jnn = w.s([jp, w.inst('prmnn')], 'syl', '( %s -> j e. NN )' % A)
    jcc = w.s([jnn], 'nncnd', '( %s -> j e. CC )' % A)
    subst = w.s([], 'simpr', '( ( %s /\\ j = %s ) -> j = %s )' % (ante, var, var))
    sp = w.s([fin, jcc, elstep, subst], 'fprodsplit1',
             '( %s -> prod_ j e. %s j = ( %s x. prod_ j e. %s j ) )' % (ante, Q, var, D))
    dfin = w.s([fin, w.inst('diffi')], 'syl', '( %s -> %s e. Fin )' % (ante, D))
    dss = w.s([ss, w.inst('ssdifss')], 'syl', '( %s -> %s C_ Prime )' % (ante, D))
    dssa = w.s([dss], 'adantr', '( %s -> %s C_ Prime )' % (AD, D))
    djel = w.s([], 'simpr', '( %s -> j e. %s )' % (AD, D))
    djp = w.s([dssa, djel], 'sseldd', '( %s -> j e. Prime )' % AD)
    djnn = w.s([djp, w.inst('prmnn')], 'syl', '( %s -> j e. NN )' % AD)
    rnn = w.s([dfin, djnn], 'fprodnncl', '( %s -> prod_ j e. %s j e. NN )' % (ante, D))
    rz = w.s([rnn], 'nnzd', '( %s -> prod_ j e. %s j e. ZZ )' % (ante, D))
    vp = w.s([ss, elstep], 'sseldd', '( %s -> %s e. Prime )' % (ante, var))
    vz = w.s([vp, w.inst('prmz')], 'syl', '( %s -> %s e. ZZ )' % (ante, var))
    dv = w.s([vz, rz, w.inst('dvdsmul1')], 'syl2anc', '( %s -> %s || ( %s x. prod_ j e. %s j ) )' % (ante, var, var, D))
    return w.s([sp, dv], 'breqtrrd', '( %s -> %s || prod_ j e. %s j )' % (ante, var, Q)), vp


def lineq(w, ante, hyps, lhs, rhs, leaves, lre, rre, linarith):
    """( ante -> lhs = rhs ) for linear real expressions, by two linarith calls
    and letri3 (lin.py proves inequalities only); lre, rre prove realness."""
    a = linarith(w, ante, hyps, '%s <_ %s' % (lhs, rhs), leaves=leaves)
    b = linarith(w, ante, hyps, '%s <_ %s' % (rhs, lhs), leaves=leaves)
    bi = w.s([lre, rre, w.inst('letri3')], 'syl2anc', '( %s -> ( %s = %s <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (ante, lhs, rhs, lhs, rhs, rhs, lhs))
    return w.s([bi, w.s([a, b], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ante, lhs, rhs, rhs, lhs))], 'mpbird', '( %s -> %s = %s )' % (ante, lhs, rhs))
