#!/usr/bin/env python3
"""Sortie A1b: step 4 of Algorithm.lean (the DP table: emptyTbl, setIfNone,
dpGo, dpStep).  MM_DB=sorties/a1b.mm python3 tools/gen/a1b_dp.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import (W, Cl, Spec, th_sf, th_cl, th_0, th_p1, defapply, conjsteps,
                    promote_qed, applied_text, W0, TB)

CLAUSE = lambda w, cl, sp: cl.mem(sp.clause(), sp.cod)
TBM = '( ( Word NN0 |_| 1o ) ^m NN0 )'
UPD = '( ( T |` ( A \\ { R } ) ) u. { <. R , V >. } )'

DPGO = Spec('DpGo', 'DpGoS', TB, '( Tbl X. NN0 )',
            [('l', 'NN', 'L', 'fix'), ('p', 'NN0', 'P', 'fix'), ('t', TB, 'T', 'fix'),
             ('f', 'NN0', 'F', 'fuel'), ('a', TB, 'A', 'chg')],
            '<. g , 0 >.',
            desc='  Lean: dpGo, the loop of one dynamic-programming step.')


def algupd():
    ante = '( T : A --> B /\\ R e. A /\\ V e. B )'
    w = W('algupd', 'Function update keeps a function total: Lean\'s '
                    'Function.update t r v, written ` ( ( T |` ( A \\ { R } ) ) u. '
                    '{ <. R , V >. } ) ` as in the machine model, maps ` A ` into '
                    '` B ` again.  This is what keeps ~ df-setifnone inside ~ df-tbl .')
    tf = w.s([], 'simp1', '( %s -> T : A --> B )' % ante)
    ra = w.s([], 'simp2', '( %s -> R e. A )' % ante)
    vb = w.s([], 'simp3', '( %s -> V e. B )' % ante)
    ds = w.s([w.s([], 'difss', '( A \\ { R } ) C_ A')], 'a1i', '( %s -> ( A \\ { R } ) C_ A )' % ante)
    rs = w.s([tf, ds, w.s([], 'fssres', '( ( T : A --> B /\\ ( A \\ { R } ) C_ A ) -> '
                                        '( T |` ( A \\ { R } ) ) : ( A \\ { R } ) --> B )')],
             'syl2anc', '( %s -> ( T |` ( A \\ { R } ) ) : ( A \\ { R } ) --> B )' % ante)
    i = w.s([], 'fsnunf2', '( ( ( T |` ( A \\ { R } ) ) : ( A \\ { R } ) --> B /\\ R e. A /\\ V e. B ) '
                           '-> %s : A --> B )' % UPD)
    w.qed([rs, ra, vb, i], 'syl3anc', '( %s -> %s : A --> B )' % (ante, UPD))
    return w


def emptytblval():
    w = W('emptytblval', 'The empty table has no entry.  Lean: emptyTbl.')
    ante, hs = conjsteps(w, ['R e. NN0'])
    cl = Cl(w, ante)
    cl.have('R', 'NN0', hs['R e. NN0'])
    st, val = defapply(w, cl, 'df-emptytbl', 'EmptyTbl', ['R'])
    promote_qed(w, st)
    return w


def emptytblcl():
    w = W('emptytblcl', 'The empty table is a table.')
    bm = '( r e. NN0 |-> ( inr ` (/) ) )'
    a2 = '( T. /\\ r e. NN0 )'
    c2 = Cl(w, a2)
    b = c2.mem('( inr ` (/) )', '( Word NN0 |_| 1o )')
    fm = w.s([b, w.s([], 'df-emptytbl', 'EmptyTbl = %s' % bm)], 'fmptd',
             '( T. -> EmptyTbl : NN0 --> ( Word NN0 |_| 1o ) )')
    fm2 = w.s([fm], 'mptru', 'EmptyTbl : NN0 --> ( Word NN0 |_| 1o )')
    dj = w.s([], 'djuex', '( ( Word NN0 e. _V /\\ 1o e. _V ) -> ( Word NN0 |_| 1o ) e. _V )')
    wx = w.s([], 'wrdexi', 'Word NN0 e. _V')
    ox = w.s([], '1oex', '1o e. _V')
    dv = w.s([wx, ox, dj], 'mp2an', '( Word NN0 |_| 1o ) e. _V')
    nx = w.s([], 'nn0ex', 'NN0 e. _V')
    em = w.s([dv, nx, w.s([], 'elmapg', '( ( ( Word NN0 |_| 1o ) e. _V /\\ NN0 e. _V ) -> '
                                       '( EmptyTbl e. %s <-> EmptyTbl : NN0 --> ( Word NN0 |_| 1o ) ) )' % TBM)],
             'mp2an', '( EmptyTbl e. %s <-> EmptyTbl : NN0 --> ( Word NN0 |_| 1o ) )' % TBM)
    el = w.s([fm2, em], 'mpbir', 'EmptyTbl e. %s' % TBM)
    df = w.s([], 'df-tbl', 'Tbl = %s' % TBM)
    w.qed([el, df], 'eleqtrri', 'EmptyTbl e. Tbl')
    return w


def setifnoneval():
    w = W('setifnoneval', 'The value of ~ df-setifnone .  Lean: setIfNone.')
    args = [('T', TB), ('R', 'NN0'), ('S', W0)]
    ante, hs = conjsteps(w, ['%s e. %s' % (v, t) for v, t in args])
    cl = Cl(w, ante)
    for v, t in args:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-setifnone', 'SetIfNone', ['T', 'R', 'S'])
    promote_qed(w, st)
    return w


def setifnonecl():
    w = W('setifnonecl', 'A guarded table write is a table.')
    args = [('T', TB), ('R', 'NN0'), ('S', W0)]
    ante, hs = conjsteps(w, ['%s e. %s' % (v, t) for v, t in args])
    cl = Cl(w, ante)
    for v, t in args:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-setifnone', 'SetIfNone', ['T', 'R', 'S'])
    # the two branches of the if
    upd = '( ( T |` ( NN0 \\ { R } ) ) u. { <. R , ( inl ` S ) >. } )'
    tf = w.s([hs['T e. Tbl'], w.s([], 'df-tbl', 'Tbl = %s' % TBM)], 'eleqtrdi',
             '( %s -> T e. %s )' % (ante, TBM))
    tfn = w.s([tf, w.s([], 'elmapi', '( T e. %s -> T : NN0 --> ( Word NN0 |_| 1o ) )' % TBM)],
              'syl', '( %s -> T : NN0 --> ( Word NN0 |_| 1o ) )' % ante)
    ilc = cl.mem('( inl ` S )', '( Word NN0 |_| 1o )')
    up = w.s([tfn, hs['R e. NN0'], ilc,
              w.s([], 'algupd', '( ( T : NN0 --> ( Word NN0 |_| 1o ) /\\ R e. NN0 /\\ '
                                '( inl ` S ) e. ( Word NN0 |_| 1o ) ) -> %s : NN0 --> ( Word NN0 |_| 1o ) )' % upd)],
             'syl3anc', '( %s -> %s : NN0 --> ( Word NN0 |_| 1o ) )' % (ante, upd))
    dv = cl.mem('( Word NN0 |_| 1o )', '_V')
    nx = cl.mem('NN0', '_V')
    em = w.s([dv, nx, w.s([], 'elmapg', '( ( ( Word NN0 |_| 1o ) e. _V /\\ NN0 e. _V ) -> '
                                       '( %s e. %s <-> %s : NN0 --> ( Word NN0 |_| 1o ) ) )' % (upd, TBM, upd))],
             'syl2anc', '( %s -> ( %s e. %s <-> %s : NN0 --> ( Word NN0 |_| 1o ) ) )' % (ante, upd, TBM, upd))
    el = w.s([em, up], 'mpbird', '( %s -> %s e. %s )' % (ante, upd, TBM))
    df = w.s([w.s([], 'df-tbl', 'Tbl = %s' % TBM)], 'a1i', '( %s -> Tbl = %s )' % (ante, TBM))
    el2 = w.s([el, df], 'eleqtrrd', '( %s -> %s e. Tbl )' % (ante, upd))
    cl.have(upd, 'Tbl', el2)
    mm = cl.mem(val, 'Tbl')
    w.qed([st, mm], 'eqeltrd', '( %s -> ( ( T SetIfNone R ) ` S ) e. Tbl )' % ante)
    return w


def dpstepval():
    w = W('dpstepval', 'The value of ~ df-dpstep .  Lean: dpStep.')
    args = [('L', 'NN'), ('P', 'NN0'), ('T', TB)]
    ante, hs = conjsteps(w, ['%s e. %s' % (v, t) for v, t in args])
    cl = Cl(w, ante)
    for v, t in args:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-dpstep', 'DpStep', ['L', 'P', 'T'])
    promote_qed(w, st)
    return w


def dpstepcl():
    w = W('dpstepcl', 'One dynamic-programming step returns a table and an operation count.')
    args = [('L', 'NN'), ('P', 'NN0'), ('T', TB)]
    ante, hs = conjsteps(w, ['%s e. %s' % (v, t) for v, t in args])
    cl = Cl(w, ante)
    for v, t in args:
        cl.have(v, t, hs['%s e. %s' % (v, t)])
    st, val = defapply(w, cl, 'df-dpstep', 'DpStep', ['L', 'P', 'T'])
    mm = cl.mem(val, '( Tbl X. NN0 )')
    w.qed([st, mm], 'eqeltrd', '( %s -> ( ( L DpStep P ) ` T ) e. ( Tbl X. NN0 ) )' % ante)
    return w


BUILD = {'algupd': algupd, 'emptytblval': emptytblval, 'emptytblcl': emptytblcl,
         'setifnoneval': setifnoneval, 'setifnonecl': setifnonecl,
         'dpgosf': lambda: th_sf(DPGO, CLAUSE), 'dpgocl': lambda: th_cl(DPGO),
         'dpgo0': lambda: th_0(DPGO), 'dpgop1': lambda: th_p1(DPGO),
         'dpstepval': dpstepval, 'dpstepcl': dpstepcl}

ORDER = ['algupd', 'emptytblval', 'emptytblcl', 'setifnoneval', 'setifnonecl',
         'dpgosf', 'dpgocl', 'dpgo0', 'dpgop1', 'dpstepval', 'dpstepcl']

if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
