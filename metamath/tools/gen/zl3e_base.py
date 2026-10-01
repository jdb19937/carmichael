"""ZL3e: shared helpers for the section-H generators (tools/gen/zl3e_*.py)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl3d_g2 import *                     # W D chain cst ad vsub fv1 pcases par_nn0 eps_cl linarith nlinarith lineq Closure ...
from c0lib import runh, hyp
import zl3elib as LE
HOL = LE.HOL

SE = LE.STATEMENTS
ONLY = [a for a in sys.argv[1:]]


def goe(w):
    if ONLY and w.label not in ONLY:
        return True
    if os.environ.get('ZL3E_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if LE.HYPS.get(w.label) else w.run()


def wante(label, main):
    return main and (not ONLY or label in ONLY)


def ante_e(label):
    return L.split_imp(SE[label])


def lcl(w, A, lab, fact):
    """( A -> fact ) for a closed fact proved by lab"""
    return cst(w, A, lab, fact)


def num_(w, A, n, kind='RR'):
    """( A -> n e. RR ) for a numeral / fraction literal"""
    return Closure(w, A, {}).mem(n, kind)


def rsplit(w, A, st, f, parts):
    """split a conjunction step into its conjuncts (list of formulas, left-assoc binary)"""
    raise NotImplementedError


def p01(w, A, pp, P='P'):
    """from ( A -> P e. { 0 , 1 } ): P e. RR, 0 <_ P, P <_ 1"""
    pn = par_nn0(w, A, pp, P)
    pr = D(w, A, 'nn0red', [pn], '%s e. RR' % P); p0 = D(w, A, 'nn0ge0d', [pn], '0 <_ %s' % P)
    A0 = '( %s /\\ %s = 0 )' % (A, P); A1 = '( %s /\\ %s = 1 )' % (A, P)
    s0 = w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (A0, P)), cst(w, A0, '0le1', '0 <_ 1')], 'eqbrtrd', '( %s -> %s <_ 1 )' % (A0, P))
    s1 = w.s([w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, P)), cst(w, A1, '1le1', '1 <_ 1')], 'eqbrtrd', '( %s -> %s <_ 1 )' % (A1, P))
    p1 = w.s([s0, s1, w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( %s = 0 \\/ %s = 1 ) )' % (A, P, P))], 'mpjaodan', '( %s -> %s <_ 1 )' % (A, P))
    return pn, pr, p0, p1


def reim_w(w, A, v, vc, pc, pr, P='P'):
    """Re and Im of W = ( v + P ) / 2"""
    Wv = '( ( %s + %s ) / 2 )' % (v, P)
    two = cst(w, A, '2re', '2 e. RR'); t0 = cst(w, A, '2ne0', '2 =/= 0')
    spc = D(w, A, 'addcld', [vc, pc], '( %s + %s ) e. CC' % (v, P))
    re_ = chain(w, A, ['( Re ` %s )' % Wv, '( ( Re ` ( %s + %s ) ) / 2 )' % (v, P), '( ( ( Re ` %s ) + ( Re ` %s ) ) / 2 )' % (v, P), '( ( ( Re ` %s ) + %s ) / 2 )' % (v, P)],
                [D(w, A, 'redivd', [two, spc, t0], '( Re ` %s ) = ( ( Re ` ( %s + %s ) ) / 2 )' % (Wv, v, P)),
                 D(w, A, 'oveq1d', [D(w, A, 'readdd', [vc, pc], '( Re ` ( %s + %s ) ) = ( ( Re ` %s ) + ( Re ` %s ) )' % (v, P, v, P))],
                   '( ( Re ` ( %s + %s ) ) / 2 ) = ( ( ( Re ` %s ) + ( Re ` %s ) ) / 2 )' % (v, P, v, P)),
                 D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'rered', [pr], '( Re ` %s ) = %s' % (P, P))], '( ( Re ` %s ) + ( Re ` %s ) ) = ( ( Re ` %s ) + %s )' % (v, P, v, P))],
                   '( ( ( Re ` %s ) + ( Re ` %s ) ) / 2 ) = ( ( ( Re ` %s ) + %s ) / 2 )' % (v, P, v, P))])
    im_ = chain(w, A, ['( Im ` %s )' % Wv, '( ( Im ` ( %s + %s ) ) / 2 )' % (v, P), '( ( ( Im ` %s ) + ( Im ` %s ) ) / 2 )' % (v, P), '( ( ( Im ` %s ) + 0 ) / 2 )' % v,
                       '( ( Im ` %s ) / 2 )' % v],
                [D(w, A, 'imdivd', [two, spc, t0], '( Im ` %s ) = ( ( Im ` ( %s + %s ) ) / 2 )' % (Wv, v, P)),
                 D(w, A, 'oveq1d', [D(w, A, 'imaddd', [vc, pc], '( Im ` ( %s + %s ) ) = ( ( Im ` %s ) + ( Im ` %s ) )' % (v, P, v, P))],
                   '( ( Im ` ( %s + %s ) ) / 2 ) = ( ( ( Im ` %s ) + ( Im ` %s ) ) / 2 )' % (v, P, v, P)),
                 D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'syl', [pr, w.inst('reim0')], '( Im ` %s ) = 0' % P)], '( ( Im ` %s ) + ( Im ` %s ) ) = ( ( Im ` %s ) + 0 )' % (v, P, v))],
                   '( ( ( Im ` %s ) + ( Im ` %s ) ) / 2 ) = ( ( ( Im ` %s ) + 0 ) / 2 )' % (v, P, v)),
                 D(w, A, 'oveq1d', [D(w, A, 'addridd', [D(w, A, 'recnd', [D(w, A, 'imcld', [vc], '( Im ` %s ) e. RR' % v)], '( Im ` %s ) e. CC' % v)], '( ( Im ` %s ) + 0 ) = ( Im ` %s )' % (v, v))],
                   '( ( ( Im ` %s ) + 0 ) / 2 ) = ( ( Im ` %s ) / 2 )' % (v, v))])
    return spc, re_, im_


def wsub(w, fn, v, val):
    """closed ( v = val -> ( fn(v) <-> fn(val) ) )"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, val, v, val))
    st, new = w.wcongr(fn(v), {}, '%s = %s' % (v, val), {}, rules={v: (val, idst)})
    assert new == fn(val), (new, fn(val))
    return st


def ta_facts(w, A, ta):
    """from ( A -> TA ): M e. NN, P e. { 0 , 1 }, C : NN --> CC, bound"""
    mp = D(w, A, 'simpld', [ta], '( M e. NN /\\ P e. { 0 , 1 } )')
    return D(w, A, 'simpld', [mp], 'M e. NN'), D(w, A, 'simprd', [mp], 'P e. { 0 , 1 }')


def hol_eq(w, A, eq, F, G, Dm):
    """( A -> ( HOL(F,Dm) <-> HOL(G,Dm) ) ) from eq: ( A -> F = G )"""
    e1 = D(w, A, 'eleq1d', [eq], '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (F, Dm, G, Dm))
    e2 = D(w, A, 'sseq2d', [D(w, A, 'dmeqd', [D(w, A, 'oveq2d', [eq], '( CC _D %s ) = ( CC _D %s )' % (F, G))], 'dom ( CC _D %s ) = dom ( CC _D %s )' % (F, G))],
           '( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) )' % (Dm, F, Dm, G))
    return D(w, A, 'anbi12d', [e1, e2], '( %s <-> %s )' % (HOL(F, Dm), HOL(G, Dm)))


