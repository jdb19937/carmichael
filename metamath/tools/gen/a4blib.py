"""Sortie A4b helpers: the two combination patterns of the cost budget.

`scale(w, c, mre, m12, K, P, R, expr, hle, exre)` turns
    hle : ( ph -> expr <_ ( K x. ( exp ` ( P x. M ) ) ) )
into ( ph -> expr <_ ( exp ` ( R x. M ) ) ) with ( 1 / 4 ) + P <_ R and K <_ 8
(Lean AlgBudget.lean writes this with `mulE` and h2c / h4c / h5c / h7c / h8).

`emul(...)` is the application of cbemul at literal coefficients.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import num
from lin import linarith

PH = 'ph'
def A(f): return '( ph -> %s )' % f
def EXP(P): return '( exp ` ( %s x. M ) )' % P


def lit(w, c, t, kind='RR'):
    return w.s([num.fact(w, t, kind)], 'a1i', A({'RR': '%s e. RR', 'ge0': '0 <_ %s'}[kind] % t))


def scale(w, c, mre, m12, K, P, R, expr, exre, hle):
    E = EXP(P)
    ere = c.mem(E, 'RR'); e0 = c.ge0(E)
    eid = w.s([ere], 'leidd', A('%s <_ %s' % (E, E)))
    pre = lit(w, c, P); rre = lit(w, c, R); kre = lit(w, c, K); k0 = lit(w, c, K, 'ge0')
    k8 = linarith(w, PH, [], '%s <_ 8' % K, closure=c)
    pr = linarith(w, PH, [], '( ( 1 / 4 ) + %s ) <_ %s' % (P, R), closure=c)
    st = w.s([mre, m12, pre, rre, pr, kre, k0, k8, ere, e0, eid], 'cbesc',
             A('( %s x. %s ) <_ %s' % (K, E, EXP(R))))
    ke = c.mem('( %s x. %s )' % (K, E), 'RR')
    return w.s([exre, ke, c.mem(EXP(R), 'RR'), hle, st], 'letrd', A('%s <_ %s' % (expr, EXP(R))))


def emul(w, c, mre, m0, P, Q, R, X, Y, xre, x0, xb, yre, y0, yb, name=None):
    pre = lit(w, c, P); qre = lit(w, c, Q); rre = lit(w, c, R)
    pq = linarith(w, PH, [], '( %s + %s ) <_ %s' % (P, Q, R), closure=c)
    return w.s([mre, m0, pre, qre, rre, pq, xre, x0, xb, yre, y0, yb], 'cbemul',
               A('( %s x. %s ) <_ %s' % (X, Y, EXP(R))), name=name)
