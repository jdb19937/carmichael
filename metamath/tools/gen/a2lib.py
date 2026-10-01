"""Sortie A2 helpers: the eventual calculus (E. m e. NN0 A. n e. ( ZZ>= ` m ) ...),
worksheets with $e hypotheses in deduction form, and small step patterns."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1lib                    # parser extensions (rab, prod_, sum_, decimals, InWindow)
from tm import *
import c0lib
from c0lib import runh, imp, closed, instapply
import cl, lin, num
from cl import Closure
from lin import linarith

EV = lambda P: 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % P


class WH(W):
    """worksheet with $e hypotheses in deduction form ( ph -> ... )"""
    def __init__(self, label, desc):
        W.__init__(self, label, desc)
        self.hn = 0
        self.hyps = []

    def h(self, formula, ph='ph'):
        """add a $e hypothesis ( ph -> formula ); returns its step name"""
        self.hn += 1
        name = '%d' % self.hn
        lab = '%s.%d' % (self.label, self.hn)
        self.lines.append('h%s::%s |- ( %s -> %s )' % (name, lab, ph, formula))
        self.hyps.append(name)
        return name

    def hc(self, formula):
        """add a closed $e hypothesis"""
        self.hn += 1
        name = '%d' % self.hn
        lab = '%s.%d' % (self.label, self.hn)
        self.lines.append('h%s::%s |- %s' % (name, lab, formula))
        self.hyps.append(name)
        return name

    def run(self, unify_only=False):
        if self.hyps:
            return runh(self, unify_only)
        return W.run(self, unify_only)


def evand(w, ante, steps, texts):
    """combine eventual facts pairwise with evan2; steps[i] proves
    ( ante -> E. m e. NN0 A. n e. ( ZZ>= ` m ) texts[i] ).  Returns
    (step, text) for the right-nested conjunction."""
    assert len(steps) == len(texts) >= 1
    st, tx = steps[0], texts[0]
    for s2, t2 in zip(steps[1:], texts[1:]):
        nt = '( %s /\\ %s )' % (tx, t2)
        st = w.s([st, s2], 'evan2', '( %s -> %s )' % (ante, EV(nt)))
        tx = nt
    return st, tx


def uzlei(w, ante, A, B, stA, stB, leab):
    """( ante -> ( ZZ>= ` B ) C_ ( ZZ>= ` A ) ) from A <_ B, A e. ZZ, B e. ZZ"""
    e = w.s([stA, stB, leab, w.inst('eluz2')], 'mpbir3an',
            '( %s -> %s e. ( ZZ>= ` %s ) )' % (ante, B, A))
    return w.s([e, w.inst('uzss')], 'syl', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` %s ) )' % (ante, B, A))


def sqrtle2(w, ante, X, Y, xr, x0, yr, y0, hle):
    """( ante -> ( sqrt ` X ) <_ Y ) from hle : ( ante -> X <_ ( Y ^ 2 ) )"""
    ysq = w.s([yr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (ante, Y))
    ysq0 = w.s([yr], 'sqge0d', '( %s -> 0 <_ ( %s ^ 2 ) )' % (ante, Y))
    bi = w.s([xr, x0, ysq, ysq0, w.inst('sqrtle')], 'syl22anc',
             '( %s -> ( %s <_ ( %s ^ 2 ) <-> ( sqrt ` %s ) <_ ( sqrt ` ( %s ^ 2 ) ) ) )' % (ante, X, Y, X, Y))
    st = w.s([hle, bi], 'mpbid', '( %s -> ( sqrt ` %s ) <_ ( sqrt ` ( %s ^ 2 ) ) )' % (ante, X, Y))
    eq = w.s([yr, y0, w.inst('sqrtsq')], 'syl2anc', '( %s -> ( sqrt ` ( %s ^ 2 ) ) = %s )' % (ante, Y, Y))
    return w.s([st, eq], 'breqtrd', '( %s -> ( sqrt ` %s ) <_ %s )' % (ante, X, Y))
