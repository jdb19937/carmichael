"""T7b: the installed -> runs corollaries of the leaf wrappers: the wrapper's
program equations and label typings replaced by the installation predicate.
Usage: MM_DB=sorties/t7b.mm python3 tools/gen/t7b_c_runs.py LABEL...
(LABEL = tmidup, tmidupb, ... see RUNS)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from t7mul import CONCL_CANS
from t7leb import (TREE_DUPB, CONCL_DUPB, TREE_DROPB, CONCL_DROPB, TREE_IZB, CONCL_IZB, TREE_INCB, CONCL_INCB,
                   TREE_PRDB, CONCL_PRDB, TREE_CMPB, CONCL_CMPB)

SEL = sys.argv[1:]

# label -> (fragment, wrapper, wrapper tree, wrapper conclusion, description)
RUNS = {
    'tmidup': ('dup', 'tmcdup', TREE_DUP, CONCL_DUP),
    'tmidupb': ('dup', 'tmcdupb', TREE_DUPB, CONCL_DUPB),
    'tmidrop': ('drop', 'tmcdrop', TREE_DROP, CONCL_DROP),
    'tmidropb': ('drop', 'tmcdropb', TREE_DROPB, CONCL_DROPB),
    'tmiiz': ('iz', 'tmciz', TREE_IZ, CONCL_IZ),
    'tmiizb': ('iz', 'tmcizb', TREE_IZB, CONCL_IZB),
    'tmicmp': ('cmp', 'tmccmp', TREE_CMP(), CONCL_CMP),
    'tmicmpb': ('cmp', 'tmccmpb', TREE_CMPB, CONCL_CMPB),
    'tmisub': ('sub', 'tmcsubx', TREE_SUBX(), CONCL_SUBX),
    'tmiinc': ('inc', 'tmcincr', TREE_INC, CONCL_INC),
    'tmiincb': ('inc', 'tmcincb', TREE_INCB, CONCL_INCB),
    'tmiprd': ('prd', 'tmcprdn', TREE_PRD, CONCL_PRD),
    'tmiprdb': ('prd', 'tmcprdb', TREE_PRDB, CONCL_PRDB),
    'tmican': ('can', 'tmccan', TREE_CAN, CONCL_CAN),
    'tmicanb': ('can', 'tmccanb', TREE_CANB, CONCL_CANB),
    'tmiadd': ('add', 'tmcaddx', TREE_ADDX(), CONCL_ADDX),
    'tmicans': ('can', 'tmccans', TREE_CAN, CONCL_CANS),
}


def pred_tree(tree, f):
    """the wrapper's antecedent tree with the program replaced by the
    predicate and the label typings removed, labels renamed by f.lmap()"""
    def go(t):
        if t == f.prog or (not isinstance(t, str) and cj(t) == cj(f.prog)):
            return '@PRED@'
        if t == f.labs or (not isinstance(t, str) and cj(t) == cj(f.labs)):
            return None
        if isinstance(t, str):
            assert not t.startswith('( M ` '), t
            return t
        kids = [go(x) for x in t]
        kids = [k for k in kids if k is not None]
        if len(kids) == 1:
            return kids[0]
        return tuple(kids)
    m = f.lmap()
    t = tsub(go(tree), m)
    def put(x):
        if isinstance(x, str):
            return f.pred() if x == '@PRED@' else x
        return tuple(put(y) for y in x)
    return put(t)


def runs_stmt(lab):
    fn, wr, tree, concl = RUNS[lab]
    f = FRAGS[fn]
    return pred_tree(tree, f), tsub_text(concl, f.lmap())


def runs(lab):
    fn, wr, tree, concl = RUNS[lab]
    f = FRAGS[fn]
    T, C = runs_stmt(lab)
    ph = cj(T)
    w = W(lab, 'The installed form of ~ %s : Lean\'s ` %s ` runs wherever the fragment is installed '
               '(the program equations and label typings are the installation predicate\'s).' % (wr, f.name))
    c = Ctx(w, ph, T)
    pst = c[f.pred()]
    d = w.s([], 'df-%s' % f.const.lower(), f.df())
    u = w.s([pst, d], 'sylib', '( %s -> %s )' % (ph, f.rhs()))
    cu = Ctx(w, ph, f.rhs_tree(), root=u)
    bld = Bld(w, ph, c, cu.all())
    st, c2 = inst(w, ph, wr, f.lmap(), bld)
    assert c2 == C, (c2, C)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        runs(l)
