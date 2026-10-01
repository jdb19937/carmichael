"""T7b: mulC_le_B on the installation predicate ( ~ tmimulb ), the measurement
of the predicate route against the equation form ~ tmcmulb ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from t7mul import IDX5, DIST5, DATA_MB

SEL = sys.argv[1:]


def mulc_flat(P='P', E='E'):
    """tmcmulb's flat label names -> the nested labels of TMImulC at P , E"""
    fc = FRAGS['mulc']; fm = FRAGS['mul']
    lc = fc.lmap(P, E)
    Pm, Em = PL(P, 0), lc["E'"]
    lm = fm.lmap(Pm, Em)
    out = {k: lm[k] for k in fm.labels}
    out['E'] = lm['E']; out["B'"] = lm["B'"]
    ld = FRAGS['dup'].lmap(PL(Pm, fm.slot(0)), lm['Q0'])
    la = FRAGS['add'].lmap(PL(Pm, fm.slot(1)), lm['B"'])
    lk = FRAGS['can'].lmap(PL(P, 1), E)
    for k, v in ML_DUP.items():
        if k in ld: out[v] = ld[k]
    for k, v in ML_ADD.items():
        if k in la: out[v] = la[k]
    for k, v in CAN_LAB.items():
        if k in lk and k not in ('K', 'J'): out[v] = lk[k]
    return out


def STMT_MULB():
    f = FRAGS['mulc']
    tree = ((T_PHM7, f.pred()), (IDX5, DIST5), DATA_MB)
    return tree, tsub_text(CONCL_MB, mulc_flat())


def tmimulb():
    lab = 'tmimulb'
    T, C = STMT_MULB()
    ph = cj(T)
    w = W(lab, 'Lean ` mulC_le_B ` on the installation predicate: wherever ` mulC x y w s t ` is installed, '
               'the product of two encoded numbers below ` 2 ^ N ` is pushed on ` w ` in ` ( TMB ` N ) ` steps '
               '(the installed form of ~ tmcmulb ).')
    c = Ctx(w, ph, T)
    ex = unfold_all(w, ph, c[FRAGS['mulc'].pred()], 'mulc', FRAGS['mulc'].stacks, 'P', 'E')
    bld = Bld(w, ph, c, ex)
    st, c2 = inst(w, ph, 'tmcmulb', mulc_flat(), bld)
    assert c2 == C, (c2, C)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


if __name__ == '__main__':
    if 'tmimulb' in SEL: tmimulb()
