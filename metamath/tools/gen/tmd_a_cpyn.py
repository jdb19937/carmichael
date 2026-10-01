"""T-MD item 0: ` copyList_correct ` and ` copyList_le_B ` (~ tm2lcpyn ,
~ tm2lcpyb2 ) in the shape of ~ tm2lappn / ~ tm2lappb on ~ tm2lcpy
(template tools/gen/t6b_c_nlvl.py)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from t6b_c_nlvl import nlevel_common, bform, EL

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def cpy_n(w, ph, c, u, dk):
    eq2 = w.s([u['eq']], 'oveq1d', '( %s -> ( %s ++ R ) = %s )' % (ph, ENC('L'), LST(EL, 'R')))
    dk2 = w.s([dk, eq2], 'eqtrd', '( %s -> ( D ` K ) = %s )' % (ph, LST(EL, 'R')))
    ex = {'%s e. %s' % (EL, WWB): u['elc'], '( D ` K ) = %s' % LST(EL, 'R'): dk2, RALW(EL): u['bw']}
    bld = Builder(w, ph, c, ex)
    s1, c1 = inst(w, ph, 'tm2lcpy', {'L': EL}, bld)
    C0, D1, B1 = triple_parts(c1)
    D1x = UPDT('D', 'J', '( %s ++ ( D ` J ) )' % ENCB(EL))
    assert C0 == CL('P0', SS, 'D') and D1 == CL('E', "N'", D1x), (C0, D1)
    eqr = w.s([u['eq']], 'eqcomd', '( %s -> %s = %s )' % (ph, ENCB(EL), ENC('L')))
    st, r = w.rewrite(D1x, {ENCB(EL): (ENC('L'), eqr)}, ph)
    assert r == CFINN, r
    C2 = CL('E', "N'", CFINN)
    s2 = hrtransport(w, ph, s1, C0, D1, B1, None, C2, eqd=cleq(w, ph, 'E', "N'", D1x, CFINN, st))
    be = w.s([u['ln']], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( ( 6 x. B ) + ; 1 7 ) ) = ( %s x. ( ( 6 x. B ) + ; 1 7 ) ) )' % (ph, EL, NL))
    be2 = w.s([be], 'oveq1d', '( %s -> %s = %s )' % (ph, B1, BCPY))
    o = w.s([be2], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C2, B1, C2, BCPY))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C2, B1), HR(C0, 'T', 'M', C2, BCPY)))
    return b, s2, C0, C2


def tm2lcpyn():
    lab = 'tm2lcpyn'
    ph = PHCN
    w = W(lab, 'The fragment ` copyList ` at the N level: the list ` ( encList ` L ) ` of '
               'numbers below ` 2 ^ B ` is copied onto stack ` J ` .  Lean: ` copyList_correct ` ; '
               '~ tm2lcpy at ` ( encNatGam o. L ) ` with ~ tm2lenceq , ~ tm2lrnenc and ~ lenco .')
    c = Ctx(w, ph, T_PHCN)
    u = nlevel_common(w, ph, c)
    dk = c['( D ` K ) = ( %s ++ R )' % ENC('L')]
    b, s2, C0, C2 = cpy_n(w, ph, c, u, dk)
    w.qed([b, s2], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BCPY)))
    return w.run()


def tm2lcpyb2():
    lab = 'tm2lcpyb2'
    ph = PHCN
    w = W(lab, 'The fragment ` copyList ` within the budget ` ( ( ( # ` L ) + 1 ) x. ( TMB ` B ) ) ` . '
               'Lean: ` copyList_le_B ` ; ~ tm2lcpyn and ~ tm2llistb .')
    c = Ctx(w, ph, T_PHCN)
    phm = c[PHM]
    ll = c['L e. Word NN0']; bb = c['B e. NN0']
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    C0 = CL('P0', SS, 'D'); C2 = CL('E', "N'", CFINN)
    base = w.s([], 'tm2lcpyn', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BCPY)))
    bform(w, ph, phm, base, C0, C2, BCPY, nl, bb, '( ( 6 x. B ) + ; 1 7 )', '9')
    return w.run()


if __name__ == '__main__':
    if want('tm2lcpyn'): tm2lcpyn()
    if want('tm2lcpyb2'): tm2lcpyb2()
