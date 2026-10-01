"""T-MD: eight updates at four distinct indices, the second four repeating the
first, collapse to four (~ tm2stkup8 ): the innermost update at ` I' ` commutes
outward past the three others (~ tm2stkupc ), is absorbed (~ tm2stkup2 ), and
~ tm2stkup6 collapses the six that remain.  The down loop of ` divmod ` uses it
at every iteration (four stacks change)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2stkup8():
    lab = 'tm2stkup8'
    tree, ph = TREE_UP8, cj(TREE_UP8)
    w = W(lab, 'Eight updates at four distinct indices, the outer four repeating the inner four, '
               'collapse to four: the innermost update at ` I\' ` commutes outward past the three '
               'others (~ tm2stkupc ), is absorbed by the outermost (~ tm2stkup2 ), and the six that '
               'remain collapse by ~ tm2stkup6 .  Every iteration of the shift-down loop of ` divmod ` '
               'changes four stacks and uses this.')
    c = Ctx(w, ph, tree)
    tv, dd = c['T e. V'], c[STKD('D')]
    nkj, nki, nkip = c['K =/= J'], c['K =/= I'], c["K =/= I'"]
    nji, njip, niip = c['J =/= I'], c["J =/= I'"], c["I =/= I'"]
    kk, jj, ii, ip = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG], c["I' e. %s" % DG]
    yw, ypw, zw, zpw = c[WRD('Y', GK)], c[WRD("Y'", GK)], c[WRD('Z', GJ)], c[WRD("Z'", GJ)]
    nw, npw, ow, opw = c[WRD('N', GI)], c[WRD("N'", GI)], c[WRD('O', GIP)], c[WRD("O'", GIP)]
    D3 = UP3('D', 'K', 'Y', 'J', 'Z', 'I', 'N')
    d1 = updcl(w, ph, 'D', 'K', 'Y', tv, dd, kk, yw)
    d2 = updcl(w, ph, UP('D', 'K', 'Y'), 'J', 'Z', tv, d1, jj, zw)
    d3 = updcl(w, ph, UP(UP('D', 'K', 'Y'), 'J', 'Z'), 'I', 'N', tv, d2, ii, nw)
    D4 = UP(D3, "I'", 'O')
    d4 = updcl(w, ph, D3, "I'", 'O', tv, d3, ip, ow)
    D5 = UP(D4, 'K', "Y'")
    d5 = updcl(w, ph, D4, 'K', "Y'", tv, d4, kk, ypw)
    D6 = UP(D5, 'J', "Z'")
    d6 = updcl(w, ph, D5, 'J', "Z'", tv, d5, jj, zpw)
    LHS = UP(UP(D6, 'I', "N'"), "I'", "O'")
    # commute I' outward: UP( UP( D3 , I' , O ) , K , Y' ) = UP( UP( D3 , K , Y' ) , I' , O )
    c1 = upc(w, ph, D3, "I'", 'O', 'K', "Y'", tv, d3, w.s([nkip], 'necomd', "( %s -> I' =/= K )" % ph), ip, ow, kk, ypw)
    E5 = UP(UP(D3, 'K', "Y'"), "I'", 'O')
    e5 = updcl(w, ph, UP(D3, 'K', "Y'"), "I'", 'O', tv, updcl(w, ph, D3, 'K', "Y'", tv, d3, kk, ypw), ip, ow)
    c2 = upc(w, ph, UP(D3, 'K', "Y'"), "I'", 'O', 'J', "Z'", tv, updcl(w, ph, D3, 'K', "Y'", tv, d3, kk, ypw), w.s([njip], 'necomd', "( %s -> I' =/= J )" % ph), ip, ow, jj, zpw)
    E6b = UP(UP(D3, 'K', "Y'"), 'J', "Z'")
    e6b = updcl(w, ph, UP(D3, 'K', "Y'"), 'J', "Z'", tv, updcl(w, ph, D3, 'K', "Y'", tv, d3, kk, ypw), jj, zpw)
    c3 = upc(w, ph, E6b, "I'", 'O', 'I', "N'", tv, e6b, w.s([niip], 'necomd', "( %s -> I' =/= I )" % ph), ip, ow, ii, npw)
    E7 = UP(E6b, 'I', "N'")
    e7 = updcl(w, ph, E6b, 'I', "N'", tv, e6b, ii, npw)
    c4 = up2(w, ph, E7, "I'", 'O', "O'", tv, e7, ip, ow, opw)
    # tm2stkup6 on the inner six
    c6, RHS6 = up6(w, ph, 'D', 'Y', "Y'", 'Z', "Z'", 'N', "N'", tv, dd, nkj, nki, nji, kk, jj, ii, yw, ypw, zw, zpw, nw, npw)
    tbl = {D5: (E5, c1), UP(E5, 'J', "Z'"): (UP(E6b, "I'", 'O'), c2), UP(UP(E6b, "I'", 'O'), 'I', "N'"): (UP(E7, "I'", 'O'), c3),
           UP(UP(E7, "I'", 'O'), "I'", "O'"): (UP(E7, "I'", "O'"), c4), E7: (RHS6, c6)}
    ps, res = evaluate(w, ph, LHS, {}, extra_rules=(lambda n: tbl.get(n.text())))
    RHS = UP(RHS6, "I'", "O'")
    assert res == RHS, (res, RHS)
    w.qed([ps], 'id', '( %s -> %s = %s )' % (ph, LHS, RHS)) if False else None
    # ps proves ( ph -> LHS = RHS ) already; restate as qed
    w.lines.append('qed:%s:idi |- ( %s -> %s = %s )' % (ps, ph, LHS, RHS))
    return w.run()


if __name__ == '__main__':
    if want('tm2stkup8'): tm2stkup8()
