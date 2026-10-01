"""T7: the shift-down loop's stack family and its step equation (blueprint
D7): ` P := ( i e. NN0 |-> UPD4( D ; I' , ( Q ` i ) ; J , ( Y ` i ) ; I , ( H ` i ) ; K , ( X ` i ) ) ) `
satisfies ` ( P ` ( N + 1 ) ) = UPD4( ( P ` N ) ; ... ( N + 1 ) ... ) ` by ~ tm2stkup8 ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from tmdlib import up8g

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

FAMB = lambda i: '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (WRD(XF(i), GK), WRD(YF(i), GJ), WRD(HF(i), GI), WRD(QF(i), GIP))


def fam_at(w, ph, fam, N):
    """the four word typings at N from fam : ( ph -> A. i e. NN0 FAMB( i ) ) and N e. NN0 (step ncl)"""
    idi = w.s([], 'id', '( i = %s -> i = %s )' % (N, N))
    cg, new = w.wcongr(FAMB('i'), {'i': N}, 'i = %s' % N, {'i': idi})
    assert new == FAMB(N)
    return cg, new


def tmcdmstp():
    lab = 'tmcdmstp'
    ph = cj(TREE_DMSTP)
    w = W(lab, 'The stack family of the shift-down loop of ` divmodCore ` (T-MD D8) and its step equation: the '
               'four updates of iteration ` N + 1 ` on top of the four of iteration ` N ` collapse by '
               '~ tm2stkup8 .  T7 instantiates ` P ` of ~ tm2fdmdq / ~ tm2fdmc2 with it.')
    c = Ctx(w, ph, TREE_DMSTP)
    tv, dd = c['T e. V'], c[STKD('D')]
    fam, ncl = c[FAM4], c['N e. NN0']
    n1cl = w.s([ncl, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    idx = {k: c['%s e. %s' % (k, DG)] for k in ['K', 'J', 'I', "I'"]}
    nkj, nki, nkip = c['K =/= J'], c['K =/= I'], c["K =/= I'"]
    nji, njip, niip = c['J =/= I'], c["J =/= I'"], c["I =/= I'"]
    def words(N):
        cg, new = fam_at(w, ph, fam, N)
        at = w.s([cg, fam, ncl if N == 'N' else n1cl], 'rspcdva', '( %s -> %s )' % (ph, new))
        l = w.s([at], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, WRD(XF(N), GK), WRD(YF(N), GJ)))
        r = w.s([at], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, WRD(HF(N), GI), WRD(QF(N), GIP)))
        return dict(X=w.s([l], 'simpld', '( %s -> %s )' % (ph, WRD(XF(N), GK))), Y=w.s([l], 'simprd', '( %s -> %s )' % (ph, WRD(YF(N), GJ))),
                    H=w.s([r], 'simpld', '( %s -> %s )' % (ph, WRD(HF(N), GI))), Q=w.s([r], 'simprd', '( %s -> %s )' % (ph, WRD(QF(N), GIP))))
    wN, wN1 = words('N'), words('( N + 1 )')
    def stkcl(N, ws):
        """UPD4( D , N ) e. Stk"""
        d1 = updcl(w, ph, 'D', "I'", QF(N), tv, dd, idx["I'"], ws['Q'])
        D1 = UP('D', "I'", QF(N))
        d2 = updcl(w, ph, D1, 'J', YF(N), tv, d1, idx['J'], ws['Y'])
        D2 = UP(D1, 'J', YF(N))
        d3 = updcl(w, ph, D2, 'I', HF(N), tv, d2, idx['I'], ws['H'])
        D3 = UP(D2, 'I', HF(N))
        return updcl(w, ph, D3, 'K', XF(N), tv, d3, idx['K'], ws['X'])
    def pval(N, ncl_, ws):
        """( PFAM ` N ) = UPD4( D , N )"""
        idi = w.s([], 'id', '( j = %s -> j = %s )' % (N, N))
        cg, new = w.congr(UPD4('D', 'j'), {'j': N}, 'j = %s' % N, {'j': idi})
        assert new == UPD4('D', N)
        cga = w.s([cg], 'adantl', '( ( %s /\\ j = %s ) -> %s = %s )' % (ph, N, UPD4('D', 'j'), UPD4('D', N)))
        da = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, PFAM, PFAM))
        ex = w.s([stkcl(N, ws)], 'elexd', '( %s -> %s e. _V )' % (ph, UPD4('D', N)))
        return w.s([da, cga, ncl_, ex], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ph, PFAM, N, UPD4('D', N)))
    pN = pval('N', ncl, wN)
    pN1 = pval('( N + 1 )', n1cl, wN1)
    # the collapse: UPD4( UPD4( D , N ) , N + 1 ) = UPD4( D , N + 1 )
    ne = {'ab': w.s([njip], 'necomd', "( %s -> I' =/= J )" % ph), 'ac': w.s([niip], 'necomd', "( %s -> I' =/= I )" % ph),
          'ad': w.s([nkip], 'necomd', "( %s -> I' =/= K )" % ph), 'bc': nji, 'bd': w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph),
          'cd': w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)}
    N1 = '( N + 1 )'
    vals = (QF('N'), QF(N1), YF('N'), YF(N1), HF('N'), HF(N1), XF('N'), XF(N1))
    wds = (wN['Q'], wN1['Q'], wN['Y'], wN1['Y'], wN['H'], wN1['H'], wN['X'], wN1['X'])
    col, RHS = up8g(w, ph, 'D', "I'", 'J', 'I', 'K', vals, tv, dd, ne, (idx["I'"], idx['J'], idx['I'], idx['K']), wds)
    assert RHS == UPD4('D', N1), (RHS, UPD4('D', N1))
    LHS = UPD4(UPD4('D', 'N'), N1)
    # UPD4( ( P ` N ) , N + 1 ) = UPD4( UPD4( D , N ) , N + 1 )
    rw, new = w.rewrite(UPD4('( %s ` N )' % PFAM, N1), {'( %s ` N )' % PFAM: (UPD4('D', 'N'), pN)}, ph)
    assert new == LHS, (new, LHS)
    e = w.s([rw, col], 'eqtrd', '( %s -> %s = %s )' % (ph, UPD4('( %s ` N )' % PFAM, N1), RHS))
    w.qed([pN1, e], 'eqtr4d', '( %s -> %s )' % (ph, CONCL_DMSTP))
    return w.run()


if __name__ == '__main__':
    if want('tmcdmstp'): tmcdmstp()
