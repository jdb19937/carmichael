"""T7: the multiplication at the machine.  ` tmcmltr ` : the per-iteration
composite ` dup x t s ; add w t s w ` of Lean's ` mulBody ` (its true branch)
as one triple, by ~ tmcdup then ~ tmcaddx and the stack collapse."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN, LN2 = '( # ` L )', "( # ` L' )"
IBL, IBL2 = '( inclBool o. L )', "( inclBool o. L' )"


def tmcmltr():
    lab = 'tmcmltr'
    TREE = TREE_MLTR()
    ph = cj(TREE)
    w = W(lab, 'One set-bit iteration of the multiplication at the machine (Lean ` mulBody ` , the ` ite ` \'s true '
               'branch): ` dup x t s ` copies the shifted multiplicand onto ` t ` (~ tmcdup ), ` add w t s w ` adds it '
               'into the accumulator in place (~ tmcaddx ); ` t ` and ` s ` are restored, so the composite updates '
               'the accumulator\'s stack only.')
    c = Ctx(w, ph, TREE)
    mk = machine(w, ph, c, ['K', 'I', "I'", 'I"'])
    tv, dd = mk['tv'], c[STKD('D')]
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    xg, yg = c[WRD('X', GAM)], c[WRD('Y', GAM)]
    dk, di = c[DATA_MLTR[1][0]], c[DATA_MLTR[1][1]]
    K = lambda k: mk['k'][k]
    # ---- dup at K , I" , I'
    ibw2 = w.s([ll2, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IBL2, BITS))
    mdup = dict(ML_DUP); mdup.update({'W': IBL2, 'X': 'X', 'D': 'D'})
    base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
    extra = dict(base); extra[WRD(IBL2, BITS)] = ibw2
    bld = Builder(w, ph, c, extra)
    t1, c1 = inst(w, ph, 'tmcdup', mdup, bld)
    C1, D1, n1 = triple_parts(c1)
    DI2 = '( D ` I" )'
    W1 = CC(IBL2, CC(S1('4'), DI2))
    DD1 = UP('D', 'I"', W1)
    assert D1 == CLN('Q0', SS, DD1), D1
    # ---- add at I , I" , I' on the stacks DD1
    di2g = w.s([w.s([tv, dd, K('I"')['kd'], w.inst('tm2stkfv')], 'syl3anc', '( %s -> %s e. Word %s )' % (ph, DI2, GX('I"'))), K('I"')['wge']], 'eleqtrd',
               "( %s -> %s e. Word Gamma' )" % (ph, DI2))
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ss = closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS)
    ssw = w.s([ss, w.inst('sswrd')], 'syl', "( %s -> Word %s C_ Word Gamma' )" % (ph, BITS))
    ibg2 = w.s([ssw, ibw2], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, IBL2))
    w1g = w.s([ibg2, w.s([s4, di2g, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, CC(S1('4'), DI2))), w.inst('ccatcl')], 'syl2anc',
              "( %s -> %s e. Word Gamma' )" % (ph, W1))
    w1k = w.s([w1g, K('I"')['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, W1, GX('I"')))
    dd1 = updcl(w, ph, 'D', 'I"', W1, tv, dd, K('I"')['kd'], w1k)
    ne_ii = c['I =/= I"']
    d1i = updnv(w, ph, 'D', 'I"', W1, 'I', tv, dd, K('I"')['kd'], w.s([w1g], 'elexd', '( %s -> %s e. _V )' % (ph, W1)), K('I')['kd'], ne_ii)
    d1i2 = w.s([d1i, di], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ++ ( <" 4 "> ++ Y ) ) )' % (ph, DD1, IBL))
    d1t = updkv(w, ph, 'D', 'I"', W1, tv, dd, K('I"')['kd'], w.s([w1g], 'elexd', '( %s -> %s e. _V )' % (ph, W1)))
    madd = dict(ML_ADD); madd.update({'L': 'L', "L'": "L'", 'X': 'Y', 'Y': DI2, 'D': DD1})
    extra2 = dict(base)
    extra2.update({STKD(DD1): dd1, WRD(DI2, GAM): di2g, '( %s ` I ) = ( %s ++ ( <" 4 "> ++ Y ) )' % (DD1, IBL): d1i2,
              '( %s ` I" ) = ( %s ++ ( <" 4 "> ++ %s ) )' % (DD1, IBL2, DI2): d1t})
    bld2 = Builder(w, ph, c, extra2)
    t2, c2 = inst(w, ph, 'tmcaddx', madd, bld2)
    C2, D2, n2 = triple_parts(c2)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, mk['phm'], t1, t2, C1, D1, D2, n1, n2)
    # ---- the stacks: UPD( UPD( UPD( D , I" , W1 ) , I , B ) , I" , ( D ` I" ) ) = UPD( D , I , B )
    B = CC(WA, '( <" 4 "> ++ Y )')
    POST = UP(UP(DD1, 'I', B), 'I"', DI2)
    assert D2 == CLN('B"', SS, POST), D2
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    AB = "( ( L addBits L' ) ` (/) )"
    abw = w.s([ll, ll2, b0, w.inst('addbitscl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, AB))
    wab = w.s([abw, closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS), w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, WA, BITS))
    wag = w.s([ssw, wab], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, WA))
    bg = w.s([wag, w.s([s4, yg, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ Y ) e. Word Gamma' )" % ph), w.inst('ccatcl')], 'syl2anc',
             "( %s -> %s e. Word Gamma' )" % (ph, B))
    bk = w.s([bg, K('I')['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, B, GX('I')))
    dik = w.s([di2g, K('I"')['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, DI2, GX('I"')))
    ne_ti = w.s([ne_ii], 'necomd', '( %s -> I" =/= I )' % ph)
    u3 = up3(w, ph, 'D', 'I"', W1, 'I', B, DI2, tv, dd, ne_ti, K('I"')['kd'], w1k, dik, K('I')['kd'], bk)
    ui = upid(w, ph, 'D', 'I"', tv, dd, K('I"')['kd'])
    r, newp = w.rewrite(UP(UP('D', 'I"', DI2), 'I', B), {UP('D', 'I"', DI2): ('D', ui)}, ph)
    assert newp == UP('D', 'I', B), newp
    deq0 = w.s([u3, r], 'eqtrd', '( %s -> %s = %s )' % (ph, POST, UP('D', 'I', B)))
    deq = clneq(w, ph, 'B"', SS, deq0, POST, UP('D', 'I', B))
    # ---- the bound: |W| = |L'|
    bl = w.s([ll2, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, IBL2, LN2))
    e1 = w.s([w.s([bl], 'oveq2d', '( %s -> ( 2 x. ( # ` %s ) ) = ( 2 x. %s ) )' % (ph, IBL2, LN2))], 'oveq1d',
             '( %s -> ( ( 2 x. ( # ` %s ) ) + 5 ) = ( ( 2 x. %s ) + 5 ) )' % (ph, IBL2, LN2))
    NN = '( %s + %s )' % (n1, n2)
    neq = w.s([e1], 'oveq1d', '( %s -> %s = %s )' % (ph, NN, BND_MLTR))
    t3, C3, D3, n3 = hrrw(w, ph, t12, C1, D2, NN, deq=deq, neq=neq, qed=True)
    assert TRI(C3, D3, n3) == CONCL_MLTR, (TRI(C3, D3, n3), CONCL_MLTR)
    return w.run()


if __name__ == '__main__':
    if want('tmcmltr'): tmcmltr()
