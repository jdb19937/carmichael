"""T-MD: the composite ` canonNum ` of TM/Canon.lean (blueprint D3): push the
marker on the scratch stack, move the number onto it reversed (~ tm2ftr ), strip
the high zeros (~ tm2fsp ), push the terminator back, move the canonical word
back (~ tm2ftr ).  Five instances of ~ tm2hseq ; the work is the stack algebra
between the stages (T5's ~ tm2fdup is the model)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DJ, DK = '( D ` J )', '( D ` K )'
YDJ = CC(S1('Y'), DJ)


def tm2fcan():
    lab = 'tm2fcan'
    tree, ph = TREE_CAN, cj(TREE_CAN)
    w = W(lab, 'The composite ` canonNum ` of TM/Canon.lean: ` push comma s ; moveNum x s ; '
               'stripLoop s ; push comma x ; moveNum s x ` replaces the top number of stack ` K ` '
               'by its canonical form (the high zeros ` W0 ` of the reversed word stripped), '
               'restores the scratch stack ` J ` and keeps the state in ` N ` , in '
               '` ( 2 x. ( # ` W ) ) + 5 ` steps.  Lean: ` canonNum_runs ` (bound ` 3 |l| + 5 ` ); '
               'the decomposition of the reversed word is a hypothesis (blueprint D3, T7: '
               '~ bwstriprevg , ~ bwstripfst ).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, nkj = c['K e. %s' % DG], c['J e. %s' % DG], c['K =/= J']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    dd, dke = c[STKD('D')], c['( D ` K ) = %s' % WYX]
    ww, xx, w0, wp = c[WRD('W', 'B')], c[WRD('X', GK)], c[WRD('W0', 'B0')], c[WRD("W'", 'B')]
    bk, bj, b0b, gf = c['B C_ %s' % GK], c['B C_ %s' % GJ], c['B0 C_ B'], c['G : B --> B']
    yk, yj, ypj, xpj = c['Y e. %s' % GK], c['Y e. %s' % GJ], c["Y' e. %s" % GJ], c[WRD("X'", GJ)]
    dec, dec2 = c['%s = %s' % (RGW, CC('W0', "W'"))], c["( W' ++ <\" Y \"> ) = %s" % CC(S1("Y'"), "X'")]
    nss = c[SSS('N')]
    # words
    gj = w.s([gf, bj, w.inst('fss')], 'syl2anc', '( %s -> G : B --> %s )' % (ph, GJ))
    gk = w.s([gf, bk, w.inst('fss')], 'syl2anc', '( %s -> G : B --> %s )' % (ph, GK))
    gww = w.s([ww, gf, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, GW))
    rgwb = revw(w, ph, gww, GW, 'B')
    rgwj = sswordd(w, ph, rgwb, RGW, 'B', GJ, bj)
    w0b = sswordd(w, ph, w0, 'W0', 'B0', 'B', b0b)
    w0j = sswordd(w, ph, w0b, 'W0', 'B', GJ, bj)
    wpj = sswordd(w, ph, wp, "W'", 'B', GJ, bj)
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    dkw = stkfv(w, ph, 'D', 'K', tv, dd, kk)
    ysj = s1w(w, ph, yj, 'Y', GJ); ysk = s1w(w, ph, yk, 'Y', GK); ypsj = s1w(w, ph, ypj, "Y'", GJ)
    ydjw = ccatw(w, ph, ysj, djw, S1('Y'), DJ, GJ)
    yxw = ccatw(w, ph, ysk, xx, S1('Y'), 'X', GK)
    rgwydj = ccatw(w, ph, rgwj, ydjw, RGW, YDJ, GJ)
    X3 = CC("X'", DJ)
    x3w = ccatw(w, ph, xpj, djw, "X'", DJ, GJ)
    YPX3 = CC(S1("Y'"), X3)
    ypx3w = ccatw(w, ph, ypsj, x3w, S1("Y'"), X3, GJ)
    W0YPX3 = CC('W0', YPX3)
    WPYDJ = CC("W'", YDJ)
    wpydjw = ccatw(w, ph, wpj, ydjw, "W'", YDJ, GJ)
    gwpw = w.s([wp, gf, w.inst('wrdco')], 'syl2anc', "( %s -> ( G o. W' ) e. Word B )" % ph)
    rgwpb = revw(w, ph, gwpw, "( G o. W' )", 'B')
    rgwpk = sswordd(w, ph, rgwpb, RGWP, 'B', GK, bk)
    FINW = CC(RGWP, YX)
    finww = ccatw(w, ph, rgwpk, yxw, RGWP, YX, GK)
    # ---- stage 1: push Y on J at N
    D1 = UP('D', 'J', YDJ)
    d1cl = updcl(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjw)
    bld1 = bldr(w, ph, c, phm)
    s1, c1 = inst(w, ph, 'tm2fpshn', {'E': "A'", 'K': 'J', 'Z': 'Y'}, bld1)
    C0, D1c, B1 = triple_parts(c1)
    assert C0 == CLN('A', 'N', 'D') and D1c == CLN("A'", 'N', D1), (C0, D1c)
    # ---- stage 2: moveNum K -> J (tm2ftr at A := A' , E := A" , H := YDJ , D := D1)
    PRE2 = UP(UP(D1, 'K', WYX), 'J', YDJ)
    D2 = UP(UP(D1, 'K', 'X'), 'J', CC(RGW, YDJ))
    ex2 = {'%s e. %s' % (D1, STK_T): d1cl, WRD(YDJ, GJ): ydjw, 'G : B --> %s' % GJ: gj}
    bld2 = bldr(w, ph, c, phm, ex2)
    s2, c2 = inst(w, ph, 'tm2ftr', {'A': "A'", 'E': 'A"', 'H': YDJ, 'D': D1}, bld2)
    C2a, D2c, B2 = triple_parts(c2)
    assert C2a == CLN("A'", 'N', PRE2) and D2c == CLN('A"', 'N', D2), (C2a, D2c)
    # PRE2 = D1
    ydjv = elv(w, ph, ydjw, YDJ)
    d1k = updnv(w, ph, 'D', 'J', YDJ, 'K', tv, dd, jj, ydjv, kk, nkj)
    d1k2 = w.s([d1k, dke], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, WYX))
    e1 = upidv(w, ph, D1, 'K', WYX, d1k2, tv, d1cl, kk)
    d1j = updkv(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjv)
    e2 = upidv(w, ph, D1, 'J', YDJ, d1j, tv, d1cl, jj)
    g1, mid = w.rewrite(PRE2, {UP(D1, 'K', WYX): (D1, e1)}, ph)
    assert mid == UP(D1, 'J', YDJ), mid
    g2 = w.s([g1, e2], 'eqtrd', '( %s -> %s = %s )' % (ph, PRE2, D1))
    ceq2 = clneq(w, ph, "A'", 'N', w.s([g2], 'eqcomd', '( %s -> %s = %s )' % (ph, D1, PRE2)), D1, PRE2)
    s2r, _, _, _ = hrrw(w, ph, s2, C2a, D2c, B2, ceq=w.s([ceq2], 'eqcomd', '( %s -> %s = %s )' % (ph, C2a, CLN("A'", 'N', D1))))
    s12 = hrseq(w, ph, phm, s1, s2r, C0, CLN("A'", 'N', D1), D2c, B1, B2)
    N12 = '( %s + %s )' % (B1, B2)
    # ---- stage 3: the strip on J (tm2fsp at K := J , F := F' , F' := F" , C := C' , Y := Y' , X := X3 , D := D2K , A := A" , E := E')
    D2K = UP(D1, 'K', 'X')
    d2kcl = updcl(w, ph, D1, 'K', 'X', tv, d1cl, kk, xx)
    b0j = w.s([b0b, bj], 'sstrd', '( %s -> B0 C_ %s )' % (ph, GJ))
    ex3 = {'%s e. %s' % (D2K, STK_T): d2kcl, WRD(X3, GJ): x3w, 'B0 C_ %s' % GJ: b0j}
    bld3 = bldr(w, ph, c, phm, ex3)
    s3, c3 = inst(w, ph, 'tm2fsp', {'A': 'A"', 'E': "E'", 'K': 'J', 'F': "F'", "F'": 'F"', 'C': "C'", 'Y': "Y'", 'X': X3, 'D': D2K, 'W': 'W0'}, bld3)
    C3a, D3c, B3 = triple_parts(c3)
    PRE3 = UP(D2K, 'J', W0YPX3)
    D3 = UP(D2K, 'J', YPX3)
    assert C3a == CLN('A"', 'N', PRE3) and D3c == CLN("E'", 'N', D3), (C3a, D3c)
    # ( RGW ++ YDJ ) = W0YPX3
    q1 = w.s([dec], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, RGW, YDJ, CC('W0', "W'"), YDJ))
    q2 = w.s([w0j, wpj, ydjw, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ %s ) = ( W0 ++ %s ) )' % (ph, CC('W0', "W'"), YDJ, WPYDJ))
    q3 = w.s([wpj, ysj, djw, w.inst('ccatass')], 'syl3anc', "( %s -> ( ( W' ++ <\" Y \"> ) ++ %s ) = %s )" % (ph, DJ, WPYDJ))
    q4 = w.s([dec2], 'oveq1d', "( %s -> ( ( W' ++ <\" Y \"> ) ++ %s ) = ( %s ++ %s ) )" % (ph, DJ, CC(S1("Y'"), "X'"), DJ))
    q5 = w.s([ypsj, xpj, djw, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ %s ) = %s )' % (ph, CC(S1("Y'"), "X'"), DJ, YPX3))
    q6 = w.s([q3], 'eqcomd', "( %s -> %s = ( ( W' ++ <\" Y \"> ) ++ %s ) )" % (ph, WPYDJ, DJ))
    q7 = w.s([q6, w.s([q4, q5], 'eqtrd', "( %s -> ( ( W' ++ <\" Y \"> ) ++ %s ) = %s )" % (ph, DJ, YPX3))], 'eqtrd',
             '( %s -> %s = %s )' % (ph, WPYDJ, YPX3))
    q8 = w.s([q7], 'oveq2d', '( %s -> ( W0 ++ %s ) = %s )' % (ph, WPYDJ, W0YPX3))
    q9 = w.s([w.s([q1, q2], 'eqtrd', '( %s -> ( %s ++ %s ) = ( W0 ++ %s ) )' % (ph, RGW, YDJ, WPYDJ)), q8], 'eqtrd',
             '( %s -> ( %s ++ %s ) = %s )' % (ph, RGW, YDJ, W0YPX3))
    ceq3 = clneq(w, ph, 'A"', 'N', upeq(w, ph, D2K, 'J', q9, CC(RGW, YDJ), W0YPX3), D2, PRE3)
    s3r, _, _, _ = hrrw(w, ph, s3, C3a, D3c, B3, ceq=w.s([ceq3], 'eqcomd', '( %s -> %s = %s )' % (ph, C3a, D2c)))
    s123 = hrseq(w, ph, phm, s12, s3r, C0, D2c, D3c, N12, B3)
    N123 = '( %s + %s )' % (N12, B3)
    # ---- stage 4: push Y on K at N (D := D3)
    d3cl = updcl(w, ph, D2K, 'J', YPX3, tv, d2kcl, jj, ypx3w)
    ex4 = {'%s e. %s' % (D3, STK_T): d3cl}
    bld4 = bldr(w, ph, c, phm, ex4)
    s4, c4 = inst(w, ph, 'tm2fpshn', {'A': "E'", 'E': 'E"', 'Z': 'Y', 'D': D3}, bld4)
    C4a, D4c, B4 = triple_parts(c4)
    D4 = UP(D3, 'K', CC(S1('Y'), '( %s ` K )' % D3))
    assert C4a == D3c and D4c == CLN('E"', 'N', D4), (C4a, D4c)
    d3k1 = updnv(w, ph, D2K, 'J', YPX3, 'K', tv, d2kcl, jj, elv(w, ph, ypx3w, YPX3), kk, nkj)
    d3k2 = updkv(w, ph, D1, 'K', 'X', tv, d1cl, kk, elv(w, ph, xx, 'X'))
    d3k = w.s([d3k1, d3k2], 'eqtrd', '( %s -> ( %s ` K ) = X )' % (ph, D3))
    r4, D4p = w.rewrite(D4, {'( %s ` K )' % D3: ('X', d3k)}, ph)
    assert D4p == UP(D3, 'K', YX), D4p
    s4r, _, _, _ = hrrw(w, ph, s4, C4a, D4c, B4, deq=clneq(w, ph, 'E"', 'N', r4, D4, D4p))
    s1234 = hrseq(w, ph, phm, s123, s4r, C0, D3c, CLN('E"', 'N', D4p), N123, B4)
    N1234 = '( %s + %s )' % (N123, B4)
    # ---- stage 5: moveNum J -> K (tm2ftr at K := J , J := K , A := E" , W := W' , X := DJ , H := YX , D := D2K)
    PRE5 = UP(UP(D2K, 'J', WPYDJ), 'K', YX)
    POST5 = UP(UP(D2K, 'J', DJ), 'K', CC(RGWP, YX))
    ex5 = {'%s e. %s' % (D2K, STK_T): d2kcl, WRD(YX, GK): yxw, 'G : B --> %s' % GK: gk, WRD(DJ, GJ): djw, 'J =/= K': njk}
    bld5 = bldr(w, ph, c, phm, ex5)
    s5, c5 = inst(w, ph, 'tm2ftr', {'A': 'E"', 'K': 'J', 'J': 'K', 'W': "W'", 'X': DJ, 'H': YX, 'D': D2K}, bld5)
    C5a, D5c, B5 = triple_parts(c5)
    assert C5a == CLN('E"', 'N', PRE5) and D5c == CLN('E', 'N', POST5), (C5a, D5c)
    # D4p = PRE5 : D3 = UP( D2K , J , WPYDJ ) by q7
    e5 = upeq(w, ph, D2K, 'J', q7, WPYDJ, YPX3)
    e5c = w.s([e5], 'eqcomd', '( %s -> %s = %s )' % (ph, D3, UP(D2K, 'J', WPYDJ)))
    r5, pre5n = w.rewrite(D4p, {D3: (UP(D2K, 'J', WPYDJ), e5c)}, ph)
    assert pre5n == PRE5, pre5n
    ceq5 = clneq(w, ph, 'E"', 'N', r5, D4p, PRE5)
    # POST5 collapses to UP( D , K , FINW )
    u3 = up3(w, ph, 'D', 'J', YDJ, 'K', 'X', DJ, tv, dd, njk, jj, ydjw, djw, kk, xx)
    assert concl(w, ph, u3).startswith(UP(D2K, 'J', DJ) + ' = ')
    uj = upid(w, ph, 'D', 'J', tv, dd, jj)
    dkx = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)
    u2 = up2(w, ph, 'D', 'K', 'X', FINW, tv, dd, kk, xx, finww)
    tbl = {UP(D2K, 'J', DJ): (UP(UP('D', 'J', DJ), 'K', 'X'), u3), UP('D', 'J', DJ): ('D', uj),
           UP(UP('D', 'K', 'X'), 'K', FINW): (UP('D', 'K', FINW), u2)}
    ps, postn = evaluate(w, ph, POST5, {}, extra_rules=(lambda n: tbl.get(n.text())))
    FIN = UP('D', 'K', FINW)
    assert postn == FIN, (postn, FIN)
    s5r, _, _, _ = hrrw(w, ph, s5, C5a, D5c, B5, ceq=w.s([ceq5], 'eqcomd', '( %s -> %s = %s )' % (ph, C5a, CLN('E"', 'N', D4p))),
                        deq=clneq(w, ph, 'E', 'N', ps, POST5, FIN))
    tall = hrseq(w, ph, phm, s1234, s5r, C0, CLN('E"', 'N', D4p), CLN('E', 'N', FIN), N1234, B5)
    NALL = '( %s + %s )' % (N1234, B5)
    # the bound: |W0| + |W'| = |W|
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    nw0 = w.s([w0, w.inst('lencl')], 'syl', '( %s -> ( # ` W0 ) e. NN0 )' % ph)
    nwp = w.s([wp, w.inst('lencl')], 'syl', "( %s -> ( # ` W' ) e. NN0 )" % ph)
    l1 = w.s([gww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RGW, GW))
    l2 = w.s([ww, gf, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, GW))
    l3 = w.s([dec], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RGW, CC('W0', "W'")))
    l4 = w.s([w0b, wp, w.inst('ccatlen')], 'syl2anc', "( %s -> ( # ` %s ) = ( ( # ` W0 ) + ( # ` W' ) ) )" % (ph, CC('W0', "W'")))
    l5 = w.s([w.s([l3, l4], 'eqtrd', "( %s -> ( # ` %s ) = ( ( # ` W0 ) + ( # ` W' ) ) )" % (ph, RGW))], 'eqcomd',
             "( %s -> ( ( # ` W0 ) + ( # ` W' ) ) = ( # ` %s ) )" % (ph, RGW))
    l6 = w.s([l5, w.s([l1, l2], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RGW))], 'eqtrd',
             "( %s -> ( ( # ` W0 ) + ( # ` W' ) ) = ( # ` W ) )" % ph)
    bound(w, ph, phm, tall, C0, CLN('E', 'N', FIN), NALL, '( ( 2 x. ( # ` W ) ) + 5 )',
          {'( # ` W )': nw, '( # ` W0 )': nw0, "( # ` W' )": nwp}, hyps=[l6], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fcan'): tm2fcan()
