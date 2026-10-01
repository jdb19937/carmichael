"""Sortie CEN1: the real-part expansion of A |1 + sum V|^2 (cenexp; Lean Census mul_conj_expand)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen1lib import *
from lin import lineq
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_exp():
    w = W('cenexp', 'The expansion of ` A | 1 + sum_J V | ^ 2 ` for real ` A ` into its constant, linear, diagonal and off-diagonal real parts (Lean Census ` mul_conj_expand ` , used in real parts).')
    h = {}
    for i in range(1, 5):
        h[i] = w.s([], 'cenexp.%d' % i, S['cenexp.%d' % i], name='h%d' % i)
    P0 = 'ph'; P1 = '( ph /\\ j e. J )'; PL = '( ph /\\ l e. J )'
    P1D = '( %s /\\ l e. ( J \\ { j } ) )' % P1; P1L = '( %s /\\ l e. J )' % P1
    def s(ctx, hh, r, f):
        return w.s(hh, r, '( %s -> %s )' % (ctx, f))
    ar = h[4]; ac = s(P0, [ar], 'recnd', 'A e. CC')
    SV = 'sum_ j e. J V'; CS = '( * ` %s )' % SV; CSW = 'sum_ l e. J ( * ` W )'
    svc = s(P0, [h[1], h[2]], 'fsumcl', '%s e. CC' % SV)
    csc = s(P0, [svc], 'cjcld', '%s e. CC' % CS)
    # W e. CC for l e. J
    ral = s(P0, [h[2]], 'ralrimiva', 'A. j e. J V e. CC')
    e3 = w.s([h[3]], 'eleq1d', '( j = l -> ( V e. CC <-> W e. CC ) )')
    rw = w.s([e3], 'rspcv', '( l e. J -> ( A. j e. J V e. CC -> W e. CC ) )')
    wcl = s(PL, [s(PL, [], 'simpr', 'l e. J'), s(PL, [s(PL, [], 'simpl', 'ph'), ral], 'syl', 'A. j e. J V e. CC'), rw], 'sylc', 'W e. CC')
    def wc_in(ctx, lin_st):
        ph_ = s(ctx, [], 'simpll', 'ph')
        return s(ctx, [ph_, lin_st, wcl], 'syl2anc', 'W e. CC')
    # conj of the sum as a sum over l
    c1 = s(P0, [h[1], h[2]], 'fsumcj', '%s = sum_ j e. J ( * ` V )' % CS)
    c2 = w.s([w.s([h[3]], 'fveq2d', '( j = l -> ( * ` V ) = ( * ` W ) )')], 'cbvsumv', 'sum_ j e. J ( * ` V ) = %s' % CSW)
    c3 = s(P0, [c1, s(P0, [c2], 'a1i', 'sum_ j e. J ( * ` V ) = %s' % CSW)], 'eqtrd', '%s = %s' % (CS, CSW))
    # ---- per j ------------------------------------------------------------------
    vc = h[2]
    fin1 = s(P1, [s(P1, [], 'simpl', 'ph'), h[1]], 'syl', 'J e. Fin')
    ac1 = s(P1, [s(P1, [], 'simpl', 'ph'), ac], 'syl', 'A e. CC')
    ar1 = s(P1, [s(P1, [], 'simpl', 'ph'), ar], 'syl', 'A e. RR')
    wl = wc_in(P1L, s(P1L, [], 'simpr', 'l e. J'))
    cwl = s(P1L, [wl], 'cjcld', '( * ` W ) e. CC')
    vl = s(P1L, [s(P1L, [], 'simpl', P1), vc], 'syl', 'V e. CC')
    B = '( V x. ( * ` W ) )'; D = '( V x. ( * ` V ) )'
    bcl = s(P1L, [vl, cwl], 'mulcld', '%s e. CC' % B)
    x1 = s(P1, [s(P1, [s(P1, [s(P1, [], 'simpl', 'ph'), c3], 'syl', '%s = %s' % (CS, CSW))], 'oveq2d', '( V x. %s ) = ( V x. %s )' % (CS, CSW))], 'oveq2d',
           '( A x. ( V x. %s ) ) = ( A x. ( V x. %s ) )' % (CS, CSW))
    x2 = s(P1, [fin1, vc, cwl], 'fsummulc2', '( V x. %s ) = sum_ l e. J %s' % (CSW, B))
    bd0 = w.s([h[3]], 'equcoms', '( l = j -> V = W )')
    bd = w.s([w.s([w.s([bd0], 'eqcomd', '( l = j -> W = V )')], 'fveq2d', '( l = j -> ( * ` W ) = ( * ` V ) )')], 'oveq2d', '( l = j -> %s = %s )' % (B, D))
    SD = 'sum_ l e. ( J \\ { j } ) %s' % B
    x3 = s(P1, [w.s([], 'nfv', 'F/ l %s' % P1), w.s([], 'nfcv', 'F/_ l %s' % D), fin1, bcl, s(P1, [], 'simpr', 'j e. J'), bd], 'fsumsplit1', 'sum_ l e. J %s = ( %s + %s )' % (B, D, SD))
    dc = s(P1, [vc, s(P1, [vc], 'cjcld', '( * ` V ) e. CC')], 'mulcld', '%s e. CC' % D)
    find = s(P1, [fin1, w.inst('diffi')], 'syl', '( J \\ { j } ) e. Fin')
    ldj = s(P1D, [s(P1D, [], 'simpr', 'l e. ( J \\ { j } )'), w.inst('eldifi')], 'syl', 'l e. J')
    wd = wc_in(P1D, ldj)
    bcd = s(P1D, [s(P1D, [s(P1D, [], 'simpl', P1), vc], 'syl', 'V e. CC'), s(P1D, [wd], 'cjcld', '( * ` W ) e. CC')], 'mulcld', '%s e. CC' % B)
    sdc = s(P1, [find, bcd], 'fsumcl', '%s e. CC' % SD)
    x23 = s(P1, [x2, x3], 'eqtrd', '( V x. %s ) = ( %s + %s )' % (CSW, D, SD))
    x4 = s(P1, [s(P1, [x23], 'oveq2d', '( A x. ( V x. %s ) ) = ( A x. ( %s + %s ) )' % (CSW, D, SD)), s(P1, [ac1, dc, sdc], 'adddid', '( A x. ( %s + %s ) ) = ( ( A x. %s ) + ( A x. %s ) )' % (D, SD, D, SD))],
           'eqtrd', '( A x. ( V x. %s ) ) = ( ( A x. %s ) + ( A x. %s ) )' % (CSW, D, SD))
    AB = '( A x. %s )' % B
    SAD = 'sum_ l e. ( J \\ { j } ) %s' % AB
    x5 = s(P1, [find, ac1, bcd], 'fsummulc2', '( A x. %s ) = %s' % (SD, SAD))
    abd = s(P1D, [s(P1D, [s(P1D, [], 'simpl', P1), ac1], 'syl', 'A e. CC'), bcd], 'mulcld', '%s e. CC' % AB)
    RSAD = 'sum_ l e. ( J \\ { j } ) ( Re ` %s )' % AB
    x6 = s(P1, [find, abd], 'fsumre', '( Re ` %s ) = %s' % (SAD, RSAD))
    V2 = '( ( abs ` V ) ^ 2 )'
    avs = s(P1, [vc, w.inst('absvalsq')], 'syl', '%s = %s' % (V2, D))
    av2r = s(P1, [s(P1, [vc], 'abscld', '( abs ` V ) e. RR')], 'resqcld', '%s e. RR' % V2)
    x7a = s(P1, [avs], 'oveq2d', '( A x. %s ) = ( A x. %s )' % (V2, D))
    x7r = s(P1, [ar1, av2r], 'remulcld', '( A x. %s ) e. RR' % V2)
    x7 = s(P1, [s(P1, [x7a], 'fveq2d', '( Re ` ( A x. %s ) ) = ( Re ` ( A x. %s ) )' % (V2, D)), s(P1, [x7r], 'rered', '( Re ` ( A x. %s ) ) = ( A x. %s )' % (V2, V2))],
           'eqtr3d', '( Re ` ( A x. %s ) ) = ( A x. %s )' % (D, V2))
    X8L = '( A x. ( V x. %s ) )' % CSW
    x8 = x4
    x8b = s(P1, [x8, s(P1, [x5], 'oveq2d', '( ( A x. %s ) + ( A x. %s ) ) = ( ( A x. %s ) + %s )' % (D, SD, D, SAD))], 'eqtrd', '%s = ( ( A x. %s ) + %s )' % (X8L, D, SAD))
    adc = s(P1, [ac1, dc], 'mulcld', '( A x. %s ) e. CC' % D)
    sadc = s(P1, [find, abd], 'fsumcl', '%s e. CC' % SAD)
    x9 = s(P1, [s(P1, [x8b], 'fveq2d', '( Re ` %s ) = ( Re ` ( ( A x. %s ) + %s ) )' % (X8L, D, SAD)), s(P1, [adc, sadc], 'readdd', '( Re ` ( ( A x. %s ) + %s ) ) = ( ( Re ` ( A x. %s ) ) + ( Re ` %s ) )' % (D, SAD, D, SAD))],
           'eqtrd', '( Re ` %s ) = ( ( Re ` ( A x. %s ) ) + ( Re ` %s ) )' % (X8L, D, SAD))
    PERJ = '( ( A x. %s ) + %s )' % (V2, RSAD)
    x10 = s(P1, [x9, s(P1, [x7, x6], 'oveq12d', '( ( Re ` ( A x. %s ) ) + ( Re ` %s ) ) = %s' % (D, SAD, PERJ))], 'eqtrd', '( Re ` %s ) = %s' % (X8L, PERJ))
    # ---- outer ---------------------------------------------------------------------
    cswc = s(P0, [c3, csc], 'eqeltrrd', '%s e. CC' % CSW)
    y0 = s(P0, [s(P0, [c3], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (SV, CS, SV, CSW))], 'oveq2d', '( A x. ( %s x. %s ) ) = ( A x. ( %s x. %s ) )' % (SV, CS, SV, CSW))
    y1 = s(P0, [h[1], cswc, h[2]], 'fsummulc1', '( %s x. %s ) = sum_ j e. J ( V x. %s )' % (SV, CSW, CSW))
    vcs = s(P1, [vc, s(P1, [s(P1, [], 'simpl', 'ph'), cswc], 'syl', '%s e. CC' % CSW)], 'mulcld', '( V x. %s ) e. CC' % CSW)
    SX8 = 'sum_ j e. J %s' % X8L
    y2 = s(P0, [h[1], ac, vcs], 'fsummulc2', '( A x. sum_ j e. J ( V x. %s ) ) = %s' % (CSW, SX8))
    y12 = s(P0, [y0, s(P0, [s(P0, [y1], 'oveq2d', '( A x. ( %s x. %s ) ) = ( A x. sum_ j e. J ( V x. %s ) )' % (SV, CSW, CSW)), y2], 'eqtrd', '( A x. ( %s x. %s ) ) = %s' % (SV, CSW, SX8))],
              'eqtrd', '( A x. ( %s x. %s ) ) = %s' % (SV, CS, SX8))
    x8c = s(P1, [ac1, vcs], 'mulcld', '%s e. CC' % X8L)
    y3 = s(P0, [h[1], x8c], 'fsumre', '( Re ` %s ) = sum_ j e. J ( Re ` %s )' % (SX8, X8L))
    y4 = s(P0, [x10], 'sumeq2dv', 'sum_ j e. J ( Re ` %s ) = sum_ j e. J %s' % (X8L, PERJ))
    SAV2 = 'sum_ j e. J ( A x. %s )' % V2
    SS2 = 'sum_ j e. J %s' % RSAD
    rsadr = s(P1, [find, s(P1D, [abd], 'recld', '( Re ` %s ) e. RR' % AB)], 'fsumrecl', '%s e. RR' % RSAD)
    y5 = s(P0, [h[1], s(P1, [x7r], 'recnd', '( A x. %s ) e. CC' % V2), s(P1, [rsadr], 'recnd', '%s e. CC' % RSAD)], 'fsumadd', 'sum_ j e. J %s = ( %s + %s )' % (PERJ, SAV2, SS2))
    YR = '( Re ` ( A x. ( %s x. %s ) ) )' % (SV, CS)
    y6 = s(P0, [s(P0, [y12], 'fveq2d', '%s = ( Re ` %s )' % (YR, SX8)), y3, y4, y5], 'x', 'x') if False else None
    y6a = s(P0, [s(P0, [y12], 'fveq2d', '%s = ( Re ` %s )' % (YR, SX8)), y3], 'eqtrd', '%s = sum_ j e. J ( Re ` %s )' % (YR, X8L))
    y6 = s(P0, [s(P0, [y6a, y4], 'eqtrd', '%s = sum_ j e. J %s' % (YR, PERJ)), y5], 'eqtrd', '%s = ( %s + %s )' % (YR, SAV2, SS2))
    # ---- the square ------------------------------------------------------------------
    P = '( 1 + %s )' % SV
    pc = s(P0, [s(P0, [], '1cnd', '1 e. CC'), svc], 'addcld', '%s e. CC' % P)
    P2 = '( ( abs ` %s ) ^ 2 )' % P
    z0 = s(P0, [pc, w.inst('absvalsq')], 'syl', '%s = ( %s x. ( * ` %s ) )' % (P2, P, P))
    cp = s(P0, [s(P0, [s(P0, [], '1cnd', '1 e. CC'), svc], 'cjaddd', '( * ` %s ) = ( ( * ` 1 ) + %s )' % (P, CS)), s(P0, [s(P0, [s(P0, [], '1red', '1 e. RR')], 'cjred', '( * ` 1 ) = 1')], 'oveq1d', '( ( * ` 1 ) + %s ) = ( 1 + %s )' % (CS, CS))],
           'eqtrd', '( * ` %s ) = ( 1 + %s )' % (P, CS))
    z1 = s(P0, [z0, s(P0, [cp], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. ( 1 + %s ) )' % (P, P, P, CS))], 'eqtrd', '%s = ( %s x. ( 1 + %s ) )' % (P2, P, CS))
    RHS = '( ( ( A + ( A x. %s ) ) + ( A x. %s ) ) + ( A x. ( %s x. %s ) ) )' % (SV, CS, SV, CS)
    cd = Closure(w, P0, {'A': ('CC', ac), SV: ('CC', svc), CS: ('CC', csc)})
    cd.atom(SV); cd.atom(CS)
    z2 = ringeq(w, P0, '( A x. ( %s x. ( 1 + %s ) ) )' % (P, CS), RHS, cd)
    z3 = s(P0, [s(P0, [z1], 'oveq2d', '( A x. %s ) = ( A x. ( %s x. ( 1 + %s ) ) )' % (P2, P, CS)), z2], 'eqtrd', '( A x. %s ) = %s' % (P2, RHS))
    lhr = s(P0, [ar, s(P0, [s(P0, [pc], 'abscld', '( abs ` %s ) e. RR' % P)], 'resqcld', '%s e. RR' % P2)], 'remulcld', '( A x. %s ) e. RR' % P2)
    z4 = s(P0, [s(P0, [s(P0, [lhr], 'rered', '( Re ` ( A x. %s ) ) = ( A x. %s )' % (P2, P2))], 'eqcomd', '( A x. %s ) = ( Re ` ( A x. %s ) )' % (P2, P2)),
                s(P0, [z3], 'fveq2d', '( Re ` ( A x. %s ) ) = ( Re ` %s )' % (P2, RHS))], 'eqtrd', '( A x. %s ) = ( Re ` %s )' % (P2, RHS))
    asv = s(P0, [ac, svc], 'mulcld', '( A x. %s ) e. CC' % SV)
    acs = s(P0, [ac, csc], 'mulcld', '( A x. %s ) e. CC' % CS)
    ass = s(P0, [ac, s(P0, [svc, csc], 'mulcld', '( %s x. %s ) e. CC' % (SV, CS))], 'mulcld', '( A x. ( %s x. %s ) ) e. CC' % (SV, CS))
    R1 = '( A + ( A x. %s ) )' % SV
    R2 = '( %s + ( A x. %s ) )' % (R1, CS)
    r1c = s(P0, [ac, asv], 'addcld', '%s e. CC' % R1)
    r2c = s(P0, [r1c, acs], 'addcld', '%s e. CC' % R2)
    z5 = s(P0, [r2c, ass], 'readdd', '( Re ` %s ) = ( ( Re ` %s ) + %s )' % (RHS, R2, YR))
    z6 = s(P0, [r1c, acs], 'readdd', '( Re ` %s ) = ( ( Re ` %s ) + ( Re ` ( A x. %s ) ) )' % (R2, R1, CS))
    z7 = s(P0, [ac, asv], 'readdd', '( Re ` %s ) = ( ( Re ` A ) + ( Re ` ( A x. %s ) ) )' % (R1, SV))
    z8 = s(P0, [ar], 'rered', '( Re ` A ) = A')
    # Re ( A Sv ) = sum Re ( A V )
    SAV = 'sum_ j e. J ( A x. V )'
    avc = s(P1, [ac1, vc], 'mulcld', '( A x. V ) e. CC')
    z9 = s(P0, [h[1], ac, vc], 'fsummulc2', '( A x. %s ) = %s' % (SV, SAV))
    SRAV = 'sum_ j e. J ( Re ` ( A x. V ) )'
    z10 = s(P0, [s(P0, [z9], 'fveq2d', '( Re ` ( A x. %s ) ) = ( Re ` %s )' % (SV, SAV)), s(P0, [h[1], avc], 'fsumre', '( Re ` %s ) = %s' % (SAV, SRAV))], 'eqtrd', '( Re ` ( A x. %s ) ) = %s' % (SV, SRAV))
    # Re ( A conj Sv ) = Re ( A Sv )
    z11 = s(P0, [ac, svc], 'cjmuld', '( * ` ( A x. %s ) ) = ( ( * ` A ) x. %s )' % (SV, CS))
    z12 = s(P0, [z11, s(P0, [s(P0, [ar], 'cjred', '( * ` A ) = A')], 'oveq1d', '( ( * ` A ) x. %s ) = ( A x. %s )' % (CS, CS))], 'eqtrd', '( * ` ( A x. %s ) ) = ( A x. %s )' % (SV, CS))
    z13 = s(P0, [s(P0, [z12], 'fveq2d', '( Re ` ( * ` ( A x. %s ) ) ) = ( Re ` ( A x. %s ) )' % (SV, CS)), s(P0, [asv], 'recjd', '( Re ` ( * ` ( A x. %s ) ) ) = ( Re ` ( A x. %s ) )' % (SV, SV))],
            'eqtr3d', '( Re ` ( A x. %s ) ) = ( Re ` ( A x. %s ) )' % (CS, SV))
    # final linear combination
    at = {}
    cl = Closure(w, P0, {})
    for e_, st in (('A', ar), ('( A x. %s )' % P2, lhr), ('( Re ` %s )' % RHS, s(P0, [s(P0, [r2c, ass], 'addcld', '%s e. CC' % RHS)], 'recld', '( Re ` %s ) e. RR' % RHS)),
                   ('( Re ` %s )' % R2, s(P0, [r2c], 'recld', '( Re ` %s ) e. RR' % R2)), ('( Re ` %s )' % R1, s(P0, [r1c], 'recld', '( Re ` %s ) e. RR' % R1)),
                   (YR, s(P0, [ass], 'recld', '%s e. RR' % YR)), ('( Re ` A )', s(P0, [ac], 'recld', '( Re ` A ) e. RR')),
                   ('( Re ` ( A x. %s ) )' % SV, s(P0, [asv], 'recld', '( Re ` ( A x. %s ) ) e. RR' % SV)), ('( Re ` ( A x. %s ) )' % CS, s(P0, [acs], 'recld', '( Re ` ( A x. %s ) ) e. RR' % CS)),
                   (SRAV, s(P0, [h[1], s(P1, [avc], 'recld', '( Re ` ( A x. V ) ) e. RR')], 'fsumrecl', '%s e. RR' % SRAV)),
                   (SAV2, s(P0, [h[1], x7r], 'fsumrecl', '%s e. RR' % SAV2)), (SS2, s(P0, [h[1], rsadr], 'fsumrecl', '%s e. RR' % SS2))):
        cl.leaf(e_, 'RR', st); cl.atom(e_)
    GOAL_R = '( ( ( A + ( 2 x. %s ) ) + %s ) + %s )' % (SRAV, SAV2, SS2)
    fin = lineq(w, P0, '( A x. %s )' % P2, GOAL_R, hyps=[z4, z5, z6, z7, z8, z10, z13, y6], closure=cl)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['cenexp']))
    return run(w)


if __name__ == '__main__':
    gen_exp()
