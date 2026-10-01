"""Sortie ZC1: Lean's gFun = 1 - 2 ^ ( 1 - s ): holomorphy (gfhol) and its zero count (gfzc)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import c9_h
patch(c9_h)
from c10_f import clo
import zc1_d
import zc1_e
from zc1_e import l25rp, AT2
import lin
lin.FASTPATH = True

GC = '( z e. CC |-> ( 1 - ( 2 ^c ( 1 - z ) ) ) )'
S['gfhol'] = HOLF(GF, HP0)
ZG = ZS(GF, 'T')
S['gfrct'] = '( T e. RR -> A. x e. %s ( abs ` ( %s ` x ) ) <_ 3 )' % (RCT('T'), GF)
S['gfctr'] = '( t e. RR -> ( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. t ) ) ) ) )' % GF
S['gfzc'] = '( T e. RR -> ( %s e. Fin /\\ A. q e. %s %s e. NN /\\ %s <_ ( ; ; 8 0 0 x. ( log ` ( ( abs ` T ) + 2 ) ) ) ) )' % (ZG, ZG, HO(GF), MASS(ZG, GF))


def gen_gfhol():
    w = W('gfhol', 'Lean\'s ` gFun ` , ` s |-> 1 - 2 ^ ( 1 - s ) ` , is holomorphic (entire; here on the right half-plane): ~ dvcxp2 , ~ dvmptco , ~ zl2hent .')
    A0 = 'T.'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    Az = '( T. /\\ z e. CC )'
    Ay = '( T. /\\ y e. CC )'
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    sy = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ay, f))
    cc = s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', 'CC e. { RR , CC }')
    one = s([], '1cnd', '1 e. CC')
    d1 = s([cc, one], 'dvmptc', '( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 )')
    d2 = s([cc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    zc = sz([], 'simpr', 'z e. CC')
    one_z = sz([], '1cnd', '1 e. CC'); zero_z = sz([], '0cnd', '0 e. CC')
    dA = s([cc, one_z, zero_z, d1, zc, one_z, d2], 'dvmptsub', '( CC _D ( z e. CC |-> ( 1 - z ) ) ) = ( z e. CC |-> ( 0 - 1 ) )')
    two = numst(w, A0, '2', 'RR+')
    dC0 = s([two, w.inst('dvcxp2')], 'syl', '( CC _D ( y e. CC |-> ( 2 ^c y ) ) ) = ( y e. CC |-> ( ( log ` 2 ) x. ( 2 ^c y ) ) )')
    omz = sz([one_z, zc], 'subcld', '( 1 - z ) e. CC')
    m1 = sz([zero_z, one_z], 'subcld', '( 0 - 1 ) e. CC')
    yc = sy([], 'simpr', 'y e. CC')
    cy = sy([sy([], '2cnd', '2 e. CC'), yc], 'cxpcld', '( 2 ^c y ) e. CC')
    l2c = sy([sy([lift(w, two, Ay)], 'relogcld', '( log ` 2 ) e. RR')], 'recnd', '( log ` 2 ) e. CC')
    dy = sy([l2c, cy], 'mulcld', '( ( log ` 2 ) x. ( 2 ^c y ) ) e. CC')
    e = w.s([], 'oveq2', '( y = ( 1 - z ) -> ( 2 ^c y ) = ( 2 ^c ( 1 - z ) ) )')
    f = w.s([e], 'oveq2d', '( y = ( 1 - z ) -> ( ( log ` 2 ) x. ( 2 ^c y ) ) = ( ( log ` 2 ) x. ( 2 ^c ( 1 - z ) ) ) )')
    F_ = '( ( log ` 2 ) x. ( 2 ^c ( 1 - z ) ) )'
    dE = s([cc, cc, omz, m1, cy, dy, dA, dC0, e, f], 'dvmptco', '( CC _D ( z e. CC |-> ( 2 ^c ( 1 - z ) ) ) ) = ( z e. CC |-> ( %s x. ( 0 - 1 ) ) )' % F_)
    ez = sz([sz([], '2cnd', '2 e. CC'), omz], 'cxpcld', '( 2 ^c ( 1 - z ) ) e. CC')
    fz = sz([sz([lift(w, s([two], 'relogcld', '( log ` 2 ) e. RR'), Az)], 'recnd', '( log ` 2 ) e. CC'), ez], 'mulcld', '%s e. CC' % F_)
    fm = sz([fz, m1], 'mulcld', '( %s x. ( 0 - 1 ) ) e. CC' % F_)
    DV = '( 0 - ( %s x. ( 0 - 1 ) ) )' % F_
    dG = s([cc, one_z, zero_z, d1, ez, fm, dE], 'dvmptsub', '( CC _D %s ) = ( z e. CC |-> %s )' % (GC, DV))
    dvv = sz([zero_z, fm], 'subcld', '%s e. CC' % DV)
    dm = s([s([dvv], 'ralrimiva', 'A. z e. CC %s e. CC' % DV), w.inst('dmmptg')], 'syl', 'dom ( z e. CC |-> %s ) = CC' % DV)
    dmG = s([s([dG], 'dmeqd', 'dom ( CC _D %s ) = dom ( z e. CC |-> %s )' % (GC, DV)), dm], 'eqtrd', 'dom ( CC _D %s ) = CC' % GC)
    gv = sz([one_z, ez], 'subcld', '( 1 - ( 2 ^c ( 1 - z ) ) ) e. CC')
    gf = s([gv], 'fmptd', '%s : CC --> CC' % GC)
    ss = s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC')
    cn = s([s([ss, gf, ss], '3jca', '( CC C_ CC /\\ %s : CC --> CC /\\ CC C_ CC )' % GC), dmG, w.inst('dvcn')], 'syl2anc', '%s e. ( CC -cn-> CC )' % GC)
    dmss = s([s([dmG], 'eqcomd', 'CC = dom ( CC _D %s )' % GC), w.inst('eqimssd') if False else None], 'x', 'x') if False else s([s([dmG], 'eqcomd', 'CC = dom ( CC _D %s )' % GC)], 'eqimssd', 'CC C_ dom ( CC _D %s )' % GC)
    hc = s([cn, dmss], 'jca', HOLF(GC, 'CC'))
    op = s([w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0)], 'a1i', '%s e. ( TopOpen ` CCfld )' % HP0)
    h = s([s([hc, op], 'jca', ante_of(tsub(stmt('zl2hent'), {'A': '( 1 - ( 2 ^c ( 1 - z ) ) )', 'D': HP0}))[0]), w.inst('zl2hent')], 'syl', HOLF(GF, HP0))
    w.qed([h], 'mptru', S['gfhol'])
    return run8(w)


def gval(w, A0, xst, x):
    """( A0 -> ( GF ` x ) = ( 1 - ( 2 ^c ( 1 - x ) ) ) ) from xst : ( A0 -> x e. HP0 )"""
    BODY = '( 1 - ( 2 ^c ( 1 - z ) ) )'
    VAL = tsub(BODY, {'z': x})
    vx = w.s([w.s([], 'ovex', '%s e. _V' % VAL)], 'a1i', '( %s -> %s e. _V )' % (A0, VAL))
    fv, val = _cg.mptval(w, A0, 'z', HP0, BODY, x, xst, exs=vx, gen=w.g)
    return fv, VAL


def gen_gfzc(part=None):
    if part == 'rct':
        w = W('gfrct', 'Lean\'s ` gFun ` is at most ` 3 ` in modulus on the rectangle ` [ 1 / 4 , 15 / 4 ] x. [ T - 3 , T + 3 ] ` ( ~ zc1rct , ~ abscxp ; Lean ` diskData_gFun ` ).')
    elif part == 'ctr':
        w = W('gfctr', 'Centre bound for Lean\'s ` gFun ` : ` 1 / 2 <_ abs ( 1 - 2 ^ ( 1 - ( 2 + i t ) ) ) ` ( ~ abscxp , ~ abs2difd ).')
    else:
      w = W('gfzc', 'Zero count for Lean\'s ` gFun ` , ` 1 - 2 ^ ( 1 - s ) ` , on the square of half-side ` 13 / 8 ` about ` 2 + i T ` : at most ` 800 log ( abs T + 2 ) ` ( ~ jensq13 with ` B = 3 ` , ` M = 1 / 2 ` ; Lean ` diskData_gFun ` ).')
    A0 = 'T e. RR'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'id', 'T e. RR')
    hol = s([w.s([], 'gfhol', S['gfhol'])], 'a1i', S['gfhol'])
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    x2r = s([atr, numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % AT2)
    B, M = '3', '( 1 / 2 )'
    br = numst(w, A0, '3', 'RR')
    two = numst(w, A0, '2', 'RR+')

    def bstep(Ax):
        sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ax, f))
        rc = sx([sx([lift(w, tr, Ax), sx([], 'simpr', 'x e. %s' % RCT('T'))], 'jca', '( T e. RR /\\ x e. %s )' % RCT('T')), w.inst('zc1rct')], 'syl',
                tsub(ante_of(stmt('zc1rct'))[1], {'U': 'x'}))
        xh = sx([rc, w.inst('simp1')], 'syl', 'x e. %s' % HP0)
        rg = sx([rc, w.inst('simp2')], 'syl', '( 1 / 4 ) <_ ( Re ` x )')
        el = sx([sx([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( x e. %s <-> ( x e. CC /\\ 0 < ( Re ` x ) ) )' % HP0)
        xc = sx([sx([xh, el], 'mpbid', '( x e. CC /\\ 0 < ( Re ` x ) )'), w.inst('simpl')], 'syl', 'x e. CC')
        fv, VAL = gval(w, Ax, xh, 'x')
        omx = sx([sx([], '1cnd', '1 e. CC'), xc], 'subcld', '( 1 - x ) e. CC')
        pc = sx([sx([], '2cnd', '2 e. CC'), omx], 'cxpcld', '( 2 ^c ( 1 - x ) ) e. CC')
        tri = sx([sx([], '1cnd', '1 e. CC'), pc], 'abs2dif2d', '( abs ` %s ) <_ ( ( abs ` 1 ) + ( abs ` ( 2 ^c ( 1 - x ) ) ) )' % VAL)
        ac = sx([sx([lift(w, two, Ax), omx], 'jca', '( 2 e. RR+ /\\ ( 1 - x ) e. CC )'), w.inst('abscxp')], 'syl', '( abs ` ( 2 ^c ( 1 - x ) ) ) = ( 2 ^c ( Re ` ( 1 - x ) ) )')
        rsub = sx([sx([], '1cnd', '1 e. CC'), xc], 'resubd', '( Re ` ( 1 - x ) ) = ( ( Re ` 1 ) - ( Re ` x ) )')
        re1 = sx([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( Re ` 1 ) = 1')
        rx = sx([xc], 'recld', '( Re ` x ) e. RR'); rom = sx([omx], 'recld', '( Re ` ( 1 - x ) ) e. RR')
        r1r = sx([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
        re1r = sx([re1, r1r], 'eqeltrrd', '( Re ` 1 ) e. RR') if False else sx([sx([], '1cnd', '1 e. CC')], 'recld', '( Re ` 1 ) e. RR')
        le1 = lin8(w, Ax, [rsub, re1, rg], '( Re ` ( 1 - x ) ) <_ 1', {'( Re ` x )': rx, '( Re ` ( 1 - x ) )': rom, '( Re ` 1 )': re1r})
        A1 = '( ( 2 e. RR /\\ 1 <_ 2 ) /\\ ( ( Re ` ( 1 - x ) ) e. RR /\\ 1 e. RR ) /\\ ( Re ` ( 1 - x ) ) <_ 1 )'
        p1 = sx([sx([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), sx([w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2')], 'jca', '( 2 e. RR /\\ 1 <_ 2 )')
        p2 = sx([rom, r1r], 'jca', '( ( Re ` ( 1 - x ) ) e. RR /\\ 1 e. RR )')
        cl_ = sx([sx([p1, p2, le1], '3jca', A1), w.inst('cxplea')], 'syl', '( 2 ^c ( Re ` ( 1 - x ) ) ) <_ ( 2 ^c 1 )')
        c1 = sx([sx([], '2cnd', '2 e. CC'), w.inst('cxp1')], 'syl', '( 2 ^c 1 ) = 2')
        a2 = sx([sx([ac, cl_], 'eqbrtrd', '( abs ` ( 2 ^c ( 1 - x ) ) ) <_ ( 2 ^c 1 )'), c1], 'breqtrd', '( abs ` ( 2 ^c ( 1 - x ) ) ) <_ 2')
        a1 = sx([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')
        AF = '( abs ` ( %s ` x ) )' % GF
        af = sx([fv], 'fveq2d', '%s = ( abs ` %s )' % (AF, VAL))
        vc = sx([sx([], '1cnd', '1 e. CC'), pc], 'subcld', '%s e. CC' % VAL)
        lv = {AF: sx([sx([af, sx([vc], 'abscld', '( abs ` %s ) e. RR' % VAL)], 'eqeltrrd', '( abs ` %s ) e. RR' % VAL) if False else None], 'x', 'x') if False else None}
        lv = {'( abs ` %s )' % VAL: sx([vc], 'abscld', '( abs ` %s ) e. RR' % VAL), '( abs ` 1 )': sx([sx([], '1cnd', '1 e. CC')], 'abscld', '( abs ` 1 ) e. RR'),
              '( abs ` ( 2 ^c ( 1 - x ) ) )': sx([pc], 'abscld', '( abs ` ( 2 ^c ( 1 - x ) ) ) e. RR')}
        b = lin8(w, Ax, [tri, a2, a1], '( abs ` %s ) <_ 3' % VAL, lv)
        return sx([af, b], 'eqbrtrd', '%s <_ 3' % AF)

    def mstep(At, ts=None):
      if ts is None:
        tin = w.s([], 'simpr', '( %s -> t e. ( ( T - 2 ) [,] ( T + 2 ) ) )' % At)
        ts = w.s([w.s([lift(w, s([tr, numst(w, A0, '2', 'RR')], 'resubcld', '( T - 2 ) e. RR'), At), lift(w, s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), At)],
                      'iccssred', '( %s -> ( ( T - 2 ) [,] ( T + 2 ) ) C_ RR )' % At), tin], 'sseldd', '( %s -> t e. RR )' % At)
      if True:
        st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (At, f))
        C = '( 2 + ( _i x. t ) )'
        cc_ = st([st([], '2cnd', '2 e. CC'), st([st([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), st([ts], 'recnd', 't e. CC')], 'mulcld', '( _i x. t ) e. CC')], 'addcld', '%s e. CC' % C)
        re0 = st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), ts], 'crred', '( Re ` %s ) = 2' % C)
        ch = st([st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C, HP0, C, C))
        ch2 = st([st([cc_, st([lin8(w, At, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C, C)), ch], 'mpbird', '%s e. %s' % (C, HP0))
        fv, VAL = gval(w, At, ch2, C)
        D1 = '( %s - 1 )' % C
        d1c = st([cc_, st([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % D1)
        rd1 = st([cc_, st([], '1cnd', '1 e. CC')], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` 1 ) )' % (D1, C))
        re1 = st([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( Re ` 1 ) = 1')
        rv1 = st([st([rd1, st([re0, re1], 'oveq12d', '( ( Re ` %s ) - ( Re ` 1 ) ) = ( 2 - 1 )' % C)], 'eqtrd', '( Re ` %s ) = ( 2 - 1 )' % D1),
                  st([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')], 'eqtrd', '( Re ` %s ) = 1' % D1)
        ng = st([cc_, st([], '1cnd', '1 e. CC')], 'negsubdi2d', '-u %s = ( 1 - %s )' % (D1, C))
        rng = st([d1c, w.inst('reneg')], 'syl', '( Re ` -u %s ) = -u ( Re ` %s )' % (D1, D1))
        rr = st([st([st([ng], 'fveq2d', '( Re ` -u %s ) = ( Re ` ( 1 - %s ) )' % (D1, C)), rng], 'eqtr3d', '( Re ` ( 1 - %s ) ) = -u ( Re ` %s )' % (C, D1)),
                 st([rv1], 'negeqd', '-u ( Re ` %s ) = -u 1' % D1)], 'eqtrd', '( Re ` ( 1 - %s ) ) = -u 1' % C)
        omc = st([st([], '1cnd', '1 e. CC'), cc_], 'subcld', '( 1 - %s ) e. CC' % C)
        ac = st([st([numst(w, At, '2', 'RR+'), omc], 'jca', '( 2 e. RR+ /\\ ( 1 - %s ) e. CC )' % C), w.inst('abscxp')], 'syl', '( abs ` ( 2 ^c ( 1 - %s ) ) ) = ( 2 ^c ( Re ` ( 1 - %s ) ) )' % (C, C))
        ac2 = st([ac, st([rr], 'oveq2d', '( 2 ^c ( Re ` ( 1 - %s ) ) ) = ( 2 ^c -u 1 )' % C)], 'eqtrd', '( abs ` ( 2 ^c ( 1 - %s ) ) ) = ( 2 ^c -u 1 )' % C)
        cn = st([st([st([], '2cnd', '2 e. CC'), st([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0'), st([], '1cnd', '1 e. CC')], '3jca', '( 2 e. CC /\\ 2 =/= 0 /\\ 1 e. CC )'),
                 w.inst('cxpneg')], 'syl', '( 2 ^c -u 1 ) = ( 1 / ( 2 ^c 1 ) )')
        c1 = st([st([st([], '2cnd', '2 e. CC'), w.inst('cxp1')], 'syl', '( 2 ^c 1 ) = 2')], 'oveq2d', '( 1 / ( 2 ^c 1 ) ) = ( 1 / 2 )')
        half = st([ac2, st([cn, c1], 'eqtrd', '( 2 ^c -u 1 ) = ( 1 / 2 )')], 'eqtrd', '( abs ` ( 2 ^c ( 1 - %s ) ) ) = ( 1 / 2 )' % C)
        pc = st([st([], '2cnd', '2 e. CC'), omc], 'cxpcld', '( 2 ^c ( 1 - %s ) ) e. CC' % C)
        ad = st([st([], '1cnd', '1 e. CC'), pc], 'abs2difd', '( ( abs ` 1 ) - ( abs ` ( 2 ^c ( 1 - %s ) ) ) ) <_ ( abs ` %s )' % (C, VAL))
        a1 = st([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')
        ad1 = st([st([a1, half], 'oveq12d', '( ( abs ` 1 ) - ( abs ` ( 2 ^c ( 1 - %s ) ) ) ) = ( 1 - ( 1 / 2 ) )' % C), ad], 'eqbrtrrd', '( 1 - ( 1 / 2 ) ) <_ ( abs ` %s )' % VAL)
        vc = st([st([], '1cnd', '1 e. CC'), pc], 'subcld', '%s e. CC' % VAL)
        m = lin8(w, At, [ad1], '( 1 / 2 ) <_ ( abs ` %s )' % VAL, {'( abs ` %s )' % VAL: st([vc], 'abscld', '( abs ` %s ) e. RR' % VAL)})
        return st([m, st([fv], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (GF, C, VAL))], 'breqtrrd', '( 1 / 2 ) <_ ( abs ` ( %s ` %s ) )' % (GF, C))
    if part == 'ctr':
        g = mstep('t e. RR', ts=w.s([], 'id', '( t e. RR -> t e. RR )'))
        w.lines.append('qed:%s:idi |- %s' % (g, S['gfctr']))
        return run8(w)
    mrp = numst(w, A0, M, 'RR+')
    J = tsub(S['jensq13'], {'F': GF, 'B': B, 'M': M})
    ja, jc = ante_of(J)
    Y1, Y2, Y3 = top_and(ja)
    Ax = '( %s /\\ x e. %s )' % (A0, RCT('T'))
    bx = s([bstep(Ax)], 'ralrimiva', top_and(Y2)[1])
    if part == 'rct':
        w.lines.append('qed:%s:idi |- %s' % (bx, S['gfrct']))
        return run8(w)
    At = '( %s /\\ t e. ( ( T - 2 ) [,] ( T + 2 ) ) )' % A0
    mt = s([mstep(At)], 'ralrimiva', top_and(Y3)[1])
    jr = s([s([s([hol, tr], 'jca', Y1), s([br, bx], 'jca', Y2), s([mrp, mt], 'jca', Y3)], '3jca', ja), w.inst('jensq13')], 'syl', jc)
    C1, C2, C3 = top_and(jc)
    zf = s([jr, w.inst('simp1')], 'syl', C1); nn = s([jr, w.inst('simp2')], 'syl', C2); ms = s([jr, w.inst('simp3')], 'syl', C3)
    lv = {'( abs ` T )': atr}
    x2 = lin8(w, A0, [ag0], '2 <_ %s' % AT2, lv)
    brp = numst(w, A0, '3', 'RR+')
    mb = lin8(w, A0, [], '%s <_ %s' % (M, B), {})
    P = '( ; ; 1 2 8 x. %s )' % AT2
    bmx = s([lin8(w, A0, [ag0], '%s <_ ( %s x. %s )' % (B, M, P), lv), s([br, s([numst(w, A0, '; ; 1 2 8', 'RR'), x2r], 'remulcld', '%s e. RR' % P), mrp], 'ledivmuld',
             '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B, M, P, B, M, P))], 'mpbird', '( %s / %s ) <_ %s' % (B, M, P))
    Wz = tsub(S['zc1w8'], {'X': AT2, 'B': B, 'M': M})
    wa, wc = ante_of(Wz)
    w8 = s([s([s([x2r, x2], 'jca', top_and(wa)[0]), s([s([brp, mrp], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (B, M)), s([mb, bmx], 'jca', '( %s <_ %s /\\ ( %s / %s ) <_ %s )' % (M, B, B, M, P))], 'jca', top_and(wa)[1])],
                'jca', wa), w.inst('zc1w8')], 'syl', wc)
    MS = C3.split(' <_ ', 1)[0]
    msr = s([zf, w.s([w.s([nn], 'r19.21bi', '( ( %s /\\ q e. %s ) -> %s e. NN )' % (A0, ZG, HO(GF)))], 'nnred', '( ( %s /\\ q e. %s ) -> %s e. RR )' % (A0, ZG, HO(GF)))], 'fsumrecl', '%s e. RR' % MS)
    W_ = JW(B, M)
    wr = s([s([numst(w, A0, '4', 'RR'), s([s([brp, mrp], 'rpdivcld', '( %s / %s ) e. RR+' % (B, M))], 'relogcld', '( log ` ( %s / %s ) ) e. RR' % (B, M))], 'remulcld',
              '( 4 x. ( log ` ( %s / %s ) ) ) e. RR' % (B, M)), l25rp(w, A0)], 'rerpdivcld', '%s e. RR' % W_)
    x2p = s([x2r, lin8(w, A0, [ag0], '0 < %s' % AT2, lv)], 'elrpd', '%s e. RR+' % AT2)
    fin = s([msr, wr, s([numst(w, A0, '; ; 8 0 0', 'RR'), s([x2p], 'relogcld', '( log ` %s ) e. RR' % AT2)], 'remulcld', '( ; ; 8 0 0 x. ( log ` %s ) ) e. RR' % AT2), ms, w8], 'letrd',
            '%s <_ ( ; ; 8 0 0 x. ( log ` %s ) )' % (MS, AT2))
    w.qed([zf, nn, fin], '3jca', S['gfzc'])
    return run8(w)


if __name__ == '__main__':
    gen_gfhol()
    gen_gfzc()
    gen_gfzc('rct')
    gen_gfzc('ctr')
