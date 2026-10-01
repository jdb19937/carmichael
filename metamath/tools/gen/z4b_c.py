"""Sortie Z4b, section C: the Gallagher-Sobolev pointwise bound (LargeSieve sobolev_sq_le)
and the monotonicity of the integral of a nonnegative function in its interval."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z4blib import *
from lin import linarith
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def hf(w, A0):
    P = parts(w, A0)
    return P, P['F : RR --> CC'], P['( RR _D F ) = G'], P['G e. %s' % CNR]


def fcn_of(w, A0, ff, dfg, gcn):
    """( A0 -> F e. CNR ) by dvcn"""
    gf = ap(w, A0, 'cncff', [gcn], 'G : RR --> CC')
    dm = eqt(w, A0, st(w, A0, [dfg], 'dmeqd', 'dom ( RR _D F ) = dom G'), ap(w, A0, 'fdm', [gf], 'dom G = RR'))
    j3 = J(w, A0, a1(w, A0, 'ax-resscn', 'RR C_ CC'), ff, a1(w, A0, 'ssid', 'RR C_ RR'))
    return ap(w, A0, 'dvcn', [J(w, A0, j3, dm)], 'F e. %s' % CNR), gf


def fvcl(w, ante, fst, F, v, vr):
    """( ante -> ( F ` v ) e. CC ) from fst: F : RR --> CC, vr: v e. RR"""
    return st(w, ante, [fst, vr], 'ffvelcdmd', '( %s ` %s ) e. CC' % (F, v))


if __name__ == '__main__':
    # ---- lsitgmono
    w = W('lsitgmono', 'The integral of a nonnegative continuous function over a subinterval is at most its integral over the interval.')
    hyps_of(w, 'lsitgmono')
    A0 = 'ph'
    from functools import lru_cache
    @lru_cache(None)
    def xr(a, b):
        return w.s([w.inst('elioore'), 'hr'.replace('h', '')], 'sylan2', '( ( ph /\\ t e. %s ) -> X e. RR )' % IOO(a, b))
    @lru_cache(None)
    def xge(a, b):
        return w.s([w.inst('elioore'), 'p'], 'sylan2', '( ( ph /\\ t e. %s ) -> 0 <_ X )' % IOO(a, b))
    @lru_cache(None)
    def xc(a, b):
        return st(w, '( ph /\\ t e. %s )' % IOO(a, b), [xr(a, b)], 'recnd', 'X e. CC')
    @lru_cache(None)
    def ibl(a, b):
        return w.s([a.lower(), b.lower(), 'c'], 'lsibl', '( ph -> ( t e. %s |-> X ) e. L^1 )' % IOO(a, b))
    ub = w.s(['u', 'v', 'b', 'uv', 'vb'], 'letrd', '( ph -> U <_ B )')
    uab = w.s([w.s(['a', 'b', w.inst('elicc2')], 'syl2anc', '( ph -> ( U e. %s <-> ( U e. RR /\\ A <_ U /\\ U <_ B ) ) )' % ICC('A', 'B')),
               w.s(['u', 'au', ub], '3jca', '( ph -> ( U e. RR /\\ A <_ U /\\ U <_ B ) )')], 'mpbird', '( ph -> U e. %s )' % ICC('A', 'B'))
    vub = w.s([w.s(['u', 'b', w.inst('elicc2')], 'syl2anc', '( ph -> ( V e. %s <-> ( V e. RR /\\ U <_ V /\\ V <_ B ) ) )' % ICC('U', 'B')),
               w.s(['v', 'uv', 'vb'], '3jca', '( ph -> ( V e. RR /\\ U <_ V /\\ V <_ B ) )')], 'mpbird', '( ph -> V e. %s )' % ICC('U', 'B'))
    s1 = w.s(['a', 'b', uab, xc('A', 'B'), ibl('A', 'U'), ibl('U', 'B')], 'itgsplitioo',
             '( ph -> %s = ( %s + %s ) )' % (ITG(IOO('A', 'B'), 'X'), ITG(IOO('A', 'U'), 'X'), ITG(IOO('U', 'B'), 'X')))
    s2 = w.s(['u', 'b', vub, xc('U', 'B'), ibl('U', 'V'), ibl('V', 'B')], 'itgsplitioo',
             '( ph -> %s = ( %s + %s ) )' % (ITG(IOO('U', 'B'), 'X'), ITG(IOO('U', 'V'), 'X'), ITG(IOO('V', 'B'), 'X')))
    g1 = w.s([ibl('A', 'U'), xr('A', 'U'), xge('A', 'U')], 'itgge0', '( ph -> 0 <_ %s )' % ITG(IOO('A', 'U'), 'X'))
    g2 = w.s([ibl('V', 'B'), xr('V', 'B'), xge('V', 'B')], 'itgge0', '( ph -> 0 <_ %s )' % ITG(IOO('V', 'B'), 'X'))
    def rl(a, b, sa, sb):
        return w.s([xr(a, b), ibl(a, b)], 'itgrecl', '( ph -> %s e. RR )' % ITG(IOO(a, b), 'X'))
    lv = {ITG(IOO(a, b), 'X'): rl(a, b, sa, sb) for a, b, sa, sb in [('A', 'B', 'A', 'B'), ('A', 'U', 'A', 'U'), ('U', 'B', 'U', 'B'), ('U', 'V', 'U', 'V'), ('V', 'B', 'V', 'B')]}
    I = lambda a, b: ITG(IOO(a, b), 'X')
    R = lambda a, b: lv[I(a, b)]
    h1 = w.s([g2, w.s([R('U', 'V'), R('V', 'B')], 'addge01d', '( ph -> ( 0 <_ %s <-> %s <_ ( %s + %s ) ) )' % (I('V', 'B'), I('U', 'V'), I('U', 'V'), I('V', 'B')))], 'mpbid',
             '( ph -> %s <_ ( %s + %s ) )' % (I('U', 'V'), I('U', 'V'), I('V', 'B')))
    h2 = w.s([h1, s2], 'breqtrrd', '( ph -> %s <_ %s )' % (I('U', 'V'), I('U', 'B')))
    h3 = w.s([g1, w.s([R('U', 'B'), R('A', 'U')], 'addge02d', '( ph -> ( 0 <_ %s <-> %s <_ ( %s + %s ) ) )' % (I('A', 'U'), I('U', 'B'), I('A', 'U'), I('U', 'B')))], 'mpbid',
             '( ph -> %s <_ ( %s + %s ) )' % (I('U', 'B'), I('A', 'U'), I('U', 'B')))
    h4 = w.s([h3, s1], 'breqtrrd', '( ph -> %s <_ %s )' % (I('U', 'B'), I('A', 'B')))
    w.qed([R('U', 'V'), R('U', 'B'), R('A', 'B'), h2, h4], 'letrd', STATEMENTS['lsitgmono'])
    go(w)

    # ---- lssoblem1: the derivative of | F | ^ 2 = F conj F
    A0 = HF
    w = W('lssoblem1', 'The derivative of t |-> F ( t ) conj F ( t ) for a differentiable F with continuous derivative G, and its continuity (LargeSieve sobolev_sq_le, hgderiv).')
    P, ff, dfg, gcn = hf(w, A0)
    fcn, gf = fcn_of(w, A0, ff, dfg, gcn)
    At = '( %s /\\ t e. RR )' % A0
    tr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    ft = fvcl(w, At, lift(w, ff, At), 'F', 't', tr); gt = fvcl(w, At, lift(w, gf, At), 'G', 't', tr)
    FM = '( t e. RR |-> ( F ` t ) )'; GM = '( t e. RR |-> ( G ` t ) )'
    fm = st(w, A0, [ff], 'feqmptd', 'F = %s' % FM); gm = st(w, A0, [gf], 'feqmptd', 'G = %s' % GM)
    x1 = st(w, A0, [fm], 'oveq2d', '( RR _D F ) = ( RR _D %s )' % FM)
    dF = eqt(w, A0, eqt(w, A0, eqc(w, A0, x1), dfg), gm)
    rr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    dC = st(w, A0, [ft, gt, dF], 'dvmptcj', '( RR _D ( t e. RR |-> ( * ` ( F ` t ) ) ) ) = ( t e. RR |-> ( * ` ( G ` t ) ) )')
    cft = st(w, At, [ft], 'cjcld', '( * ` ( F ` t ) ) e. CC'); cgt = st(w, At, [gt], 'cjcld', '( * ` ( G ` t ) ) e. CC')
    dM = st(w, A0, [rr, ft, gt, dF, cft, cgt, dC], 'dvmptmul', '( RR _D %s ) = %s' % (NFv('t'), DNFv('t')))
    fmc = fmap(w, A0, fcn, 'F', 't'); gmc = fmap(w, A0, gcn, 'G', 't')
    cj = a1(w, A0, 'cjcncf', '* e. ( CC -cn-> CC )')
    cfc = st(w, A0, [cj, fmc], 'cncfmpt1f', '( t e. RR |-> ( * ` ( F ` t ) ) ) e. %s' % CNR)
    cgc = st(w, A0, [cj, gmc], 'cncfmpt1f', '( t e. RR |-> ( * ` ( G ` t ) ) ) e. %s' % CNR)
    m1 = cnmul(w, A0, gmc, '( G ` t )', cfc, '( * ` ( F ` t ) )', 't')
    m2 = cnmul(w, A0, cgc, '( * ` ( G ` t ) )', fmc, '( F ` t )', 't')
    ad = cnadd(w, A0, m1, '( ( G ` t ) x. ( * ` ( F ` t ) ) )', m2, '( ( * ` ( G ` t ) ) x. ( F ` t ) )', 't')
    w.qed([dM, ad], 'jca', STATEMENTS['lssoblem1']); go(w)

    # ---- lssoblem2: | g ( V ) - g ( U ) | <_ int_U^V 2 | F | | G |
    A0 = '( %s /\\ ( U e. RR /\\ V e. RR /\\ U <_ V ) )' % HF
    w = W('lssoblem2', 'The oscillation of | F | ^ 2 over [ U , V ] is at most the integral of 2 | F | | G | (LargeSieve sobolev_sq_le, hftc and hmono).')
    P, ff, dfg, gcn = hf(w, A0)
    ur, vr, le = P['U e. RR'], P['V e. RR'], P['U <_ V']
    fcn, gf = fcn_of(w, A0, ff, dfg, gcn)
    L1 = ap(w, A0, 'lssoblem1', [P[HF]], '( ( RR _D %s ) = %s /\\ %s e. %s )' % (NFv('t'), DNFv('t'), DNFv('t'), CNR))
    dN = st(w, A0, [L1], 'simpld', '( RR _D %s ) = %s' % (NFv('t'), DNFv('t'))); dcn = st(w, A0, [L1], 'simprd', '%s e. %s' % (DNFv('t'), CNR))
    As = '( %s /\\ t e. RR )' % A0
    sr = w.s([], 'simpr', '( %s -> t e. RR )' % As)
    fs = fvcl(w, As, lift(w, ff, As), 'F', 't', sr); gs = fvcl(w, As, lift(w, gf, As), 'G', 't', sr)
    NB = '( ( F ` t ) x. ( * ` ( F ` t ) ) )'
    nbc = st(w, As, [fs, st(w, As, [fs], 'cjcld', '( * ` ( F ` t ) ) e. CC')], 'mulcld', '%s e. CC' % NB)
    nff = st(w, A0, [nbc], 'fmptd', '%s : RR --> CC' % NFv('t'))
    ftc = ap(w, A0, 'lsftc', [J(w, A0, J(w, A0, ur, vr, le), J(w, A0, nff, dN, dcn))],
             '%s = ( ( %s ` V ) - ( %s ` U ) )' % (ITG(IOO('U', 'V'), '( %s ` s )' % DNFv('t'), 's'), NFv('t'), NFv('t')))
    def endv(X, xr):
        fx = fvcl(w, A0, ff, 'F', X, xr)
        pc = st(w, A0, [fx, st(w, A0, [fx], 'cjcld', '( * ` ( F ` %s ) ) e. CC' % X)], 'mulcld', '( ( F ` %s ) x. ( * ` ( F ` %s ) ) ) e. CC' % (X, X))
        nv = fvmd(w, A0, 't', 'RR', NB, X, xr, pc)
        av = ap(w, A0, 'absvalsq', [fx], '%s = ( ( F ` %s ) x. ( * ` ( F ` %s ) ) )' % (FA2('F', X), X, X))
        return eqt(w, A0, nv, eqc(w, A0, av)), fx
    nV, fV = endv('V', vr); nU, fU = endv('U', ur)
    df = st(w, A0, [nV, nU], 'oveq12d', '( ( %s ` V ) - ( %s ` U ) ) = ( %s - %s )' % (NFv('t'), NFv('t'), FA2('F', 'V'), FA2('F', 'U')))
    eq1 = eqt(w, A0, ftc, df)
    Dx = '( ( ( G ` s ) x. ( * ` ( F ` s ) ) ) + ( ( * ` ( G ` s ) ) x. ( F ` s ) ) )'
    Dt = '( ( ( G ` t ) x. ( * ` ( F ` t ) ) ) + ( ( * ` ( G ` t ) ) x. ( F ` t ) ) )'
    Aso = '( %s /\\ s e. %s )' % (A0, IOO('U', 'V'))
    so = ioore(w, A0, 'U', 'V', 's')
    fso = fvcl(w, Aso, lift(w, ff, Aso), 'F', 's', so); gso = fvcl(w, Aso, lift(w, gf, Aso), 'G', 's', so)
    cfs = st(w, Aso, [fso], 'cjcld', '( * ` ( F ` s ) ) e. CC'); cgs = st(w, Aso, [gso], 'cjcld', '( * ` ( G ` s ) ) e. CC')
    t1 = st(w, Aso, [gso, cfs], 'mulcld', '( ( G ` s ) x. ( * ` ( F ` s ) ) ) e. CC'); t2 = st(w, Aso, [cgs, fso], 'mulcld', '( ( * ` ( G ` s ) ) x. ( F ` s ) ) e. CC')
    dxc = st(w, Aso, [t1, t2], 'addcld', '%s e. CC' % Dx)
    dvs = fvmd(w, Aso, 't', 'RR', Dt, 's', so, dxc)
    eq2 = st(w, A0, [dvs], 'itgeq2dv', '%s = %s' % (ITG(IOO('U', 'V'), '( %s ` s )' % DNFv('t'), 's'), ITG(IOO('U', 'V'), Dx, 's')))
    eq3 = eqt(w, A0, eqc(w, A0, eq1), eq2)   # diff = S. Dx
    DIF = '( %s - %s )' % (FA2('F', 'V'), FA2('F', 'U'))
    ab1 = st(w, A0, [eq3], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (DIF, ITG(IOO('U', 'V'), Dx, 's')))
    cbs, _ = w.congr(Dt, {'t': 's'}, 't = s', {'t': w.s([], 'id', '( t = s -> t = s )')})
    cbm = w.s([w.s([cbs], 'cbvmptv', '%s = ( s e. RR |-> %s )' % (DNFv('t'), Dx))], 'a1i', '( %s -> %s = ( s e. RR |-> %s ) )' % (A0, DNFv('t'), Dx))
    dcns = st(w, A0, [cbm, dcn], 'eqeltrrd', '( s e. RR |-> %s ) e. %s' % (Dx, CNR))
    ibd = w.s([ur, vr, dcns], 'lsibl', '( %s -> ( s e. %s |-> %s ) e. L^1 )' % (A0, IOO('U', 'V'), Dx))
    ia = st(w, A0, [dxc, ibd], 'itgabs', '( abs ` %s ) <_ %s' % (ITG(IOO('U', 'V'), Dx, 's'), ITG(IOO('U', 'V'), '( abs ` %s )' % Dx, 's')))
    iba = st(w, A0, [dxc, ibd], 'iblabs', '( s e. %s |-> ( abs ` %s ) ) e. L^1' % (IOO('U', 'V'), Dx))
    fgc = cnfg(w, A0, fmap(w, A0, fcn, 'F', 's'), fmap(w, A0, gcn, 'G', 's'), 's')
    ibf = w.s([ur, vr, fgc], 'lsibl', '( %s -> ( s e. %s |-> %s ) e. L^1 )' % (A0, IOO('U', 'V'), FG2('s')))
    aF = '( abs ` ( F ` s ) )'; aG = '( abs ` ( G ` s ) )'
    afr = st(w, Aso, [fso], 'abscld', '%s e. RR' % aF); agr = st(w, Aso, [gso], 'abscld', '%s e. RR' % aG)
    adr = st(w, Aso, [dxc], 'abscld', '( abs ` %s ) e. RR' % Dx)
    fgr = st(w, Aso, [st(w, Aso, [a1(w, Aso, '2re', '2 e. RR'), afr], 'remulcld', '( 2 x. %s ) e. RR' % aF), agr], 'remulcld', '%s e. RR' % FG2('s'))
    tri = st(w, Aso, [t1, t2], 'abstrid', '( abs ` %s ) <_ ( ( abs ` ( ( G ` s ) x. ( * ` ( F ` s ) ) ) ) + ( abs ` ( ( * ` ( G ` s ) ) x. ( F ` s ) ) ) )' % Dx)
    e1 = eqt(w, Aso, st(w, Aso, [gso, cfs], 'absmuld', '( abs ` ( ( G ` s ) x. ( * ` ( F ` s ) ) ) ) = ( %s x. ( abs ` ( * ` ( F ` s ) ) ) )' % aG),
             st(w, Aso, [ap(w, Aso, 'abscj', [fso], '( abs ` ( * ` ( F ` s ) ) ) = %s' % aF)], 'oveq2d', '( %s x. ( abs ` ( * ` ( F ` s ) ) ) ) = ( %s x. %s )' % (aG, aG, aF)))
    e2 = eqt(w, Aso, st(w, Aso, [cgs, fso], 'absmuld', '( abs ` ( ( * ` ( G ` s ) ) x. ( F ` s ) ) ) = ( ( abs ` ( * ` ( G ` s ) ) ) x. %s )' % aF),
             st(w, Aso, [ap(w, Aso, 'abscj', [gso], '( abs ` ( * ` ( G ` s ) ) ) = %s' % aG)], 'oveq1d', '( ( abs ` ( * ` ( G ` s ) ) ) x. %s ) = ( %s x. %s )' % (aF, aG, aF)))
    afc = st(w, Aso, [afr], 'recnd', '%s e. CC' % aF); agc = st(w, Aso, [agr], 'recnd', '%s e. CC' % aG)
    e3 = eqt(w, Aso, st(w, Aso, [w.s([], '2cnd', '( %s -> 2 e. CC )' % Aso), afc, agc], 'mulassd', '%s = ( 2 x. ( %s x. %s ) )' % (FG2('s'), aF, aG)),
             st(w, Aso, [st(w, Aso, [afc, agc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (aF, aG, aG, aF))], 'oveq2d', '( 2 x. ( %s x. %s ) ) = ( 2 x. ( %s x. %s ) )' % (aF, aG, aG, aF)))
    GF = '( %s x. %s )' % (aG, aF)
    gfr = st(w, Aso, [agr, afr], 'remulcld', '%s e. RR' % GF)
    a1r = st(w, Aso, [t1], 'abscld', '( abs ` ( ( G ` s ) x. ( * ` ( F ` s ) ) ) ) e. RR')
    a2r = st(w, Aso, [t2], 'abscld', '( abs ` ( ( * ` ( G ` s ) ) x. ( F ` s ) ) ) e. RR')
    A1_ = '( abs ` ( ( G ` s ) x. ( * ` ( F ` s ) ) ) )'; A2_ = '( abs ` ( ( * ` ( G ` s ) ) x. ( F ` s ) ) )'
    sa = st(w, Aso, [e1, e2], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (A1_, A2_, GF, GF))
    sb = eqc(w, Aso, st(w, Aso, [st(w, Aso, [gfr], 'recnd', '%s e. CC' % GF)], '2timesd', '( 2 x. %s ) = ( %s + %s )' % (GF, GF, GF)))
    pw = st(w, Aso, [tri, eqt(w, Aso, eqt(w, Aso, sa, sb), eqc(w, Aso, e3))], 'breqtrd', '( abs ` %s ) <_ %s' % (Dx, FG2('s')))
    il = st(w, A0, [iba, ibf, adr, fgr, pw], 'itgle', '%s <_ %s' % (ITG(IOO('U', 'V'), '( abs ` %s )' % Dx, 's'), ITG(IOO('U', 'V'), FG2('s'), 's')))
    I1 = ITG(IOO('U', 'V'), Dx, 's'); I2 = ITG(IOO('U', 'V'), '( abs ` %s )' % Dx, 's'); I3 = ITG(IOO('U', 'V'), FG2('s'), 's')
    i1c = st(w, A0, [dxc, ibd], 'itgcl', '%s e. CC' % I1)
    gVr = st(w, A0, [st(w, A0, [fV], 'abscld', '( abs ` ( F ` V ) ) e. RR')], 'resqcld', '%s e. RR' % FA2('F', 'V'))
    gUr = st(w, A0, [st(w, A0, [fU], 'abscld', '( abs ` ( F ` U ) ) e. RR')], 'resqcld', '%s e. RR' % FA2('F', 'U'))
    dfr = st(w, A0, [gVr, gUr], 'resubcld', '%s e. RR' % DIF)
    lv = {'( abs ` %s )' % DIF: st(w, A0, [st(w, A0, [dfr], 'recnd', '%s e. CC' % DIF)], 'abscld', '( abs ` %s ) e. RR' % DIF),
          '( abs ` %s )' % I1: st(w, A0, [i1c], 'abscld', '( abs ` %s ) e. RR' % I1),
          I2: st(w, A0, [adr, iba], 'itgrecl', '%s e. RR' % I2), I3: st(w, A0, [fgr, ibf], 'itgrecl', '%s e. RR' % I3)}
    w.qed([lv['( abs ` %s )' % DIF], lv[I2], lv[I3], st(w, A0, [ab1, ia], 'eqbrtrd', '( abs ` %s ) <_ %s' % (DIF, I2)), il], 'letrd', STATEMENTS['lssoblem2'])
    go(w)

    # ---- lssoblem3: g ( X ) <_ g ( Y ) + int_A^B 2 | F | | G | for X, Y in [ A , B ]
    A0 = '( %s /\\ ( ( A e. RR /\\ B e. RR ) /\\ ( X e. %s /\\ Y e. %s ) ) )' % (HF, ICC('A', 'B'), ICC('A', 'B'))
    w = W('lssoblem3', 'The value of | F | ^ 2 at one point of [ A , B ] is at most its value at another plus the integral of 2 | F | | G | over [ A , B ] (LargeSieve sobolev_sq_le, hosc).')
    P, ff, dfg, gcn = hf(w, A0)
    ar, br = P['A e. RR'], P['B e. RR']
    fcn, gf = fcn_of(w, A0, ff, dfg, gcn)
    def icc3(X):
        e = ap(w, A0, 'elicc2', [ar, br], '( %s e. %s <-> ( %s e. RR /\\ A <_ %s /\\ %s <_ B ) )' % (X, ICC('A', 'B'), X, X, X))
        t = st(w, A0, [P['%s e. %s' % (X, ICC('A', 'B'))], e], 'mpbid', '( %s e. RR /\\ A <_ %s /\\ %s <_ B )' % (X, X, X))
        return (st(w, A0, [t], 'simp1d', '%s e. RR' % X), st(w, A0, [t], 'simp2d', 'A <_ %s' % X), st(w, A0, [t], 'simp3d', '%s <_ B' % X))
    xr, ax, xb = icc3('X'); yr, ay, yb = icc3('Y')
    fgc = cnfg(w, A0, fmap(w, A0, fcn, 'F', 's'), fmap(w, A0, gcn, 'G', 's'), 's')
    As = '( %s /\\ s e. RR )' % A0
    sr = w.s([], 'simpr', '( %s -> s e. RR )' % As)
    fs = fvcl(w, As, lift(w, ff, As), 'F', 's', sr); gs = fvcl(w, As, lift(w, gf, As), 'G', 's', sr)
    cs = ctx(w, As, {'( F ` s )': ('CC', fs), '( G ` s )': ('CC', gs)})
    fgr = cs.mem(FG2('s'), 'RR'); fg0 = cs.ge0(FG2('s'))
    ibab = w.s([ar, br, fgc], 'lsibl', '( %s -> ( s e. %s |-> %s ) e. L^1 )' % (A0, IOO('A', 'B'), FG2('s')))
    fgr_ab = w.s([w.inst('elioore'), fgr], 'sylan2', '( ( %s /\\ s e. %s ) -> %s e. RR )' % (A0, IOO('A', 'B'), FG2('s')))
    CAB = ITG(IOO('A', 'B'), FG2('s'), 's')
    cr = st(w, A0, [fgr_ab, ibab], 'itgrecl', '%s e. RR' % CAB)
    fX = fvcl(w, A0, ff, 'F', 'X', xr); fY = fvcl(w, A0, ff, 'F', 'Y', yr)
    gX = st(w, A0, [st(w, A0, [fX], 'abscld', '( abs ` ( F ` X ) ) e. RR')], 'resqcld', '%s e. RR' % FA2('F', 'X'))
    gY = st(w, A0, [st(w, A0, [fY], 'abscld', '( abs ` ( F ` Y ) ) e. RR')], 'resqcld', '%s e. RR' % FA2('F', 'Y'))
    def case(U, V, ur, vr, au, vb, swap):
        Ac = '( %s /\\ %s <_ %s )' % (A0, U, V)
        le = w.s([], 'simpr', '( %s -> %s <_ %s )' % (Ac, U, V))
        L = lambda s_: lift(w, s_, Ac)
        l2 = ap(w, Ac, 'lssoblem2', [J(w, Ac, L(P[HF]), J(w, Ac, L(ur), L(vr), le))],
                '( abs ` ( %s - %s ) ) <_ %s' % (FA2('F', V), FA2('F', U), ITG(IOO(U, V), FG2('s'), 's')))
        # lsitgmono with t := s
        fgrc = w.s([fgr], 'adantlr', '( ( %s /\\ s e. RR ) -> %s e. RR )' % (Ac, FG2('s')))
        fg0c = w.s([fg0], 'adantlr', '( ( %s /\\ s e. RR ) -> 0 <_ %s )' % (Ac, FG2('s')))
        mono = w.s([L(ar), L(br), L(ur), L(vr), L(au), le, L(vb), L(fgc), fgrc, fg0c], 'lsitgmono',
                   '( %s -> %s <_ %s )' % (Ac, ITG(IOO(U, V), FG2('s'), 's'), CAB))
        D1 = '( %s - %s )' % (FA2('F', V), FA2('F', U))
        d1r = st(w, Ac, [L(gX if V == 'X' else gY), L(gY if U == 'Y' else gX)], 'resubcld', '%s e. RR' % D1)
        ibuv = w.s([L(ur), L(vr), L(fgc)], 'lsibl', '( %s -> ( s e. %s |-> %s ) e. L^1 )' % (Ac, IOO(U, V), FG2('s')))
        fgr_uv = w.s([w.inst('elioore'), fgrc], 'sylan2', '( ( %s /\\ s e. %s ) -> %s e. RR )' % (Ac, IOO(U, V), FG2('s')))
        cuv = st(w, Ac, [fgr_uv, ibuv], 'itgrecl', '%s e. RR' % ITG(IOO(U, V), FG2('s'), 's'))
        lv = {FA2('F', 'X'): L(gX), FA2('F', 'Y'): L(gY), CAB: L(cr), ITG(IOO(U, V), FG2('s'), 's'): cuv,
              '( abs ` %s )' % D1: st(w, Ac, [st(w, Ac, [d1r], 'recnd', '%s e. CC' % D1)], 'abscld', '( abs ` %s ) e. RR' % D1)}
        AB = lv['( abs ` %s )' % D1]; IUV = lv[ITG(IOO(U, V), FG2('s'), 's')]; CR_ = L(cr)
        if not swap:
            la = st(w, Ac, [d1r], 'leabsd', '%s <_ ( abs ` %s )' % (D1, D1))
            x1 = st(w, Ac, [d1r, AB, IUV, la, l2], 'letrd', '%s <_ %s' % (D1, ITG(IOO(U, V), FG2('s'), 's')))
            x2 = st(w, Ac, [d1r, IUV, CR_, x1, mono], 'letrd', '%s <_ %s' % (D1, CAB))
            return st(w, Ac, [x2, st(w, Ac, [L(gX), L(gY), CR_], 'lesubadd2d', '( ( %s - %s ) <_ %s <-> %s <_ ( %s + %s ) )' % (FA2('F', 'X'), FA2('F', 'Y'), CAB, FA2('F', 'X'), FA2('F', 'Y'), CAB))],
                      'mpbid', concl('lssoblem3'))
        D2 = '( %s - %s )' % (FA2('F', U), FA2('F', V))
        d2r = st(w, Ac, [L(gX), L(gY)], 'resubcld', '%s e. RR' % D2)
        la = st(w, Ac, [d2r], 'leabsd', '%s <_ ( abs ` %s )' % (D2, D2))
        asb = ap(w, Ac, 'abssub', [st(w, Ac, [L(gX)], 'recnd', '%s e. CC' % FA2('F', 'X')), st(w, Ac, [L(gY)], 'recnd', '%s e. CC' % FA2('F', 'Y'))],
                 '( abs ` %s ) = ( abs ` %s )' % (D2, D1))
        x0 = st(w, Ac, [la, asb], 'breqtrd', '%s <_ ( abs ` %s )' % (D2, D1))
        x1 = st(w, Ac, [d2r, AB, IUV, x0, l2], 'letrd', '%s <_ %s' % (D2, ITG(IOO(U, V), FG2('s'), 's')))
        x2 = st(w, Ac, [d2r, IUV, CR_, x1, mono], 'letrd', '%s <_ %s' % (D2, CAB))
        return st(w, Ac, [x2, st(w, Ac, [L(gX), L(gY), CR_], 'lesubadd2d', '( ( %s - %s ) <_ %s <-> %s <_ ( %s + %s ) )' % (FA2('F', 'X'), FA2('F', 'Y'), CAB, FA2('F', 'X'), FA2('F', 'Y'), CAB))],
                  'mpbid', concl('lssoblem3'))
    c1 = case('Y', 'X', yr, xr, ay, xb, False)
    c2 = case('X', 'Y', xr, yr, ax, yb, True)
    w.qed([yr, xr, c1, c2], 'lecasei', STATEMENTS['lssoblem3']); go(w)

    # ---- lssob: the Gallagher-Sobolev bound
    A0 = '( %s /\\ ( D e. RR+ /\\ X e. RR ) )' % HF
    w = W('lssob', 'Gallagher-Sobolev pointwise bound: | F ( X ) | ^ 2 is at most 1 / D times the integral of | F | ^ 2 plus the integral of 2 | F | | G | over the interval of length D centred at X (LargeSieve sobolev_sq_le).')
    P, ff, dfg, gcn = hf(w, A0)
    drp, xr = P['D e. RR+'], P['X e. RR']
    fcn, gf = fcn_of(w, A0, ff, dfg, gcn)
    a = '( X - ( D / 2 ) )'; b = '( X + ( D / 2 ) )'
    c0 = ctx(w, A0, {'D': ('RR+', drp), 'X': ('RR', xr)})
    ar = c0.mem(a, 'RR'); br = c0.mem(b, 'RR'); dr = c0.mem('D', 'RR')
    dgt = c0.gt0('D')
    def inicc(E, lo, hi):
        e = ap(w, A0, 'elicc2', [ar, br], '( %s e. %s <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (E, ICC(a, b), E, a, E, E, b))
        return st(w, A0, [st(w, A0, [xr, lo, hi], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (E, a, E, E, b)), e], 'mpbird', '%s e. %s' % (E, ICC(a, b)))
    d2r = c0.mem('( D / 2 )', 'RR'); d20 = c0.ge0('( D / 2 )')
    aX = st(w, A0, [d20, st(w, A0, [xr, d2r], 'subge02d', '( 0 <_ ( D / 2 ) <-> %s <_ X )' % a)], 'mpbid', '%s <_ X' % a)
    Xb = st(w, A0, [d20, st(w, A0, [xr, d2r], 'addge01d', '( 0 <_ ( D / 2 ) <-> X <_ %s )' % b)], 'mpbid', 'X <_ %s' % b)
    ab = st(w, A0, [ar, xr, br, aX, Xb], 'letrd', '%s <_ %s' % (a, b))
    xab = inicc('X', aX, Xb)
    J_ = IOO(a, b)
    At = '( %s /\\ t e. %s )' % (A0, J_)
    tab = st(w, At, [a1(w, At, 'ioossicc', '%s C_ %s' % (J_, ICC(a, b))), w.s([], 'simpr', '( %s -> t e. %s )' % (At, J_))], 'sseldd', 't e. %s' % ICC(a, b))
    CS = ITG(J_, FG2('s'), 's'); CT = ITG(J_, FG2('t'))
    gXs = FA2('F', 'X'); gts = FA2('F', 't')
    L = lambda s_: lift(w, s_, At)
    l3 = ap(w, At, 'lssoblem3', [J(w, At, L(P[HF]), J(w, At, J(w, At, L(ar), L(br)), J(w, At, L(xab), tab)))], '%s <_ ( %s + %s )' % (gXs, gts, CS))
    # closures
    fX = fvcl(w, A0, ff, 'F', 'X', xr)
    gXr = st(w, A0, [st(w, A0, [fX], 'abscld', '( abs ` ( F ` X ) ) e. RR')], 'resqcld', '%s e. RR' % gXs)
    fmt = fmap(w, A0, fcn, 'F', 't'); gmt = fmap(w, A0, gcn, 'G', 't')
    Atr = '( %s /\\ t e. RR )' % A0
    ftr = fvcl(w, Atr, lift(w, ff, Atr), 'F', 't', w.s([], 'simpr', '( %s -> t e. RR )' % Atr))
    sqc = cnsq(w, A0, fmt, '( F ` t )', 't', ftr)
    fgs = cnfg(w, A0, fmap(w, A0, fcn, 'F', 's'), fmap(w, A0, gcn, 'G', 's'), 's')
    As = '( %s /\\ s e. RR )' % A0
    fss = fvcl(w, As, lift(w, ff, As), 'F', 's', w.s([], 'simpr', '( %s -> s e. RR )' % As))
    gss = fvcl(w, As, lift(w, gf, As), 'G', 's', w.s([], 'simpr', '( %s -> s e. RR )' % As))
    fgsr = ctx(w, As, {'( F ` s )': ('CC', fss), '( G ` s )': ('CC', gss)}).mem(FG2('s'), 'RR')
    csr = st(w, A0, [w.s([w.inst('elioore'), fgsr], 'sylan2', '( ( %s /\\ s e. %s ) -> %s e. RR )' % (A0, J_, FG2('s'))),
                     w.s([ar, br, fgs], 'lsibl', '( %s -> ( s e. %s |-> %s ) e. L^1 )' % (A0, J_, FG2('s')))], 'itgrecl', '%s e. RR' % CS)
    gtr = st(w, At, [st(w, At, [fvcl(w, At, L(ff), 'F', 't', ioore(w, A0, a, b))], 'abscld', '( abs ` ( F ` t ) ) e. RR')], 'resqcld', '%s e. RR' % gts)
    gXc = st(w, A0, [gXr], 'recnd', '%s e. CC' % gXs); csc = st(w, A0, [csr], 'recnd', '%s e. CC' % CS)
    ib1 = w.s([ar, br, cnconst(w, A0, gXc, gXs, 't')], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, J_, gXs))
    ib2 = w.s([ar, br, sqc], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, J_, gts))
    ib3 = w.s([ar, br, cnconst(w, A0, csc, CS, 't')], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, J_, CS))
    ib23 = w.s([ar, br, cnadd(w, A0, sqc, gts, cnconst(w, A0, csc, CS, 't'), CS, 't')], 'lsibl', '( %s -> ( t e. %s |-> ( %s + %s ) ) e. L^1 )' % (A0, J_, gts, CS))
    il = st(w, A0, [ib1, ib23, L(gXr), st(w, At, [gtr, L(csr)], 'readdcld', '( %s + %s ) e. RR' % (gts, CS)), l3], 'itgle',
            '%s <_ %s' % (ITG(J_, gXs), ITG(J_, '( %s + %s )' % (gts, CS))))
    vol = ap(w, A0, 'volioo', [ar, br, ab], '( vol ` %s ) = ( %s - %s )' % (J_, b, a))
    from lin import lineq
    xc_ = c0.mem('X', 'CC'); d2c = c0.mem('( D / 2 )', 'CC')
    vd = eqt(w, A0, st(w, A0, [xc_, d2c, d2c], 'pnncand', '( %s - %s ) = ( ( D / 2 ) + ( D / 2 ) )' % (b, a)), st(w, A0, [c0.mem('D', 'CC')], '2halvesd', '( ( D / 2 ) + ( D / 2 ) ) = D'))
    vol2 = eqt(w, A0, vol, vd)
    dv = a1(w, A0, 'ioombl', '%s e. dom vol' % J_)
    volr = st(w, A0, [vol2, dr], 'eqeltrd', '( vol ` %s ) e. RR' % J_)
    k1 = eqt(w, A0, ap(w, A0, 'itgconst', [dv, volr, gXc], '%s = ( %s x. ( vol ` %s ) )' % (ITG(J_, gXs), gXs, J_)),
             st(w, A0, [vol2], 'oveq2d', '( %s x. ( vol ` %s ) ) = ( %s x. D )' % (gXs, J_, gXs)))
    gtc = st(w, At, [gtr], 'recnd', '%s e. CC' % gts)
    k2 = st(w, A0, [gtc, ib2, L(csc), ib3], 'itgadd', '%s = ( %s + %s )' % (ITG(J_, '( %s + %s )' % (gts, CS)), ITG(J_, gts), ITG(J_, CS)))
    k3 = eqt(w, A0, ap(w, A0, 'itgconst', [dv, volr, csc], '%s = ( %s x. ( vol ` %s ) )' % (ITG(J_, CS), CS, J_)),
             st(w, A0, [vol2], 'oveq2d', '( %s x. ( vol ` %s ) ) = ( %s x. D )' % (CS, J_, CS)))
    I = ITG(J_, gts)
    ir = st(w, A0, [w.s([w.inst('elioore'), lift(w, w.s([], 'id', '( %s -> %s )' % (Atr, Atr)) and st(w, Atr, [st(w, Atr, [ftr], 'abscld', '( abs ` ( F ` t ) ) e. RR')], 'resqcld', '%s e. RR' % gts), Atr)], 'sylan2',
                        '( ( %s /\\ t e. %s ) -> %s e. RR )' % (A0, J_, gts)), ib2], 'itgrecl', '%s e. RR' % I)
    # D g ( X ) <_ I + C D, then divide
    h0 = st(w, A0, [k1, il], 'eqbrtrrd', '( %s x. D ) <_ %s' % (gXs, ITG(J_, '( %s + %s )' % (gts, CS))))
    h1 = st(w, A0, [h0, k2], 'breqtrd', '( %s x. D ) <_ ( %s + %s )' % (gXs, I, ITG(J_, CS)))
    h = st(w, A0, [h1, st(w, A0, [k3], 'oveq2d', '( %s + %s ) = ( %s + ( %s x. D ) )' % (I, ITG(J_, CS), I, CS))], 'breqtrd', '( %s x. D ) <_ ( %s + ( %s x. D ) )' % (gXs, I, CS))
    num = '( %s + ( %s x. D ) )' % (I, CS)
    numr = st(w, A0, [ir, st(w, A0, [csr, dr], 'remulcld', '( %s x. D ) e. RR' % CS)], 'readdcld', '%s e. RR' % num)
    q = st(w, A0, [h, ap(w, A0, 'lemuldivd', [gXr, numr, drp], '( ( %s x. D ) <_ %s <-> %s <_ ( %s / D ) )' % (gXs, num, gXs, num)) if False else
                   st(w, A0, [gXr, numr, drp], 'lemuldivd', '( ( %s x. D ) <_ %s <-> %s <_ ( %s / D ) )' % (gXs, num, gXs, num))], 'mpbid', '%s <_ ( %s / D )' % (gXs, num))
    dc = st(w, A0, [dr], 'recnd', 'D e. CC'); dne = c0.ne0('D')
    ic = st(w, A0, [ir], 'recnd', '%s e. CC' % I)
    cdc = st(w, A0, [csc, dc], 'mulcld', '( %s x. D ) e. CC' % CS)
    r1 = st(w, A0, [ic, cdc, dc, dne], 'divdird', '( %s / D ) = ( ( %s / D ) + ( ( %s x. D ) / D ) )' % (num, I, CS))
    r2 = st(w, A0, [st(w, A0, [ic, dc, dne], 'divrec2d', '( %s / D ) = ( ( 1 / D ) x. %s )' % (I, I)),
                    st(w, A0, [csc, dc, dne], 'divcan4d', '( ( %s x. D ) / D ) = %s' % (CS, CS))], 'oveq12d',
            '( ( %s / D ) + ( ( %s x. D ) / D ) ) = ( ( ( 1 / D ) x. %s ) + %s )' % (I, CS, I, CS))
    rr_ = eqt(w, A0, r1, r2)
    sub, _ = w.congr(FG2('s'), {'s': 't'}, 's = t', {'s': w.s([], 'id', '( s = t -> s = t )')})
    cb = a1(w, A0, 'cbvitgv', '%s = %s' % (CS, CT)) if False else w.s([w.s([sub], 'cbvitgv', '%s = %s' % (CS, CT))], 'a1i', '( %s -> %s = %s )' % (A0, CS, CT))
    fin = st(w, A0, [q, eqt(w, A0, rr_, st(w, A0, [cb], 'oveq2d', '( ( ( 1 / D ) x. %s ) + %s ) = ( ( ( 1 / D ) x. %s ) + %s )' % (I, CS, I, CT)))], 'breqtrd',
             '%s <_ ( ( ( 1 / D ) x. %s ) + %s )' % (gXs, I, CT))
    qedlast(w); go(w)
