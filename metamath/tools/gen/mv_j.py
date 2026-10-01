"""Sortie MV, section J: mean_value_chars (mvmvc1, mvmvc2, mvmvc, mvmvcp)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from mvlib import *
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


Gd = '( DChr ` N )'; Dd = DB(); Zd = '( Z/nZ ` N )'; Ld = LZ()
KK = '( ( ; 1 2 x. ( T ^ 2 ) ) / _pi )'


def eqids(w):
    return [w.s([], 'eqid', '%s = %s' % (x, x)) for x in (Gd, Zd, Dd, Ld)]


def aval(w, ante, v, aok, vmem):
    """( ante -> ( A ` v ) e. CC ) from aok: ( ante -> AOK ), vmem: ( ante -> v e. FZM )"""
    idst = w.s([], 'id', '( k = %s -> k = %s )' % (v, v))
    cst, new = w.wcongr('( A ` k ) e. CC', {'k': v}, 'k = %s' % v, {'k': idst})
    return w.s([cst, aok, vmem], 'rspcdva', '( %s -> ( A ` %s ) e. CC )' % (ante, v))


def chv(w, ante, v, nnst, xmem, vz):
    """( ante -> ( x ` ( L ` v ) ) e. CC )"""
    eG, eZ, eD, eL = eqids(w)
    return w.s([eG, eZ, eD, eL, xmem, vz], 'dchrzrhcl', '( %s -> %s e. CC )' % (ante, CHV('x', v)))


def trige0(w, ante, D_, Y, dge):
    """( ante -> 0 <_ TRI(D_, Y) ) given Y real (closure-free): by ifbothda"""
    T_ = TRI(D_, Y)
    cond = '( abs ` %s ) <_ %s' % (Y, D_)
    b1 = w.s([], 'breq2', '( ( %s - ( abs ` %s ) ) = %s -> ( 0 <_ ( %s - ( abs ` %s ) ) <-> 0 <_ %s ) )' % (D_, Y, T_, D_, Y, T_))
    b2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (T_, T_))
    return b1, b2, T_, cond


def mvmvc1():
    w = W('mvmvc1', 'mean_value_chars, kernel and orthogonality steps: the character sum of the t-integrals is at most ( 12 T ^ 2 / pi ) sum_ m sum_ n | a_m | | a_n | TRI ( log n - log m ) ( phi ( N ) if N || m - n ).')
    A0 = HMV
    P = parts(w, A0)
    nn, tp, mn0, aok = P['N e. NN'], P['T e. RR+'], P['M e. NN0'], P[AOK]
    cl = Closure(w, A0, {'N': ('NN', nn), 'T': ('RR+', tp), 'M': ('NN0', mn0), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZM))
    eG, eZ, eD, eL = eqids(w)
    dfin = w.s([nn, w.s([eG, eD], 'dchrfi', '( N e. NN -> %s e. Fin )' % Dd)], 'syl', '( %s -> %s e. Fin )' % (A0, Dd))
    Ax = '( %s /\\ x e. %s )' % (A0, Dd)
    xm = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, Dd))
    Cx = '( u e. %s |-> ( ( A ` u ) x. %s ) )' % (FZM, CHV('x', 'u'))
    Lf = '( u e. %s |-> -u ( log ` u ) )' % FZM
    # values of Cx, Lf at a variable v under an antecedent that knows x e. D and v e. FZM
    def vals(ante, v, vmem, xmem_):
        vn = ap(w, ante, 'elfznn', [vmem], '%s e. NN' % v)
        vz = w.s([vn], 'nnzd', '( %s -> %s e. ZZ )' % (ante, v))
        av = aval(w, ante, v, lift(w, aok, ante), vmem)
        cv = chv(w, ante, v, None, xmem_, vz)
        cval = '( ( A ` %s ) x. %s )' % (v, CHV('x', v))
        c1 = fvmd(w, ante, 'u', FZM, '( ( A ` u ) x. %s )' % CHV('x', 'u'), v, vmem, w.s([av, cv], 'mulcld', '( %s -> %s e. CC )' % (ante, cval)))
        lr = w.s([w.s([vn], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, v))], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (ante, v))
        l1 = fvmd(w, ante, 'u', FZM, '-u ( log ` u )', v, vmem, w.s([w.s([lr], 'renegcld', '( %s -> -u ( log ` %s ) e. RR )' % (ante, v))], 'recnd', '( %s -> -u ( log ` %s ) e. CC )' % (ante, v)))
        return dict(vn=vn, vz=vz, av=av, cv=cv, c1=c1, l1=l1, lr=lr, cval=cval)
    # HK at x
    Axa = '( %s /\\ a e. %s )' % (Ax, FZM)
    va = vals(Axa, 'a', w.s([], 'simpr', '( %s -> a e. %s )' % (Axa, FZM)), lift(w, xm, Axa))
    cia = w.s([va['c1'], w.s([va['av'], va['cv']], 'mulcld', '( %s -> %s e. CC )' % (Axa, va['cval']))], 'eqeltrd', '( %s -> ( %s ` a ) e. CC )' % (Axa, Cx))
    lia = w.s([va['l1'], w.s([va['lr']], 'renegcld', '( %s -> -u ( log ` a ) e. RR )' % Axa)], 'eqeltrd', '( %s -> ( %s ` a ) e. RR )' % (Axa, Lf))
    hq = w.s([w.s([cia, lia], 'jca', '( %s -> ( ( %s ` a ) e. CC /\\ ( %s ` a ) e. RR ) )' % (Axa, Cx, Lf))], 'ralrimiva',
             '( %s -> A. a e. %s ( ( %s ` a ) e. CC /\\ ( %s ` a ) e. RR ) )' % (Ax, FZM, Cx, Lf))
    hk = w.s([lift(w, fz, Ax), hq], 'jca', '( %s -> ( %s e. Fin /\\ A. a e. %s ( ( %s ` a ) e. CC /\\ ( %s ` a ) e. RR ) ) )' % (Ax, FZM, FZM, Cx, Lf))
    def sxi(t_, iv='m'):
        return 'sum_ %s e. %s ( ( %s ` %s ) x. ( exp ` ( _i x. ( ( %s ` %s ) x. %s ) ) ) )' % (iv, FZM, Cx, iv, Lf, iv, t_)
    TRIc = TRI(DT, '( ( %s ` m ) - ( %s ` n ) )' % (Lf, Lf))
    BILc = 'sum_ m e. %s sum_ n e. %s ( ( ( %s ` m ) x. ( * ` ( %s ` n ) ) ) x. %s )' % (FZM, FZM, Cx, Cx, TRIc)
    km = ap(w, Ax, 'mvkmvt', [J(w, Ax, lift(w, tp, Ax), hk)], '%s <_ ( %s x. ( Re ` %s ) )' % (ITG(TT, ABS2(sxi('t'))), KK, BILc))
    # rewrite the integrand: sxi ( t ) = DS ( x , t )
    Axt = '( %s /\\ t e. %s )' % (Ax, TT)
    tr = ap(w, Axt, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Axt, TT))], 't e. RR')
    Axtm = '( %s /\\ m e. %s )' % (Axt, FZM)
    vm = vals(Axtm, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (Axtm, FZM)), lift(w, xm, Axtm))
    EXm = '( exp ` ( _i x. ( -u ( log ` m ) x. t ) ) )'
    tm1 = dst(w, Axtm, [vm['c1'], dst(w, Axtm, [dst(w, Axtm, [dst(w, Axtm, [vm['l1']], 'oveq1d', '( ( %s ` m ) x. t ) = ( -u ( log ` m ) x. t )' % Lf)], 'oveq2d',
                                                                 '( _i x. ( ( %s ` m ) x. t ) ) = ( _i x. ( -u ( log ` m ) x. t ) )' % Lf)], 'fveq2d',
                                                 '( exp ` ( _i x. ( ( %s ` m ) x. t ) ) ) = %s' % (Lf, EXm))], 'oveq12d',
              '( ( %s ` m ) x. ( exp ` ( _i x. ( ( %s ` m ) x. t ) ) ) ) = ( ( ( A ` m ) x. %s ) x. %s )' % (Cx, Lf, CHV('x', 'm'), EXm))
    s1 = dst(w, Axt, [tm1], 'sumeq2dv', '%s = sum_ m e. %s ( ( ( A ` m ) x. %s ) x. %s )' % (sxi('t'), FZM, CHV('x', 'm'), EXm))
    subn, _ = w.congr('( ( ( A ` m ) x. %s ) x. %s )' % (CHV('x', 'm'), EXm), {'m': 'n'}, 'm = n', {'m': w.s([], 'id', '( m = n -> m = n )')})
    cbv = w.s([subn], 'cbvsumv', 'sum_ m e. %s ( ( ( A ` m ) x. %s ) x. %s ) = %s' % (FZM, CHV('x', 'm'), EXm, DS('x', 't')))
    sxe = eqt(w, Axt, s1, w.s([cbv], 'a1i', '( %s -> sum_ m e. %s ( ( ( A ` m ) x. %s ) x. %s ) = %s )' % (Axt, FZM, CHV('x', 'm'), EXm, DS('x', 't'))))
    ie = dst(w, Ax, [dst(w, Axt, [dst(w, Axt, [sxe], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (sxi('t'), DS('x', 't')))], 'oveq1d', '%s = %s' % (ABS2(sxi('t')), ABS2(DS('x', 't'))))],
             'itgeq2dv', '%s = %s' % (ITG(TT, ABS2(sxi('t'))), ITG(TT, ABS2(DS('x', 't')))))
    # rewrite BILc
    Axmn = '( ( %s /\\ m e. %s ) /\\ n e. %s )' % (Ax, FZM, FZM)
    mmem = lift(w, w.s([], 'simpr', '( ( %s /\\ m e. %s ) -> m e. %s )' % (Ax, FZM, FZM)), Axmn)
    nmem = w.s([], 'simpr', '( %s -> n e. %s )' % (Axmn, FZM))
    wm = vals(Axmn, 'm', mmem, lift(w, xm, Axmn)); wn = vals(Axmn, 'n', nmem, lift(w, xm, Axmn))
    TH2 = '( -u ( log ` m ) - -u ( log ` n ) )'
    TRIr = TRI(DT, TH2)
    thr = dst(w, Axmn, [wm['l1'], wn['l1']], 'oveq12d', '( ( %s ` m ) - ( %s ` n ) ) = %s' % (Lf, Lf, TH2))
    trr = w.rewrite(TRIc, {'( ( %s ` m ) - ( %s ` n ) )' % (Lf, Lf): (TH2, thr)}, Axmn)
    assert trr[1] == TRIr, trr[1]
    CMN = '( ( ( ( A ` m ) x. %s ) x. ( * ` ( ( A ` n ) x. %s ) ) ) x. %s )' % (CHV('x', 'm'), CHV('x', 'n'), TRIr)
    bt = dst(w, Axmn, [dst(w, Axmn, [wm['c1'], dst(w, Axmn, [wn['c1']], 'fveq2d', '( * ` ( %s ` n ) ) = ( * ` ( ( A ` n ) x. %s ) )' % (Cx, CHV('x', 'n')))], 'oveq12d',
                               '( ( %s ` m ) x. ( * ` ( %s ` n ) ) ) = ( ( ( A ` m ) x. %s ) x. ( * ` ( ( A ` n ) x. %s ) ) )' % (Cx, Cx, CHV('x', 'm'), CHV('x', 'n'))), trr[0]], 'oveq12d',
             '( ( ( %s ` m ) x. ( * ` ( %s ` n ) ) ) x. %s ) = %s' % (Cx, Cx, TRIc, CMN))
    # regroup the pair term: ( a_m a_n* TRI ) ( x_m x_n* )
    Wmn = '( ( ( A ` m ) x. ( * ` ( A ` n ) ) ) x. %s )' % TRIr
    XX = '( %s x. ( * ` %s ) )' % (CHV('x', 'm'), CHV('x', 'n'))
    cjm = w.s([wn['av'], wn['cv']], 'cjmuld', '( %s -> ( * ` ( ( A ` n ) x. %s ) ) = ( ( * ` ( A ` n ) ) x. ( * ` %s ) ) )' % (Axmn, CHV('x', 'n'), CHV('x', 'n')))
    # TRI is real (a ring atom)
    lvp = {'( A ` m )': ('CC', wm['av']), '( A ` n )': ('CC', wn['av']), CHV('x', 'm'): ('CC', wm['cv']), CHV('x', 'n'): ('CC', wn['cv']),
           '( log ` m )': ('RR', wm['lr']), '( log ` n )': ('RR', wn['lr']), 'T': ('RR+', lift(w, tp, Axmn)), '_pi': ('RR+', a1(w, Axmn, 'pirp', '_pi e. RR+'))}
    cp = Closure(w, Axmn, lvp)
    for t_ in [TRIr, '( * ` ( A ` n ) )', '( * ` %s )' % CHV('x', 'n')]:
        cp.leaf(t_, 'CC', cp.mem(t_, 'CC'))
    rg = ringeq(w, Axmn, '( ( ( ( A ` m ) x. %s ) x. ( ( * ` ( A ` n ) ) x. ( * ` %s ) ) ) x. %s )' % (CHV('x', 'm'), CHV('x', 'n'), TRIr), '( %s x. %s )' % (Wmn, XX), cp)
    bt2 = eqt(w, Axmn, eqt(w, Axmn, bt, dst(w, Axmn, [dst(w, Axmn, [cjm], 'oveq2d', '( ( ( A ` m ) x. %s ) x. ( * ` ( ( A ` n ) x. %s ) ) ) = ( ( ( A ` m ) x. %s ) x. ( ( * ` ( A ` n ) ) x. ( * ` %s ) ) )' % (
        CHV('x', 'm'), CHV('x', 'n'), CHV('x', 'm'), CHV('x', 'n')))], 'oveq1d', '%s = ( ( ( ( A ` m ) x. %s ) x. ( ( * ` ( A ` n ) ) x. ( * ` %s ) ) ) x. %s )' % (
        CMN, CHV('x', 'm'), CHV('x', 'n'), TRIr))), rg)     # term = W x XX
    Axm = '( %s /\\ m e. %s )' % (Ax, FZM)
    b1 = dst(w, Axm, [bt2], 'sumeq2dv', 'sum_ n e. %s ( ( ( %s ` m ) x. ( * ` ( %s ` n ) ) ) x. %s ) = sum_ n e. %s ( %s x. %s )' % (FZM, Cx, Cx, TRIc, FZM, Wmn, XX))
    BIL2 = 'sum_ m e. %s sum_ n e. %s ( %s x. %s )' % (FZM, FZM, Wmn, XX)
    b2 = dst(w, Ax, [b1], 'sumeq2dv', '%s = %s' % (BILc, BIL2))
    kx = w.s([km, dst(w, Ax, [dst(w, Ax, [b2], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (BILc, BIL2))], 'oveq2d', '( %s x. ( Re ` %s ) ) = ( %s x. ( Re ` %s ) )' % (KK, BILc, KK, BIL2))], 'breqtrd',
             '( %s -> %s <_ ( %s x. ( Re ` %s ) ) )' % (Ax, ITG(TT, ABS2(sxi('t'))), KK, BIL2))
    kx2 = w.s([ie, kx], 'eqbrtrrd', '( %s -> %s <_ ( %s x. ( Re ` %s ) ) )' % (Ax, ITG(TT, ABS2(DS('x', 't'))), KK, BIL2))
    # the integral is real: continuity of the exponential sum
    hkq = HK.replace('C', Cx).replace('( L ` a )', '( %s ` a )' % Lf) if False else None
    dvx = ap(w, Ax, 'mvsxdv', [hk], '( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (
        sxi('t'), 'sum_ m e. %s ( ( ( %s ` m ) x. ( _i x. ( %s ` m ) ) ) x. ( exp ` ( _i x. ( ( %s ` m ) x. t ) ) ) )' % (FZM, Cx, Lf, Lf), sxi('t'),
        'sum_ m e. %s ( ( ( %s ` m ) x. ( _i x. ( %s ` m ) ) ) x. ( exp ` ( _i x. ( ( %s ` m ) x. t ) ) ) )' % (FZM, Cx, Lf, Lf)))
    cn1 = w.s([dvx], 'simp2d', '( %s -> ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (Ax, sxi('t')))
    Axr = '( %s /\\ t e. RR )' % Ax
    trr_ = w.s([], 'simpr', '( %s -> t e. RR )' % Axr)
    def sxclx(ante, tst):
        Am_ = '( %s /\\ m e. %s )' % (ante, FZM)
        vv = vals(Am_, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (Am_, FZM)), lift(w, xm, Am_))
        ci_ = w.s([vv['c1'], w.s([vv['av'], vv['cv']], 'mulcld', '( %s -> %s e. CC )' % (Am_, vv['cval']))], 'eqeltrd', '( %s -> ( %s ` m ) e. CC )' % (Am_, Cx))
        li_ = w.s([vv['l1'], w.s([vv['lr']], 'renegcld', '( %s -> -u ( log ` m ) e. RR )' % Am_)], 'eqeltrd', '( %s -> ( %s ` m ) e. RR )' % (Am_, Lf))
        c_ = Closure(w, Am_, {'( %s ` m )' % Cx: ('CC', ci_), '( %s ` m )' % Lf: ('RR', li_), 't': ('RR', lift(w, tst, Am_)), '_i': ('CC', a1(w, Am_, 'ax-icn', '_i e. CC'))})
        return w.s([lift(w, fz, ante), c_.mem('( ( %s ` m ) x. ( exp ` ( _i x. ( ( %s ` m ) x. t ) ) ) )' % (Cx, Lf), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (ante, sxi('t')))
    cxr = Closure(w, Axr, {sxi('t'): ('CC', sxclx(Axr, trr_)), 't': ('RR', trr_)})
    cnb = CN(w, Ax, 't', 'RR', a1(w, Ax, 'ax-resscn', 'RR C_ CC'), Closure(w, Ax, {'T': ('RR+', lift(w, tp, Ax))}), cxr, known={sxi('t'): cn1})
    clx = Closure(w, Ax, {'T': ('RR+', lift(w, tp, Ax))})
    ibx = w.s([clx.mem('-u T', 'RR'), clx.mem('T', 'RR'), cnb(ABS2(sxi('t')))], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (Ax, TT, ABS2(sxi('t'))))
    cxt = Closure(w, Axt, {sxi('t'): ('CC', sxclx(Axt, tr))})
    irx = w.s([cxt.mem(ABS2(sxi('t')), 'RR'), ibx], 'itgrecl', '( %s -> %s e. RR )' % (Ax, ITG(TT, ABS2(sxi('t')))))
    irds = w.s([ie, irx], 'eqeltrrd' if False else 'id', 'x') if False else w.s([eqc(w, Ax, ie), irx], 'eqeltrd' if False else 'id', 'x') if False else \
        w.s([ie, irx], 'eqeltrrd', '( %s -> %s e. RR )' % (Ax, ITG(TT, ABS2(DS('x', 't')))))
    # the bilinear form at x is complex
    Amn0 = '( ( %s /\\ m e. %s ) /\\ n e. %s )' % (Ax, FZM, FZM)
    wcl = cp.mem('( %s x. %s )' % (Wmn, XX), 'CC')
    innr = w.s([lift(w, fz, Axm), wcl], 'fsumcl', '( %s -> sum_ n e. %s ( %s x. %s ) e. CC )' % (Axm, FZM, Wmn, XX))
    bil2c = w.s([lift(w, fz, Ax), innr], 'fsumcl', '( %s -> %s e. CC )' % (Ax, BIL2))
    clk = Closure(w, Ax, {'T': ('RR+', lift(w, tp, Ax)), '_pi': ('RR+', a1(w, Ax, 'pirp', '_pi e. RR+'))})
    rhsx = w.s([clk.mem(KK, 'RR'), w.s([bil2c], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, BIL2))], 'remulcld', '( %s -> ( %s x. ( Re ` %s ) ) e. RR )' % (Ax, KK, BIL2))
    SUMX = 'sum_ x e. %s ( %s x. ( Re ` %s ) )' % (Dd, KK, BIL2)
    fl = w.s([dfin, irds, rhsx, kx2], 'fsumle', '( %s -> sum_ x e. %s %s <_ %s )' % (A0, Dd, ITG(TT, ABS2(DS('x', 't'))), SUMX))
    reb = w.s([bil2c], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, BIL2))
    f1 = w.s([dfin, cl.mem(KK, 'CC'), w.s([reb], 'recnd', '( %s -> ( Re ` %s ) e. CC )' % (Ax, BIL2))], 'fsummulc2',
             '( %s -> ( %s x. sum_ x e. %s ( Re ` %s ) ) = %s )' % (A0, KK, Dd, BIL2, SUMX))
    TOT = 'sum_ x e. %s %s' % (Dd, BIL2)
    f2 = w.s([dfin, bil2c], 'fsumre', '( %s -> ( Re ` %s ) = sum_ x e. %s ( Re ` %s ) )' % (A0, TOT, Dd, BIL2))
    # exchange the sums: sum_ x sum_ m sum_ n = sum_ m sum_ n sum_ x
    Axmn_ = '( %s /\\ ( x e. %s /\\ m e. %s ) )' % (A0, Dd, FZM)
    INN = 'sum_ n e. %s ( %s x. %s )' % (FZM, Wmn, XX)
    # membership of INN under ( A0 /\\ ( x e. D /\\ m e. FZM ) )
    Aq = '( ( %s /\\ ( x e. %s /\\ m e. %s ) ) /\\ n e. %s )' % (A0, Dd, FZM, FZM)
    xq = lift(w, w.s([], 'simprl', '( %s -> x e. %s )' % (Axmn_, Dd)), Aq)
    mq = lift(w, w.s([], 'simprr', '( %s -> m e. %s )' % (Axmn_, FZM)), Aq)
    nq = w.s([], 'simpr', '( %s -> n e. %s )' % (Aq, FZM))
    def pv(ante, xs, ms, ns):
        mnn = ap(w, ante, 'elfznn', [ms], 'm e. NN'); nnn = ap(w, ante, 'elfznn', [ns], 'n e. NN')
        return Closure(w, ante, {'( A ` m )': ('CC', aval(w, ante, 'm', lift(w, aok, ante), ms)), '( A ` n )': ('CC', aval(w, ante, 'n', lift(w, aok, ante), ns)),
                                 CHV('x', 'm'): ('CC', chv(w, ante, 'm', None, xs, w.s([mnn], 'nnzd', '( %s -> m e. ZZ )' % ante))),
                                 CHV('x', 'n'): ('CC', chv(w, ante, 'n', None, xs, w.s([nnn], 'nnzd', '( %s -> n e. ZZ )' % ante))),
                                 '( log ` m )': ('RR', w.s([w.s([mnn], 'nnrpd', '( %s -> m e. RR+ )' % ante)], 'relogcld', '( %s -> ( log ` m ) e. RR )' % ante)),
                                 '( log ` n )': ('RR', w.s([w.s([nnn], 'nnrpd', '( %s -> n e. RR+ )' % ante)], 'relogcld', '( %s -> ( log ` n ) e. RR )' % ante)),
                                 'T': ('RR+', lift(w, tp, ante)), '_pi': ('RR+', a1(w, ante, 'pirp', '_pi e. RR+'))})
    cq = pv(Aq, xq, mq, nq)
    innq = w.s([lift(w, fz, Axmn_), cq.mem('( %s x. %s )' % (Wmn, XX), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Axmn_, INN))
    c1 = w.s([dfin, fz, innq], 'fsumcom', '( %s -> %s = sum_ m e. %s sum_ x e. %s %s )' % (A0, TOT, FZM, Dd, INN))
    Am = '( %s /\\ m e. %s )' % (A0, FZM)
    Ar = '( %s /\\ ( x e. %s /\\ n e. %s ) )' % (Am, Dd, FZM)
    cr = pv(Ar, w.s([], 'simprl', '( %s -> x e. %s )' % (Ar, Dd)), lift(w, w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM)), Ar), w.s([], 'simprr', '( %s -> n e. %s )' % (Ar, FZM)))
    c2 = w.s([lift(w, dfin, Am), lift(w, fz, Am), cr.mem('( %s x. %s )' % (Wmn, XX), 'CC')], 'fsumcom', '( %s -> sum_ x e. %s %s = sum_ n e. %s sum_ x e. %s ( %s x. %s ) )' % (Am, Dd, INN, FZM, Dd, Wmn, XX))
    SXX = 'sum_ x e. %s %s' % (Dd, XX)
    Amn = '( ( %s /\\ m e. %s ) /\\ n e. %s )' % (A0, FZM, FZM)
    Amnx = '( %s /\\ x e. %s )' % (Amn, Dd)
    cmx = pv(Amnx, w.s([], 'simpr', '( %s -> x e. %s )' % (Amnx, Dd)), lift(w, lift(w, w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM)), Amn), Amnx),
             lift(w, w.s([], 'simpr', '( %s -> n e. %s )' % (Amn, FZM)), Amnx))
    cmn = pv(Amn, None, lift(w, w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM)), Amn), w.s([], 'simpr', '( %s -> n e. %s )' % (Amn, FZM))) if False else None
    mnm = lift(w, w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM)), Amn); mnn_ = w.s([], 'simpr', '( %s -> n e. %s )' % (Amn, FZM))
    m_n = ap(w, Amn, 'elfznn', [mnm], 'm e. NN'); n_n = ap(w, Amn, 'elfznn', [mnn_], 'n e. NN')
    cmn = Closure(w, Amn, {'( A ` m )': ('CC', aval(w, Amn, 'm', lift(w, aok, Amn), mnm)), '( A ` n )': ('CC', aval(w, Amn, 'n', lift(w, aok, Amn), mnn_)),
                           'm': ('NN', m_n), 'n': ('NN', n_n), 'T': ('RR+', lift(w, tp, Amn)), 'N': ('NN', lift(w, nn, Amn)), '_pi': ('RR+', a1(w, Amn, 'pirp', '_pi e. RR+'))})
    mc = w.s([lift(w, dfin, Amn), cmn.mem(Wmn, 'CC'), cmx.mem(XX, 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ x e. %s ( %s x. %s ) )' % (Amn, Wmn, SXX, Dd, Wmn, XX))
    c3 = eqt(w, Am, c2, dst(w, Am, [eqc(w, Amn, mc)], 'sumeq2dv', 'sum_ n e. %s sum_ x e. %s ( %s x. %s ) = sum_ n e. %s ( %s x. %s )' % (FZM, Dd, Wmn, XX, FZM, Wmn, SXX)))
    TOT2 = 'sum_ m e. %s sum_ n e. %s ( %s x. %s )' % (FZM, FZM, Wmn, SXX)
    tot = eqt(w, A0, c1, dst(w, A0, [c3], 'sumeq2dv', 'sum_ m e. %s sum_ x e. %s %s = %s' % (FZM, Dd, INN, TOT2)))
    # the pair bound
    sxc = w.s([lift(w, dfin, Amn), cmx.mem(XX, 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Amn, SXX))
    IFs = 'if ( N || ( m - n ) , ( phi ` N ) , 0 )'
    mo = ap(w, Amn, 'mvorth', [w.s([lift(w, nn, Amn), cmn.mem('m', 'ZZ'), cmn.mem('n', 'ZZ')], '3jca', '( %s -> ( N e. NN /\\ m e. ZZ /\\ n e. ZZ ) )' % Amn)],
            '( abs ` %s ) <_ %s' % (SXX.replace(XX, '( %s x. ( * ` %s ) )' % (CHV('x', 'm'), CHV('x', 'n'))), IFs))
    b1_, b2_, _, cond = trige0(w, Amn, DT, TH2, None)
    trg = w.s([b1_, b2_, w.s([cmn.mem(DT, 'RR'), cmn.mem('( abs ` %s )' % TH2, 'RR'), w.s([], 'simpr', '( ( %s /\\ %s ) -> %s )' % (Amn, cond, cond))], 'subge0d' if False else 'id', 'x') if False else
               w.s([w.s([w.s([cmn.mem('( abs ` %s )' % TH2, 'RR')], 'adantr', '( ( %s /\\ %s ) -> ( abs ` %s ) e. RR )' % (Amn, cond, TH2)),
                          w.s([cmn.mem(DT, 'RR')], 'adantr', '( ( %s /\\ %s ) -> %s e. RR )' % (Amn, cond, DT))], 'subge0d', '( ( %s /\\ %s ) -> ( 0 <_ ( %s - ( abs ` %s ) ) <-> ( abs ` %s ) <_ %s ) )' % (
                   Amn, cond, DT, TH2, TH2, DT)), w.s([], 'simpr', '( ( %s /\\ %s ) -> %s )' % (Amn, cond, cond))], 'mpbird', '( ( %s /\\ %s ) -> 0 <_ ( %s - ( abs ` %s ) ) )' % (Amn, cond, DT, TH2)),
               w.s([w.s([], '0red', '( ( %s /\\ -. %s ) -> 0 e. RR )' % (Amn, cond))], 'leidd', '( ( %s /\\ -. %s ) -> 0 <_ 0 )' % (Amn, cond))], 'ifbothda', '( %s -> 0 <_ %s )' % (Amn, TRIr))
    cmn.leaf(TRIr, 'RR', cmn.mem(TRIr, 'RR'))
    AM, AN = '( abs ` ( A ` m ) )', '( abs ` ( A ` n ) )'
    aw1 = w.s([cmn.mem('( ( A ` m ) x. ( * ` ( A ` n ) ) )', 'CC'), cmn.mem(TRIr, 'CC')], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` ( ( A ` m ) x. ( * ` ( A ` n ) ) ) ) x. ( abs ` %s ) ) )' % (Amn, Wmn, TRIr))
    aw2 = w.s([cmn.mem('( A ` m )', 'CC'), cmn.mem('( * ` ( A ` n ) )', 'CC')], 'absmuld', '( %s -> ( abs ` ( ( A ` m ) x. ( * ` ( A ` n ) ) ) ) = ( %s x. ( abs ` ( * ` ( A ` n ) ) ) ) )' % (Amn, AM))
    aw3 = w.s([cmn.mem('( A ` n )', 'CC')], 'abscjd', '( %s -> ( abs ` ( * ` ( A ` n ) ) ) = %s )' % (Amn, AN))
    aw4 = w.s([cmn.mem(TRIr, 'RR'), trg], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (Amn, TRIr, TRIr))
    AW = eqt(w, Amn, aw1, dst(w, Amn, [eqt(w, Amn, aw2, dst(w, Amn, [aw3], 'oveq2d', '( %s x. ( abs ` ( * ` ( A ` n ) ) ) ) = ( %s x. %s )' % (AM, AM, AN))), aw4], 'oveq12d',
                                   '( ( abs ` ( ( A ` m ) x. ( * ` ( A ` n ) ) ) ) x. ( abs ` %s ) ) = ( ( %s x. %s ) x. %s )' % (TRIr, AM, AN, TRIr)))
    ap_ = w.s([cmn.mem(Wmn, 'CC'), sxc], 'absmuld', '( %s -> ( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Amn, Wmn, SXX, Wmn, SXX))
    wge = w.s([cmn.mem(Wmn, 'CC')], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Amn, Wmn))
    cmn.leaf(IFs, 'RR', w.s([cmn.mem('( phi ` N )', 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % Amn)], 'ifcld', '( %s -> %s e. RR )' % (Amn, IFs)))
    lm = w.s([w.s([sxc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Amn, SXX)), cmn.mem(IFs, 'RR'), cmn.mem('( abs ` %s )' % Wmn, 'RR'), wge, mo], 'lemul2ad',
             '( %s -> ( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( abs ` %s ) x. %s ) )' % (Amn, Wmn, SXX, Wmn, IFs))
    rgc = Closure(w, Amn, {AM: ('RR', cmn.mem(AM, 'RR')), AN: ('RR', cmn.mem(AN, 'RR')), TRIr: ('RR', cmn.mem(TRIr, 'RR')), IFs: ('RR', cmn.mem(IFs, 'RR'))})
    rr2 = eqt(w, Amn, dst(w, Amn, [AW], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (Wmn, IFs, AM, AN, TRIr, IFs)),
              ringeq(w, Amn, '( ( ( %s x. %s ) x. %s ) x. %s )' % (AM, AN, TRIr, IFs), WPAIR(), rgc))
    pb = w.s([w.s([ap_, lm], 'eqbrtrd', '( %s -> ( abs ` ( %s x. %s ) ) <_ ( ( abs ` %s ) x. %s ) )' % (Amn, Wmn, SXX, Wmn, IFs)), rr2], 'breqtrd',
             '( %s -> ( abs ` ( %s x. %s ) ) <_ %s )' % (Amn, Wmn, SXX, WPAIR()))
    # sum up: Re TOT <_ | TOT | <_ sum sum | . | <_ sum sum WPAIR
    Amn_c = cmn
    pc = w.s([cmn.mem(Wmn, 'CC'), sxc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Amn, Wmn, SXX))
    in1 = w.s([lift(w, fz, Am), pc], 'fsumcl', '( %s -> sum_ n e. %s ( %s x. %s ) e. CC )' % (Am, FZM, Wmn, SXX))
    fa1 = w.s([fz, in1], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ m e. %s ( abs ` sum_ n e. %s ( %s x. %s ) ) )' % (A0, TOT2, FZM, FZM, Wmn, SXX))
    fa2 = w.s([lift(w, fz, Am), pc], 'fsumabs', '( %s -> ( abs ` sum_ n e. %s ( %s x. %s ) ) <_ sum_ n e. %s ( abs ` ( %s x. %s ) ) )' % (Am, FZM, Wmn, SXX, FZM, Wmn, SXX))
    wpr = cmn.mem(WPAIR(), 'RR')
    fl2 = w.s([lift(w, fz, Am), w.s([pc], 'abscld', '( %s -> ( abs ` ( %s x. %s ) ) e. RR )' % (Amn, Wmn, SXX)), wpr, pb], 'fsumle',
              '( %s -> sum_ n e. %s ( abs ` ( %s x. %s ) ) <_ sum_ n e. %s %s )' % (Am, FZM, Wmn, SXX, FZM, WPAIR()))
    SWN = 'sum_ n e. %s %s' % (FZM, WPAIR())
    rin = w.s([lift(w, fz, Am), wpr], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SWN))
    ai = w.s([w.s([in1], 'abscld', '( %s -> ( abs ` sum_ n e. %s ( %s x. %s ) ) e. RR )' % (Am, FZM, Wmn, SXX)),
              w.s([lift(w, fz, Am), w.s([pc], 'abscld', '( %s -> ( abs ` ( %s x. %s ) ) e. RR )' % (Amn, Wmn, SXX))], 'fsumrecl', '( %s -> sum_ n e. %s ( abs ` ( %s x. %s ) ) e. RR )' % (Am, FZM, Wmn, SXX)),
              rin, fa2, fl2], 'letrd', '( %s -> ( abs ` sum_ n e. %s ( %s x. %s ) ) <_ %s )' % (Am, FZM, Wmn, SXX, SWN))
    fl3 = w.s([fz, w.s([in1], 'abscld', '( %s -> ( abs ` sum_ n e. %s ( %s x. %s ) ) e. RR )' % (Am, FZM, Wmn, SXX)), rin, ai], 'fsumle',
              '( %s -> sum_ m e. %s ( abs ` sum_ n e. %s ( %s x. %s ) ) <_ sum_ m e. %s %s )' % (A0, FZM, FZM, Wmn, SXX, FZM, SWN))
    SS = 'sum_ m e. %s %s' % (FZM, SWN)
    tot2c = w.s([fz, in1], 'fsumcl', '( %s -> %s e. CC )' % (A0, TOT2))
    rl = ap(w, A0, 'releabs', [tot2c], '( Re ` %s ) <_ ( abs ` %s )' % (TOT2, TOT2))
    cl.leaf('( Re ` %s )' % TOT2, 'RR', w.s([tot2c], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, TOT2)))
    cl.leaf('( abs ` %s )' % TOT2, 'RR', w.s([tot2c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, TOT2)))
    cl.leaf('sum_ m e. %s ( abs ` sum_ n e. %s ( %s x. %s ) )' % (FZM, FZM, Wmn, SXX), 'RR',
            w.s([fz, w.s([in1], 'abscld', '( %s -> ( abs ` sum_ n e. %s ( %s x. %s ) ) e. RR )' % (Am, FZM, Wmn, SXX))], 'fsumrecl', '( %s -> sum_ m e. %s ( abs ` sum_ n e. %s ( %s x. %s ) ) e. RR )' % (A0, FZM, FZM, Wmn, SXX)))
    cl.leaf(SS, 'RR', w.s([fz, rin], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SS)))
    ree = dst(w, A0, [tot], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (TOT, TOT2))
    cl.leaf('( Re ` %s )' % TOT, 'RR', w.s([ree, cl.mem('( Re ` %s )' % TOT2, 'RR')], 'eqeltrd', '( %s -> ( Re ` %s ) e. RR )' % (A0, TOT)))
    reb2 = linarith(w, A0, [ree, rl, fa1, fl3], '( Re ` %s ) <_ %s' % (TOT, SS), closure=cl)
    kg = ltle(w, A0, cl, cl.gt0(KK))
    kb = w.s([cl.mem('( Re ` %s )' % TOT, 'RR'), cl.mem(SS, 'RR'), cl.mem(KK, 'RR'), kg, reb2], 'lemul2ad', '( %s -> ( %s x. ( Re ` %s ) ) <_ ( %s x. %s ) )' % (A0, KK, TOT, KK, SS))
    rhs_eq = eqt(w, A0, eqc(w, A0, f1), dst(w, A0, [eqc(w, A0, f2)], 'oveq2d', '( %s x. sum_ x e. %s ( Re ` %s ) ) = ( %s x. ( Re ` %s ) )' % (KK, Dd, BIL2, KK, TOT)))
    w.s([w.s([fl, rhs_eq], 'breqtrd', '( %s -> sum_ x e. %s %s <_ ( %s x. ( Re ` %s ) ) )' % (A0, Dd, ITG(TT, ABS2(DS('x', 't'))), KK, TOT)), kb], 'letrd' if False else 'id', 'x') if False else None
    lhsr = w.s([dfin, irds], 'fsumrecl', '( %s -> sum_ x e. %s %s e. RR )' % (A0, Dd, ITG(TT, ABS2(DS('x', 't')))))
    le_ = w.s([lhsr, cl.mem('( %s x. ( Re ` %s ) )' % (KK, TOT), 'RR'), cl.mem('( %s x. %s )' % (KK, SS), 'RR'),
         w.s([fl, rhs_eq], 'breqtrd', '( %s -> sum_ x e. %s %s <_ ( %s x. ( Re ` %s ) ) )' % (A0, Dd, ITG(TT, ABS2(DS('x', 't'))), KK, TOT)), kb], 'letrd',
        '( %s -> sum_ x e. %s %s <_ ( %s x. %s ) )' % (A0, Dd, ITG(TT, ABS2(DS('x', 't'))), KK, SS))
    J(w, A0, lhsr, le_)
    qedlast(w)
    go(w)


def WW(m, n):
    return 'if ( ( N || ( %s - %s ) /\\ ( abs ` ( ( log ` %s ) - ( log ` %s ) ) ) < %s ) , 1 , 0 )' % (n, m, n, m, DT)


def mvmvc2():
    w = W('mvmvc2', 'mean_value_chars, the counting step: ( 12 T ^ 2 / pi ) sum_ m sum_ n | a_m | | a_n | TRI ( phi ( N ) if N || m - n ) <_ 100 ( M + N T ) sum | a_n | ^ 2 (term_bound, symmetrisation, sum_window_le).')
    A0 = HMV
    P = parts(w, A0)
    nn, tp, mn0, aok = P['N e. NN'], P['T e. RR+'], P['M e. NN0'], P[AOK]
    cl = Closure(w, A0, {'N': ('NN', nn), 'T': ('RR+', tp), 'M': ('NN0', mn0), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZM))
    PH = '( phi ` N )'
    C = '( ( ( 4 x. M ) / ( N x. T ) ) + 1 )'
    Am = '( %s /\\ m e. %s )' % (A0, FZM)
    Amn = '( ( %s /\\ m e. %s ) /\\ n e. %s )' % (A0, FZM, FZM)
    mm_ = lift(w, w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM)), Amn); nm_ = w.s([], 'simpr', '( %s -> n e. %s )' % (Amn, FZM))
    mN = ap(w, Amn, 'elfznn', [mm_], 'm e. NN'); nN = ap(w, Amn, 'elfznn', [nm_], 'n e. NN')
    am = aval(w, Amn, 'm', lift(w, aok, Amn), mm_); an = aval(w, Amn, 'n', lift(w, aok, Amn), nm_)
    c = Closure(w, Amn, {'( A ` m )': ('CC', am), '( A ` n )': ('CC', an), 'm': ('NN', mN), 'n': ('NN', nN), 'N': ('NN', lift(w, nn, Amn)), 'T': ('RR+', lift(w, tp, Amn)),
                         '_pi': ('RR+', a1(w, Amn, 'pirp', '_pi e. RR+'))})
    a = '( abs ` ( A ` m ) )'; b = '( abs ` ( A ` n ) )'
    TH2 = '( -u ( log ` m ) - -u ( log ` n ) )'
    TRIr = TRI(DT, TH2); IFs = 'if ( N || ( m - n ) , %s , 0 )' % PH; wv = WW('m', 'n')
    for t_ in [a, b]:
        c.leaf(t_, 'RR', c.mem(t_, 'RR'))
    a0 = w.s([am], 'absge0d', '( %s -> 0 <_ %s )' % (Amn, a)); b0 = w.s([an], 'absge0d', '( %s -> 0 <_ %s )' % (Amn, b))
    # p1: a b <_ ( a ^ 2 + b ^ 2 ) / 2
    sq = w.s([c.mem('( %s - %s )' % (a, b), 'RR')], 'sqge0d', '( %s -> 0 <_ ( ( %s - %s ) ^ 2 ) )' % (Amn, a, b))
    se = ringeqp(w, Amn, '( ( %s - %s ) ^ 2 )' % (a, b), '( ( ( %s ^ 2 ) + ( %s ^ 2 ) ) - ( 2 x. ( %s x. %s ) ) )' % (a, b, a, b), Closure(w, Amn, {a: ('RR', c.mem(a, 'RR')), b: ('RR', c.mem(b, 'RR'))}))
    for t_ in ['( ( %s - %s ) ^ 2 )' % (a, b), '( %s ^ 2 )' % a, '( %s ^ 2 )' % b, '( %s x. %s )' % (a, b)]:
        c.leaf(t_, 'RR', c.mem(t_, 'RR'))
    p1 = linarith(w, Amn, [sq, se], '( %s x. %s ) <_ ( ( ( %s ^ 2 ) + ( %s ^ 2 ) ) / 2 )' % (a, b, a, b), closure=c)
    # p2: TRI IF <_ PH ( DT w ) by cases
    phr = c.mem(PH, 'RR'); ph0 = ltle(w, Amn, c, c.gt0(PH))
    dtr = c.mem(DT, 'RR'); dt0 = ltle(w, Amn, c, c.gt0(DT))
    thr = c.mem(TH2, 'RR')
    wr = w.s([a1(w, Amn, '1re', '1 e. RR'), w.s([], '0red', '( %s -> 0 e. RR )' % Amn)], 'ifcld', '( %s -> %s e. RR )' % (Amn, wv))
    b1 = w.s([], 'breq2', '( 1 = %s -> ( 0 <_ 1 <-> 0 <_ %s ) )' % (wv, wv)); b2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (wv, wv))
    cw = '( N || ( n - m ) /\\ ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s )' % DT
    w0 = w.s([b1, b2, w.s([a1(w, '( %s /\\ %s )' % (Amn, cw), '0le1', '0 <_ 1')], 'id', 'x') if False else a1(w, '( %s /\\ %s )' % (Amn, cw), '0le1', '0 <_ 1'),
              w.s([w.s([], '0red', '( ( %s /\\ -. %s ) -> 0 e. RR )' % (Amn, cw))], 'leidd', '( ( %s /\\ -. %s ) -> 0 <_ 0 )' % (Amn, cw))], 'ifbothda', '( %s -> 0 <_ %s )' % (Amn, wv))
    c.leaf(wv, 'RR', wr); c.leaf(TRIr, 'RR', c.mem(TRIr, 'RR'))
    c.leaf(IFs, 'RR', w.s([phr, w.s([], '0red', '( %s -> 0 e. RR )' % Amn)], 'ifcld', '( %s -> %s e. RR )' % (Amn, IFs)))
    rhs0 = w.s([phr, c.mem('( %s x. %s )' % (DT, wv), 'RR'), ph0, w.s([dtr, wr, dt0, w0], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (Amn, DT, wv))], 'mulge0d',
               '( %s -> 0 <_ ( %s x. ( %s x. %s ) ) )' % (Amn, PH, DT, wv))
    RHS2 = '( %s x. ( %s x. %s ) )' % (PH, DT, wv)
    LHS2 = '( %s x. %s )' % (TRIr, IFs)
    D1 = 'N || ( m - n )'
    # case not D1: IF = 0
    Bn = '( %s /\\ -. %s )' % (Amn, D1)
    z = eqt(w, Bn, dst(w, Bn, [ap(w, Bn, 'iffalse', [w.s([], 'simpr', '( %s -> -. %s )' % (Bn, D1))], '%s = 0' % IFs)], 'oveq2d', '%s = ( %s x. 0 )' % (LHS2, TRIr)),
            w.s([lift(w, c.mem(TRIr, 'CC'), Bn)], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (Bn, TRIr)))
    kn = w.s([z, lift(w, rhs0, Bn)], 'eqbrtrd', '( %s -> %s <_ %s )' % (Bn, LHS2, RHS2))
    # case D1
    By = '( %s /\\ %s )' % (Amn, D1)
    ify = ap(w, By, 'iftrue', [w.s([], 'simpr', '( %s -> %s )' % (By, D1))], '%s = %s' % (IFs, PH))
    cy = Closure(w, By, {PH: ('RR', lift(w, phr, By)), DT: ('RR', lift(w, dtr, By)), TH2: ('RR', lift(w, thr, By)), TRIr: ('RR', lift(w, c.mem(TRIr, 'RR'), By)), wv: ('RR', lift(w, wr, By))})
    # the two conditions: N || ( n - m ) and | log n - log m | = | TH2 |
    dn = w.s([w.s([w.s([lift(w, c.mem('N', 'ZZ'), By), lift(w, c.mem('( m - n )', 'ZZ'), By), w.inst('dvdsnegb')], 'syl2anc', '( %s -> ( %s <-> N || -u ( m - n ) ) )' % (By, D1)),
                   w.s([], 'simpr', '( %s -> %s )' % (By, D1))], 'mpbid' if False else 'id', 'x') if False else
              w.s([w.s([], 'simpr', '( %s -> %s )' % (By, D1)), w.s([lift(w, c.mem('N', 'ZZ'), By), lift(w, c.mem('( m - n )', 'ZZ'), By), w.inst('dvdsnegb')], 'syl2anc', '( %s -> ( %s <-> N || -u ( m - n ) ) )' % (By, D1))],
                  'mpbid', '( %s -> N || -u ( m - n ) )' % By),
              w.s([lift(w, c.mem('m', 'CC'), By), lift(w, c.mem('n', 'CC'), By)], 'negsubdi2d', '( %s -> -u ( m - n ) = ( n - m ) )' % By)], 'breqtrd' if False else 'id', 'x') if False else None
    dnm0 = w.s([w.s([], 'simpr', '( %s -> %s )' % (By, D1)), w.s([lift(w, c.mem('N', 'ZZ'), By), lift(w, c.mem('( m - n )', 'ZZ'), By), w.inst('dvdsnegb')], 'syl2anc', '( %s -> ( %s <-> N || -u ( m - n ) ) )' % (By, D1))],
               'mpbid', '( %s -> N || -u ( m - n ) )' % By)
    dnm = w.s([dnm0, w.s([lift(w, c.mem('m', 'CC'), By), lift(w, c.mem('n', 'CC'), By)], 'negsubdi2d', '( %s -> -u ( m - n ) = ( n - m ) )' % By)], 'breqtrd', '( %s -> N || ( n - m ) )' % By)
    ce = Closure(w, By, {'( log ` m )': ('RR', lift(w, c.mem('( log ` m )', 'RR'), By)), '( log ` n )': ('RR', lift(w, c.mem('( log ` n )', 'RR'), By))})
    the = ringeq(w, By, TH2, '( ( log ` n ) - ( log ` m ) )', ce)
    athe = dst(w, By, [the], 'fveq2d', '( abs ` %s ) = ( abs ` ( ( log ` n ) - ( log ` m ) ) )' % TH2)
    C2 = '( abs ` %s ) < %s' % (TH2, DT)
    # sub-case | TH2 | < DT: w = 1, TRI <_ DT
    B2 = '( %s /\\ %s )' % (By, C2)
    lt2 = w.s([], 'simpr', '( %s -> %s )' % (B2, C2))
    c2b = w.s([lift(w, dnm, B2), w.s([lift(w, athe, B2), lt2], 'eqbrtrrd', '( %s -> ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s )' % (B2, DT))], 'jca', '( %s -> %s )' % (B2, cw))
    w1 = ap(w, B2, 'iftrue', [c2b], '%s = 1' % wv)
    le2 = ltle(w, B2, Closure(w, B2, {TH2: ('RR', lift(w, thr, B2)), DT: ('RR', lift(w, dtr, B2))}), lt2) if False else \
        w.s([w.s([lift(w, thr, B2)], 'abscld' if False else 'id', 'x') if False else lift(w, cy.mem('( abs ` %s )' % TH2, 'RR'), B2), lift(w, dtr, B2), lt2], 'ltled', '( %s -> ( abs ` %s ) <_ %s )' % (B2, TH2, DT))
    t2 = ap(w, B2, 'iftrue', [le2], '%s = ( %s - ( abs ` %s ) )' % (TRIr, DT, TH2))
    cb2 = Closure(w, B2, {PH: [('RR', lift(w, phr, B2)), ('ge0', lift(w, ph0, B2))], DT: ('RR', lift(w, dtr, B2)), TH2: ('RR', lift(w, thr, B2)), TRIr: ('RR', lift(w, c.mem(TRIr, 'RR'), B2)),
                          wv: ('RR', lift(w, wr, B2)), IFs: ('RR', lift(w, c.mem(IFs, 'RR'), B2))})
    cb2.leaf('( abs ` %s )' % TH2, 'RR', cb2.mem('( abs ` %s )' % TH2, 'RR'))
    tle = linarith(w, B2, [t2, w.s([lift(w, thr, B2) if False else w.s([lift(w, c.mem(TH2, 'CC'), B2)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (B2, TH2))], 'id', 'x') if False else
                            w.s([lift(w, c.mem(TH2, 'CC'), B2)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (B2, TH2))], '%s <_ %s' % (TRIr, DT), closure=cb2)
    m2 = w.s([cb2.mem(TRIr, 'RR'), cb2.mem(DT, 'RR'), cb2.mem(PH, 'RR'), lift(w, ph0, B2), tle], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (B2, TRIr, PH, DT, PH))
    for t_ in ['( %s x. %s )' % (TRIr, PH), '( %s x. %s )' % (DT, PH), LHS2, RHS2, '( %s x. %s )' % (DT, wv)]:
        cb2.leaf(t_, 'RR', cb2.mem(t_, 'RR'))
    rcl = Closure(w, B2, {TRIr: ('RR', lift(w, c.mem(TRIr, 'RR'), B2)), PH: ('RR', lift(w, phr, B2)), DT: ('RR', lift(w, dtr, B2))})
    e_l = eqt(w, B2, dst(w, B2, [lift(w, ify, B2)], 'oveq2d', '%s = ( %s x. %s )' % (LHS2, TRIr, PH)), w.s([w.s([], 'id', 'x')], 'id', 'x') if False else
              w.s([cb2.mem(TRIr, 'CC'), cb2.mem(PH, 'CC')], 'mulcomd' if False else 'id', 'x') if False else dst(w, B2, [w.s([], 'id', 'x')], 'id', 'x') if False else
              w.s([w.s([], 'eqidd' if False else 'id', 'x')], 'id', 'x') if False else w.s([], 'eqidd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (B2, TRIr, PH, TRIr, PH)))
    e_r = eqt(w, B2, dst(w, B2, [dst(w, B2, [w1], 'oveq2d', '( %s x. %s ) = ( %s x. 1 )' % (DT, wv, DT))], 'oveq2d', '%s = ( %s x. ( %s x. 1 ) )' % (RHS2, PH, DT)),
              ringeq(w, B2, '( %s x. ( %s x. 1 ) )' % (PH, DT), '( %s x. %s )' % (DT, PH), rcl))
    k22 = linarith(w, B2, [e_l, m2, e_r], '%s <_ %s' % (LHS2, RHS2), closure=cb2)
    # sub-case not: TRI <_ 0
    B3 = '( %s /\\ -. %s )' % (By, C2)
    n3 = w.s([], 'simpr', '( %s -> -. %s )' % (B3, C2))
    cb3 = Closure(w, B3, {TH2: ('RR', lift(w, thr, B3)), DT: ('RR', lift(w, dtr, B3))})
    cb3.leaf('( abs ` %s )' % TH2, 'RR', cb3.mem('( abs ` %s )' % TH2, 'RR'))
    ge3 = w.s([n3, w.s([cb3.mem(DT, 'RR'), cb3.mem('( abs ` %s )' % TH2, 'RR')], 'lenltd', '( %s -> ( %s <_ ( abs ` %s ) <-> -. %s ) )' % (B3, DT, TH2, C2))], 'mpbird',
              '( %s -> %s <_ ( abs ` %s ) )' % (B3, DT, TH2))
    cond = '( abs ` %s ) <_ %s' % (TH2, DT)
    bb1 = w.s([], 'breq1', '( ( %s - ( abs ` %s ) ) = %s -> ( ( %s - ( abs ` %s ) ) <_ 0 <-> %s <_ 0 ) )' % (DT, TH2, TRIr, DT, TH2, TRIr))
    bb2 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ 0 <-> %s <_ 0 ) )' % (TRIr, TRIr))
    B3c = '( %s /\\ %s )' % (B3, cond)
    cb3c = Closure(w, B3c, {TH2: ('RR', lift(w, thr, B3c)), DT: ('RR', lift(w, dtr, B3c))})
    cb3c.leaf('( abs ` %s )' % TH2, 'RR', cb3c.mem('( abs ` %s )' % TH2, 'RR'))
    tl = linarith(w, B3c, [lift(w, ge3, B3c)], '( %s - ( abs ` %s ) ) <_ 0' % (DT, TH2), closure=cb3c)
    t0_ = w.s([bb1, bb2, tl, w.s([w.s([], '0red', '( ( %s /\\ -. %s ) -> 0 e. RR )' % (B3, cond))], 'leidd', '( ( %s /\\ -. %s ) -> 0 <_ 0 )' % (B3, cond))], 'ifbothda', '( %s -> %s <_ 0 )' % (B3, TRIr))
    m3 = w.s([lift(w, c.mem(TRIr, 'RR'), B3), w.s([], '0red', '( %s -> 0 e. RR )' % B3), lift(w, phr, B3), lift(w, ph0, B3), t0_], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( 0 x. %s ) )' % (B3, TRIr, PH, PH))
    z3 = w.s([lift(w, c.mem(PH, 'CC'), B3)], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (B3, PH))
    cb33 = Closure(w, B3, {})
    for t_, st_ in [('( %s x. %s )' % (TRIr, PH), lift(w, c.mem('( %s x. %s )' % (TRIr, PH), 'RR'), B3)), ('( 0 x. %s )' % PH, lift(w, c.mem('( 0 x. %s )' % PH, 'RR'), B3)),
                    (LHS2, lift(w, c.mem(LHS2, 'RR'), B3)), (RHS2, lift(w, c.mem(RHS2, 'RR'), B3))]:
        cb33.leaf(t_, 'RR', st_)
    el3 = dst(w, B3, [lift(w, ify, B3)], 'oveq2d', '%s = ( %s x. %s )' % (LHS2, TRIr, PH))
    k33 = linarith(w, B3, [el3, m3, z3, lift(w, rhs0, B3)], '%s <_ %s' % (LHS2, RHS2), closure=cb33)
    ky = w.s([k22, k33, w.s([w.s([], 'exmid', '( %s \\/ -. %s )' % (C2, C2))], 'a1i', '( %s -> ( %s \\/ -. %s ) )' % (By, C2, C2))], 'mpjaodan', '( %s -> %s <_ %s )' % (By, LHS2, RHS2))
    p2 = w.s([ky, kn, w.s([w.s([], 'exmid', '( %s \\/ -. %s )' % (D1, D1))], 'a1i', '( %s -> ( %s \\/ -. %s ) )' % (Amn, D1, D1))], 'mpjaodan', '( %s -> %s <_ %s )' % (Amn, LHS2, RHS2))
    # p3: the pair term
    b1_, b2_, _, cnd = trige0(w, Amn, DT, TH2, None)
    trg = w.s([b1_, b2_, w.s([w.s([w.s([c.mem('( abs ` %s )' % TH2, 'RR')], 'adantr', '( ( %s /\\ %s ) -> ( abs ` %s ) e. RR )' % (Amn, cnd, TH2)),
                                   w.s([dtr], 'adantr', '( ( %s /\\ %s ) -> %s e. RR )' % (Amn, cnd, DT))], 'subge0d', '( ( %s /\\ %s ) -> ( 0 <_ ( %s - ( abs ` %s ) ) <-> ( abs ` %s ) <_ %s ) )' % (
                                   Amn, cnd, DT, TH2, TH2, DT)), w.s([], 'simpr', '( ( %s /\\ %s ) -> %s )' % (Amn, cnd, cnd))], 'mpbird', '( ( %s /\\ %s ) -> 0 <_ ( %s - ( abs ` %s ) ) )' % (Amn, cnd, DT, TH2)),
               w.s([w.s([], '0red', '( ( %s /\\ -. %s ) -> 0 e. RR )' % (Amn, cnd))], 'leidd', '( ( %s /\\ -. %s ) -> 0 <_ 0 )' % (Amn, cnd))], 'ifbothda', '( %s -> 0 <_ %s )' % (Amn, TRIr))
    ib1 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (PH, IFs, PH, IFs)); ib2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IFs, IFs))
    ifg = w.s([ib1, ib2, w.s([ph0], 'adantr', '( ( %s /\\ %s ) -> 0 <_ %s )' % (Amn, D1, PH)), w.s([w.s([], '0red', '( ( %s /\\ -. %s ) -> 0 e. RR )' % (Amn, D1))], 'leidd', '( ( %s /\\ -. %s ) -> 0 <_ 0 )' % (Amn, D1))],
              'ifbothda', '( %s -> 0 <_ %s )' % (Amn, IFs))
    l20 = w.s([c.mem(TRIr, 'RR'), c.mem(IFs, 'RR'), trg, ifg], 'mulge0d', '( %s -> 0 <_ %s )' % (Amn, LHS2))
    ab0 = w.s([c.mem(a, 'RR'), c.mem(b, 'RR'), a0, b0], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (Amn, a, b))
    AB2 = '( ( ( %s ^ 2 ) + ( %s ^ 2 ) ) / 2 )' % (a, b)
    p3 = w.s([c.mem('( %s x. %s )' % (a, b), 'RR'), c.mem(AB2, 'RR'), c.mem(LHS2, 'RR'), c.mem(RHS2, 'RR'), ab0, l20, p1, p2], 'lemul12ad',
             '( %s -> ( ( %s x. %s ) x. %s ) <_ ( %s x. %s ) )' % (Amn, a, b, LHS2, AB2, RHS2))
    K2 = '( ( %s x. %s ) / 2 )' % (PH, DT)
    Rv = '( ( %s ^ 2 ) x. %s )' % (a, wv); Sv = '( ( %s ^ 2 ) x. %s )' % (b, wv)
    rc = Closure(w, Amn, {x_: ('RR', c.mem(x_, 'RR')) for x_ in ['( %s ^ 2 )' % a, '( %s ^ 2 )' % b, PH, DT, wv]})
    p4 = ringeq(w, Amn, '( %s x. %s )' % (AB2, RHS2), '( %s x. ( %s + %s ) )' % (K2, Rv, Sv), rc)
    assert WPAIR() == '( ( %s x. %s ) x. %s )' % (a, b, LHS2)
    pp = w.s([p3, p4], 'breqtrd', '( %s -> %s <_ ( %s x. ( %s + %s ) ) )' % (Amn, WPAIR(), K2, Rv, Sv))
    # sums
    SWP = 'sum_ n e. %s %s' % (FZM, WPAIR()); SRS = 'sum_ n e. %s ( %s x. ( %s + %s ) )' % (FZM, K2, Rv, Sv)
    f1 = w.s([lift(w, fz, Am), c.mem(WPAIR(), 'RR'), c.mem('( %s x. ( %s + %s ) )' % (K2, Rv, Sv), 'RR'), pp], 'fsumle', '( %s -> %s <_ %s )' % (Am, SWP, SRS))
    cam = Closure(w, Am, {'N': ('NN', lift(w, nn, Am)), 'T': ('RR+', lift(w, tp, Am)), '_pi': ('RR+', a1(w, Am, 'pirp', '_pi e. RR+'))})
    f2 = w.s([fz, w.s([lift(w, fz, Am), c.mem(WPAIR(), 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SWP)), w.s([lift(w, fz, Am), c.mem('( %s x. ( %s + %s ) )' % (K2, Rv, Sv), 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SRS)), f1],
             'fsumle', '( %s -> sum_ m e. %s %s <_ sum_ m e. %s %s )' % (A0, FZM, SWP, FZM, SRS))
    # sum sum K2 ( R + S ) = K2 ( sum sum R + sum sum S )
    g1 = w.s([lift(w, fz, Am), cam.mem(K2, 'CC'), c.mem('( %s + %s )' % (Rv, Sv), 'CC')], 'fsummulc2', '( %s -> ( %s x. sum_ n e. %s ( %s + %s ) ) = %s )' % (Am, K2, FZM, Rv, Sv, SRS))
    g2 = w.s([lift(w, fz, Am), c.mem(Rv, 'CC'), c.mem(Sv, 'CC')], 'fsumadd', '( %s -> sum_ n e. %s ( %s + %s ) = ( sum_ n e. %s %s + sum_ n e. %s %s ) )' % (Am, FZM, Rv, Sv, FZM, Rv, FZM, Sv))
    SR = 'sum_ n e. %s %s' % (FZM, Rv); SSv = 'sum_ n e. %s %s' % (FZM, Sv)
    g3 = eqt(w, Am, eqc(w, Am, g1), dst(w, Am, [g2], 'oveq2d', '( %s x. sum_ n e. %s ( %s + %s ) ) = ( %s x. ( %s + %s ) )' % (K2, FZM, Rv, Sv, K2, SR, SSv)))
    srr = w.s([lift(w, fz, Am), c.mem(Rv, 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Am, SR)); ssr = w.s([lift(w, fz, Am), c.mem(Sv, 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Am, SSv))
    g4 = w.s([fz, cl.mem(K2, 'CC'), w.s([srr, ssr], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (Am, SR, SSv))], 'fsummulc2',
             '( %s -> ( %s x. sum_ m e. %s ( %s + %s ) ) = sum_ m e. %s ( %s x. ( %s + %s ) ) )' % (A0, K2, FZM, SR, SSv, FZM, K2, SR, SSv))
    g5 = w.s([fz, srr, ssr], 'fsumadd', '( %s -> sum_ m e. %s ( %s + %s ) = ( sum_ m e. %s %s + sum_ m e. %s %s ) )' % (A0, FZM, SR, SSv, FZM, SR, FZM, SSv))
    SSR = 'sum_ m e. %s %s' % (FZM, SR); SSS = 'sum_ m e. %s %s' % (FZM, SSv)
    TOTRS = 'sum_ m e. %s %s' % (FZM, SRS)
    g6 = eqt(w, A0, dst(w, A0, [g3], 'sumeq2dv', '%s = sum_ m e. %s ( %s x. ( %s + %s ) )' % (TOTRS, FZM, K2, SR, SSv)), eqc(w, A0, g4))
    g7 = eqt(w, A0, g6, dst(w, A0, [g5], 'oveq2d', '( %s x. sum_ m e. %s ( %s + %s ) ) = ( %s x. ( %s + %s ) )' % (K2, FZM, SR, SSv, K2, SSR, SSS)))
    # sum sum R <_ ( sum_ m a_m ^ 2 ) C
    a2 = '( %s ^ 2 )' % a
    cam.leaf('( A ` m )', 'CC', aval(w, Am, 'm', lift(w, aok, Am), w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM))))
    SW = 'sum_ n e. %s %s' % (FZM, wv)
    r1 = w.s([lift(w, fz, Am), cam.mem(a2, 'CC'), c.mem(wv, 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = %s )' % (Am, a2, SW, SR))
    mwin = ap(w, Am, 'mvwin', [J(w, Am, J(w, Am, lift(w, nn, Am), lift(w, tp, Am), lift(w, mn0, Am)), w.s([], 'simpr', '( %s -> m e. %s )' % (Am, FZM)))],
              '%s <_ ( ( ( 4 x. M ) / ( N x. T ) ) + 1 )' % SW.replace('if ( ( N ||', 'if ( ( N ||'))
    cam.leaf('M', 'NN0', lift(w, mn0, Am))
    swr = w.s([lift(w, fz, Am), c.mem(wv, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SW))
    r2 = w.s([swr, cam.mem(C, 'RR'), cam.mem(a2, 'RR'), w.s([cam.mem(a, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (Am, a2)), mwin], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (Am, a2, SW, a2, C))
    r3 = w.s([eqc(w, Am, r1), r2], 'eqbrtrd', '( %s -> %s <_ ( %s x. %s ) )' % (Am, SR, a2, C))
    r4 = w.s([fz, w.s([lift(w, fz, Am), c.mem(Rv, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SR)), cam.mem('( %s x. %s )' % (a2, C), 'RR'), r3], 'fsumle',
             '( %s -> %s <_ sum_ m e. %s ( %s x. %s ) )' % (A0, SSR, FZM, a2, C))
    SA_m = 'sum_ m e. %s %s' % (FZM, a2)
    r5 = w.s([fz, cl.mem(C, 'CC'), cam.mem(a2, 'CC')], 'fsummulc1', '( %s -> ( %s x. %s ) = sum_ m e. %s ( %s x. %s ) )' % (A0, SA_m, C, FZM, a2, C))
    RB = w.s([r4, eqc(w, A0, r5)], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, SSR, SA_m, C))
    # sum sum S
    Amn2 = '( %s /\\ ( m e. %s /\\ n e. %s ) )' % (A0, FZM, FZM)
    q_m = w.s([], 'simprl', '( %s -> m e. %s )' % (Amn2, FZM)); q_n = w.s([], 'simprr', '( %s -> n e. %s )' % (Amn2, FZM))
    cq = Closure(w, Amn2, {'( A ` n )': ('CC', aval(w, Amn2, 'n', lift(w, aok, Amn2), q_n)), 'm': ('NN', ap(w, Amn2, 'elfznn', [q_m], 'm e. NN')), 'n': ('NN', ap(w, Amn2, 'elfznn', [q_n], 'n e. NN')),
                           'N': ('NN', lift(w, nn, Amn2)), 'T': ('RR+', lift(w, tp, Amn2)), '_pi': ('RR+', a1(w, Amn2, 'pirp', '_pi e. RR+'))})
    cq.leaf(wv, 'RR', w.s([a1(w, Amn2, '1re', '1 e. RR'), w.s([], '0red', '( %s -> 0 e. RR )' % Amn2)], 'ifcld', '( %s -> %s e. RR )' % (Amn2, wv)))
    sc = w.s([fz, fz, cq.mem(Sv, 'CC')], 'fsumcom', '( %s -> %s = sum_ n e. %s sum_ m e. %s %s )' % (A0, SSS, FZM, FZM, Sv))
    An = '( %s /\\ n e. %s )' % (A0, FZM)
    Anm = '( ( %s /\\ n e. %s ) /\\ m e. %s )' % (A0, FZM, FZM)
    n_m = w.s([], 'simpr', '( %s -> m e. %s )' % (Anm, FZM)); n_n = lift(w, w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM)), Anm)
    cz = Closure(w, Anm, {'m': ('NN', ap(w, Anm, 'elfznn', [n_m], 'm e. NN')), 'n': ('NN', ap(w, Anm, 'elfznn', [n_n], 'n e. NN')), 'N': ('NN', lift(w, nn, Anm))})
    wv2 = 'if ( ( N || ( m - n ) /\\ ( abs ` ( ( log ` m ) - ( log ` n ) ) ) < %s ) , 1 , 0 )' % DT
    d_a = w.s([cz.mem('N', 'ZZ'), cz.mem('( n - m )', 'ZZ'), w.inst('dvdsnegb')], 'syl2anc', '( %s -> ( N || ( n - m ) <-> N || -u ( n - m ) ) )' % Anm)
    d_b = dst(w, Anm, [w.s([cz.mem('n', 'CC'), cz.mem('m', 'CC')], 'negsubdi2d', '( %s -> -u ( n - m ) = ( m - n ) )' % Anm)], 'breq2d', '( N || -u ( n - m ) <-> N || ( m - n ) )')
    d_ = w.s([d_a, d_b], 'bitrd', '( %s -> ( N || ( n - m ) <-> N || ( m - n ) ) )' % Anm)
    l_ = dst(w, Anm, [w.s([cz.mem('( log ` n )', 'CC'), cz.mem('( log ` m )', 'CC')], 'abssubd', '( %s -> ( abs ` ( ( log ` n ) - ( log ` m ) ) ) = ( abs ` ( ( log ` m ) - ( log ` n ) ) ) )' % Anm)],
             'breq1d', '( ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s <-> ( abs ` ( ( log ` m ) - ( log ` n ) ) ) < %s )' % (DT, DT))
    an_ = w.s([d_, l_], 'anbi12d', '( %s -> ( ( N || ( n - m ) /\\ ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s ) <-> ( N || ( m - n ) /\\ ( abs ` ( ( log ` m ) - ( log ` n ) ) ) < %s ) ) )' % (Anm, DT, DT))
    ww = w.s([an_], 'ifbid', '( %s -> %s = %s )' % (Anm, wv, wv2))
    SW2 = 'sum_ m e. %s %s' % (FZM, wv); SW3 = 'sum_ m e. %s %s' % (FZM, wv2)
    se_ = dst(w, An, [ww], 'sumeq2dv', '%s = %s' % (SW2, SW3))
    mwin2 = ap(w, An, 'mvwin', [J(w, An, J(w, An, lift(w, nn, An), lift(w, tp, An), lift(w, mn0, An)), w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM)))], '%s <_ %s' % (SW3, C))
    can = Closure(w, An, {'( A ` n )': ('CC', aval(w, An, 'n', lift(w, aok, An), w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM)))), 'N': ('NN', lift(w, nn, An)), 'T': ('RR+', lift(w, tp, An)),
                          'M': ('NN0', lift(w, mn0, An))})
    b2_ = '( %s ^ 2 )' % b
    s1_ = w.s([lift(w, fz, An), can.mem(b2_, 'CC'), cz.mem(wv, 'CC') if False else w.s([w.s([a1(w, Anm, '1re', '1 e. RR'), w.s([], '0red', '( %s -> 0 e. RR )' % Anm)], 'ifcld', '( %s -> %s e. RR )' % (Anm, wv))], 'recnd', '( %s -> %s e. CC )' % (Anm, wv))],
              'fsummulc2', '( %s -> ( %s x. %s ) = sum_ m e. %s ( %s x. %s ) )' % (An, b2_, SW2, FZM, b2_, wv))
    sw2r = w.s([se_, w.s([lift(w, fz, An), w.s([a1(w, Anm, '1re', '1 e. RR'), w.s([], '0red', '( %s -> 0 e. RR )' % Anm)], 'ifcld', '( %s -> %s e. RR )' % (Anm, wv2))], 'fsumrecl', '( %s -> %s e. RR )' % (An, SW3))],
               'eqeltrd', '( %s -> %s e. RR )' % (An, SW2))
    s2_ = w.s([sw2r, can.mem(C, 'RR'), can.mem(b2_, 'RR'), w.s([can.mem(b, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (An, b2_)), w.s([se_, mwin2], 'eqbrtrd', '( %s -> %s <_ %s )' % (An, SW2, C))],
              'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (An, b2_, SW2, b2_, C))
    SMS = 'sum_ m e. %s %s' % (FZM, Sv)
    s3_ = w.s([eqc(w, An, s1_), s2_], 'eqbrtrd', '( %s -> %s <_ ( %s x. %s ) )' % (An, SMS, b2_, C))
    s4_ = w.s([fz, w.s([lift(w, fz, An), w.s([w.s([can.mem(b2_, 'RR')], 'adantr', '( %s -> %s e. RR )' % (Anm, b2_)), w.s([a1(w, Anm, '1re', '1 e. RR'), w.s([], '0red', '( %s -> 0 e. RR )' % Anm)], 'ifcld', '( %s -> %s e. RR )' % (Anm, wv))], 'remulcld', '( %s -> %s e. RR )' % (Anm, Sv))],
                   'fsumrecl', '( %s -> %s e. RR )' % (An, SMS)), can.mem('( %s x. %s )' % (b2_, C), 'RR'), s3_], 'fsumle', '( %s -> sum_ n e. %s %s <_ sum_ n e. %s ( %s x. %s ) )' % (A0, FZM, SMS, FZM, b2_, C))
    s5_ = w.s([fz, cl.mem(C, 'CC'), can.mem(b2_, 'CC')], 'fsummulc1', '( %s -> ( %s x. %s ) = sum_ n e. %s ( %s x. %s ) )' % (A0, SA2, C, FZM, b2_, C))
    SB = w.s([w.s([sc, s4_], 'eqbrtrd', '( %s -> %s <_ sum_ n e. %s ( %s x. %s ) )' % (A0, SSS, FZM, b2_, C)), eqc(w, A0, s5_)], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, SSS, SA2, C))
    # sum_ m a_m ^ 2 = SA2
    subn, _ = w.congr(a2, {'m': 'n'}, 'm = n', {'m': w.s([], 'id', '( m = n -> m = n )')})
    cbv = w.s([subn], 'cbvsumv', '%s = %s' % (SA_m, SA2))
    RB2 = w.s([RB, w.s([w.s([cbv], 'oveq1i', '( %s x. %s ) = ( %s x. %s )' % (SA_m, C, SA2, C))], 'a1i', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, SA_m, C, SA2, C))], 'breqtrd',
              '( %s -> %s <_ ( %s x. %s ) )' % (A0, SSR, SA2, C))
    # assemble
    SSWP = 'sum_ m e. %s %s' % (FZM, SWP)
    for t_, st_ in [(SSWP, w.s([fz, w.s([lift(w, fz, Am), c.mem(WPAIR(), 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SWP))], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SSWP))),
                    (TOTRS, w.s([fz, w.s([lift(w, fz, Am), c.mem('( %s x. ( %s + %s ) )' % (K2, Rv, Sv), 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SRS))], 'fsumrecl', '( %s -> %s e. RR )' % (A0, TOTRS))),
                    (SSR, w.s([fz, w.s([lift(w, fz, Am), c.mem(Rv, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SR))], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SSR))),
                    (SSS, w.s([fz, w.s([lift(w, fz, Am), c.mem(Sv, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (Am, SSv))], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SSS)))]:
        cl.leaf(t_, 'RR', st_)
    cl.leaf(SA2, 'RR', w.s([fz, cam.mem('( %s ^ 2 )' % a, 'RR') if False else can.mem(b2_, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SA2)))
    cl.leaf(C, 'RR', cl.mem(C, 'RR'))
    cl.leaf('( %s x. %s )' % (SA2, C), 'RR', cl.mem('( %s x. %s )' % (SA2, C), 'RR'))
    cl.leaf(K2, 'RR', cl.mem(K2, 'RR'))
    k2g = ltle(w, A0, cl, cl.gt0(K2))
    ab_ = w.s([cl.mem('( %s + %s )' % (SSR, SSS), 'RR'), cl.mem('( ( %s x. %s ) + ( %s x. %s ) )' % (SA2, C, SA2, C), 'RR'), cl.mem(K2, 'RR'), k2g,
               w.s([RB2, SB], 'le2addd', '( %s -> ( %s + %s ) <_ ( ( %s x. %s ) + ( %s x. %s ) ) )' % (A0, SSR, SSS, SA2, C, SA2, C))], 'lemul2ad',
              '( %s -> ( %s x. ( %s + %s ) ) <_ ( %s x. ( ( %s x. %s ) + ( %s x. %s ) ) ) )' % (A0, K2, SSR, SSS, K2, SA2, C, SA2, C))
    t1 = w.s([f2, w.s([g7, ab_], 'eqbrtrd', '( %s -> %s <_ ( %s x. ( ( %s x. %s ) + ( %s x. %s ) ) ) )' % (A0, TOTRS, K2, SA2, C, SA2, C))], 'letrd' if False else 'id', 'x') if False else None
    BIG = '( %s x. ( ( %s x. %s ) + ( %s x. %s ) ) )' % (K2, SA2, C, SA2, C)
    cl.leaf(BIG, 'RR', cl.mem(BIG, 'RR'))
    ssle = w.s([cl.mem(SSWP, 'RR'), cl.mem(TOTRS, 'RR'), cl.mem(BIG, 'RR'), f2, w.s([g7, ab_], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, TOTRS, BIG))], 'letrd', '( %s -> %s <_ %s )' % (A0, SSWP, BIG))
    kg = ltle(w, A0, cl, cl.gt0(KK))
    kl = w.s([cl.mem(SSWP, 'RR'), cl.mem(BIG, 'RR'), cl.mem(KK, 'RR'), kg, ssle], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A0, KK, SSWP, KK, BIG))
    # constants: KK DT = 6 T
    kd1 = w.s([cl.mem('( ; 1 2 x. ( T ^ 2 ) )', 'CC'), cl.mem('_pi', 'CC'), cl.mem('_pi', 'CC'), cl.mem('( 2 x. T )', 'CC'), cl.ne0('_pi'), cl.ne0('( 2 x. T )')], 'divmuldivd',
              '( %s -> ( %s x. %s ) = ( ( ( ; 1 2 x. ( T ^ 2 ) ) x. _pi ) / ( _pi x. ( 2 x. T ) ) ) )' % (A0, KK, DT))
    cT = Closure(w, A0, {'T': ('RR', cl.mem('T', 'RR')), '_pi': ('RR', cl.mem('_pi', 'RR'))})
    kd2 = dst(w, A0, [ringeqp(w, A0, '( ( ; 1 2 x. ( T ^ 2 ) ) x. _pi )', '( ( 6 x. T ) x. ( _pi x. ( 2 x. T ) ) )', cT)], 'oveq1d',
              '( ( ( ; 1 2 x. ( T ^ 2 ) ) x. _pi ) / ( _pi x. ( 2 x. T ) ) ) = ( ( ( 6 x. T ) x. ( _pi x. ( 2 x. T ) ) ) / ( _pi x. ( 2 x. T ) ) )')
    kd3 = w.s([cl.mem('( 6 x. T )', 'CC'), cl.mem('( _pi x. ( 2 x. T ) )', 'CC'), cl.ne0('( _pi x. ( 2 x. T ) )')], 'divcan4d',
              '( %s -> ( ( ( 6 x. T ) x. ( _pi x. ( 2 x. T ) ) ) / ( _pi x. ( 2 x. T ) ) ) = ( 6 x. T ) )' % A0)
    KD = eqt(w, A0, eqt(w, A0, kd1, kd2), kd3)
    ccm = Closure(w, A0, {KK: ('RR', cl.mem(KK, 'RR')), PH: ('RR', cl.mem(PH, 'RR')), DT: ('RR', cl.mem(DT, 'RR')), SA2: ('RR', cl.mem(SA2, 'RR')), C: ('RR', cl.mem(C, 'RR'))})
    e1 = ringeq(w, A0, '( %s x. %s )' % (KK, BIG), '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) )' % (KK, DT, PH, C, SA2), ccm)
    e2 = dst(w, A0, [dst(w, A0, [KD], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( ( 6 x. T ) x. %s )' % (KK, DT, PH, PH))], 'oveq1d',
             '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) ) = ( ( ( 6 x. T ) x. %s ) x. ( %s x. %s ) )' % (KK, DT, PH, C, SA2, PH, C, SA2))
    # phi <_ N
    phn = ap(w, A0, 'z5phile', [nn], '%s <_ N' % PH)
    cs0 = w.s([cl.mem(C, 'RR'), cl.mem(SA2, 'RR'), cl.ge0(C) if False else ltle(w, A0, cl, cl.gt0(C)),
               w.s([fz, can.mem(b2_, 'RR'), w.s([can.mem(b, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (An, b2_))], 'fsumge0', '( %s -> 0 <_ %s )' % (A0, SA2))], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (A0, C, SA2))
    p6 = w.s([cl.mem(PH, 'RR'), cl.mem('N', 'RR'), cl.mem('( 6 x. T )', 'RR'), ltle(w, A0, cl, cl.gt0('( 6 x. T )')), phn], 'lemul2ad', '( %s -> ( ( 6 x. T ) x. %s ) <_ ( ( 6 x. T ) x. N ) )' % (A0, PH))
    p7 = w.s([cl.mem('( ( 6 x. T ) x. %s )' % PH, 'RR'), cl.mem('( ( 6 x. T ) x. N )', 'RR'), cl.mem('( %s x. %s )' % (C, SA2), 'RR'), cs0, p6], 'lemul1ad',
             '( %s -> ( ( ( 6 x. T ) x. %s ) x. ( %s x. %s ) ) <_ ( ( ( 6 x. T ) x. N ) x. ( %s x. %s ) ) )' % (A0, PH, C, SA2, C, SA2))
    # ( 6 T N ) C = 24 M + 6 N T
    Qd = '( ( 4 x. M ) / ( N x. T ) )'
    dq = w.s([cl.mem('( 4 x. M )', 'CC'), cl.mem('( N x. T )', 'CC'), cl.ne0('( N x. T )')], 'divcan2d', '( %s -> ( ( N x. T ) x. %s ) = ( 4 x. M ) )' % (A0, Qd))
    cq2 = Closure(w, A0, {'T': ('RR', cl.mem('T', 'RR')), 'N': ('RR', cl.mem('N', 'RR')), Qd: ('RR', cl.mem(Qd, 'RR')), 'M': ('RR', cl.mem('M', 'RR')), SA2: ('RR', cl.mem(SA2, 'RR'))})
    h1 = ringeq(w, A0, '( ( ( 6 x. T ) x. N ) x. ( %s x. %s ) )' % (C, SA2), '( ( ( 6 x. ( ( N x. T ) x. %s ) ) + ( 6 x. ( N x. T ) ) ) x. %s )' % (Qd, SA2), cq2)
    h2 = dst(w, A0, [dst(w, A0, [dst(w, A0, [dq], 'oveq2d', '( 6 x. ( ( N x. T ) x. %s ) ) = ( 6 x. ( 4 x. M ) )' % Qd)], 'oveq1d',
                                 '( ( 6 x. ( ( N x. T ) x. %s ) ) + ( 6 x. ( N x. T ) ) ) = ( ( 6 x. ( 4 x. M ) ) + ( 6 x. ( N x. T ) ) )' % Qd)], 'oveq1d',
             '( ( ( 6 x. ( ( N x. T ) x. %s ) ) + ( 6 x. ( N x. T ) ) ) x. %s ) = ( ( ( 6 x. ( 4 x. M ) ) + ( 6 x. ( N x. T ) ) ) x. %s )' % (Qd, SA2, SA2))
    L24 = '( ( 6 x. ( 4 x. M ) ) + ( 6 x. ( N x. T ) ) )'
    cl.leaf('( N x. T )', 'RR', cl.mem('( N x. T )', 'RR'))
    l24 = linarith(w, A0, [cl.ge0('M'), w.s([cl.mem('N', 'RR'), cl.mem('T', 'RR'), ltle(w, A0, cl, cl.gt0('N')), ltle(w, A0, cl, cl.gt0('T'))], 'mulge0d', '( %s -> 0 <_ ( N x. T ) )' % A0)],
                   '%s <_ ( ; ; 1 0 0 x. ( M + ( N x. T ) ) )' % L24, closure=cl)
    sa0 = w.s([fz, can.mem(b2_, 'RR'), w.s([can.mem(b, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (An, b2_))], 'fsumge0', '( %s -> 0 <_ %s )' % (A0, SA2))
    h3 = w.s([cl.mem(L24, 'RR'), cl.mem('( ; ; 1 0 0 x. ( M + ( N x. T ) ) )', 'RR'), cl.mem(SA2, 'RR'), sa0, l24], 'lemul1ad',
             '( %s -> ( %s x. %s ) <_ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s ) )' % (A0, L24, SA2, SA2))
    for t_ in ['( %s x. %s )' % (KK, SSWP), '( %s x. %s )' % (KK, BIG), '( ( ( 6 x. T ) x. %s ) x. ( %s x. %s ) )' % (PH, C, SA2), '( ( ( 6 x. T ) x. N ) x. ( %s x. %s ) )' % (C, SA2),
               '( %s x. %s )' % (L24, SA2), '( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s )' % SA2, '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) )' % (KK, DT, PH, C, SA2)]:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR'))
    assert MID == '( %s x. %s )' % (KK, SSWP), (MID[:80])
    fin_ = linarith(w, A0, [kl, e1, e2, p7, h1, h2, h3], '%s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s )' % (MID, SA2), closure=cl)
    J(w, A0, cl.mem(MID, 'RR'), cl.mem('( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s )' % SA2, 'RR'), fin_)
    qedlast(w)
    go(w)


def mvmvc():
    w = W('mvmvc', 'Character-twisted mean value theorem (MeanValue mean_value_chars): sum_ x mod N S. ( -u T , T ) | sum_ n <_ M a_n x ( n ) n ^ ( - i t ) | ^ 2 <_ 100 ( M + N T ) sum | a_n | ^ 2.')
    A0 = HMV
    k1 = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    m1 = ap(w, A0, 'mvmvc1', [k1], STATEMENTS['mvmvc1'].split(' -> ', 1)[1][:-2])
    m2 = ap(w, A0, 'mvmvc2', [k1], STATEMENTS['mvmvc2'].split(' -> ', 1)[1][:-2])
    P = parts(w, A0)
    nn, tp, mn0, aok = P['N e. NN'], P['T e. RR+'], P['M e. NN0'], P[AOK]
    L_ = 'sum_ x e. %s %s' % (Dd, ITG(TT, ABS2(DS('x', 't'))))
    R_ = '( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s )' % SA2
    w.s([dst(w, A0, [m1], 'simpld', '%s e. RR' % L_), w.s([m2], 'simp1d', '( %s -> %s e. RR )' % (A0, MID)), w.s([m2], 'simp2d', '( %s -> %s e. RR )' % (A0, R_)),
         dst(w, A0, [m1], 'simprd', '%s <_ %s' % (L_, MID)), w.s([m2], 'simp3d', '( %s -> %s <_ %s )' % (A0, MID, R_))], 'letrd', '( %s -> %s <_ %s )' % (A0, L_, R_))
    qedlast(w)
    go(w)


def mvmvcp():
    w = W('mvmvcp', 'mean_value_chars in the complex-power form n ^ ( - i t ) (MeanValue mean_value_chars_cpow).')
    A0 = HMV
    P = parts(w, A0)
    aok = P[AOK]
    Ax = '( %s /\\ x e. %s )' % (A0, Dd)
    Axt = '( %s /\\ t e. %s )' % (Ax, TT)
    Axtn = '( %s /\\ n e. %s )' % (Axt, FZM)
    tr = lift(w, ap(w, Axt, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Axt, TT))], 't e. RR'), Axtn)
    nm = w.s([], 'simpr', '( %s -> n e. %s )' % (Axtn, FZM))
    nN = ap(w, Axtn, 'elfznn', [nm], 'n e. NN')
    c = Closure(w, Axtn, {'n': ('NN', nN), 't': ('RR', tr), '_i': ('CC', a1(w, Axtn, 'ax-icn', '_i e. CC'))})
    c.leaf('( log ` n )', 'RR', c.mem('( log ` n )', 'RR'))
    E = '-u ( _i x. t )'
    ce = w.s([c.mem('n', 'CC'), c.ne0('n'), c.mem(E, 'CC'), w.inst('cxpef')], 'syl3anc', '( %s -> ( n ^c %s ) = ( exp ` ( %s x. ( log ` n ) ) ) )' % (Axtn, E, E))
    r = ringeq(w, Axtn, '( %s x. ( log ` n ) )' % E, '( _i x. ( -u ( log ` n ) x. t ) )', c)
    pe = eqt(w, Axtn, ce, dst(w, Axtn, [r], 'fveq2d', '( exp ` ( %s x. ( log ` n ) ) ) = %s' % (E, NEX('n', 't'))))
    te = dst(w, Axtn, [pe], 'oveq2d', '( ( ( A ` n ) x. %s ) x. ( n ^c %s ) ) = ( ( ( A ` n ) x. %s ) x. %s )' % (CHV('x', 'n'), E, CHV('x', 'n'), NEX('n', 't')))
    se = dst(w, Axt, [te], 'sumeq2dv', '%s = %s' % (DSP('x', 't'), DS('x', 't')))
    ae = dst(w, Axt, [dst(w, Axt, [se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (DSP('x', 't'), DS('x', 't')))], 'oveq1d', '%s = %s' % (ABS2(DSP('x', 't')), ABS2(DS('x', 't'))))
    ie = dst(w, Ax, [ae], 'itgeq2dv', '%s = %s' % (ITG(TT, ABS2(DSP('x', 't'))), ITG(TT, ABS2(DS('x', 't')))))
    xe = dst(w, A0, [ie], 'sumeq2dv', 'sum_ x e. %s %s = sum_ x e. %s %s' % (Dd, ITG(TT, ABS2(DSP('x', 't'))), Dd, ITG(TT, ABS2(DS('x', 't')))))
    mv = ap(w, A0, 'mvmvc', [w.s([], 'id', '( %s -> %s )' % (A0, A0))], STATEMENTS['mvmvc'].split(' -> ', 1)[1][:-2])
    w.s([xe, mv], 'eqbrtrd', '( %s -> sum_ x e. %s %s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s ) )' % (A0, Dd, ITG(TT, ABS2(DSP('x', 't'))), SA2))
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvmvc1()
    mvmvc2()
    mvmvc()
    mvmvcp()
