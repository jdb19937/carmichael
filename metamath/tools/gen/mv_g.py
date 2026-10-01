"""Sortie MV, section G: kernel_mvt (mvrefl, mvsx, mvsxdv, mvsinlow is in mv_c, mvkmvt)."""
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


def mvrefl():
    w = W('mvrefl', 'Reflection: S. ( -u T (,) 0 ) F ( t ) = S. ( 0 (,) T ) F ( -u t ) for F continuous on RR (lintrev with two affine parametrisations, z6aff).')
    A0 = '( T e. RR+ /\\ F e. ( RR -cn-> CC ) )'
    P = parts(w, A0)
    tp, fc = P['T e. RR+'], P['F e. ( RR -cn-> CC )']
    cl = Closure(w, A0, {'T': ('RR+', tp)})
    tr = cl.mem('T', 'RR'); mT = '-u T'
    mtr = cl.mem(mT, 'RR'); z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A0)
    ff = ap(w, A0, 'cncff', [fc], 'F : RR --> CC')
    # the segment ( -u T cseg 0 ) lies in RR
    Ic = '( -u T [,] 0 )'
    def iccmem(a, b, x, ar_, br_, xr, lo, hi, ante=A0):
        bi = w.s([ar_, br_, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (ante, x, a, b, x, a, x, x, b))
        return w.s([w.s([xr, lo, hi], '3jca', '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (ante, x, a, x, x, b)), bi], 'mpbird', '( %s -> %s e. ( %s [,] %s ) )' % (ante, x, a, b))
    t0 = ltle(w, A0, cl, cl.gt0('T'))
    mt0 = linarith(w, A0, [t0], '-u T <_ 0', closure=cl)
    m1 = iccmem(mT, '0', mT, mtr, z0, mtr, w.s([mtr], 'leidd', '( %s -> -u T <_ -u T )' % A0), mt0)
    m2 = iccmem(mT, '0', '0', mtr, z0, z0, mt0, w.s([z0], 'leidd', '( %s -> 0 <_ 0 )' % A0))
    cs = w.s([J(w, A0, mtr, z0), J(w, A0, m1, m2), w.inst('csegicc')], 'syl2anc', '( %s -> ( -u T cseg 0 ) C_ %s )' % (A0, Ic))
    icr = w.s([mtr, z0, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, Ic))
    csr = w.s([cs, icr], 'sstrd', '( %s -> ( -u T cseg 0 ) C_ RR )' % A0)
    mtc = cl.mem(mT, 'CC'); z0c = w.s([], '0cnd', '( %s -> 0 e. CC )' % A0)
    lr = ap(w, A0, 'lintrev', [J(w, A0, J(w, A0, mtc, z0c), J(w, A0, fc, csr))], '( F lint <. 0 , -u T >. ) = -u ( F lint <. -u T , 0 >. )')
    fv = w.s([fc], 'elexd' if False else 'id', 'x') if False else w.s([fc], 'elexd', '( %s -> F e. _V )' % A0)
    L1 = '( ( F ` ( -u T + ( s x. ( 0 - -u T ) ) ) ) x. ( 0 - -u T ) )'
    L2 = '( ( F ` ( 0 + ( s x. ( -u T - 0 ) ) ) ) x. ( -u T - 0 ) )'
    v1 = w.s([fv, mtc, z0c, w.inst('lintval')], 'syl3anc', '( %s -> ( F lint <. -u T , 0 >. ) = S. ( 0 (,) 1 ) %s _d s )' % (A0, L1))
    v2 = w.s([fv, z0c, mtc, w.inst('lintval')], 'syl3anc', '( %s -> ( F lint <. 0 , -u T >. ) = S. ( 0 (,) 1 ) %s _d s )' % (A0, L2))
    # LHS by z6aff with H = ( F |` Ic )
    H = '( F |` %s )' % Ic
    hc = w.s([icr, fc, w.inst('rescncf')], 'sylc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, H, Ic))
    ml0 = linarith(w, A0, [cl.gt0('T')], '-u T < 0', closure=cl)
    za = w.s([J(w, A0, J(w, A0, mtr, z0), ml0), hc, w.inst('z6aff')], 'syl2anc' if False else 'id', 'x') if False else \
        ap(w, A0, 'z6aff', [J(w, A0, J(w, A0, J(w, A0, mtr, z0), ml0), hc)],
           'S. ( -u T (,) 0 ) ( %s ` u ) _d u = S. ( 0 (,) 1 ) ( ( %s ` ( -u T + ( s x. ( 0 - -u T ) ) ) ) x. ( 0 - -u T ) ) _d s' % (H, H))
    # ( H ` u ) = ( F ` u ) on ( -u T (,) 0 )
    Au = '( %s /\\ u e. ( -u T (,) 0 ) )' % A0
    um = w.s([w.s([], 'simpr', '( %s -> u e. ( -u T (,) 0 ) )' % Au), a1(w, Au, 'ioossicc', '( -u T (,) 0 ) C_ %s' % Ic)], 'sseldd' if False else 'id', 'x') if False else \
        w.s([a1(w, Au, 'ioossicc', '( -u T (,) 0 ) C_ %s' % Ic), w.s([], 'simpr', '( %s -> u e. ( -u T (,) 0 ) )' % Au)], 'sseldd', '( %s -> u e. %s )' % (Au, Ic))
    hu = ap(w, Au, 'fvres', [um], '( %s ` u ) = ( F ` u )' % H)
    e1 = dst(w, A0, [hu], 'itgeq2dv', 'S. ( -u T (,) 0 ) ( %s ` u ) _d u = S. ( -u T (,) 0 ) ( F ` u ) _d u' % H)
    # ( H ` ( -T + s T ) ) = F ( ... ) on ( 0 , 1 )
    As = '( %s /\\ s e. ( 0 (,) 1 ) )' % A0
    sm = w.s([], 'simpr', '( %s -> s e. ( 0 (,) 1 ) )' % As)
    sr = ap(w, As, 'elioore', [sm], 's e. RR')
    so = ap(w, As, 'eliooord', [sm], '( 0 < s /\\ s < 1 )')
    cs_ = Closure(w, As, {'T': ('RR+', lift(w, tp, As)), 's': ('RR', sr)})
    pt = '( -u T + ( s x. ( 0 - -u T ) ) )'
    s0 = ltle(w, As, cs_, dst(w, As, [so], 'simpld', '0 < s')); s1 = ltle(w, As, cs_, dst(w, As, [so], 'simprd', 's < 1'))
    st_ = w.s([sr, cs_.mem('T', 'RR'), s0, lift(w, t0, As)], 'mulge0d', '( %s -> 0 <_ ( s x. T ) )' % As)
    st1 = w.s([sr, a1(w, As, '1re', '1 e. RR'), cs_.mem('T', 'RR'), lift(w, t0, As), s1], 'lemul1ad', '( %s -> ( s x. T ) <_ ( 1 x. T ) )' % As)
    cs_.leaf('( s x. T )', 'RR', cs_.mem('( s x. T )', 'RR'))
    pe = ringeq(w, As, pt, '( -u T + ( s x. T ) )', cs_)
    cs_.leaf(pt, 'RR', cs_.mem(pt, 'RR'))
    plo = linarith(w, As, [pe, st_], '-u T <_ %s' % pt, closure=cs_)
    phi = linarith(w, As, [pe, st1], '%s <_ 0' % pt, closure=cs_)
    ptm = iccmem(mT, '0', pt, lift(w, mtr, As), w.s([], '0red', '( %s -> 0 e. RR )' % As), cs_.mem(pt, 'RR'), plo, phi, ante=As)
    hp = ap(w, As, 'fvres', [ptm], '( %s ` %s ) = ( F ` %s )' % (H, pt, pt))
    e2 = dst(w, A0, [dst(w, As, [hp], 'oveq1d', '( ( %s ` %s ) x. ( 0 - -u T ) ) = %s' % (H, pt, L1))], 'itgeq2dv',
             'S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( 0 - -u T ) ) _d s = S. ( 0 (,) 1 ) %s _d s' % (H, pt, L1))
    LHS = eqt(w, A0, eqt(w, A0, eqc(w, A0, e1), za), e2)          # S. ( -T , 0 ) F u = S. ( 0 , 1 ) L1
    # RHS by z6aff with K = ( u e. ( 0 [,] T ) |-> ( F ` -u u ) )
    I0 = '( 0 [,] T )'
    K = '( v e. %s |-> ( F ` -u v ) )' % I0
    Au0 = '( %s /\\ v e. %s )' % (A0, I0)
    bi0 = w.s([z0, tr, w.inst('elicc2')], 'syl2anc', '( %s -> ( v e. %s <-> ( v e. RR /\\ 0 <_ v /\\ v <_ T ) ) )' % (A0, I0))
    ur = w.s([w.s([w.s([], 'simpr', '( %s -> v e. %s )' % (Au0, I0)), lift(w, bi0, Au0)], 'mpbid', '( %s -> ( v e. RR /\\ 0 <_ v /\\ v <_ T ) )' % Au0)], 'simp1d', '( %s -> v e. RR )' % Au0)
    icr0 = w.s([z0, tr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, I0))
    cu = Closure(w, Au0, {'v': ('RR', ur)})
    cn0 = CN(w, A0, 'v', I0, w.s([icr0, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, I0)), cl, cu)
    ncn = cn0('-u v')
    nf_ = dst(w, A0, [cu.mem('-u v', 'RR')], 'fmptd', '( v e. %s |-> -u v ) : %s --> RR' % (I0, I0))
    nrr = w.s([w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), ncn, w.inst('cncfcdm')], 'syl2anc',
                   '( %s -> ( ( v e. %s |-> -u v ) e. ( %s -cn-> RR ) <-> ( v e. %s |-> -u v ) : %s --> RR ) )' % (A0, I0, I0, I0, I0)), nf_], 'mpbird' if False else 'mpbir2and' if False else 'id', 'x') if False else \
        w.s([nf_, w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), ncn, w.inst('cncfcdm')], 'syl2anc',
                      '( %s -> ( ( v e. %s |-> -u v ) e. ( %s -cn-> RR ) <-> ( v e. %s |-> -u v ) : %s --> RR ) )' % (A0, I0, I0, I0, I0))], 'mpbird',
            '( %s -> ( v e. %s |-> -u v ) e. ( %s -cn-> RR ) )' % (A0, I0, I0))
    fe = dst(w, A0, [ff], 'feqmptd', 'F = ( y e. RR |-> ( F ` y ) )')
    fyc = w.s([fe, fc], 'eqeltrrd', '( %s -> ( y e. RR |-> ( F ` y ) ) e. ( RR -cn-> CC ) )' % A0)
    kc = w.s([w.s([], 'nfv', 'F/ v %s' % A0), nrr, fyc, w.s([w.s([], 'ssidd' if False else 'ssid', 'RR C_ RR')], 'a1i', '( %s -> RR C_ RR )' % A0),
              w.s([], 'fveq2', '( y = -u v -> ( F ` y ) = ( F ` -u v ) )')], 'cncfcompt2', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, K, I0))
    t0l = cl.gt0('T')
    zb = ap(w, A0, 'z6aff', [J(w, A0, J(w, A0, J(w, A0, z0, tr), t0l), kc)],
            'S. ( 0 (,) T ) ( %s ` u ) _d u = S. ( 0 (,) 1 ) ( ( %s ` ( 0 + ( s x. ( T - 0 ) ) ) ) x. ( T - 0 ) ) _d s' % (K, K))
    Aw = '( %s /\\ u e. ( 0 (,) T ) )' % A0
    uw = w.s([a1(w, Aw, 'ioossicc', '( 0 (,) T ) C_ %s' % I0), w.s([], 'simpr', '( %s -> u e. ( 0 (,) T ) )' % Aw)], 'sseldd', '( %s -> u e. %s )' % (Aw, I0))
    urw = w.s([lift(w, icr0, Aw), uw], 'sseldd', '( %s -> u e. RR )' % Aw)
    fvw = w.s([lift(w, ff, Aw), w.s([urw], 'renegcld', '( %s -> -u u e. RR )' % Aw)], 'ffvelcdmd', '( %s -> ( F ` -u u ) e. CC )' % Aw)
    ku = fvmd(w, Aw, 'v', I0, '( F ` -u v )', 'u', uw, fvw)
    e3 = dst(w, A0, [ku], 'itgeq2dv', 'S. ( 0 (,) T ) ( %s ` u ) _d u = S. ( 0 (,) T ) ( F ` -u u ) _d u' % K)
    q = '( 0 + ( s x. ( T - 0 ) ) )'
    q0 = w.s([cs_.mem('( s x. T )', 'RR'), st_], 'id', 'x') if False else None
    qe = ringeq(w, As, q, '( s x. T )', cs_)
    cs_.leaf(q, 'RR', cs_.mem(q, 'RR'))
    qlo = linarith(w, As, [qe, st_], '0 <_ %s' % q, closure=cs_)
    qhi = linarith(w, As, [qe, st1], '%s <_ T' % q, closure=cs_)
    qm = iccmem('0', 'T', q, w.s([], '0red', '( %s -> 0 e. RR )' % As), cs_.mem('T', 'RR'), cs_.mem(q, 'RR'), qlo, qhi, ante=As)
    fq = w.s([lift(w, ff, As), cs_.mem('-u %s' % q, 'RR')], 'ffvelcdmd', '( %s -> ( F ` -u %s ) e. CC )' % (As, q))
    kq = fvmd(w, As, 'v', I0, '( F ` -u v )', q, qm, fq)
    L3 = '( ( F ` -u %s ) x. ( T - 0 ) )' % q
    e4 = dst(w, A0, [dst(w, As, [kq], 'oveq1d', '( ( %s ` %s ) x. ( T - 0 ) ) = %s' % (K, q, L3))], 'itgeq2dv',
             'S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( T - 0 ) ) _d s = S. ( 0 (,) 1 ) %s _d s' % (K, q, L3))
    RHS = eqt(w, A0, eqt(w, A0, eqc(w, A0, e3), zb), e4)          # S. ( 0 , T ) F ( -u u ) = S. ( 0 , 1 ) L3
    # L3 = -u L2 pointwise
    a2 = '( 0 + ( s x. ( -u T - 0 ) ) )'
    ga = dst(w, As, [ringeq(w, As, '-u %s' % q, a2, cs_)], 'fveq2d', '( F ` -u %s ) = ( F ` %s )' % (q, a2))
    fa2 = w.s([lift(w, ff, As), cs_.mem(a2, 'RR')], 'ffvelcdmd', '( %s -> ( F ` %s ) e. CC )' % (As, a2))
    cs2 = Closure(w, As, {'T': ('RR+', lift(w, tp, As)), '( F ` %s )' % a2: ('CC', fa2)})
    r3 = ringeq(w, As, '( ( F ` %s ) x. ( T - 0 ) )' % a2, '-u %s' % L2, cs2)
    pl = eqt(w, As, dst(w, As, [ga], 'oveq1d', '%s = ( ( F ` %s ) x. ( T - 0 ) )' % (L3, a2)), r3)       # L3 = -u L2
    e5 = dst(w, A0, [pl], 'itgeq2dv', 'S. ( 0 (,) 1 ) %s _d s = S. ( 0 (,) 1 ) -u %s _d s' % (L3, L2))
    ibl2 = ap(w, A0, 'lintibl', [J(w, A0, J(w, A0, z0c, mtc), J(w, A0, fc, w.s([w.s([z0c, mtc, w.inst('csegcomlem')], 'syl2anc', '( %s -> ( 0 cseg -u T ) C_ ( -u T cseg 0 ) )' % A0), csr], 'sstrd', '( %s -> ( 0 cseg -u T ) C_ RR )' % A0)))],
              '( s e. ( 0 (,) 1 ) |-> %s ) e. L^1' % L2)
    cl2 = w.s([lift(w, ff, As) if False else fa2, cs_.mem('( -u T - 0 )', 'CC')], 'mulcld', '( %s -> %s e. CC )' % (As, L2))
    ng = w.s([cl2, ibl2], 'itgneg', '( %s -> -u S. ( 0 (,) 1 ) %s _d s = S. ( 0 (,) 1 ) -u %s _d s )' % (A0, L2, L2))
    # assemble: LHS = lint<-T,0> = -u lint<0,-T> = -u S. L2 = S. -u L2 = S. L3 = RHS
    lintc = ap(w, A0, 'lintcl', [J(w, A0, J(w, A0, mtc, z0c), J(w, A0, fc, csr))], '( F lint <. -u T , 0 >. ) e. CC')
    nn_ = w.s([lintc], 'negnegd', '( %s -> -u -u ( F lint <. -u T , 0 >. ) = ( F lint <. -u T , 0 >. ) )' % A0)
    k1 = dst(w, A0, [lr], 'negeqd', '-u ( F lint <. 0 , -u T >. ) = -u -u ( F lint <. -u T , 0 >. )')
    k2 = eqt(w, A0, eqc(w, A0, eqt(w, A0, k1, nn_)), dst(w, A0, [v2], 'negeqd', '-u ( F lint <. 0 , -u T >. ) = -u S. ( 0 (,) 1 ) %s _d s' % L2))
    chain = eqt(w, A0, eqt(w, A0, eqt(w, A0, eqt(w, A0, eqc(w, A0, v1), k2), ng), eqc(w, A0, e5)), eqc(w, A0, RHS))
    # chain: S. ( 0 , 1 ) L1 = S. ( 0 , T ) F ( -u u ); combine with LHS and rename u -> t
    fin_u = eqt(w, A0, LHS, chain)
    ren1 = w.s([w.s([], 'fveq2', '( u = t -> ( F ` u ) = ( F ` t ) )')], 'cbvitgv' if False else 'id', 'x') if False else None
    c1 = w.s([w.s([], 'fveq2', '( u = t -> ( F ` u ) = ( F ` t ) )')], 'cbvitgv', 'S. ( -u T (,) 0 ) ( F ` u ) _d u = S. ( -u T (,) 0 ) ( F ` t ) _d t')
    c2 = w.s([w.s([w.s([], 'negeq', '( u = t -> -u u = -u t )')], 'fveq2d', '( u = t -> ( F ` -u u ) = ( F ` -u t ) )')], 'cbvitgv',
             'S. ( 0 (,) T ) ( F ` -u u ) _d u = S. ( 0 (,) T ) ( F ` -u t ) _d t')
    w.s([w.s([c1], 'a1i', '( %s -> S. ( -u T (,) 0 ) ( F ` u ) _d u = S. ( -u T (,) 0 ) ( F ` t ) _d t )' % A0), fin_u,
         w.s([c2], 'a1i', '( %s -> S. ( 0 (,) T ) ( F ` -u u ) _d u = S. ( 0 (,) T ) ( F ` -u t ) _d t )' % A0)], '3eqtr3d',
        '( %s -> S. ( -u T (,) 0 ) ( F ` t ) _d t = S. ( 0 (,) T ) ( F ` -u t ) _d t )' % A0)
    qedlast(w)
    go(w)



HKQ = 'A. a e. P ( ( C ` a ) e. CC /\\ ( L ` a ) e. RR )'


def hkat(w, ante, x, allst, memst):
    """( ante -> ( C ` x ) e. CC ) and ( ante -> ( L ` x ) e. RR ) from allst: ( ante -> HKQ ), memst: ( ante -> x e. P )"""
    idst = w.s([], 'id', '( a = %s -> a = %s )' % (x, x))
    cst, new = w.wcongr('( ( C ` a ) e. CC /\\ ( L ` a ) e. RR )', {'a': x}, 'a = %s' % x, {'a': idst})
    both = w.s([cst, allst, memst], 'rspcdva', '( %s -> %s )' % (ante, new))
    return (dst(w, ante, [both], 'simpld', '( C ` %s ) e. CC' % x), dst(w, ante, [both], 'simprd', '( L ` %s ) e. RR' % x))


def expand(w, A0, fin, allst, tau, taur, tbase=None):
    """( A0 -> ( ( abs ` SX(tau) ) ^ 2 ) = sum_ i e. P sum_ j e. P ( CCJ(i,j) x. ( exp ` ( _i x. ( ( ( L ` i ) - ( L ` j ) ) x. tau ) ) ) ) )"""
    def term(v):
        return '( ( C ` %s ) x. %s )' % (v, EX('( L ` %s )' % v, tau))
    def tcl(ante, v, mem):
        cv, lv = hkat(w, ante, v, lift(w, allst, ante), mem)
        c = Closure(w, ante, {'( C ` %s )' % v: ('CC', cv), '( L ` %s )' % v: ('RR', lv), tau: ('RR', lift(w, taur, ante)), '_i': ('CC', a1(w, ante, 'ax-icn', '_i e. CC'))})
        return c, cv, lv
    Ai = '( %s /\\ i e. P )' % A0; Aj = '( %s /\\ j e. P )' % A0
    ci, _, _ = tcl(Ai, 'i', w.s([], 'simpr', '( %s -> i e. P )' % Ai))
    cj, _, _ = tcl(Aj, 'j', w.s([], 'simpr', '( %s -> j e. P )' % Aj))
    S = SX(tau)
    cl0 = Closure(w, A0, {})
    sc = w.s([fin, ci.mem(term('i'), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (A0, S))
    a1s = ap(w, A0, 'absvalsq', [sc], '( ( abs ` %s ) ^ 2 ) = ( %s x. ( * ` %s ) )' % (S, S, S))
    cjs = w.s([fin, ci.mem(term('i'), 'CC')], 'fsumcj', '( %s -> ( * ` %s ) = sum_ i e. P ( * ` %s ) )' % (A0, S, term('i')))
    sub, _ = w.congr('( * ` %s )' % term('i'), {'i': 'j'}, 'i = j', {'i': w.s([], 'id', '( i = j -> i = j )')})
    cbv = w.s([sub], 'cbvsumv', 'sum_ i e. P ( * ` %s ) = sum_ j e. P ( * ` %s )' % (term('i'), term('j')))
    cj2 = eqt(w, A0, cjs, w.s([cbv], 'a1i', '( %s -> sum_ i e. P ( * ` %s ) = sum_ j e. P ( * ` %s ) )' % (A0, term('i'), term('j'))))
    p1 = dst(w, A0, [cj2], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. sum_ j e. P ( * ` %s ) )' % (S, S, S, term('j')))
    f2 = w.s([fin, fin, ci.mem(term('i'), 'CC'), cj.mem('( * ` %s )' % term('j'), 'CC')], 'fsum2mul',
             '( %s -> sum_ i e. P sum_ j e. P ( %s x. ( * ` %s ) ) = ( %s x. sum_ j e. P ( * ` %s ) ) )' % (A0, term('i'), term('j'), S, term('j')))
    # summand
    Aij = '( ( %s /\\ i e. P ) /\\ j e. P )' % A0
    cij_i = hkat(w, Aij, 'i', lift(w, allst, Aij), lift(w, w.s([], 'simpr', '( %s -> i e. P )' % Ai), Aij))
    cij_j = hkat(w, Aij, 'j', lift(w, allst, Aij), w.s([], 'simpr', '( %s -> j e. P )' % Aij))
    tr_ = lift(w, taur, Aij)
    c = Closure(w, Aij, {'( C ` i )': ('CC', cij_i[0]), '( L ` i )': ('RR', cij_i[1]), '( C ` j )': ('CC', cij_j[0]), '( L ` j )': ('RR', cij_j[1]), tau: ('RR', tr_),
                         '_i': ('CC', a1(w, Aij, 'ax-icn', '_i e. CC'))})
    if tbase is not None:
        c.leaf('t', 'RR', lift(w, tbase, Aij))
    Ei = EX('( L ` i )', tau); Ej = EX('( L ` j )', tau)
    q1 = w.s([c.mem('( C ` j )', 'CC'), c.mem(Ej, 'CC')], 'cjmuld', '( %s -> ( * ` %s ) = ( ( * ` ( C ` j ) ) x. ( * ` %s ) ) )' % (Aij, term('j'), Ej))
    q2 = dst(w, Aij, [q1], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. ( ( * ` ( C ` j ) ) x. ( * ` %s ) ) )' % (term('i'), term('j'), term('i'), Ej))
    q3 = w.s([c.mem('( C ` i )', 'CC'), c.mem(Ei, 'CC'), c.mem('( * ` ( C ` j ) )', 'CC'), c.mem('( * ` %s )' % Ej, 'CC')], 'mul4d',
             '( %s -> ( %s x. ( ( * ` ( C ` j ) ) x. ( * ` %s ) ) ) = ( %s x. ( %s x. ( * ` %s ) ) ) )' % (Aij, term('i'), Ej, CCJ('i', 'j'), Ei, Ej))
    Xj = '( _i x. ( ( L ` j ) x. %s ) )' % tau
    ce = ap(w, Aij, 'efcj', [c.mem(Xj, 'CC')], '( exp ` ( * ` %s ) ) = ( * ` %s )' % (Xj, Ej))
    cm = w.s([a1(w, Aij, 'ax-icn', '_i e. CC'), c.mem('( ( L ` j ) x. %s )' % tau, 'CC')], 'cjmuld', '( %s -> ( * ` %s ) = ( ( * ` _i ) x. ( * ` ( ( L ` j ) x. %s ) ) ) )' % (Aij, Xj, tau))
    cr = w.s([c.mem('( ( L ` j ) x. %s )' % tau, 'RR')], 'cjred', '( %s -> ( * ` ( ( L ` j ) x. %s ) ) = ( ( L ` j ) x. %s ) )' % (Aij, tau, tau))
    cm2 = eqt(w, Aij, cm, dst(w, Aij, [a1(w, Aij, 'cji', '( * ` _i ) = -u _i'), cr], 'oveq12d', '( ( * ` _i ) x. ( * ` ( ( L ` j ) x. %s ) ) ) = ( -u _i x. ( ( L ` j ) x. %s ) )' % (tau, tau)))
    cjE = eqt(w, Aij, eqc(w, Aij, ce), dst(w, Aij, [cm2], 'fveq2d', '( exp ` ( * ` %s ) ) = ( exp ` ( -u _i x. ( ( L ` j ) x. %s ) ) )' % (Xj, tau)))
    Yi = '( _i x. ( ( L ` i ) x. %s ) )' % tau; Yj = '( -u _i x. ( ( L ` j ) x. %s ) )' % tau
    ea = ap(w, Aij, 'efadd', [c.mem(Yi, 'CC'), w.s([a1(w, Aij, 'negicn', '-u _i e. CC'), c.mem('( ( L ` j ) x. %s )' % tau, 'CC')], 'mulcld', '( %s -> %s e. CC )' % (Aij, Yj))],
            '( exp ` ( %s + %s ) ) = ( %s x. ( exp ` %s ) )' % (Yi, Yj, Ei, Yj))
    c.leaf('_i', 'CC', a1(w, Aij, 'ax-icn', '_i e. CC'))
    ar = ringeq(w, Aij, '( %s + %s )' % (Yi, Yj), '( _i x. ( ( ( L ` i ) - ( L ` j ) ) x. %s ) )' % tau, c)
    eprod = eqt(w, Aij, eqt(w, Aij, dst(w, Aij, [cjE], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. ( exp ` %s ) )' % (Ei, Ej, Ei, Yj)), eqc(w, Aij, ea)),
                dst(w, Aij, [ar], 'fveq2d', '( exp ` ( %s + %s ) ) = ( exp ` ( _i x. ( ( ( L ` i ) - ( L ` j ) ) x. %s ) ) )' % (Yi, Yj, tau)))
    EIJ = '( exp ` ( _i x. ( ( ( L ` i ) - ( L ` j ) ) x. %s ) ) )' % tau
    q4 = dst(w, Aij, [eprod], 'oveq2d', '( %s x. ( %s x. ( * ` %s ) ) ) = ( %s x. %s )' % (CCJ('i', 'j'), Ei, Ej, CCJ('i', 'j'), EIJ))
    summ = eqt(w, Aij, eqt(w, Aij, q2, q3), q4)
    s1 = dst(w, Ai, [summ], 'sumeq2dv', 'sum_ j e. P ( %s x. ( * ` %s ) ) = sum_ j e. P ( %s x. %s )' % (term('i'), term('j'), CCJ('i', 'j'), EIJ))
    s2 = dst(w, A0, [s1], 'sumeq2dv', 'sum_ i e. P sum_ j e. P ( %s x. ( * ` %s ) ) = sum_ i e. P sum_ j e. P ( %s x. %s )' % (term('i'), term('j'), CCJ('i', 'j'), EIJ))
    return eqt(w, A0, eqt(w, A0, eqt(w, A0, a1s, p1), eqc(w, A0, f2)), s2)


def mvsx():
    w = W('mvsx', '| S ( t ) | ^ 2 + | S ( -u t ) | ^ 2 = 2 sum_ i sum_ j Re ( c_i c_j* ) cos ( ( L_i - L_j ) t ) for a finite exponential sum S (kernel_mvt, hpt).')
    A0 = '( ( P e. Fin /\\ %s ) /\\ t e. RR )' % HKQ
    P_ = parts(w, A0)
    fin, allst, tr = P_['P e. Fin'], P_[HKQ], P_['t e. RR']
    ntr = w.s([tr], 'renegcld', '( %s -> -u t e. RR )' % A0)
    e1 = expand(w, A0, fin, allst, 't', tr)
    e2 = expand(w, A0, fin, allst, '-u t', ntr, tr)
    Aij = '( ( %s /\\ i e. P ) /\\ j e. P )' % A0
    Ai = '( %s /\\ i e. P )' % A0
    ci = hkat(w, Aij, 'i', lift(w, allst, Aij), lift(w, w.s([], 'simpr', '( %s -> i e. P )' % Ai), Aij))
    cj = hkat(w, Aij, 'j', lift(w, allst, Aij), w.s([], 'simpr', '( %s -> j e. P )' % Aij))
    c = Closure(w, Aij, {'( C ` i )': ('CC', ci[0]), '( L ` i )': ('RR', ci[1]), '( C ` j )': ('CC', cj[0]), '( L ` j )': ('RR', cj[1]), 't': ('RR', lift(w, tr, Aij)),
                         '_i': ('CC', a1(w, Aij, 'ax-icn', '_i e. CC'))})
    TH = '( ( ( L ` i ) - ( L ` j ) ) x. t )'
    Ep = '( exp ` ( _i x. %s ) )' % TH
    Em = '( exp ` ( _i x. ( ( ( L ` i ) - ( L ` j ) ) x. -u t ) ) )'
    cc_ = CCJ('i', 'j')
    # e^+ + e^- = 2 cos
    cv = ap(w, Aij, 'cosval', [c.mem(TH, 'CC')], '( cos ` %s ) = ( ( %s + ( exp ` ( -u _i x. %s ) ) ) / 2 )' % (TH, Ep, TH))
    am = dst(w, Aij, [ringeq(w, Aij, '( _i x. ( ( ( L ` i ) - ( L ` j ) ) x. -u t ) )', '( -u _i x. %s )' % TH, c)], 'fveq2d', '%s = ( exp ` ( -u _i x. %s ) )' % (Em, TH))
    COS = '( cos ` %s )' % TH
    for t_ in [Ep, Em, '( exp ` ( -u _i x. %s ) )' % TH, COS, cc_]:
        c.leaf(t_, 'CC', c.mem(t_, 'CC'))
    two = ringeq(w, Aij, '( ( %s + ( exp ` ( -u _i x. %s ) ) ) / 2 )' % (Ep, TH), '( ( %s + ( exp ` ( -u _i x. %s ) ) ) / 2 )' % (Ep, TH), c) if False else None
    # ( c ( e+ ) ) + ( c ( e- ) ) = c ( 2 cos )
    k1 = dst(w, Aij, [am], 'oveq2d', '( %s x. %s ) = ( %s x. ( exp ` ( -u _i x. %s ) ) )' % (cc_, Em, cc_, TH))
    k2 = ringeq(w, Aij, '( ( %s x. %s ) + ( %s x. ( exp ` ( -u _i x. %s ) ) ) )' % (cc_, Ep, cc_, TH), '( %s x. ( 2 x. ( ( %s + ( exp ` ( -u _i x. %s ) ) ) / 2 ) ) )' % (cc_, Ep, TH), c)
    k3 = dst(w, Aij, [dst(w, Aij, [eqc(w, Aij, cv)], 'oveq2d', '( 2 x. ( ( %s + ( exp ` ( -u _i x. %s ) ) ) / 2 ) ) = ( 2 x. %s )' % (Ep, TH, COS))], 'oveq2d',
             '( %s x. ( 2 x. ( ( %s + ( exp ` ( -u _i x. %s ) ) ) / 2 ) ) ) = ( %s x. ( 2 x. %s ) )' % (cc_, Ep, TH, cc_, COS))
    pair = eqt(w, Aij, eqt(w, Aij, dst(w, Aij, [k1], 'oveq2d', '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( %s x. %s ) + ( %s x. ( exp ` ( -u _i x. %s ) ) ) )' % (cc_, Ep, cc_, Em, cc_, Ep, cc_, TH)), k2), k3)
    # Re of the pair: Re ( c ( 2 cos ) ) = 2 ( Re c ) cos
    cr = c.mem(COS, 'RR')
    re1 = w.s([c.mem('( 2 x. %s )' % COS, 'RR'), c.mem(cc_, 'CC')], 'remul2' if False else 'id', 'x') if False else None
    mc = w.s([c.mem(cc_, 'CC'), c.mem('( 2 x. %s )' % COS, 'CC')], 'mulcomd', '( %s -> ( %s x. ( 2 x. %s ) ) = ( ( 2 x. %s ) x. %s ) )' % (Aij, cc_, COS, COS, cc_))
    rm = w.s([c.mem('( 2 x. %s )' % COS, 'RR'), c.mem(cc_, 'CC'), w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` ( ( 2 x. %s ) x. %s ) ) = ( ( 2 x. %s ) x. ( Re ` %s ) ) )' % (Aij, COS, cc_, COS, cc_))
    RC = '( Re ` %s )' % cc_
    c.leaf(RC, 'RR', c.mem(RC, 'RR')); c.leaf(COS, 'RR', cr)
    rr_ = ringeq(w, Aij, '( ( 2 x. %s ) x. %s )' % (COS, RC), '( 2 x. ( %s x. %s ) )' % (RC, COS), c)
    reP = eqt(w, Aij, eqt(w, Aij, dst(w, Aij, [mc], 'fveq2d', '( Re ` ( %s x. ( 2 x. %s ) ) ) = ( Re ` ( ( 2 x. %s ) x. %s ) )' % (cc_, COS, COS, cc_)), rm), rr_)
    # sums
    SP = 'sum_ i e. P sum_ j e. P ( %s x. %s )' % (cc_, Ep)
    SM = 'sum_ i e. P sum_ j e. P ( %s x. %s )' % (cc_, Em)
    ad_in = w.s([lift(w, fin, Ai), c.mem('( %s x. %s )' % (cc_, Ep), 'CC'), c.mem('( %s x. %s )' % (cc_, Em), 'CC')], 'fsumadd',
                '( %s -> sum_ j e. P ( ( %s x. %s ) + ( %s x. %s ) ) = ( sum_ j e. P ( %s x. %s ) + sum_ j e. P ( %s x. %s ) ) )' % (Ai, cc_, Ep, cc_, Em, cc_, Ep, cc_, Em))
    ci_ = Closure(w, Ai, {})
    inP = w.s([lift(w, fin, Ai), c.mem('( %s x. %s )' % (cc_, Ep), 'CC')], 'fsumcl', '( %s -> sum_ j e. P ( %s x. %s ) e. CC )' % (Ai, cc_, Ep))
    inM = w.s([lift(w, fin, Ai), c.mem('( %s x. %s )' % (cc_, Em), 'CC')], 'fsumcl', '( %s -> sum_ j e. P ( %s x. %s ) e. CC )' % (Ai, cc_, Em))
    ad_out = w.s([fin, inP, inM], 'fsumadd', '( %s -> sum_ i e. P ( sum_ j e. P ( %s x. %s ) + sum_ j e. P ( %s x. %s ) ) = ( %s + %s ) )' % (A0, cc_, Ep, cc_, Em, SP, SM))
    s_in = eqt(w, Ai, eqc(w, Ai, ad_in), dst(w, Ai, [pair], 'sumeq2dv', 'sum_ j e. P ( ( %s x. %s ) + ( %s x. %s ) ) = sum_ j e. P ( %s x. ( 2 x. %s ) )' % (cc_, Ep, cc_, Em, cc_, COS)))
    TOT = 'sum_ i e. P sum_ j e. P ( %s x. ( 2 x. %s ) )' % (cc_, COS)
    s_out = eqt(w, A0, eqc(w, A0, ad_out), dst(w, A0, [s_in], 'sumeq2dv', 'sum_ i e. P ( sum_ j e. P ( %s x. %s ) + sum_ j e. P ( %s x. %s ) ) = %s' % (cc_, Ep, cc_, Em, TOT)))
    L = '( %s + %s )' % (ABS2(SX('t')), ABS2(SX('-u t')))
    lhs = eqt(w, A0, dst(w, A0, [e1, e2], 'oveq12d', '%s = ( %s + %s )' % (L, SP, SM)), s_out)        # L = TOT
    # real parts
    cl0 = Closure(w, A0, {})
    Ati = '( %s /\\ i e. P )' % A0
    lr = w.s([w.s([w.s([fin, Closure(w, Ai, {'( C ` i )': ('CC', hkat(w, Ai, 'i', lift(w, allst, Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai))[0]),
                                                  '( L ` i )': ('RR', hkat(w, Ai, 'i', lift(w, allst, Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai))[1]), 't': ('RR', lift(w, tr, Ai)), '_i': ('CC', a1(w, Ai, 'ax-icn', '_i e. CC'))}).mem('( ( C ` i ) x. %s )' % EX('( L ` i )', 't'), 'CC')],
                                'fsumcl', '( %s -> %s e. CC )' % (A0, SX('t')))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, SX('t')))], 'resqcld', '( %s -> %s e. RR )' % (A0, ABS2(SX('t'))))
    lr2 = w.s([w.s([w.s([fin, Closure(w, Ai, {'( C ` i )': ('CC', hkat(w, Ai, 'i', lift(w, allst, Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai))[0]),
                                                   '( L ` i )': ('RR', hkat(w, Ai, 'i', lift(w, allst, Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai))[1]), '-u t': ('RR', lift(w, ntr, Ai)), '_i': ('CC', a1(w, Ai, 'ax-icn', '_i e. CC'))}).mem('( ( C ` i ) x. %s )' % EX('( L ` i )', '-u t'), 'CC')],
                                 'fsumcl', '( %s -> %s e. CC )' % (A0, SX('-u t')))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, SX('-u t')))], 'resqcld', '( %s -> %s e. RR )' % (A0, ABS2(SX('-u t'))))
    Lr = w.s([lr, lr2], 'readdcld', '( %s -> %s e. RR )' % (A0, L))
    reL = w.s([Lr], 'rered', '( %s -> ( Re ` %s ) = %s )' % (A0, L, L))
    re_tot = dst(w, A0, [lhs], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (L, TOT))
    innerc = w.s([lift(w, fin, Ai), c.mem('( %s x. ( 2 x. %s ) )' % (cc_, COS), 'CC')], 'fsumcl', '( %s -> sum_ j e. P ( %s x. ( 2 x. %s ) ) e. CC )' % (Ai, cc_, COS))
    fr1 = w.s([fin, innerc], 'fsumre', '( %s -> ( Re ` %s ) = sum_ i e. P ( Re ` sum_ j e. P ( %s x. ( 2 x. %s ) ) ) )' % (A0, TOT, cc_, COS))
    fr2 = w.s([lift(w, fin, Ai), c.mem('( %s x. ( 2 x. %s ) )' % (cc_, COS), 'CC')], 'fsumre', '( %s -> ( Re ` sum_ j e. P ( %s x. ( 2 x. %s ) ) ) = sum_ j e. P ( Re ` ( %s x. ( 2 x. %s ) ) ) )' % (Ai, cc_, COS, cc_, COS))
    in2 = eqt(w, Ai, fr2, dst(w, Ai, [reP], 'sumeq2dv', 'sum_ j e. P ( Re ` ( %s x. ( 2 x. %s ) ) ) = sum_ j e. P ( 2 x. ( %s x. %s ) )' % (cc_, COS, RC, COS)))
    mm = w.s([lift(w, fin, Ai), w.s([], '2cnd', '( %s -> 2 e. CC )' % Ai), c.mem('( %s x. %s )' % (RC, COS), 'CC')], 'fsummulc2',
             '( %s -> ( 2 x. sum_ j e. P ( %s x. %s ) ) = sum_ j e. P ( 2 x. ( %s x. %s ) ) )' % (Ai, RC, COS, RC, COS))
    in3 = eqt(w, Ai, in2, eqc(w, Ai, mm))
    o1 = dst(w, A0, [in3], 'sumeq2dv', 'sum_ i e. P ( Re ` sum_ j e. P ( %s x. ( 2 x. %s ) ) ) = sum_ i e. P ( 2 x. sum_ j e. P ( %s x. %s ) )' % (cc_, COS, RC, COS))
    icr = w.s([lift(w, fin, Ai), c.mem('( %s x. %s )' % (RC, COS), 'CC')], 'fsumcl', '( %s -> sum_ j e. P ( %s x. %s ) e. CC )' % (Ai, RC, COS))
    o2 = w.s([fin, w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), icr], 'fsummulc2',
             '( %s -> ( 2 x. sum_ i e. P sum_ j e. P ( %s x. %s ) ) = sum_ i e. P ( 2 x. sum_ j e. P ( %s x. %s ) ) )' % (A0, RC, COS, RC, COS))
    fin_ = eqt(w, A0, eqt(w, A0, eqt(w, A0, eqt(w, A0, eqc(w, A0, reL), re_tot), fr1), o1), eqc(w, A0, o2))
    qedlast(w)
    go(w)


def mvsxdv():
    w = W('mvsxdv', 'The derivative of the exponential sum S ( t ) = sum_ i c_i exp ( i L_i t ) and the continuity of S and S` on RR (hasDerivAt_exp_mul_I).')
    A0 = HK
    P_ = parts(w, A0)
    fin, allst = P_['P e. Fin'], P_[HKQ]
    rr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    Jt = '( ( TopOpen ` CCfld ) |`t RR )'
    ej = w.s([], 'eqid', '%s = %s' % (Jt, Jt)); ek = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    xj = w.s([w.s([w.s([w.s([], 'retop', '( topGen ` ran (,) ) e. Top'), w.s([w.s([], 'uniretop', 'RR = U. ( topGen ` ran (,) )')], 'topopn', '( ( topGen ` ran (,) ) e. Top -> RR e. ( topGen ` ran (,) ) )')], 'ax-mp', 'RR e. ( topGen ` ran (,) )'), w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % Jt)], 'eleqtri', 'RR e. %s' % Jt)], 'a1i', '( %s -> RR e. %s )' % (A0, Jt))
    Ai = '( %s /\\ i e. P )' % A0
    ci, li = hkat(w, Ai, 'i', lift(w, allst, Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai))
    Ci, Li = '( C ` i )', '( L ` i )'
    IL = '( _i x. %s )' % Li
    E = EX(Li, 't')

    def dterm(K, kst):
        """under Ai: ( RR _D ( t e. RR |-> ( K x. E ) ) ) = ( t e. RR |-> ( ( K x. IL ) x. E ) ), and the membership pieces"""
        rri = lift(w, rr, Ai)
        Ait = '( %s /\\ t e. RR )' % Ai
        tr = w.s([], 'simpr', '( %s -> t e. RR )' % Ait)
        c = Closure(w, Ait, {Li: ('RR', lift(w, li, Ait)), 't': ('RR', tr), '_i': ('CC', a1(w, Ait, 'ax-icn', '_i e. CC')), K: ('CC', lift(w, kst, Ait))})
        if K != Ci:
            c.leaf(Ci, 'CC', lift(w, ci, Ait))
        did = w.s([rri], 'dvmptid', '( %s -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )' % Ai)
        d1 = w.s([rri, c.mem('t', 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % Ait), did, w.s([li], 'recnd', '( %s -> %s e. CC )' % (Ai, Li))], 'dvmptcmul',
                 '( %s -> ( RR _D ( t e. RR |-> ( %s x. t ) ) ) = ( t e. RR |-> ( %s x. 1 ) ) )' % (Ai, Li, Li))
        d2 = w.s([rri, c.mem('( %s x. t )' % Li, 'CC'), c.mem('( %s x. 1 )' % Li, 'CC'), d1, a1(w, Ai, 'ax-icn', '_i e. CC')], 'dvmptcmul',
                 '( %s -> ( RR _D ( t e. RR |-> ( _i x. ( %s x. t ) ) ) ) = ( t e. RR |-> ( _i x. ( %s x. 1 ) ) ) )' % (Ai, Li, Li))
        ef = a1(w, Ai, 'eff', 'exp : CC --> CC')
        fe = dst(w, Ai, [ef], 'feqmptd', 'exp = ( y e. CC |-> ( exp ` y ) )')
        de = eqt(w, Ai, eqt(w, Ai, eqc(w, Ai, dst(w, Ai, [fe], 'oveq2d', '( CC _D exp ) = ( CC _D ( y e. CC |-> ( exp ` y ) ) )')), a1(w, Ai, 'dvef', '( CC _D exp ) = exp')), fe)
        Aiy = '( %s /\\ y e. CC )' % Ai
        yc = w.s([w.s([], 'simpr', '( %s -> y e. CC )' % Aiy)], 'efcld', '( %s -> ( exp ` y ) e. CC )' % Aiy)
        X = '( _i x. ( %s x. t ) )' % Li
        co = w.s([rri, lift(w, a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }'), Ai), c.mem(X, 'CC'), c.mem('( _i x. ( %s x. 1 ) )' % Li, 'CC'), yc, yc, d2, de,
                  w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = ( exp ` %s ) )' % (X, X)), w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = ( exp ` %s ) )' % (X, X))],
                 'dvmptco', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( %s x. ( _i x. ( %s x. 1 ) ) ) ) )' % (Ai, E, E, Li))
        d3 = w.s([rri, c.mem(E, 'CC'), c.mem('( %s x. ( _i x. ( %s x. 1 ) ) )' % (E, Li), 'CC'), co, kst], 'dvmptcmul',
                 '( %s -> ( RR _D ( t e. RR |-> ( %s x. %s ) ) ) = ( t e. RR |-> ( %s x. ( %s x. ( _i x. ( %s x. 1 ) ) ) ) ) )' % (Ai, K, E, K, E, Li))
        c.leaf(E, 'CC', c.mem(E, 'CC'))
        r = ringeq(w, Ait, '( %s x. ( %s x. ( _i x. ( %s x. 1 ) ) ) )' % (K, E, Li), '( ( %s x. %s ) x. %s )' % (K, IL, E), c)
        m = dst(w, Ai, [r], 'mpteq2dva', '( t e. RR |-> ( %s x. ( %s x. ( _i x. ( %s x. 1 ) ) ) ) ) = ( t e. RR |-> ( ( %s x. %s ) x. %s ) )' % (K, E, Li, K, IL, E))
        return eqt(w, Ai, d3, m), c, Ait
    D1, c1, Ait = dterm(Ci, ci)
    K2 = '( %s x. %s )' % (Ci, IL)
    k2 = dst(w, Ai, [ci, w.s([a1(w, Ai, 'ax-icn', '_i e. CC'), w.s([li], 'recnd', '( %s -> %s e. CC )' % (Ai, Li))], 'mulcld', '( %s -> %s e. CC )' % (Ai, IL))], 'mulcld', '%s e. CC' % K2)
    D2, c2, _ = dterm(K2, k2)
    Aitt = '( %s /\\ i e. P /\\ t e. RR )' % A0
    def trip(E_):
        """( ( A0 /\\ i e. P /\\ t e. RR ) -> E_ e. CC ) from the Ait closure"""
        st_ = c2.mem(E_, 'CC')
        return w.s([st_], 'sylanl1' if False else '3impa', '( %s -> %s e. CC )' % (Aitt, E_)) if False else \
            w.s([w.s([st_], 'ex' if False else 'id', '( ( %s /\\ t e. RR ) -> %s e. CC )' % (Ai, E_))], '3impa' if False else 'id', '( ( %s /\\ t e. RR ) -> %s e. CC )' % (Ai, E_))
    def trip3(E_):
        st_ = c2.mem(E_, 'CC')
        return w.s([st_], '3impa', '( %s -> %s e. CC )' % (Aitt, E_))
    T1 = '( %s x. %s )' % (Ci, E); T2 = '( %s x. %s )' % (K2, E); T3 = '( ( %s x. %s ) x. %s )' % (K2, IL, E)
    S1 = 'sum_ i e. P %s' % T1; S2 = 'sum_ i e. P %s' % T2; S3 = 'sum_ i e. P %s' % T3
    dv1 = w.s([ej, ek, rr, xj, fin, trip3(T1), trip3(T2), D1], 'dvmptfsum', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) )' % (A0, S1, S2))
    dv2 = w.s([ej, ek, rr, xj, fin, trip3(T2), trip3(T3), D2], 'dvmptfsum', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) )' % (A0, S2, S3))
    # continuity by dvcn
    At = '( %s /\\ t e. RR )' % A0
    def sumc(T_):
        return w.s([lift(w, fin, At), w.s([c2.mem(T_, 'CC')], 'an32s' if False else 'id', 'x') if False else
                    w.s([trip3(T_)], '3expa' if False else 'id', 'x') if False else w.s([c2.mem(T_, 'CC')], 'an32s', '( ( %s /\\ i e. P ) -> %s e. CC )' % (At, T_))],
                   'fsumcl', '( %s -> sum_ i e. P %s e. CC )' % (At, T_))
    def cont(Sa, Sb, dv):
        F = '( t e. RR |-> %s )' % Sa
        ff = dst(w, A0, [sumc(Sa[len('sum_ i e. P '):])], 'fmptd', '%s : RR --> CC' % F)
        dmE = w.s([], 'eqid', '( t e. RR |-> %s ) = ( t e. RR |-> %s )' % (Sb, Sb))
        dm = eqt(w, A0, dst(w, A0, [dv], 'dmeqd', 'dom ( RR _D %s ) = dom ( t e. RR |-> %s )' % (F, Sb)),
                 w.s([dmE, sumc(Sb[len('sum_ i e. P '):])], 'dmmptd', '( %s -> dom ( t e. RR |-> %s ) = RR )' % (A0, Sb)))
        j3 = J(w, A0, a1(w, A0, 'ax-resscn', 'RR C_ CC'), ff, a1(w, A0, 'ssid', 'RR C_ RR'))
        return ap(w, A0, 'dvcn', [J(w, A0, j3, dm)], '%s e. ( RR -cn-> CC )' % F)
    cn1 = cont(S1, S2, dv1); cn2 = cont(S2, S3, dv2)
    w.s([dv1, cn1, cn2], '3jca', '( %s -> ( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) ) )' % (A0, S1, S2, S1, S2))
    qedlast(w)
    go(w)


def sxcl(w, ante, allst, fin, tau, extra=None):
    """( ante -> SX(tau) e. CC ) for a real tau (extra: leaves under ( ante /\\ i e. P ))"""
    Ai = '( %s /\\ i e. P )' % ante
    ci, li = hkat(w, Ai, 'i', lift(w, allst, Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai))
    lv = {'( C ` i )': ('CC', ci), '( L ` i )': ('RR', li), '_i': ('CC', a1(w, Ai, 'ax-icn', '_i e. CC'))}
    for k, (kind, st_) in (extra or {}).items():
        lv[k] = (kind, lift(w, st_, Ai))
    c = Closure(w, Ai, lv)
    return w.s([fin, c.mem('( ( C ` i ) x. %s )' % EX('( L ` i )', tau), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (ante, SX(tau)))


def mvkm0():
    w = W('mvkm0', 'The t-integral over ( -u T , T ) of | S | ^ 2 as the integral over ( 0 , T ) of | S ( t ) | ^ 2 + | S ( -u t ) | ^ 2 (kernel_mvt, by mvrefl).')
    A0 = '( T e. RR+ /\\ %s )' % HK
    P_ = parts(w, A0)
    tp, hk, fin, allst = P_['T e. RR+'], P_[HK], P_['P e. Fin'], P_[HKQ]
    cl = Closure(w, A0, {'T': ('RR+', tp)})
    dv = ap(w, A0, 'mvsxdv', [hk], '( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (SX('t'), SXD('t'), SX('t'), SXD('t')))
    cn1 = w.s([dv], 'simp2d', '( %s -> ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (A0, SX('t')))
    At = '( %s /\\ t e. RR )' % A0
    tr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    sxt = sxcl(w, At, lift(w, allst, At), lift(w, fin, At), 't', {'t': ('RR', tr)})
    ct = Closure(w, At, {SX('t'): ('CC', sxt), 't': ('RR', tr)})
    cn = CN(w, A0, 't', 'RR', a1(w, A0, 'ax-resscn', 'RR C_ CC'), cl, ct, known={SX('t'): cn1})
    E = ABS2(SX('t')); En = ABS2(SX('-u t'))
    gcn = cn(E)
    G = '( t e. RR |-> %s )' % E
    # the reflected map, continuous by composition
    Gy = '( y e. RR |-> %s )' % ABS2(SX('y'))
    ren = w.s([w.s([], 'id' if False else 'cbvmptv', '%s = %s' % (G, Gy)) if False else None][:0] or [], 'id', 'x') if False else None
    sub, _ = w.congr(E, {'t': 'y'}, 't = y', {'t': w.s([], 'id', '( t = y -> t = y )')})
    cbv = w.s([sub], 'cbvmptv', '%s = %s' % (G, Gy))
    gycn = w.s([w.s([cbv], 'a1i', '( %s -> %s = %s )' % (A0, G, Gy)), gcn], 'eqeltrrd', '( %s -> %s e. ( RR -cn-> CC ) )' % (A0, Gy))
    ncn = cn('-u t')
    nf_ = dst(w, A0, [w.s([tr], 'renegcld', '( %s -> -u t e. RR )' % At)], 'fmptd', '( t e. RR |-> -u t ) : RR --> RR')
    nrr = w.s([nf_, w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), ncn, w.inst('cncfcdm')], 'syl2anc',
                        '( %s -> ( ( t e. RR |-> -u t ) e. ( RR -cn-> RR ) <-> ( t e. RR |-> -u t ) : RR --> RR ) )' % A0)], 'mpbird',
              '( %s -> ( t e. RR |-> -u t ) e. ( RR -cn-> RR ) )' % A0)
    sub2, _ = w.congr(ABS2(SX('y')), {'y': '-u t'}, 'y = -u t', {'y': w.s([], 'id', '( y = -u t -> y = -u t )')})
    gncn = w.s([w.s([], 'nfv', 'F/ t %s' % A0), nrr, gycn, w.s([w.s([], 'ssid', 'RR C_ RR')], 'a1i', '( %s -> RR C_ RR )' % A0), sub2], 'cncfcompt2',
               '( %s -> ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (A0, En))
    trr = cl.mem('T', 'RR'); mtr = cl.mem('-u T', 'RR'); z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A0)
    ib1 = w.s([mtr, z0, gcn], 'lsibl', '( %s -> ( t e. ( -u T (,) 0 ) |-> %s ) e. L^1 )' % (A0, E))
    ib2 = w.s([z0, trr, gcn], 'lsibl', '( %s -> ( t e. ( 0 (,) T ) |-> %s ) e. L^1 )' % (A0, E))
    ib3 = w.s([z0, trr, gncn], 'lsibl', '( %s -> ( t e. ( 0 (,) T ) |-> %s ) e. L^1 )' % (A0, En))
    t0 = ltle(w, A0, cl, cl.gt0('T'))
    mt0 = linarith(w, A0, [t0], '-u T <_ 0', closure=cl)
    bi = w.s([mtr, trr, w.inst('elicc2')], 'syl2anc', '( %s -> ( 0 e. ( -u T [,] T ) <-> ( 0 e. RR /\\ -u T <_ 0 /\\ 0 <_ T ) ) )' % A0)
    zm = w.s([w.s([z0, mt0, t0], '3jca', '( %s -> ( 0 e. RR /\\ -u T <_ 0 /\\ 0 <_ T ) )' % A0), bi], 'mpbird', '( %s -> 0 e. ( -u T [,] T ) )' % A0)
    Ati = '( %s /\\ t e. ( -u T (,) T ) )' % A0
    tri = ap(w, Ati, 'elioore', [w.s([], 'simpr', '( %s -> t e. ( -u T (,) T ) )' % Ati)], 't e. RR')
    ec = Closure(w, Ati, {SX('t'): ('CC', sxcl(w, Ati, lift(w, allst, Ati), lift(w, fin, Ati), 't', {'t': ('RR', tri)}))}).mem(E, 'CC')
    sp = w.s([mtr, trr, zm, ec, ib1, ib2], 'itgsplitioo', '( %s -> %s = ( %s + %s ) )' % (A0, ITG(TT, E), ITG(IOO('-u T', '0'), E), ITG(IOO('0', 'T'), E)))
    rf = ap(w, A0, 'mvrefl', [tp, gycn], 'S. ( -u T (,) 0 ) ( %s ` t ) _d t = S. ( 0 (,) T ) ( %s ` -u t ) _d t' % (Gy, Gy))
    Aa = '( %s /\\ t e. ( -u T (,) 0 ) )' % A0
    tra = ap(w, Aa, 'elioore', [w.s([], 'simpr', '( %s -> t e. ( -u T (,) 0 ) )' % Aa)], 't e. RR')
    ca = Closure(w, Aa, {SX('t'): ('CC', sxcl(w, Aa, lift(w, allst, Aa), lift(w, fin, Aa), 't', {'t': ('RR', tra)}))})
    fa = fvmd(w, Aa, 'y', 'RR', ABS2(SX('y')), 't', tra, ca.mem(E, 'CC'))
    Ab = '( %s /\\ t e. ( 0 (,) T ) )' % A0
    trb = ap(w, Ab, 'elioore', [w.s([], 'simpr', '( %s -> t e. ( 0 (,) T ) )' % Ab)], 't e. RR')
    ntb = w.s([trb], 'renegcld', '( %s -> -u t e. RR )' % Ab)
    cb = Closure(w, Ab, {SX('-u t'): ('CC', sxcl(w, Ab, lift(w, allst, Ab), lift(w, fin, Ab), '-u t', {'-u t': ('RR', ntb), 't': ('RR', trb)})),
                         SX('t'): ('CC', sxcl(w, Ab, lift(w, allst, Ab), lift(w, fin, Ab), 't', {'t': ('RR', trb)}))})
    fb = fvmd(w, Ab, 'y', 'RR', ABS2(SX('y')), '-u t', ntb, cb.mem(En, 'CC'))
    e1 = dst(w, A0, [fa], 'itgeq2dv', 'S. ( -u T (,) 0 ) ( %s ` t ) _d t = %s' % (Gy, ITG(IOO('-u T', '0'), E)))
    e2 = dst(w, A0, [fb], 'itgeq2dv', 'S. ( 0 (,) T ) ( %s ` -u t ) _d t = %s' % (Gy, ITG(IOO('0', 'T'), En)))
    neg = eqt(w, A0, eqt(w, A0, eqc(w, A0, e1), rf), e2)        # S. ( -T , 0 ) E = S. ( 0 , T ) En
    ad = w.s([cb.mem(E, 'CC'), ib2, cb.mem(En, 'CC'), ib3], 'itgadd', '( %s -> %s = ( %s + %s ) )' % (A0, ITG(IOO('0', 'T'), QQ), ITG(IOO('0', 'T'), E), ITG(IOO('0', 'T'), En)))
    iq = w.s([cb.mem(E, 'CC'), ib2, cb.mem(En, 'CC'), ib3], 'ibladd', '( %s -> ( t e. ( 0 (,) T ) |-> %s ) e. L^1 )' % (A0, QQ))
    c0 = Closure(w, A0, {})
    I1, I2, I3 = ITG(IOO('-u T', '0'), E), ITG(IOO('0', 'T'), E), ITG(IOO('0', 'T'), En)
    x1 = dst(w, A0, [neg], 'oveq1d', '( %s + %s ) = ( %s + %s )' % (I1, I2, I3, I2))
    ac = w.s([w.s([cb.mem(En, 'CC'), ib3], 'itgcl', '( %s -> %s e. CC )' % (A0, I3)), w.s([cb.mem(E, 'CC'), ib2], 'itgcl', '( %s -> %s e. CC )' % (A0, I2))], 'addcomd',
             '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, I3, I2, I2, I3))
    val = eqt(w, A0, eqt(w, A0, eqt(w, A0, sp, x1), ac), eqc(w, A0, ad))
    J(w, A0, iq, val)
    qedlast(w)
    go(w)


def mvkm2():
    w = W('mvkm2', 'The kernel-weighted integral of | S ( t ) | ^ 2 + | S ( -u t ) | ^ 2 over ( U , V ), 0 <_ U, as 2 sum sum Re ( c_i c_j* ) S. KC ( A , L_i - L_j ) (the bilinear form of kernel_mvt, hstep3).')
    A0 = '( ( T e. RR+ /\\ %s ) /\\ ( U e. RR /\\ V e. RR /\\ 0 <_ U ) )' % HK
    P_ = parts(w, A0)
    tp, hk, fin, allst, ur, vr, u0 = P_['T e. RR+'], P_[HK], P_['P e. Fin'], P_[HKQ], P_['U e. RR'], P_['V e. RR'], P_['0 <_ U']
    I = IOO('U', 'V'); A = AK
    cl = Closure(w, A0, {'T': ('RR+', tp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    ar = cl.mem(A, 'RR')
    RC = '( Re ` %s )' % CCJ('i', 'j'); TH = THIJ
    COS = '( cos ` ( %s x. t ) )' % TH
    X = '( %s x. %s )' % (RC, KC(A, TH))
    SS = 'sum_ i e. P sum_ j e. P ( %s x. %s )' % (RC, COS)
    XX = 'sum_ i e. P sum_ j e. P %s' % X
    # pointwise
    At = '( %s /\\ t e. %s )' % (A0, I)
    mt = w.s([], 'simpr', '( %s -> t e. %s )' % (At, I))
    tr = ap(w, At, 'elioore', [mt], 't e. RR')
    t0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % At), lift(w, ur, At), tr, lift(w, u0, At), dst(w, At, [ap(w, At, 'eliooord', [mt], '( U < t /\\ t < V )')], 'simpld', 'U < t')],
             'lelttrd', '( %s -> 0 < t )' % At)
    sx = ap(w, At, 'mvsx', [J(w, At, lift(w, hk, At), tr)], '%s = ( 2 x. %s )' % (QQ, SS))
    Ati = '( %s /\\ i e. P )' % At
    Atij = '( ( %s /\\ i e. P ) /\\ j e. P )' % At
    ci = hkat(w, Atij, 'i', lift(w, allst, Atij), lift(w, w.s([], 'simpr', '( %s -> i e. P )' % Ati), Atij))
    cj = hkat(w, Atij, 'j', lift(w, allst, Atij), w.s([], 'simpr', '( %s -> j e. P )' % Atij))
    t2 = '( t ^ 2 )'
    def tfacts(ante, trs, t0s):
        t2p = w.s([trs, w.s([t0s], 'gt0ne0d', '( %s -> t =/= 0 )' % ante)], 'sqgt0d', '( %s -> 0 < %s )' % (ante, t2))
        return {'t': [('RR', trs), ('gt0', t0s)], t2: [('RR', w.s([trs], 'resqcld', '( %s -> %s e. RR )' % (ante, t2))), ('gt0', t2p), ('ne0', w.s([t2p], 'gt0ne0d', '( %s -> %s =/= 0 )' % (ante, t2)))]}
    lv = {'( C ` i )': ('CC', ci[0]), '( L ` i )': ('RR', ci[1]), '( C ` j )': ('CC', cj[0]), '( L ` j )': ('RR', cj[1]), A: ('RR', lift(w, ar, Atij))}
    lv.update(tfacts(Atij, lift(w, tr, Atij), lift(w, t0, Atij)))
    c = Closure(w, Atij, lv)
    k = KQ(A)
    for t_ in [k, COS, RC, KS(A)]:
        c.leaf(t_, 'RR', c.mem(t_, 'RR'))
    q1 = ringeq(w, Atij, '( %s x. ( %s x. %s ) )' % (k, RC, COS), '( %s x. ( %s x. %s ) )' % (RC, k, COS), c)
    q2 = w.s([c.mem(KS(A), 'CC'), c.mem(COS, 'CC'), c.mem(t2, 'CC'), c.ne0(t2)], 'div23d', '( %s -> ( ( %s x. %s ) / %s ) = ( %s x. %s ) )' % (Atij, KS(A), COS, t2, k, COS))
    q3 = eqt(w, Atij, q1, dst(w, Atij, [eqc(w, Atij, q2)], 'oveq2d', '( %s x. ( %s x. %s ) ) = %s' % (RC, k, COS, X)))
    SJ = 'sum_ j e. P ( %s x. %s )' % (RC, COS)
    lvi = tfacts(Ati, lift(w, tr, Ati), lift(w, t0, Ati)); lvi[A] = ('RR', lift(w, ar, Ati))
    cti = Closure(w, Ati, lvi)
    cti.leaf(k, 'RR', cti.mem(k, 'RR'))
    m1 = w.s([lift(w, fin, Ati), cti.mem(k, 'CC'), c.mem('( %s x. %s )' % (RC, COS), 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ j e. P ( %s x. ( %s x. %s ) ) )' % (Ati, k, SJ, k, RC, COS))
    m1b = eqt(w, Ati, m1, dst(w, Ati, [q3], 'sumeq2dv', 'sum_ j e. P ( %s x. ( %s x. %s ) ) = sum_ j e. P %s' % (k, RC, COS, X)))
    lvt = tfacts(At, tr, t0); lvt[A] = ('RR', lift(w, ar, At))
    ct = Closure(w, At, lvt)
    ct.leaf(k, 'RR', ct.mem(k, 'RR'))
    sjc = w.s([lift(w, fin, Ati), c.mem('( %s x. %s )' % (RC, COS), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Ati, SJ))
    m2 = w.s([lift(w, fin, At), ct.mem(k, 'CC'), sjc], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ i e. P ( %s x. %s ) )' % (At, k, SS, k, SJ))
    m2b = eqt(w, At, m2, dst(w, At, [m1b], 'sumeq2dv', 'sum_ i e. P ( %s x. %s ) = %s' % (k, SJ, XX)))
    ssc = w.s([lift(w, fin, At), sjc], 'fsumcl', '( %s -> %s e. CC )' % (At, SS))
    ct.leaf(SS, 'CC', ssc)
    r1 = ringeq(w, At, '( %s x. ( 2 x. %s ) )' % (k, SS), '( 2 x. ( %s x. %s ) )' % (k, SS), ct)
    pw = eqt(w, At, eqt(w, At, dst(w, At, [sx], 'oveq2d', '%s = ( %s x. ( 2 x. %s ) )' % (KQQ, k, SS)), r1),
             dst(w, At, [m2b], 'oveq2d', '( 2 x. ( %s x. %s ) ) = ( 2 x. %s )' % (k, SS, XX)))      # kQQ = 2 XX
    # integrals
    Ai = '( %s /\\ i e. P )' % A0
    Aij = '( ( %s /\\ i e. P ) /\\ j e. P )' % A0
    di = hkat(w, Aij, 'i', lift(w, allst, Aij), lift(w, w.s([], 'simpr', '( %s -> i e. P )' % Ai), Aij))
    dj = hkat(w, Aij, 'j', lift(w, allst, Aij), w.s([], 'simpr', '( %s -> j e. P )' % Aij))
    cij = Closure(w, Aij, {'( C ` i )': ('CC', di[0]), '( L ` i )': ('RR', di[1]), '( C ` j )': ('CC', dj[0]), '( L ` j )': ('RR', dj[1]), A: ('RR', lift(w, ar, Aij))})
    kb = ap(w, Aij, 'mvkibl', [J(w, Aij, J(w, Aij, cij.mem(A, 'RR'), cij.mem(TH, 'RR')), J(w, Aij, lift(w, ur, Aij), lift(w, vr, Aij), lift(w, u0, Aij)))],
            '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (I, KC(A, TH), I, KQ(A)))
    kcib = dst(w, Aij, [kb], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, KC(A, TH)))
    # membership of KC under ( Aij /\ t e. I )
    Aijt = '( %s /\\ t e. %s )' % (Aij, I)
    mt2 = w.s([], 'simpr', '( %s -> t e. %s )' % (Aijt, I))
    tr2 = ap(w, Aijt, 'elioore', [mt2], 't e. RR')
    t02 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Aijt), lift(w, ur, Aijt), tr2, lift(w, u0, Aijt), dst(w, Aijt, [ap(w, Aijt, 'eliooord', [mt2], '( U < t /\\ t < V )')], 'simpld', 'U < t')],
              'lelttrd', '( %s -> 0 < t )' % Aijt)
    lv2 = {'( C ` i )': ('CC', lift(w, di[0], Aijt)), '( L ` i )': ('RR', lift(w, di[1], Aijt)), '( C ` j )': ('CC', lift(w, dj[0], Aijt)), '( L ` j )': ('RR', lift(w, dj[1], Aijt)),
           A: ('RR', lift(w, ar, Aijt))}
    lv2.update(tfacts(Aijt, tr2, t02))
    c2 = Closure(w, Aijt, lv2)
    rcc = cij.mem(RC, 'CC')
    ibX = w.s([rcc, c2.mem(KC(A, TH), 'CC'), kcib], 'iblmulc2', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (Aij, I, X))
    itX = w.s([rcc, c2.mem(KC(A, TH), 'CC'), kcib], 'itgmulc2', '( %s -> ( %s x. %s ) = %s )' % (Aij, RC, ITG(I, KC(A, TH)), ITG(I, X)))
    # itgfsum over j, then over i
    Aitj = '( %s /\\ ( t e. %s /\\ j e. P ) )' % (Ai, I)
    mt3 = w.s([], 'simprl', '( %s -> t e. %s )' % (Aitj, I)); mj3 = w.s([], 'simprr', '( %s -> j e. P )' % Aitj)
    tr3 = ap(w, Aitj, 'elioore', [mt3], 't e. RR')
    t03 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Aitj), lift(w, ur, Aitj), tr3, lift(w, u0, Aitj), dst(w, Aitj, [ap(w, Aitj, 'eliooord', [mt3], '( U < t /\\ t < V )')], 'simpld', 'U < t')],
              'lelttrd', '( %s -> 0 < t )' % Aitj)
    e3i = hkat(w, Aitj, 'i', lift(w, allst, Aitj), lift(w, w.s([], 'simpr', '( %s -> i e. P )' % Ai), Aitj))
    e3j = hkat(w, Aitj, 'j', lift(w, allst, Aitj), mj3)
    lv3 = {'( C ` i )': ('CC', e3i[0]), '( L ` i )': ('RR', e3i[1]), '( C ` j )': ('CC', e3j[0]), '( L ` j )': ('RR', e3j[1]), A: ('RR', lift(w, ar, Aitj))}
    lv3.update(tfacts(Aitj, tr3, t03))
    c3 = Closure(w, Aitj, lv3)
    ioo = a1(w, Ai, 'ioombl', '%s e. dom vol' % I)
    fj = w.s([ioo, lift(w, fin, Ai), c3.mem(X, 'CC'), ibX], 'itgfsum', '( %s -> ( ( t e. %s |-> sum_ j e. P %s ) e. L^1 /\\ %s = sum_ j e. P %s ) )' % (Ai, I, X, ITG(I, 'sum_ j e. P %s' % X), ITG(I, X)))
    fj1 = dst(w, Ai, [fj], 'simpld', '( t e. %s |-> sum_ j e. P %s ) e. L^1' % (I, X))
    fj2 = dst(w, Ai, [fj], 'simprd', '%s = sum_ j e. P %s' % (ITG(I, 'sum_ j e. P %s' % X), ITG(I, X)))
    fj3 = eqt(w, Ai, fj2, dst(w, Ai, [eqc(w, Aij, itX)], 'sumeq2dv', 'sum_ j e. P %s = sum_ j e. P ( %s x. %s )' % (ITG(I, X), RC, ITG(I, KC(A, TH)))))
    Atio = '( %s /\\ ( t e. %s /\\ i e. P ) )' % (A0, I)
    mt4 = w.s([], 'simprl', '( %s -> t e. %s )' % (Atio, I))
    tr4 = ap(w, Atio, 'elioore', [mt4], 't e. RR')
    t04 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Atio), lift(w, ur, Atio), tr4, lift(w, u0, Atio), dst(w, Atio, [ap(w, Atio, 'eliooord', [mt4], '( U < t /\\ t < V )')], 'simpld', 'U < t')],
              'lelttrd', '( %s -> 0 < t )' % Atio)
    Atioj = '( %s /\\ j e. P )' % Atio
    e4i = hkat(w, Atioj, 'i', lift(w, allst, Atioj), lift(w, w.s([], 'simprr', '( %s -> i e. P )' % Atio), Atioj))
    e4j = hkat(w, Atioj, 'j', lift(w, allst, Atioj), w.s([], 'simpr', '( %s -> j e. P )' % Atioj))
    lv4 = {'( C ` i )': ('CC', e4i[0]), '( L ` i )': ('RR', e4i[1]), '( C ` j )': ('CC', e4j[0]), '( L ` j )': ('RR', e4j[1]), A: ('RR', lift(w, ar, Atioj))}
    lv4.update(tfacts(Atioj, lift(w, tr4, Atioj), lift(w, t04, Atioj)))
    c4 = Closure(w, Atioj, lv4)
    sjX = w.s([lift(w, fin, Atio), c4.mem(X, 'CC')], 'fsumcl', '( %s -> sum_ j e. P %s e. CC )' % (Atio, X))
    fi = w.s([a1(w, A0, 'ioombl', '%s e. dom vol' % I), fin, sjX, fj1], 'itgfsum', '( %s -> ( ( t e. %s |-> %s ) e. L^1 /\\ %s = sum_ i e. P %s ) )' % (A0, I, XX, ITG(I, XX), ITG(I, 'sum_ j e. P %s' % X)))
    fi1 = dst(w, A0, [fi], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, XX))
    fi2 = eqt(w, A0, dst(w, A0, [fi], 'simprd', '%s = sum_ i e. P %s' % (ITG(I, XX), ITG(I, 'sum_ j e. P %s' % X))),
              dst(w, A0, [fj3], 'sumeq2dv', 'sum_ i e. P %s = %s' % (ITG(I, 'sum_ j e. P %s' % X), KSUM('U', 'V'))))
    # the factor 2
    xxc = w.s([lift(w, fin, At), w.s([lift(w, fin, Ati), c.mem(X, 'CC')], 'fsumcl', '( %s -> sum_ j e. P %s e. CC )' % (Ati, X))], 'fsumcl', '( %s -> %s e. CC )' % (At, XX))
    two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
    ib2 = w.s([two, xxc, fi1], 'iblmulc2', '( %s -> ( t e. %s |-> ( 2 x. %s ) ) e. L^1 )' % (A0, I, XX))
    it2 = w.s([two, xxc, fi1], 'itgmulc2', '( %s -> ( 2 x. %s ) = %s )' % (A0, ITG(I, XX), ITG(I, '( 2 x. %s )' % XX)))
    mq = dst(w, A0, [pw], 'mpteq2dva', '( t e. %s |-> %s ) = ( t e. %s |-> ( 2 x. %s ) )' % (I, KQQ, I, XX))
    ibK = w.s([mq, ib2], 'eqeltrd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, I, KQQ))
    val = eqt(w, A0, eqt(w, A0, dst(w, A0, [pw], 'itgeq2dv', '%s = %s' % (ITG(I, KQQ), ITG(I, '( 2 x. %s )' % XX))), eqc(w, A0, it2)),
              dst(w, A0, [fi2], 'oveq2d', '( 2 x. %s ) = ( 2 x. %s )' % (ITG(I, XX), KSUM('U', 'V'))))
    J(w, A0, ibK, val)
    qedlast(w)
    go(w)


def mvkm1():
    w = W('mvkm1', 'For R >_ T: the t-integral of | S | ^ 2 over ( -u T , T ) is at most ( 3 / ( 2 A ^ 2 ) ) 2 sum sum Re ( c_i c_j* ) S. ( 0 (,) R ) KC ( A , L_i - L_j ), A = pi / ( 4 T ) (kernel_mvt, hstep12 with mvsinlow).')
    A0 = '( ( T e. RR+ /\\ %s ) /\\ ( R e. RR+ /\\ T <_ R ) )' % HK
    P_ = parts(w, A0)
    tp, hk, fin, allst, rp, tR = P_['T e. RR+'], P_[HK], P_['P e. Fin'], P_[HKQ], P_['R e. RR+'], P_['T <_ R']
    A = AK
    cl = Closure(w, A0, {'T': ('RR+', tp), 'R': ('RR+', rp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    cl.leaf(A, 'RR+', cl.mem(A, 'RR+'))
    thk = J(w, A0, tp, hk)
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A0)
    k0 = ap(w, A0, 'mvkm0', [thk], '( ( t e. ( 0 (,) T ) |-> %s ) e. L^1 /\\ %s = %s )' % (QQ, ITG(TT, ABS2(SX('t'))), ITG(IOO('0', 'T'), QQ)))
    def km2(U, V, ur_, vr_, u0_):
        r = ap(w, A0, 'mvkm2', [J(w, A0, thk, J(w, A0, ur_, vr_, u0_))], '( ( t e. %s |-> %s ) e. L^1 /\\ %s = ( 2 x. %s ) )' % (IOO(U, V), KQQ, ITG(IOO(U, V), KQQ), KSUM(U, V)))
        return dst(w, A0, [r], 'simpld', '( t e. %s |-> %s ) e. L^1' % (IOO(U, V), KQQ)), dst(w, A0, [r], 'simprd', '%s = ( 2 x. %s )' % (ITG(IOO(U, V), KQQ), KSUM(U, V)))
    z00 = a1(w, A0, '0le0', '0 <_ 0')
    i0T, _ = km2('0', 'T', z0, cl.mem('T', 'RR'), z00)
    iTR, _ = km2('T', 'R', cl.mem('T', 'RR'), cl.mem('R', 'RR'), cl.ge0('T'))
    i0R, v0R = km2('0', 'R', z0, cl.mem('R', 'RR'), z00)
    # pointwise facts on an interval ( U , V ) with 0 <_ U
    def pt(U, V, u0_, urs):
        Av = '( %s /\\ t e. %s )' % (A0, IOO(U, V))
        m = w.s([], 'simpr', '( %s -> t e. %s )' % (Av, IOO(U, V)))
        tr = ap(w, Av, 'elioore', [m], 't e. RR')
        oo = ap(w, Av, 'eliooord', [m], '( %s < t /\\ t < %s )' % (U, V))
        t0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Av), lift(w, urs, Av), tr, lift(w, u0_, Av), dst(w, Av, [oo], 'simpld', '%s < t' % U)], 'lelttrd', '( %s -> 0 < t )' % Av)
        t2p = w.s([tr, w.s([t0], 'gt0ne0d', '( %s -> t =/= 0 )' % Av)], 'sqgt0d', '( %s -> 0 < ( t ^ 2 ) )' % Av)
        sx1 = sxcl(w, Av, lift(w, allst, Av), lift(w, fin, Av), 't', {'t': ('RR', tr)})
        ntr = w.s([tr], 'renegcld', '( %s -> -u t e. RR )' % Av)
        sx2 = sxcl(w, Av, lift(w, allst, Av), lift(w, fin, Av), '-u t', {'-u t': ('RR', ntr), 't': ('RR', tr)})
        c = Closure(w, Av, {'t': [('RR', tr), ('gt0', t0)], '( t ^ 2 )': [('RR', w.s([tr], 'resqcld', '( %s -> ( t ^ 2 ) e. RR )' % Av)), ('gt0', t2p),
                                                                              ('ne0', w.s([t2p], 'gt0ne0d', '( %s -> ( t ^ 2 ) =/= 0 )' % Av))],
                            SX('t'): ('CC', sx1), SX('-u t'): ('CC', sx2), A: ('RR+', lift(w, cl.mem(A, 'RR+'), Av)), 'T': ('RR+', lift(w, tp, Av)),
                            '_pi': ('RR+', a1(w, Av, 'pirp', '_pi e. RR+'))})
        q0 = w.s([c.mem(ABS2(SX('t')), 'RR'), c.mem(ABS2(SX('-u t')), 'RR'), w.s([c.mem('( abs ` %s )' % SX('t'), 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (Av, ABS2(SX('t')))),
                  w.s([c.mem('( abs ` %s )' % SX('-u t'), 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (Av, ABS2(SX('-u t'))))], 'addge0d', '( %s -> 0 <_ %s )' % (Av, QQ))
        k0_ = w.s([c.mem(KS(A), 'RR'), c.mem('( t ^ 2 )', 'RR+'), w.s([c.mem('( sin ` ( %s x. t ) )' % A, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (Av, KS(A)))], 'divge0d',
                  '( %s -> 0 <_ %s )' % (Av, KQ(A)))
        return Av, m, tr, oo, t0, c, q0, k0_
    # on ( 0 , T ): QQ <_ ( 3 / D ) ( k QQ )
    Av, m, tr, oo, t0, c, q0, k0_ = pt('0', 'T', z00, z0)
    D = '( 2 x. ( %s ^ 2 ) )' % A
    at_ = '( %s x. t )' % A
    tT = ltle(w, Av, c, dst(w, Av, [oo], 'simprd', 't < T'))
    atT = w.s([tr, c.mem('T', 'RR'), c.mem(A, 'RR+'), tT], 'lemul2ad' if False else 'id', 'x') if False else \
        w.s([tr, c.mem('T', 'RR'), c.mem(A, 'RR'), ltle(w, Av, c, c.gt0(A)), tT], 'lemul2ad', '( %s -> %s <_ ( %s x. T ) )' % (Av, at_, A))
    d1 = w.s([c.mem('_pi', 'CC'), a1(w, Av, '4cn', '4 e. CC'), c.mem('T', 'CC'), a1(w, Av, '4ne0', '4 =/= 0'), c.ne0('T')], 'divdiv1d', '( %s -> ( ( _pi / 4 ) / T ) = %s )' % (Av, A))
    d2 = w.s([c.mem('( _pi / 4 )', 'CC'), c.mem('T', 'CC'), c.ne0('T')], 'divcan1d', '( %s -> ( ( ( _pi / 4 ) / T ) x. T ) = ( _pi / 4 ) )' % Av)
    aT = w.s([dst(w, Av, [d1], 'oveq1d', '( ( ( _pi / 4 ) / T ) x. T ) = ( %s x. T )' % A), d2], 'eqtr3d', '( %s -> ( %s x. T ) = ( _pi / 4 ) )' % (Av, A))
    p4 = dst(w, Av, [a1(w, Av, 'pigt2lt4', '( 2 < _pi /\\ _pi < 4 )')], 'simprd', '_pi < 4')
    c.leaf(at_, 'RR', c.mem(at_, 'RR')); c.leaf('( %s x. T )' % A, 'RR', c.mem('( %s x. T )' % A, 'RR'))
    at1 = linarith(w, Av, [atT, aT, p4], '%s <_ 1' % at_, closure=c)
    sl = ap(w, Av, 'mvsinlow', [w.s([c.mem(at_, 'RR'), c.gt0(at_), at1], '3jca', '( %s -> ( %s e. RR /\\ 0 < %s /\\ %s <_ 1 ) )' % (Av, at_, at_, at_))],
            '( ( 2 / 3 ) x. ( %s ^ 2 ) ) <_ %s' % (at_, KS(A)))
    ca = Closure(w, Av, {A: ('RR', c.mem(A, 'RR')), 't': ('RR', tr)})
    e1 = ringeqp(w, Av, '( ( ( 2 / 3 ) x. ( %s ^ 2 ) ) x. ( t ^ 2 ) )' % A, '( ( 2 / 3 ) x. ( %s ^ 2 ) )' % at_, ca)
    sl2 = w.s([e1, sl], 'eqbrtrd', '( %s -> ( ( ( 2 / 3 ) x. ( %s ^ 2 ) ) x. ( t ^ 2 ) ) <_ %s )' % (Av, A, KS(A)))
    ld = w.s([c.mem('( ( 2 / 3 ) x. ( %s ^ 2 ) )' % A, 'RR'), c.mem(KS(A), 'RR'), c.mem('( t ^ 2 )', 'RR+')], 'lemuldivd',
             '( %s -> ( ( ( ( 2 / 3 ) x. ( %s ^ 2 ) ) x. ( t ^ 2 ) ) <_ %s <-> ( ( 2 / 3 ) x. ( %s ^ 2 ) ) <_ %s ) )' % (Av, A, KS(A), A, KQ(A)))
    kl = w.s([sl2, ld], 'mpbid', '( %s -> ( ( 2 / 3 ) x. ( %s ^ 2 ) ) <_ %s )' % (Av, A, KQ(A)))
    c.leaf('( %s ^ 2 )' % A, 'RR', c.mem('( %s ^ 2 )' % A, 'RR')); c.leaf(KQ(A), 'RR', c.mem(KQ(A), 'RR'))
    f1 = linarith(w, Av, [kl], '%s <_ ( 3 x. %s )' % (D, KQ(A)), closure=c)
    f2 = w.s([c.mem(D, 'RR'), c.mem('( 3 x. %s )' % KQ(A), 'RR'), c.mem(QQ, 'RR'), q0, f1], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( ( 3 x. %s ) x. %s ) )' % (Av, D, QQ, KQ(A), QQ))
    Drp = c.mem(D, 'RR+')
    f3 = w.s([f2, w.s([c.mem(QQ, 'RR'), c.mem('( ( 3 x. %s ) x. %s )' % (KQ(A), QQ), 'RR'), Drp], 'lemuldiv2d',
                      '( %s -> ( ( %s x. %s ) <_ ( ( 3 x. %s ) x. %s ) <-> %s <_ ( ( ( 3 x. %s ) x. %s ) / %s ) ) )' % (Av, D, QQ, KQ(A), QQ, QQ, KQ(A), QQ, D))], 'mpbid',
             '( %s -> %s <_ ( ( ( 3 x. %s ) x. %s ) / %s ) )' % (Av, QQ, KQ(A), QQ, D))
    f4a = w.s([a1(w, Av, '3cn', '3 e. CC'), c.mem(KQ(A), 'CC'), c.mem(QQ, 'CC')], 'mulassd', '( %s -> ( ( 3 x. %s ) x. %s ) = ( 3 x. %s ) )' % (Av, KQ(A), QQ, KQQ))
    f4b = w.s([a1(w, Av, '3cn', '3 e. CC'), c.mem(KQQ, 'CC'), c.mem(D, 'CC'), c.ne0(D)], 'div23d', '( %s -> ( ( 3 x. %s ) / %s ) = ( ( 3 / %s ) x. %s ) )' % (Av, KQQ, D, D, KQQ))
    f4 = eqt(w, Av, dst(w, Av, [f4a], 'oveq1d', '( ( ( 3 x. %s ) x. %s ) / %s ) = ( ( 3 x. %s ) / %s )' % (KQ(A), QQ, D, KQQ, D)), f4b)
    pw = w.s([f3, f4], 'breqtrd', '( %s -> %s <_ ( ( 3 / %s ) x. %s ) )' % (Av, QQ, D, KQQ))
    qib = dst(w, A0, [k0], 'simpld', '( t e. ( 0 (,) T ) |-> %s ) e. L^1' % QQ)
    c3d = cl.mem('( 3 / %s )' % D, 'CC')
    ib3 = w.s([c3d, c.mem(KQQ, 'CC'), i0T], 'iblmulc2', '( %s -> ( t e. ( 0 (,) T ) |-> ( ( 3 / %s ) x. %s ) ) e. L^1 )' % (A0, D, KQQ))
    il = w.s([qib, ib3, c.mem(QQ, 'RR'), c.mem('( ( 3 / %s ) x. %s )' % (D, KQQ), 'RR'), pw], 'itgle', '( %s -> %s <_ %s )' % (A0, ITG(IOO('0', 'T'), QQ), ITG(IOO('0', 'T'), '( ( 3 / %s ) x. %s )' % (D, KQQ))))
    im = w.s([c3d, c.mem(KQQ, 'CC'), i0T], 'itgmulc2', '( %s -> ( ( 3 / %s ) x. %s ) = %s )' % (A0, D, ITG(IOO('0', 'T'), KQQ), ITG(IOO('0', 'T'), '( ( 3 / %s ) x. %s )' % (D, KQQ))))
    # extend to ( 0 , R )
    Av2, m2, tr2, oo2, t02, c2, q02, k02 = pt('T', 'R', cl.ge0('T'), cl.mem('T', 'RR'))
    kq0 = w.s([c2.mem(KQ(A), 'RR'), c2.mem(QQ, 'RR'), k02, q02], 'mulge0d', '( %s -> 0 <_ %s )' % (Av2, KQQ))
    g0 = w.s([iTR, c2.mem(KQQ, 'RR'), kq0], 'itgge0', '( %s -> 0 <_ %s )' % (A0, ITG(IOO('T', 'R'), KQQ)))
    Av3, m3, tr3, oo3, t03, c3, q03, k03 = pt('0', 'R', z00, z0)
    bi = w.s([z0, cl.mem('R', 'RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( T e. ( 0 [,] R ) <-> ( T e. RR /\\ 0 <_ T /\\ T <_ R ) ) )' % A0)
    tm = w.s([w.s([cl.mem('T', 'RR'), cl.ge0('T'), tR], '3jca', '( %s -> ( T e. RR /\\ 0 <_ T /\\ T <_ R ) )' % A0), bi], 'mpbird', '( %s -> T e. ( 0 [,] R ) )' % A0)
    sp = w.s([z0, cl.mem('R', 'RR'), tm, c3.mem(KQQ, 'CC'), i0T, iTR], 'itgsplitioo',
             '( %s -> %s = ( %s + %s ) )' % (A0, ITG(IOO('0', 'R'), KQQ), ITG(IOO('0', 'T'), KQQ), ITG(IOO('T', 'R'), KQQ)))
    I0T, ITR, I0R = ITG(IOO('0', 'T'), KQQ), ITG(IOO('T', 'R'), KQQ), ITG(IOO('0', 'R'), KQQ)
    cl.leaf(I0T, 'RR', w.s([c.mem(KQQ, 'RR'), i0T], 'itgrecl', '( %s -> %s e. RR )' % (A0, I0T)))
    cl.leaf(ITR, 'RR', w.s([c2.mem(KQQ, 'RR'), iTR], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITR)))
    cl.leaf(I0R, 'RR', w.s([c3.mem(KQQ, 'RR'), i0R], 'itgrecl', '( %s -> %s e. RR )' % (A0, I0R)))
    ext = linarith(w, A0, [sp, g0], '%s <_ %s' % (I0T, I0R), closure=cl)
    ext2 = w.s([ext, v0R], 'breqtrd', '( %s -> %s <_ ( 2 x. %s ) )' % (A0, I0T, KSUM('0', 'R')))
    cl.leaf('( 2 x. %s )' % KSUM('0', 'R'), 'RR', w.s([v0R, cl.mem(I0R, 'RR')], 'eqeltrrd', '( %s -> ( 2 x. %s ) e. RR )' % (A0, KSUM('0', 'R'))))
    m3_ = w.s([cl.mem(I0T, 'RR'), cl.mem('( 2 x. %s )' % KSUM('0', 'R'), 'RR'), cl.mem('( 3 / %s )' % D, 'RR'), ltle(w, A0, cl, cl.gt0('( 3 / %s )' % D)), ext2], 'lemul2ad',
              '( %s -> ( ( 3 / %s ) x. %s ) <_ ( ( 3 / %s ) x. ( 2 x. %s ) ) )' % (A0, D, I0T, D, KSUM('0', 'R')))
    kv = dst(w, A0, [k0], 'simprd', '%s = %s' % (ITG(TT, ABS2(SX('t'))), ITG(IOO('0', 'T'), QQ)))
    fin_ = w.s([w.s([kv, w.s([il, eqc(w, A0, im)], 'breqtrrd' if False else 'breqtrd', '( %s -> %s <_ ( ( 3 / %s ) x. %s ) )' % (A0, ITG(IOO('0', 'T'), QQ), D, I0T))], 'eqbrtrd',
                    '( %s -> %s <_ ( ( 3 / %s ) x. %s ) )' % (A0, ITG(TT, ABS2(SX('t'))), D, I0T)), m3_], 'letrd' if False else 'id', 'x') if False else None
    s1 = w.s([il, eqc(w, A0, im)], 'breqtrd', '( %s -> %s <_ ( ( 3 / %s ) x. %s ) )' % (A0, ITG(IOO('0', 'T'), QQ), D, I0T))
    s2 = w.s([kv, s1], 'eqbrtrd', '( %s -> %s <_ ( ( 3 / %s ) x. %s ) )' % (A0, ITG(TT, ABS2(SX('t'))), D, I0T))
    lhsr = w.s([kv, cl.mem(ITG(IOO('0', 'T'), QQ), 'RR') if False else w.s([c.mem(QQ, 'RR'), qib], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITG(IOO('0', 'T'), QQ)))], 'eqeltrd',
               '( %s -> %s e. RR )' % (A0, ITG(TT, ABS2(SX('t')))))
    w.s([lhsr, cl.mem('( ( 3 / %s ) x. %s )' % (D, I0T), 'RR'), cl.mem('( ( 3 / %s ) x. ( 2 x. %s ) )' % (D, KSUM('0', 'R')), 'RR'), s2, m3_], 'letrd',
        '( %s -> %s <_ ( ( 3 / %s ) x. ( 2 x. %s ) ) )' % (A0, ITG(TT, ABS2(SX('t'))), D, KSUM('0', 'R')))
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvrefl()
    mvsx()
    mvsxdv()
    mvkm0()
    mvkm2()
    mvkm1()
