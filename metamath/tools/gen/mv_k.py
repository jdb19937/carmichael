"""Sortie MV, section K: LargeValues (mvdisj, mvpcs, mvdfam, mvlvm)."""
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


def hyps(w, lab):
    for n, f in HYPS[lab]:
        w.s([], n, f, name='h' + n.split('.')[-1])


def mvdisj():
    w = W('mvdisj', 'Unit windows around 1-separated points of [ -u T , T ] are disjoint subintervals of ( -u ( T + 1 ) , T + 1 ): the window integrals of a nonnegative continuous function sum to at most its integral there (LargeValues per_char_sobolev, hsum_r).')
    hyps(w, 'mvdisj')
    A0 = 'ph'
    pf = dst(w, A0, ['p'], 'simp1d' if False else 'id', 'x') if False else w.s(['p'], 'simp1d', '( ph -> P e. Fin )')
    yf = w.s(['p'], 'simp2d', '( ph -> Y : P --> RR )'); tr = w.s(['p'], 'simp3d', '( ph -> T e. RR )')
    K = T1; kl = '-u ( T + 1 )'; kh = '( T + 1 )'
    c0 = Closure(w, A0, {'T': ('RR', tr)})
    klr = c0.mem(kl, 'RR'); khr = c0.mem(kh, 'RR')
    JIv = lambda v: JI1('( Y ` %s )' % v)
    IF_ = lambda v: 'if ( t e. %s , X , 0 )' % JIv(v)
    Ai = '( ph /\\ i e. P )'
    Li = lambda s_: lift(w, s_, Ai)
    ip = w.s([], 'simpr', '( %s -> i e. P )' % Ai)
    YI = '( Y ` i )'
    yi = w.s([Li(yf), ip], 'ffvelcdmd', '( %s -> %s e. RR )' % (Ai, YI))
    rg, _ = w.wcongr('( abs ` ( Y ` a ) ) <_ T', {'a': 'i'}, 'a = i', {'a': w.s([], 'id', '( a = i -> a = i )')})
    yb = w.s([rg, Li('a'), ip], 'rspcdva', '( %s -> ( abs ` %s ) <_ T )' % (Ai, YI))
    ab = w.s([yb, w.s([yi, Li(tr)], 'absled', '( %s -> ( ( abs ` %s ) <_ T <-> ( -u T <_ %s /\\ %s <_ T ) ) )' % (Ai, YI, YI, YI))], 'mpbid', '( %s -> ( -u T <_ %s /\\ %s <_ T ) )' % (Ai, YI, YI))
    ci = Closure(w, Ai, {'T': ('RR', Li(tr)), YI: ('RR', yi)})
    lo = '( %s - ( 1 / 2 ) )' % YI; hi = '( %s + ( 1 / 2 ) )' % YI
    l1 = linarith(w, Ai, [dst(w, Ai, [ab], 'simpld', '-u T <_ %s' % YI)], '%s <_ %s' % (kl, lo), closure=ci)
    l2 = linarith(w, Ai, [dst(w, Ai, [ab], 'simprd', '%s <_ T' % YI)], '%s <_ %s' % (hi, kh), closure=ci)
    sub = ap(w, Ai, 'ioossioo', [J(w, Ai, w.s([Li(klr)], 'rexrd', '( %s -> %s e. RR* )' % (Ai, kl)), w.s([Li(khr)], 'rexrd', '( %s -> %s e. RR* )' % (Ai, kh))), J(w, Ai, l1, l2)],
             '%s C_ %s' % (JIv('i'), K))
    Ait = '( %s /\\ t e. %s )' % (Ai, JIv('i'))
    tj = w.s([], 'simpr', '( %s -> t e. %s )' % (Ait, JIv('i')))
    ift = ap(w, Ait, 'iftrue', [tj], '%s = X' % IF_('i'))
    e1 = eqc(w, Ai, dst(w, Ai, [ift], 'itgeq2dv', '%s = %s' % (ITG(JIv('i'), IF_('i')), ITG(JIv('i'), 'X'))))
    Aid = '( %s /\\ t e. ( %s \\ %s ) )' % (Ai, K, JIv('i'))
    nd = dst(w, Aid, [w.s([], 'simpr', '( %s -> t e. ( %s \\ %s ) )' % (Aid, K, JIv('i')))], 'eldifbd', '-. t e. %s' % JIv('i'))
    iff = ap(w, Aid, 'iffalse', [nd], '%s = 0' % IF_('i'))
    e2 = dst(w, Ai, [sub, iff], 'itgss', '%s = %s' % (ITG(JIv('i'), IF_('i')), ITG(K, IF_('i'))))
    e12 = eqt(w, Ai, e1, e2)
    xrk = w.s([w.inst('elioore'), 'r'], 'sylan2', '( ( ph /\\ t e. %s ) -> X e. RR )' % K)
    Atki = '( ph /\\ ( t e. %s /\\ i e. P ) )' % K
    xrtk = w.s([w.s([], 'simpl', '( %s -> ph )' % Atki), w.s([], 'simprl', '( %s -> t e. %s )' % (Atki, K))], 'jca', '( %s -> ( ph /\\ t e. %s ) )' % (Atki, K))
    xrtk2 = w.s([xrtk, xrk], 'syl', '( %s -> X e. RR )' % Atki)
    ifr = lambda ante, xst: w.s([xst, a1(w, ante, '0re', '0 e. RR')], 'ifcld', '( %s -> %s e. RR )' % (ante, IF_('i')))
    ifc = w.s([ifr(Atki, xrtk2)], 'recnd', '( %s -> %s e. CC )' % (Atki, IF_('i')))
    ibj0 = w.s([ci.mem(lo, 'RR'), ci.mem(hi, 'RR'), Li('c')], 'lsibl', '( %s -> ( t e. %s |-> X ) e. L^1 )' % (Ai, JIv('i')))
    mq = dst(w, Ai, [ift], 'mpteq2dva', '( t e. %s |-> %s ) = ( t e. %s |-> X )' % (JIv('i'), IF_('i'), JIv('i')))
    ibj = dst(w, Ai, [mq, ibj0], 'eqeltrd', '( t e. %s |-> %s ) e. L^1' % (JIv('i'), IF_('i')))
    Aij = Ait
    xrj = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Aij, Ai)), w.inst('simpl')], 'syl', '( %s -> ph )' % Aij),
               w.s([w.s([], 'simpr', '( %s -> t e. %s )' % (Aij, JIv('i'))), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % Aij), 'r'], 'syl2anc', '( %s -> X e. RR )' % Aij)
    ifcj = w.s([ifr(Aij, xrj)], 'recnd', '( %s -> %s e. CC )' % (Aij, IF_('i')))
    kdv = a1(w, Ai, 'ioombl', '%s e. dom vol' % K)
    ibk = dst(w, Ai, [sub, kdv, ifcj, iff, ibj], 'iblss2', '( t e. %s |-> %s ) e. L^1' % (K, IF_('i')))
    fs = dst(w, A0, [a1(w, A0, 'ioombl', '%s e. dom vol' % K), pf, ifc, ibk], 'itgfsum',
             '( ( t e. %s |-> sum_ i e. P %s ) e. L^1 /\\ %s = sum_ i e. P %s )' % (K, IF_('i'), ITG(K, 'sum_ i e. P %s' % IF_('i')), ITG(K, IF_('i'))))
    fs1 = dst(w, A0, [fs], 'simpld', '( t e. %s |-> sum_ i e. P %s ) e. L^1' % (K, IF_('i')))
    fs2 = dst(w, A0, [fs], 'simprd', '%s = sum_ i e. P %s' % (ITG(K, 'sum_ i e. P %s' % IF_('i')), ITG(K, IF_('i'))))
    se = dst(w, A0, [e12], 'sumeq2dv', 'sum_ i e. P %s = sum_ i e. P %s' % (ITG(JIv('i'), 'X'), ITG(K, IF_('i'))))
    Ak = '( ph /\\ t e. %s )' % K
    Lk = lambda s_: lift(w, s_, Ak)
    x0k = w.s([w.inst('elioore'), 'n'], 'sylan2', '( ( ph /\\ t e. %s ) -> 0 <_ X )' % K)
    pts = w.s([Lk(pf), Lk(yf), a1(w, Ak, '1rp', '1 e. RR+')], '3jca', '( %s -> ( P e. Fin /\\ Y : P --> RR /\\ 1 e. RR+ ) )' % Ak)
    pt = ap(w, Ak, 'lsdisjpt', [J(w, Ak, pts, Lk('s'), J(w, Ak, xrk, x0k))], 'sum_ i e. P %s <_ X' % IF_('i'))
    Akti = '( %s /\\ i e. P )' % Ak
    sr = dst(w, Ak, [Lk(pf), w.s([lift(w, xrk, Akti), a1(w, Akti, '0re', '0 e. RR')], 'ifcld', '( %s -> %s e. RR )' % (Akti, IF_('i')))], 'fsumrecl', 'sum_ i e. P %s e. RR' % IF_('i'))
    ibx = w.s([klr, khr, 'c'], 'lsibl', '( ph -> ( t e. %s |-> X ) e. L^1 )' % K)
    il = dst(w, A0, [fs1, ibx, sr, xrk, pt], 'itgle', '%s <_ %s' % (ITG(K, 'sum_ i e. P %s' % IF_('i')), ITG(K, 'X')))
    dst(w, A0, [eqt(w, A0, se, eqc(w, A0, fs2)), il], 'eqbrtrd', STATEMENTS['mvdisj'].split(' -> ', 1)[1][:-2])
    qedlast(w)
    go(w)



def mvpcs():
    w = W('mvpcs', 'The Sobolev step over 1-separated points of [ -u T , T ]: sum | F ( Y_i ) | ^ 2 <_ 2 S. | F | ^ 2 + S. | G | ^ 2 over ( -u ( T + 1 ) , T + 1 ) for F with continuous derivative G (LargeValues per_char_sobolev).')
    A0 = '( %s /\\ ( P e. Fin /\\ Y : P --> RR /\\ T e. RR ) /\\ ( A. a e. P ( abs ` ( Y ` a ) ) <_ T /\\ %s ) )' % (HF, SEP1)
    P_ = parts(w, A0)
    hf, ff, dfg, gcn = P_[HF], P_['F : RR --> CC'], P_['( RR _D F ) = G'], P_['G e. %s' % CNR]
    pf, yf, tr = P_['P e. Fin'], P_['Y : P --> RR'], P_['T e. RR']
    yb, sep = P_['A. a e. P ( abs ` ( Y ` a ) ) <_ T'], P_[SEP1]
    from z4blib import fmap
    gf = ap(w, A0, 'cncff', [gcn], 'G : RR --> CC')
    dm = eqt(w, A0, dst(w, A0, [dfg], 'dmeqd', 'dom ( RR _D F ) = dom G'), ap(w, A0, 'fdm', [gf], 'dom G = RR'))
    j3 = J(w, A0, a1(w, A0, 'ax-resscn', 'RR C_ CC'), ff, a1(w, A0, 'ssid', 'RR C_ RR'))
    fcn = ap(w, A0, 'dvcn', [J(w, A0, j3, dm)], 'F e. %s' % CNR)
    fm = fmap(w, A0, fcn, 'F', 't'); gm = fmap(w, A0, gcn, 'G', 't')
    At = '( %s /\\ t e. RR )' % A0
    trr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    ct = Closure(w, At, {'( F ` t )': ('CC', w.s([lift(w, ff, At), trr], 'ffvelcdmd', '( %s -> ( F ` t ) e. CC )' % At)),
                         '( G ` t )': ('CC', w.s([lift(w, gf, At), trr], 'ffvelcdmd', '( %s -> ( G ` t ) e. CC )' % At)), 't': ('RR', trr)})
    cn = CN(w, A0, 't', 'RR', a1(w, A0, 'ax-resscn', 'RR C_ CC'), Closure(w, A0, {}), ct, known={'( F ` t )': fm, '( G ` t )': gm})
    F2 = ABS2('( F ` t )'); G2 = ABS2('( G ` t )'); FG = '( ( 2 x. ( abs ` ( F ` t ) ) ) x. ( abs ` ( G ` t ) ) )'
    X = '( ( 2 x. %s ) + %s )' % (F2, G2)
    Ai = '( %s /\\ i e. P )' % A0
    ip = w.s([], 'simpr', '( %s -> i e. P )' % Ai)
    YI = '( Y ` i )'
    yi = w.s([lift(w, yf, Ai), ip], 'ffvelcdmd', '( %s -> %s e. RR )' % (Ai, YI))
    Ji = JI1(YI)
    sb = ap(w, Ai, 'lssob', [J(w, Ai, lift(w, hf, Ai), J(w, Ai, a1(w, Ai, '1rp', '1 e. RR+'), yi))],
            '( ( abs ` ( F ` %s ) ) ^ 2 ) <_ ( ( ( 1 / 1 ) x. %s ) + %s )' % (YI, ITG(Ji, F2), ITG(Ji, FG)))
    ci = Closure(w, Ai, {YI: ('RR', yi)})
    lo = ci.mem('( %s - ( 1 / 2 ) )' % YI, 'RR'); hi = ci.mem('( %s + ( 1 / 2 ) )' % YI, 'RR')
    def ibl(E):
        return w.s([lo, hi, lift(w, cn(E), Ai)], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (Ai, Ji, E))
    Ait = '( %s /\\ t e. %s )' % (Ai, Ji)
    tri = ap(w, Ait, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Ait, Ji))], 't e. RR')
    cit = Closure(w, Ait, {'( F ` t )': ('CC', w.s([lift(w, ff, Ait), tri], 'ffvelcdmd', '( %s -> ( F ` t ) e. CC )' % Ait)),
                           '( G ` t )': ('CC', w.s([lift(w, gf, Ait), tri], 'ffvelcdmd', '( %s -> ( G ` t ) e. CC )' % Ait))})
    AF = '( abs ` ( F ` t ) )'; AG = '( abs ` ( G ` t ) )'
    for t_ in [AF, AG]:
        cit.leaf(t_, 'RR', cit.mem(t_, 'RR'))
    sqe = ringeqp(w, Ait, '( ( %s - %s ) ^ 2 )' % (AF, AG), '( ( %s + %s ) - %s )' % (F2, G2, FG), Closure(w, Ait, {AF: ('RR', cit.mem(AF, 'RR')), AG: ('RR', cit.mem(AG, 'RR'))}))
    sq0 = w.s([cit.mem('( %s - %s )' % (AF, AG), 'RR')], 'sqge0d', '( %s -> 0 <_ ( ( %s - %s ) ^ 2 ) )' % (Ait, AF, AG))
    for t_ in [F2, G2, FG, '( ( %s - %s ) ^ 2 )' % (AF, AG)]:
        cit.leaf(t_, 'RR', cit.mem(t_, 'RR'))
    pw = linarith(w, Ait, [sqe, sq0], '%s <_ ( %s + %s )' % (FG, F2, G2), closure=cit)
    il = w.s([ibl(FG), ibl('( %s + %s )' % (F2, G2)), cit.mem(FG, 'RR'), cit.mem('( %s + %s )' % (F2, G2), 'RR'), pw], 'itgle', '( %s -> %s <_ %s )' % (Ai, ITG(Ji, FG), ITG(Ji, '( %s + %s )' % (F2, G2))))
    ia = w.s([cit.mem(F2, 'CC'), ibl(F2), cit.mem(G2, 'CC'), ibl(G2)], 'itgadd', '( %s -> %s = ( %s + %s ) )' % (Ai, ITG(Ji, '( %s + %s )' % (F2, G2)), ITG(Ji, F2), ITG(Ji, G2)))
    ix = w.s([cit.mem('( 2 x. %s )' % F2, 'CC'), ibl('( 2 x. %s )' % F2), cit.mem(G2, 'CC'), ibl(G2)], 'itgadd', '( %s -> %s = ( %s + %s ) )' % (Ai, ITG(Ji, X), ITG(Ji, '( 2 x. %s )' % F2), ITG(Ji, G2)))
    im = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % Ai), cit.mem(F2, 'CC'), ibl(F2)], 'itgmulc2', '( %s -> ( 2 x. %s ) = %s )' % (Ai, ITG(Ji, F2), ITG(Ji, '( 2 x. %s )' % F2)))
    d1 = eqt(w, Ai, dst(w, Ai, [a1(w, Ai, '1div1e1', '( 1 / 1 ) = 1')], 'oveq1d', '( ( 1 / 1 ) x. %s ) = ( 1 x. %s )' % (ITG(Ji, F2), ITG(Ji, F2))),
             w.s([w.s([cit.mem(F2, 'CC'), ibl(F2)], 'itgcl', '( %s -> %s e. CC )' % (Ai, ITG(Ji, F2)))], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (Ai, ITG(Ji, F2), ITG(Ji, F2))))
    cr = Closure(w, Ai, {})
    for t_, E_ in [(ITG(Ji, F2), F2), (ITG(Ji, G2), G2), (ITG(Ji, FG), FG), (ITG(Ji, '( %s + %s )' % (F2, G2)), '( %s + %s )' % (F2, G2)), (ITG(Ji, X), X), (ITG(Ji, '( 2 x. %s )' % F2), '( 2 x. %s )' % F2)]:
        cr.leaf(t_, 'RR', w.s([cit.mem(E_, 'RR'), ibl(E_)], 'itgrecl', '( %s -> %s e. RR )' % (Ai, t_)))
    cr.leaf('( ( 1 / 1 ) x. %s )' % ITG(Ji, F2), 'RR', w.s([d1, cr.mem(ITG(Ji, F2), 'RR')], 'eqeltrd', '( %s -> ( ( 1 / 1 ) x. %s ) e. RR )' % (Ai, ITG(Ji, F2))))
    cr.leaf(ABS2('( F ` %s )' % YI), 'RR', w.s([w.s([w.s([lift(w, ff, Ai), yi], 'ffvelcdmd', '( %s -> ( F ` %s ) e. CC )' % (Ai, YI))], 'abscld', '( %s -> ( abs ` ( F ` %s ) ) e. RR )' % (Ai, YI))],
                                                'resqcld', '( %s -> %s e. RR )' % (Ai, ABS2('( F ` %s )' % YI))))
    pti = linarith(w, Ai, [sb, d1, il, ia, ix, im], '%s <_ %s' % (ABS2('( F ` %s )' % YI), ITG(Ji, X)), closure=cr)
    fl = w.s([pf, cr.mem(ABS2('( F ` %s )' % YI), 'RR'), cr.mem(ITG(Ji, X), 'RR'), pti], 'fsumle', '( %s -> sum_ i e. P %s <_ sum_ i e. P %s )' % (A0, ABS2('( F ` %s )' % YI), ITG(Ji, X)))
    # mvdisj with X
    xr = ct.mem(X, 'RR')
    x0 = w.s([ct.mem('( 2 x. %s )' % F2, 'RR'), ct.mem(G2, 'RR'), w.s([ct.mem('( 2 x. %s )' % F2, 'RR') if False else w.s([], '2re', '2 e. RR') and a1(w, At, '2re', '2 e. RR'),
                                                                    ct.mem(F2, 'RR'), a1(w, At, '0le2', '0 <_ 2'), w.s([ct.mem(AF, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (At, F2))], 'mulge0d', '( %s -> 0 <_ ( 2 x. %s ) )' % (At, F2)),
              w.s([ct.mem(AG, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (At, G2))], 'addge0d', '( %s -> 0 <_ %s )' % (At, X))
    dj = w.s([w.s([pf, yf, tr], '3jca', '( %s -> ( P e. Fin /\\ Y : P --> RR /\\ T e. RR ) )' % A0), yb, sep, cn(X), xr, x0], 'mvdisj', '( %s -> sum_ i e. P %s <_ %s )' % (A0, ITG(Ji, X), ITG(T1, X)))
    c0 = Closure(w, A0, {'T': ('RR', tr)})
    K = T1
    def iblK(E):
        return w.s([c0.mem('-u ( T + 1 )', 'RR'), c0.mem('( T + 1 )', 'RR'), cn(E)], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, K, E))
    Atk = '( %s /\\ t e. %s )' % (A0, K)
    tk = ap(w, Atk, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Atk, K))], 't e. RR')
    ck = Closure(w, Atk, {'( F ` t )': ('CC', w.s([lift(w, ff, Atk), tk], 'ffvelcdmd', '( %s -> ( F ` t ) e. CC )' % Atk)),
                          '( G ` t )': ('CC', w.s([lift(w, gf, Atk), tk], 'ffvelcdmd', '( %s -> ( G ` t ) e. CC )' % Atk))})
    kx = w.s([ck.mem('( 2 x. %s )' % F2, 'CC'), iblK('( 2 x. %s )' % F2), ck.mem(G2, 'CC'), iblK(G2)], 'itgadd', '( %s -> %s = ( %s + %s ) )' % (A0, ITG(K, X), ITG(K, '( 2 x. %s )' % F2), ITG(K, G2)))
    km = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), ck.mem(F2, 'CC'), iblK(F2)], 'itgmulc2', '( %s -> ( 2 x. %s ) = %s )' % (A0, ITG(K, F2), ITG(K, '( 2 x. %s )' % F2)))
    val = eqt(w, A0, kx, dst(w, A0, [eqc(w, A0, km)], 'oveq1d', '( %s + %s ) = ( ( 2 x. %s ) + %s )' % (ITG(K, '( 2 x. %s )' % F2), ITG(K, G2), ITG(K, F2), ITG(K, G2))))
    lhs = 'sum_ i e. P %s' % ABS2('( F ` %s )' % YI)
    w.s([w.s([fl, dj], 'letrd' if False else 'id', 'x') if False else None][:0] or [], 'id', 'x') if False else None
    sa = w.s([pf, cr.mem(ABS2('( F ` %s )' % YI), 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (A0, lhs))
    sb2 = w.s([pf, cr.mem(ITG(Ji, X), 'RR')], 'fsumrecl', '( %s -> sum_ i e. P %s e. RR )' % (A0, ITG(Ji, X)))
    kr = w.s([ck.mem(X, 'RR'), iblK(X)], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITG(K, X)))
    w.s([w.s([sa, sb2, kr, fl, dj], 'letrd', '( %s -> %s <_ %s )' % (A0, lhs, ITG(K, X))), val], 'breqtrd',
        '( %s -> %s <_ ( ( 2 x. %s ) + %s ) )' % (A0, lhs, ITG(K, F2), ITG(K, G2)))
    qedlast(w)
    go(w)


from mv_j import aval, chv, eqids, Dd, Ld
CXU = '( u e. %s |-> ( ( A ` u ) x. %s ) )' % (FZM, CHV('x', 'u'))
LFU = '( u e. %s |-> -u ( log ` u ) )' % FZM
EXM = '( exp ` ( _i x. ( -u ( log ` m ) x. t ) ) )'


def vals(w, ante, v, vmem, xmem, aok):
    vn = ap(w, ante, 'elfznn', [vmem], '%s e. NN' % v)
    vz = w.s([vn], 'nnzd', '( %s -> %s e. ZZ )' % (ante, v))
    av = aval(w, ante, v, lift(w, aok, ante), vmem)
    cv = chv(w, ante, v, None, xmem, vz)
    cval = '( ( A ` %s ) x. %s )' % (v, CHV('x', v))
    c1 = fvmd(w, ante, 'u', FZM, '( ( A ` u ) x. %s )' % CHV('x', 'u'), v, vmem, w.s([av, cv], 'mulcld', '( %s -> %s e. CC )' % (ante, cval)))
    lr = w.s([w.s([vn], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, v))], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (ante, v))
    l1 = fvmd(w, ante, 'u', FZM, '-u ( log ` u )', v, vmem, w.s([w.s([lr], 'renegcld', '( %s -> -u ( log ` %s ) e. RR )' % (ante, v))], 'recnd', '( %s -> -u ( log ` %s ) e. CC )' % (ante, v)))
    ci = w.s([c1, w.s([av, cv], 'mulcld', '( %s -> %s e. CC )' % (ante, cval))], 'eqeltrd', '( %s -> ( %s ` %s ) e. CC )' % (ante, CXU, v))
    li = w.s([l1, w.s([lr], 'renegcld', '( %s -> -u ( log ` %s ) e. RR )' % (ante, v))], 'eqeltrd', '( %s -> ( %s ` %s ) e. RR )' % (ante, LFU, v))
    return dict(vn=vn, vz=vz, av=av, cv=cv, c1=c1, l1=l1, lr=lr, cval=cval, ci=ci, li=li)


def sxm(t_):
    return 'sum_ m e. %s ( ( %s ` m ) x. ( exp ` ( _i x. ( ( %s ` m ) x. %s ) ) ) )' % (FZM, CXU, LFU, t_)


def sxdm(t_):
    return 'sum_ m e. %s ( ( ( %s ` m ) x. ( _i x. ( %s ` m ) ) ) x. ( exp ` ( _i x. ( ( %s ` m ) x. %s ) ) ) )' % (FZM, CXU, LFU, LFU, t_)


def sx_to_ds(w, ante, tau, taur, xmem, aok, deriv=False):
    """( ante -> sxm(tau) = DS(x,tau) ) (or sxdm(tau) = DS_AD(x,tau))"""
    Am_ = '( %s /\\ m e. %s )' % (ante, FZM)
    vm = vals(w, Am_, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (Am_, FZM)), lift(w, xmem, Am_), aok)
    EXt = '( exp ` ( _i x. ( -u ( log ` m ) x. %s ) ) )' % tau
    ee = dst(w, Am_, [dst(w, Am_, [dst(w, Am_, [vm['l1']], 'oveq1d', '( ( %s ` m ) x. %s ) = ( -u ( log ` m ) x. %s )' % (LFU, tau, tau))], 'oveq2d',
                                  '( _i x. ( ( %s ` m ) x. %s ) ) = ( _i x. ( -u ( log ` m ) x. %s ) )' % (LFU, tau, tau))], 'fveq2d',
             '( exp ` ( _i x. ( ( %s ` m ) x. %s ) ) ) = %s' % (LFU, tau, EXt))
    if not deriv:
        tm = dst(w, Am_, [vm['c1'], ee], 'oveq12d', '( ( %s ` m ) x. ( exp ` ( _i x. ( ( %s ` m ) x. %s ) ) ) ) = ( ( ( A ` m ) x. %s ) x. %s )' % (CXU, LFU, tau, CHV('x', 'm'), EXt))
        body_m = '( ( ( A ` m ) x. %s ) x. %s )' % (CHV('x', 'm'), EXt)
        lhs = sxm(tau); tgt = DS('x', tau)
    else:
        adv = fvmd(w, Am_, 'u', 'NN', '( ( A ` u ) x. ( _i x. -u ( log ` u ) ) )', 'm', vm['vn'],
                   w.s([vm['av'], w.s([a1(w, Am_, 'ax-icn', '_i e. CC'), w.s([w.s([vm['lr']], 'renegcld', '( %s -> -u ( log ` m ) e. RR )' % Am_)], 'recnd', '( %s -> -u ( log ` m ) e. CC )' % Am_)],
                                  'mulcld', '( %s -> ( _i x. -u ( log ` m ) ) e. CC )' % Am_)], 'mulcld', '( %s -> ( ( A ` m ) x. ( _i x. -u ( log ` m ) ) ) e. CC )' % Am_))
        k1 = dst(w, Am_, [vm['c1'], dst(w, Am_, [vm['l1']], 'oveq2d', '( _i x. ( %s ` m ) ) = ( _i x. -u ( log ` m ) )' % LFU)], 'oveq12d',
                 '( ( %s ` m ) x. ( _i x. ( %s ` m ) ) ) = ( ( ( A ` m ) x. %s ) x. ( _i x. -u ( log ` m ) ) )' % (CXU, LFU, CHV('x', 'm')))
        cc = Closure(w, Am_, {'( A ` m )': ('CC', vm['av']), CHV('x', 'm'): ('CC', vm['cv']), '( log ` m )': ('RR', vm['lr']), '_i': ('CC', a1(w, Am_, 'ax-icn', '_i e. CC'))})
        k2 = ringeq(w, Am_, '( ( ( A ` m ) x. %s ) x. ( _i x. -u ( log ` m ) ) )' % CHV('x', 'm'), '( ( ( A ` m ) x. ( _i x. -u ( log ` m ) ) ) x. %s )' % CHV('x', 'm'), cc)
        k3 = dst(w, Am_, [eqc(w, Am_, adv)], 'oveq1d', '( ( ( A ` m ) x. ( _i x. -u ( log ` m ) ) ) x. %s ) = ( ( %s ` m ) x. %s )' % (CHV('x', 'm'), ADM, CHV('x', 'm')))
        cf = eqt(w, Am_, eqt(w, Am_, k1, k2), k3)
        tm = dst(w, Am_, [cf, ee], 'oveq12d', '( ( ( %s ` m ) x. ( _i x. ( %s ` m ) ) ) x. ( exp ` ( _i x. ( ( %s ` m ) x. %s ) ) ) ) = ( ( ( %s ` m ) x. %s ) x. %s )' % (
            CXU, LFU, LFU, tau, ADM, CHV('x', 'm'), EXt))
        body_m = '( ( ( %s ` m ) x. %s ) x. %s )' % (ADM, CHV('x', 'm'), EXt)
        lhs = sxdm(tau); tgt = DS('x', tau, A=ADM)
    s1 = dst(w, ante, [tm], 'sumeq2dv', '%s = sum_ m e. %s %s' % (lhs, FZM, body_m))
    subn, new = w.congr(body_m, {'m': 'n'}, 'm = n', {'m': w.s([], 'id', '( m = n -> m = n )')})
    assert 'sum_ n e. %s %s' % (FZM, new) == tgt, (new, tgt)
    cbv = w.s([subn], 'cbvsumv', 'sum_ m e. %s %s = %s' % (FZM, body_m, tgt))
    return eqt(w, ante, s1, w.s([cbv], 'a1i', '( %s -> sum_ m e. %s %s = %s )' % (ante, FZM, body_m, tgt)))


def mvdfam1():
    w = W('mvdfam1', 'The discrete mean value bound for one character: the points of a 1-spaced family carrying the character x satisfy the Sobolev bound with the polynomial and its derivative (LargeValues mean_value_chars_discrete_family, hper).')
    A0 = '( %s /\\ x e. %s )' % (HFX, Dd)
    P_ = parts(w, A0)
    nn, tr, t2, mn0, aok = P_['N e. NN'], P_['T e. RR'], P_['2 <_ T'], P_['M e. NN0'], P_[AOK]
    sfin, kf, yf, rng, sep = P_['S e. Fin'], P_['K : S --> %s' % Dd], P_['Y : S --> RR'], P_[RNGF], P_[SEPF]
    xm = P_['x e. %s' % Dd]
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZM))
    Axa = '( %s /\\ c e. %s )' % (A0, FZM)
    va = vals(w, Axa, 'c', w.s([], 'simpr', '( %s -> c e. %s )' % (Axa, FZM)), lift(w, xm, Axa), aok)
    hq = w.s([w.s([va['ci'], va['li']], 'jca', '( %s -> ( ( %s ` c ) e. CC /\\ ( %s ` c ) e. RR ) )' % (Axa, CXU, LFU))], 'ralrimiva',
             '( %s -> A. c e. %s ( ( %s ` c ) e. CC /\\ ( %s ` c ) e. RR ) )' % (A0, FZM, CXU, LFU))
    hk = w.s([fz, hq], 'jca', '( %s -> ( %s e. Fin /\\ A. c e. %s ( ( %s ` c ) e. CC /\\ ( %s ` c ) e. RR ) ) )' % (A0, FZM, FZM, CXU, LFU))
    F = '( y e. RR |-> %s )' % sxm('y'); G = '( y e. RR |-> %s )' % sxdm('y')
    dv = ap(w, A0, 'mvsxdv', [hk], '( ( RR _D %s ) = %s /\\ %s e. %s /\\ %s e. %s )' % (F, G, F, CNR, G, CNR))
    At = '( %s /\\ y e. RR )' % A0
    trr = w.s([], 'simpr', '( %s -> y e. RR )' % At)
    Atm = '( %s /\\ m e. %s )' % (At, FZM)
    vm = vals(w, Atm, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (Atm, FZM)), lift(w, xm, Atm), aok)
    cm = Closure(w, Atm, {'( %s ` m )' % CXU: ('CC', vm['ci']), '( %s ` m )' % LFU: ('RR', vm['li']), 'y': ('RR', lift(w, trr, Atm)), '_i': ('CC', a1(w, Atm, 'ax-icn', '_i e. CC'))})
    sxc = w.s([lift(w, fz, At), cm.mem('( ( %s ` m ) x. ( exp ` ( _i x. ( ( %s ` m ) x. y ) ) ) )' % (CXU, LFU), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (At, sxm('y')))
    ff = dst(w, A0, [sxc], 'fmptd', '%s : RR --> CC' % F)
    hf = w.s([ff, w.s([dv], 'simp1d', '( %s -> ( RR _D %s ) = %s )' % (A0, F, G)), w.s([dv], 'simp3d', '( %s -> %s e. %s )' % (A0, G, CNR))], '3jca',
             '( %s -> ( %s : RR --> CC /\\ ( RR _D %s ) = %s /\\ %s e. %s ) )' % (A0, F, F, G, G, CNR))
    # the fiber as a point set
    SX_ = SXF
    ss = a1(w, A0, 'ssrab2', '%s C_ S' % SX_)
    pfin = w.s([sfin, ss], 'ssfid', '( %s -> %s e. Fin )' % (A0, SX_))
    YR = '( Y |` %s )' % SX_
    yr = w.s([yf, ss], 'fssresd', '( %s -> %s : %s --> RR )' % (A0, YR, SX_))
    def elem(v_, ante, memst):
        sub_, _ = w.wcongr('( K ` q ) = x', {'q': v_}, 'q = %s' % v_, {'q': w.s([], 'id', '( q = %s -> q = %s )' % (v_, v_))})
        er_ = w.s([sub_], 'elrab', '( %s e. %s <-> ( %s e. S /\\ ( K ` %s ) = x ) )' % (v_, SX_, v_, v_))
        return w.s([memst, w.s([er_], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. S /\\ ( K ` %s ) = x ) ) )' % (ante, v_, SX_, v_, v_))], 'mpbid', '( %s -> ( %s e. S /\\ ( K ` %s ) = x ) )' % (ante, v_, v_))
    # range (letters c, d: the antecedent binds a, b)
    Aa = '( %s /\\ c e. %s )' % (A0, SX_)
    ea = elem('c', Aa, w.s([], 'simpr', '( %s -> c e. %s )' % (Aa, SX_)))
    asb = dst(w, Aa, [ea], 'simpld', 'c e. S')
    cr_, _ = w.wcongr('( abs ` ( Y ` a ) ) <_ T', {'a': 'c'}, 'a = c', {'a': w.s([], 'id', '( a = c -> a = c )')})
    rga2 = w.s([cr_, lift(w, rng, Aa), asb], 'rspcdva', '( %s -> ( abs ` ( Y ` c ) ) <_ T )' % Aa)
    fva = ap(w, Aa, 'fvres', [w.s([], 'simpr', '( %s -> c e. %s )' % (Aa, SX_))], '( %s ` c ) = ( Y ` c )' % YR)
    rgr = w.s([dst(w, Aa, [fva], 'fveq2d', '( abs ` ( %s ` c ) ) = ( abs ` ( Y ` c ) )' % YR), rga2], 'eqbrtrd', '( %s -> ( abs ` ( %s ` c ) ) <_ T )' % (Aa, YR))
    rgall = w.s([rgr], 'ralrimiva', '( %s -> A. c e. %s ( abs ` ( %s ` c ) ) <_ T )' % (A0, SX_, YR))
    # separation
    Aab = '( ( %s /\\ c e. %s ) /\\ d e. %s )' % (A0, SX_, SX_)
    ea2 = elem('c', Aab, lift(w, w.s([], 'simpr', '( %s -> c e. %s )' % (Aa, SX_)), Aab))
    eb2 = elem('d', Aab, w.s([], 'simpr', '( %s -> d e. %s )' % (Aab, SX_)))
    ka = dst(w, Aab, [ea2], 'simprd', '( K ` c ) = x'); kb = dst(w, Aab, [eb2], 'simprd', '( K ` d ) = x')
    kab = eqt(w, Aab, ka, eqc(w, Aab, kb))
    PHab = '( ( a =/= b /\\ ( K ` a ) = ( K ` b ) ) -> 1 <_ ( abs ` ( ( Y ` a ) - ( Y ` b ) ) ) )'
    c1_, n1 = w.wcongr('A. b e. S %s' % PHab, {'a': 'c'}, 'a = c', {'a': w.s([], 'id', '( a = c -> a = c )')})
    sp1 = w.s([c1_, lift(w, sep, Aab), dst(w, Aab, [ea2], 'simpld', 'c e. S')], 'rspcdva', '( %s -> %s )' % (Aab, n1))
    PHcb = PHab.replace('a =/= b', 'c =/= b').replace('( K ` a )', '( K ` c )').replace('( Y ` a )', '( Y ` c )')
    assert n1 == 'A. b e. S %s' % PHcb, n1
    c2_, n2 = w.wcongr(PHcb, {'b': 'd'}, 'b = d', {'b': w.s([], 'id', '( b = d -> b = d )')})
    s3 = w.s([c2_, sp1, dst(w, Aab, [eb2], 'simpld', 'd e. S')], 'rspcdva', '( %s -> %s )' % (Aab, n2))
    s4 = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ c =/= d ) -> c =/= d )' % Aab), w.s([kab], 'adantr', '( ( %s /\\ c =/= d ) -> ( K ` c ) = ( K ` d ) )' % Aab)], 'jca',
                  '( ( %s /\\ c =/= d ) -> ( c =/= d /\\ ( K ` c ) = ( K ` d ) ) )' % Aab), w.s([s3], 'adantr', '( ( %s /\\ c =/= d ) -> %s )' % (Aab, n2))],
             'mpd', '( ( %s /\\ c =/= d ) -> 1 <_ ( abs ` ( ( Y ` c ) - ( Y ` d ) ) ) )' % Aab)
    fvb = ap(w, Aab, 'fvres', [w.s([], 'simpr', '( %s -> d e. %s )' % (Aab, SX_))], '( %s ` d ) = ( Y ` d )' % YR)
    dfe = dst(w, Aab, [dst(w, Aab, [lift(w, fva, Aab), fvb], 'oveq12d', '( ( %s ` c ) - ( %s ` d ) ) = ( ( Y ` c ) - ( Y ` d ) )' % (YR, YR))], 'fveq2d',
              '( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) = ( abs ` ( ( Y ` c ) - ( Y ` d ) ) )' % (YR, YR))
    s5 = w.s([s4, w.s([dfe], 'adantr', '( ( %s /\\ c =/= d ) -> ( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) = ( abs ` ( ( Y ` c ) - ( Y ` d ) ) ) )' % (Aab, YR, YR))], 'breqtrrd',
             '( ( %s /\\ c =/= d ) -> 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) )' % (Aab, YR, YR))
    sep1 = w.s([w.s([w.s([s5], 'ex', '( %s -> ( c =/= d -> 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) ) )' % (Aab, YR, YR))], 'ralrimiva',
                    '( ( %s /\\ c e. %s ) -> A. d e. %s ( c =/= d -> 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) ) )' % (A0, SX_, SX_, YR, YR))], 'ralrimiva',
               '( %s -> A. c e. %s A. d e. %s ( c =/= d -> 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) ) )' % (A0, SX_, SX_, YR, YR))
    SEPR = 'A. c e. %s A. d e. %s ( c =/= d -> 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` d ) ) ) )' % (SX_, SX_, YR, YR)
    pc = ap(w, A0, 'mvpcs', [w.s([hf, w.s([pfin, yr, tr], '3jca', '( %s -> ( %s e. Fin /\\ %s : %s --> RR /\\ T e. RR ) )' % (A0, SX_, YR, SX_)), w.s([rgall, sep1], 'jca',
                                   '( %s -> ( A. c e. %s ( abs ` ( %s ` c ) ) <_ T /\\ %s ) )' % (A0, SX_, YR, SEPR))], '3jca', '( %s -> ( ( %s : RR --> CC /\\ ( RR _D %s ) = %s /\\ %s e. %s ) /\\ ( %s e. Fin /\\ %s : %s --> RR /\\ T e. RR ) /\\ ( A. c e. %s ( abs ` ( %s ` c ) ) <_ T /\\ %s ) ) )' % (
                                   A0, F, F, G, G, CNR, SX_, YR, SX_, SX_, YR, SEPR))],
            'sum_ i e. %s ( ( abs ` ( %s ` ( %s ` i ) ) ) ^ 2 ) <_ ( ( 2 x. %s ) + %s )' % (SX_, F, YR, ITG(T1, ABS2('( %s ` t )' % F)), ITG(T1, ABS2('( %s ` t )' % G))))
    # rewrite the three pieces
    Ai = '( %s /\\ i e. %s )' % (A0, SX_)
    im = w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, SX_))
    ei = elem('i', Ai, im)
    iS = dst(w, Ai, [ei], 'simpld', 'i e. S')
    yi = w.s([lift(w, yf, Ai), iS], 'ffvelcdmd', '( %s -> ( Y ` i ) e. RR )' % Ai)
    fvi = ap(w, Ai, 'fvres', [im], '( %s ` i ) = ( Y ` i )' % YR)
    Ai2 = '( %s /\\ m e. %s )' % (Ai, FZM)
    vi = vals(w, Ai2, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (Ai2, FZM)), lift(w, xm, Ai2), aok)
    ci2 = Closure(w, Ai2, {'( %s ` m )' % CXU: ('CC', vi['ci']), '( %s ` m )' % LFU: ('RR', vi['li']), '( Y ` i )': ('RR', lift(w, yi, Ai2)), '_i': ('CC', a1(w, Ai2, 'ax-icn', '_i e. CC'))})
    sxi_c = w.s([lift(w, fz, Ai), ci2.mem('( ( %s ` m ) x. ( exp ` ( _i x. ( ( %s ` m ) x. ( Y ` i ) ) ) ) )' % (CXU, LFU), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Ai, sxm('( Y ` i )')))
    fv1 = fvmd(w, Ai, 'y', 'RR', sxm('y'), '( Y ` i )', yi, sxi_c)
    fv2 = sx_to_ds(w, Ai, '( Y ` i )', yi, lift(w, xm, Ai), aok)
    fpt = eqt(w, Ai, eqt(w, Ai, dst(w, Ai, [fvi], 'fveq2d', '( %s ` ( %s ` i ) ) = ( %s ` ( Y ` i ) )' % (F, YR, F)), fv1), fv2)
    lt = dst(w, Ai, [dst(w, Ai, [fpt], 'fveq2d', '( abs ` ( %s ` ( %s ` i ) ) ) = ( abs ` %s )' % (F, YR, DS('x', '( Y ` i )')))], 'oveq1d',
             '( ( abs ` ( %s ` ( %s ` i ) ) ) ^ 2 ) = %s' % (F, YR, ABS2(DS('x', '( Y ` i )'))))
    ls = dst(w, A0, [lt], 'sumeq2dv', 'sum_ i e. %s ( ( abs ` ( %s ` ( %s ` i ) ) ) ^ 2 ) = sum_ i e. %s %s' % (SX_, F, YR, SX_, ABS2(DS('x', '( Y ` i )'))))
    subr, newr = w.congr(ABS2(DS('x', '( Y ` i )')), {'i': 'r'}, 'i = r', {'i': w.s([], 'id', '( i = r -> i = r )')})
    cbr = w.s([subr], 'cbvsumv', 'sum_ i e. %s %s = sum_ r e. %s %s' % (SX_, ABS2(DS('x', '( Y ` i )')), SX_, newr))
    LS = eqt(w, A0, ls, w.s([cbr], 'a1i', '( %s -> sum_ i e. %s %s = sum_ r e. %s %s )' % (A0, SX_, ABS2(DS('x', '( Y ` i )')), SX_, newr)))
    def itg_rw(fn_, form, deriv):
        Atk = '( %s /\\ t e. %s )' % (A0, T1)
        tk = ap(w, Atk, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Atk, T1))], 't e. RR')
        Atk2 = '( %s /\\ m e. %s )' % (Atk, FZM)
        vk = vals(w, Atk2, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (Atk2, FZM)), lift(w, xm, Atk2), aok)
        ck2 = Closure(w, Atk2, {'( %s ` m )' % CXU: ('CC', vk['ci']), '( %s ` m )' % LFU: ('RR', vk['li']), 't': ('RR', lift(w, tk, Atk2)), '_i': ('CC', a1(w, Atk2, 'ax-icn', '_i e. CC'))})
        term = form('t')[len('sum_ m e. %s ' % FZM):]
        scl = w.s([lift(w, fz, Atk), ck2.mem(term, 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Atk, form('t')))
        f1_ = fvmd(w, Atk, 'y', 'RR', form('y'), 't', tk, scl)
        f2_ = sx_to_ds(w, Atk, 't', tk, lift(w, xm, Atk), aok, deriv=deriv)
        tgt = DS('x', 't', A=ADM) if deriv else DS('x', 't')
        e_ = dst(w, Atk, [dst(w, Atk, [eqt(w, Atk, f1_, f2_)], 'fveq2d', '( abs ` ( %s ` t ) ) = ( abs ` %s )' % (fn_, tgt))], 'oveq1d', '( ( abs ` ( %s ` t ) ) ^ 2 ) = %s' % (fn_, ABS2(tgt)))
        return dst(w, A0, [e_], 'itgeq2dv', '%s = %s' % (ITG(T1, ABS2('( %s ` t )' % fn_)), ITG(T1, ABS2(tgt))))
    IF_ = itg_rw(F, sxm, False)
    IG_ = itg_rw(G, sxdm, True)
    rhs = dst(w, A0, [dst(w, A0, [IF_], 'oveq2d', '( 2 x. %s ) = ( 2 x. %s )' % (ITG(T1, ABS2('( %s ` t )' % F)), ITG(T1, ABS2(DS('x', 't')))))], 'id', 'x') if False else \
        dst(w, A0, [dst(w, A0, [IF_], 'oveq2d', '( 2 x. %s ) = ( 2 x. %s )' % (ITG(T1, ABS2('( %s ` t )' % F)), ITG(T1, ABS2(DS('x', 't'))))), IG_], 'oveq12d',
            '( ( 2 x. %s ) + %s ) = ( ( 2 x. %s ) + %s )' % (ITG(T1, ABS2('( %s ` t )' % F)), ITG(T1, ABS2('( %s ` t )' % G)), ITG(T1, ABS2(DS('x', 't'))), ITG(T1, ABS2(DS('x', 't', A=ADM)))))
    le_ = w.s([LS, pc, rhs], '3brtr3d', '( %s -> sum_ r e. %s %s <_ ( ( 2 x. %s ) + %s ) )' % (A0, SX_, newr, ITG(T1, ABS2(DS('x', 't'))), ITG(T1, ABS2(DS('x', 't', A=ADM)))))
    # memberships
    from z4blib import fmap
    fcn = w.s([dv], 'simp2d', '( %s -> %s e. %s )' % (A0, F, CNR)); gcn = w.s([dv], 'simp3d', '( %s -> %s e. %s )' % (A0, G, CNR))
    fm = fmap(w, A0, fcn, F, 't'); gm = fmap(w, A0, gcn, G, 't')
    ff_ = ap(w, A0, 'cncff', [fcn], '%s : RR --> CC' % F); gf_ = ap(w, A0, 'cncff', [gcn], '%s : RR --> CC' % G)
    Atr = '( %s /\\ t e. RR )' % A0
    ttr = w.s([], 'simpr', '( %s -> t e. RR )' % Atr)
    ctr = Closure(w, Atr, {'( %s ` t )' % F: ('CC', w.s([lift(w, ff_, Atr), ttr], 'ffvelcdmd', '( %s -> ( %s ` t ) e. CC )' % (Atr, F))),
                           '( %s ` t )' % G: ('CC', w.s([lift(w, gf_, Atr), ttr], 'ffvelcdmd', '( %s -> ( %s ` t ) e. CC )' % (Atr, G)))})
    cnk = CN(w, A0, 't', 'RR', a1(w, A0, 'ax-resscn', 'RR C_ CC'), Closure(w, A0, {}), ctr, known={'( %s ` t )' % F: fm, '( %s ` t )' % G: gm})
    c0 = Closure(w, A0, {'T': ('RR', tr)})
    def real_itg(fn_, eqst, tgt):
        E_ = ABS2('( %s ` t )' % fn_)
        ib = w.s([c0.mem('-u ( T + 1 )', 'RR'), c0.mem('( T + 1 )', 'RR'), cnk(E_)], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, T1, E_))
        Atk = '( %s /\\ t e. %s )' % (A0, T1)
        tk = ap(w, Atk, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Atk, T1))], 't e. RR')
        fk = w.s([lift(w, ff_ if fn_ == F else gf_, Atk), tk], 'ffvelcdmd', '( %s -> ( %s ` t ) e. CC )' % (Atk, fn_))
        er = w.s([Closure(w, Atk, {'( %s ` t )' % fn_: ('CC', fk)}).mem(E_, 'RR'), ib], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITG(T1, E_)))
        return w.s([eqst, er], 'eqeltrrd', '( %s -> %s e. RR )' % (A0, tgt))
    r1 = real_itg(F, IF_, ITG(T1, ABS2(DS('x', 't'))))
    r2 = real_itg(G, IG_, ITG(T1, ABS2(DS('x', 't', A=ADM))))
    Aii = '( %s /\\ i e. %s )' % (A0, SX_)
    iy = w.s([lift(w, yr, Aii), w.s([], 'simpr', '( %s -> i e. %s )' % (Aii, SX_))], 'ffvelcdmd', '( %s -> ( %s ` i ) e. RR )' % (Aii, YR))
    fyi = w.s([lift(w, ff_, Aii), iy], 'ffvelcdmd', '( %s -> ( %s ` ( %s ` i ) ) e. CC )' % (Aii, F, YR))
    lr_ = w.s([pfin, Closure(w, Aii, {'( %s ` ( %s ` i ) )' % (F, YR): ('CC', fyi)}).mem('( ( abs ` ( %s ` ( %s ` i ) ) ) ^ 2 )' % (F, YR), 'RR')], 'fsumrecl',
              '( %s -> sum_ i e. %s ( ( abs ` ( %s ` ( %s ` i ) ) ) ^ 2 ) e. RR )' % (A0, SX_, F, YR))
    r0 = w.s([LS, lr_], 'eqeltrrd' if False else 'id', 'x') if False else w.s([eqc(w, A0, LS), lr_], 'eqeltrrd', '( %s -> sum_ r e. %s %s e. RR )' % (A0, SX_, newr)) if False else \
        w.s([LS, lr_], 'eqeltrrd' if False else 'eqeltrd' if False else 'id', 'x') if False else None
    r0 = w.s([w.s([LS], 'eqcomd', '( %s -> sum_ r e. %s %s = sum_ i e. %s ( ( abs ` ( %s ` ( %s ` i ) ) ) ^ 2 ) )' % (A0, SX_, newr, SX_, F, YR)), lr_], 'eqeltrd',
             '( %s -> sum_ r e. %s %s e. RR )' % (A0, SX_, newr))
    J(w, A0, w.s([r0, r1, r2], '3jca', '( %s -> ( sum_ r e. %s %s e. RR /\\ %s e. RR /\\ %s e. RR ) )' % (A0, SX_, newr, ITG(T1, ABS2(DS('x', 't'))), ITG(T1, ABS2(DS('x', 't', A=ADM))))), le_)
    qedlast(w)
    go(w)


def mvdfam():
    w = W('mvdfam', 'Grouped discrete mean value theorem (LargeValues mean_value_chars_discrete_family), indexed form: for a family ( S , K , Y ) of points of [ -u T , T ], 1-spaced among equal characters, sum_ r | sum_ n a_n K_r ( n ) n ^ ( - i Y_r ) | ^ 2 <_ 200 ( M + N ( T + 1 ) ) sum ( 1 + log ^ 2 n ) | a_n | ^ 2.')
    A0 = HFX
    P_ = parts(w, A0)
    nn, tr, t2, mn0, aok = P_['N e. NN'], P_['T e. RR'], P_['2 <_ T'], P_['M e. NN0'], P_[AOK]
    sfin, kf, yf = P_['S e. Fin'], P_['K : S --> %s' % Dd], P_['Y : S --> RR']
    eG, eZ, eD, eL = eqids(w)
    dfin = w.s([nn, w.s([eG, eD], 'dchrfi', '( N e. NN -> %s e. Fin )' % Dd)], 'syl', '( %s -> %s e. Fin )' % (A0, Dd))
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZM))
    fDS = lambda x_, t_: ABS2(DS(x_, t_))
    # DS ( x , tau ) is complex
    def dscl(ante, xst, taust, x_, tau):
        An_ = '( %s /\\ n e. %s )' % (ante, FZM)
        nm = w.s([], 'simpr', '( %s -> n e. %s )' % (An_, FZM))
        nN = ap(w, An_, 'elfznn', [nm], 'n e. NN')
        av = aval(w, An_, 'n', lift(w, aok, An_), nm)
        cv = w.s([eG, eZ, eD, eL, lift(w, xst, An_), w.s([nN], 'nnzd', '( %s -> n e. ZZ )' % An_)], 'dchrzrhcl', '( %s -> %s e. CC )' % (An_, CHV(x_, 'n')))
        c_ = Closure(w, An_, {'( A ` n )': ('CC', av), CHV(x_, 'n'): ('CC', cv), 'n': ('NN', nN), tau: ('RR', lift(w, taust, An_)), '_i': ('CC', a1(w, An_, 'ax-icn', '_i e. CC'))})
        return w.s([lift(w, fz, ante), c_.mem('( ( ( A ` n ) x. %s ) x. %s )' % (CHV(x_, 'n'), NEX('n', tau)), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (ante, DS(x_, tau)))
    # regroup
    Ar = '( %s /\\ r e. S )' % A0
    rm = w.s([], 'simpr', '( %s -> r e. S )' % Ar)
    kr = w.s([lift(w, kf, Ar), rm], 'ffvelcdmd', '( %s -> ( K ` r ) e. %s )' % (Ar, Dd))
    yr_ = w.s([lift(w, yf, Ar), rm], 'ffvelcdmd', '( %s -> ( Y ` r ) e. RR )' % Ar)
    FR = fDS('( K ` r )', '( Y ` r )')
    fx = fDS('x', '( Y ` r )')
    sub, _ = w.congr(fx, {'x': '( K ` r )'}, 'x = ( K ` r )', {'x': w.s([], 'id', '( x = ( K ` r ) -> x = ( K ` r ) )')})
    frc = Closure(w, Ar, {DS('( K ` r )', '( Y ` r )'): ('CC', dscl(Ar, kr, yr_, '( K ` r )', '( Y ` r )'))}).mem(FR, 'CC')
    si = w.s([sub, lift(w, dfin, Ar), kr, frc], 'sumite', '( %s -> sum_ x e. %s if ( x = ( K ` r ) , %s , 0 ) = %s )' % (Ar, Dd, fx, FR))
    IFx = 'if ( x = ( K ` r ) , %s , 0 )' % fx
    g1 = dst(w, A0, [eqc(w, Ar, si)], 'sumeq2dv', 'sum_ r e. S %s = sum_ r e. S sum_ x e. %s %s' % (FR, Dd, IFx))
    Arx = '( %s /\\ ( r e. S /\\ x e. %s ) )' % (A0, Dd)
    rm2 = w.s([], 'simprl', '( %s -> r e. S )' % Arx); xm2 = w.s([], 'simprr', '( %s -> x e. %s )' % (Arx, Dd))
    yr2 = w.s([lift(w, yf, Arx), rm2], 'ffvelcdmd', '( %s -> ( Y ` r ) e. RR )' % Arx)
    ifc = w.s([Closure(w, Arx, {DS('x', '( Y ` r )'): ('CC', dscl(Arx, xm2, yr2, 'x', '( Y ` r )'))}).mem(fx, 'CC'), w.s([], '0cnd', '( %s -> 0 e. CC )' % Arx)], 'ifcld',
              '( %s -> %s e. CC )' % (Arx, IFx))
    g2 = w.s([sfin, dfin, ifc], 'fsumcom', '( %s -> sum_ r e. S sum_ x e. %s %s = sum_ x e. %s sum_ r e. S %s )' % (A0, Dd, IFx, Dd, IFx))
    # per x: sum over S of the if = sum over the fiber
    Ax = '( %s /\\ x e. %s )' % (A0, Dd)
    xm = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, Dd))
    SX_ = SXF
    Axr = '( %s /\\ r e. S )' % Ax
    sub2, _ = w.wcongr('( K ` q ) = x', {'q': 'r'}, 'q = r', {'q': w.s([], 'id', '( q = r -> q = r )')})
    er = w.s([sub2], 'elrab', '( r e. %s <-> ( r e. S /\\ ( K ` r ) = x ) )' % SX_)
    b1 = w.s([w.s([w.s([], 'simpr', '( %s -> r e. S )' % Axr), w.inst('ibar')], 'syl', '( %s -> ( ( K ` r ) = x <-> ( r e. S /\\ ( K ` r ) = x ) ) )' % Axr),
              w.s([er], 'a1i', '( %s -> ( r e. %s <-> ( r e. S /\\ ( K ` r ) = x ) ) )' % (Axr, SX_))], 'bitr4d', '( %s -> ( ( K ` r ) = x <-> r e. %s ) )' % (Axr, SX_))
    b2 = w.s([w.s([], 'eqcom', '( x = ( K ` r ) <-> ( K ` r ) = x )'), b1], 'syl5bb' if False else 'id', 'x') if False else \
        w.s([w.s([w.s([], 'eqcom', '( x = ( K ` r ) <-> ( K ` r ) = x )')], 'a1i', '( %s -> ( x = ( K ` r ) <-> ( K ` r ) = x ) )' % Axr), b1], 'bitrd', '( %s -> ( x = ( K ` r ) <-> r e. %s ) )' % (Axr, SX_))
    ib = w.s([b2], 'ifbid', '( %s -> %s = if ( r e. %s , %s , 0 ) )' % (Axr, IFx, SX_, fx))
    Axq = '( %s /\\ r e. %s )' % (Ax, SX_)
    rqS = w.s([a1(w, Axq, 'ssrab2', '%s C_ S' % SX_), w.s([], 'simpr', '( %s -> r e. %s )' % (Axq, SX_))], 'sseldd', '( %s -> r e. S )' % Axq)
    yq = w.s([lift(w, yf, Axq), rqS], 'ffvelcdmd', '( %s -> ( Y ` r ) e. RR )' % Axq)
    fq = Closure(w, Axq, {DS('x', '( Y ` r )'): ('CC', dscl(Axq, lift(w, xm, Axq), yq, 'x', '( Y ` r )'))}).mem(fx, 'CC')
    ssum = w.s([w.s([a1(w, Ax, 'ssrab2', '%s C_ S' % SX_), w.s([fq], 'ralrimiva', '( %s -> A. r e. %s %s e. CC )' % (Ax, SX_, fx))], 'jca', '( %s -> ( %s C_ S /\\ A. r e. %s %s e. CC ) )' % (Ax, SX_, SX_, fx)),
                w.s([lift(w, sfin, Ax)], 'olcd', '( %s -> ( S C_ ( ZZ>= ` 1 ) \\/ S e. Fin ) )' % Ax), w.inst('sumss2')], 'syl2anc',
               '( %s -> sum_ r e. %s %s = sum_ r e. S if ( r e. %s , %s , 0 ) )' % (Ax, SX_, fx, SX_, fx))
    fib = eqt(w, Ax, dst(w, Ax, [ib], 'sumeq2dv', 'sum_ r e. S %s = sum_ r e. S if ( r e. %s , %s , 0 ) )' % (IFx, SX_, fx)) if False else
              dst(w, Ax, [ib], 'sumeq2dv', 'sum_ r e. S %s = sum_ r e. S if ( r e. %s , %s , 0 )' % (IFx, SX_, fx)), eqc(w, Ax, ssum))   # sum_S IF = FIBL
    ALL = eqt(w, A0, eqt(w, A0, g1, g2), dst(w, A0, [fib], 'sumeq2dv', 'sum_ x e. %s sum_ r e. S %s = sum_ x e. %s %s' % (Dd, IFx, Dd, FIBL)))
    # per x bound (mvdfam1)
    d1 = ap(w, Ax, 'mvdfam1', [J(w, Ax, lift(w, w.s([], 'id', '( %s -> %s )' % (A0, A0)), Ax), xm)], split_imp(STATEMENTS['mvdfam1'])[1])
    d1r = dst(w, Ax, [d1], 'simpld', '( %s e. RR /\\ %s e. RR /\\ %s e. RR )' % (FIBL, FI1, FI2))
    d1l = dst(w, Ax, [d1], 'simprd', '%s <_ ( ( 2 x. %s ) + %s )' % (FIBL, FI1, FI2))
    f0r = w.s([d1r], 'simp1d', '( %s -> %s e. RR )' % (Ax, FIBL)); f1r = w.s([d1r], 'simp2d', '( %s -> %s e. RR )' % (Ax, FI1)); f2r = w.s([d1r], 'simp3d', '( %s -> %s e. RR )' % (Ax, FI2))
    cx = Closure(w, Ax, {FI1: ('RR', f1r), FI2: ('RR', f2r)})
    fl = w.s([dfin, f0r, cx.mem('( ( 2 x. %s ) + %s )' % (FI1, FI2), 'RR'), d1l], 'fsumle', '( %s -> sum_ x e. %s %s <_ sum_ x e. %s ( ( 2 x. %s ) + %s ) )' % (A0, Dd, FIBL, Dd, FI1, FI2))
    fa = w.s([dfin, cx.mem('( 2 x. %s )' % FI1, 'CC'), cx.mem(FI2, 'CC')], 'fsumadd', '( %s -> sum_ x e. %s ( ( 2 x. %s ) + %s ) = ( sum_ x e. %s ( 2 x. %s ) + sum_ x e. %s %s ) )' % (
        A0, Dd, FI1, FI2, Dd, FI1, Dd, FI2))
    fm2 = w.s([dfin, w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), cx.mem(FI1, 'CC')], 'fsummulc2', '( %s -> ( 2 x. sum_ x e. %s %s ) = sum_ x e. %s ( 2 x. %s ) )' % (A0, Dd, FI1, Dd, FI1))
    # mvmvc at T + 1 for A and for ADM
    cT = Closure(w, A0, {'T': ('RR', tr), 'N': ('NN', nn)})
    t0 = linarith(w, A0, [t2], '0 < ( T + 1 )', closure=cT)
    t1p = w.s([cT.mem('( T + 1 )', 'RR'), t0], 'elrpd', '( %s -> ( T + 1 ) e. RR+ )' % A0)
    hm1 = J(w, A0, J(w, A0, nn, t1p), J(w, A0, mn0, aok))
    mv1 = ap(w, A0, 'mvmvc1', [hm1], STATEMENTS['mvmvc1'].split(' -> ', 1)[1][:-2].replace('( -u T (,) T )', T1).replace('( _pi / ( 2 x. T ) )', '( _pi / ( 2 x. ( T + 1 ) ) )').replace('( T ^ 2 )', '( ( T + 1 ) ^ 2 )'))
    SUMI1 = 'sum_ x e. %s %s' % (Dd, FI1)
    mvA = ap(w, A0, 'mvmvc', [hm1], '%s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s )' % (SUMI1, SA2))
    s1r = dst(w, A0, [mv1], 'simpld', '%s e. RR' % SUMI1)
    # ADM coefficients
    Ak = '( %s /\\ c e. %s )' % (A0, FZM)
    km = w.s([], 'simpr', '( %s -> c e. %s )' % (Ak, FZM))
    kN = ap(w, Ak, 'elfznn', [km], 'c e. NN')
    ak_ = aval(w, Ak, 'c', lift(w, aok, Ak), km)
    ck = Closure(w, Ak, {'( A ` c )': ('CC', ak_), 'c': ('NN', kN), '_i': ('CC', a1(w, Ak, 'ax-icn', '_i e. CC'))})
    adv = fvmd(w, Ak, 'u', 'NN', '( ( A ` u ) x. ( _i x. -u ( log ` u ) ) )', 'c', kN, ck.mem('( ( A ` c ) x. ( _i x. -u ( log ` c ) ) )', 'CC'))
    adc = w.s([adv, ck.mem('( ( A ` c ) x. ( _i x. -u ( log ` c ) ) )', 'CC')], 'eqeltrd', '( %s -> ( %s ` c ) e. CC )' % (Ak, ADM))
    aok2 = w.s([adc], 'ralrimiva', '( %s -> A. c e. %s ( %s ` c ) e. CC )' % (A0, FZM, ADM))
    hm2 = J(w, A0, J(w, A0, nn, t1p), J(w, A0, mn0, aok2))
    SA2D = 'sum_ n e. %s ( ( abs ` ( %s ` n ) ) ^ 2 )' % (FZM, ADM)
    SUMI2 = 'sum_ x e. %s %s' % (Dd, FI2)
    mv1d = ap(w, A0, 'mvmvc1', [hm2], STATEMENTS['mvmvc1'].split(' -> ', 1)[1][:-2].replace('( -u T (,) T )', T1).replace('( _pi / ( 2 x. T ) )', '( _pi / ( 2 x. ( T + 1 ) ) )').replace('( T ^ 2 )', '( ( T + 1 ) ^ 2 )').replace('( A ` ', '( %s ` ' % ADM))
    mvD = ap(w, A0, 'mvmvc', [hm2], '%s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s )' % (SUMI2, SA2D))
    s2r = dst(w, A0, [mv1d], 'simpld', '%s e. RR' % SUMI2)
    # | ADM n | ^ 2 = log ^ 2 n | A n | ^ 2
    An = '( %s /\\ n e. %s )' % (A0, FZM)
    nm = w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM)); nN = ap(w, An, 'elfznn', [nm], 'n e. NN')
    an_ = aval(w, An, 'n', lift(w, aok, An), nm)
    cn_ = Closure(w, An, {'( A ` n )': ('CC', an_), 'n': ('NN', nN), '_i': ('CC', a1(w, An, 'ax-icn', '_i e. CC'))})
    advn = fvmd(w, An, 'u', 'NN', '( ( A ` u ) x. ( _i x. -u ( log ` u ) ) )', 'n', nN, cn_.mem('( ( A ` n ) x. ( _i x. -u ( log ` n ) ) )', 'CC'))
    Vn = '( ( A ` n ) x. ( _i x. -u ( log ` n ) ) )'
    ab1 = w.s([cn_.mem('( A ` n )', 'CC'), cn_.mem('( _i x. -u ( log ` n ) )', 'CC')], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` ( A ` n ) ) x. ( abs ` ( _i x. -u ( log ` n ) ) ) ) )' % (An, Vn))
    ab2 = w.s([a1(w, An, 'ax-icn', '_i e. CC'), cn_.mem('-u ( log ` n )', 'CC')], 'absmuld', '( %s -> ( abs ` ( _i x. -u ( log ` n ) ) ) = ( ( abs ` _i ) x. ( abs ` -u ( log ` n ) ) ) )' % An)
    ab3 = eqt(w, An, ab2, dst(w, An, [a1(w, An, 'absi', '( abs ` _i ) = 1'), ap(w, An, 'absneg', [cn_.mem('( log ` n )', 'CC')], '( abs ` -u ( log ` n ) ) = ( abs ` ( log ` n ) )')], 'oveq12d',
                                  '( ( abs ` _i ) x. ( abs ` -u ( log ` n ) ) ) = ( 1 x. ( abs ` ( log ` n ) ) )'))
    AL = '( abs ` ( log ` n ) )'
    ALN = eqt(w, An, eqt(w, An, dst(w, An, [advn], 'fveq2d', '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (ADM, Vn)), ab1), dst(w, An, [ab3], 'oveq2d',
                          '( ( abs ` ( A ` n ) ) x. ( abs ` ( _i x. -u ( log ` n ) ) ) ) = ( ( abs ` ( A ` n ) ) x. ( 1 x. %s ) )' % AL))
    ra = Closure(w, An, {'( abs ` ( A ` n ) )': ('RR', cn_.mem('( abs ` ( A ` n ) )', 'RR')), AL: ('RR', cn_.mem(AL, 'RR')), '( log ` n )': ('RR', cn_.mem('( log ` n )', 'RR'))})
    sqA = dst(w, An, [ALN], 'oveq1d', '( ( abs ` ( %s ` n ) ) ^ 2 ) = ( ( ( abs ` ( A ` n ) ) x. ( 1 x. %s ) ) ^ 2 )' % (ADM, AL))
    sqB = ringeqp(w, An, '( ( ( abs ` ( A ` n ) ) x. ( 1 x. %s ) ) ^ 2 )' % AL, '( ( %s ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )' % AL, ra)
    sqC = dst(w, An, [ap(w, An, 'absresq', [cn_.mem('( log ` n )', 'RR')], '( %s ^ 2 ) = ( ( log ` n ) ^ 2 )' % AL)], 'oveq1d',
              '( ( %s ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) ) = ( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )' % AL)
    ADn = eqt(w, An, eqt(w, An, sqA, sqB), sqC)
    L2S = 'sum_ n e. %s ( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )' % FZM
    sad = dst(w, A0, [ADn], 'sumeq2dv', '%s = %s' % (SA2D, L2S))
    # sum ( 1 + log ^ 2 ) | a | ^ 2 = SA2 + L2S
    cn_.leaf('( ( abs ` ( A ` n ) ) ^ 2 )', 'RR', cn_.mem('( ( abs ` ( A ` n ) ) ^ 2 )', 'RR')); cn_.leaf('( ( log ` n ) ^ 2 )', 'RR', cn_.mem('( ( log ` n ) ^ 2 )', 'RR'))
    tsp = ringeq(w, An, '( ( 1 + ( ( log ` n ) ^ 2 ) ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )', '( ( ( abs ` ( A ` n ) ) ^ 2 ) + ( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) ) )', cn_)
    fs = eqt(w, A0, dst(w, A0, [tsp], 'sumeq2dv', '%s = sum_ n e. %s ( ( ( abs ` ( A ` n ) ) ^ 2 ) + ( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) ) )' % (SLA2, FZM)),
             w.s([fz, cn_.mem('( ( abs ` ( A ` n ) ) ^ 2 )', 'CC'), cn_.mem('( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )', 'CC')], 'fsumadd',
                 '( %s -> sum_ n e. %s ( ( ( abs ` ( A ` n ) ) ^ 2 ) + ( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) ) ) = ( %s + %s ) )' % (A0, FZM, SA2, L2S)))
    # assembly
    X = '( ; ; 1 0 0 x. ( M + ( N x. ( T + 1 ) ) ) )'
    cl = Closure(w, A0, {'T': ('RR', tr), 'N': ('NN', nn), 'M': ('NN0', mn0)})
    x0 = w.s([a1(w, A0, '1nn0' if False else '0re', '0 e. RR') if False else w.s([], 'id', 'x')], 'id', 'x') if False else None
    xg = linarith(w, A0, [t0, ltle(w, A0, cl, cl.gt0('N')) if False else w.s([cl.mem('N', 'RR'), cl.mem('( T + 1 )', 'RR'), ltle(w, A0, cl, cl.gt0('N')), ltle(w, A0, cl, cT.gt0('( T + 1 )') if False else t0)], 'mulge0d', '( %s -> 0 <_ ( N x. ( T + 1 ) ) )' % A0),
                               cl.ge0('M')], '0 <_ %s' % X, closure=cl)
    SL2r = w.s([fz, cn_.mem('( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )', 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (A0, L2S))
    SL20 = w.s([fz, cn_.mem('( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) )', 'RR'), w.s([cn_.mem('( ( log ` n ) ^ 2 )', 'RR'), cn_.mem('( ( abs ` ( A ` n ) ) ^ 2 )', 'RR'),
                                                                                                        w.s([cn_.mem('( log ` n )', 'RR')], 'sqge0d', '( %s -> 0 <_ ( ( log ` n ) ^ 2 ) )' % An),
                                                                                                        w.s([cn_.mem('( abs ` ( A ` n ) )', 'RR')], 'sqge0d', '( %s -> 0 <_ ( ( abs ` ( A ` n ) ) ^ 2 ) )' % An)], 'mulge0d',
                                                                                                       '( %s -> 0 <_ ( ( ( log ` n ) ^ 2 ) x. ( ( abs ` ( A ` n ) ) ^ 2 ) ) )' % An)], 'fsumge0', '( %s -> 0 <_ %s )' % (A0, L2S))
    SA2r = w.s([fz, cn_.mem('( ( abs ` ( A ` n ) ) ^ 2 )', 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SA2))
    xl = w.s([cl.mem(X, 'RR'), SL2r, xg, SL20], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (A0, X, L2S))
    SFR = 'sum_ r e. S %s' % FR
    SFIB = 'sum_ x e. %s %s' % (Dd, FIBL)
    for t_, st_ in [(SFIB, w.s([dfin, f0r], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SFIB))), (SUMI1, s1r), (SUMI2, s2r), (SA2, SA2r), (L2S, SL2r)]:
        cl.leaf(t_, 'RR', st_)
    cl.leaf(SFR, 'RR', w.s([ALL, cl.mem(SFIB, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, SFR)))
    SUMX = 'sum_ x e. %s ( ( 2 x. %s ) + %s )' % (Dd, FI1, FI2)
    cl.leaf(SUMX, 'RR', w.s([dfin, cx.mem('( ( 2 x. %s ) + %s )' % (FI1, FI2), 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SUMX)))
    cl.leaf('sum_ x e. %s ( 2 x. %s )' % (Dd, FI1), 'RR', w.s([dfin, cx.mem('( 2 x. %s )' % FI1, 'RR')], 'fsumrecl', '( %s -> sum_ x e. %s ( 2 x. %s ) e. RR )' % (A0, Dd, FI1)))
    cl.leaf(SA2D, 'RR', w.s([sad, SL2r], 'eqeltrd', '( %s -> %s e. RR )' % (A0, SA2D)))
    cl.leaf(SLA2, 'RR', w.s([fs, cl.mem('( %s + %s )' % (SA2, L2S), 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, SLA2)))
    for t_ in ['( %s x. %s )' % (X, SA2), '( %s x. %s )' % (X, SA2D), '( %s x. %s )' % (X, L2S), '( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s )' % SLA2]:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR') if 'SLA2' not in t_ else cl.mem(t_, 'RR'))
    xd = dst(w, A0, [sad], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (X, SA2D, X, L2S))
    fin_ = dst(w, A0, [fs], 'oveq2d', '( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s ) = ( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. ( %s + %s ) )' % (SLA2, SA2, L2S))
    rq = ringeq(w, A0, '( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. ( %s + %s ) )' % (SA2, L2S), '( ( 2 x. ( %s x. %s ) ) + ( 2 x. ( %s x. %s ) ) )' % (X, SA2, X, L2S),
                Closure(w, A0, {'M': ('RR', cl.mem('M', 'RR')), 'N': ('RR', cl.mem('N', 'RR')), 'T': ('RR', tr), SA2: ('RR', SA2r), L2S: ('RR', SL2r)}))
    linarith(w, A0, [ALL, fl, fa, fm2, mvA, mvD, xd, fin_, rq, xl], '%s <_ ( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s )' % (SFR, SLA2), closure=cl, name='qed')
    go(w)


def mvlvm():
    w = W('mvlvm', 'LV1, the mean-value large-values count (LargeValues large_values_mean): #S V ^ 2 <_ 300 ( 1 + log M ) ^ 2 ( M + N T ) sum | a_n | ^ 2 for a 1-spaced family of large values.')
    B0 = LVB
    LG = 'A. a e. S V <_ ( abs ` %s )' % DS('( K ` a )', '( Y ` a )')
    A0 = '( %s /\\ %s )' % (B0, LG)
    P_ = parts(w, B0)
    nn, tr, t2, mn0, aok, m1 = P_['N e. NN'], P_['T e. RR'], P_['2 <_ T'], P_['M e. NN0'], P_[AOK], P_['1 <_ M']
    sfin, kf, yf, vr, v0 = P_['S e. Fin'], P_['K : S --> %s' % Dd], P_['Y : S --> RR'], P_['V e. RR'], P_['0 <_ V']
    rng, sep = P_[RNGF], P_[SEPF]
    lg = w.s([], 'simpr', '( %s -> %s )' % (A0, LG))
    L = lambda st_: lift(w, st_, A0)
    eG, eZ, eD, eL = eqids(w)
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (B0, FZM))
    # mvdfam (under B0)
    hfx = w.s([P_[HLV], P_[HFAM], w.s([rng, sep], 'jca', '( %s -> ( %s /\\ %s ) )' % (B0, RNGF, SEPF))], '3jca', '( %s -> %s )' % (B0, HFX))
    SR = 'sum_ r e. S %s' % ABS2(DS('( K ` r )', '( Y ` r )'))
    df = ap(w, B0, 'mvdfam', [hfx], '%s <_ ( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s )' % (SR, SLA2))
    # DS ( K r , Y r ) is complex (under B0)
    Br = '( %s /\\ r e. S )' % B0
    rm = w.s([], 'simpr', '( %s -> r e. S )' % Br)
    kr = w.s([lift(w, kf, Br), rm], 'ffvelcdmd', '( %s -> ( K ` r ) e. %s )' % (Br, Dd))
    yr_ = w.s([lift(w, yf, Br), rm], 'ffvelcdmd', '( %s -> ( Y ` r ) e. RR )' % Br)
    Brn = '( %s /\\ n e. %s )' % (Br, FZM)
    nm = w.s([], 'simpr', '( %s -> n e. %s )' % (Brn, FZM)); nN = ap(w, Brn, 'elfznn', [nm], 'n e. NN')
    cv = w.s([eG, eZ, eD, eL, lift(w, kr, Brn), w.s([nN], 'nnzd', '( %s -> n e. ZZ )' % Brn)], 'dchrzrhcl', '( %s -> %s e. CC )' % (Brn, CHV('( K ` r )', 'n')))
    cr = Closure(w, Brn, {'( A ` n )': ('CC', aval(w, Brn, 'n', lift(w, aok, Brn), nm)), CHV('( K ` r )', 'n'): ('CC', cv), 'n': ('NN', nN), '( Y ` r )': ('RR', lift(w, yr_, Brn)),
                          '_i': ('CC', a1(w, Brn, 'ax-icn', '_i e. CC'))})
    DSr = DS('( K ` r )', '( Y ` r )')
    dsc = w.s([lift(w, fz, Br), cr.mem('( ( ( A ` n ) x. %s ) x. %s )' % (CHV('( K ` r )', 'n'), NEX('n', '( Y ` r )')), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Br, DSr))
    AD_ = '( abs ` %s )' % DSr
    adr = w.s([dsc], 'abscld', '( %s -> %s e. RR )' % (Br, AD_))
    # the count (under A0)
    Ar = '( %s /\\ r e. S )' % A0
    rmA = w.s([], 'simpr', '( %s -> r e. S )' % Ar)
    sub, _ = w.wcongr('V <_ ( abs ` %s )' % DS('( K ` a )', '( Y ` a )'), {'a': 'r'}, 'a = r', {'a': w.s([], 'id', '( a = r -> a = r )')})
    vl = w.s([sub, lift(w, lg, Ar), rmA], 'rspcdva', '( %s -> V <_ %s )' % (Ar, AD_))
    adrA = w.s([adr], 'adantlr', '( %s -> %s e. RR )' % (Ar, AD_))
    vrA = lift(w, L(vr), Ar); v0A = lift(w, L(v0), Ar)
    sq = w.s([J(w, Ar, vrA, v0A), J(w, Ar, adrA, vl), w.inst('le2sq2')], 'syl2anc', '( %s -> ( V ^ 2 ) <_ ( %s ^ 2 ) )' % (Ar, AD_))
    fl = w.s([L(sfin), w.s([vrA], 'resqcld', '( %s -> ( V ^ 2 ) e. RR )' % Ar), w.s([adrA], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (Ar, AD_)), sq],
             'fsumle', '( %s -> sum_ r e. S ( V ^ 2 ) <_ %s )' % (A0, SR))
    fc = w.s([L(sfin), w.s([w.s([L(vr)], 'resqcld', '( %s -> ( V ^ 2 ) e. RR )' % A0)], 'recnd', '( %s -> ( V ^ 2 ) e. CC )' % A0), w.inst('fsumconst')], 'syl2anc',
             '( %s -> sum_ r e. S ( V ^ 2 ) = ( ( # ` S ) x. ( V ^ 2 ) ) )' % A0)
    cnt = w.s([fc, fl], 'eqbrtrrd', '( %s -> ( ( # ` S ) x. ( V ^ 2 ) ) <_ %s )' % (A0, SR))
    # weights (under B0)
    Bn = '( %s /\\ n e. %s )' % (B0, FZM)
    nm2 = w.s([], 'simpr', '( %s -> n e. %s )' % (Bn, FZM)); nN2 = ap(w, Bn, 'elfznn', [nm2], 'n e. NN')
    cn2 = Closure(w, Bn, {'n': ('NN', nN2), 'M': ('NN0', lift(w, mn0, Bn)), '( A ` n )': ('CC', aval(w, Bn, 'n', lift(w, aok, Bn), nm2))})
    mp = w.s([cn2.mem('M', 'RR'), w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Bn), w.s([], '1red', '( %s -> 1 e. RR )' % Bn), cn2.mem('M', 'RR'), a1(w, Bn, '0lt1', '0 < 1'), lift(w, m1, Bn)], 'ltletrd', '( %s -> 0 < M )' % Bn)],
             'elrpd', '( %s -> M e. RR+ )' % Bn)
    ln = w.s([ap(w, Bn, 'elfzle2', [nm2], 'n <_ M'), w.s([cn2.mem('n', 'RR+'), mp], 'logled', '( %s -> ( n <_ M <-> ( log ` n ) <_ ( log ` M ) ) )' % Bn)], 'mpbid', '( %s -> ( log ` n ) <_ ( log ` M ) )' % Bn)
    l0 = ap(w, Bn, 'logge0', [J(w, Bn, cn2.mem('n', 'RR'), ap(w, Bn, 'nnge1', [nN2], '1 <_ n'))], '0 <_ ( log ` n )')
    cn2.leaf('( log ` n )', 'RR', cn2.mem('( log ` n )', 'RR')); cn2.leaf('( log ` M )', 'RR', w.s([mp], 'relogcld', '( %s -> ( log ` M ) e. RR )' % Bn))
    ls = w.s([J(w, Bn, cn2.mem('( log ` n )', 'RR'), l0), J(w, Bn, cn2.mem('( log ` M )', 'RR'), ln), w.inst('le2sq2')], 'syl2anc', '( %s -> ( ( log ` n ) ^ 2 ) <_ ( ( log ` M ) ^ 2 ) )' % Bn)
    ex = ringeqp(w, Bn, '( ( 1 + ( log ` M ) ) ^ 2 )', '( ( 1 + ( 2 x. ( log ` M ) ) ) + ( ( log ` M ) ^ 2 ) )', Closure(w, Bn, {'( log ` M )': ('RR', cn2.mem('( log ` M )', 'RR'))}))
    for t_ in ['( ( log ` n ) ^ 2 )', '( ( log ` M ) ^ 2 )', '( ( 1 + ( log ` M ) ) ^ 2 )']:
        cn2.leaf(t_, 'RR', cn2.mem(t_, 'RR'))
    wl = linarith(w, Bn, [ls, ex, l0, ln], '( 1 + ( ( log ` n ) ^ 2 ) ) <_ ( ( 1 + ( log ` M ) ) ^ 2 )', closure=cn2)
    A2n = '( ( abs ` ( A ` n ) ) ^ 2 )'
    a2g = w.s([cn2.mem('( abs ` ( A ` n ) )', 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (Bn, A2n))
    wm = w.s([cn2.mem('( 1 + ( ( log ` n ) ^ 2 ) )', 'RR'), cn2.mem('( ( 1 + ( log ` M ) ) ^ 2 )', 'RR'), cn2.mem(A2n, 'RR'), a2g, wl],
             'lemul1ad', '( %s -> ( ( 1 + ( ( log ` n ) ^ 2 ) ) x. %s ) <_ ( ( ( 1 + ( log ` M ) ) ^ 2 ) x. %s ) )' % (Bn, A2n, A2n))
    LM2 = '( ( 1 + ( log ` M ) ) ^ 2 )'
    wfl = w.s([fz, cn2.mem('( ( 1 + ( ( log ` n ) ^ 2 ) ) x. %s )' % A2n, 'RR'), cn2.mem('( %s x. %s )' % (LM2, A2n), 'RR'), wm], 'fsumle',
              '( %s -> %s <_ sum_ n e. %s ( %s x. %s ) )' % (B0, SLA2, FZM, LM2, A2n))
    clB = Closure(w, B0, {'M': ('NN0', mn0)})
    mpp = w.s([clB.mem('M', 'RR'), w.s([w.s([], '0red', '( %s -> 0 e. RR )' % B0), w.s([], '1red', '( %s -> 1 e. RR )' % B0), clB.mem('M', 'RR'), a1(w, B0, '0lt1', '0 < 1'), m1], 'ltletrd', '( %s -> 0 < M )' % B0)],
              'elrpd', '( %s -> M e. RR+ )' % B0)
    lm2r = w.s([w.s([w.s([], '1red', '( %s -> 1 e. RR )' % B0), w.s([mpp], 'relogcld', '( %s -> ( log ` M ) e. RR )' % B0)], 'readdcld', '( %s -> ( 1 + ( log ` M ) ) e. RR )' % B0)], 'resqcld',
               '( %s -> %s e. RR )' % (B0, LM2))
    wmc = w.s([fz, w.s([lm2r], 'recnd', '( %s -> %s e. CC )' % (B0, LM2)), cn2.mem(A2n, 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ n e. %s ( %s x. %s ) )' % (B0, LM2, SA2, FZM, LM2, A2n))
    WT = w.s([wfl, eqc(w, B0, wmc)], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (B0, SLA2, LM2, SA2))
    slr = w.s([fz, cn2.mem('( ( 1 + ( ( log ` n ) ^ 2 ) ) x. %s )' % A2n, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (B0, SLA2))
    l1n = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Bn), cn2.mem('( ( log ` n ) ^ 2 )', 'RR'), a1(w, Bn, '0le1', '0 <_ 1'), w.s([cn2.mem('( log ` n )', 'RR')], 'sqge0d', '( %s -> 0 <_ ( ( log ` n ) ^ 2 ) )' % Bn)],
              'addge0d', '( %s -> 0 <_ ( 1 + ( ( log ` n ) ^ 2 ) ) )' % Bn)
    sl0 = w.s([fz, cn2.mem('( ( 1 + ( ( log ` n ) ^ 2 ) ) x. %s )' % A2n, 'RR'), w.s([cn2.mem('( 1 + ( ( log ` n ) ^ 2 ) )', 'RR'), cn2.mem(A2n, 'RR'), l1n, a2g], 'mulge0d',
                                                                                        '( %s -> 0 <_ ( ( 1 + ( ( log ` n ) ^ 2 ) ) x. %s ) )' % (Bn, A2n))], 'fsumge0', '( %s -> 0 <_ %s )' % (B0, SLA2))
    sar = w.s([fz, cn2.mem(A2n, 'RR')], 'fsumrecl', '( %s -> %s e. RR )' % (B0, SA2))
    srr = w.s([sfin, adr and w.s([adr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (Br, AD_))], 'fsumrecl', '( %s -> %s e. RR )' % (B0, SR))
    # size and the chain (under B0)
    cl = Closure(w, B0, {'N': ('NN', nn), 'T': ('RR', tr), 'M': ('NN0', mn0)})
    cl.leaf('( N x. T )', 'RR', cl.mem('( N x. T )', 'RR'))
    nt = w.s([cl.mem('N', 'RR'), a1(w, B0, '2re', '2 e. RR'), tr, ltle(w, B0, cl, cl.gt0('N')), t2], 'lemul2ad', '( %s -> ( N x. 2 ) <_ ( N x. T ) )' % B0)
    cl.leaf('( N x. ( T + 1 ) )', 'RR', cl.mem('( N x. ( T + 1 ) )', 'RR'))
    ntd = ringeq(w, B0, '( N x. ( T + 1 ) )', '( ( N x. T ) + N )', Closure(w, B0, {'N': ('RR', cl.mem('N', 'RR')), 'T': ('RR', tr)}))
    hsz = linarith(w, B0, [nt, ntd, cl.ge0('M')], '( M + ( N x. ( T + 1 ) ) ) <_ ( ( 3 / 2 ) x. ( M + ( N x. T ) ) )', closure=cl)
    X1 = '( M + ( N x. ( T + 1 ) ) )'; X2 = '( M + ( N x. T ) )'
    x2g = linarith(w, B0, [cl.ge0('M'), w.s([cl.mem('N', 'RR'), tr, ltle(w, B0, cl, cl.gt0('N')), linarith(w, B0, [t2], '0 <_ T', closure=cl)], 'mulge0d', '( %s -> 0 <_ ( N x. T ) )' % B0)],
                   '0 <_ %s' % X2, closure=cl)
    for t_, st_ in [(SLA2, slr), (SA2, sar), (LM2, lm2r), (SR, srr)]:
        cl.leaf(t_, 'RR', st_)
    cl.leaf(X1, 'RR', cl.mem(X1, 'RR')); cl.leaf(X2, 'RR', cl.mem(X2, 'RR'))
    p1 = w.s([cl.mem(X1, 'RR'), cl.mem('( ( 3 / 2 ) x. %s )' % X2, 'RR'), slr, sl0, hsz], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( ( ( 3 / 2 ) x. %s ) x. %s ) )' % (B0, X1, SLA2, X2, SLA2))
    p2 = w.s([slr, cl.mem('( %s x. %s )' % (LM2, SA2), 'RR'), cl.mem(X2, 'RR'), x2g, WT], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. ( %s x. %s ) ) )' % (B0, X2, SLA2, X2, LM2, SA2))
    rc = Closure(w, B0, {x_: ('RR', cl.mem(x_, 'RR')) for x_ in [X1, X2, SLA2, SA2, LM2]})
    e1 = ringeq(w, B0, '( ( ; ; 2 0 0 x. %s ) x. %s )' % (X1, SLA2), '( ; ; 2 0 0 x. ( %s x. %s ) )' % (X1, SLA2), rc)
    e2 = ringeq(w, B0, '( ( ( 3 / 2 ) x. %s ) x. %s )' % (X2, SLA2), '( ( 3 / 2 ) x. ( %s x. %s ) )' % (X2, SLA2), rc)
    e3 = ringeq(w, B0, '( ( ( ; ; 3 0 0 x. %s ) x. %s ) x. %s )' % (LM2, X2, SA2), '( ; ; 3 0 0 x. ( %s x. ( %s x. %s ) ) )' % (X2, LM2, SA2), rc)
    for t_ in ['( ( ; ; 2 0 0 x. %s ) x. %s )' % (X1, SLA2), '( %s x. %s )' % (X1, SLA2), '( ( ( 3 / 2 ) x. %s ) x. %s )' % (X2, SLA2), '( %s x. %s )' % (X2, SLA2),
               '( %s x. ( %s x. %s ) )' % (X2, LM2, SA2), '( ( ( ; ; 3 0 0 x. %s ) x. %s ) x. %s )' % (LM2, X2, SA2)]:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR'))
    RHS = '( ( ( ; ; 3 0 0 x. %s ) x. %s ) x. %s )' % (LM2, X2, SA2)
    bnd = linarith(w, B0, [df, e1, p1, e2, p2, e3], '%s <_ %s' % (SR, RHS), closure=cl)
    hr = w.s([w.s([sfin, w.inst('hashcl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % B0)], 'nn0red', '( %s -> ( # ` S ) e. RR )' % B0)
    cvr = w.s([hr, w.s([vr], 'resqcld', '( %s -> ( V ^ 2 ) e. RR )' % B0)], 'remulcld', '( %s -> ( ( # ` S ) x. ( V ^ 2 ) ) e. RR )' % B0)
    w.s([L(cvr), L(srr), L(cl.mem(RHS, 'RR')), cnt, L(bnd)], 'letrd', '( %s -> ( ( # ` S ) x. ( V ^ 2 ) ) <_ %s )' % (A0, RHS))
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvdisj()
    mvpcs()
    mvdfam1()
    mvdfam()
    mvlvm()
