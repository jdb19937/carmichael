"""Sortie MV, section I: counting and orthogonality (mvlgap, mvwabs, mvwin, mvorth)."""
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


def mvlgap():
    w = W('mvlgap', '( Q - M ) / Q <_ log Q - log M for naturals 1 <_ M <_ Q (MeanValue log_gap_lower).')
    A0 = '( M e. NN /\\ Q e. NN /\\ M <_ Q )'
    P = parts(w, A0)
    mn, qn, mq = P['M e. NN'], P['Q e. NN'], P['M <_ Q']
    cl = Closure(w, A0, {'M': ('NN', mn), 'Q': ('NN', qn)})
    G = '( ( Q - M ) / Q )'; LG = '( ( log ` Q ) - ( log ` M ) )'
    lo = w.s([cl.mem('M', 'RR'), cl.mem('Q', 'RR')], 'leloed', '( %s -> ( M <_ Q <-> ( M < Q \\/ M = Q ) ) )' % A0)
    lo2 = w.s([mq, lo], 'mpbid', '( %s -> ( M < Q \\/ M = Q ) )' % A0)
    # case M < Q
    A1 = '( %s /\\ M < Q )' % A0
    c1 = Closure(w, A1, {'M': ('NN', lift(w, mn, A1)), 'Q': ('NN', lift(w, qn, A1))})
    Y = '( Q / M )'
    y1 = w.s([w.s([], 'simpr', '( %s -> M < Q )' % A1), w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A1), c1.mem('Q', 'RR'), c1.mem('M', 'RR+')], 'ltdivmuld' if False else 'ltmuldivd',
                                                               '( %s -> ( ( 1 x. M ) < Q <-> 1 < %s ) )' % (A1, Y))], 'id', 'x') if False else None
    lt1 = w.s([c1.mem('M', 'RR'), c1.mem('Q', 'RR'), c1.mem('M', 'RR+')], 'ltdiv1d' if False else 'id', 'x') if False else None
    mm = w.s([c1.mem('M', 'CC'), c1.ne0('M')], 'dividd', '( %s -> ( M / M ) = 1 )' % A1)
    ld = w.s([c1.mem('M', 'RR'), c1.mem('Q', 'RR'), c1.mem('M', 'RR+')], 'ltdiv1d', '( %s -> ( M < Q <-> ( M / M ) < ( Q / M ) ) )' % A1)
    y1 = w.s([mm, w.s([w.s([], 'simpr', '( %s -> M < Q )' % A1), ld], 'mpbid', '( %s -> ( M / M ) < ( Q / M ) )' % A1)], 'eqbrtrrd', '( %s -> 1 < %s )' % (A1, Y))
    zl = w.s([c1.mem(Y, 'RR'), y1], 'zdmlogl1' if False else 'id', 'x') if False else ap(w, A1, 'zdmlogl1', [J(w, A1, c1.mem(Y, 'RR'), y1)], '( 1 - ( 1 / %s ) ) <_ ( log ` %s )' % (Y, Y))
    ld2 = w.s([c1.mem('Q', 'RR+'), c1.mem('M', 'RR+'), w.inst('relogdiv')], 'syl2anc', '( %s -> ( log ` %s ) = %s )' % (A1, Y, LG))
    rq = w.s([c1.mem('Q', 'CC'), c1.mem('M', 'CC'), c1.ne0('Q'), c1.ne0('M')], 'recdivd', '( %s -> ( 1 / %s ) = ( M / Q ) )' % (A1, Y))
    g1 = w.s([c1.mem('Q', 'CC'), c1.mem('M', 'CC'), c1.mem('Q', 'CC'), c1.ne0('Q')], 'divsubdird', '( %s -> %s = ( ( Q / Q ) - ( M / Q ) ) )' % (A1, G))
    g2 = eqt(w, A1, g1, dst(w, A1, [w.s([c1.mem('Q', 'CC'), c1.ne0('Q')], 'dividd', '( %s -> ( Q / Q ) = 1 )' % A1)], 'oveq1d', '( ( Q / Q ) - ( M / Q ) ) = ( 1 - ( M / Q ) )'))
    g3 = eqt(w, A1, g2, eqc(w, A1, dst(w, A1, [rq], 'oveq2d', '( 1 - ( 1 / %s ) ) = ( 1 - ( M / Q ) )' % Y)))
    k1 = w.s([w.s([g3, zl], 'eqbrtrd', '( %s -> %s <_ ( log ` %s ) )' % (A1, G, Y)), ld2], 'breqtrd', '( %s -> %s <_ %s )' % (A1, G, LG))
    # case M = Q
    A2 = '( %s /\\ M = Q )' % A0
    e = w.s([], 'simpr', '( %s -> M = Q )' % A2)
    c2 = Closure(w, A2, {'M': ('NN', lift(w, mn, A2)), 'Q': ('NN', lift(w, qn, A2))})
    z1 = eqt(w, A2, dst(w, A2, [dst(w, A2, [e], 'oveq2d', '( Q - M ) = ( Q - Q )')], 'oveq1d', '%s = ( ( Q - Q ) / Q )' % G),
             dst(w, A2, [dst(w, A2, [c2.mem('Q', 'CC')], 'subidd', '( Q - Q ) = 0')], 'oveq1d', '( ( Q - Q ) / Q ) = ( 0 / Q )'))
    z2 = eqt(w, A2, z1, w.s([c2.mem('Q', 'CC'), c2.ne0('Q')], 'div0d', '( %s -> ( 0 / Q ) = 0 )' % A2))
    z3 = eqt(w, A2, dst(w, A2, [dst(w, A2, [e], 'fveq2d', '( log ` M ) = ( log ` Q )')], 'oveq2d', '%s = ( ( log ` Q ) - ( log ` Q ) )' % LG),
             dst(w, A2, [c2.mem('( log ` Q )', 'CC')], 'subidd', '( ( log ` Q ) - ( log ` Q ) ) = 0'))
    k2 = w.s([z2, w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A2)], 'leidd', '( %s -> 0 <_ 0 )' % A2), z3], '3brtr4d', '( %s -> %s <_ %s )' % (A2, G, LG))
    w.s([k1, k2, lo2], 'mpjaodan', '( %s -> %s <_ %s )' % (A0, G, LG))
    qedlast(w)
    go(w)



def mvwabs():
    w = W('mvwabs', 'Two integers of [ 1 , Q ] at logarithmic distance < pi / ( 2 T ) are at distance <_ 2 Q / T (MeanValue window_abs_bound).')
    A0 = '( ( m e. ( 1 ... Q ) /\\ n e. ( 1 ... Q ) ) /\\ ( T e. RR+ /\\ ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s ) )' % DT
    P = parts(w, A0)
    mf, nf, tp, hl = P['m e. ( 1 ... Q )'], P['n e. ( 1 ... Q )'], P['T e. RR+'], P['( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s' % DT]
    mn = ap(w, A0, 'elfznn', [mf], 'm e. NN'); nn = ap(w, A0, 'elfznn', [nf], 'n e. NN')
    fm = ap(w, A0, 'elfzle2', [mf], 'm <_ Q'); fn = ap(w, A0, 'elfzle2', [nf], 'n <_ Q')
    qz = ap(w, A0, 'elfzel2', [mf], 'Q e. ZZ')
    cl = Closure(w, A0, {'m': ('NN', mn), 'n': ('NN', nn), 'Q': ('ZZ', qz), 'T': ('RR+', tp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    qr = cl.mem('Q', 'RR')
    q1 = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), cl.mem('m', 'RR'), qr, ap(w, A0, 'nnge1', [mn], '1 <_ m'), fm], 'letrd', '( %s -> 1 <_ Q )' % A0)
    qp = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.s([], '1red', '( %s -> 1 e. RR )' % A0), qr, a1(w, A0, '0lt1', '0 < 1'), q1], 'ltletrd', '( %s -> 0 < Q )' % A0)
    cl.leaf('Q', 'gt0', qp)
    LN = '( ( log ` n ) - ( log ` m ) )'
    # DT <_ 2 / T
    p4 = dst(w, A0, [a1(w, A0, 'pigt2lt4', '( 2 < _pi /\\ _pi < 4 )')], 'simprd', '_pi < 4')
    ph2 = linarith(w, A0, [p4], '( _pi / 2 ) <_ 2', closure=cl)
    dd = w.s([cl.mem('_pi', 'CC'), a1(w, A0, '2cn', '2 e. CC'), cl.mem('T', 'CC'), a1(w, A0, '2ne0', '2 =/= 0'), cl.ne0('T')], 'divdiv1d', '( %s -> ( ( _pi / 2 ) / T ) = %s )' % (A0, DT))
    dl = w.s([w.s([cl.mem('( _pi / 2 )', 'RR'), a1(w, A0, '2re', '2 e. RR'), tp, ph2], 'lediv1dd', '( %s -> ( ( _pi / 2 ) / T ) <_ ( 2 / T ) )' % A0), dd], 'id', 'x') if False else \
        w.s([dd, w.s([cl.mem('( _pi / 2 )', 'RR'), a1(w, A0, '2re', '2 e. RR'), tp, ph2], 'lediv1dd', '( %s -> ( ( _pi / 2 ) / T ) <_ ( 2 / T ) )' % A0)], 'eqbrtrrd',
            '( %s -> %s <_ ( 2 / T ) )' % (A0, DT))
    tq = w.s([w.s([a1(w, A0, '2cn', '2 e. CC'), cl.mem('Q', 'CC'), cl.mem('T', 'CC'), cl.ne0('T')], 'div23d', '( %s -> ( ( 2 x. Q ) / T ) = ( ( 2 / T ) x. Q ) )' % A0),
              w.s([cl.mem('( 2 / T )', 'CC'), cl.mem('Q', 'CC')], 'mulcomd', '( %s -> ( ( 2 / T ) x. Q ) = ( Q x. ( 2 / T ) ) )' % A0)], 'eqtrd', '( %s -> ( ( 2 x. Q ) / T ) = ( Q x. ( 2 / T ) ) )' % A0)
    def case(a, b, fa, fb, sign):
        """case a <_ b: ( b - a ) <_ Q ( 2 / T ), with | n - m | = b - a"""
        Ac = '( %s /\\ %s <_ %s )' % (A0, a, b)
        ab = w.s([], 'simpr', '( %s -> %s <_ %s )' % (Ac, a, b))
        c = Closure(w, Ac, {'m': ('NN', lift(w, mn, Ac)), 'n': ('NN', lift(w, nn, Ac)), 'Q': [('RR', lift(w, qr, Ac)), ('gt0', lift(w, qp, Ac))], 'T': ('RR+', lift(w, tp, Ac)),
                            '_pi': ('RR+', a1(w, Ac, 'pirp', '_pi e. RR+'))})
        g = ap(w, Ac, 'mvlgap', [w.s([c.mem(a, 'NN'), c.mem(b, 'NN'), ab], '3jca', '( %s -> ( %s e. NN /\\ %s e. NN /\\ %s <_ %s ) )' % (Ac, a, b, a, b))],
               '( ( %s - %s ) / %s ) <_ ( ( log ` %s ) - ( log ` %s ) )' % (b, a, b, b, a))
        d0 = linarith(w, Ac, [ab], '0 <_ ( %s - %s )' % (b, a), closure=c)
        l2 = w.s([c.mem(b, 'RR+'), c.mem('Q', 'RR+'), c.mem('( %s - %s )' % (b, a), 'RR'), d0, lift(w, fb, Ac)], 'lediv2ad', '( %s -> ( ( %s - %s ) / Q ) <_ ( ( %s - %s ) / %s ) )' % (Ac, b, a, b, a, b))
        lr = c.mem(LN, 'RR')
        if sign > 0:
            la = ap(w, Ac, 'leabs', [lr], '%s <_ ( abs ` %s )' % (LN, LN))
            lg = w.s([g, la], 'letrd' if False else 'id', 'x') if False else None
            rel = [g, la]
        else:
            neg = ap(w, Ac, 'leabs', [c.mem('-u %s' % LN, 'RR')], '-u %s <_ ( abs ` -u %s )' % (LN, LN))
            an = ap(w, Ac, 'absneg', [c.mem(LN, 'CC')], '( abs ` -u %s ) = ( abs ` %s )' % (LN, LN))
            rel = [g, neg, an]
        for t_ in ['( abs ` %s )' % LN, '( abs ` -u %s )' % LN, '( log ` n )', '( log ` m )', '( ( %s - %s ) / Q )' % (b, a), '( ( %s - %s ) / %s )' % (b, a, b), DT, '( 2 / T )']:
            c.leaf(t_, 'RR', c.mem(t_, 'RR'))
        lq = linarith(w, Ac, rel + [l2, lift(w, hl, Ac), lift(w, dl, Ac)], '( ( %s - %s ) / Q ) <_ ( 2 / T )' % (b, a), closure=c)
        dm = w.s([lq, w.s([c.mem('( %s - %s )' % (b, a), 'RR'), c.mem('( 2 / T )', 'RR'), c.mem('Q', 'RR+')], 'ledivmuld',
                          '( %s -> ( ( ( %s - %s ) / Q ) <_ ( 2 / T ) <-> ( %s - %s ) <_ ( Q x. ( 2 / T ) ) ) )' % (Ac, b, a, b, a))], 'mpbid',
                 '( %s -> ( %s - %s ) <_ ( Q x. ( 2 / T ) ) )' % (Ac, b, a))
        if sign > 0:
            av = w.s([c.mem('( n - m )', 'RR'), d0], 'absidd', '( %s -> ( abs ` ( n - m ) ) = ( n - m ) )' % Ac)
        else:
            av = eqt(w, Ac, ap(w, Ac, 'abssub', [c.mem('n', 'CC'), c.mem('m', 'CC')] if False else [], 'x') if False else
                     w.s([c.mem('n', 'CC'), c.mem('m', 'CC')], 'abssubd', '( %s -> ( abs ` ( n - m ) ) = ( abs ` ( m - n ) ) )' % Ac),
                     w.s([c.mem('( m - n )', 'RR'), d0], 'absidd', '( %s -> ( abs ` ( m - n ) ) = ( m - n ) )' % Ac))
        return w.s([w.s([av, dm], 'eqbrtrd', '( %s -> ( abs ` ( n - m ) ) <_ ( Q x. ( 2 / T ) ) )' % Ac), lift(w, tq, Ac)], 'breqtrrd', '( %s -> ( abs ` ( n - m ) ) <_ ( ( 2 x. Q ) / T ) )' % Ac)
    k1 = case('m', 'n', fm, fn, 1)
    k2 = case('n', 'm', fn, fm, -1)
    lt = w.s([cl.mem('m', 'RR'), cl.mem('n', 'RR')], 'letrid', '( %s -> ( m <_ n \\/ n <_ m ) )' % A0)
    w.s([k1, k2, lt], 'mpjaodan', '( %s -> ( abs ` ( n - m ) ) <_ ( ( 2 x. Q ) / T ) )' % A0)
    qedlast(w)
    go(w)


def mvwin():
    w = W('mvwin', 'The window count: at most 4 Q / ( D T ) + 1 integers n e. [ 1 , Q ] are congruent to m mod D and within logarithmic distance pi / ( 2 T ) of m (MeanValue sum_window_le).')
    A0 = '( ( D e. NN /\\ T e. RR+ /\\ Q e. NN0 ) /\\ m e. ( 1 ... Q ) )'
    P = parts(w, A0)
    dn, tp, qn, mf = P['D e. NN'], P['T e. RR+'], P['Q e. NN0'], P['m e. ( 1 ... Q )']
    PHI = '( D || ( n - m ) /\\ ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s )' % DT
    PHIk = PHI.replace('( n - m )', '( k - m )').replace('( log ` n )', '( log ` k )')
    S = '{ k e. ( 1 ... Q ) | %s }' % PHIk
    X = '( ( 2 x. Q ) / ( D x. T ) )'
    Jf = '( |_ ` %s )' % X
    mn = ap(w, A0, 'elfznn', [mf], 'm e. NN')
    cl = Closure(w, A0, {'D': ('NN', dn), 'T': ('RR+', tp), 'Q': ('NN0', qn), 'm': ('NN', mn)})
    x0 = cl.ge0(X)
    jn = w.s([cl.mem(X, 'RR'), x0, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, Jf))
    cl.leaf(Jf, 'NN0', jn)
    B = '( -u %s ... %s )' % (Jf, Jf)
    # the map u |-> ( u - m ) / D into B
    Au = '( %s /\\ u e. %s )' % (A0, S)
    um = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, S))
    PHu = PHI.replace('( n - m )', '( u - m )').replace('( log ` n )', '( log ` u )')
    sub, _ = w.wcongr(PHIk, {'k': 'u'}, 'k = u', {'k': w.s([], 'id', '( k = u -> k = u )')})
    er = w.s([sub], 'elrab', '( u e. %s <-> ( u e. ( 1 ... Q ) /\\ %s ) )' % (S, PHu))
    uu = w.s([um, w.s([er], 'a1i', '( %s -> ( u e. %s <-> ( u e. ( 1 ... Q ) /\\ %s ) ) )' % (Au, S, PHu))], 'mpbid', '( %s -> ( u e. ( 1 ... Q ) /\\ %s ) )' % (Au, PHu))
    uf = dst(w, Au, [uu], 'simpld', 'u e. ( 1 ... Q )')
    ph_ = dst(w, Au, [uu], 'simprd', PHu)
    ud = dst(w, Au, [ph_], 'simpld', 'D || ( u - m )')
    ul = dst(w, Au, [ph_], 'simprd', '( abs ` ( ( log ` u ) - ( log ` m ) ) ) < %s' % DT)
    un = ap(w, Au, 'elfznn', [uf], 'u e. NN')
    cu = Closure(w, Au, {'D': ('NN', lift(w, dn, Au)), 'T': ('RR+', lift(w, tp, Au)), 'Q': ('NN0', lift(w, qn, Au)), 'm': ('NN', lift(w, mn, Au)), 'u': ('NN', un),
                         Jf: ('NN0', lift(w, jn, Au))})
    K = '( ( u - m ) / D )'
    kz = w.s([ud, w.s([cu.mem('D', 'ZZ'), cu.ne0('D'), cu.mem('( u - m )', 'ZZ'), w.inst('dvdsval2')], 'syl3anc', '( %s -> ( D || ( u - m ) <-> %s e. ZZ ) )' % (Au, K))], 'mpbid', '( %s -> %s e. ZZ )' % (Au, K))
    wa = ap(w, Au, 'mvwabs', [J(w, Au, J(w, Au, lift(w, mf, Au), uf), J(w, Au, lift(w, tp, Au), ul))], '( abs ` ( u - m ) ) <_ ( ( 2 x. Q ) / T )')
    ad = w.s([cu.mem('( u - m )', 'CC'), cu.mem('D', 'CC'), cu.ne0('D')], 'absdivd', '( %s -> ( abs ` %s ) = ( ( abs ` ( u - m ) ) / ( abs ` D ) ) )' % (Au, K))
    adD = w.s([cu.mem('D', 'RR'), ltle(w, Au, cu, cu.gt0('D'))], 'absidd', '( %s -> ( abs ` D ) = D )' % Au)
    ad2 = eqt(w, Au, ad, dst(w, Au, [adD], 'oveq2d', '( ( abs ` ( u - m ) ) / ( abs ` D ) ) = ( ( abs ` ( u - m ) ) / D )'))
    dv = w.s([cu.mem('( abs ` ( u - m ) )', 'RR'), cu.mem('( ( 2 x. Q ) / T )', 'RR'), cu.mem('D', 'RR+'), wa], 'lediv1dd', '( %s -> ( ( abs ` ( u - m ) ) / D ) <_ ( ( ( 2 x. Q ) / T ) / D ) )' % Au)
    x1 = w.s([cu.mem('( 2 x. Q )', 'CC'), cu.mem('T', 'CC'), cu.mem('D', 'CC'), cu.ne0('T'), cu.ne0('D')], 'divdiv1d', '( %s -> ( ( ( 2 x. Q ) / T ) / D ) = ( ( 2 x. Q ) / ( T x. D ) ) )' % Au)
    x2 = dst(w, Au, [w.s([cu.mem('T', 'CC'), cu.mem('D', 'CC')], 'mulcomd', '( %s -> ( T x. D ) = ( D x. T ) )' % Au)], 'oveq2d', '( ( 2 x. Q ) / ( T x. D ) ) = %s' % X)
    kle = w.s([w.s([ad2, dv], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( ( ( 2 x. Q ) / T ) / D ) )' % (Au, K)), eqt(w, Au, x1, x2)], 'breqtrd', '( %s -> ( abs ` %s ) <_ %s )' % (Au, K, X))
    ab = w.s([kle, w.s([cu.mem(K, 'RR'), cu.mem(X, 'RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) ) )' % (Au, K, X, X, K, K, X))], 'mpbid',
             '( %s -> ( -u %s <_ %s /\\ %s <_ %s ) )' % (Au, X, K, K, X))
    kx = dst(w, Au, [ab], 'simprd', '%s <_ %s' % (K, X)); nx = dst(w, Au, [ab], 'simpld', '-u %s <_ %s' % (X, K))
    kJ = w.s([kx, w.s([cu.mem(X, 'RR'), kz, w.inst('flge')], 'syl2anc', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (Au, K, X, K, Jf))], 'mpbid', '( %s -> %s <_ %s )' % (Au, K, Jf))
    cu.leaf(K, 'ZZ', kz)
    nk = linarith(w, Au, [nx], '-u %s <_ %s' % (K, X), closure=cu)
    nkJ = w.s([nk, w.s([cu.mem(X, 'RR'), cu.mem('-u %s' % K, 'ZZ'), w.inst('flge')], 'syl2anc', '( %s -> ( -u %s <_ %s <-> -u %s <_ %s ) )' % (Au, K, X, K, Jf))], 'mpbid',
              '( %s -> -u %s <_ %s )' % (Au, K, Jf))
    cu.leaf(Jf, 'RR', cu.mem(Jf, 'RR'))
    mJ = linarith(w, Au, [nkJ], '-u %s <_ %s' % (Jf, K), closure=cu)
    ef = w.s([kz, cu.mem('-u %s' % Jf, 'ZZ'), cu.mem(Jf, 'ZZ'), w.inst('elfz')], 'syl3anc', '( %s -> ( %s e. %s <-> ( -u %s <_ %s /\\ %s <_ %s ) ) )' % (Au, K, B, Jf, K, K, Jf))
    kB = w.s([w.s([mJ, kJ], 'jca', '( %s -> ( -u %s <_ %s /\\ %s <_ %s ) )' % (Au, Jf, K, K, Jf)), ef], 'mpbird', '( %s -> %s e. %s )' % (Au, K, B))
    d1 = w.s([kB], 'ex', '( %s -> ( u e. %s -> %s e. %s ) )' % (A0, S, K, B))
    # injectivity
    Auv = '( %s /\\ ( u e. %s /\\ v e. %s ) )' % (A0, S, S)
    def elem(v_, ante, memst):
        sub_, _ = w.wcongr(PHIk, {'k': v_}, 'k = %s' % v_, {'k': w.s([], 'id', '( k = %s -> k = %s )' % (v_, v_))})
        PHv = PHI.replace('( n - m )', '( %s - m )' % v_).replace('( log ` n )', '( log ` %s )' % v_)
        er_ = w.s([sub_], 'elrab', '( %s e. %s <-> ( %s e. ( 1 ... Q ) /\\ %s ) )' % (v_, S, v_, PHv))
        both = w.s([memst, w.s([er_], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. ( 1 ... Q ) /\\ %s ) ) )' % (ante, v_, S, v_, PHv))], 'mpbid', '( %s -> ( %s e. ( 1 ... Q ) /\\ %s ) )' % (ante, v_, PHv))
        return ap(w, ante, 'elfznn', [dst(w, ante, [both], 'simpld', '%s e. ( 1 ... Q )' % v_)], '%s e. NN' % v_)
    uv_u = elem('u', Auv, w.s([], 'simprl', '( %s -> u e. %s )' % (Auv, S)))
    uv_v = elem('v', Auv, w.s([], 'simprr', '( %s -> v e. %s )' % (Auv, S)))
    cv = Closure(w, Auv, {'D': ('NN', lift(w, dn, Auv)), 'm': ('NN', lift(w, mn, Auv)), 'u': ('NN', uv_u), 'v': ('NN', uv_v)})
    Kv = '( ( v - m ) / D )'
    Ae = '( %s /\\ %s = %s )' % (Auv, K, Kv)
    ce = Closure(w, Ae, {'D': ('NN', lift(w, dn, Ae)), 'm': ('NN', lift(w, mn, Ae)), 'u': ('NN', lift(w, uv_u, Ae)), 'v': ('NN', lift(w, uv_v, Ae))})
    d11 = w.s([ce.mem('( u - m )', 'CC'), ce.mem('( v - m )', 'CC'), ce.mem('D', 'CC'), ce.ne0('D'), w.s([], 'simpr', '( %s -> %s = %s )' % (Ae, K, Kv))], 'div11d', '( %s -> ( u - m ) = ( v - m ) )' % Ae)
    fwd = w.s([ce.mem('u', 'CC'), ce.mem('v', 'CC'), ce.mem('m', 'CC'), d11], 'subcan2d', '( %s -> u = v )' % Ae)
    bwd = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ u = v ) -> u = v )' % Auv)], 'oveq1d', '( ( %s /\\ u = v ) -> ( u - m ) = ( v - m ) )' % Auv)], 'oveq1d', '( ( %s /\\ u = v ) -> %s = %s )' % (Auv, K, Kv))
    iff = w.s([fwd, bwd], 'impbida', '( %s -> ( %s = %s <-> u = v ) )' % (Auv, K, Kv))
    d2 = w.s([iff], 'ex', '( %s -> ( ( u e. %s /\\ v e. %s ) -> ( %s = %s <-> u = v ) ) )' % (A0, S, S, K, Kv))
    dm = w.s([d1, d2], 'dom2d', '( %s -> ( %s e. Fin -> %s ~<_ %s ) )' % (A0, B, S, B))
    dm2 = w.s([a1(w, A0, 'fzfi', '%s e. Fin' % B), dm], 'mpd', '( %s -> %s ~<_ %s )' % (A0, S, B))
    sfin = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... Q ) e. Fin )' % A0), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... Q )' % S)], 'ssfid', '( %s -> %s e. Fin )' % (A0, S))
    hd = w.s([sfin, a1(w, A0, 'fzfi', '%s e. Fin' % B), w.inst('hashdom')], 'syl2anc', '( %s -> ( ( # ` %s ) <_ ( # ` %s ) <-> %s ~<_ %s ) )' % (A0, S, B, S, B))
    hle = w.s([dm2, hd], 'mpbird', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (A0, S, B))
    jj = w.s([cl.mem('-u %s' % Jf, 'ZZ'), cl.mem(Jf, 'ZZ'), linarith(w, A0, [cl.ge0(Jf)], '-u %s <_ %s' % (Jf, Jf), closure=cl)], 'eluz2' if False else 'id', 'x') if False else None
    cl.leaf(Jf, 'RR', cl.mem(Jf, 'RR'))
    uz = w.s([cl.mem('-u %s' % Jf, 'ZZ'), cl.mem(Jf, 'ZZ'), linarith(w, A0, [ap(w, A0, 'nn0ge0', [jn], '0 <_ %s' % Jf)], '-u %s <_ %s' % (Jf, Jf), closure=cl)], 'eluz2d' if False else '3jca' if False else 'id', 'x') if False else \
        w.s([w.s([cl.mem('-u %s' % Jf, 'ZZ'), cl.mem(Jf, 'ZZ'), linarith(w, A0, [ap(w, A0, 'nn0ge0', [jn], '0 <_ %s' % Jf)], '-u %s <_ %s' % (Jf, Jf), closure=cl)], '3jca',
                  '( %s -> ( -u %s e. ZZ /\\ %s e. ZZ /\\ -u %s <_ %s ) )' % (A0, Jf, Jf, Jf, Jf)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` -u %s ) )' % (A0, Jf, Jf))
    hf = ap(w, A0, 'hashfz', [uz], '( # ` %s ) = ( ( %s - -u %s ) + 1 )' % (B, Jf, Jf))
    # the sum is # S
    An = '( %s /\\ n e. ( 1 ... Q ) )' % A0
    subn, _ = w.wcongr(PHIk, {'k': 'n'}, 'k = n', {'k': w.s([], 'id', '( k = n -> k = n )')})
    ern = w.s([subn], 'elrab', '( n e. %s <-> ( n e. ( 1 ... Q ) /\\ %s ) )' % (S, PHI))
    rb = w.s([w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... Q ) )' % An), w.inst('ibar')], 'syl', '( %s -> ( %s <-> ( n e. ( 1 ... Q ) /\\ %s ) ) )' % (An, PHI, PHI)),
              w.s([ern], 'a1i', '( %s -> ( n e. %s <-> ( n e. ( 1 ... Q ) /\\ %s ) ) )' % (An, S, PHI))], 'bitr4d',
             '( %s -> ( %s <-> n e. %s ) )' % (An, PHI, S))
    ib = w.s([rb], 'ifbid', '( %s -> if ( %s , 1 , 0 ) = if ( n e. %s , 1 , 0 ) )' % (An, PHI, S))
    se = dst(w, A0, [ib], 'sumeq2dv', 'sum_ n e. ( 1 ... Q ) if ( %s , 1 , 0 ) = sum_ n e. ( 1 ... Q ) if ( n e. %s , 1 , 0 )' % (PHI, S))
    sh = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... Q ) e. Fin )' % A0), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... Q )' % S), w.inst('sumhash')], 'syl2anc',
             '( %s -> sum_ n e. ( 1 ... Q ) if ( n e. %s , 1 , 0 ) = ( # ` %s ) )' % (A0, S, S))
    SUM = 'sum_ n e. ( 1 ... Q ) if ( %s , 1 , 0 )' % PHI
    sv = eqt(w, A0, se, sh)
    # arithmetic: 2 J + 1 <_ 4 Q / ( D T ) + 1
    fl = ap(w, A0, 'flle', [cl.mem(X, 'RR')], '%s <_ %s' % (Jf, X))
    x4 = w.s([a1(w, A0, '2cn', '2 e. CC'), cl.mem('( 2 x. Q )', 'CC'), cl.mem('( D x. T )', 'CC'), cl.ne0('( D x. T )')], 'divassd',
             '( %s -> ( ( 2 x. ( 2 x. Q ) ) / ( D x. T ) ) = ( 2 x. %s ) )' % (A0, X))
    x5 = dst(w, A0, [ringeq(w, A0, '( 2 x. ( 2 x. Q ) )', '( 4 x. Q )', cl)], 'oveq1d', '( ( 2 x. ( 2 x. Q ) ) / ( D x. T ) ) = ( ( 4 x. Q ) / ( D x. T ) )')
    x6 = w.s([x4, x5], 'eqtr3d', '( %s -> ( 2 x. %s ) = ( ( 4 x. Q ) / ( D x. T ) ) )' % (A0, X))
    for t_ in ['( # ` %s )' % S, '( # ` %s )' % B, X, '( ( 4 x. Q ) / ( D x. T ) )']:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR') if '#' not in t_ else w.s([w.s([sfin if S in t_ else a1(w, A0, 'fzfi', '%s e. Fin' % B), w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A0, t_))], 'nn0red', '( %s -> %s e. RR )' % (A0, t_)))
    cl.leaf(SUM, 'RR', w.s([sv, cl.mem('( # ` %s )' % S, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, SUM)))
    linarith(w, A0, [sv, hle, hf, fl, x6], '%s <_ ( ( ( 4 x. Q ) / ( D x. T ) ) + 1 )' % SUM, closure=cl, name='qed')
    go(w)


def mvorth():
    w = W('mvorth', 'Orthogonality bound: | sum_ x x ( U ) x ( V )* | <_ phi ( N ) if N || U - V, else 0 (MeanValue sum_char_mul_conj, conj_char_eq_inv; sum2dchr).')
    A0 = '( N e. NN /\\ U e. ZZ /\\ V e. ZZ )'
    P = parts(w, A0)
    nn, uz, vz = P['N e. NN'], P['U e. ZZ'], P['V e. ZZ']
    Gd = '( DChr ` N )'; Dd = DB(); Zd = '( Z/nZ ` N )'; Bd = '( Base ` %s )' % Zd; Ud = '( Unit ` %s )' % Zd; Ld = LZ()
    eqs = [w.s([], 'eqid', '%s = %s' % (x, x)) for x in (Gd, Dd, Zd, Bd, Ud, Ld)]
    eG, eD, eZ, eB, eU, eL = eqs
    LU = '( %s ` U )' % Ld; LV = '( %s ` V )' % Ld
    n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    fo = w.s([n0, w.s([eZ, eB, eL], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> %s )' % (Ld, Bd))], 'syl', '( %s -> %s : ZZ -onto-> %s )' % (A0, Ld, Bd))
    ff = ap(w, A0, 'fof', [fo], '%s : ZZ --> %s' % (Ld, Bd))
    lub = w.s([ff, uz], 'ffvelcdmd', '( %s -> %s e. %s )' % (A0, LU, Bd))
    lvb = w.s([ff, vz], 'ffvelcdmd', '( %s -> %s e. %s )' % (A0, LV, Bd))
    SUM = 'sum_ x e. %s ( ( x ` %s ) x. ( * ` ( x ` %s ) ) )' % (Dd, LU, LV)
    IF = 'if ( N || ( U - V ) , ( phi ` N ) , 0 )'
    zd = w.s([n0, uz, vz, w.s([eZ, eL], 'zndvds', '( ( N e. NN0 /\\ U e. ZZ /\\ V e. ZZ ) -> ( %s = %s <-> N || ( U - V ) ) )' % (LU, LV))], 'syl3anc',
             '( %s -> ( %s = %s <-> N || ( U - V ) ) )' % (A0, LU, LV))
    # case: L V a unit
    A1 = '( %s /\\ %s e. %s )' % (A0, LV, Ud)
    s2 = w.s([eG, eD, eZ, eB, eU, lift(w, nn, A1), lift(w, lub, A1), w.s([], 'simpr', '( %s -> %s e. %s )' % (A1, LV, Ud))], 'sum2dchr',
             '( %s -> %s = if ( %s = %s , ( phi ` N ) , 0 ) )' % (A1, SUM, LU, LV))
    ib = w.s([lift(w, zd, A1)], 'ifbid', '( %s -> if ( %s = %s , ( phi ` N ) , 0 ) = %s )' % (A1, LU, LV, IF))
    ev = eqt(w, A1, s2, ib)
    c1 = Closure(w, A1, {'N': ('NN', lift(w, nn, A1))})
    ifr = w.s([c1.mem('( phi ` N )', 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A1)], 'ifcld', '( %s -> %s e. RR )' % (A1, IF))
    if0 = w.s([w.s([c1.mem('( phi ` N )', 'RR'), c1.ge0('( phi ` N )')], 'jca', '( %s -> ( ( phi ` N ) e. RR /\\ 0 <_ ( phi ` N ) ) )' % A1) if False else
               ltle(w, A1, c1, c1.gt0('( phi ` N )')), w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A1)], 'leidd', '( %s -> 0 <_ 0 )' % A1)], 'id', 'x') if False else None
    phg = ltle(w, A1, c1, c1.gt0('( phi ` N )'))
    z00 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A1)], 'leidd', '( %s -> 0 <_ 0 )' % A1)
    ifg = w.s([phg, z00], 'ifcld' if False else 'id', 'x') if False else None
    g0 = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('ifcli') if False else w.s([], 'id', 'x')], 'id', 'x')], 'id', 'x') if False else None
    # 0 <_ IF by cases on the condition
    ifc = w.s([phg, z00], 'ifbothd' if False else 'id', 'x') if False else None
    breq = w.s([], 'breq2', '( ( phi ` N ) = %s -> ( 0 <_ ( phi ` N ) <-> 0 <_ %s ) )' % (IF, IF))
    breq0 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IF, IF))
    ge = w.s([breq, breq0, phg, z00], 'ifbothda' if False else 'id', 'x') if False else None
    ge = w.s([breq, breq0, w.s([phg], 'adantr', '( ( %s /\\ N || ( U - V ) ) -> 0 <_ ( phi ` N ) )' % A1), w.s([z00], 'adantr', '( ( %s /\\ -. N || ( U - V ) ) -> 0 <_ 0 )' % A1)],
             'ifbothda', '( %s -> 0 <_ %s )' % (A1, IF))
    k1 = w.s([w.s([w.s([ev], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A1, SUM, IF)), w.s([ifr, ge], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A1, IF, IF))], 'eqtrd',
                   '( %s -> ( abs ` %s ) = %s )' % (A1, SUM, IF)), w.s([ifr], 'leidd', '( %s -> %s <_ %s )' % (A1, IF, IF))], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A1, SUM, IF))
    # case: L V not a unit
    A2 = '( %s /\\ -. %s e. %s )' % (A0, LV, Ud)
    A2x = '( %s /\\ x e. %s )' % (A2, Dd)
    xm = w.s([], 'simpr', '( %s -> x e. %s )' % (A2x, Dd))
    dn = w.s([eG, eZ, eD, eB, eU, xm, lift(w, lvb, A2x)], 'dchrn0', '( %s -> ( ( x ` %s ) =/= 0 <-> %s e. %s ) )' % (A2x, LV, LV, Ud))
    nu = lift(w, w.s([], 'simpr', '( %s -> -. %s e. %s )' % (A2, LV, Ud)), A2x)
    xz = w.s([w.s([nu, dn], 'mtbird', '( %s -> -. ( x ` %s ) =/= 0 )' % (A2x, LV))], 'nne' if False else 'id', 'x') if False else \
        w.s([w.s([nu, dn], 'mtbird', '( %s -> -. ( x ` %s ) =/= 0 )' % (A2x, LV)), w.s([], 'nne', '( -. ( x ` %s ) =/= 0 <-> ( x ` %s ) = 0 )' % (LV, LV))], 'sylib', '( %s -> ( x ` %s ) = 0 )' % (A2x, LV))
    cz = eqt(w, A2x, dst(w, A2x, [xz], 'fveq2d', '( * ` ( x ` %s ) ) = ( * ` 0 )' % LV), a1(w, A2x, 'cj0', '( * ` 0 ) = 0'))
    tz = eqt(w, A2x, dst(w, A2x, [cz], 'oveq2d', '( ( x ` %s ) x. ( * ` ( x ` %s ) ) ) = ( ( x ` %s ) x. 0 )' % (LU, LV, LU)),
             w.s([w.s([eG, eZ, eD, eL, xm, lift(w, uz, A2x)], 'dchrzrhcl', '( %s -> ( x ` %s ) e. CC )' % (A2x, LU))], 'mul01d', '( %s -> ( ( x ` %s ) x. 0 ) = 0 )' % (A2x, LU)))
    sz = eqt(w, A2, dst(w, A2, [tz], 'sumeq2dv', '%s = sum_ x e. %s 0' % (SUM, Dd)),
             w.s([w.s([w.s([lift(w, nn, A2), w.s([eG, eD], 'dchrfi', '( N e. NN -> %s e. Fin )' % Dd)], 'syl', '( %s -> %s e. Fin )' % (A2, Dd))], 'olcd', '( %s -> ( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin ) )' % (A2, Dd, Dd)),
                  w.inst('sumz')], 'syl', '( %s -> sum_ x e. %s 0 = 0 )' % (A2, Dd)))
    c2 = Closure(w, A2, {'N': ('NN', lift(w, nn, A2))})
    phg2 = ltle(w, A2, c2, c2.gt0('( phi ` N )'))
    z002 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A2)], 'leidd', '( %s -> 0 <_ 0 )' % A2)
    ge2 = w.s([breq, breq0, w.s([phg2], 'adantr', '( ( %s /\\ N || ( U - V ) ) -> 0 <_ ( phi ` N ) )' % A2), w.s([z002], 'adantr', '( ( %s /\\ -. N || ( U - V ) ) -> 0 <_ 0 )' % A2)],
              'ifbothda', '( %s -> 0 <_ %s )' % (A2, IF))
    k2 = w.s([w.s([dst(w, A2, [sz], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % SUM), a1(w, A2, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> ( abs ` %s ) = 0 )' % (A2, SUM)), ge2],
             'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A2, SUM, IF))
    w.s([k1, k2, w.s([w.s([], 'exmid', '( %s e. %s \\/ -. %s e. %s )' % (LV, Ud, LV, Ud))], 'a1i', '( %s -> ( %s e. %s \\/ -. %s e. %s ) )' % (A0, LV, Ud, LV, Ud))], 'mpjaodan',
        '( %s -> ( abs ` %s ) <_ %s )' % (A0, SUM, IF))
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvlgap()
    mvwabs()
    mvwin()
    mvorth()
