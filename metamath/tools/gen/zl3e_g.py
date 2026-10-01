"""ZL3e section G: the exponential bound on 1 / Gamma.  `MM_DB=sorties/zl3e.mm python3 tools/gen/zl3e_g.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl3e_base import *

MAIN = __name__ == '__main__'
KS = '( ( 2 x. K ) + 1 )'

# ---------------------------------------------------------------- zl3tsb
if wante('zl3tsb', MAIN):
    w = W('zl3tsb', 'The telescoping bound behind ~ zl3ppb : ` sum_ ( m = 1 .. N ) ( 2 K + 1 ) / ( m ^ 2 + K ^ 2 ) <_ 8 ` .')
    A, Cc = ante_e('zl3tsb')
    kn0 = D(w, A, 'simpl', [], 'K e. NN0'); nn0 = D(w, A, 'simpr', [], 'N e. NN0')
    kr = D(w, A, 'nn0red', [kn0], 'K e. RR'); kc = D(w, A, 'nn0cnd', [kn0], 'K e. CC'); k0 = D(w, A, 'nn0ge0d', [kn0], '0 <_ K')
    Am = '( %s /\\ m e. ( 1 ... N ) )' % A
    mfz = w.s([], 'simpr', '( %s -> m e. ( 1 ... N ) )' % Am)
    mn = D(w, Am, 'syl', [mfz, w.inst('elfznn')], 'm e. NN')
    mr = D(w, Am, 'nnred', [mn], 'm e. RR'); m1 = D(w, Am, 'nnge1d', [mn], '1 <_ m')
    krm, k0m, kcm = ad(w, Am, kr, 'K e. RR'), ad(w, Am, k0, '0 <_ K'), ad(w, Am, kc, 'K e. CC')
    a = '( m + K )'; b = '( ( m + 1 ) + K )'; Q = '( ( m ^ 2 ) + ( K ^ 2 ) )'; Dd = '( %s x. %s )' % (a, b)
    cl = Closure(w, Am, {'m': ('NN', mn), 'K': [('NN0', ad(w, Am, kn0, 'K e. NN0')), ('ge0', k0m)]})
    arp = cl.mem(a, 'RR+'); brp = cl.mem(b, 'RR+'); qrp = cl.mem(Q, 'RR+')
    ar, br, qr = cl.mem(a, 'RR'), cl.mem(b, 'RR'), cl.mem(Q, 'RR')
    ac, bc = cl.mem(a, 'CC'), cl.mem(b, 'CC')
    ane, bne = cl.ne0(a), cl.ne0(b)
    dr = cl.mem(Dd, 'RR'); dc = cl.mem(Dd, 'CC'); dne = cl.ne0(Dd)
    ksr = cl.mem(KS, 'RR'); ks0 = cl.ge0(KS); ksc = cl.mem(KS, 'CC')
    # ( 1 / a ) - ( 1 / b ) = 1 / D
    diff0 = D(w, Am, 'subrecd', [ac, bc, ane, bne], '( ( 1 / %s ) - ( 1 / %s ) ) = ( ( %s - %s ) / %s )' % (a, b, b, a, Dd))
    ba1 = lineq(w, Am, '( %s - %s )' % (b, a), '1', closure=cl)
    diff = D(w, Am, 'eqtrd', [diff0, D(w, Am, 'oveq1d', [ba1], '( ( %s - %s ) / %s ) = ( 1 / %s )' % (b, a, Dd, Dd))],
             '( ( 1 / %s ) - ( 1 / %s ) ) = ( 1 / %s )' % (a, b, Dd))
    # D <_ 4 Q
    sq1 = D(w, Am, 'sqge0d', [D(w, Am, 'resubcld', [mr, krm], '( m - K ) e. RR')], '0 <_ ( ( m - K ) ^ 2 )')
    kq = D(w, Am, 'resubcld', [krm, cl.mem('( 1 / 4 )', 'RR')], '( K - ( 1 / 4 ) ) e. RR')
    sq2 = D(w, Am, 'sqge0d', [kq], '0 <_ ( ( K - ( 1 / 4 ) ) ^ 2 )')
    mm = D(w, Am, 'mulge0d', [D(w, Am, 'resubcld', [mr, cl.mem('1', 'RR')], '( m - 1 ) e. RR'), mr,
                               linarith(w, Am, [m1], '0 <_ ( m - 1 )', closure=cl), linarith(w, Am, [m1], '0 <_ m', closure=cl)],
           '0 <_ ( ( m - 1 ) x. m )')
    d4 = nlinarith(w, Am, [sq1, sq2, mm, m1], '%s <_ ( 4 x. %s )' % (Dd, Q), closure=cl)
    d4b = D(w, Am, 'mpbird', [d4, D(w, Am, 'ledivmuld', [dr, qr, cl.mem('4', 'RR+')], '( ( %s / 4 ) <_ %s <-> %s <_ ( 4 x. %s ) )' % (Dd, Q, Dd, Q))],
            '( %s / 4 ) <_ %s' % (Dd, Q))
    d4rp = D(w, Am, 'rpdivcld', [cl.mem(Dd, 'RR+'), cl.mem('4', 'RR+')], '( %s / 4 ) e. RR+' % Dd)
    t1 = D(w, Am, 'lediv2ad', [d4rp, qrp, ksr, ks0, d4b], '( %s / %s ) <_ ( %s / ( %s / 4 ) )' % (KS, Q, KS, Dd))
    four = cl.mem('4', 'CC'); f0 = cl.ne0('4')
    T2 = '( ( %s x. 4 ) x. ( ( 1 / %s ) - ( 1 / %s ) ) )' % (KS, a, b)
    e1 = chain(w, Am, ['( %s / ( %s / 4 ) )' % (KS, Dd), '( ( %s x. 4 ) / %s )' % (KS, Dd), '( ( %s x. 4 ) x. ( 1 / %s ) )' % (KS, Dd), T2],
               [D(w, Am, 'divdiv2d', [ksc, dc, four, dne, f0], '( %s / ( %s / 4 ) ) = ( ( %s x. 4 ) / %s )' % (KS, Dd, KS, Dd)),
                D(w, Am, 'divrecd', [cl.mem('( %s x. 4 )' % KS, 'CC'), dc, dne], '( ( %s x. 4 ) / %s ) = ( ( %s x. 4 ) x. ( 1 / %s ) )' % (KS, Dd, KS, Dd)),
                ('r', D(w, Am, 'oveq2d', [diff], '%s = ( ( %s x. 4 ) x. ( 1 / %s ) )' % (T2, KS, Dd)))])
    tle = D(w, Am, 'breqtrd', [t1, e1], '( %s / %s ) <_ %s' % (KS, Q, T2))
    t1r = cl.mem('( %s / %s )' % (KS, Q), 'RR')
    t2r = D(w, Am, 'remulcld', [cl.mem('( %s x. 4 )' % KS, 'RR'), D(w, Am, 'resubcld', [cl.mem('( 1 / %s )' % a, 'RR'), cl.mem('( 1 / %s )' % b, 'RR')],
                                                                         '( ( 1 / %s ) - ( 1 / %s ) ) e. RR' % (a, b))], '%s e. RR' % T2)
    fin = D(w, A, 'fzfid', [], '( 1 ... N ) e. Fin')
    SUM = lambda body: 'sum_ m e. ( 1 ... N ) %s' % body
    s1 = D(w, A, 'fsumle', [fin, t1r, t2r, tle], '%s <_ %s' % (SUM('( %s / %s )' % (KS, Q)), SUM(T2)))
    DF = '( ( 1 / %s ) - ( 1 / %s ) )' % (a, b)
    dfc = D(w, Am, 'subcld', [cl.mem('( 1 / %s )' % a, 'CC'), cl.mem('( 1 / %s )' % b, 'CC')], '%s e. CC' % DF)
    ks4 = Closure(w, A, {'K': [('NN0', kn0), ('ge0', k0)], 'N': ('NN0', nn0)})
    s2 = D(w, A, 'fsummulc2', [fin, ks4.mem('( %s x. 4 )' % KS, 'CC'), dfc], '( ( %s x. 4 ) x. %s ) = %s' % (KS, SUM(DF), SUM(T2)))
    # telescoping
    Ak = '( %s /\\ k e. ( 1 ... ( N + 1 ) ) )' % A
    kfz = w.s([], 'simpr', '( %s -> k e. ( 1 ... ( N + 1 ) ) )' % Ak)
    kk = D(w, Ak, 'syl', [kfz, w.inst('elfznn')], 'k e. NN')
    clk = Closure(w, Ak, {'k': ('NN', kk), 'K': [('NN0', ad(w, Ak, kn0, 'K e. NN0')), ('ge0', ad(w, Ak, k0, '0 <_ K'))]})
    h7 = clk.mem('( 1 / ( k + K ) )', 'CC')
    sb = lambda v: w.s([w.s([], 'oveq1', '( k = %s -> ( k + K ) = ( %s + K ) )' % (v, v))], 'oveq2d', '( k = %s -> ( 1 / ( k + K ) ) = ( 1 / ( %s + K ) ) )' % (v, v))
    h1, h2, h3, h4 = sb('m'), sb('( m + 1 )'), sb('1'), sb('( N + 1 )')
    h5 = D(w, A, 'nn0zd', [nn0], 'N e. ZZ')
    h6 = D(w, A, 'sylib', [w.s([nn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( N + 1 ) e. NN )' % A), w.inst('elnnuz')],
           '( N + 1 ) e. ( ZZ>= ` 1 )')
    tel = D(w, A, 'telfsum', [h1, h2, h3, h4, h5, h6, h7], '%s = ( ( 1 / ( 1 + K ) ) - ( 1 / ( ( N + 1 ) + K ) ) )' % SUM(DF))
    u, v = '( 1 / ( 1 + K ) )', '( 1 / ( ( N + 1 ) + K ) )'
    s3 = D(w, A, 'oveq2d', [tel], '( ( %s x. 4 ) x. %s ) = ( ( %s x. 4 ) x. ( %s - %s ) )' % (KS, SUM(DF), KS, u, v))
    clA = Closure(w, A, {'K': [('NN0', kn0), ('ge0', k0)], 'N': [('NN0', nn0)]})
    ur, vr = clA.mem(u, 'RR'), clA.mem(v, 'RR'); v0 = clA.ge0(v)
    sa = linarith(w, A, [v0], '( %s - %s ) <_ %s' % (u, v, u), closure=clA)
    sbb = D(w, A, 'lemul2ad', [D(w, A, 'resubcld', [ur, vr], '( %s - %s ) e. RR' % (u, v)), ur, clA.mem('( %s x. 4 )' % KS, 'RR'), clA.ge0('( %s x. 4 )' % KS), sa],
            '( ( %s x. 4 ) x. ( %s - %s ) ) <_ ( ( %s x. 4 ) x. %s )' % (KS, u, v, KS, u))
    k1c = clA.mem('( 1 + K )', 'CC'); k1ne = clA.ne0('( 1 + K )')
    sc = D(w, A, 'divrecd', [clA.mem('( %s x. 4 )' % KS, 'CC'), k1c, k1ne], '( ( %s x. 4 ) / ( 1 + K ) ) = ( ( %s x. 4 ) x. %s )' % (KS, KS, u))
    lin8 = linarith(w, A, [k0], '( %s x. 4 ) <_ ( ( 1 + K ) x. 8 )' % KS, closure=clA)
    sd = D(w, A, 'mpbird', [lin8, D(w, A, 'ledivmuld', [clA.mem('( %s x. 4 )' % KS, 'RR'), clA.mem('8', 'RR'), clA.mem('( 1 + K )', 'RR+')],
                                   '( ( ( %s x. 4 ) / ( 1 + K ) ) <_ 8 <-> ( %s x. 4 ) <_ ( ( 1 + K ) x. 8 ) )' % (KS, KS))], '( ( %s x. 4 ) / ( 1 + K ) ) <_ 8' % KS)
    se = D(w, A, 'eqbrtrrd', [sc, sd], '( ( %s x. 4 ) x. %s ) <_ 8' % (KS, u))
    sf = D(w, A, 'letrd', [D(w, A, 'remulcld', [clA.mem('( %s x. 4 )' % KS, 'RR'), D(w, A, 'resubcld', [ur, vr], '( %s - %s ) e. RR' % (u, v))], '( ( %s x. 4 ) x. ( %s - %s ) ) e. RR' % (KS, u, v)),
                           D(w, A, 'remulcld', [clA.mem('( %s x. 4 )' % KS, 'RR'), ur], '( ( %s x. 4 ) x. %s ) e. RR' % (KS, u)), clA.mem('8', 'RR'), sbb, se],
           '( ( %s x. 4 ) x. ( %s - %s ) ) <_ 8' % (KS, u, v))
    sg = D(w, A, 'eqbrtrd', [D(w, A, 'eqtr3d', [s2, s3], '%s = ( ( %s x. 4 ) x. ( %s - %s ) )' % (SUM(T2), KS, u, v)), sf], '%s <_ 8' % SUM(T2))
    s1r = D(w, A, 'fsumrecl', [fin, t1r], '%s e. RR' % SUM('( %s / %s )' % (KS, Q)))
    s2r = D(w, A, 'fsumrecl', [fin, t2r], '%s e. RR' % SUM(T2))
    w.qed([D(w, A, 'letrd', [s1r, s2r, clA.mem('8', 'RR'), s1, sg], Cc)], 'idi', SE['zl3tsb'])
    goe(w)


def wsub(w, fn, v, val):
    """closed ( v = val -> ( fn(v) <-> fn(val) ) )"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, val, v, val))
    st, new = w.wcongr(fn(v), {}, '%s = %s' % (v, val), {}, rules={v: (val, idst)})
    assert new == fn(val), (new, fn(val))
    return st


def one_plus(w, A, X, Q, xc, qc, qne):
    """( A -> ( 1 + ( X / Q ) ) = ( ( Q + X ) / Q ) )"""
    dd = D(w, A, 'divdird', [qc, xc, qc, qne], '( ( %s + %s ) / %s ) = ( ( %s / %s ) + ( %s / %s ) )' % (Q, X, Q, Q, Q, X, Q))
    di = D(w, A, 'syl2anc', [qc, qne, w.inst('divid')], '( %s / %s ) = 1' % (Q, Q))
    e = D(w, A, 'eqtrd', [dd, D(w, A, 'oveq1d', [di], '( ( %s / %s ) + ( %s / %s ) ) = ( 1 + ( %s / %s ) )' % (Q, Q, X, Q, X, Q))],
          '( ( %s + %s ) / %s ) = ( 1 + ( %s / %s ) )' % (Q, X, Q, X, Q))
    return D(w, A, 'eqcomd', [e], '( 1 + ( %s / %s ) ) = ( ( %s + %s ) / %s )' % (X, Q, Q, X, Q))


# ---------------------------------------------------------------- zl3ppb
if wante('zl3ppb', MAIN):
    w = W('zl3ppb', '` prod_ ( m = 1 .. N ) ( 1 + K ^ 2 / m ^ 2 ) <_ e ^ ( 8 K ) ` for integers ` K >_ 0 ` , by induction on ` K ` : each step multiplies by ` prod ( 1 + ( 2 K + 1 ) / ( m ^ 2 + K ^ 2 ) ) <_ e ^ ( sum ... ) <_ e ^ 8 ` ( ~ zl3tsb ).')
    PS = lambda k: 'prod_ m e. ( 1 ... N ) ( 1 + ( ( %s ^ 2 ) / ( m ^ 2 ) ) ) <_ ( exp ` ( 8 x. %s ) )' % (k, k)
    h1, h2, h3, h4 = wsub(w, PS, 'k', '0'), wsub(w, PS, 'k', 'j'), wsub(w, PS, 'k', '( j + 1 )'), wsub(w, PS, 'k', 'K')
    ph = 'N e. NN'
    # base
    Pm = '( %s /\\ m e. ( 1 ... N ) )' % ph
    mn = D(w, Pm, 'syl', [w.s([], 'simpr', '( %s -> m e. ( 1 ... N ) )' % Pm), w.inst('elfznn')], 'm e. NN')
    clm = Closure(w, Pm, {'m': ('NN', mn)})
    z2 = D(w, Pm, 'sq0', [], '( 0 ^ 2 ) = 0') if False else cst(w, Pm, 'sq0', '( 0 ^ 2 ) = 0')
    t0 = chain(w, Pm, ['( 1 + ( ( 0 ^ 2 ) / ( m ^ 2 ) ) )', '( 1 + ( 0 / ( m ^ 2 ) ) )', '( 1 + 0 )', '1'],
               [D(w, Pm, 'oveq2d', [D(w, Pm, 'oveq1d', [z2], '( ( 0 ^ 2 ) / ( m ^ 2 ) ) = ( 0 / ( m ^ 2 ) )')], '( 1 + ( ( 0 ^ 2 ) / ( m ^ 2 ) ) ) = ( 1 + ( 0 / ( m ^ 2 ) ) )'),
                D(w, Pm, 'oveq2d', [D(w, Pm, 'div0d', [clm.mem('( m ^ 2 )', 'CC')], '( 0 / ( m ^ 2 ) ) = 0') if False else
                                    D(w, Pm, 'syl2anc', [clm.mem('( m ^ 2 )', 'CC'), clm.ne0('( m ^ 2 )'), w.inst('div0')], '( 0 / ( m ^ 2 ) ) = 0')],
                      '( 1 + ( 0 / ( m ^ 2 ) ) ) = ( 1 + 0 )'),
                cst(w, Pm, '1p0e1', '( 1 + 0 ) = 1')])
    p1 = D(w, ph, 'prodeq2dv', [t0], 'prod_ m e. ( 1 ... N ) ( 1 + ( ( 0 ^ 2 ) / ( m ^ 2 ) ) ) = prod_ m e. ( 1 ... N ) 1')
    pr1 = w.s([w.s([w.s([], 'fzfi', '( 1 ... N ) e. Fin')], 'olci', '( ( 1 ... N ) C_ ( ZZ>= ` 1 ) \\/ ( 1 ... N ) e. Fin )'), w.inst('prod1')], 'ax-mp', 'prod_ m e. ( 1 ... N ) 1 = 1')
    p2 = D(w, ph, 'eqtrd', [p1, w.s([pr1], 'a1i', '( %s -> prod_ m e. ( 1 ... N ) 1 = 1 )' % ph)], 'prod_ m e. ( 1 ... N ) ( 1 + ( ( 0 ^ 2 ) / ( m ^ 2 ) ) ) = 1')
    e0 = chain(w, ph, ['( exp ` ( 8 x. 0 ) )', '( exp ` 0 )', '1'],
               [D(w, ph, 'fveq2d', [cst(w, ph, '8cn', '8 e. CC') and D(w, ph, 'mul01d', [cst(w, ph, '8cn', '8 e. CC')], '( 8 x. 0 ) = 0')], '( exp ` ( 8 x. 0 ) ) = ( exp ` 0 )'),
                cst(w, ph, 'ef0', '( exp ` 0 ) = 1')])
    base = D(w, ph, 'breq12d', [p2, e0], '( %s <-> 1 <_ 1 )' % PS('0'))
    ch = D(w, ph, 'mpbird', [cst(w, ph, '1le1', '1 <_ 1'), base], PS('0'))
    goe(w) if False else None
    # step
    B0 = '( %s /\\ j e. NN0 )' % ph
    B = B0
    BT = '( %s /\\ %s )' % (B0, PS('j'))
    jn0 = D(w, B, 'simpr', [], 'j e. NN0'); nnB = D(w, B, 'simpl', [], 'N e. NN'); th = w.s([], 'simpr', '( %s -> %s )' % (BT, PS('j')))
    j0 = D(w, B, 'nn0ge0d', [jn0], '0 <_ j')
    Bm = '( %s /\\ m e. ( 1 ... N ) )' % B
    mnB = D(w, Bm, 'syl', [w.s([], 'simpr', '( %s -> m e. ( 1 ... N ) )' % Bm), w.inst('elfznn')], 'm e. NN')
    clB = Closure(w, Bm, {'m': ('NN', mnB), 'j': [('NN0', ad(w, Bm, jn0, 'j e. NN0')), ('ge0', ad(w, Bm, j0, '0 <_ j'))]})
    q, p, c = '( m ^ 2 )', '( j ^ 2 )', '( ( 2 x. j ) + 1 )'
    qp = '( %s + %s )' % (q, p)
    am = '( 1 + ( %s / %s ) )' % (p, q); bm = '( 1 + ( %s / %s ) )' % (c, qp); tm = '( 1 + ( ( ( j + 1 ) ^ 2 ) / %s ) )' % q
    qc, pc, cc_, qpc = clB.mem(q, 'CC'), clB.mem(p, 'CC'), clB.mem(c, 'CC'), clB.mem(qp, 'CC')
    qne, qpne = clB.ne0(q), clB.ne0(qp)
    jc = clB.mem('j', 'CC')
    sq = D(w, Bm, 'syl', [jc, w.inst('binom21')], '( ( j + 1 ) ^ 2 ) = ( ( ( j ^ 2 ) + ( 2 x. j ) ) + 1 )')
    sq2 = D(w, Bm, 'eqtrd', [sq, D(w, Bm, 'addassd', [pc, clB.mem('( 2 x. j )', 'CC'), clB.mem('1', 'CC')], '( ( ( j ^ 2 ) + ( 2 x. j ) ) + 1 ) = ( %s + %s )' % (p, c))],
             '( ( j + 1 ) ^ 2 ) = ( %s + %s )' % (p, c))
    pcs = '( %s + %s )' % (p, c)
    idm = chain(w, Bm, [tm, '( 1 + ( %s / %s ) )' % (pcs, q), '( ( %s + %s ) / %s )' % (q, pcs, q), '( ( %s + %s ) / %s )' % (qp, c, q),
                        '( ( ( %s + %s ) / %s ) x. ( %s / %s ) )' % (qp, c, qp, qp, q), '( %s x. %s )' % (bm, am), '( %s x. %s )' % (am, bm)],
                [D(w, Bm, 'oveq2d', [D(w, Bm, 'oveq1d', [sq2], '( ( ( j + 1 ) ^ 2 ) / %s ) = ( %s / %s )' % (q, pcs, q))], '%s = ( 1 + ( %s / %s ) )' % (tm, pcs, q)),
                 one_plus(w, Bm, pcs, q, clB.mem(pcs, 'CC'), qc, qne),
                 D(w, Bm, 'oveq1d', [D(w, Bm, 'addassd', [qc, pc, cc_], '( ( %s + %s ) + %s ) = ( %s + %s )' % (q, p, c, q, pcs)) and
                                     D(w, Bm, 'eqcomd', [D(w, Bm, 'addassd', [qc, pc, cc_], '( ( %s + %s ) + %s ) = ( %s + %s )' % (q, p, c, q, pcs))], '( %s + %s ) = ( ( %s + %s ) + %s )' % (q, pcs, q, p, c))],
                       '( ( %s + %s ) / %s ) = ( ( %s + %s ) / %s )' % (q, pcs, q, qp, c, q)),
                 ('r', D(w, Bm, 'dmdcan2d', [clB.mem('( %s + %s )' % (qp, c), 'CC'), qpc, qc, qpne, qne], '( ( ( %s + %s ) / %s ) x. ( %s / %s ) ) = ( ( %s + %s ) / %s )' % (qp, c, qp, qp, q, qp, c, q))),
                 D(w, Bm, 'oveq12d', [D(w, Bm, 'eqcomd', [one_plus(w, Bm, c, qp, cc_, qpc, qpne)], '( ( %s + %s ) / %s ) = %s' % (qp, c, qp, bm)),
                                      D(w, Bm, 'eqcomd', [one_plus(w, Bm, p, q, pc, qc, qne)], '( %s / %s ) = %s' % (qp, q, am))],
                       '( ( ( %s + %s ) / %s ) x. ( %s / %s ) ) = ( %s x. %s )' % (qp, c, qp, qp, q, bm, am)),
                 D(w, Bm, 'mulcomd', [clB.mem(bm, 'CC'), clB.mem(am, 'CC')], '( %s x. %s ) = ( %s x. %s )' % (bm, am, am, bm))])
    PR_ = lambda body: 'prod_ m e. ( 1 ... N ) %s' % body
    finB = D(w, B, 'fzfid', [], '( 1 ... N ) e. Fin')
    pe = D(w, B, 'prodeq2dv', [idm], '%s = %s' % (PR_(tm), PR_('( %s x. %s )' % (am, bm))))
    pm = D(w, B, 'fprodmul', [finB, clB.mem(am, 'CC'), clB.mem(bm, 'CC')], '%s = ( %s x. %s )' % (PR_('( %s x. %s )' % (am, bm)), PR_(am), PR_(bm)))
    cm = '( %s / %s )' % (c, qp)
    # prod b <_ exp ( sum c ) <_ exp 8
    nfB = w.s([], 'nfv', 'F/ m %s' % B)
    ble = D(w, Bm, 'ltled', [clB.mem(bm, 'RR'), clB.mem('( exp ` %s )' % cm, 'RR'), D(w, Bm, 'syl', [clB.mem(cm, 'RR+'), w.inst('efgt1p')], '%s < ( exp ` %s )' % (bm, cm))],
            '%s <_ ( exp ` %s )' % (bm, cm))
    pb = D(w, B, 'fprodle', [nfB, finB, clB.mem(bm, 'RR'), clB.ge0(bm), clB.mem('( exp ` %s )' % cm, 'RR'), ble], '%s <_ %s' % (PR_(bm), PR_('( exp ` %s )' % cm)))
    Bz = '( %s /\\ m e. ( ZZ>= ` 1 ) )' % B
    mz = D(w, Bz, 'sylib', [w.s([], 'simpr', '( %s -> m e. ( ZZ>= ` 1 ) )' % Bz), w.inst('elnnuz')], 'm e. NN') if False else \
        D(w, Bz, 'sylibr', [w.s([], 'simpr', '( %s -> m e. ( ZZ>= ` 1 ) )' % Bz), w.inst('elnnuz')], 'm e. NN')
    clz = Closure(w, Bz, {'m': ('NN', mz), 'j': [('NN0', ad(w, Bz, jn0, 'j e. NN0')), ('ge0', ad(w, Bz, j0, '0 <_ j'))]})
    nuz = D(w, B, 'sylib', [nnB, w.inst('elnnuz')], 'N e. ( ZZ>= ` 1 )')
    pfs = D(w, B, 'fprodefsum', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )') and w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )'), nuz, clz.mem(cm, 'CC')],
            '%s = ( exp ` sum_ m e. ( 1 ... N ) %s )' % (PR_('( exp ` %s )' % cm), cm))
    tsb = D(w, B, 'syl2anc', [jn0, D(w, B, 'nnnn0d', [nnB], 'N e. NN0'), w.inst('zl3tsb')], 'sum_ m e. ( 1 ... N ) %s <_ 8' % cm.replace('( m ^ 2 ) + ( j ^ 2 )', '( m ^ 2 ) + ( j ^ 2 )'))
    sr = D(w, B, 'fsumrecl', [finB, clB.mem(cm, 'RR')], 'sum_ m e. ( 1 ... N ) %s e. RR' % cm)
    e8 = efle_(w, B, 'sum_ m e. ( 1 ... N ) %s' % cm, '8', sr, cst(w, B, '8re', '8 e. RR'), tsb)
    pb2 = D(w, B, 'letrd', [D(w, B, 'fprodrecl', [finB, clB.mem(bm, 'RR')], '%s e. RR' % PR_(bm)), D(w, B, 'reefcld', [sr], '( exp ` sum_ m e. ( 1 ... N ) %s ) e. RR' % cm),
                            cst(w, B, '8re', '8 e. RR') and D(w, B, 'reefcld', [cst(w, B, '8re', '8 e. RR')], '( exp ` 8 ) e. RR'),
                            D(w, B, 'breqtrd', [pb, pfs], '%s <_ ( exp ` sum_ m e. ( 1 ... N ) %s )' % (PR_(bm), cm)), e8], '%s <_ ( exp ` 8 )' % PR_(bm))
    ar = D(w, B, 'fprodrecl', [finB, clB.mem(am, 'RR')], '%s e. RR' % PR_(am))
    a0 = D(w, B, 'fprodge0', [nfB, finB, clB.mem(am, 'RR'), clB.ge0(am)], '0 <_ %s' % PR_(am))
    b0 = D(w, B, 'fprodge0', [nfB, finB, clB.mem(bm, 'RR'), clB.ge0(bm)], '0 <_ %s' % PR_(bm))
    j8 = D(w, B, 'reefcld', [D(w, B, 'remulcld', [cst(w, B, '8re', '8 e. RR'), D(w, B, 'nn0red', [jn0], 'j e. RR')], '( 8 x. j ) e. RR')], '( exp ` ( 8 x. j ) ) e. RR')
    L_ = lambda st, f: ad(w, BT, st, f)
    mul = D(w, BT, 'lemul12ad', [L_(ar, '%s e. RR' % PR_(am)), L_(j8, '( exp ` ( 8 x. j ) ) e. RR'), L_(D(w, B, 'fprodrecl', [finB, clB.mem(bm, 'RR')], '%s e. RR' % PR_(bm)), '%s e. RR' % PR_(bm)), L_(D(w, B, 'reefcld', [cst(w, B, '8re', '8 e. RR')], '( exp ` 8 ) e. RR'), '( exp ` 8 ) e. RR'),
                                L_(a0, '0 <_ %s' % PR_(am)), L_(b0, '0 <_ %s' % PR_(bm)), th, L_(pb2, '%s <_ ( exp ` 8 )' % PR_(bm))],
            '( %s x. %s ) <_ ( ( exp ` ( 8 x. j ) ) x. ( exp ` 8 ) )' % (PR_(am), PR_(bm)))
    jc_ = D(w, B, 'nn0cnd', [jn0], 'j e. CC')
    ee = chain(w, B, ['( ( exp ` ( 8 x. j ) ) x. ( exp ` 8 ) )', '( exp ` ( ( 8 x. j ) + 8 ) )', '( exp ` ( 8 x. ( j + 1 ) ) )'],
               [('r', efadd_(w, B, '( 8 x. j )', '8', D(w, B, 'mulcld', [cst(w, B, '8cn', '8 e. CC'), jc_], '( 8 x. j ) e. CC'), cst(w, B, '8cn', '8 e. CC'))),
                D(w, B, 'fveq2d', [D(w, B, 'eqcomd', [D(w, B, 'adddid', [cst(w, B, '8cn', '8 e. CC'), jc_, cst(w, B, 'ax-1cn', '1 e. CC')], '( 8 x. ( j + 1 ) ) = ( ( 8 x. j ) + ( 8 x. 1 ) )')],
                                                   '( ( 8 x. j ) + ( 8 x. 1 ) ) = ( 8 x. ( j + 1 ) )') and
                                   D(w, B, 'eqtr3d', [D(w, B, 'oveq2d', [D(w, B, 'mulridd', [cst(w, B, '8cn', '8 e. CC')], '( 8 x. 1 ) = 8')], '( ( 8 x. j ) + ( 8 x. 1 ) ) = ( ( 8 x. j ) + 8 )'),
                                                      D(w, B, 'eqcomd', [D(w, B, 'adddid', [cst(w, B, '8cn', '8 e. CC'), jc_, cst(w, B, 'ax-1cn', '1 e. CC')], '( 8 x. ( j + 1 ) ) = ( ( 8 x. j ) + ( 8 x. 1 ) )')],
                                                        '( ( 8 x. j ) + ( 8 x. 1 ) ) = ( 8 x. ( j + 1 ) )')], '( ( 8 x. j ) + 8 ) = ( 8 x. ( j + 1 ) )')],
                      '( exp ` ( ( 8 x. j ) + 8 ) ) = ( exp ` ( 8 x. ( j + 1 ) ) )')])
    pe2 = D(w, B, 'eqtrd', [pe, pm], '%s = ( %s x. %s )' % (PR_(tm), PR_(am), PR_(bm)))
    ta = D(w, BT, 'breqtrd', [D(w, BT, 'eqbrtrd', [L_(pe2, '%s = ( %s x. %s )' % (PR_(tm), PR_(am), PR_(bm))), mul],
                                                 '%s <_ ( ( exp ` ( 8 x. j ) ) x. ( exp ` 8 ) )' % PR_(tm)), L_(ee, '( exp ` ( ( 8 x. j ) + 8 ) ) = ( exp ` ( 8 x. ( j + 1 ) ) )') if False else L_(ee, '( ( exp ` ( 8 x. j ) ) x. ( exp ` 8 ) ) = ( exp ` ( 8 x. ( j + 1 ) ) )')], PS('( j + 1 )'))
    fin = w.s([h1, h2, h3, h4, ch, ta], 'nn0indd', '( ( N e. NN /\\ K e. NN0 ) -> %s )' % PS('K'))
    w.qed([fin], 'ancoms', SE['zl3ppb'])
    goe(w)


FACT = lambda m, A: '( ( ( ( %s + 1 ) / %s ) ^c %s ) / ( ( %s / %s ) + 1 ) )' % (m, m, A, A, m)


def eut_val(w, Ac, A, arg, argmem):
    """( Ac -> ( EUT(A) ` arg ) = FACT(arg, A) )"""
    return fv1(w, Ac, 'm', 'NN', lambda v: FACT(v, A), arg, argmem, 'ovex')


# ---------------------------------------------------------------- zl3gfc
if wante('zl3gfc', MAIN):
    w = W('zl3gfc', 'One factor of the Gauss product ( ~ gamcvg2 ) at ` V ` against the factor at ` Re V ` : ` F_M ( Re V ) ^ 2 <_ abs ( F_M ( V ) ) ^ 2 ( 1 + K ^ 2 / M ^ 2 ) ` for ` abs ( Im V ) <_ K ` .')
    A, Cc = ante_e('zl3gfc')
    hv = D(w, A, 'simpl', [], LE.HVK)
    vc = D(w, A, 'simplld', [hv], 'V e. CC') if False else D(w, A, 'simpld', [D(w, A, 'simpld', [hv], '( V e. CC /\\ 0 <_ ( Re ` V ) )')], 'V e. CC')
    x0 = D(w, A, 'simprd', [D(w, A, 'simpld', [hv], '( V e. CC /\\ 0 <_ ( Re ` V ) )')], '0 <_ ( Re ` V )')
    kk = D(w, A, 'simprd', [hv], '( K e. NN0 /\\ ( abs ` ( Im ` V ) ) <_ K )')
    kn0 = D(w, A, 'simpld', [kk], 'K e. NN0'); yk = D(w, A, 'simprd', [kk], '( abs ` ( Im ` V ) ) <_ K')
    mn = D(w, A, 'simpr', [], 'M e. NN')
    x, y = '( Re ` V )', '( Im ` V )'
    xr = D(w, A, 'recld', [vc], '%s e. RR' % x); yr = D(w, A, 'imcld', [vc], '%s e. RR' % y)
    cl = Closure(w, A, {'M': ('NN', mn), 'K': [('NN0', kn0)], x: [('RR', xr), ('ge0', x0)], y: ('RR', yr), 'V': ('CC', vc)})
    r = '( ( M + 1 ) / M )'
    rrp = cl.mem(r, 'RR+')
    cV, cx = '( %s ^c V )' % r, '( %s ^c %s )' % (r, x)
    cxrp = D(w, A, 'syl2anc', [rrp, xr, w.inst('rpcxpcl')], '%s e. RR+' % cx)
    cl.leaf(cx, 'RR+', cxrp)
    acV = D(w, A, 'syl2anc', [rrp, vc, w.inst('abscxp')], '( abs ` %s ) = %s' % (cV, cx))
    d, e = '( ( V / M ) + 1 )', '( ( %s / M ) + 1 )' % x
    mr = cl.mem('M', 'RR'); mne = cl.ne0('M')
    dc = cl.mem(d, 'CC')
    re_d = chain(w, A, ['( Re ` %s )' % d, '( ( Re ` ( V / M ) ) + ( Re ` 1 ) )', '( ( %s / M ) + 1 )' % x],
                 [D(w, A, 'readdd', [cl.mem('( V / M )', 'CC'), cl.mem('1', 'CC')], '( Re ` %s ) = ( ( Re ` ( V / M ) ) + ( Re ` 1 ) )' % d),
                  D(w, A, 'oveq12d', [D(w, A, 'redivd', [mr, vc, mne], '( Re ` ( V / M ) ) = ( %s / M )' % x), cst(w, A, 're1', '( Re ` 1 ) = 1')],
                    '( ( Re ` ( V / M ) ) + ( Re ` 1 ) ) = ( ( %s / M ) + 1 )' % x)])
    im_d = chain(w, A, ['( Im ` %s )' % d, '( ( Im ` ( V / M ) ) + ( Im ` 1 ) )', '( ( %s / M ) + 0 )' % y, '( %s / M )' % y],
                 [D(w, A, 'imaddd', [cl.mem('( V / M )', 'CC'), cl.mem('1', 'CC')], '( Im ` %s ) = ( ( Im ` ( V / M ) ) + ( Im ` 1 ) )' % d),
                  D(w, A, 'oveq12d', [D(w, A, 'imdivd', [mr, vc, mne], '( Im ` ( V / M ) ) = ( %s / M )' % y), cst(w, A, 'im1', '( Im ` 1 ) = 0')],
                    '( ( Im ` ( V / M ) ) + ( Im ` 1 ) ) = ( ( %s / M ) + 0 )' % y),
                  D(w, A, 'addridd', [cl.mem('( %s / M )' % y, 'CC')], '( ( %s / M ) + 0 ) = ( %s / M )' % (y, y))])
    E2, Y2 = '( %s ^ 2 )' % e, '( ( %s / M ) ^ 2 )' % y
    dd = '( ( abs ` %s ) ^ 2 )' % d
    dsq = chain(w, A, [dd, '( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (d, d), '( %s + %s )' % (E2, Y2)],
                [D(w, A, 'syl', [dc, w.inst('absvalsq2')], '%s = ( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (dd, d, d)),
                 D(w, A, 'oveq12d', [D(w, A, 'oveq1d', [re_d], '( ( Re ` %s ) ^ 2 ) = %s' % (d, E2)), D(w, A, 'oveq1d', [im_d], '( ( Im ` %s ) ^ 2 ) = %s' % (d, Y2))],
                   '( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) ) = ( %s + %s )' % (d, d, E2, Y2))])
    T = '( ( K ^ 2 ) / ( M ^ 2 ) )'
    S = '( 1 + %s )' % T
    er = cl.mem(e, 'RR'); e1 = linarith(w, A, [cl.ge0('( %s / M )' % x)], '1 <_ %s' % e, closure=cl)
    e21 = D(w, A, 'syl3anc', [er, cst(w, A, '2nn0', '2 e. NN0'), e1, w.inst('expge1')], '1 <_ %s' % E2)
    ay = D(w, A, 'abscld', [cl.mem(y, 'CC')], '( abs ` %s ) e. RR' % y)
    y2 = D(w, A, 'eqbrtrrd', [D(w, A, 'syl', [yr, w.inst('absresq')], '( ( abs ` %s ) ^ 2 ) = ( %s ^ 2 )' % (y, y)),
                              D(w, A, 'syl2anc', [D(w, A, 'jca', [ay, D(w, A, 'absge0d', [cl.mem(y, 'CC')], '0 <_ ( abs ` %s )' % y)], '( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) )' % (y, y)),
                                                  D(w, A, 'jca', [cl.mem('K', 'RR'), yk], '( K e. RR /\\ ( abs ` %s ) <_ K )' % y), w.inst('le2sq2')],
                                '( ( abs ` %s ) ^ 2 ) <_ ( K ^ 2 )' % y)], '( %s ^ 2 ) <_ ( K ^ 2 )' % y)
    m2rp = cl.mem('( M ^ 2 )', 'RR+')
    y2m = D(w, A, 'mpbid', [y2, D(w, A, 'lediv1d', [cl.mem('( %s ^ 2 )' % y, 'RR'), cl.mem('( K ^ 2 )', 'RR'), m2rp],
                                  '( ( %s ^ 2 ) <_ ( K ^ 2 ) <-> ( ( %s ^ 2 ) / ( M ^ 2 ) ) <_ %s )' % (y, y, T))], '( ( %s ^ 2 ) / ( M ^ 2 ) ) <_ %s' % (y, T))
    y2e = D(w, A, 'sqdivd', [cl.mem(y, 'CC'), cl.mem('M', 'CC'), mne], '%s = ( ( %s ^ 2 ) / ( M ^ 2 ) )' % (Y2, y))
    Y2T = D(w, A, 'eqbrtrd', [y2e, y2m], '%s <_ %s' % (Y2, T))
    tr, t0 = cl.mem(T, 'RR'), cl.ge0(T)
    e2r = cl.mem(E2, 'RR')
    TE = D(w, A, 'lemulge12d', [tr, e2r, t0, e21], '%s <_ ( %s x. %s )' % (T, E2, T)) if False else \
        D(w, A, 'mpbid', [D(w, A, 'lemul1ad', [cl.mem('1', 'RR'), e2r, tr, t0, e21], '( 1 x. %s ) <_ ( %s x. %s )' % (T, E2, T)),
                           D(w, A, 'breq1d', [D(w, A, 'mullidd', [cl.mem(T, 'CC')], '( 1 x. %s ) = %s' % (T, T))], '( ( 1 x. %s ) <_ ( %s x. %s ) <-> %s <_ ( %s x. %s ) )' % (T, E2, T, T, E2, T))],
          '%s <_ ( %s x. %s )' % (T, E2, T))
    ddle = D(w, A, 'eqbrtrd', [dsq, nlinarith(w, A, [Y2T, TE], '( %s + %s ) <_ ( %s x. %s )' % (E2, Y2, E2, S), closure=cl, atoms=[E2, Y2, T])], '%s <_ ( %s x. %s )' % (dd, E2, S))
    # the two squares
    cnum = '( %s ^ 2 )' % cx
    ene = cl.ne0(e)
    lhs_e = chain(w, A, ['( ( %s ` M ) ^ 2 )' % LE.EUT(x), '( ( %s / %s ) ^ 2 )' % (cx, e), '( %s / %s )' % (cnum, E2)],
                  [D(w, A, 'oveq1d', [eut_val(w, A, x, 'M', mn)], '( ( %s ` M ) ^ 2 ) = ( ( %s / %s ) ^ 2 )' % (LE.EUT(x), cx, e)),
                   D(w, A, 'sqdivd', [cl.mem(cx, 'CC'), cl.mem(e, 'CC'), ene], '( ( %s / %s ) ^ 2 ) = ( %s / %s )' % (cx, e, cnum, E2))])
    # d =/= 0 : 0 < Re d
    dne = D(w, A, 'mpbid', [D(w, A, 'gt0ne0d', [D(w, A, 'breqtrrd', [linarith(w, A, [cl.ge0('( %s / M )' % x)], '0 < %s' % e, closure=cl), re_d], '0 < ( Re ` %s )' % d)], '( Re ` %s ) =/= 0' % d) if False else
                            D(w, A, 'gt0ne0d', [D(w, A, 'breqtrrd', [linarith(w, A, [cl.ge0('( %s / M )' % x)], '0 < %s' % e, closure=cl), re_d], '0 < ( Re ` %s )' % d)], '( Re ` %s ) =/= 0' % d),
                            cst(w, A, 'tru', 'T.') and D(w, A, 'syl', [dc, w.inst('recne0...')], '') if False else None], '') if False else None
    red0 = D(w, A, 'gt0ne0d', [D(w, A, 'breqtrrd', [linarith(w, A, [cl.ge0('( %s / M )' % x)], '0 < %s' % e, closure=cl), re_d], '0 < ( Re ` %s )' % d)], '( Re ` %s ) =/= 0' % d)
    dne = D(w, A, 'mpd', [red0, D(w, A, 'necon3d', [D(w, A, 'fveq2', [], '')], '')], '') if False else \
        D(w, A, 'mpbird', [red0, D(w, A, 'necon3bid', [], '')], '') if False else None
    # d =/= 0 from Re d =/= 0 : fveq2 + re0
    ad0 = w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (d, d)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (d, d))
    dne = D(w, A, 'necon3i', [], '') if False else w.s([red0, w.s([ad0], 'necon3i', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (d, d))], 'syl', '( %s -> %s =/= 0 )' % (A, d))
    ade = D(w, A, 'absdivd', [cl.mem(cV, 'CC'), dc, dne], '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (cV, d, cV, d))
    adc = D(w, A, 'abscld', [dc], '( abs ` %s ) e. RR' % d); adcc = D(w, A, 'recnd', [adc], '( abs ` %s ) e. CC' % d)
    adne = D(w, A, 'absne0d', [dc, dne], '( abs ` %s ) =/= 0' % d)
    rhs_e = chain(w, A, ['( ( abs ` ( %s ` M ) ) ^ 2 )' % LE.EUT('V'), '( ( abs ` ( %s / %s ) ) ^ 2 )' % (cV, d), '( ( %s / ( abs ` %s ) ) ^ 2 )' % (cx, d), '( %s / %s )' % (cnum, dd)],
                  [D(w, A, 'oveq1d', [D(w, A, 'fveq2d', [eut_val(w, A, 'V', 'M', mn)], '( abs ` ( %s ` M ) ) = ( abs ` ( %s / %s ) )' % (LE.EUT('V'), cV, d))],
                     '( ( abs ` ( %s ` M ) ) ^ 2 ) = ( ( abs ` ( %s / %s ) ) ^ 2 )' % (LE.EUT('V'), cV, d)),
                   D(w, A, 'oveq1d', [D(w, A, 'eqtrd', [ade, D(w, A, 'oveq1d', [acV], '( ( abs ` %s ) / ( abs ` %s ) ) = ( %s / ( abs ` %s ) )' % (cV, d, cx, d))],
                                        '( abs ` ( %s / %s ) ) = ( %s / ( abs ` %s ) )' % (cV, d, cx, d))], '( ( abs ` ( %s / %s ) ) ^ 2 ) = ( ( %s / ( abs ` %s ) ) ^ 2 )' % (cV, d, cx, d)),
                   D(w, A, 'sqdivd', [cl.mem(cx, 'CC'), adcc, adne], '( ( %s / ( abs ` %s ) ) ^ 2 ) = ( %s / %s )' % (cx, d, cnum, dd))])
    ddrp = D(w, A, 'elrpd', [D(w, A, 'resqcld', [adc], '%s e. RR' % dd), D(w, A, 'sqgt0d', [adc, adne], '0 < %s' % dd) if False else
                             D(w, A, 'sqgt0d', [adc, adne], '0 < %s' % dd)], '%s e. RR+' % dd)
    srp = cl.mem(S, 'RR+'); e2rp = cl.mem(E2, 'RR+')
    ESrp = D(w, A, 'rpmulcld', [e2rp, srp], '( %s x. %s ) e. RR+' % (E2, S))
    csr = D(w, A, 'remulcld', [cl.mem(cnum, 'RR'), cl.mem(S, 'RR')], '( %s x. %s ) e. RR' % (cnum, S))
    cs0 = D(w, A, 'mulge0d', [cl.mem(cnum, 'RR'), cl.mem(S, 'RR'), cl.ge0(cnum), cl.ge0(S)], '0 <_ ( %s x. %s )' % (cnum, S))
    q1 = D(w, A, 'lediv2ad', [ddrp, ESrp, csr, cs0, ddle], '( ( %s x. %s ) / ( %s x. %s ) ) <_ ( ( %s x. %s ) / %s )' % (cnum, S, E2, S, cnum, S, dd))
    q2 = D(w, A, 'divcan5rd', [cl.mem(cnum, 'CC'), cl.mem(E2, 'CC'), cl.mem(S, 'CC'), cl.ne0(E2), cl.ne0(S)], '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (cnum, S, E2, S, cnum, E2))
    q3 = D(w, A, 'div23d', [cl.mem(cnum, 'CC'), cl.mem(S, 'CC'), D(w, A, 'rpcnd', [ddrp], '%s e. CC' % dd), D(w, A, 'rpne0d', [ddrp], '%s =/= 0' % dd)],
           '( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s )' % (cnum, S, dd, cnum, dd, S))
    q4 = D(w, A, 'breqtrd', [D(w, A, 'eqbrtrrd', [q2, q1], '( %s / %s ) <_ ( ( %s x. %s ) / %s )' % (cnum, E2, cnum, S, dd)), q3], '( %s / %s ) <_ ( ( %s / %s ) x. %s )' % (cnum, E2, cnum, dd, S))
    fin = D(w, A, 'breqtrd', [D(w, A, 'eqbrtrd', [lhs_e, q4], '( ( %s ` M ) ^ 2 ) <_ ( ( %s / %s ) x. %s )' % (LE.EUT(x), cnum, dd, S)),
                              D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [rhs_e], '( %s / %s ) = ( ( abs ` ( %s ` M ) ) ^ 2 )' % (cnum, dd, LE.EUT('V')))],
                                '( ( %s / %s ) x. %s ) = ( ( ( abs ` ( %s ` M ) ) ^ 2 ) x. %s )' % (cnum, dd, S, LE.EUT('V'), S))], Cc)
    w.qed([fin], 'idi', SE['zl3gfc'])
    goe(w)


def fact_facts(w, Ak, kn, vc, x0, V='V', k='k'):
    """under Ak with k e. NN, V e. CC, 0 <_ Re V: ( EUT(Re V) ` k ) e. RR+, ( EUT(V) ` k ) e. CC"""
    x = '( Re ` %s )' % V
    xr = D(w, Ak, 'recld', [vc], '%s e. RR' % x)
    cl = Closure(w, Ak, {k: ('NN', kn), x: [('RR', xr), ('ge0', x0)], V: ('CC', vc)})
    r = '( ( %s + 1 ) / %s )' % (k, k)
    cx = '( %s ^c %s )' % (r, x)
    cl.leaf(cx, 'RR+', D(w, Ak, 'syl2anc', [cl.mem(r, 'RR+'), xr, w.inst('rpcxpcl')], '%s e. RR+' % cx))
    e = '( ( %s / %s ) + 1 )' % (x, k)
    vx = eut_val(w, Ak, x, k, kn)
    xrp = D(w, Ak, 'eqeltrd', [vx, cl.mem(FACT(k, x), 'RR+')], '( %s ` %s ) e. RR+' % (LE.EUT(x), k))
    d = '( ( %s / %s ) + 1 )' % (V, k)
    dc = cl.mem(d, 'CC')
    re_d = chain(w, Ak, ['( Re ` %s )' % d, '( ( Re ` ( %s / %s ) ) + ( Re ` 1 ) )' % (V, k), e],
                 [D(w, Ak, 'readdd', [cl.mem('( %s / %s )' % (V, k), 'CC'), cl.mem('1', 'CC')], '( Re ` %s ) = ( ( Re ` ( %s / %s ) ) + ( Re ` 1 ) )' % (d, V, k)),
                  D(w, Ak, 'oveq12d', [D(w, Ak, 'redivd', [cl.mem(k, 'RR'), vc, cl.ne0(k)], '( Re ` ( %s / %s ) ) = ( %s / %s )' % (V, k, x, k)), cst(w, Ak, 're1', '( Re ` 1 ) = 1')],
                    '( ( Re ` ( %s / %s ) ) + ( Re ` 1 ) ) = %s' % (V, k, e))])
    red0 = D(w, Ak, 'gt0ne0d', [D(w, Ak, 'breqtrrd', [linarith(w, Ak, [cl.ge0('( %s / %s )' % (x, k))], '0 < %s' % e, closure=cl), re_d], '0 < ( Re ` %s )' % d)], '( Re ` %s ) =/= 0' % d)
    ad0 = w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (d, d)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (d, d))
    dne = w.s([red0, w.s([ad0], 'necon3i', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (d, d))], 'syl', '( %s -> %s =/= 0 )' % (Ak, d))
    cV = '( %s ^c %s )' % (r, V)
    vv = eut_val(w, Ak, V, k, kn)
    vcc = D(w, Ak, 'eqeltrd', [vv, D(w, Ak, 'divcld', [D(w, Ak, 'cxpcld', [cl.mem(r, 'CC'), vc], '%s e. CC' % cV), dc, dne], '%s e. CC' % FACT(k, V))],
            '( %s ` %s ) e. CC' % (LE.EUT(V), k))
    return xrp, vcc


# ---------------------------------------------------------------- zl3gsq
if wante('zl3gsq', MAIN):
    w = W('zl3gsq', 'The partial Gauss products ( ~ gamcvg2 ) at ` Re V ` and at ` V ` : ` P_N ( Re V ) ^ 2 <_ abs ( P_N ( V ) ) ^ 2 e ^ ( 8 K ) ` for ` abs ( Im V ) <_ K ` ( ~ zl3gfc , ~ zl3ppb ).')
    A, Cc = ante_e('zl3gsq')
    hv = D(w, A, 'simpl', [], LE.HVK); nn = D(w, A, 'simpr', [], 'N e. NN')
    vx = D(w, A, 'simpld', [hv], '( V e. CC /\\ 0 <_ ( Re ` V ) )')
    vc = D(w, A, 'simpld', [vx], 'V e. CC'); x0 = D(w, A, 'simprd', [vx], '0 <_ ( Re ` V )')
    kk = D(w, A, 'simprd', [hv], '( K e. NN0 /\\ ( abs ` ( Im ` V ) ) <_ K )'); kn0 = D(w, A, 'simpld', [kk], 'K e. NN0')
    x = '( Re ` V )'
    Ex, EV = LE.EUT(x), LE.EUT('V')
    ax, aV = '( %s ` k )' % Ex, '( %s ` k )' % EV
    Ak = '( %s /\\ k e. ( 1 ... N ) )' % A
    kn = D(w, Ak, 'syl', [w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % Ak), w.inst('elfznn')], 'k e. NN')
    xrp, vcc = fact_facts(w, Ak, kn, ad(w, Ak, vc, 'V e. CC'), ad(w, Ak, x0, '0 <_ %s' % x))
    Az = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A
    knz = D(w, Az, 'sylibr', [w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Az), w.inst('elnnuz')], 'k e. NN')
    _, vccz = fact_facts(w, Az, knz, ad(w, Az, vc, 'V e. CC'), ad(w, Az, x0, '0 <_ %s' % x))
    nuz = D(w, A, 'sylib', [nn, w.inst('elnnuz')], 'N e. ( ZZ>= ` 1 )')
    PR_ = lambda b: 'prod_ k e. ( 1 ... N ) %s' % b
    sx = D(w, A, 'fprodser', [D(w, Ak, 'eqidd', [], '%s = %s' % (ax, ax)), nuz, D(w, Ak, 'rpcnd', [xrp], '%s e. CC' % ax)], '%s = ( %s ` N )' % (PR_(ax), LE.GSQ(x)))
    sV = D(w, A, 'fprodser', [D(w, Ak, 'eqidd', [], '%s = %s' % (aV, aV)), nuz, vcc], '%s = ( %s ` N )' % (PR_(aV), LE.GSQ('V')))
    fin = D(w, A, 'fzfid', [], '( 1 ... N ) e. Fin')
    nfA = w.s([], 'nfv', 'F/ k %s' % A)
    ab = D(w, A, 'fprodabs', [w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )'), nuz, vccz], '( abs ` %s ) = %s' % (PR_(aV), PR_('( abs ` %s )' % aV)))
    # per factor, k-level
    Kt = '( 1 + ( ( K ^ 2 ) / ( k ^ 2 ) ) )'
    gfc = D(w, Ak, 'syl2anc', [ad(w, Ak, hv, LE.HVK), kn, w.inst('zl3gfc')], '( ( %s ^ 2 ) <_ ( ( ( abs ` %s ) ^ 2 ) x. %s ) )' % (ax, aV, Kt) if False else
            '( %s ^ 2 ) <_ ( ( ( abs ` %s ) ^ 2 ) x. %s )' % (ax, aV, Kt))
    clk = Closure(w, Ak, {'k': ('NN', kn), 'K': ('NN0', ad(w, Ak, kn0, 'K e. NN0')), ax: ('RR+', xrp), aV: ('CC', vcc)})
    lhs_r, lhs_0 = clk.mem('( %s ^ 2 )' % ax, 'RR'), clk.ge0('( %s ^ 2 )' % ax)
    rhs_r = clk.mem('( ( ( abs ` %s ) ^ 2 ) x. %s )' % (aV, Kt), 'RR')
    p1 = D(w, A, 'fprodle', [nfA, fin, lhs_r, lhs_0, rhs_r, gfc], '%s <_ %s' % (PR_('( %s ^ 2 )' % ax), PR_('( ( ( abs ` %s ) ^ 2 ) x. %s )' % (aV, Kt))))
    # rewrite both sides
    def sq_prod(a_, acc, full):
        """( A -> prod ( a ^ 2 ) = ( prod a ) ^ 2 )"""
        e1 = D(w, A, 'prodeq2dv', [D(w, Ak, 'sqvald', [acc], '( %s ^ 2 ) = ( %s x. %s )' % (a_, a_, a_))], '%s = %s' % (PR_('( %s ^ 2 )' % a_), PR_('( %s x. %s )' % (a_, a_))))
        e2 = D(w, A, 'fprodmul', [fin, acc, acc], '%s = ( %s x. %s )' % (PR_('( %s x. %s )' % (a_, a_)), PR_(a_), PR_(a_)))
        e3 = D(w, A, 'sqvald', [full], '( %s ^ 2 ) = ( %s x. %s )' % (PR_(a_), PR_(a_), PR_(a_)))
        return D(w, A, 'eqtr4d', [D(w, A, 'eqtrd', [e1, e2], '%s = ( %s x. %s )' % (PR_('( %s ^ 2 )' % a_), PR_(a_), PR_(a_))), e3], '%s = ( %s ^ 2 )' % (PR_('( %s ^ 2 )' % a_), PR_(a_)))
    axc = D(w, Ak, 'rpcnd', [xrp], '%s e. CC' % ax)
    L1 = sq_prod(ax, axc, D(w, A, 'fprodcl', [fin, axc], '%s e. CC' % PR_(ax)))
    aa = '( abs ` %s )' % aV
    aac = clk.mem(aa, 'CC')
    L2 = sq_prod(aa, aac, D(w, A, 'fprodcl', [fin, aac], '%s e. CC' % PR_(aa)))
    split = D(w, A, 'fprodmul', [fin, clk.mem('( %s ^ 2 )' % aa, 'CC'), clk.mem(Kt, 'CC')], '%s = ( %s x. %s )' % (PR_('( ( %s ^ 2 ) x. %s )' % (aa, Kt)), PR_('( %s ^ 2 )' % aa), PR_(Kt)))
    Km = '( 1 + ( ( K ^ 2 ) / ( m ^ 2 ) ) )'
    cbv = w.s([w.s([w.s([w.s([], 'oveq1', '( k = m -> ( k ^ 2 ) = ( m ^ 2 ) )')], 'oveq2d', '( k = m -> ( ( K ^ 2 ) / ( k ^ 2 ) ) = ( ( K ^ 2 ) / ( m ^ 2 ) ) )')], 'oveq2d',
                     '( k = m -> %s = %s )' % (Kt, Km))], 'cbvprodv', '%s = prod_ m e. ( 1 ... N ) %s' % (PR_(Kt), Km))
    ppb = D(w, A, 'syl2anc', [kn0, nn, w.inst('zl3ppb')], 'prod_ m e. ( 1 ... N ) %s <_ ( exp ` ( 8 x. K ) )' % Km)
    pk = D(w, A, 'eqbrtrd', [w.s([cbv], 'a1i', '( %s -> %s = prod_ m e. ( 1 ... N ) %s )' % (A, PR_(Kt), Km)), ppb], '%s <_ ( exp ` ( 8 x. K ) )' % PR_(Kt))
    PA2 = PR_('( %s ^ 2 )' % aa)
    pa2r = D(w, A, 'fprodrecl', [fin, clk.mem('( %s ^ 2 )' % aa, 'RR')], '%s e. RR' % PA2)
    pa20 = D(w, A, 'fprodge0', [nfA, fin, clk.mem('( %s ^ 2 )' % aa, 'RR'), clk.ge0('( %s ^ 2 )' % aa)], '0 <_ %s' % PA2)
    pkr = D(w, A, 'fprodrecl', [fin, clk.mem(Kt, 'RR')], '%s e. RR' % PR_(Kt))
    e8 = D(w, A, 'reefcld', [D(w, A, 'remulcld', [cst(w, A, '8re', '8 e. RR'), D(w, A, 'nn0red', [kn0], 'K e. RR')], '( 8 x. K ) e. RR')], '( exp ` ( 8 x. K ) ) e. RR')
    p2 = D(w, A, 'lemul2ad', [pkr, e8, pa2r, pa20, pk], '( %s x. %s ) <_ ( %s x. ( exp ` ( 8 x. K ) ) )' % (PA2, PR_(Kt), PA2))
    chainr = D(w, A, 'letrd', [D(w, A, 'fprodrecl', [fin, lhs_r], '%s e. RR' % PR_('( %s ^ 2 )' % ax)),
                               D(w, A, 'remulcld', [pa2r, pkr], '( %s x. %s ) e. RR' % (PA2, PR_(Kt))),
                               D(w, A, 'remulcld', [pa2r, e8], '( %s x. ( exp ` ( 8 x. K ) ) ) e. RR' % PA2),
                               D(w, A, 'breqtrd', [p1, split], '%s <_ ( %s x. %s )' % (PR_('( %s ^ 2 )' % ax), PA2, PR_(Kt))), p2],
             '%s <_ ( %s x. ( exp ` ( 8 x. K ) ) )' % (PR_('( %s ^ 2 )' % ax), PA2))
    # convert to the seq forms
    lhs_eq = D(w, A, 'eqtrd', [L1, D(w, A, 'oveq1d', [sx], '( %s ^ 2 ) = ( ( %s ` N ) ^ 2 )' % (PR_(ax), LE.GSQ(x)))], '%s = ( ( %s ` N ) ^ 2 )' % (PR_('( %s ^ 2 )' % ax), LE.GSQ(x)))
    absq = D(w, A, 'eqtr3d', [D(w, A, 'fveq2d', [sV], '( abs ` %s ) = ( abs ` ( %s ` N ) )' % (PR_(aV), LE.GSQ('V'))), ab], '( abs ` ( %s ` N ) ) = %s' % (LE.GSQ('V'), PR_(aa)))
    rhs_eq = D(w, A, 'eqtrd', [L2, D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [absq], '%s = ( abs ` ( %s ` N ) )' % (PR_(aa), LE.GSQ('V')))],
                                                     '( %s ^ 2 ) = ( ( abs ` ( %s ` N ) ) ^ 2 )' % (PR_(aa), LE.GSQ('V')))], '%s = ( ( abs ` ( %s ` N ) ) ^ 2 )' % (PA2, LE.GSQ('V')))
    fin_ = D(w, A, 'breqtrd', [D(w, A, 'eqbrtrrd', [lhs_eq, chainr], '( ( %s ` N ) ^ 2 ) <_ ( %s x. ( exp ` ( 8 x. K ) ) )' % (LE.GSQ(x), PA2)),
                               D(w, A, 'oveq1d', [rhs_eq], '( %s x. ( exp ` ( 8 x. K ) ) ) = ( ( ( abs ` ( %s ` N ) ) ^ 2 ) x. ( exp ` ( 8 x. K ) ) )' % (PA2, LE.GSQ('V')))], Cc)
    w.qed([fin_], 'idi', SE['zl3gsq'])
    goe(w)


# ---------------------------------------------------------------- zl3glb
if wante('zl3glb', MAIN):
    w = W('zl3glb', 'Lower bound of ` abs Gamma ` on vertical lines: ` Gamma ( Re V ) Re V <_ e ^ ( 4 K ) abs ( Gamma ( V ) V ) ` for ` abs ( Im V ) <_ K ` , the limit of ~ zl3gsq through ~ gamcvg2 .')
    A, Cc = ante_e('zl3glb')
    vx = D(w, A, 'simpl', [], '( V e. CC /\\ 0 < ( Re ` V ) )'); vc = D(w, A, 'simpld', [vx], 'V e. CC'); xg0 = D(w, A, 'simprd', [vx], '0 < ( Re ` V )')
    kk = D(w, A, 'simpr', [], '( K e. NN0 /\\ ( abs ` ( Im ` V ) ) <_ K )'); kn0 = D(w, A, 'simpld', [kk], 'K e. NN0')
    x = '( Re ` V )'
    xr = D(w, A, 'recld', [vc], '%s e. RR' % x); x0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), xr, xg0], '0 <_ %s' % x)
    xrp = D(w, A, 'elrpd', [xr, xg0], '%s e. RR+' % x)
    hvk = D(w, A, 'jca', [D(w, A, 'jca', [vc, x0], '( V e. CC /\\ 0 <_ %s )' % x), kk], LE.HVK)
    Sx, SV = LE.GSQ(x), LE.GSQ('V')
    cvx = D(w, A, 'gamcvg2', [w.s([], 'eqid', '%s = %s' % (LE.EUT(x), LE.EUT(x))), D(w, A, 'syl', [xrp, w.inst('rpdmgm')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % x)],
            '%s ~~> ( ( _G ` %s ) x. %s )' % (Sx, x, x))
    cvV = D(w, A, 'gamcvg2', [w.s([], 'eqid', '%s = %s' % (LE.EUT('V'), LE.EUT('V'))), D(w, A, 'syl2anc', [vc, xg0, w.inst('zrenn')], 'V e. ( CC \\ ( ZZ \\ NN ) )')],
            '%s ~~> ( ( _G ` V ) x. V )' % SV)
    E4 = '( exp ` ( 4 x. K ) )'
    GA = '( n e. NN |-> ( abs ` ( %s ` n ) ) )' % SV
    GB = '( n e. NN |-> ( %s x. ( abs ` ( %s ` n ) ) ) )' % (E4, SV)
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = cst(w, A, '1zzd', '1 e. ZZ') if False else D(w, A, '1zzd', [], '1 e. ZZ')
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    # seq values at k, via fprodser with the product index j
    Akj = '( %s /\\ j e. ( 1 ... k ) )' % Ak
    jn = D(w, Akj, 'syl', [w.s([], 'simpr', '( %s -> j e. ( 1 ... k ) )' % Akj), w.inst('elfznn')], 'j e. NN')
    xrpj, vccj = fact_facts(w, Akj, jn, ad(w, Akj, ad(w, Ak, vc, 'V e. CC'), 'V e. CC'), ad(w, Akj, ad(w, Ak, x0, '0 <_ %s' % x), '0 <_ %s' % x), k='j')
    kuz = D(w, Ak, 'sylib', [kn, w.inst('elnnuz')], 'k e. ( ZZ>= ` 1 )')
    ajx, ajV = '( %s ` j )' % LE.EUT(x), '( %s ` j )' % LE.EUT('V')
    PJ = lambda b: 'prod_ j e. ( 1 ... k ) %s' % b
    sxk = D(w, Ak, 'fprodser', [D(w, Akj, 'eqidd', [], '%s = %s' % (ajx, ajx)), kuz, D(w, Akj, 'rpcnd', [xrpj], '%s e. CC' % ajx)], '%s = ( %s ` k )' % (PJ(ajx), Sx))
    sVk = D(w, Ak, 'fprodser', [D(w, Akj, 'eqidd', [], '%s = %s' % (ajV, ajV)), kuz, vccj], '%s = ( %s ` k )' % (PJ(ajV), SV))
    finj = D(w, Ak, 'fzfid', [], '( 1 ... k ) e. Fin')
    sxrp = D(w, Ak, 'eqeltrrd', [sxk, D(w, Ak, 'fprodrpcl', [finj, xrpj], '%s e. RR+' % PJ(ajx))], '( %s ` k ) e. RR+' % Sx)
    sVc = D(w, Ak, 'eqeltrrd', [sVk, D(w, Ak, 'fprodcl', [finj, vccj], '%s e. CC' % PJ(ajV))], '( %s ` k ) e. CC' % SV)
    ga_v = fv1(w, Ak, 'n', 'NN', lambda v: '( abs ` ( %s ` %s ) )' % (SV, v), 'k', kn, 'fvex')
    gb_v = fv1(w, Ak, 'n', 'NN', lambda v: '( %s x. ( abs ` ( %s ` %s ) ) )' % (E4, SV, v), 'k', kn, 'ovex')
    ga_e = D(w, Ak, 'eqtrd', [gb_v, D(w, Ak, 'oveq2d', [D(w, Ak, 'eqcomd', [ga_v], '( abs ` ( %s ` k ) ) = ( %s ` k )' % (SV, GA))],
                                                         '( %s x. ( abs ` ( %s ` k ) ) ) = ( %s x. ( %s ` k ) )' % (E4, SV, E4, GA))], '( %s ` k ) = ( %s x. ( %s ` k ) )' % (GB, E4, GA))
    cA = D(w, A, 'climabs', [nnz, cvV, D(w, A, 'mptexd', [], '%s e. _V' % GA) if False else cst(w, A, 'nnex', 'NN e. _V') and
                             D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % GA), one, sVc, ga_v], '%s ~~> ( abs ` ( ( _G ` V ) x. V ) )' % GA)
    k4r = D(w, A, 'remulcld', [cst(w, A, '4re', '4 e. RR'), D(w, A, 'nn0red', [kn0], 'K e. RR')], '( 4 x. K ) e. RR')
    e4r = D(w, A, 'reefcld', [k4r], '%s e. RR' % E4)
    gak = D(w, Ak, 'eqeltrd', [ga_v, D(w, Ak, 'abscld', [sVc], '( abs ` ( %s ` k ) ) e. RR' % SV)], '( %s ` k ) e. RR' % GA)
    cB = D(w, A, 'climmulc2', [nnz, one, cA, D(w, A, 'recnd', [e4r], '%s e. CC' % E4), D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % GB),
                               D(w, Ak, 'recnd', [gak], '( %s ` k ) e. CC' % GA), ga_e], '%s ~~> ( %s x. ( abs ` ( ( _G ` V ) x. V ) ) )' % (GB, E4))
    # the per-k bound
    sx, sv = '( %s ` k )' % Sx, '( abs ` ( %s ` k ) )' % SV
    gsq = D(w, Ak, 'syl2anc', [ad(w, Ak, hvk, LE.HVK), kn, w.inst('zl3gsq')], '( %s ^ 2 ) <_ ( ( %s ^ 2 ) x. ( exp ` ( 8 x. K ) ) )' % (sx, sv))
    svr = D(w, Ak, 'abscld', [sVc], '%s e. RR' % sv); sv0 = D(w, Ak, 'absge0d', [sVc], '0 <_ %s' % sv)
    e4k, k4k = ad(w, Ak, e4r, '%s e. RR' % E4), ad(w, Ak, k4r, '( 4 x. K ) e. RR')
    e40 = D(w, Ak, 'efge0d', [k4k], '0 <_ %s' % E4) if False else D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), e4k, D(w, Ak, 'syl', [k4k, w.inst('efgt0')], '0 < %s' % E4)], '0 <_ %s' % E4)
    rhs = '( %s x. %s )' % (E4, sv)
    rr = D(w, Ak, 'remulcld', [e4k, svr], '%s e. RR' % rhs); r0 = D(w, Ak, 'mulge0d', [e4k, svr, e40, sv0], '0 <_ %s' % rhs)
    e4c = D(w, Ak, 'recnd', [e4k], '%s e. CC' % E4)
    e8 = chain(w, Ak, ['( %s ^ 2 )' % E4, '( %s x. %s )' % (E4, E4), '( exp ` ( ( 4 x. K ) + ( 4 x. K ) ) )', '( exp ` ( 8 x. K ) )'],
               [D(w, Ak, 'sqvald', [e4c], '( %s ^ 2 ) = ( %s x. %s )' % (E4, E4, E4)),
                ('r', efadd_(w, Ak, '( 4 x. K )', '( 4 x. K )', D(w, Ak, 'recnd', [k4k], '( 4 x. K ) e. CC'), D(w, Ak, 'recnd', [k4k], '( 4 x. K ) e. CC'))),
                D(w, Ak, 'fveq2d', [lineq(w, Ak, '( ( 4 x. K ) + ( 4 x. K ) )', '( 8 x. K )', leaves={'K': ('RR', ad(w, Ak, D(w, A, 'nn0red', [kn0], 'K e. RR'), 'K e. RR'))})],
                  '( exp ` ( ( 4 x. K ) + ( 4 x. K ) ) ) = ( exp ` ( 8 x. K ) )')])
    rsq = chain(w, Ak, ['( %s ^ 2 )' % rhs, '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (E4, sv), '( ( exp ` ( 8 x. K ) ) x. ( %s ^ 2 ) )' % sv, '( ( %s ^ 2 ) x. ( exp ` ( 8 x. K ) ) )' % sv],
                [D(w, Ak, 'sqmuld', [e4c, D(w, Ak, 'recnd', [svr], '%s e. CC' % sv)], '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (rhs, E4, sv)),
                 D(w, Ak, 'oveq1d', [e8], '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) = ( ( exp ` ( 8 x. K ) ) x. ( %s ^ 2 ) )' % (E4, sv, sv)),
                 D(w, Ak, 'mulcomd', [D(w, Ak, 'recnd', [D(w, Ak, 'reefcld', [D(w, Ak, 'remulcld', [cst(w, Ak, '8re', '8 e. RR'), ad(w, Ak, D(w, A, 'nn0red', [kn0], 'K e. RR'), 'K e. RR')], '( 8 x. K ) e. RR')], '( exp ` ( 8 x. K ) ) e. RR')], '( exp ` ( 8 x. K ) ) e. CC'),
                                      D(w, Ak, 'recnd', [D(w, Ak, 'resqcld', [svr], '( %s ^ 2 ) e. RR' % sv)], '( %s ^ 2 ) e. CC' % sv)],
                   '( ( exp ` ( 8 x. K ) ) x. ( %s ^ 2 ) ) = ( ( %s ^ 2 ) x. ( exp ` ( 8 x. K ) ) )' % (sv, sv))])
    sxr = D(w, Ak, 'rpred', [sxrp], '%s e. RR' % sx); sx0 = D(w, Ak, 'rpge0d', [sxrp], '0 <_ %s' % sx)
    le2 = D(w, Ak, 'syl2anc', [D(w, Ak, 'jca', [sxr, sx0], '( %s e. RR /\\ 0 <_ %s )' % (sx, sx)), D(w, Ak, 'jca', [rr, r0], '( %s e. RR /\\ 0 <_ %s )' % (rhs, rhs)), w.inst('le2sq')],
            '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (sx, rhs, sx, rhs))
    pk = D(w, Ak, 'mpbird', [D(w, Ak, 'breqtrrd', [gsq, rsq], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (sx, rhs)), le2], '%s <_ %s' % (sx, rhs))
    gbk = D(w, Ak, 'eqtr4d', [gb_v, D(w, Ak, 'eqidd', [], '%s = %s' % (rhs, rhs))], '( %s ` k ) = %s' % (GB, rhs)) if False else gb_v
    pk2 = D(w, Ak, 'breqtrrd', [pk, gbk], '%s <_ ( %s ` k )' % (sx, GB))
    fin = D(w, A, 'climle', [nnz, one, cvx, cB, sxr, D(w, Ak, 'eqeltrd', [gbk, rr], '( %s ` k ) e. RR' % GB), pk2], Cc)
    w.qed([fin], 'idi', SE['zl3glb'])
    goe(w)


# ---------------------------------------------------------------- zl3igb
if wante('zl3igb', MAIN):
    w = W('zl3igb', 'Exponential bound on ` 1 / Gamma ` on the strip ` 3 / 4 <_ Re u <_ 5 / 2 ` : ` 1 / abs Gamma ( u ) <_ c e ^ ( 5 abs Im u ) ` ( ~ zl3glb at ` K = |_ abs Im u + 1 ` , ~ zl3grat ).')
    HUN = '( 1 / ; ; 1 0 0 )'
    IV = '( %s [,] 3 )' % HUN
    GRAT = 'A. p e. %s A. q e. %s ( _G ` p ) <_ ( d x. ( _G ` q ) )' % (IV, IV)
    E5 = '( exp ` ( 5 x. ( abs ` ( Im ` u ) ) ) )'
    c = '( ( ; 1 0 / 3 ) x. ( d x. ( exp ` 4 ) ) )'
    BODY = lambda cc: 'A. u e. CC ( ( ( 3 / 4 ) <_ ( Re ` u ) /\\ ( Re ` u ) <_ ( 5 / 2 ) ) -> ( ( _G ` u ) =/= 0 /\\ ( 1 / ( abs ` ( _G ` u ) ) ) <_ ( %s x. ( exp ` ( 5 x. ( abs ` ( Im ` u ) ) ) ) ) ) )' % cc
    Ad = '( d e. RR+ /\\ %s )' % GRAT
    drp = w.s([], 'simpl', '( %s -> d e. RR+ )' % Ad); grat = w.s([], 'simpr', '( %s -> %s )' % (Ad, GRAT))
    Au = '( %s /\\ u e. CC )' % Ad
    Ar = '( %s /\\ ( ( 3 / 4 ) <_ ( Re ` u ) /\\ ( Re ` u ) <_ ( 5 / 2 ) ) )' % Au
    uc = D(w, Ar, 'simplr', [], 'u e. CC')
    x, y = '( Re ` u )', '( Im ` u )'
    lo = D(w, Ar, 'simprl', [], '( 3 / 4 ) <_ %s' % x); hi = D(w, Ar, 'simprr', [], '%s <_ ( 5 / 2 )' % x)
    dr = D(w, Ar, 'rpred', [ad(w, Ar, ad(w, Au, drp, 'd e. RR+'), 'd e. RR+')], 'd e. RR')
    drpA = ad(w, Ar, ad(w, Au, drp, 'd e. RR+'), 'd e. RR+')
    xr = D(w, Ar, 'recld', [uc], '%s e. RR' % x); yr = D(w, Ar, 'imcld', [uc], '%s e. RR' % y)
    ay = '( abs ` %s )' % y
    ayr = D(w, Ar, 'abscld', [D(w, Ar, 'recnd', [yr], '%s e. CC' % y)], '%s e. RR' % ay); ay0 = D(w, Ar, 'absge0d', [D(w, Ar, 'recnd', [yr], '%s e. CC' % y)], '0 <_ %s' % ay)
    cl = Closure(w, Ar, {x: ('RR', xr), ay: [('RR', ayr), ('ge0', ay0)], 'd': [('RR+', drpA)]})
    xg0 = linarith(w, Ar, [lo], '0 < %s' % x, closure=cl)
    xrp = D(w, Ar, 'elrpd', [xr, xg0], '%s e. RR+' % x)
    udm = D(w, Ar, 'syl2anc', [uc, xg0, w.inst('zrenn')], 'u e. ( CC \\ ( ZZ \\ NN ) )')
    gne = D(w, Ar, 'syl', [udm, w.inst('gamne0')], '( _G ` u ) =/= 0')
    gc = D(w, Ar, 'syl', [udm, w.inst('gamcl')], '( _G ` u ) e. CC')
    # K
    Fl = '( |_ ` %s )' % ay
    K = '( %s + 1 )' % Fl
    fln = D(w, Ar, 'syl2anc', [ayr, ay0, w.inst('flge0nn0')], '%s e. NN0' % Fl)
    kn0 = D(w, Ar, 'peano2nn0d', [fln], '%s e. NN0' % K) if False else D(w, Ar, 'syl', [fln, w.inst('peano2nn0')], '%s e. NN0' % K)
    ylt = D(w, Ar, 'syl', [ayr, w.inst('flltp1')], '%s < %s' % (ay, K))
    fle = D(w, Ar, 'syl', [ayr, w.inst('flle')], '%s <_ %s' % (Fl, ay))
    kr = D(w, Ar, 'nn0red', [kn0], '%s e. RR' % K)
    glb = D(w, Ar, 'syl2anc', [D(w, Ar, 'jca', [uc, xg0], '( u e. CC /\\ 0 < %s )' % x),
                               D(w, Ar, 'jca', [kn0, D(w, Ar, 'ltled', [ayr, kr, ylt], '%s <_ %s' % (ay, K))], '( %s e. NN0 /\\ %s <_ %s )' % (K, ay, K)), w.inst('zl3glb')],
            '( ( _G ` %s ) x. %s ) <_ ( ( exp ` ( 4 x. %s ) ) x. ( abs ` ( ( _G ` u ) x. u ) ) )' % (x, x, K))
    # Gamma ( x ) >_ 1 / d via zl3grat at p = 1 , q = x
    Gx = '( _G ` %s )' % x
    subp = w.s([w.s([w.s([], 'fveq2', '( p = 1 -> ( _G ` p ) = ( _G ` 1 ) )')], 'breq1d', '( p = 1 -> ( ( _G ` p ) <_ ( d x. ( _G ` q ) ) <-> ( _G ` 1 ) <_ ( d x. ( _G ` q ) ) ) )')], 'idi',
               '( p = 1 -> ( ( _G ` p ) <_ ( d x. ( _G ` q ) ) <-> ( _G ` 1 ) <_ ( d x. ( _G ` q ) ) ) )')
    subq = w.s([w.s([w.s([], 'fveq2', '( q = %s -> ( _G ` q ) = %s )' % (x, Gx))], 'oveq2d', '( q = %s -> ( d x. ( _G ` q ) ) = ( d x. %s ) )' % (x, Gx))], 'breq2d',
               '( q = %s -> ( ( _G ` 1 ) <_ ( d x. ( _G ` q ) ) <-> ( _G ` 1 ) <_ ( d x. %s ) ) )' % (x, Gx))
    hun = cl.mem(HUN, 'RR')
    iv_mem = lambda X, xrr, l, h: D(w, Ar, 'mpbir3and' if False else 'syl3anbrc', [xrr, l, h, D(w, Ar, 'syl2anc', [hun, cst(w, Ar, '3re', '3 e. RR'), w.inst('elicc2')],
                                                                                            '( %s e. %s <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ 3 ) )' % (X, IV, X, HUN, X, X))], '%s e. %s' % (X, IV)) if False else \
        D(w, Ar, 'mpbir3and', [D(w, Ar, 'syl2anc', [hun, cst(w, Ar, '3re', '3 e. RR'), w.inst('elicc2')], '( %s e. %s <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ 3 ) )' % (X, IV, X, HUN, X, X)), xrr, l, h],
          '%s e. %s' % (X, IV))
    one_iv = iv_mem('1', cl.mem('1', 'RR'), num_(w, Ar, '1', 'RR') and Closure(w, Ar, {}).mem('1', 'RR') and linarith(w, Ar, [], '%s <_ 1' % HUN, closure=cl), linarith(w, Ar, [], '1 <_ 3', closure=cl))
    x_iv = iv_mem(x, xr, linarith(w, Ar, [lo], '%s <_ %s' % (HUN, x), closure=cl), linarith(w, Ar, [hi], '%s <_ 3' % x, closure=cl))
    g1 = D(w, Ar, 'mpd', [ad(w, Ar, ad(w, Au, grat, GRAT), GRAT), D(w, Ar, 'syl2anc', [one_iv, x_iv, w.s([subp, subq], 'rspc2v', '( ( 1 e. %s /\\ %s e. %s ) -> ( %s -> ( _G ` 1 ) <_ ( d x. %s ) ) )' % (IV, x, IV, GRAT, Gx))],
                                                                          '( %s -> ( _G ` 1 ) <_ ( d x. %s ) )' % (GRAT, Gx))], '( _G ` 1 ) <_ ( d x. %s )' % Gx)
    g1b = D(w, Ar, 'eqbrtrrd', [cst(w, Ar, 'gam1', '( _G ` 1 ) = 1'), g1], '1 <_ ( d x. %s )' % Gx)
    gxrp = D(w, Ar, 'syl', [xrp, w.inst('rpgamcl')], '%s e. RR+' % Gx)
    Gm = '( %s x. %s )' % (Gx, x)
    cl.leaf(Gx, 'RR+', gxrp)
    # 3 / 4 <_ d G
    s3 = D(w, Ar, 'lemul12ad', [cl.mem('( 3 / 4 )', 'RR'), xr, cl.mem('1', 'RR'), cl.mem('( d x. %s )' % Gx, 'RR'), cl.ge0('( 3 / 4 )'), cl.ge0('1'), lo, g1b],
           '( ( 3 / 4 ) x. 1 ) <_ ( %s x. ( d x. %s ) )' % (x, Gx))
    E4 = '( exp ` ( 4 x. %s ) )' % K
    gu, au = '( abs ` ( _G ` u ) )', '( abs ` u )'
    une = D(w, Ar, 'syl', [udm, w.inst('dmgmn0')], 'u =/= 0') if False else None
    ure0 = D(w, Ar, 'gt0ne0d', [xg0], '%s =/= 0' % x)
    ad0 = w.s([w.s([], 'fveq2', '( u = 0 -> ( Re ` u ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( u = 0 -> ( Re ` u ) = 0 )')
    une = w.s([ure0, w.s([ad0], 'necon3i', '( ( Re ` u ) =/= 0 -> u =/= 0 )')], 'syl', '( %s -> u =/= 0 )' % Ar)
    gur = D(w, Ar, 'abscld', [gc], '%s e. RR' % gu); aur = D(w, Ar, 'abscld', [uc], '%s e. RR' % au)
    gup = D(w, Ar, 'mpbid', [gne, D(w, Ar, 'syl', [gc, w.inst('absgt0')], '( ( _G ` u ) =/= 0 <-> 0 < %s )' % gu)], '0 < %s' % gu)
    aup = D(w, Ar, 'mpbid', [une, D(w, Ar, 'syl', [uc, w.inst('absgt0')], '( u =/= 0 <-> 0 < %s )' % au)], '0 < %s' % au)
    cl.leaf(gu, 'RR+', D(w, Ar, 'elrpd', [gur, gup], '%s e. RR+' % gu)); cl.leaf(au, 'RR+', D(w, Ar, 'elrpd', [aur, aup], '%s e. RR+' % au))
    cl.have(Fl, 'NN0', fln)
    am = D(w, Ar, 'absmuld', [gc, uc], '( abs ` ( ( _G ` u ) x. u ) ) = ( %s x. %s )' % (gu, au))
    s4 = D(w, Ar, 'breqtrd', [glb, D(w, Ar, 'oveq2d', [am], '( %s x. ( abs ` ( ( _G ` u ) x. u ) ) ) = ( %s x. ( %s x. %s ) )' % (E4, E4, gu, au))],
           '%s <_ ( %s x. ( %s x. %s ) )' % (Gm, E4, gu, au))
    # E4 <_ e ^ 4 e ^ ( 4 | y | )
    k4 = linarith(w, Ar, [fle], '( 4 x. %s ) <_ ( 4 + ( 4 x. %s ) )' % (K, ay), closure=cl)
    e4le = efle_(w, Ar, '( 4 x. %s )' % K, '( 4 + ( 4 x. %s ) )' % ay, cl.mem('( 4 x. %s )' % K, 'RR'), cl.mem('( 4 + ( 4 x. %s ) )' % ay, 'RR'), k4)
    EY4 = '( exp ` ( 4 x. %s ) )' % ay
    e4s = D(w, Ar, 'breqtrd', [e4le, efadd_(w, Ar, '4', '( 4 x. %s )' % ay, cl.mem('4', 'CC'), cl.mem('( 4 x. %s )' % ay, 'CC'))], '%s <_ ( ( exp ` 4 ) x. %s )' % (E4, EY4))
    # | u | <_ ( 5 / 2 ) e ^ | y |
    EY = '( exp ` %s )' % ay
    ax_ = '( abs ` %s )' % x
    ari = D(w, Ar, 'syl', [uc, w.inst('absreimle')], '%s <_ ( %s + %s )' % (au, ax_, ay))
    axe = D(w, Ar, 'syl', [xr, w.inst('absidm')], '') if False else D(w, Ar, 'syl2anc', [xr, D(w, Ar, 'ltled', [cst(w, Ar, '0re', '0 e. RR'), xr, xg0], '0 <_ %s' % x), w.inst('absidd')], '') if False else \
        D(w, Ar, 'absidd', [xr, D(w, Ar, 'ltled', [cst(w, Ar, '0re', '0 e. RR'), xr, xg0], '0 <_ %s' % x)], '%s = %s' % (ax_, x))
    bv = D(w, Ar, 'syl2anc', [ayr, ay0, w.inst('bvefge1p')], '( 1 + %s ) <_ %s' % (ay, EY))
    cl.leaf(EY, 'RR+', D(w, Ar, 'rpefcld', [ayr], '%s e. RR+' % EY))
    aule = linarith(w, Ar, [ari, D(w, Ar, 'eqcomd', [axe], '%s = %s' % (x, ax_)) and D(w, Ar, 'eqle', [], '') if False else ari, hi, bv, cl.ge0(ay)],
                    '%s <_ ( ( 5 / 2 ) x. %s )' % (au, EY), closure=cl, atoms=[au, ay, EY, x]) if False else None
    ax_le = D(w, Ar, 'eqbrtrd', [axe, hi], '%s <_ ( 5 / 2 )' % ax_)
    aule = linarith(w, Ar, [ari, ax_le, bv, ay0], '%s <_ ( ( 5 / 2 ) x. %s )' % (au, EY), closure=cl, atoms=[au, ay, EY, ax_])
    # d ( E4 ( gu au ) ) <_ d ( ( e4 EY4 ) ( gu ( 5/2 EY ) ) )
    P1 = '( %s x. ( %s x. %s ) )' % (E4, gu, au)
    P2 = '( ( ( exp ` 4 ) x. %s ) x. ( %s x. ( ( 5 / 2 ) x. %s ) ) )' % (EY4, gu, EY)
    cl.leaf(E4, 'RR+', D(w, Ar, 'rpefcld', [cl.mem('( 4 x. %s )' % K, 'RR')], '%s e. RR+' % E4))
    cl.leaf(EY4, 'RR+', D(w, Ar, 'rpefcld', [cl.mem('( 4 x. %s )' % ay, 'RR')], '%s e. RR+' % EY4))
    cl.leaf('( exp ` 4 )', 'RR+', D(w, Ar, 'rpefcld', [cl.mem('4', 'RR')], '( exp ` 4 ) e. RR+'))
    in1 = D(w, Ar, 'lemul2ad', [aur, cl.mem('( ( 5 / 2 ) x. %s )' % EY, 'RR'), cl.mem(gu, 'RR'), cl.ge0(gu), aule], '( %s x. %s ) <_ ( %s x. ( ( 5 / 2 ) x. %s ) )' % (gu, au, gu, EY))
    in2 = D(w, Ar, 'lemul12ad', [cl.mem(E4, 'RR'), cl.mem('( ( exp ` 4 ) x. %s )' % EY4, 'RR'), cl.mem('( %s x. %s )' % (gu, au), 'RR'), cl.mem('( %s x. ( ( 5 / 2 ) x. %s ) )' % (gu, EY), 'RR'),
                                 cl.ge0(E4), cl.ge0('( %s x. %s )' % (gu, au)), e4s, in1], '%s <_ %s' % (P1, P2))
    s5 = D(w, Ar, 'lemul2ad', [cl.mem(Gm, 'RR'), cl.mem(P1, 'RR'), dr, cl.ge0('d'), s4], '( d x. %s ) <_ ( d x. %s )' % (Gm, P1))
    s6 = D(w, Ar, 'lemul2ad', [cl.mem(P1, 'RR'), cl.mem(P2, 'RR'), dr, cl.ge0('d'), in2], '( d x. %s ) <_ ( d x. %s )' % (P1, P2))
    E5y = '( exp ` ( 5 x. %s ) )' % ay
    e5 = D(w, Ar, 'eqtr3d', [efadd_(w, Ar, '( 4 x. %s )' % ay, ay, cl.mem('( 4 x. %s )' % ay, 'CC'), cl.mem(ay, 'CC')),
                             D(w, Ar, 'fveq2d', [lineq(w, Ar, '( ( 4 x. %s ) + %s )' % (ay, ay), '( 5 x. %s )' % ay, closure=cl)], '( exp ` ( ( 4 x. %s ) + %s ) ) = %s' % (ay, ay, E5y))],
           '( %s x. %s ) = %s' % (EY4, EY, E5y))
    cc_ = '( 4 x. ( d x. ( exp ` 4 ) ) )'
    R = '( %s x. %s )' % (cc_, E5y)
    goal2 = '1 <_ ( %s x. ( %s x. ( %s x. %s ) ) )' % (gu, cc_, EY4, EY)
    import lin as _lin
    _lin.MAXDEG = 6
    lin2 = nlinarith(w, Ar, [s3, s5, s6], goal2, closure=cl, atoms=[Gx, x, gu, au, E4, EY4, EY, '( exp ` 4 )', 'd'], fast=False)
    g3 = D(w, Ar, 'breqtrd', [lin2, D(w, Ar, 'oveq2d', [D(w, Ar, 'oveq2d', [e5], '( %s x. ( %s x. %s ) ) = %s' % (cc_, EY4, EY, R))],
                                                        '( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. %s )' % (gu, cc_, EY4, EY, gu, R))], '1 <_ ( %s x. %s )' % (gu, R))
    rr = cl.mem(R, 'RR')
    last = D(w, Ar, 'mpbird', [g3, D(w, Ar, 'ledivmuld', [cl.mem('1', 'RR'), rr, cl.mem(gu, 'RR+')], '( ( 1 / %s ) <_ %s <-> 1 <_ ( %s x. %s ) )' % (gu, R, gu, R))], '( 1 / %s ) <_ %s' % (gu, R))
    both = D(w, Ar, 'jca', [gne, last], '( ( _G ` u ) =/= 0 /\\ ( 1 / %s ) <_ %s )' % (gu, R))
    imp = D(w, Au, 'ex', [both], '( ( ( 3 / 4 ) <_ %s /\\ %s <_ ( 5 / 2 ) ) -> ( ( _G ` u ) =/= 0 /\\ ( 1 / %s ) <_ %s ) )' % (x, x, gu, R))
    ral = D(w, Ad, 'ralrimiva', [imp], BODY(cc_))
    crp = Closure(w, Ad, {'d': ('RR+', drp)}).mem(cc_, 'RR+')
    sub_c = w.s([], 'oveq1', '( c = %s -> ( c x. %s ) = ( %s x. %s ) )' % (cc_, '( exp ` ( 5 x. ( abs ` ( Im ` u ) ) ) )', cc_, '( exp ` ( 5 x. ( abs ` ( Im ` u ) ) ) )'))
    sb, new = w.wcongr(BODY('c'), {}, 'c = %s' % cc_, {}, rules={'c': (cc_, w.s([], 'id', '( c = %s -> c = %s )' % (cc_, cc_)))})
    assert new == BODY(cc_)
    ex_ = D(w, Ad, 'rspcedv', [], '') if False else w.s([crp, ral, w.s([sb], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. c e. RR+ %s )' % (cc_, BODY(cc_), BODY('c')))], 'sylanc' if False else 'syl2anc',
                                                   '( %s -> E. c e. RR+ %s )' % (Ad, BODY('c')))
    fin = w.s([w.s([], 'zl3grat', 'E. d e. RR+ %s' % GRAT), w.s([ex_], 'rexlimiva', '( E. d e. RR+ %s -> E. c e. RR+ %s )' % (GRAT, BODY('c')))], 'ax-mp', 'E. c e. RR+ %s' % BODY('c'))
    w.qed([fin], 'idi', SE['zl3igb'])
    goe(w)


def cbv_rex(w, fn, old, new, dom):
    """( E. old e. dom fn(old) <-> E. new e. dom fn(new) )"""
    return w.s([wsub(w, fn, old, new)], 'cbvrexvw', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (old, dom, fn(old), new, dom, fn(new)))


IGB = lambda cc, u='u': ('A. %s e. CC ( ( ( 3 / 4 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 5 / 2 ) ) -> ( ( _G ` %s ) =/= 0 /\\ ( 1 / ( abs ` ( _G ` %s ) ) ) <_ ( %s x. ( exp ` ( 5 x. ( abs ` ( Im ` %s ) ) ) ) ) ) )'
                         % (u, u, u, u, u, cc, u))

# ---------------------------------------------------------------- zl3hgb
if wante('zl3hgb', MAIN):
    w = W('zl3hgb', 'Exponential bounds on the strip ` -1/2 <_ Re v <_ 2 ` for ` h ( v ) = ( pi / M ) ^ w / Gamma ( w + 1 ) ` and ` g ( v ) = w h ( v ) ` , ` w = ( v + P ) / 2 ` ( ~ zl3igb ).')
    A, Cc = ante_e('zl3hgb')
    Wv = LE.WV('v'); HVv = LE.HV('v'); GVv = LE.GV('v')
    t = '( abs ` ( Im ` v ) )'
    E3 = '( exp ` ( 3 x. %s ) )' % t
    PM = '( _pi / M )'
    CPM = '( exp ` ( ( 3 / 2 ) x. ( abs ` ( log ` %s ) ) ) )' % PM
    cc_ = '( 2 x. ( d x. %s ) )' % CPM
    BODY = lambda cc: ('A. v e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) -> ( ( abs ` %s ) <_ ( %s x. %s ) /\\ ( abs ` %s ) <_ ( %s x. %s ) ) )'
                       % (HVv, cc, E3, GVv, cc, E3))
    A0 = '( %s /\\ ( d e. RR+ /\\ %s ) )' % (A, IGB('d'))
    A1 = '( %s /\\ v e. CC )' % A0
    A2 = '( %s /\\ ( -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) )' % A1
    L2 = lambda st, f: ad(w, A2, ad(w, A1, st, f), f)
    mp = D(w, A0, 'simpl', [], LE.MP)
    mn = D(w, A2, 'simpld', [L2(mp, LE.MP)], 'M e. NN'); pp = D(w, A2, 'simprd', [L2(mp, LE.MP)], 'P e. { 0 , 1 }')
    drp = L2(D(w, A0, 'simprl', [], 'd e. RR+'), 'd e. RR+'); igb = L2(D(w, A0, 'simprr', [], IGB('d')), IGB('d'))
    vc = D(w, A2, 'simplr', [], 'v e. CC')
    lo = D(w, A2, 'simprl', [], '-u ( 1 / 2 ) <_ ( Re ` v )'); hi = D(w, A2, 'simprr', [], '( Re ` v ) <_ 2')
    pn, pr, p0, p1 = p01(w, A2, pp)
    pc = D(w, A2, 'recnd', [pr], 'P e. CC')
    spc, reW, imW = reim_w(w, A2, 'v', vc, pc, pr)
    wc = D(w, A2, 'divcld', [spc, cst(w, A2, '2cn', '2 e. CC'), cst(w, A2, '2ne0', '2 =/= 0')], '%s e. CC' % Wv)
    V1 = '( %s + 1 )' % Wv
    v1c = D(w, A2, 'addcld', [wc, cst(w, A2, 'ax-1cn', '1 e. CC')], '%s e. CC' % V1)
    reV = D(w, A2, 'eqtrd', [D(w, A2, 'readdd', [wc, cst(w, A2, 'ax-1cn', '1 e. CC')], '( Re ` %s ) = ( ( Re ` %s ) + ( Re ` 1 ) )' % (V1, Wv)),
                             D(w, A2, 'oveq12d', [reW, cst(w, A2, 're1', '( Re ` 1 ) = 1')], '( ( Re ` %s ) + ( Re ` 1 ) ) = ( ( ( ( Re ` v ) + P ) / 2 ) + 1 )' % Wv)],
            '( Re ` %s ) = ( ( ( ( Re ` v ) + P ) / 2 ) + 1 )' % V1)
    imV = D(w, A2, 'eqtrd', [D(w, A2, 'imaddd', [wc, cst(w, A2, 'ax-1cn', '1 e. CC')], '( Im ` %s ) = ( ( Im ` %s ) + ( Im ` 1 ) )' % (V1, Wv)),
                             D(w, A2, 'eqtrd', [D(w, A2, 'oveq12d', [imW, cst(w, A2, 'im1', '( Im ` 1 ) = 0')], '( ( Im ` %s ) + ( Im ` 1 ) ) = ( ( ( Im ` v ) / 2 ) + 0 )' % Wv),
                                                D(w, A2, 'addridd', [D(w, A2, 'divcld', [D(w, A2, 'recnd', [D(w, A2, 'imcld', [vc], '( Im ` v ) e. RR')], '( Im ` v ) e. CC'),
                                                                                          cst(w, A2, '2cn', '2 e. CC'), cst(w, A2, '2ne0', '2 =/= 0')], '( ( Im ` v ) / 2 ) e. CC')],
                                                  '( ( ( Im ` v ) / 2 ) + 0 ) = ( ( Im ` v ) / 2 )')], '( ( Im ` %s ) + ( Im ` 1 ) ) = ( ( Im ` v ) / 2 )' % Wv)],
            '( Im ` %s ) = ( ( Im ` v ) / 2 )' % V1)
    rvr = D(w, A2, 'recld', [vc], '( Re ` v ) e. RR')
    cl = Closure(w, A2, {'( Re ` v )': ('RR', rvr), 'P': [('RR', pr), ('ge0', p0)], 'M': ('NN', mn), 'd': ('RR+', drp), '_pi': ('RR+', cst(w, A2, 'pirp', '_pi e. RR+')), 'v': ('CC', vc),
                         t: [('RR', D(w, A2, 'abscld', [D(w, A2, 'recnd', [D(w, A2, 'imcld', [vc], '( Im ` v ) e. RR')], '( Im ` v ) e. CC')], '%s e. RR' % t)),
                             ('ge0', D(w, A2, 'absge0d', [D(w, A2, 'recnd', [D(w, A2, 'imcld', [vc], '( Im ` v ) e. RR')], '( Im ` v ) e. CC')], '0 <_ %s' % t))]})
    rng = D(w, A2, 'jca', [D(w, A2, 'breqtrrd', [linarith(w, A2, [lo, p0], '( 3 / 4 ) <_ ( ( ( ( Re ` v ) + P ) / 2 ) + 1 )', closure=cl), reV], '( 3 / 4 ) <_ ( Re ` %s )' % V1),
                           D(w, A2, 'eqbrtrd', [reV, linarith(w, A2, [hi, p1], '( ( ( ( Re ` v ) + P ) / 2 ) + 1 ) <_ ( 5 / 2 )', closure=cl)], '( Re ` %s ) <_ ( 5 / 2 )' % V1)],
              '( ( 3 / 4 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 5 / 2 ) )' % (V1, V1))
    IGb = lambda u: '( ( ( 3 / 4 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 5 / 2 ) ) -> ( ( _G ` %s ) =/= 0 /\\ ( 1 / ( abs ` ( _G ` %s ) ) ) <_ ( d x. ( exp ` ( 5 x. ( abs ` ( Im ` %s ) ) ) ) ) ) )' % (u, u, u, u, u)
    inst = D(w, A2, 'mpd', [igb, D(w, A2, 'syl', [v1c, w.s([vsub(w, IGb, 'u', V1) if False else wsub(w, IGb, 'u', V1)], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (V1, IGB('d'), IGb(V1)))],
                                                    '( %s -> %s )' % (IGB('d'), IGb(V1)))], IGb(V1))
    gb = D(w, A2, 'mpd', [rng, inst], '( ( _G ` %s ) =/= 0 /\\ ( 1 / ( abs ` ( _G ` %s ) ) ) <_ ( d x. ( exp ` ( 5 x. ( abs ` ( Im ` %s ) ) ) ) ) )' % (V1, V1, V1))
    gne = D(w, A2, 'simpld', [gb], '( _G ` %s ) =/= 0' % V1)
    gle = D(w, A2, 'simprd', [gb], '( 1 / ( abs ` ( _G ` %s ) ) ) <_ ( d x. ( exp ` ( 5 x. ( abs ` ( Im ` %s ) ) ) ) )' % (V1, V1))
    # | Im V1 | = t / 2
    aiv = chain(w, A2, ['( abs ` ( Im ` %s ) )' % V1, '( abs ` ( ( Im ` v ) / 2 ) )', '( ( abs ` ( Im ` v ) ) / ( abs ` 2 ) )', '( %s / 2 )' % t],
                [D(w, A2, 'fveq2d', [imV], '( abs ` ( Im ` %s ) ) = ( abs ` ( ( Im ` v ) / 2 ) )' % V1),
                 D(w, A2, 'absdivd', [D(w, A2, 'recnd', [D(w, A2, 'imcld', [vc], '( Im ` v ) e. RR')], '( Im ` v ) e. CC'), cst(w, A2, '2cn', '2 e. CC'), cst(w, A2, '2ne0', '2 =/= 0')],
                   '( abs ` ( ( Im ` v ) / 2 ) ) = ( ( abs ` ( Im ` v ) ) / ( abs ` 2 ) )'),
                 D(w, A2, 'oveq2d', [D(w, A2, 'absidd', [cst(w, A2, '2re', '2 e. RR'), cst(w, A2, '0le2', '0 <_ 2')], '( abs ` 2 ) = 2')], '( ( abs ` ( Im ` v ) ) / ( abs ` 2 ) ) = ( %s / 2 )' % t)])
    E5 = '( exp ` ( 5 x. ( %s / 2 ) ) )' % t
    gle2 = D(w, A2, 'breqtrd', [gle, D(w, A2, 'oveq2d', [D(w, A2, 'fveq2d', [D(w, A2, 'oveq2d', [aiv], '( 5 x. ( abs ` ( Im ` %s ) ) ) = ( 5 x. ( %s / 2 ) )' % (V1, t))],
                                                                    '( exp ` ( 5 x. ( abs ` ( Im ` %s ) ) ) ) = %s' % (V1, E5))],
                                                      '( d x. ( exp ` ( 5 x. ( abs ` ( Im ` %s ) ) ) ) ) = ( d x. %s )' % (V1, E5))],
             '( 1 / ( abs ` ( _G ` %s ) ) ) <_ ( d x. %s )' % (V1, E5))
    # | ( pi / M ) ^c W | <_ CPM
    pmrp = cl.mem(PM, 'RR+')
    LG = '( log ` %s )' % PM
    lgr = D(w, A2, 'relogcld', [pmrp], '%s e. RR' % LG)
    rew = '( Re ` %s )' % Wv
    rewr = D(w, A2, 'recld', [wc], '%s e. RR' % rew)
    acx = D(w, A2, 'syl2anc', [pmrp, wc, w.inst('abscxp')], '( abs ` ( %s ^c %s ) ) = ( %s ^c %s )' % (PM, Wv, PM, rew))
    cxe = D(w, A2, 'cxpefd', [D(w, A2, 'rpcnd', [pmrp], '%s e. CC' % PM), D(w, A2, 'rpne0d', [pmrp], '%s =/= 0' % PM), D(w, A2, 'recnd', [rewr], '%s e. CC' % rew)],
            '( %s ^c %s ) = ( exp ` ( %s x. %s ) )' % (PM, rew, rew, LG))
    prod_ = '( %s x. %s )' % (rew, LG)
    pr_r = D(w, A2, 'remulcld', [rewr, lgr], '%s e. RR' % prod_)
    l1 = D(w, A2, 'syl', [pr_r, w.inst('leabs')], '%s <_ ( abs ` %s )' % (prod_, prod_))
    l2 = D(w, A2, 'absmuld', [D(w, A2, 'recnd', [rewr], '%s e. CC' % rew), D(w, A2, 'recnd', [lgr], '%s e. CC' % LG)], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (prod_, rew, LG))
    arw = '( abs ` %s )' % rew
    arwle = D(w, A2, 'mpbird', [D(w, A2, 'jca', [D(w, A2, 'breqtrrd', [linarith(w, A2, [lo, p0], '-u ( 3 / 2 ) <_ ( ( ( Re ` v ) + P ) / 2 )', closure=cl), reW], '-u ( 3 / 2 ) <_ %s' % rew),
                                                 D(w, A2, 'eqbrtrd', [reW, linarith(w, A2, [hi, p1], '( ( ( Re ` v ) + P ) / 2 ) <_ ( 3 / 2 )', closure=cl)], '%s <_ ( 3 / 2 )' % rew)],
                                           '( -u ( 3 / 2 ) <_ %s /\\ %s <_ ( 3 / 2 ) )' % (rew, rew)),
                                   D(w, A2, 'absled', [rewr, cl.mem('( 3 / 2 )', 'RR')], '( %s <_ ( 3 / 2 ) <-> ( -u ( 3 / 2 ) <_ %s /\\ %s <_ ( 3 / 2 ) ) )' % (arw, rew, rew))],
                  '%s <_ ( 3 / 2 )' % arw)
    alg = '( abs ` %s )' % LG
    algr = D(w, A2, 'abscld', [D(w, A2, 'recnd', [lgr], '%s e. CC' % LG)], '%s e. RR' % alg); alg0 = D(w, A2, 'absge0d', [D(w, A2, 'recnd', [lgr], '%s e. CC' % LG)], '0 <_ %s' % alg)
    l3 = D(w, A2, 'lemul1ad', [D(w, A2, 'abscld', [D(w, A2, 'recnd', [rewr], '%s e. CC' % rew)], '%s e. RR' % arw), cl.mem('( 3 / 2 )', 'RR'), algr, alg0, arwle],
           '( %s x. %s ) <_ ( ( 3 / 2 ) x. %s )' % (arw, alg, alg))
    ex_le = D(w, A2, 'letrd', [pr_r, D(w, A2, 'abscld', [D(w, A2, 'recnd', [pr_r], '%s e. CC' % prod_)], '( abs ` %s ) e. RR' % prod_),
                               D(w, A2, 'remulcld', [cl.mem('( 3 / 2 )', 'RR'), algr], '( ( 3 / 2 ) x. %s ) e. RR' % alg), l1, D(w, A2, 'eqbrtrd', [l2, l3], '( abs ` %s ) <_ ( ( 3 / 2 ) x. %s )' % (prod_, alg))],
          '%s <_ ( ( 3 / 2 ) x. %s )' % (prod_, alg))
    cpm_le = D(w, A2, 'eqbrtrd', [D(w, A2, 'eqtrd', [acx, cxe], '( abs ` ( %s ^c %s ) ) = ( exp ` %s )' % (PM, Wv, prod_)),
                                  efle_(w, A2, prod_, '( ( 3 / 2 ) x. %s )' % alg, pr_r, D(w, A2, 'remulcld', [cl.mem('( 3 / 2 )', 'RR'), algr], '( ( 3 / 2 ) x. %s ) e. RR' % alg), ex_le)],
               '( abs ` ( %s ^c %s ) ) <_ %s' % (PM, Wv, CPM))
    # | h |
    Gv1 = '( _G ` %s )' % V1
    g1c = D(w, A2, 'syl', [D(w, A2, 'syl2anc', [v1c, D(w, A2, 'breqtrrd', [linarith(w, A2, [lo, p0], '0 < ( ( ( ( Re ` v ) + P ) / 2 ) + 1 )', closure=cl), reV], '0 < ( Re ` %s )' % V1),
                                                w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % V1), w.inst('gamcl')], '%s e. CC' % Gv1)
    cxw = '( %s ^c %s )' % (PM, Wv)
    cxwc = D(w, A2, 'cxpcld', [D(w, A2, 'rpcnd', [pmrp], '%s e. CC' % PM), wc], '%s e. CC' % cxw)
    IG = '( 1 / ( abs ` %s ) )' % Gv1
    ag = '( abs ` %s )' % Gv1
    agr = D(w, A2, 'abscld', [g1c], '%s e. RR' % ag); agne = D(w, A2, 'absne0d', [g1c, gne], '%s =/= 0' % ag)
    hab = chain(w, A2, ['( abs ` %s )' % HVv, '( ( abs ` %s ) / %s )' % (cxw, ag), '( ( abs ` %s ) x. %s )' % (cxw, IG)],
                [D(w, A2, 'absdivd', [cxwc, g1c, gne], '( abs ` %s ) = ( ( abs ` %s ) / %s )' % (HVv, cxw, ag)),
                 D(w, A2, 'divrecd', [D(w, A2, 'abscld', [cxwc], '( abs ` %s ) e. RR' % cxw) and D(w, A2, 'recnd', [D(w, A2, 'abscld', [cxwc], '( abs ` %s ) e. RR' % cxw)], '( abs ` %s ) e. CC' % cxw),
                                      D(w, A2, 'recnd', [agr], '%s e. CC' % ag), agne], '( ( abs ` %s ) / %s ) = ( ( abs ` %s ) x. %s )' % (cxw, ag, cxw, IG))])
    igr = D(w, A2, 'rereccld', [agr, agne], '%s e. RR' % IG)
    ig0 = D(w, A2, 'ltled', [cst(w, A2, '0re', '0 e. RR'), igr, D(w, A2, 'recgt0d', [agr, D(w, A2, 'mpbid', [gne, D(w, A2, 'syl', [g1c, w.inst('absgt0')], '( %s =/= 0 <-> 0 < %s )' % (Gv1, ag))], '0 < %s' % ag)], '0 < %s' % IG)],
            '0 <_ %s' % IG)
    acxr = D(w, A2, 'abscld', [cxwc], '( abs ` %s ) e. RR' % cxw)
    cl.leaf(E5, 'RR+', D(w, A2, 'rpefcld', [cl.mem('( 5 x. ( %s / 2 ) )' % t, 'RR')], '%s e. RR+' % E5))
    cl.leaf(CPM, 'RR+', D(w, A2, 'rpefcld', [D(w, A2, 'remulcld', [cl.mem('( 3 / 2 )', 'RR'), algr], '( ( 3 / 2 ) x. %s ) e. RR' % alg)], '%s e. RR+' % CPM))
    hle = D(w, A2, 'breqtrrd' if False else 'eqbrtrd', [hab, D(w, A2, 'lemul12ad', [acxr, cl.mem(CPM, 'RR'), igr, cl.mem('( d x. %s )' % E5, 'RR'),
                                                                                   D(w, A2, 'absge0d', [cxwc], '0 <_ ( abs ` %s )' % cxw), ig0, cpm_le, gle2],
                                                                       '( ( abs ` %s ) x. %s ) <_ ( %s x. ( d x. %s ) )' % (cxw, IG, CPM, E5))],
          '( abs ` %s ) <_ ( %s x. ( d x. %s ) )' % (HVv, CPM, E5))
    # exponentials: e ^ ( 5 t / 2 ) <_ e ^ ( 3 t ) , e ^ ( t / 2 ) e ^ ( 5 t / 2 ) = e ^ ( 3 t )
    Eh = '( exp ` ( %s / 2 ) )' % t
    cl.leaf(Eh, 'RR+', D(w, A2, 'rpefcld', [cl.mem('( %s / 2 )' % t, 'RR')], '%s e. RR+' % Eh))
    cl.leaf(E3, 'RR+', D(w, A2, 'rpefcld', [cl.mem('( 3 x. %s )' % t, 'RR')], '%s e. RR+' % E3))
    e53 = efle_(w, A2, '( 5 x. ( %s / 2 ) )' % t, '( 3 x. %s )' % t, cl.mem('( 5 x. ( %s / 2 ) )' % t, 'RR'), cl.mem('( 3 x. %s )' % t, 'RR'),
                linarith(w, A2, [cl.ge0(t)], '( 5 x. ( %s / 2 ) ) <_ ( 3 x. %s )' % (t, t), closure=cl))
    ehe = D(w, A2, 'eqtr3d', [efadd_(w, A2, '( %s / 2 )' % t, '( 5 x. ( %s / 2 ) )' % t, cl.mem('( %s / 2 )' % t, 'CC'), cl.mem('( 5 x. ( %s / 2 ) )' % t, 'CC')),
                              D(w, A2, 'fveq2d', [lineq(w, A2, '( ( %s / 2 ) + ( 5 x. ( %s / 2 ) ) )' % (t, t), '( 3 x. %s )' % t, closure=cl)],
                                '( exp ` ( ( %s / 2 ) + ( 5 x. ( %s / 2 ) ) ) ) = %s' % (t, t, E3))], '( %s x. %s ) = %s' % (Eh, E5, E3))
    # | W | <_ ( 3 / 2 ) e ^ ( t / 2 )
    aw = '( abs ` %s )' % Wv
    awle0 = D(w, A2, 'syl', [wc, w.inst('absreimle')], '%s <_ ( ( abs ` ( Re ` %s ) ) + ( abs ` ( Im ` %s ) ) )' % (aw, Wv, Wv))
    aimw = D(w, A2, 'eqtrd', [D(w, A2, 'fveq2d', [imW], '( abs ` ( Im ` %s ) ) = ( abs ` ( ( Im ` v ) / 2 ) )' % Wv), aiv if False else
                              D(w, A2, 'eqtrd', [D(w, A2, 'absdivd', [D(w, A2, 'recnd', [D(w, A2, 'imcld', [vc], '( Im ` v ) e. RR')], '( Im ` v ) e. CC'), cst(w, A2, '2cn', '2 e. CC'), cst(w, A2, '2ne0', '2 =/= 0')],
                                                   '( abs ` ( ( Im ` v ) / 2 ) ) = ( ( abs ` ( Im ` v ) ) / ( abs ` 2 ) )'),
                                                 D(w, A2, 'oveq2d', [D(w, A2, 'absidd', [cst(w, A2, '2re', '2 e. RR'), cst(w, A2, '0le2', '0 <_ 2')], '( abs ` 2 ) = 2')], '( ( abs ` ( Im ` v ) ) / ( abs ` 2 ) ) = ( %s / 2 )' % t)],
                                '( abs ` ( ( Im ` v ) / 2 ) ) = ( %s / 2 )' % t)], '( abs ` ( Im ` %s ) ) = ( %s / 2 )' % (Wv, t))
    bvh = D(w, A2, 'syl2anc', [cl.mem('( %s / 2 )' % t, 'RR'), cl.ge0('( %s / 2 )' % t), w.inst('bvefge1p')], '( 1 + ( %s / 2 ) ) <_ %s' % (t, Eh))
    awr = D(w, A2, 'abscld', [wc], '%s e. RR' % aw)
    cl.have(rew, 'RR', rewr); cl.have('( Im ` %s )' % Wv, 'RR', D(w, A2, 'imcld', [wc], '( Im ` %s ) e. RR' % Wv))
    awle = linarith(w, A2, [awle0, D(w, A2, 'eqle' if False else 'eqlei' if False else 'eqled', [aimw], '( abs ` ( Im ` %s ) ) <_ ( %s / 2 )' % (Wv, t)), arwle, bvh, cl.ge0(t)],
                    '%s <_ ( ( 3 / 2 ) x. %s )' % (aw, Eh), closure=cl, atoms=[aw, arw, '( abs ` ( Im ` %s ) )' % Wv, Eh, t])
    # | g | = | W | | h |
    gab = D(w, A2, 'absmuld', [wc, D(w, A2, 'divcld', [cxwc, g1c, gne], '%s e. CC' % HVv)], '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (GVv, aw, HVv))
    ahr = D(w, A2, 'abscld', [D(w, A2, 'divcld', [cxwc, g1c, gne], '%s e. CC' % HVv)], '( abs ` %s ) e. RR' % HVv)
    ah0 = D(w, A2, 'absge0d', [D(w, A2, 'divcld', [cxwc, g1c, gne], '%s e. CC' % HVv)], '0 <_ ( abs ` %s )' % HVv)
    gle3 = D(w, A2, 'eqbrtrd', [gab, D(w, A2, 'lemul12ad', [awr, cl.mem('( ( 3 / 2 ) x. %s )' % Eh, 'RR'), ahr, cl.mem('( %s x. ( d x. %s ) )' % (CPM, E5), 'RR'),
                                                              D(w, A2, 'absge0d', [wc], '0 <_ %s' % aw), ah0, awle, hle],
                                                   '( %s x. ( abs ` %s ) ) <_ ( ( ( 3 / 2 ) x. %s ) x. ( %s x. ( d x. %s ) ) )' % (aw, HVv, Eh, CPM, E5))],
             '( abs ` %s ) <_ ( ( ( 3 / 2 ) x. %s ) x. ( %s x. ( d x. %s ) ) )' % (GVv, Eh, CPM, E5))
    import lin as _lin
    _lin.MAXDEG = 6
    cl.have('( abs ` %s )' % HVv, 'RR', ahr); cl.have('( abs ` %s )' % GVv, 'RR', D(w, A2, 'abscld', [D(w, A2, 'mulcld', [wc, D(w, A2, 'divcld', [cxwc, g1c, gne], '%s e. CC' % HVv)], '%s e. CC' % GVv)], '( abs ` %s ) e. RR' % GVv))
    # final: h <_ c E3 , g <_ c E3 with c = 2 ( d CPM )
    m1 = D(w, A2, 'lemul2ad', [cl.mem(E5, 'RR'), cl.mem(E3, 'RR'), cl.mem('( %s x. d )' % CPM, 'RR'), cl.ge0('( %s x. d )' % CPM), e53], '( ( %s x. d ) x. %s ) <_ ( ( %s x. d ) x. %s )' % (CPM, E5, CPM, E3))
    hfin = nlinarith(w, A2, [hle, m1, cl.ge0('( ( %s x. d ) x. %s )' % (CPM, E3))], '( abs ` %s ) <_ ( %s x. %s )' % (HVv, cc_, E3), closure=cl, atoms=[CPM, 'd', E5, E3, '( abs ` %s )' % HVv])
    gfin0 = D(w, A2, 'breqtrd', [gle3, D(w, A2, 'eqtrd', [lineq(w, A2, '( ( ( 3 / 2 ) x. %s ) x. ( %s x. ( d x. %s ) ) )' % (Eh, CPM, E5), '( ( ( 3 / 2 ) x. ( %s x. d ) ) x. ( %s x. %s ) )' % (CPM, Eh, E5),
                                                                  closure=cl, atoms=[Eh, CPM, 'd', E5], products=True),
                                                           D(w, A2, 'oveq2d', [ehe], '( ( ( 3 / 2 ) x. ( %s x. d ) ) x. ( %s x. %s ) ) = ( ( ( 3 / 2 ) x. ( %s x. d ) ) x. %s )' % (CPM, Eh, E5, CPM, E3))],
                                             '( ( ( 3 / 2 ) x. %s ) x. ( %s x. ( d x. %s ) ) ) = ( ( ( 3 / 2 ) x. ( %s x. d ) ) x. %s )' % (Eh, CPM, E5, CPM, E3))],
              '( abs ` %s ) <_ ( ( ( 3 / 2 ) x. ( %s x. d ) ) x. %s )' % (GVv, CPM, E3))
    gfin = nlinarith(w, A2, [gfin0, cl.ge0('( ( %s x. d ) x. %s )' % (CPM, E3))], '( abs ` %s ) <_ ( %s x. %s )' % (GVv, cc_, E3), closure=cl, atoms=[CPM, 'd', E3, '( abs ` %s )' % GVv])
    both = D(w, A2, 'jca', [hfin, gfin], '( ( abs ` %s ) <_ ( %s x. %s ) /\\ ( abs ` %s ) <_ ( %s x. %s ) )' % (HVv, cc_, E3, GVv, cc_, E3))
    imp = D(w, A1, 'ex', [both], '( ( -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) -> ( ( abs ` %s ) <_ ( %s x. %s ) /\\ ( abs ` %s ) <_ ( %s x. %s ) ) )' % (HVv, cc_, E3, GVv, cc_, E3))
    ral = D(w, A0, 'ralrimiva', [imp], BODY(cc_))
    cl0 = Closure(w, A0, {'d': ('RR+', D(w, A0, 'simprl', [], 'd e. RR+')), 'M': ('NN', D(w, A0, 'simpld', [mp], 'M e. NN')), '_pi': ('RR+', cst(w, A0, 'pirp', '_pi e. RR+'))})
    crp = D(w, A0, 'rpmulcld', [cl0.mem('2', 'RR+'), D(w, A0, 'rpmulcld', [D(w, A0, 'simprl', [], 'd e. RR+'), D(w, A0, 'rpefcld', [D(w, A0, 'remulcld', [cl0.mem('( 3 / 2 )', 'RR'),
                                                  D(w, A0, 'abscld', [D(w, A0, 'recnd', [D(w, A0, 'relogcld', [cl0.mem(PM, 'RR+')], '%s e. RR' % LG)], '%s e. CC' % LG)], '%s e. RR' % alg)], '( ( 3 / 2 ) x. %s ) e. RR' % alg)], '%s e. RR+' % CPM)],
                                                  '( d x. %s ) e. RR+' % CPM)], '%s e. RR+' % cc_)
    sb = wsub(w, BODY, 'c', cc_)
    ex_ = w.s([crp, ral, w.s([sb], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. c e. RR+ %s )' % (cc_, BODY(cc_), BODY('c')))], 'syl2anc', '( %s -> E. c e. RR+ %s )' % (A0, BODY('c')))
    exd = D(w, A, 'rexlimdva', [w.s([w.s([ex_], 'anassrs', '( ( ( %s /\\ d e. RR+ ) /\\ %s ) -> E. c e. RR+ %s )' % (A, IGB('d'), BODY('c')))], 'ex', '( ( %s /\\ d e. RR+ ) -> ( %s -> E. c e. RR+ %s ) )' % (A, IGB('d'), BODY('c')))], '( E. d e. RR+ %s -> E. c e. RR+ %s )' % (IGB('d'), BODY('c')))
    igbd = w.s([w.s([], 'zl3igb', 'E. c e. RR+ %s' % IGB('c')), cbv_rex(w, IGB, 'c', 'd', 'RR+')], 'mpbi', 'E. d e. RR+ %s' % IGB('d'))
    fin = D(w, A, 'mpi', [exd, igbd], 'E. c e. RR+ %s' % BODY('c'))
    w.qed([fin], 'idi', SE['zl3hgb'])
    goe(w)
