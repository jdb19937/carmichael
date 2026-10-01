"""Sortie MV, section C: sine and cosine bounds (mvcoslb, mvsindbl, mvsinlb,
mvsinlow, mvsinb)."""
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


def ioc01(w, ante, h, cl, hle1):
    """( ante -> h e. ( 0 (,] 1 ) ) from cl (h real, 0 < h) and hle1: h <_ 1"""
    bi = w.s([a1(w, ante, '0xr', '0 e. RR*'), a1(w, ante, '1re', '1 e. RR'), w.inst('elioc2')], 'syl2anc',
             '( %s -> ( %s e. ( 0 (,] 1 ) <-> ( %s e. RR /\\ 0 < %s /\\ %s <_ 1 ) ) )' % (ante, h, h, h, h))
    j = w.s([cl.mem(h, 'RR'), cl.gt0(h), hle1], '3jca', '( %s -> ( %s e. RR /\\ 0 < %s /\\ %s <_ 1 ) )' % (ante, h, h, h))
    return w.s([j, bi], 'mpbird', '( %s -> %s e. ( 0 (,] 1 ) )' % (ante, h))


def mvcoslb():
    w = W('mvcoslb', 'cos X >_ 1 - X ^ 2 / 2 for 0 < X <_ 2 (cos X = 1 - 2 sin ^ 2 ( X / 2 ) and sin ( X / 2 ) < X / 2).')
    A0 = '( X e. RR /\\ 0 < X /\\ X <_ 2 )'
    P = parts(w, A0)
    xr, x0, x2 = P['X e. RR'], P['0 < X'], P['X <_ 2']
    cl = Closure(w, A0, {'X': [('RR', xr), ('gt0', x0)]})
    h = '( X / 2 )'
    hle = linarith(w, A0, [x2], '%s <_ 1' % h, closure=cl)
    hm = ioc01(w, A0, h, cl, hle)
    sb = ap(w, A0, 'sin01bnd', [hm], '( ( %s - ( ( %s ^ 3 ) / 3 ) ) < ( sin ` %s ) /\\ ( sin ` %s ) < %s )' % (h, h, h, h, h))
    slt = dst(w, A0, [sb], 'simprd', '( sin ` %s ) < %s' % (h, h))
    sp = ap(w, A0, 'sin01gt0', [hm], '0 < ( sin ` %s )' % h)
    S = '( sin ` %s )' % h
    c2 = ap(w, A0, 'cos2tsin', [cl.mem(h, 'CC')], '( cos ` ( 2 x. %s ) ) = ( 1 - ( 2 x. ( %s ^ 2 ) ) )' % (h, S))
    e2 = dst(w, A0, [cl.mem('X', 'CC'), w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), a1(w, A0, '2ne0', '2 =/= 0')],
             'divcan2d', '( 2 x. %s ) = X' % h)
    cX = eqt(w, A0, eqc(w, A0, dst(w, A0, [e2], 'fveq2d', '( cos ` ( 2 x. %s ) ) = ( cos ` X )' % h)), c2)
    sr = cl.mem(S, 'RR')
    sle = w.s([J(w, A0, sr, w.s([sp], 'ltled', '( %s -> 0 <_ %s )' % (A0, S))), J(w, A0, cl.mem(h, 'RR'), w.s([slt], 'ltled', '( %s -> %s <_ %s )' % (A0, S, h))),
               w.inst('le2sq2')], 'syl2anc', '( %s -> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (A0, S, h))
    heq = ringeqp(w, A0, '( %s ^ 2 )' % h, '( ( X ^ 2 ) / 4 )', cl)
    cl.leaf('( %s ^ 2 )' % S, 'RR', cl.mem('( %s ^ 2 )' % S, 'RR'))
    cl.leaf('( cos ` X )', 'RR', cl.mem('( cos ` X )', 'RR'))
    cl.leaf('( %s ^ 2 )' % h, 'RR', cl.mem('( %s ^ 2 )' % h, 'RR'))
    cl.leaf('( X ^ 2 )', 'RR', cl.mem('( X ^ 2 )', 'RR'))
    linarith(w, A0, [cX, sle, heq], '( 1 - ( ( X ^ 2 ) / 2 ) ) <_ ( cos ` X )', closure=cl, name='qed')
    go(w)


def mvsindbl():
    w = W('mvsindbl', 'The doubling step: from 0 <_ L <_ sin H and 0 < H <_ 1, 2 L ( 1 - H ^ 2 / 2 ) <_ sin ( 2 H ) (sin2t and mvcoslb).')
    A0 = '( ( H e. RR /\\ 0 < H /\\ H <_ 1 ) /\\ ( L e. RR /\\ 0 <_ L /\\ L <_ ( sin ` H ) ) )'
    P = parts(w, A0)
    hr, h0, h1 = P['H e. RR'], P['0 < H'], P['H <_ 1']
    lr, l0, ls = P['L e. RR'], P['0 <_ L'], P['L <_ ( sin ` H )']
    cl = Closure(w, A0, {'H': [('RR', hr), ('gt0', h0)], 'L': [('RR', lr), ('ge0', l0)]})
    h2 = linarith(w, A0, [h1], 'H <_ 2', closure=cl)
    cb = ap(w, A0, 'mvcoslb', [w.s([hr, h0, h2], '3jca', '( %s -> ( H e. RR /\\ 0 < H /\\ H <_ 2 ) )' % A0)],
            '( 1 - ( ( H ^ 2 ) / 2 ) ) <_ ( cos ` H )')
    hh = w.s([J(w, A0, hr, ltle(w, A0, cl, h0)), J(w, A0, a1(w, A0, '1re', '1 e. RR'), h1), w.inst('le2sq2')],
             'syl2anc', '( %s -> ( H ^ 2 ) <_ ( 1 ^ 2 ) )' % A0)
    hh1 = eqt(w, A0, w.s([], 'id', '( %s -> ( H ^ 2 ) = ( H ^ 2 ) )' % A0), w.s([], 'id', '( %s -> ( H ^ 2 ) = ( H ^ 2 ) )' % A0)) if False else None
    sq1 = a1(w, A0, 'sq1', '( 1 ^ 2 ) = 1')
    hh2 = w.s([hh, sq1], 'breqtrd', '( %s -> ( H ^ 2 ) <_ 1 )' % A0)
    C = '( 1 - ( ( H ^ 2 ) / 2 ) )'
    cl.leaf('( H ^ 2 )', 'RR', cl.mem('( H ^ 2 )', 'RR'))
    c0 = linarith(w, A0, [hh2], '0 <_ %s' % C, closure=cl)
    SH = '( sin ` H )'; CH = '( cos ` H )'
    m = w.s([lr, cl.mem(SH, 'RR'), cl.mem(C, 'RR'), cl.mem(CH, 'RR'), l0, c0, ls, cb], 'lemul12ad',
            '( %s -> ( L x. %s ) <_ ( %s x. %s ) )' % (A0, C, SH, CH))
    s2 = ap(w, A0, 'sin2t', [cl.mem('H', 'CC')], '( sin ` ( 2 x. H ) ) = ( 2 x. ( %s x. %s ) )' % (SH, CH))
    at = {'( L x. %s )' % C: None}
    cl.leaf('( %s x. %s )' % (SH, CH), 'RR', cl.mem('( %s x. %s )' % (SH, CH), 'RR'))
    cl.leaf('( L x. %s )' % C, 'RR', cl.mem('( L x. %s )' % C, 'RR'))
    cl.leaf('( sin ` ( 2 x. H ) )', 'RR', cl.mem('( sin ` ( 2 x. H ) )', 'RR'))
    cl.leaf(C, 'RR', cl.mem(C, 'RR'))
    re = ringeq(w, A0, '( ( 2 x. L ) x. %s )' % C, '( 2 x. ( L x. %s ) )' % C, cl)
    cl.leaf('( ( 2 x. L ) x. %s )' % C, 'RR', cl.mem('( ( 2 x. L ) x. %s )' % C, 'RR'))
    linarith(w, A0, [m, s2, re], '( ( 2 x. L ) x. %s ) <_ ( sin ` ( 2 x. H ) )' % C, closure=cl, name='qed')
    go(w)



def sqle(w, ante, cl, A, B, a0, ab):
    """( ante -> ( A ^ 2 ) <_ ( B ^ 2 ) ) from a0: 0 <_ A, ab: A <_ B (le2sq2)"""
    return w.s([J(w, ante, cl.mem(A, 'RR'), a0), J(w, ante, cl.mem(B, 'RR'), ab), w.inst('le2sq2')], 'syl2anc',
               '( %s -> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (ante, A, B))


def mvsinlb():
    w = W('mvsinlb', 'sin Y >_ Y ( 1 - 17 Y ^ 2 / 96 ) for 0 < Y <_ 2: two doublings (mvsindbl) from sin01bnd at Y / 4.')
    A0 = '( Y e. RR /\\ 0 < Y /\\ Y <_ 2 )'
    P = parts(w, A0)
    yr, y0, y2 = P['Y e. RR'], P['0 < Y'], P['Y <_ 2']
    cl = Closure(w, A0, {'Y': [('RR', yr), ('gt0', y0)]})
    q = '( Y / 4 )'; h = '( Y / 2 )'
    qle = linarith(w, A0, [y2], '%s <_ 1' % q, closure=cl)
    qm = ioc01(w, A0, q, cl, qle)
    sb = ap(w, A0, 'sin01bnd', [qm], '( ( %s - ( ( %s ^ 3 ) / 3 ) ) < ( sin ` %s ) /\\ ( sin ` %s ) < %s )' % (q, q, q, q, q))
    L1 = '( %s - ( ( %s ^ 3 ) / 3 ) )' % (q, q)
    l1s = ltle(w, A0, cl, dst(w, A0, [sb], 'simpld', '%s < ( sin ` %s )' % (L1, q)))
    q0 = ltle(w, A0, cl, cl.gt0(q))
    qq = w.s([sqle(w, A0, cl, q, '1', q0, qle), a1(w, A0, 'sq1', '( 1 ^ 2 ) = 1')], 'breqtrd', '( %s -> ( %s ^ 2 ) <_ 1 )' % (A0, q))
    q3 = ringeqp(w, A0, '( %s ^ 3 )' % q, '( %s x. ( %s ^ 2 ) )' % (q, q), cl)
    cl.leaf('( %s ^ 2 )' % q, 'RR', cl.mem('( %s ^ 2 )' % q, 'RR'))
    q3b = w.s([cl.mem('( %s ^ 2 )' % q, 'RR'), a1(w, A0, '1re', '1 e. RR'), cl.mem(q, 'RR'), q0, qq], 'lemul2ad',
              '( %s -> ( %s x. ( %s ^ 2 ) ) <_ ( %s x. 1 ) )' % (A0, q, q, q))
    cl.leaf('( %s ^ 3 )' % q, 'RR', cl.mem('( %s ^ 3 )' % q, 'RR'))
    cl.leaf('( %s x. ( %s ^ 2 ) )' % (q, q), 'RR', cl.mem('( %s x. ( %s ^ 2 ) )' % (q, q), 'RR'))
    l10 = linarith(w, A0, [q3, q3b, y0], '0 <_ %s' % L1, closure=cl)
    cl.leaf(L1, 'RR', cl.mem(L1, 'RR'))
    d1 = ap(w, A0, 'mvsindbl', [J(w, A0, J(w, A0, cl.mem(q, 'RR'), cl.gt0(q), qle), J(w, A0, cl.mem(L1, 'RR'), l10, l1s))],
            '( ( 2 x. %s ) x. ( 1 - ( ( %s ^ 2 ) / 2 ) ) ) <_ ( sin ` ( 2 x. %s ) )' % (L1, q, q))
    e1 = dst(w, A0, [ringeq(w, A0, '( 2 x. %s )' % q, h, cl)], 'fveq2d', '( sin ` ( 2 x. %s ) ) = ( sin ` %s )' % (q, h))
    L2 = '( ( 2 x. %s ) x. ( 1 - ( ( %s ^ 2 ) / 2 ) ) )' % (L1, q)
    d1b = w.s([d1, e1], 'breqtrd', '( %s -> %s <_ ( sin ` %s ) )' % (A0, L2, h))
    c1 = linarith(w, A0, [qq], '0 <_ ( 1 - ( ( %s ^ 2 ) / 2 ) )' % q, closure=cl)
    l20 = w.s([cl.mem('( 2 x. %s )' % L1, 'RR'), cl.mem('( 1 - ( ( %s ^ 2 ) / 2 ) )' % q, 'RR'),
               linarith(w, A0, [l10], '0 <_ ( 2 x. %s )' % L1, closure=cl), c1], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, L2))
    hle = linarith(w, A0, [y2], '%s <_ 1' % h, closure=cl)
    cl.leaf(L2, 'RR', cl.mem(L2, 'RR'))
    d2 = ap(w, A0, 'mvsindbl', [J(w, A0, J(w, A0, cl.mem(h, 'RR'), cl.gt0(h), hle), J(w, A0, cl.mem(L2, 'RR'), l20, d1b))],
            '( ( 2 x. %s ) x. ( 1 - ( ( %s ^ 2 ) / 2 ) ) ) <_ ( sin ` ( 2 x. %s ) )' % (L2, h, h))
    e2 = dst(w, A0, [ringeq(w, A0, '( 2 x. %s )' % h, 'Y', cl)], 'fveq2d', '( sin ` ( 2 x. %s ) ) = ( sin ` Y )' % h)
    E = '( ( 2 x. %s ) x. ( 1 - ( ( %s ^ 2 ) / 2 ) ) )' % (L2, h)
    d2b = w.s([d2, e2], 'breqtrd', '( %s -> %s <_ ( sin ` Y ) )' % (A0, E))
    u = '( Y ^ 2 )'
    p = '( ( ( 1 - ( %s / ; 4 8 ) ) x. ( 1 - ( %s / ; 3 2 ) ) ) x. ( 1 - ( %s / 8 ) ) )' % (u, u, u)
    a_ = '( 1 - ( %s / ; 4 8 ) )' % u; b_ = '( 1 - ( %s / ; 3 2 ) )' % u; c_ = '( 1 - ( %s / 8 ) )' % u
    cl2 = Closure(w, A0, {'Y': [('RR', yr), ('gt0', y0)]})
    g1 = ringeqp(w, A0, '( 2 x. %s )' % L1, '( %s x. %s )' % (h, a_), cl2)
    g2 = ringeqp(w, A0, '( 1 - ( ( %s ^ 2 ) / 2 ) )' % q, b_, cl2)
    g3 = ringeqp(w, A0, '( 1 - ( ( %s ^ 2 ) / 2 ) )' % h, c_, cl2)
    L2b = '( ( %s x. %s ) x. %s )' % (h, a_, b_)
    g4 = dst(w, A0, [g1, g2], 'oveq12d', '%s = %s' % (L2, L2b))
    cl4 = Closure(w, A0, {'Y': ('RR', yr), a_: ('RR', cl.mem(a_, 'RR')), b_: ('RR', cl.mem(b_, 'RR')), c_: ('RR', cl.mem(c_, 'RR'))})
    g5 = ringeq(w, A0, '( ( 2 x. %s ) x. %s )' % (L2b, c_), '( Y x. %s )' % p, cl4)
    g6 = dst(w, A0, [dst(w, A0, [g4], 'oveq2d', '( 2 x. %s ) = ( 2 x. %s )' % (L2, L2b)), g3], 'oveq12d',
             '%s = ( ( 2 x. %s ) x. %s )' % (E, L2b, c_))
    eE = eqt(w, A0, g6, g5)
    u0 = w.s([yr], 'sqge0d', '( %s -> 0 <_ %s )' % (A0, u))
    u4 = w.s([sqle(w, A0, cl, 'Y', '2', ltle(w, A0, cl, y0), y2), a1(w, A0, 'sq2', '( 2 ^ 2 ) = 4')], 'breqtrd',
             '( %s -> %s <_ 4 )' % (A0, u))
    cl3 = Closure(w, A0, {u: ('RR', cl.mem(u, 'RR'))})
    lo = '( 1 - ( ( ; 1 7 x. %s ) / ; 9 6 ) )' % u
    pin = nlinarith(w, A0, [u0, u4], '%s <_ %s' % (lo, p), closure=cl3)
    m = w.s([cl.mem(lo, 'RR'), cl.mem(p, 'RR'), yr, ltle(w, A0, cl, y0), pin], 'lemul2ad',
            '( %s -> ( Y x. %s ) <_ ( Y x. %s ) )' % (A0, lo, p))
    w.s([m, w.s([eE, d2b], 'eqbrtrrd', '( %s -> ( Y x. %s ) <_ ( sin ` Y ) )' % (A0, p))], 'letrd',
        '( %s -> ( Y x. %s ) <_ ( sin ` Y ) )' % (A0, lo))
    qedlast(w)
    go(w)


def mvsinlow():
    w = W('mvsinlow', 'sin ^ 2 Y >_ ( 2 / 3 ) Y ^ 2 for 0 < Y <_ 1 (the lower bound of the Fejer kernel near 0, MeanValue fejer_lower).')
    A0 = '( Y e. RR /\\ 0 < Y /\\ Y <_ 1 )'
    P = parts(w, A0)
    yr, y0, y1 = P['Y e. RR'], P['0 < Y'], P['Y <_ 1']
    cl = Closure(w, A0, {'Y': [('RR', yr), ('gt0', y0)]})
    u = '( Y ^ 2 )'; v = '( 1 - ( ( ; 1 7 x. %s ) / ; 9 6 ) )' % u; B = '( Y x. %s )' % v; S = '( sin ` Y )'
    y2 = linarith(w, A0, [y1], 'Y <_ 2', closure=cl)
    lb = ap(w, A0, 'mvsinlb', [w.s([yr, y0, y2], '3jca', '( %s -> ( Y e. RR /\\ 0 < Y /\\ Y <_ 2 ) )' % A0)], '%s <_ %s' % (B, S))
    u0 = w.s([yr], 'sqge0d', '( %s -> 0 <_ %s )' % (A0, u))
    u1 = w.s([sqle(w, A0, cl, 'Y', '1', ltle(w, A0, cl, y0), y1), a1(w, A0, 'sq1', '( 1 ^ 2 ) = 1')], 'breqtrd', '( %s -> %s <_ 1 )' % (A0, u))
    cl.leaf(u, 'RR', cl.mem(u, 'RR'))
    v79 = linarith(w, A0, [u1], '( ; 7 9 / ; 9 6 ) <_ %s' % v, closure=cl)
    cv = Closure(w, A0, {u: ('RR', cl.mem(u, 'RR'))})
    vv = nlinarith(w, A0, [u1, u0], '( 2 / 3 ) <_ ( %s x. %s )' % (v, v), closure=cv)
    v0 = linarith(w, A0, [v79], '0 <_ %s' % v, closure=cl)
    b0 = w.s([yr, cl.mem(v, 'RR'), ltle(w, A0, cl, y0), v0], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, B))
    b2 = sqle(w, A0, cl, B, S, b0, lb)
    e1 = ringeqp(w, A0, '( %s ^ 2 )' % B, '( %s x. ( %s x. %s ) )' % (u, v, v), Closure(w, A0, {'Y': ('RR', yr)}))
    e2 = w.s([a1(w, A0, '2re', '2 e. RR') and cl.mem('( 2 / 3 )', 'RR'), cl.mem('( %s x. %s )' % (v, v), 'RR'), cl.mem(u, 'RR'), u0, vv], 'lemul2ad',
             '( %s -> ( %s x. ( 2 / 3 ) ) <_ ( %s x. ( %s x. %s ) ) )' % (A0, u, u, v, v))
    for t in ['( %s ^ 2 )' % B, '( %s ^ 2 )' % S, '( %s x. ( %s x. %s ) )' % (u, v, v)]:
        cl.leaf(t, 'RR', cl.mem(t, 'RR'))
    linarith(w, A0, [e1, e2, b2], '( ( 2 / 3 ) x. %s ) <_ ( %s ^ 2 )' % (u, S), closure=cl, name='qed')
    go(w)


def mvsinb():
    w = W('mvsinb', 'On ( 0 , pi / 2 ): 0 < sin Y < Y and 1 / sin ^ 2 Y - 1 / Y ^ 2 <_ 9 (the defect between the Fejer kernel and 1 / Y ^ 2).')
    A0 = 'Y e. ( 0 (,) ( _pi / 2 ) )'
    hy = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    yr = ap(w, A0, 'elioore', [hy], 'Y e. RR')
    oo = ap(w, A0, 'eliooord', [hy], '( 0 < Y /\\ Y < ( _pi / 2 ) )')
    y0 = dst(w, A0, [oo], 'simpld', '0 < Y'); yh = dst(w, A0, [oo], 'simprd', 'Y < ( _pi / 2 )')
    cl = Closure(w, A0, {'Y': [('RR', yr), ('gt0', y0)], '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    p4 = dst(w, A0, [a1(w, A0, 'pigt2lt4', '( 2 < _pi /\\ _pi < 4 )')], 'simprd', '_pi < 4')
    y2 = linarith(w, A0, [yh, p4], 'Y <_ 2', closure=cl)
    sp = dst(w, A0, [ap(w, A0, 'sincosq1sgn', [hy], '( 0 < ( sin ` Y ) /\\ 0 < ( cos ` Y ) )')], 'simpld', '0 < ( sin ` Y )')
    S = '( sin ` Y )'
    sl = ap(w, A0, 'sinltx', [w.s([yr, y0], 'elrpd', '( %s -> Y e. RR+ )' % A0)], '%s < Y' % S)
    u = '( Y ^ 2 )'; Wt = '( Y x. %s )' % u
    lb = ap(w, A0, 'mvsinlb', [w.s([yr, y0, y2], '3jca', '( %s -> ( Y e. RR /\\ 0 < Y /\\ Y <_ 2 ) )' % A0)],
            '( Y x. ( 1 - ( ( ; 1 7 x. %s ) / ; 9 6 ) ) ) <_ %s' % (u, S))
    cl.leaf(S, 'RR', cl.mem(S, 'RR')); cl.leaf(u, 'RR', cl.mem(u, 'RR')); cl.leaf(Wt, 'RR', cl.mem(Wt, 'RR'))
    cu = Closure(w, A0, {'Y': ('RR', yr), u: ('RR', cl.mem(u, 'RR'))})
    e0 = ringeq(w, A0, '( Y x. ( 1 - ( ( ; 1 7 x. %s ) / ; 9 6 ) ) )' % u, '( Y - ( ( ; 1 7 x. %s ) / ; 9 6 ) )' % Wt, cu)
    a1_ = linarith(w, A0, [lb, e0], '( Y - %s ) <_ ( ( ; 1 7 x. %s ) / ; 9 6 )' % (S, Wt), closure=cl)
    a2_ = linarith(w, A0, [sl], '( Y + %s ) <_ ( 2 x. Y )' % S, closure=cl)
    a3_ = w.s([cl.mem('( Y - %s )' % S, 'RR'), cl.mem('( ( ; 1 7 x. %s ) / ; 9 6 )' % Wt, 'RR'), cl.mem('( Y + %s )' % S, 'RR'), cl.mem('( 2 x. Y )', 'RR'),
               linarith(w, A0, [sl], '0 <_ ( Y - %s )' % S, closure=cl), linarith(w, A0, [sp, y0], '0 <_ ( Y + %s )' % S, closure=cl), a1_, a2_],
              'lemul12ad', '( %s -> ( ( Y - %s ) x. ( Y + %s ) ) <_ ( ( ( ; 1 7 x. %s ) / ; 9 6 ) x. ( 2 x. Y ) ) )' % (A0, S, S, Wt))
    cys = Closure(w, A0, {'Y': ('RR', yr), S: ('RR', cl.mem(S, 'RR'))})
    a4_ = ringeqp(w, A0, '( %s - ( %s ^ 2 ) )' % (u, S), '( ( Y - %s ) x. ( Y + %s ) )' % (S, S), cys)
    a5_ = ringeqp(w, A0, '( ( ( ; 1 7 x. %s ) / ; 9 6 ) x. ( 2 x. Y ) )' % Wt, '( ( ; 1 7 x. ( %s x. %s ) ) / ; 4 8 )' % (u, u), Closure(w, A0, {'Y': ('RR', yr)}))
    u4 = w.s([sqle(w, A0, cl, 'Y', '2', ltle(w, A0, cl, y0), y2), a1(w, A0, 'sq2', '( 2 ^ 2 ) = 4')], 'breqtrd', '( %s -> %s <_ 4 )' % (A0, u))
    wy = w.s([cl.mem(u, 'RR'), a1(w, A0, '4re', '4 e. RR'), yr, ltle(w, A0, cl, y0), u4], 'lemul2ad', '( %s -> %s <_ ( Y x. 4 ) )' % (A0, Wt))
    b1 = linarith(w, A0, [lb, e0, wy, y0], 'Y <_ ( 4 x. %s )' % S, closure=cl)
    b2 = sqle(w, A0, cl, 'Y', '( 4 x. %s )' % S, ltle(w, A0, cl, y0), b1)
    S2 = '( %s ^ 2 )' % S
    b3 = ringeqp(w, A0, '( ( 4 x. %s ) ^ 2 )' % S, '( ; 1 6 x. %s )' % S2, cys)
    u0 = w.s([yr], 'sqge0d', '( %s -> 0 <_ %s )' % (A0, u))
    cl.leaf(S2, 'RR', cl.mem(S2, 'RR'))
    b4 = linarith(w, A0, [b2, b3], '%s <_ ( ; 1 6 x. %s )' % (u, S2), closure=cl)
    c1 = w.s([cl.mem(u, 'RR'), cl.mem('( ; 1 6 x. %s )' % S2, 'RR'), cl.mem(u, 'RR'), u0, b4], 'lemul1ad',
             '( %s -> ( %s x. %s ) <_ ( ( ; 1 6 x. %s ) x. %s ) )' % (A0, u, u, S2, u))
    cs2 = Closure(w, A0, {S2: ('RR', cl.mem(S2, 'RR')), u: ('RR', cl.mem(u, 'RR'))})
    c2 = ringeq(w, A0, '( ( ; 1 6 x. %s ) x. %s )' % (S2, u), '( ; 1 6 x. ( %s x. %s ) )' % (S2, u), cs2)
    su = '( %s x. %s )' % (S2, u)
    s2p = w.s([cl.mem(S, 'RR'), w.s([sp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (A0, S)) if False else cl.gt0(S)], 'id', 'x') if False else None
    s2g = w.s([cl.mem(S, 'RR'), ltle(w, A0, cl, sp) if False else None], 'id', 'x') if False else None
    S2p = w.s([cl.mem(S, 'RR'), sp], 'sqgt0d' if False else 'id', 'x') if False else None
    s2pos = cl.gt0(S2) if False else None
    ss0 = w.s([cl.mem(S2, 'RR'), cl.mem(u, 'RR'), w.s([cl.mem(S, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (A0, S2)), u0], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, su))
    for t in ['( ( Y - %s ) x. ( Y + %s ) )' % (S, S), '( ( ( ; 1 7 x. %s ) / ; 9 6 ) x. ( 2 x. Y ) )' % Wt, '( %s x. %s )' % (u, u),
              '( ( ; 1 6 x. %s ) x. %s )' % (S2, u), su]:
        cl.leaf(t, 'RR', cl.mem(t, 'RR'))
    d = linarith(w, A0, [a3_, a4_, a5_, c1, c2, ss0], '( %s - %s ) <_ ( %s x. 9 )' % (u, S2, su), closure=cl)
    # divide
    s2rp = w.s([cl.mem(S, 'RR'), w.s([sp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (A0, S))], 'sqgt0d', '( %s -> 0 < %s )' % (A0, S2))
    urp = w.s([yr, w.s([y0], 'gt0ne0d', '( %s -> Y =/= 0 )' % A0)], 'sqgt0d', '( %s -> 0 < %s )' % (A0, u))
    surp = w.s([w.s([cl.mem(S2, 'RR'), s2rp], 'elrpd', '( %s -> %s e. RR+ )' % (A0, S2)), w.s([cl.mem(u, 'RR'), urp], 'elrpd', '( %s -> %s e. RR+ )' % (A0, u))],
               'rpmulcld', '( %s -> %s e. RR+ )' % (A0, su))
    dv = w.s([cl.mem('( %s - %s )' % (u, S2), 'RR'), a1(w, A0, '9re', '9 e. RR'), surp], 'ledivmuld',
             '( %s -> ( ( ( %s - %s ) / %s ) <_ 9 <-> ( %s - %s ) <_ ( %s x. 9 ) ) )' % (A0, u, S2, su, u, S2, su))
    dd = w.s([d, dv], 'mpbird', '( %s -> ( ( %s - %s ) / %s ) <_ 9 )' % (A0, u, S2, su))
    sr = w.s([cl.mem(S2, 'CC'), cl.mem(u, 'CC'), w.s([s2rp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (A0, S2)),
              w.s([urp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (A0, u))], 'subrecd',
             '( %s -> ( ( 1 / %s ) - ( 1 / %s ) ) = ( ( %s - %s ) / %s ) )' % (A0, S2, u, u, S2, su))
    bd = w.s([sr, dd], 'eqbrtrd', '( %s -> ( ( 1 / %s ) - ( 1 / %s ) ) <_ 9 )' % (A0, S2, u))
    w.s([sp, sl, bd], '3jca', '( %s -> ( 0 < %s /\\ %s < Y /\\ ( ( 1 / %s ) - ( 1 / %s ) ) <_ 9 ) )' % (A0, S, S, S2, u))
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvcoslb()
    mvsindbl()
    mvsinlb()
    mvsinlow()
    mvsinb()
