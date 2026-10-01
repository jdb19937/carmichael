"""Sortie MV, section E: the value of S. ( 0 (,) R ) sin ^ 2 ( A t ) / t ^ 2 up to 1 / R
(mvtail, mvlim, mvgn, mvgr)."""
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


def within(w, A0, a, b, lo_pos, closed=False, v='t', extra=None):
    """( ( A0 /\\ v e. I ) ...): antecedent, membership step, real step, 0 < v step, Closure (I open or closed)"""
    I = ('( %s [,] %s )' % (a, b)) if closed else IOO(a, b)
    Av = '( %s /\\ %s e. %s )' % (A0, v, I)
    m = w.s([], 'simpr', '( %s -> %s e. %s )' % (Av, v, I))
    if closed:
        vr = w.s([lift(w, lo_pos[0], Av), lift(w, lo_pos[1], Av), m], 'elicc2d' if False else 'id', 'x') if False else None
        bi = w.s([lift(w, lo_pos[0], Av), lift(w, lo_pos[1], Av), w.inst('elicc2')], 'syl2anc',
                 '( %s -> ( %s e. %s <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (Av, v, I, v, a, v, v, b))
        tri = w.s([m, bi], 'mpbid', '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (Av, v, a, v, v, b))
        vr = w.s([tri], 'simp1d', '( %s -> %s e. RR )' % (Av, v))
        lo = w.s([tri], 'simp2d', '( %s -> %s <_ %s )' % (Av, a, v))
        v0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Av), lift(w, lo_pos[0], Av), vr, lift(w, lo_pos[2], Av), lo], 'ltletrd', '( %s -> 0 < %s )' % (Av, v))
    else:
        vr = ap(w, Av, 'elioore', [m], '%s e. RR' % v)
        oo = ap(w, Av, 'eliooord', [m], '( %s < %s /\\ %s < %s )' % (a, v, v, b))
        v0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Av), lift(w, lo_pos[0], Av), vr, lift(w, lo_pos[2], Av), dst(w, Av, [oo], 'simpld', '%s < %s' % (a, v))],
                 'lelttrd' if lo_pos[3] == 'le' else 'lttrd', '( %s -> 0 < %s )' % (Av, v))
    sq = '( %s ^ 2 )' % v
    sqp = w.s([vr, w.s([v0], 'gt0ne0d', '( %s -> %s =/= 0 )' % (Av, v))], 'sqgt0d', '( %s -> 0 < %s )' % (Av, sq))
    lv = {v: [('RR', vr), ('gt0', v0), ('ne0', w.s([v0], 'gt0ne0d', '( %s -> %s =/= 0 )' % (Av, v)))],
          sq: [('RR', w.s([vr], 'resqcld', '( %s -> %s e. RR )' % (Av, sq))), ('gt0', sqp), ('ne0', w.s([sqp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (Av, sq)))]}
    for k, (kind, st_) in (extra or {}).items():
        lv[k] = (kind, lift(w, st_, Av))
    return Av, m, vr, v0, Closure(w, Av, lv)


def mvtail():
    w = W('mvtail', 'The tail bound: the integral of sin ^ 2 ( A t ) / t ^ 2 over ( R , Q ) is at most 1 / R (FTC for -u 1 / t, ef1ftc).')
    A0 = '( A e. RR /\\ ( R e. RR+ /\\ Q e. RR /\\ R <_ Q ) )'
    P = parts(w, A0)
    ar, rp, qr, rq = P['A e. RR'], P['R e. RR+'], P['Q e. RR'], P['R <_ Q']
    rr = w.s([rp], 'rpred', '( %s -> R e. RR )' % A0)
    r0 = w.s([rp], 'rpgt0d', '( %s -> 0 < R )' % A0)
    r0e = w.s([rp], 'rpge0d', '( %s -> 0 <_ R )' % A0)
    cl = Closure(w, A0, {'A': ('RR', ar), 'R': [('RR+', rp)], 'Q': ('RR', qr)})
    q0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), rr, qr, r0, rq], 'ltletrd', '( %s -> 0 < Q )' % A0)
    cl.leaf('Q', 'gt0', q0)
    G = '( -u 1 / t )'; H = '( 1 / ( t ^ 2 ) )'
    Io = IOO('R', 'Q'); Ic = '( R [,] Q )'
    extra = {'A': ('RR', ar)}
    Ac, mc, tc, t0c, cc = within(w, A0, 'R', 'Q', (rr, qr, r0), closed=True, extra=extra)
    Ao, mo, to, t0o, co = within(w, A0, 'R', 'Q', (rr, qr, r0, 'lt'), extra=extra)
    dss = w.s([w.s([rr, qr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, Ic)), a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, Ic))
    cn = CN(w, A0, 't', Ic, dss, cl, cc)
    gcn = cn(G); hcn = cn(H)
    # derivative on the open interval
    rrp = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    did = w.s([rrp], 'dvmptid', '( %s -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )' % A0)
    At_ = '( %s /\\ t e. RR )' % A0
    J = '( ( TopOpen ` CCfld ) |`t RR )'
    ej = w.s([], 'eqid', '%s = %s' % (J, J)); ek = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    yj = w.s([w.s([w.s([], 'iooretop', '%s e. ( topGen ` ran (,) )' % Io), w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % J)], 'eleqtri', '%s e. %s' % (Io, J))], 'a1i', '( %s -> %s e. %s )' % (A0, Io, J))
    dres = w.s([rrp, w.s([w.s([], 'simpr', '( %s -> t e. RR )' % At_)], 'recnd', '( %s -> t e. CC )' % At_), w.s([], '1cnd', '( %s -> 1 e. CC )' % At_), did,
                a1(w, A0, 'ioossre', '%s C_ RR' % Io), ej, ek, yj], 'dvmptres', '( %s -> ( RR _D ( t e. %s |-> t ) ) = ( t e. %s |-> 1 ) )' % (A0, Io, Io))
    tnz = w.s([co.mem('t', 'CC'), co.ne0('t')], 'eldifsnd', '( %s -> t e. ( CC \\ { 0 } ) )' % Ao)
    drec = w.s([rrp, a1(w, A0, 'neg1cn', '-u 1 e. CC'), tnz, w.s([], '1cnd', '( %s -> 1 e. CC )' % Ao), dres], 'dvrecg',
               '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> -u ( ( -u 1 x. 1 ) / ( t ^ 2 ) ) ) )' % (A0, Io, G, Io))
    k1 = dst(w, Ao, [a1(w, Ao, 'neg1cn', '-u 1 e. CC')], 'mulridd', '( -u 1 x. 1 ) = -u 1')
    k2 = dst(w, Ao, [dst(w, Ao, [k1], 'oveq1d', '( ( -u 1 x. 1 ) / ( t ^ 2 ) ) = ( -u 1 / ( t ^ 2 ) )')], 'negeqd', '-u ( ( -u 1 x. 1 ) / ( t ^ 2 ) ) = -u ( -u 1 / ( t ^ 2 ) )')
    k3 = dst(w, Ao, [a1(w, Ao, 'neg1cn', '-u 1 e. CC'), co.mem('( t ^ 2 )', 'CC'), co.ne0('( t ^ 2 )')], 'divnegd', '-u ( -u 1 / ( t ^ 2 ) ) = ( -u -u 1 / ( t ^ 2 ) )')
    k4 = dst(w, Ao, [dst(w, Ao, [w.s([], '1cnd', '( %s -> 1 e. CC )' % Ao)], 'negnegd', '-u -u 1 = 1')], 'oveq1d', '( -u -u 1 / ( t ^ 2 ) ) = %s' % H)
    kk = eqt(w, Ao, eqt(w, Ao, k2, k3), k4)
    dm = dst(w, A0, [kk], 'mpteq2dva', '( t e. %s |-> -u ( ( -u 1 x. 1 ) / ( t ^ 2 ) ) ) = ( t e. %s |-> %s )' % (Io, Io, H))
    dG = eqt(w, A0, drec, dm)
    e5 = w.s([w.s([], 'id', '( t = R -> t = R )')], 'oveq2d', '( t = R -> %s = ( -u 1 / R ) )' % G)
    e6 = w.s([w.s([], 'id', '( t = Q -> t = Q )')], 'oveq2d', '( t = Q -> %s = ( -u 1 / Q ) )' % G)
    ftc = w.s([w.s([rr, qr, rq], '3jca', '( %s -> ( R e. RR /\\ Q e. RR /\\ R <_ Q ) )' % A0), gcn, dG, hcn, e5, e6], 'ef1ftc',
              '( %s -> ( ( t e. %s |-> %s ) e. L^1 /\\ %s = ( ( -u 1 / Q ) - ( -u 1 / R ) ) ) )' % (A0, Io, H, ITG(Io, H)))
    hib = dst(w, A0, [ftc], 'simpld', '( t e. %s |-> %s ) e. L^1' % (Io, H))
    hval = dst(w, A0, [ftc], 'simprd', '%s = ( ( -u 1 / Q ) - ( -u 1 / R ) )' % ITG(Io, H))
    kib = dst(w, A0, [ap(w, A0, 'mvkibl', [J_(w, A0, J_(w, A0, ar, ar), J_(w, A0, rr, qr, r0e))],
                        '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (Io, KC('A', 'A'), Io, KQ('A')))], 'simprd', '( t e. %s |-> %s ) e. L^1' % (Io, KQ('A')))
    # pointwise KQ <_ H
    S = '( sin ` ( A x. t ) )'
    sb = ap(w, Ao, 'sinbnd', [co.mem('( A x. t )', 'RR')], '( -u 1 <_ %s /\\ %s <_ 1 )' % (S, S))
    sab = w.s([sb, w.s([co.mem(S, 'RR'), a1(w, Ao, '1re', '1 e. RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ 1 <-> ( -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (Ao, S, S, S))],
              'mpbird', '( %s -> ( abs ` %s ) <_ 1 )' % (Ao, S))
    sq = w.s([J_(w, Ao, co.mem('( abs ` %s )' % S, 'RR'), w.s([co.mem(S, 'CC')], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Ao, S))),
              J_(w, Ao, a1(w, Ao, '1re', '1 e. RR'), sab), w.inst('le2sq2')], 'syl2anc', '( %s -> ( ( abs ` %s ) ^ 2 ) <_ ( 1 ^ 2 ) )' % (Ao, S))
    ks1 = w.s([eqc(w, Ao, ap(w, Ao, 'absresq', [co.mem(S, 'RR')], '( ( abs ` %s ) ^ 2 ) = %s' % (S, KS('A')))), sq, a1(w, Ao, 'sq1', '( 1 ^ 2 ) = 1')] if False else
              [ap(w, Ao, 'absresq', [co.mem(S, 'RR')], '( ( abs ` %s ) ^ 2 ) = %s' % (S, KS('A'))), sq], 'eqbrtrrd', '( %s -> %s <_ ( 1 ^ 2 ) )' % (Ao, KS('A')))
    ks2 = w.s([ks1, a1(w, Ao, 'sq1', '( 1 ^ 2 ) = 1')], 'breqtrd', '( %s -> %s <_ 1 )' % (Ao, KS('A')))
    t2rp = w.s([co.mem('( t ^ 2 )', 'RR'), co.gt0('( t ^ 2 )')], 'elrpd', '( %s -> ( t ^ 2 ) e. RR+ )' % Ao)
    pw = w.s([co.mem(KS('A'), 'RR'), a1(w, Ao, '1re', '1 e. RR'), t2rp, ks2], 'lediv1dd', '( %s -> %s <_ %s )' % (Ao, KQ('A'), H))
    ile = w.s([kib, hib, co.mem(KQ('A'), 'RR'), co.mem(H, 'RR'), pw], 'itgle', '( %s -> %s <_ %s )' % (A0, ITG(Io, KQ('A')), ITG(Io, H)))
    # ( -u 1 / Q ) - ( -u 1 / R ) <_ 1 / R
    n1 = dst(w, A0, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), cl.mem('R', 'CC'), cl.ne0('R')], 'divnegd', '-u ( 1 / R ) = ( -u 1 / R )')
    n2 = dst(w, A0, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), cl.mem('Q', 'CC'), cl.ne0('Q')], 'divnegd', '-u ( 1 / Q ) = ( -u 1 / Q )')
    qpos = cl.gt0('( 1 / Q )')
    for t_ in ['( -u 1 / Q )', '( -u 1 / R )', ITG(Io, KQ('A')), ITG(Io, H)]:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR') if 'S.' not in t_ else (w.s([co.mem(KQ('A'), 'RR'), kib], 'itgrecl', '( %s -> %s e. RR )' % (A0, t_)) if KQ('A') in t_ else
                                                                  w.s([co.mem(H, 'RR'), hib], 'itgrecl', '( %s -> %s e. RR )' % (A0, t_))))
    linarith(w, A0, [ile, hval, n1, n2, qpos], '%s <_ ( 1 / R )' % ITG(Io, KQ('A')), closure=cl, name='qed')
    go(w)



def mvlim():
    w = W('mvlim', 'If X <_ Y + Z / n for every natural n >_ J then X <_ Y (the archimedean limit step replacing the whole-line integral).')
    Q = 'A. n e. NN ( J <_ n -> X <_ ( Y + ( Z / n ) ) )'
    A0 = '( ( X e. RR /\\ Y e. RR /\\ Z e. RR ) /\\ ( J e. RR /\\ %s ) )' % Q
    P = parts(w, A0)
    xr, yr, zr, jr, qa = P['X e. RR'], P['Y e. RR'], P['Z e. RR'], P['J e. RR'], P[Q]
    B = '( %s /\\ Y < X )' % A0
    yx = w.s([], 'simpr', '( %s -> Y < X )' % B)
    lv = {'X': ('RR', lift(w, xr, B)), 'Y': ('RR', lift(w, yr, B)), 'Z': ('RR', lift(w, zr, B)), 'J': ('RR', lift(w, jr, B))}
    cb = Closure(w, B, lv)
    d = '( X - Y )'
    dp = linarith(w, B, [yx], '0 < %s' % d, closure=cb)
    cb.leaf(d, 'gt0', dp)
    Aexp = '( ( abs ` J ) + ( ( abs ` Z ) / %s ) )' % d
    ex = ap(w, B, 'arch', [cb.mem(Aexp, 'RR')], 'E. m e. NN %s < m' % Aexp)
    C = '( ( %s /\\ m e. NN ) /\\ %s < m )' % (B, Aexp)
    mn = w.s([], 'simplr', '( %s -> m e. NN )' % C)
    am = w.s([], 'simpr', '( %s -> %s < m )' % (C, Aexp))
    lvc = dict((k, (kind, lift(w, s_, C))) for k, (kind, s_) in lv.items())
    lvc['m'] = ('NN', mn)
    cc = Closure(w, C, lvc)
    ccd = Closure(w, C, dict(lvc))
    ccd.leaf(d, 'gt0', lift(w, dp, C))
    AJ = '( abs ` J )'; AZ = '( abs ` Z )'
    aj0 = w.s([cc.mem('J', 'CC')], 'absge0d', '( %s -> 0 <_ %s )' % (C, AJ))
    az0 = w.s([cc.mem('Z', 'CC')], 'absge0d', '( %s -> 0 <_ %s )' % (C, AZ))
    jle = ap(w, C, 'leabs', [cc.mem('J', 'RR')], 'J <_ %s' % AJ)
    zle = ap(w, C, 'leabs', [cc.mem('Z', 'RR')], 'Z <_ %s' % AZ)
    for t_ in [AJ, AZ, '( %s / %s )' % (AZ, d)]:
        cc.leaf(t_, 'RR', ccd.mem(t_, 'RR'))
    zd0 = w.s([cc.mem(AZ, 'RR'), ccd.mem(d, 'RR+'), az0], 'divge0d', '( %s -> 0 <_ ( %s / %s ) )' % (C, AZ, d))
    jm = linarith(w, C, [am, jle, zd0], 'J <_ m', closure=cc)
    zdm = linarith(w, C, [am, aj0], '( %s / %s ) < m' % (AZ, d), closure=cc)
    # specialise the hypothesis at m
    ante = 'n = m'
    idst = w.s([], 'id', '( n = m -> n = m )')
    cst, new = w.wcongr('( J <_ n -> X <_ ( Y + ( Z / n ) ) )', {'n': 'm'}, ante, {'n': idst})
    sp = w.s([mn, lift(w, qa, C), w.s([cst], 'rspcv', '( m e. NN -> ( %s -> %s ) )' % (Q, new))], 'sylc', '( %s -> %s )' % (C, new))
    xle = w.s([jm, sp], 'mpd', '( %s -> X <_ ( Y + ( Z / m ) ) )' % C)
    mrp = cc.mem('m', 'RR+')
    z1 = w.s([cc.mem('Z', 'RR'), cc.mem(AZ, 'RR'), mrp, zle], 'lediv1dd', '( %s -> ( Z / m ) <_ ( %s / m ) )' % (C, AZ))
    b1 = w.s([cc.mem(AZ, 'RR'), cc.mem('m', 'RR'), ccd.mem(d, 'RR+')], 'ltdivmuld', '( %s -> ( ( %s / %s ) < m <-> %s < ( %s x. m ) ) )' % (C, AZ, d, AZ, d))
    b2 = w.s([zdm, b1], 'mpbid', '( %s -> %s < ( %s x. m ) )' % (C, AZ, d))
    b3 = w.s([cc.mem(AZ, 'RR'), cc.mem(d, 'RR'), mrp], 'ltdivmul2d', '( %s -> ( ( %s / m ) < %s <-> %s < ( %s x. m ) ) )' % (C, AZ, d, AZ, d))
    b4 = w.s([b2, b3], 'mpbird', '( %s -> ( %s / m ) < %s )' % (C, AZ, d))
    for t_ in ['( Z / m )', '( %s / m )' % AZ]:
        cc.leaf(t_, 'RR', cc.mem(t_, 'RR'))
    xx = linarith(w, C, [xle, z1, b4], 'X < X', closure=cc)
    imp = w.s([xx], 'ex', '( ( %s /\\ m e. NN ) -> ( %s < m -> X < X ) )' % (B, Aexp))
    r = w.s([imp], 'rexlimdva', '( %s -> ( E. m e. NN %s < m -> X < X ) )' % (B, Aexp))
    xxb = w.s([ex, r], 'mpd', '( %s -> X < X )' % B)
    nx = w.s([cb.mem('X', 'RR')], 'ltnrd', '( %s -> -. X < X )' % B)
    ny = w.s([xxb, nx], 'pm2.65da', '( %s -> -. Y < X )' % A0)
    w.s([ny, w.s([xr, yr], 'lenltd', '( %s -> ( X <_ Y <-> -. Y < X ) )' % A0)], 'mpbird', '( %s -> X <_ Y )' % A0)
    qedlast(w)
    go(w)


def sin2le1(w, ante, c, x):
    """( ante -> ( ( sin ` x ) ^ 2 ) <_ 1 ) and ( ante -> 0 <_ ... ) (closure c knows x real)"""
    S = '( sin ` %s )' % x
    sb = ap(w, ante, 'sinbnd', [c.mem(x, 'RR')], '( -u 1 <_ %s /\\ %s <_ 1 )' % (S, S))
    sab = w.s([sb, w.s([c.mem(S, 'RR'), a1(w, ante, '1re', '1 e. RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ 1 <-> ( -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (ante, S, S, S))],
              'mpbird', '( %s -> ( abs ` %s ) <_ 1 )' % (ante, S))
    sq = w.s([J(w, ante, c.mem('( abs ` %s )' % S, 'RR'), w.s([c.mem(S, 'CC')], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (ante, S))),
              J(w, ante, a1(w, ante, '1re', '1 e. RR'), sab), w.inst('le2sq2')], 'syl2anc', '( %s -> ( ( abs ` %s ) ^ 2 ) <_ ( 1 ^ 2 ) )' % (ante, S))
    k1 = w.s([ap(w, ante, 'absresq', [c.mem(S, 'RR')], '( ( abs ` %s ) ^ 2 ) = ( %s ^ 2 )' % (S, S)), sq], 'eqbrtrrd', '( %s -> ( %s ^ 2 ) <_ ( 1 ^ 2 ) )' % (ante, S))
    le = w.s([k1, a1(w, ante, 'sq1', '( 1 ^ 2 ) = 1')], 'breqtrd', '( %s -> ( %s ^ 2 ) <_ 1 )' % (ante, S))
    ge = w.s([c.mem(S, 'RR')], 'sqge0d', '( %s -> 0 <_ ( %s ^ 2 ) )' % (ante, S))
    return le, ge


def mvgn():
    w = W('mvgn', 'The Fejer integral at the special lengths N pi / ( 2 A ): A pi / 2 - 9 ( A / N ) ( pi / 2 ) <_ S. sin ^ 2 ( A t ) / t ^ 2 <_ A pi / 2 (mvfejint at C = A / N and mvsinb).')
    A0 = '( A e. RR+ /\\ N e. NN )'
    P = parts(w, A0)
    ap_, nn = P['A e. RR+'], P['N e. NN']
    cl = Closure(w, A0, {'A': ('RR+', ap_), 'N': ('NN', nn), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    C = '( A / N )'; Y = '( _pi / ( 2 x. %s ) )' % C; I = IOO('0', Y)
    cp = cl.mem(C, 'RR+')
    cl.leaf(C, 'RR+', cp)
    C2 = '( %s ^ 2 )' % C
    f1a = w.s([cl.mem('_pi', 'CC'), a1(w, A0, '2cn', '2 e. CC'), cl.mem(C, 'CC'), a1(w, A0, '2ne0', '2 =/= 0'), cl.ne0(C)], 'divdiv1d',
              '( %s -> ( ( _pi / 2 ) / %s ) = %s )' % (A0, C, Y))
    f1b = w.s([cl.mem('( _pi / 2 )', 'CC'), cl.mem(C, 'CC'), cl.ne0(C)], 'divcan2d', '( %s -> ( %s x. ( ( _pi / 2 ) / %s ) ) = ( _pi / 2 ) )' % (A0, C, C))
    f1 = w.s([dst(w, A0, [f1a], 'oveq2d', '( %s x. ( ( _pi / 2 ) / %s ) ) = ( %s x. %s )' % (C, C, C, Y)), f1b], 'eqtr3d', '( %s -> ( %s x. %s ) = ( _pi / 2 ) )' % (A0, C, Y))
    f2 = w.s([cl.mem('A', 'CC'), cl.mem('N', 'CC'), cl.ne0('N')], 'divcan2d', '( %s -> ( N x. %s ) = A )' % (A0, C))
    yr = cl.mem(Y, 'RR')
    # integrability and the Fejer value
    kq = dst(w, A0, [ap(w, A0, 'mvkibl', [J(w, A0, J(w, A0, cl.mem('A', 'RR'), cl.mem('A', 'RR')), J(w, A0, w.s([], '0red', '( %s -> 0 e. RR )' % A0), yr, w.s([], '0le0', '0 <_ 0') and a1(w, A0, '0le0', '0 <_ 0')))],
                                 '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (I, KC('A', 'A'), I, KQ('A')))], 'simprd', '( t e. %s |-> %s ) e. L^1' % (I, KQ('A')))
    PTt = PT('N', '( %s x. t )' % C)
    fj = ap(w, A0, 'mvfejint', [cp, cl.mem('N', 'NN0')], '( ( t e. %s |-> %s ) e. L^1 /\\ %s = ( N x. %s ) )' % (I, PTt, ITG(I, PTt), Y))
    pib = dst(w, A0, [fj], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, PTt))
    pval = dst(w, A0, [fj], 'simprd', '%s = ( N x. %s )' % (ITG(I, PTt), Y))
    # pointwise
    At = '( %s /\\ t e. %s )' % (A0, I)
    mt = w.s([], 'simpr', '( %s -> t e. %s )' % (At, I))
    tr = ap(w, At, 'elioore', [mt], 't e. RR')
    oo = ap(w, At, 'eliooord', [mt], '( 0 < t /\\ t < %s )' % Y)
    t0 = dst(w, At, [oo], 'simpld', '0 < t'); tY = dst(w, At, [oo], 'simprd', 't < %s' % Y)
    ct = Closure(w, At, {'A': ('RR+', lift(w, ap_, At)), 'N': ('NN', lift(w, nn, At)), C: ('RR+', lift(w, cp, At)), 't': [('RR', tr), ('gt0', t0)],
                         '_pi': ('RR+', a1(w, At, 'pirp', '_pi e. RR+'))})
    X = '( %s x. t )' % C
    x0 = ct.gt0(X)
    xlt = w.s([w.s([tr, ct.mem(Y, 'RR'), ct.mem(C, 'RR+')], 'ltmul2d', '( %s -> ( t < %s <-> %s < ( %s x. %s ) ) )' % (At, Y, X, C, Y)), tY], 'mpbid' if False else 'mpbird',
              '( %s -> %s < ( %s x. %s ) )' % (At, X, C, Y)) if False else \
        w.s([tY, w.s([tr, ct.mem(Y, 'RR'), ct.mem(C, 'RR+')], 'ltmul2d', '( %s -> ( t < %s <-> %s < ( %s x. %s ) ) )' % (At, Y, X, C, Y))], 'mpbid',
            '( %s -> %s < ( %s x. %s ) )' % (At, X, C, Y))
    xlt2 = w.s([xlt, lift(w, f1, At)], 'breqtrd', '( %s -> %s < ( _pi / 2 ) )' % (At, X))
    bi = w.s([a1(w, At, '0xr', '0 e. RR*'), w.s([ct.mem('( _pi / 2 )', 'RR')], 'rexrd', '( %s -> ( _pi / 2 ) e. RR* )' % At), w.inst('elioo2')], 'syl2anc',
             '( %s -> ( %s e. ( 0 (,) ( _pi / 2 ) ) <-> ( %s e. RR /\\ 0 < %s /\\ %s < ( _pi / 2 ) ) ) )' % (At, X, X, X, X))
    xm = w.s([w.s([ct.mem(X, 'RR'), x0, xlt2], '3jca', '( %s -> ( %s e. RR /\\ 0 < %s /\\ %s < ( _pi / 2 ) ) )' % (At, X, X, X)), bi], 'mpbird',
             '( %s -> %s e. ( 0 (,) ( _pi / 2 ) ) )' % (At, X))
    SX_ = '( sin ` %s )' % X; s_ = '( %s ^ 2 )' % SX_; X2 = '( %s ^ 2 )' % X
    sb = ap(w, At, 'mvsinb', [xm], '( 0 < %s /\\ %s < %s /\\ ( ( 1 / %s ) - ( 1 / %s ) ) <_ 9 )' % (SX_, SX_, X, s_, X2))
    sp = w.s([sb], 'simp1d', '( %s -> 0 < %s )' % (At, SX_)); sl = w.s([sb], 'simp2d', '( %s -> %s < %s )' % (At, SX_, X))
    s9 = w.s([sb], 'simp3d', '( %s -> ( ( 1 / %s ) - ( 1 / %s ) ) <_ 9 )' % (At, s_, X2))
    PX = PT('N', X)
    ss = ap(w, At, 'mvsinsq', [ct.mem('N', 'NN0'), ct.mem(X, 'CC')], '( ( sin ` ( N x. %s ) ) ^ 2 ) = ( %s x. %s )' % (X, s_, PX))
    nx1 = w.s([ct.mem('N', 'CC'), ct.mem(C, 'CC'), ct.mem('t', 'CC')], 'mulassd', '( %s -> ( ( N x. %s ) x. t ) = ( N x. %s ) )' % (At, C, X))
    nx = w.s([nx1, dst(w, At, [lift(w, f2, At)], 'oveq1d', '( ( N x. %s ) x. t ) = ( A x. t )' % C)], 'eqtr3d', '( %s -> ( N x. %s ) = ( A x. t ) )' % (At, X))
    q = KS('A')
    qe = eqt(w, At, eqc(w, At, dst(w, At, [dst(w, At, [nx], 'fveq2d', '( sin ` ( N x. %s ) ) = ( sin ` ( A x. t ) )' % X)], 'oveq1d',
                                      '( ( sin ` ( N x. %s ) ) ^ 2 ) = %s' % (X, q))), ss)          # q = s P
    ct.leaf(s_, 'RR+', w.s([w.s([ct.mem(SX_, 'RR'), w.s([sp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (At, SX_))], 'sqgt0d', '( %s -> 0 < %s )' % (At, s_)),
                            ct.mem(s_, 'RR') if False else w.s([ct.mem(SX_, 'RR')], 'resqcld', '( %s -> %s e. RR )' % (At, s_))][::-1], 'elrpd', '( %s -> %s e. RR+ )' % (At, s_)))
    ct.leaf(X2, 'RR+', ct.mem(X2, 'RR+'))
    q1, q0 = sin2le1(w, At, ct, '( A x. t )')
    sle = w.s([J(w, At, ct.mem(SX_, 'RR'), ltle(w, At, ct, sp)), J(w, At, ct.mem(X, 'RR'), ltle(w, At, ct, sl)), w.inst('le2sq2')], 'syl2anc', '( %s -> %s <_ %s )' % (At, s_, X2))
    u = '( %s / %s )' % (q, X2); v = '( %s / %s )' % (q, s_)
    uv = w.s([ct.mem(s_, 'RR+'), ct.mem(X2, 'RR+'), ct.mem(q, 'RR'), q0, sle], 'lediv2ad', '( %s -> %s <_ %s )' % (At, u, v))
    vP = w.s([dst(w, At, [qe], 'oveq1d', '%s = ( ( %s x. %s ) / %s )' % (v, s_, PX, s_)),
              w.s([ct.mem(PX, 'CC'), ct.mem(s_, 'CC'), ct.ne0(s_)], 'divcan3d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (At, s_, PX, s_, PX))], 'eqtrd', '( %s -> %s = %s )' % (At, v, PX))
    r1 = w.s([ct.mem(q, 'CC'), ct.mem(s_, 'CC'), ct.ne0(s_)], 'divrecd', '( %s -> %s = ( %s x. ( 1 / %s ) ) )' % (At, v, q, s_))
    r2 = w.s([ct.mem(q, 'CC'), ct.mem(X2, 'CC'), ct.ne0(X2)], 'divrecd', '( %s -> %s = ( %s x. ( 1 / %s ) ) )' % (At, u, q, X2))
    dd = '( ( 1 / %s ) - ( 1 / %s ) )' % (s_, X2)
    rc = Closure(w, At, {q: ('RR', ct.mem(q, 'RR')), '( 1 / %s )' % s_: ('RR', ct.mem('( 1 / %s )' % s_, 'RR')), '( 1 / %s )' % X2: ('RR', ct.mem('( 1 / %s )' % X2, 'RR'))})
    r3 = ringeq(w, At, '( ( %s x. ( 1 / %s ) ) - ( %s x. ( 1 / %s ) ) )' % (q, s_, q, X2), '( %s x. %s )' % (q, dd), rc)
    vu = w.s([dst(w, At, [r1, r2], 'oveq12d', '( %s - %s ) = ( ( %s x. ( 1 / %s ) ) - ( %s x. ( 1 / %s ) ) )' % (v, u, q, s_, q, X2)), r3], 'eqtrd',
             '( %s -> ( %s - %s ) = ( %s x. %s ) )' % (At, v, u, q, dd))
    rec = w.s([ct.mem(s_, 'RR+'), ct.mem(X2, 'RR+'), a1(w, At, '1re', '1 e. RR'), a1(w, At, '0le1', '0 <_ 1'), sle], 'lediv2ad', '( %s -> ( 1 / %s ) <_ ( 1 / %s ) )' % (At, X2, s_))
    ct.leaf('( 1 / %s )' % s_, 'RR', ct.mem('( 1 / %s )' % s_, 'RR')); ct.leaf('( 1 / %s )' % X2, 'RR', ct.mem('( 1 / %s )' % X2, 'RR'))
    d0 = linarith(w, At, [rec], '0 <_ %s' % dd, closure=ct)
    qd = w.s([ct.mem(q, 'RR'), a1(w, At, '1re', '1 e. RR'), ct.mem(dd, 'RR'), a1(w, At, '9re', '9 e. RR'), q0, d0, q1, s9], 'lemul12ad', '( %s -> ( %s x. %s ) <_ ( 1 x. 9 ) )' % (At, q, dd))
    # KQ = C^2 u
    sm = w.s([ct.mem(C, 'CC'), ct.mem('t', 'CC')], 'sqmuld', '( %s -> %s = ( %s x. ( t ^ 2 ) ) )' % (At, X2, C2))
    ct.leaf('( t ^ 2 )', 'RR+', ct.mem('( t ^ 2 )', 'RR+'))
    ct.leaf(C2, 'RR+', ct.mem(C2, 'RR+'))
    k1 = w.s([ct.mem(q, 'CC'), ct.mem('( t ^ 2 )', 'CC'), ct.mem(C2, 'CC'), ct.ne0('( t ^ 2 )'), ct.ne0(C2)], 'divdiv1d',
             '( %s -> ( ( %s / ( t ^ 2 ) ) / %s ) = ( %s / ( ( t ^ 2 ) x. %s ) ) )' % (At, q, C2, q, C2))
    k2 = w.s([ct.mem('( t ^ 2 )', 'CC'), ct.mem(C2, 'CC')], 'mulcomd', '( %s -> ( ( t ^ 2 ) x. %s ) = ( %s x. ( t ^ 2 ) ) )' % (At, C2, C2))
    k3 = eqt(w, At, k1, dst(w, At, [eqt(w, At, k2, eqc(w, At, sm))], 'oveq2d', '( %s / ( ( t ^ 2 ) x. %s ) ) = %s' % (q, C2, u)))
    k4 = w.s([ct.mem(KQ('A'), 'CC'), ct.mem(C2, 'CC'), ct.ne0(C2)], 'divcan2d', '( %s -> ( %s x. ( %s / %s ) ) = %s )' % (At, C2, KQ('A'), C2, KQ('A')))
    KQu = w.s([dst(w, At, [k3], 'oveq2d', '( %s x. ( %s / %s ) ) = ( %s x. %s )' % (C2, KQ('A'), C2, C2, u)), k4], 'eqtr3d', '( %s -> ( %s x. %s ) = %s )' % (At, C2, u, KQ('A')))
    CP = '( %s x. %s )' % (C2, PX)
    up = w.s([ct.mem(u, 'RR'), ct.mem(v, 'RR'), ct.mem(C2, 'RR'), w.s([ct.mem(C, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (At, C2)), uv], 'lemul2ad',
             '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (At, C2, u, C2, v))
    cv = dst(w, At, [vP], 'oveq2d', '( %s x. %s ) = %s' % (C2, v, CP))
    for t_ in ['( %s x. %s )' % (C2, u), '( %s x. %s )' % (C2, v), CP, KQ('A'), '( %s x. %s )' % (q, dd)]:
        ct.leaf(t_, 'RR', ct.mem(t_, 'RR'))
    pw1 = linarith(w, At, [up, cv, KQu], '%s <_ %s' % (KQ('A'), CP), closure=ct)
    vu9 = linarith(w, At, [vu, qd], '( %s - %s ) <_ 9' % (v, u), closure=ct)
    m9 = w.s([ct.mem('( %s - %s )' % (v, u), 'RR'), a1(w, At, '9re', '9 e. RR'), ct.mem(C2, 'RR'), w.s([ct.mem(C, 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (At, C2)), vu9],
             'lemul2ad', '( %s -> ( %s x. ( %s - %s ) ) <_ ( %s x. 9 ) )' % (At, C2, v, u, C2))
    rcc = Closure(w, At, {C2: ('RR', ct.mem(C2, 'RR')), u: ('RR', ct.mem(u, 'RR')), v: ('RR', ct.mem(v, 'RR'))})
    m9e = ringeq(w, At, '( %s x. ( %s - %s ) )' % (C2, v, u), '( ( %s x. %s ) - ( %s x. %s ) )' % (C2, v, C2, u), rcc)
    ct.leaf('( %s x. ( %s - %s ) )' % (C2, v, u), 'RR', ct.mem('( %s x. ( %s - %s ) )' % (C2, v, u), 'RR'))
    NC = '( 9 x. %s )' % C2
    pw2 = linarith(w, At, [m9, m9e, cv, KQu], '( %s - %s ) <_ %s' % (CP, NC, KQ('A')), closure=ct)
    # integrals
    c2c = cl.mem(C2, 'CC')
    ctp = Closure(w, At, {C: ('RR+', lift(w, cp, At)), 't': ('RR', tr), 'N': ('NN', lift(w, nn, At))})
    pc = ctp.mem(PTt, 'CC')
    ibCP = w.s([c2c, pc, pib], 'iblmulc2', '( %s -> ( t e. %s |-> ( %s x. %s ) ) e. L^1 )' % (A0, I, C2, PTt))
    # X is ( C x. t ): PX and PTt are the same text
    assert PX == PTt
    i1 = w.s([kq, ibCP, ct.mem(KQ('A'), 'RR'), ct.mem(CP, 'RR'), pw1], 'itgle', '( %s -> %s <_ %s )' % (A0, ITG(I, KQ('A')), ITG(I, CP)))
    i2 = w.s([c2c, pc, pib], 'itgmulc2', '( %s -> ( %s x. %s ) = %s )' % (A0, C2, ITG(I, PTt), ITG(I, CP)))
    ICP = eqt(w, A0, eqc(w, A0, i2), dst(w, A0, [pval], 'oveq2d', '( %s x. %s ) = ( %s x. ( N x. %s ) )' % (C2, ITG(I, PTt), C2, Y)))
    Amt = '( %s /\\ t e. RR )' % A0
    cmt = Closure(w, Amt, {'t': ('RR', w.s([], 'simpr', '( %s -> t e. RR )' % Amt)), C: ('RR+', lift(w, cp, Amt))})
    cnn = CN(w, A0, 't', 'RR', a1(w, A0, 'ax-resscn', 'RR C_ CC'), cl, cmt)
    ib9 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), yr, cnn(NC)], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, I, NC))
    n9c = ct.mem(NC, 'CC')
    ibd = w.s([ct.mem(CP, 'CC'), ibCP, n9c, ib9], 'iblsub', '( %s -> ( t e. %s |-> ( %s - %s ) ) e. L^1 )' % (A0, I, CP, NC))
    i3 = w.s([ibd, kq, ct.mem('( %s - %s )' % (CP, NC), 'RR'), ct.mem(KQ('A'), 'RR'), pw2], 'itgle', '( %s -> %s <_ %s )' % (A0, ITG(I, '( %s - %s )' % (CP, NC)), ITG(I, KQ('A'))))
    i4 = w.s([ct.mem(CP, 'CC'), ibCP, n9c, ib9], 'itgsub', '( %s -> %s = ( %s - %s ) )' % (A0, ITG(I, '( %s - %s )' % (CP, NC)), ITG(I, CP), ITG(I, NC)))
    ioo = a1(w, A0, 'ioombl', '%s e. dom vol' % I)
    y0 = cl.ge0(Y)
    vol = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), yr, y0, w.inst('volioo')], 'syl3anc', '( %s -> ( vol ` %s ) = ( %s - 0 ) )' % (A0, I, Y))
    vol2 = eqt(w, A0, vol, dst(w, A0, [cl.mem(Y, 'CC')], 'subid1d', '( %s - 0 ) = %s' % (Y, Y)))
    volr = w.s([vol2, yr], 'eqeltrd', '( %s -> ( vol ` %s ) e. RR )' % (A0, I))
    ic = w.s([ioo, volr, cl.mem(NC, 'CC'), w.inst('itgconst')], 'syl3anc', '( %s -> %s = ( %s x. ( vol ` %s ) ) )' % (A0, ITG(I, NC), NC, I))
    ic2 = eqt(w, A0, ic, dst(w, A0, [vol2], 'oveq2d', '( %s x. ( vol ` %s ) ) = ( %s x. %s )' % (NC, I, NC, Y)))
    # arithmetic
    ac = Closure(w, A0, {C: ('RR', cl.mem(C, 'RR')), 'N': ('RR', cl.mem('N', 'RR')), Y: ('RR', yr), 'A': ('RR', cl.mem('A', 'RR')), '_pi': ('RR', cl.mem('_pi', 'RR'))})
    ar1 = ringeq(w, A0, '( %s x. ( N x. %s ) )' % (C2, Y), '( ( N x. %s ) x. ( %s x. %s ) )' % (C, C, Y), ac) if False else \
        ringeqp(w, A0, '( %s x. ( N x. %s ) )' % (C2, Y), '( ( N x. %s ) x. ( %s x. %s ) )' % (C, C, Y), ac)
    ar2 = dst(w, A0, [f2, f1], 'oveq12d', '( ( N x. %s ) x. ( %s x. %s ) ) = ( A x. ( _pi / 2 ) )' % (C, C, Y))
    ar3 = ringeq(w, A0, '( A x. ( _pi / 2 ) )', GA('A'), ac)
    VAL = eqt(w, A0, eqt(w, A0, ar1, ar2), ar3)          # C^2 ( N Y ) = A pi / 2
    br1 = ringeqp(w, A0, '( %s x. %s )' % (NC, Y), '( 9 x. ( %s x. ( %s x. %s ) ) )' % (C, C, Y), ac)
    br2 = dst(w, A0, [dst(w, A0, [f1], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( _pi / 2 ) )' % (C, C, Y, C))], 'oveq2d',
              '( 9 x. ( %s x. ( %s x. %s ) ) ) = ( 9 x. ( %s x. ( _pi / 2 ) ) )' % (C, C, Y, C))
    ERR = eqt(w, A0, br1, br2)
    GI = ITG(I, KQ('A'))
    cl.leaf(GI, 'RR', w.s([ct.mem(KQ('A'), 'RR'), kq], 'itgrecl', '( %s -> %s e. RR )' % (A0, GI)))
    for t_, ib, E in [(ITG(I, CP), ibCP, CP), (ITG(I, '( %s - %s )' % (CP, NC)), ibd, '( %s - %s )' % (CP, NC)), (ITG(I, NC), ib9, NC)]:
        cl.leaf(t_, 'RR', w.s([ct.mem(E, 'RR'), ib], 'itgrecl', '( %s -> %s e. RR )' % (A0, t_)))
    for t_ in ['( %s x. ( N x. %s ) )' % (C2, Y), '( %s x. %s )' % (NC, Y), '( 9 x. ( %s x. ( _pi / 2 ) ) )' % C, GA('A')]:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR'))
    up = linarith(w, A0, [i1, ICP, VAL], '%s <_ %s' % (GI, GA('A')), closure=cl)
    lo = linarith(w, A0, [i3, i4, ic2, ERR, ICP, VAL], '( %s - ( 9 x. ( %s x. ( _pi / 2 ) ) ) ) <_ %s' % (GA('A'), C, GI), closure=cl)
    # the interval ( 0 , N pi / ( 2 A ) )
    Y2 = '( ( N x. _pi ) / ( 2 x. A ) )'
    d1 = w.s([a1(w, A0, '2cn', '2 e. CC'), cl.mem('A', 'CC'), cl.mem('N', 'CC'), cl.ne0('N')], 'divassd', '( %s -> ( ( 2 x. A ) / N ) = ( 2 x. %s ) )' % (A0, C))
    d2 = w.s([cl.mem('_pi', 'CC'), cl.mem('( 2 x. A )', 'CC'), cl.mem('N', 'CC'), cl.ne0('( 2 x. A )'), cl.ne0('N')], 'divdiv2d',
             '( %s -> ( _pi / ( ( 2 x. A ) / N ) ) = ( ( _pi x. N ) / ( 2 x. A ) ) )' % A0)
    d3 = dst(w, A0, [w.s([cl.mem('_pi', 'CC'), cl.mem('N', 'CC')], 'mulcomd', '( %s -> ( _pi x. N ) = ( N x. _pi ) )' % A0)], 'oveq1d',
             '( ( _pi x. N ) / ( 2 x. A ) ) = %s' % Y2)
    yy = eqt(w, A0, eqt(w, A0, dst(w, A0, [eqc(w, A0, d1)], 'oveq2d', '%s = ( _pi / ( ( 2 x. A ) / N ) )' % Y), d2), d3)
    ii = dst(w, A0, [yy], 'oveq2d', '%s = %s' % (I, IOO('0', Y2)))
    GI2 = ITG(IOO('0', Y2), KQ('A'))
    ge = w.s([ii], 'itgeq1d' if False else 'id', 'x') if False else w.s([ii, w.inst('itgeq1')], 'syl', '( %s -> %s = %s )' % (A0, GI, GI2))
    lo2 = w.s([lo, ge], 'breqtrd', '( %s -> ( %s - ( 9 x. ( %s x. ( _pi / 2 ) ) ) ) <_ %s )' % (A0, GA('A'), C, GI2))
    up2 = w.s([ge, up], 'eqbrtrrd', '( %s -> %s <_ %s )' % (A0, GI2, GA('A')))
    J(w, A0, lo2, up2)
    qedlast(w)
    go(w)


def kqpt(w, ante, v, lo, hi, ar, lo0, lo_lt=False):
    """under ( ante /\\ v e. ( lo (,) hi ) ) with 0 <_ lo: KQ(A) real and nonnegative, and the closure"""
    I = IOO(lo, hi)
    Av = '( %s /\\ %s e. %s )' % (ante, v, I)
    m = w.s([], 'simpr', '( %s -> %s e. %s )' % (Av, v, I))
    vr = ap(w, Av, 'elioore', [m], '%s e. RR' % v)
    oo = ap(w, Av, 'eliooord', [m], '( %s < %s /\\ %s < %s )' % (lo, v, v, hi))
    return Av, m, vr, oo


def mvgr():
    w = W('mvgr', 'A pi / 2 - 1 / R <_ S. ( 0 (,) R ) sin ^ 2 ( A t ) / t ^ 2 <_ A pi / 2 for every R > 0 (mvgn at N pi / ( 2 A ) >_ R, mvtail, mvlim).')
    A0 = '( A e. RR+ /\\ R e. RR+ )'
    P = parts(w, A0)
    ap_, rp = P['A e. RR+'], P['R e. RR+']
    cl = Closure(w, A0, {'A': ('RR+', ap_), 'R': ('RR+', rp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    Jx = '( ( 2 x. ( A x. R ) ) / _pi )'
    G = ITG(IOO('0', 'R'), KQ('A'))
    Z = '( 9 x. ( A x. ( _pi / 2 ) ) )'
    B = '( ( %s /\\ n e. NN ) /\\ %s <_ n )' % (A0, Jx)
    nn = w.s([], 'simplr', '( %s -> n e. NN )' % B)
    jn = w.s([], 'simpr', '( %s -> %s <_ n )' % (B, Jx))
    cb = Closure(w, B, {'A': ('RR+', lift(w, ap_, B)), 'R': ('RR+', lift(w, rp, B)), 'n': ('NN', nn), '_pi': ('RR+', a1(w, B, 'pirp', '_pi e. RR+'))})
    Rn = '( ( n x. _pi ) / ( 2 x. A ) )'
    g1 = ap(w, B, 'mvgn', [cb.mem('A', 'RR+'), nn], '( ( %s - ( 9 x. ( ( A / n ) x. ( _pi / 2 ) ) ) ) <_ %s /\\ %s <_ %s )' % (
        GA('A'), ITG(IOO('0', Rn), KQ('A')), ITG(IOO('0', Rn), KQ('A')), GA('A')))
    g1l = dst(w, B, [g1], 'simpld', '( %s - ( 9 x. ( ( A / n ) x. ( _pi / 2 ) ) ) ) <_ %s' % (GA('A'), ITG(IOO('0', Rn), KQ('A'))))
    g1u = dst(w, B, [g1], 'simprd', '%s <_ %s' % (ITG(IOO('0', Rn), KQ('A')), GA('A')))
    # R <_ Rn
    b1 = w.s([cb.mem('( 2 x. ( A x. R ) )', 'RR'), cb.mem('n', 'RR'), cb.mem('_pi', 'RR+')], 'ledivmuld',
             '( %s -> ( ( %s <_ n ) <-> ( 2 x. ( A x. R ) ) <_ ( _pi x. n ) ) )' % (B, Jx)) if False else \
        w.s([cb.mem('( 2 x. ( A x. R ) )', 'RR'), cb.mem('n', 'RR'), cb.mem('_pi', 'RR+')], 'ledivmuld',
            '( %s -> ( %s <_ n <-> ( 2 x. ( A x. R ) ) <_ ( _pi x. n ) ) )' % (B, Jx))
    b2 = w.s([jn, b1], 'mpbid', '( %s -> ( 2 x. ( A x. R ) ) <_ ( _pi x. n ) )' % B)
    rc = Closure(w, B, {'A': ('RR', cb.mem('A', 'RR')), 'R': ('RR', cb.mem('R', 'RR')), 'n': ('RR', cb.mem('n', 'RR')), '_pi': ('RR', cb.mem('_pi', 'RR'))})
    e1 = ringeq(w, B, '( ( 2 x. A ) x. R )', '( 2 x. ( A x. R ) )', rc)
    e2 = ringeq(w, B, '( _pi x. n )', '( n x. _pi )', rc)
    b3 = w.s([e1, b2, e2], '3brtr4d' if False else 'id', 'x') if False else None
    b3 = w.s([w.s([e1, b2], 'eqbrtrd', '( %s -> ( ( 2 x. A ) x. R ) <_ ( _pi x. n ) )' % B), e2], 'breqtrd', '( %s -> ( ( 2 x. A ) x. R ) <_ ( n x. _pi ) )' % B)
    b4 = w.s([cb.mem('R', 'RR'), cb.mem('( n x. _pi )', 'RR'), cb.mem('( 2 x. A )', 'RR+')], 'lemuldiv2d',
             '( %s -> ( ( ( 2 x. A ) x. R ) <_ ( n x. _pi ) <-> R <_ %s ) )' % (B, Rn))
    rle = w.s([b3, b4], 'mpbid', '( %s -> R <_ %s )' % (B, Rn))
    # split ( 0 , Rn ) at R
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % B)
    rnr = cb.mem(Rn, 'RR')
    bi = w.s([z0, rnr, w.inst('elicc2')], 'syl2anc', '( %s -> ( R e. ( 0 [,] %s ) <-> ( R e. RR /\\ 0 <_ R /\\ R <_ %s ) ) )' % (B, Rn, Rn))
    rm = w.s([w.s([cb.mem('R', 'RR'), cb.ge0('R'), rle], '3jca', '( %s -> ( R e. RR /\\ 0 <_ R /\\ R <_ %s ) )' % (B, Rn)), bi], 'mpbird', '( %s -> R e. ( 0 [,] %s ) )' % (B, Rn))
    def kib(lo, hi, lor, hir, lo0):
        return dst(w, B, [ap(w, B, 'mvkibl', [J(w, B, J(w, B, cb.mem('A', 'RR'), cb.mem('A', 'RR')), J(w, B, lor, hir, lo0))],
                            '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (IOO(lo, hi), KC('A', 'A'), IOO(lo, hi), KQ('A')))], 'simprd',
                   '( t e. %s |-> %s ) e. L^1' % (IOO(lo, hi), KQ('A')))
    k1 = kib('0', 'R', z0, cb.mem('R', 'RR'), a1(w, B, '0le0', '0 <_ 0'))
    k2 = kib('R', Rn, cb.mem('R', 'RR'), rnr, cb.ge0('R'))
    Aw, mw, wr, oow = kqpt(w, B, 't', '0', Rn, None, None)
    t0 = dst(w, Aw, [oow], 'simpld', '0 < t')
    cw = Closure(w, Aw, {'A': ('RR', lift(w, cb.mem('A', 'RR'), Aw)), 't': [('RR', wr), ('gt0', t0)]})
    sp = w.s([z0, rnr, rm, cw.mem(KQ('A'), 'CC'), k1, k2], 'itgsplitioo',
             '( %s -> %s = ( %s + %s ) )' % (B, ITG(IOO('0', Rn), KQ('A')), G, ITG(IOO('R', Rn), KQ('A'))))
    tb = ap(w, B, 'mvtail', [J(w, B, cb.mem('A', 'RR'), J(w, B, cb.mem('R', 'RR+'), rnr, rle))], '%s <_ ( 1 / R )' % ITG(IOO('R', Rn), KQ('A')))
    Av2, m2, t2r, oo2 = kqpt(w, B, 't', 'R', Rn, None, None)
    c2 = Closure(w, Av2, {'A': ('RR', lift(w, cb.mem('A', 'RR'), Av2)), 't': ('RR', t2r)})
    kq2r = c2.mem(KQ('A'), 'RR') if False else None
    t2p = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % Av2), lift(w, cb.mem('R', 'RR'), Av2), t2r, lift(w, cb.gt0('R'), Av2), dst(w, Av2, [oo2], 'simpld', 'R < t')],
              'lttrd', '( %s -> 0 < t )' % Av2)
    c2.leaf('t', 'gt0', t2p)
    tg = w.s([k2, c2.mem(KQ('A'), 'RR'), w.s([c2.mem(KS('A'), 'RR'), c2.mem('( t ^ 2 )', 'RR+'),
                                            w.s([c2.mem('( sin ` ( A x. t ) )', 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (Av2, KS('A')))], 'divge0d', '( %s -> 0 <_ %s )' % (Av2, KQ('A')))],
             'itgge0', '( %s -> 0 <_ %s )' % (B, ITG(IOO('R', Rn), KQ('A'))))
    # arithmetic of the error: 9 ( ( A / n ) ( pi / 2 ) ) = Z / n
    d1 = w.s([cb.mem('A', 'CC'), cb.mem('( _pi / 2 )', 'CC'), cb.mem('n', 'CC'), cb.ne0('n')], 'div23d',
             '( %s -> ( ( A x. ( _pi / 2 ) ) / n ) = ( ( A / n ) x. ( _pi / 2 ) ) )' % B)
    d2 = w.s([a1(w, B, '9cn', '9 e. CC'), cb.mem('( A x. ( _pi / 2 ) )', 'CC'), cb.mem('n', 'CC'), cb.ne0('n')], 'divassd',
             '( %s -> ( ( 9 x. ( A x. ( _pi / 2 ) ) ) / n ) = ( 9 x. ( ( A x. ( _pi / 2 ) ) / n ) ) )' % B)
    dz = eqt(w, B, d2, dst(w, B, [d1], 'oveq2d', '( 9 x. ( ( A x. ( _pi / 2 ) ) / n ) ) = ( 9 x. ( ( A / n ) x. ( _pi / 2 ) ) )'))
    GI = G
    kr1 = w.s([cw.mem(KQ('A'), 'RR') if False else None][:0] + [lift(w, cb.mem('A', 'RR'), B)], 'id', 'x') if False else None
    A01 = '( %s /\\ t e. %s )' % (B, IOO('0', 'R'))
    m01 = w.s([], 'simpr', '( %s -> t e. %s )' % (A01, IOO('0', 'R')))
    t01 = ap(w, A01, 'elioore', [m01], 't e. RR')
    t01p = dst(w, A01, [ap(w, A01, 'eliooord', [m01], '( 0 < t /\\ t < R )')], 'simpld', '0 < t')
    c01 = Closure(w, A01, {'A': ('RR', lift(w, cb.mem('A', 'RR'), A01)), 't': [('RR', t01), ('gt0', t01p)]})
    for t_, ib, cc_ in [(G, k1, c01), (ITG(IOO('R', Rn), KQ('A')), k2, c2), (ITG(IOO('0', Rn), KQ('A')), None, cw)]:
        if ib is None:
            continue
        cb.leaf(t_, 'RR', w.s([cc_.mem(KQ('A'), 'RR'), ib], 'itgrecl', '( %s -> %s e. RR )' % (B, t_)))
    GRn = ITG(IOO('0', Rn), KQ('A'))
    cb.leaf(GRn, 'RR', w.s([sp, cb.mem('( %s + %s )' % (G, ITG(IOO('R', Rn), KQ('A'))), 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (B, GRn)))
    for t_ in ['( 9 x. ( ( A / n ) x. ( _pi / 2 ) ) )', '( %s / n )' % Z, '( 1 / R )', GA('A')]:
        cb.leaf(t_, 'RR', cb.mem(t_, 'RR'))
    upB = linarith(w, B, [sp, tg, g1u], '%s <_ %s' % (G, GA('A')), closure=cb)
    loB = linarith(w, B, [sp, tb, g1l, dz], '( %s - ( 1 / R ) ) <_ ( %s + ( %s / n ) )' % (GA('A'), G, Z), closure=cb)
    # the limit
    A0n = '( %s /\\ n e. NN )' % A0
    ra = w.s([w.s([loB], 'ex', '( %s -> ( %s <_ n -> ( %s - ( 1 / R ) ) <_ ( %s + ( %s / n ) ) ) )' % (A0n, Jx, GA('A'), G, Z))], 'ralrimiva',
             '( %s -> A. n e. NN ( %s <_ n -> ( %s - ( 1 / R ) ) <_ ( %s + ( %s / n ) ) ) )' % (A0, Jx, GA('A'), G, Z))
    Aq = '( %s /\\ t e. %s )' % (A0, IOO('0', 'R'))
    mq = w.s([], 'simpr', '( %s -> t e. %s )' % (Aq, IOO('0', 'R')))
    tq = ap(w, Aq, 'elioore', [mq], 't e. RR')
    tqp = dst(w, Aq, [ap(w, Aq, 'eliooord', [mq], '( 0 < t /\\ t < R )')], 'simpld', '0 < t')
    cq = Closure(w, Aq, {'A': ('RR+', lift(w, ap_, Aq)), 't': [('RR', tq), ('gt0', tqp)]})
    k10 = dst(w, A0, [ap(w, A0, 'mvkibl', [J(w, A0, J(w, A0, cl.mem('A', 'RR'), cl.mem('A', 'RR')), J(w, A0, w.s([], '0red', '( %s -> 0 e. RR )' % A0), cl.mem('R', 'RR'), a1(w, A0, '0le0', '0 <_ 0')))],
                                  '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (IOO('0', 'R'), KC('A', 'A'), IOO('0', 'R'), KQ('A')))], 'simprd',
              '( t e. %s |-> %s ) e. L^1' % (IOO('0', 'R'), KQ('A')))
    gr = w.s([cq.mem(KQ('A'), 'RR'), k10], 'itgrecl', '( %s -> %s e. RR )' % (A0, G))
    lim = ap(w, A0, 'mvlim', [J(w, A0, J(w, A0, cl.mem('( %s - ( 1 / R ) )' % GA('A'), 'RR'), gr, cl.mem(Z, 'RR')), J(w, A0, cl.mem(Jx, 'RR'), ra))],
             '( %s - ( 1 / R ) ) <_ %s' % (GA('A'), G))
    # the upper bound through one n > J
    ar = ap(w, A0, 'arch', [cl.mem(Jx, 'RR')], 'E. n e. NN %s < n' % Jx)
    Bn = '( ( %s /\\ n e. NN ) /\\ %s < n )' % (A0, Jx)
    lt = w.s([], 'simpr', '( %s -> %s < n )' % (Bn, Jx))
    cbn = Closure(w, Bn, {'A': ('RR+', lift(w, ap_, Bn)), 'R': ('RR+', lift(w, rp, Bn)), 'n': ('NN', w.s([], 'simplr', '( %s -> n e. NN )' % Bn)),
                          '_pi': ('RR+', a1(w, Bn, 'pirp', '_pi e. RR+'))})
    le_ = ltle(w, Bn, cbn, lt)
    upn = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Bn, A0n)), le_], 'jca', '( %s -> %s )' % (Bn, B)), w.s([upB], 'id', '( %s -> %s <_ %s )' % (B, G, GA('A'))) if False else upB],
              'syl', '( %s -> %s <_ %s )' % (Bn, G, GA('A')))
    upr = w.s([w.s([upn], 'ex', '( %s -> ( %s < n -> %s <_ %s ) )' % (A0n, Jx, G, GA('A')))], 'rexlimdva', '( %s -> ( E. n e. NN %s < n -> %s <_ %s ) )' % (A0, Jx, G, GA('A')))
    up = w.s([ar, upr], 'mpd', '( %s -> %s <_ %s )' % (A0, G, GA('A')))
    J(w, A0, lim, up)
    qedlast(w)
    go(w)

def J_(w, ante, *steps):
    return J(w, ante, *steps)


if __name__ == '__main__':
    mvtail()
    mvlim()
    mvgn()
    mvgr()
