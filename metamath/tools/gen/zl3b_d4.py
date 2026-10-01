"""ZL3b D4-D6: the sides of R_N and the limit N -> oo; zl3pois.
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_d4.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of, twopi, TP, MP
from zl3b_d2 import cst, reim_cp, cpcl
from zl3b_d3 import pteq, lieq

only = sys.argv[1:]
S = STATEMENTS


def chain_eq(w, A, first, steps):
    """steps: list of (step, rhs); first: lhs text; returns final eq step ( A -> first = last_rhs )"""
    cur, cur_rhs = steps[0]
    for st, rhs in steps[1:]:
        cur = D(w, A, 'eqtrd', [cur, st], '%s = %s' % (first, rhs))
        cur_rhs = rhs
    return cur


# ---------------------------------------------------------------- zl3kb
if __name__ == '__main__' and (not only or 'zl3kb' in only):
    w = W('zl3kb', 'On the lines ` Im w e. ZZ + 1 / 2 ` the kernel ` 1 / ( e ^ ( 2 pi w ) - 1 ) ` is bounded by ` 1 `.')
    ph, concl = ante_of(S['zl3kb'])
    ac = w.s([], 'simpl', '( %s -> A e. CC )' % ph)
    mz = w.s([], 'simpr', '( %s -> ( ( Im ` A ) - ( 1 / 2 ) ) e. ZZ )' % ph)
    X = '( Re ` A )'; Yv = '( Im ` A )'; m = '( ( Im ` A ) - ( 1 / 2 ) )'
    xr = D(w, ph, 'recld', [ac], '%s e. RR' % X); yr = D(w, ph, 'imcld', [ac], '%s e. RR' % Yv)
    xc = D(w, ph, 'recnd', [xr], '%s e. CC' % X); yc = D(w, ph, 'recnd', [yr], '%s e. CC' % Yv)
    mc = D(w, ph, 'zcnd', [mz], '%s e. CC' % m)
    tc, tn = twopi(w, ph)
    ic = cst(w, ph, 'ax-icn', '_i e. CC'); hc = cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC'); pc = cst(w, ph, 'picn', '_pi e. CC')
    TX = '( %s x. %s )' % (TP, X); TY = '( %s x. %s )' % (TP, Yv); TM = '( %s x. %s )' % (TP, m); IT = '( _i x. %s )' % TP
    s1 = D(w, ph, 'oveq2d', [D(w, ph, 'replimd', [ac], 'A = ( %s + ( _i x. %s ) )' % (X, Yv))], '( %s x. A ) = ( %s x. ( %s + ( _i x. %s ) ) )' % (TP, TP, X, Yv))
    iyc = D(w, ph, 'mulcld', [ic, yc], '( _i x. %s ) e. CC' % Yv)
    s2 = D(w, ph, 'adddid', [tc, xc, iyc], '( %s x. ( %s + ( _i x. %s ) ) ) = ( %s + ( %s x. ( _i x. %s ) ) )' % (TP, X, Yv, TX, TP, Yv))
    s3 = D(w, ph, 'mul12d', [tc, ic, yc], '( %s x. ( _i x. %s ) ) = ( _i x. %s )' % (TP, Yv, TY))
    y1 = D(w, ph, 'eqcomd', [D(w, ph, 'npcand', [yc, hc], '( %s + ( 1 / 2 ) ) = %s' % (m, Yv))], '%s = ( %s + ( 1 / 2 ) )' % (Yv, m))
    s4 = D(w, ph, 'oveq2d', [y1], '%s = ( %s x. ( %s + ( 1 / 2 ) ) )' % (TY, TP, m))
    s5 = D(w, ph, 'adddid', [tc, mc, hc], '( %s x. ( %s + ( 1 / 2 ) ) ) = ( %s + ( %s x. ( 1 / 2 ) ) )' % (TP, m, TM, TP))
    c2 = cst(w, ph, '2cn', '2 e. CC')
    h1 = D(w, ph, 'mul32d', [c2, pc, hc], '( %s x. ( 1 / 2 ) ) = ( ( 2 x. ( 1 / 2 ) ) x. _pi )' % TP)
    h2 = D(w, ph, 'oveq1d', [w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0'), w.inst('recidi')], 'a1i', '( %s -> ( 2 x. ( 1 / 2 ) ) = 1 )' % ph) if False else
                             cst(w, ph, 'recidi', '( 2 x. ( 1 / 2 ) ) = 1') if False else
                             w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'recidi', '( 2 x. ( 1 / 2 ) ) = 1')], 'a1i', '( %s -> ( 2 x. ( 1 / 2 ) ) = 1 )' % ph)],
            '( ( 2 x. ( 1 / 2 ) ) x. _pi ) = ( 1 x. _pi )')
    h3 = D(w, ph, 'mullidd', [pc], '( 1 x. _pi ) = _pi')
    hp = chain_eq(w, ph, '( %s x. ( 1 / 2 ) )' % TP, [(h1, '( ( 2 x. ( 1 / 2 ) ) x. _pi )'), (h2, '( 1 x. _pi )'), (h3, '_pi')])
    s6 = chain_eq(w, ph, TY, [(s4, '( %s x. ( %s + ( 1 / 2 ) ) )' % (TP, m)), (s5, '( %s + ( %s x. ( 1 / 2 ) ) )' % (TM, TP)),
                             (D(w, ph, 'oveq2d', [hp], '( %s + ( %s x. ( 1 / 2 ) ) ) = ( %s + _pi )' % (TM, TP, TM)), '( %s + _pi )' % TM)])
    tmc = D(w, ph, 'mulcld', [tc, mc], '%s e. CC' % TM)
    s7 = D(w, ph, 'oveq2d', [s6], '( _i x. %s ) = ( _i x. ( %s + _pi ) )' % (TY, TM))
    s8 = D(w, ph, 'adddid', [ic, tmc, pc], '( _i x. ( %s + _pi ) ) = ( ( _i x. %s ) + ( _i x. _pi ) )' % (TM, TM))
    s9 = D(w, ph, 'eqcomd', [D(w, ph, 'mulassd', [ic, tc, mc], '( ( _i x. %s ) x. %s ) = ( _i x. %s )' % (TP, m, TM))], '( _i x. %s ) = ( %s x. %s )' % (TM, IT, m))
    s10 = D(w, ph, 'oveq1d', [s9], '( ( _i x. %s ) + ( _i x. _pi ) ) = ( ( %s x. %s ) + ( _i x. _pi ) )' % (TM, IT, m))
    B2 = '( ( %s x. %s ) + ( _i x. _pi ) )' % (IT, m)
    arg = chain_eq(w, ph, '( %s x. A )' % TP, [(s1, '( %s x. ( %s + ( _i x. %s ) ) )' % (TP, X, Yv)), (s2, '( %s + ( %s x. ( _i x. %s ) ) )' % (TX, TP, Yv)),
                                               (D(w, ph, 'oveq2d', [s3], '( %s + ( %s x. ( _i x. %s ) ) ) = ( %s + ( _i x. %s ) )' % (TX, TP, Yv, TX, TY)), '( %s + ( _i x. %s ) )' % (TX, TY)),
                                               (D(w, ph, 'oveq2d', [D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [s7, s8], '( _i x. %s ) = ( ( _i x. %s ) + ( _i x. _pi ) )' % (TY, TM)), s10], '( _i x. %s ) = %s' % (TY, B2))],
                                                  '( %s + ( _i x. %s ) ) = ( %s + %s )' % (TX, TY, TX, B2)), '( %s + %s )' % (TX, B2))])
    txc = D(w, ph, 'mulcld', [tc, xc], '%s e. CC' % TX)
    itc = D(w, ph, 'mulcld', [ic, tc], '%s e. CC' % IT)
    itm = D(w, ph, 'mulcld', [itc, mc], '( %s x. %s ) e. CC' % (IT, m))
    ipc = D(w, ph, 'mulcld', [ic, pc], '( _i x. _pi ) e. CC')
    b2c = D(w, ph, 'addcld', [itm, ipc], '%s e. CC' % B2)
    e1 = D(w, ph, 'fveq2d', [arg], '%s = ( exp ` ( %s + %s ) )' % (E2('A'), TX, B2))
    e2 = w.s([txc, b2c, w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (ph, TX, B2, TX, B2))
    e3 = w.s([itm, ipc, w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` %s ) = ( ( exp ` ( %s x. %s ) ) x. ( exp ` ( _i x. _pi ) ) ) )' % (ph, B2, IT, m))
    e4 = D(w, ph, 'oveq12d', [w.s([mz, w.inst('ef2kpi')], 'syl', '( %s -> ( exp ` ( %s x. %s ) ) = 1 )' % (ph, IT, m)), cst(w, ph, 'efipi', '( exp ` ( _i x. _pi ) ) = -u 1')],
           '( ( exp ` ( %s x. %s ) ) x. ( exp ` ( _i x. _pi ) ) ) = ( 1 x. -u 1 )' % (IT, m))
    e5 = D(w, ph, 'mulridd' if False else 'mullidd', [cst(w, ph, 'neg1cn', '-u 1 e. CC')], '( 1 x. -u 1 ) = -u 1')
    eb2 = chain_eq(w, ph, '( exp ` %s )' % B2, [(e3, '( ( exp ` ( %s x. %s ) ) x. ( exp ` ( _i x. _pi ) ) )' % (IT, m)), (e4, '( 1 x. -u 1 )'), (e5, '-u 1')])
    EX = '( exp ` %s )' % TX
    exr = w.s([D(w, ph, 'remulcld', [D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), cst(w, ph, 'pire', '_pi e. RR')], '%s e. RR' % TP), xr], '%s e. RR' % TX), w.inst('reefcl')], 'syl', '( %s -> %s e. RR )' % (ph, EX))
    exc = D(w, ph, 'recnd', [exr], '%s e. CC' % EX)
    e6 = D(w, ph, 'oveq2d', [eb2], '( %s x. ( exp ` %s ) ) = ( %s x. -u 1 )' % (EX, B2, EX))
    e7 = D(w, ph, 'eqtrd', [D(w, ph, 'mulcomd', [exc, cst(w, ph, 'neg1cn', '-u 1 e. CC')], '( %s x. -u 1 ) = ( -u 1 x. %s )' % (EX, EX)), D(w, ph, 'mulm1d', [exc], '( -u 1 x. %s ) = -u %s' % (EX, EX))],
           '( %s x. -u 1 ) = -u %s' % (EX, EX))
    ea = chain_eq(w, ph, E2('A'), [(e1, '( exp ` ( %s + %s ) )' % (TX, B2)), (e2, '( %s x. ( exp ` %s ) )' % (EX, B2)), (e6, '( %s x. -u 1 )' % EX), (e7, '-u %s' % EX)])
    one = cst(w, ph, 'ax-1cn', '1 e. CC')
    f1 = D(w, ph, 'oveq1d', [ea], '( %s - 1 ) = ( -u %s - 1 )' % (E2('A'), EX))
    f2 = D(w, ph, 'eqcomd', [w.s([exc, one, w.inst('negdi2')], 'syl2anc', '( %s -> -u ( %s + 1 ) = ( -u %s - 1 ) )' % (ph, EX, EX))], '( -u %s - 1 ) = -u ( %s + 1 )' % (EX, EX))
    f3 = D(w, ph, 'fveq2d', [D(w, ph, 'eqtrd', [f1, f2], '( %s - 1 ) = -u ( %s + 1 )' % (E2('A'), EX))], '( abs ` ( %s - 1 ) ) = ( abs ` -u ( %s + 1 ) )' % (E2('A'), EX))
    e1c = D(w, ph, 'addcld', [exc, one], '( %s + 1 ) e. CC' % EX)
    e1r = D(w, ph, 'readdcld', [exr, cst(w, ph, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % EX)
    ex0 = D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), exr, w.s([D(w, ph, 'remulcld', [D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), cst(w, ph, 'pire', '_pi e. RR')], '%s e. RR' % TP), xr], '%s e. RR' % TX), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (ph, EX))],
            '0 <_ %s' % EX)
    le1 = D(w, ph, 'mpbid', [ex0, w.s([cst(w, ph, '1re', '1 e. RR'), exr, w.inst('addge02')], 'syl2anc', '( %s -> ( 0 <_ %s <-> 1 <_ ( %s + 1 ) ) )' % (ph, EX, EX))], '1 <_ ( %s + 1 )' % EX)
    e10 = D(w, ph, 'addge0d', [exr, cst(w, ph, '1re', '1 e. RR'), ex0, cst(w, ph, '0le1', '0 <_ 1')], '0 <_ ( %s + 1 )' % EX)
    f4 = chain_eq(w, ph, '( abs ` ( %s - 1 ) )' % E2('A'), [(f3, '( abs ` -u ( %s + 1 ) )' % EX), (D(w, ph, 'absnegd', [e1c], '( abs ` -u ( %s + 1 ) ) = ( abs ` ( %s + 1 ) )' % (EX, EX)), '( abs ` ( %s + 1 ) )' % EX),
                                                    (D(w, ph, 'absidd', [e1r, e10], '( abs ` ( %s + 1 ) ) = ( %s + 1 )' % (EX, EX)), '( %s + 1 )' % EX)])
    w.qed([le1, f4], 'breqtrrd', S['zl3kb'])
    go(w, only)


# ---------------------------------------------------------------- zl3hbd
def hctx(w, ph, src):
    """from src: ( ph -> HCTX ): hent, krp, hdec steps"""
    hent = w.s([src, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, HENT))
    kh = w.s([src, w.inst('simpr')], 'syl', '( %s -> ( K e. RR+ /\\ %s ) )' % (ph, HDEC))
    krp = w.s([kh, w.inst('simpl')], 'syl', '( %s -> K e. RR+ )' % ph)
    hdec = w.s([kh, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, HDEC))
    return hent, krp, hdec


def hdec_at(w, A, hdec_A, Z):
    """from hdec_A: ( A -> HDEC ): ( A -> ( ( abs ` ( Re ` Z ) ) <_ 1 -> ( abs ` ( H ` Z ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` Z ) ) ) ) ) )
    (requires ( A -> Z e. CC ) given separately via zc)"""
    body = lambda c: '( ( abs ` ( Re ` %s ) ) <_ 1 -> ( abs ` ( H ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) )' % (c, c, c)
    E = 'c = %s' % Z
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    r1 = D(w, E, 'breq1d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Re ` c ) = ( Re ` %s )' % Z)], '( abs ` ( Re ` c ) ) = ( abs ` ( Re ` %s ) )' % Z)],
           '( ( abs ` ( Re ` c ) ) <_ 1 <-> ( abs ` ( Re ` %s ) ) <_ 1 )' % Z)
    r2 = D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( H ` c ) = ( H ` %s )' % Z)], '( abs ` ( H ` c ) ) = ( abs ` ( H ` %s ) )' % Z),
                             D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Im ` c ) = ( Im ` %s )' % Z)], '( abs ` ( Im ` c ) ) = ( abs ` ( Im ` %s ) )' % Z)],
                                                                         '-u ( abs ` ( Im ` c ) ) = -u ( abs ` ( Im ` %s ) )' % Z)], '( 2 ^c -u ( abs ` ( Im ` c ) ) ) = ( 2 ^c -u ( abs ` ( Im ` %s ) ) )' % Z)],
                               '( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) = ( K x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % Z)],
           '( ( abs ` ( H ` c ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) <-> ( abs ` ( H ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) )' % (Z, Z))
    eq = D(w, E, 'imbi12d', [r1, r2], '( %s <-> %s )' % (body('c'), body(Z)))
    return w.s([eq], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (Z, HDEC, body(Z)))


def fk_at(w, Z):
    """closed: ( Z e. D0 -> ( FK ` Z ) = ( ( H ` Z ) / ( E2(Z) - 1 ) ) )"""
    E = 'w = %s' % Z
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    sub = D(w, E, 'oveq12d', [D(w, E, 'fveq2d', [e], '( H ` w ) = ( H ` %s )' % Z), D(w, E, 'oveq1d', [D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [e], '( %s x. w ) = ( %s x. %s )' % (TP, TP, Z))], '%s = %s' % (E2('w'), E2(Z)))],
                                                                                          '( %s - 1 ) = ( %s - 1 )' % (E2('w'), E2(Z)))],
            '( ( H ` w ) / ( %s - 1 ) ) = ( ( H ` %s ) / ( %s - 1 ) )' % (E2('w'), Z, E2(Z)))
    return w.s([sub, w.s([], 'eqid', '%s = %s' % (FK, FK)), w.s([], 'ovex', '( ( H ` %s ) / ( %s - 1 ) ) e. _V' % (Z, E2(Z)))], 'fvmpt',
               '( %s e. %s -> ( %s ` %s ) = ( ( H ` %s ) / ( %s - 1 ) ) )' % (Z, D0, FK, Z, Z, E2(Z)))


def d0_mem(w, A, Z, zc, ne1):
    """( A -> Z e. D0 ) from zc: Z e. CC, ne1: E2(Z) =/= 1"""
    E = 'v = %s' % Z
    vsub = D(w, E, 'neeq1d', [D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [w.s([], 'id', '( %s -> %s )' % (E, E))], '( %s x. v ) = ( %s x. %s )' % (TP, TP, Z))], '%s = %s' % (E2('v'), E2(Z)))],
             '( %s =/= 1 <-> %s =/= 1 )' % (E2('v'), E2(Z)))
    elr = w.s([vsub], 'elrab', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 1 ) )' % (Z, D0, Z, E2(Z)))
    return w.s([D(w, A, 'jca', [zc, ne1], '( %s e. CC /\\ %s =/= 1 )' % (Z, E2(Z))), elr], 'sylibr', '( %s -> %s e. %s )' % (A, Z, D0))


if __name__ == '__main__' and (not only or 'zl3hbd' in only):
    w = W('zl3hbd', 'On a horizontal segment at a height in ` ZZ + 1 / 2 ` inside the strip ` | Re w | <_ 1 ` the integral of ` H ( w ) / ( e ^ ( 2 pi w ) - 1 ) ` is bounded by ` K 2 ^ -| Im | ` times the length.')
    ph, concl = ante_of(S['zl3hbd'])
    hc_ = w.s([], 'simpl', '( %s -> %s )' % (ph, HCTX))
    hent, krp, hdec = hctx(w, ph, hc_)
    R2 = '( ( X e. RR /\\ Y e. RR /\\ U e. RR ) /\\ ( ( ( abs ` X ) <_ 1 /\\ ( abs ` Y ) <_ 1 ) /\\ ( U - ( 1 / 2 ) ) e. ZZ ) )'
    r2 = w.s([], 'simpr', '( %s -> %s )' % (ph, R2))
    t3 = w.s([r2, w.inst('simpl')], 'syl', '( %s -> ( X e. RR /\\ Y e. RR /\\ U e. RR ) )' % ph)
    xr = w.s([t3, w.inst('simp1')], 'syl', '( %s -> X e. RR )' % ph); yr = w.s([t3, w.inst('simp2')], 'syl', '( %s -> Y e. RR )' % ph); ur = w.s([t3, w.inst('simp3')], 'syl', '( %s -> U e. RR )' % ph)
    bb = w.s([r2, w.inst('simpr')], 'syl', '( %s -> ( ( ( abs ` X ) <_ 1 /\\ ( abs ` Y ) <_ 1 ) /\\ ( U - ( 1 / 2 ) ) e. ZZ ) )' % ph)
    xy1 = w.s([bb, w.inst('simpl')], 'syl', '( %s -> ( ( abs ` X ) <_ 1 /\\ ( abs ` Y ) <_ 1 ) )' % ph)
    uz = w.s([bb, w.inst('simpr')], 'syl', '( %s -> ( U - ( 1 / 2 ) ) e. ZZ )' % ph)
    one = cst(w, ph, '1re', '1 e. RR'); m1 = cst(w, ph, 'neg1rr', '-u 1 e. RR')
    L0, R0 = CP('-u 1', 'U'), CP('1', 'U'); A_, B_ = CP('X', 'U'), CP('Y', 'U')
    l0c = cpcl(w, ph, '-u 1', 'U', m1, ur); r0c = cpcl(w, ph, '1', 'U', one, ur)
    reL, imL = reim_cp(w, ph, '-u 1', 'U', m1, ur); reR, imR = reim_cp(w, ph, '1', 'U', one, ur)
    ri = D(w, ph, 'oveq12d', [reL, reR], '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( -u 1 [,] 1 )' % (L0, R0))
    ii = D(w, ph, 'oveq12d', [imL, imR], '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( U [,] U )' % (L0, R0))
    uu = D(w, ph, 'mpbird', [w.s([ur, D(w, ph, 'leidd', [ur], 'U <_ U'), D(w, ph, 'leidd', [ur], 'U <_ U')], '3jca', '( %s -> ( U e. RR /\\ U <_ U /\\ U <_ U ) )' % ph),
                             w.s([ur, ur, w.inst('elicc2')], 'syl2anc', '( %s -> ( U e. ( U [,] U ) <-> ( U e. RR /\\ U <_ U /\\ U <_ U ) ) )' % ph)], 'U e. ( U [,] U )')
    uI = D(w, ph, 'eleqtrrd', [uu, ii], 'U e. ( ( Im ` %s ) [,] ( Im ` %s ) )' % (L0, R0))
    def inrect(V, v_r, vabs):
        ab = D(w, ph, 'mpbid', [vabs, w.s([v_r, one, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` %s ) <_ 1 <-> ( -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (ph, V, V, V))],
               '( -u 1 <_ %s /\\ %s <_ 1 )' % (V, V))
        vI = D(w, ph, 'mpbird', [w.s([v_r, w.s([ab, w.inst('simpl')], 'syl', '( %s -> -u 1 <_ %s )' % (ph, V)), w.s([ab, w.inst('simpr')], 'syl', '( %s -> %s <_ 1 )' % (ph, V))], '3jca',
                                     '( %s -> ( %s e. RR /\\ -u 1 <_ %s /\\ %s <_ 1 ) )' % (ph, V, V, V)),
                                 w.s([m1, one, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( -u 1 [,] 1 ) <-> ( %s e. RR /\\ -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (ph, V, V, V, V))],
               '%s e. ( -u 1 [,] 1 )' % V)
        vI2 = D(w, ph, 'eleqtrrd', [vI, ri], '%s e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (V, L0, R0))
        return w.s([D(w, ph, 'jca', [l0c, r0c], '( %s e. CC /\\ %s e. CC )' % (L0, R0)), D(w, ph, 'jca', [vI2, uI], '( %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ U e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (V, L0, R0, L0, R0)),
                    w.inst('crectpt')], 'syl2anc', '( %s -> %s e. ( %s crect %s ) )' % (ph, CP(V, 'U'), L0, R0))
    ain = inrect('X', xr, w.s([xy1, w.inst('simpl')], 'syl', '( %s -> ( abs ` X ) <_ 1 )' % ph))
    bin_ = inrect('Y', yr, w.s([xy1, w.inst('simpr')], 'syl', '( %s -> ( abs ` Y ) <_ 1 )' % ph))
    cvx = w.s([D(w, ph, 'jca', [l0c, r0c], '( %s e. CC /\\ %s e. CC )' % (L0, R0)), D(w, ph, 'jca', [ain, bin_], '( %s e. ( %s crect %s ) /\\ %s e. ( %s crect %s ) )' % (A_, L0, R0, B_, L0, R0)),
               w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( %s crect %s ) )' % (ph, A_, B_, L0, R0))
    # a point z of the segment
    A1 = '( %s /\\ z e. ( %s cseg %s ) )' % (ph, A_, B_)
    lift = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
    zr = D(w, A1, 'sseldd', [lift(cvx, '( %s cseg %s ) C_ ( %s crect %s )' % (A_, B_, L0, R0)), w.s([], 'simpr', '( %s -> z e. ( %s cseg %s ) )' % (A1, A_, B_))], 'z e. ( %s crect %s )' % (L0, R0))
    ec = w.s([lift(D(w, ph, 'jca', [l0c, r0c], '( %s e. CC /\\ %s e. CC )' % (L0, R0)), '( %s e. CC /\\ %s e. CC )' % (L0, R0)), w.inst('elcrect')], 'syl',
             '( %s -> ( z e. ( %s crect %s ) <-> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A1, L0, R0, L0, R0, L0, R0))
    e3 = D(w, A1, 'mpbid', [zr, ec], '( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (L0, R0, L0, R0))
    zc = w.s([e3, w.inst('simp1')], 'syl', '( %s -> z e. CC )' % A1)
    zre = D(w, A1, 'eleqtrd', [w.s([e3, w.inst('simp2')], 'syl', '( %s -> ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A1, L0, R0)), lift(ri, '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( -u 1 [,] 1 )' % (L0, R0))],
            '( Re ` z ) e. ( -u 1 [,] 1 )')
    zim = D(w, A1, 'eleqtrd', [w.s([e3, w.inst('simp3')], 'syl', '( %s -> ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A1, L0, R0)), lift(ii, '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( U [,] U )' % (L0, R0))],
            '( Im ` z ) e. ( U [,] U )')
    ur1 = lift(ur, 'U e. RR'); one1 = cst(w, A1, '1re', '1 e. RR'); m11 = cst(w, A1, 'neg1rr', '-u 1 e. RR')
    zr3 = D(w, A1, 'mpbid', [zre, w.s([m11, one1, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` z ) e. ( -u 1 [,] 1 ) <-> ( ( Re ` z ) e. RR /\\ -u 1 <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 ) ) )' % A1)],
            '( ( Re ` z ) e. RR /\\ -u 1 <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 )')
    zi3 = D(w, A1, 'mpbid', [zim, w.s([ur1, ur1, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Im ` z ) e. ( U [,] U ) <-> ( ( Im ` z ) e. RR /\\ U <_ ( Im ` z ) /\\ ( Im ` z ) <_ U ) ) )' % A1)],
            '( ( Im ` z ) e. RR /\\ U <_ ( Im ` z ) /\\ ( Im ` z ) <_ U )')
    rzr = w.s([zr3, w.inst('simp1')], 'syl', '( %s -> ( Re ` z ) e. RR )' % A1)
    reab = D(w, A1, 'mpbird', [D(w, A1, 'jca', [w.s([zr3, w.inst('simp2')], 'syl', '( %s -> -u 1 <_ ( Re ` z ) )' % A1), w.s([zr3, w.inst('simp3')], 'syl', '( %s -> ( Re ` z ) <_ 1 )' % A1)],
                                     '( -u 1 <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 )'),
                               w.s([rzr, one1, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` ( Re ` z ) ) <_ 1 <-> ( -u 1 <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 ) ) )' % A1)],
             '( abs ` ( Re ` z ) ) <_ 1')
    izr = w.s([zi3, w.inst('simp1')], 'syl', '( %s -> ( Im ` z ) e. RR )' % A1)
    ime = D(w, A1, 'mpbird', [D(w, A1, 'jca', [w.s([zi3, w.inst('simp3')], 'syl', '( %s -> ( Im ` z ) <_ U )' % A1), w.s([zi3, w.inst('simp2')], 'syl', '( %s -> U <_ ( Im ` z ) )' % A1)],
                                    '( ( Im ` z ) <_ U /\\ U <_ ( Im ` z ) )'), D(w, A1, 'letri3d', [izr, ur1], '( ( Im ` z ) = U <-> ( ( Im ` z ) <_ U /\\ U <_ ( Im ` z ) ) )')], '( Im ` z ) = U')
    # H bound
    hz = w.s([zc, lift(hdec, HDEC), reab, hdec_at(w, A1, None, 'z')], 'syl3c' if False else 'sylc', 'x') if False else None
    hdz = w.s([zc, lift(hdec, HDEC), hdec_at(w, A1, None, 'z')], 'sylc',
              '( %s -> ( ( abs ` ( Re ` z ) ) <_ 1 -> ( abs ` ( H ` z ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` z ) ) ) ) ) )' % A1)
    hb0 = D(w, A1, 'mpd', [reab, hdz], '( abs ` ( H ` z ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` z ) ) ) )')
    KU = '( K x. ( 2 ^c -u ( abs ` U ) ) )'
    kr = D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [D(w, A1, 'oveq2d', [D(w, A1, 'negeqd', [D(w, A1, 'fveq2d', [ime], '( abs ` ( Im ` z ) ) = ( abs ` U )')], '-u ( abs ` ( Im ` z ) ) = -u ( abs ` U )')],
                                                         '( 2 ^c -u ( abs ` ( Im ` z ) ) ) = ( 2 ^c -u ( abs ` U ) )')], '( K x. ( 2 ^c -u ( abs ` ( Im ` z ) ) ) ) = %s' % KU),
                            D(w, A1, 'eqidd', [], '%s = %s' % (KU, KU))], '( K x. ( 2 ^c -u ( abs ` ( Im ` z ) ) ) ) = %s' % KU)
    hb = D(w, A1, 'breqtrd', [hb0, kr], '( abs ` ( H ` z ) ) <_ %s' % KU)
    # kernel bound
    iz = D(w, A1, 'eqeltrd', [D(w, A1, 'oveq1d', [ime], '( ( Im ` z ) - ( 1 / 2 ) ) = ( U - ( 1 / 2 ) )'), lift(uz, '( U - ( 1 / 2 ) ) e. ZZ')], '( ( Im ` z ) - ( 1 / 2 ) ) e. ZZ')
    kb = w.s([zc, iz, w.inst('zl3kb')], 'syl2anc', '( %s -> 1 <_ ( abs ` ( %s - 1 ) ) )' % (A1, E2('z')))
    tc, tn = twopi(w, A1)
    ezc = w.s([D(w, A1, 'mulcld', [tc, zc], '( %s x. z ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A1, E2('z')))
    dc = D(w, A1, 'subcld', [ezc, cst(w, A1, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2('z'))
    dab = D(w, A1, 'abscld', [dc], '( abs ` ( %s - 1 ) ) e. RR' % E2('z'))
    dpos = D(w, A1, 'ltletrd', [cst(w, A1, '0re', '0 e. RR'), one1, dab, cst(w, A1, '0lt1', '0 < 1'), kb], '0 < ( abs ` ( %s - 1 ) )' % E2('z'))
    dne = D(w, A1, 'mpbird', [dpos, w.s([dc, w.inst('absgt0')], 'syl', '( %s -> ( ( %s - 1 ) =/= 0 <-> 0 < ( abs ` ( %s - 1 ) ) ) )' % (A1, E2('z'), E2('z')))], '( %s - 1 ) =/= 0' % E2('z'))
    ne1 = D(w, A1, 'subne0ad', [ezc, cst(w, A1, 'ax-1cn', '1 e. CC'), dne], '%s =/= 1' % E2('z'))
    zd0 = d0_mem(w, A1, 'z', zc, ne1)
    fz = w.s([zd0, fk_at(w, 'z')], 'syl', '( %s -> ( %s ` z ) = ( ( H ` z ) / ( %s - 1 ) ) )' % (A1, FK, E2('z')))
    hf = w.s([w.s([lift(hent, HENT), w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % A1), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % A1)
    hzc = D(w, A1, 'ffvelcdmd', [hf, zc], '( H ` z ) e. CC')
    fa = D(w, A1, 'eqtrd', [D(w, A1, 'fveq2d', [fz], '( abs ` ( %s ` z ) ) = ( abs ` ( ( H ` z ) / ( %s - 1 ) ) )' % (FK, E2('z'))),
                            D(w, A1, 'absdivd', [hzc, dc, dne], '( abs ` ( ( H ` z ) / ( %s - 1 ) ) ) = ( ( abs ` ( H ` z ) ) / ( abs ` ( %s - 1 ) ) )' % (E2('z'), E2('z')))],
           '( abs ` ( %s ` z ) ) = ( ( abs ` ( H ` z ) ) / ( abs ` ( %s - 1 ) ) )' % (FK, E2('z')))
    krp1 = lift(krp, 'K e. RR+')
    kup = D(w, A1, 'rpmulcld', [krp1, D(w, A1, 'rpcxpcld', [cst(w, A1, '2rp', '2 e. RR+'), D(w, A1, 'renegcld', [D(w, A1, 'recnd' if False else 'abscld', [D(w, A1, 'recnd', [ur1], 'U e. CC')], '( abs ` U ) e. RR')], '-u ( abs ` U ) e. RR')],
                                                    '( 2 ^c -u ( abs ` U ) ) e. RR+')], '%s e. RR+' % KU)
    ld = w.s([D(w, A1, 'abscld', [hzc], '( abs ` ( H ` z ) ) e. RR'), kup, D(w, A1, 'jca', [D(w, A1, 'elrpd', [dab, dpos], '( abs ` ( %s - 1 ) ) e. RR+' % E2('z')), kb], '( ( abs ` ( %s - 1 ) ) e. RR+ /\\ 1 <_ ( abs ` ( %s - 1 ) ) )' % (E2('z'), E2('z'))),
              w.inst('ledivge1le')], 'syl3anc', '( %s -> ( ( abs ` ( H ` z ) ) <_ %s -> ( ( abs ` ( H ` z ) ) / ( abs ` ( %s - 1 ) ) ) <_ %s ) )' % (A1, KU, E2('z'), KU))
    fb = D(w, A1, 'eqbrtrd', [fa, D(w, A1, 'mpd', [hb, ld], '( ( abs ` ( H ` z ) ) / ( abs ` ( %s - 1 ) ) ) <_ %s' % (E2('z'), KU))], '( abs ` ( %s ` z ) ) <_ %s' % (FK, KU))
    allb = w.s([fb], 'ralrimiva', '( %s -> A. z e. ( %s cseg %s ) ( abs ` ( %s ` z ) ) <_ %s )' % (ph, A_, B_, FK, KU))
    sd0 = w.s([w.s([zd0], 'ex', '( %s -> ( z e. ( %s cseg %s ) -> z e. %s ) )' % (ph, A_, B_, D0))], 'ssrdv', '( %s -> ( %s cseg %s ) C_ %s )' % (ph, A_, B_, D0))
    fkc = w.s([hent, w.inst('zl3fkcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ph, FK, D0))
    ac = cpcl(w, ph, 'X', 'U', xr, ur); bc = cpcl(w, ph, 'Y', 'U', yr, ur)
    kur = D(w, ph, 'remulcld', [D(w, ph, 'rpred', [krp], 'K e. RR'), D(w, ph, 'recxpcld' if False else 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'abscld', [D(w, ph, 'recnd', [ur], 'U e. CC')], '( abs ` U ) e. RR')], '-u ( abs ` U ) e. RR')],
                                                                                                        '( 2 ^c -u ( abs ` U ) ) e. RR+')], '( 2 ^c -u ( abs ` U ) ) e. RR')], '%s e. RR' % KU)
    la = w.s([D(w, ph, 'jca', [D(w, ph, 'jca', [ac, bc], '( %s e. CC /\\ %s e. CC )' % (A_, B_)), D(w, ph, 'jca', [fkc, sd0], '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (FK, D0, A_, B_, D0))],
                    '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A_, B_, FK, D0, A_, B_, D0)), kur, allb, w.inst('lintabs')], 'syl3anc',
             '( %s -> ( abs ` %s ) <_ ( %s x. ( abs ` ( %s - %s ) ) ) )' % (ph, LI(FK, A_, B_), KU, B_, A_))
    ic = cst(w, ph, 'ax-icn', '_i e. CC')
    dl = D(w, ph, 'pnpcan2d', [D(w, ph, 'recnd', [yr], 'Y e. CC'), D(w, ph, 'recnd', [xr], 'X e. CC'), D(w, ph, 'mulcld', [ic, D(w, ph, 'recnd', [ur], 'U e. CC')], '( _i x. U ) e. CC')],
           '( %s - %s ) = ( Y - X )' % (B_, A_))
    w.qed([la, D(w, ph, 'oveq2d', [D(w, ph, 'fveq2d', [dl], '( abs ` ( %s - %s ) ) = ( abs ` ( Y - X ) )' % (B_, A_))], '( %s x. ( abs ` ( %s - %s ) ) ) = ( %s x. ( abs ` ( Y - X ) ) )' % (KU, B_, A_, KU))],
          'breqtrd', S['zl3hbd'])
    go(w, only)


# ---------------------------------------------------------------- zl3mser
def fvj(w, A_, FN, body_j, body_k, kin, valcl, dom='NN'):
    """( A_ -> ( FN ` k ) = body_k ) for FN = ( j e. dom |-> body_j ), from kin: ( A_ -> k e. dom ), valcl: ( A_ -> body_k e. CC )"""
    E = 'j = k'
    sub = w.s([], 'SUBST', 'x') if False else None
    return None


if __name__ == '__main__' and (not only or 'zl3mser' in only):
    w = W('zl3mser', 'A series dominated by a geometric series ` B R ^ k ` converges and its sum is bounded by ` B R / ( 1 - R ) `.')
    H_ = {}
    for n, f in HYPS['zl3mser']:
        H_[n] = hyp(w, n, 'zl3mser.' + n, f)
    ph = 'ph'
    P1 = '( ph /\\ k e. NN )'; PU = '( ph /\\ k e. ( ZZ>= ` 1 ) )'
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    kU = w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % PU)
    kN = D(w, PU, 'eleqtrrd', [kU, w.s([nnu], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % PU)], 'k e. NN')
    def fromNN(stepP1, f):
        return w.s([w.s([], 'simpl', '( %s -> ph )' % PU), kN, stepP1], 'syl2anc', '( %s -> %s )' % (PU, f))
    br = H_['1']; rr = H_['2']; r0 = H_['3']; r1 = H_['4']; acc = H_['5']; abd = H_['6']
    rc = D(w, ph, 'recnd', [rr], 'R e. CC'); bc = D(w, ph, 'recnd', [br], 'B e. CC')
    ra = D(w, ph, 'eqbrtrd', [D(w, ph, 'absidd', [rr, r0], '( abs ` R ) = R'), r1], '( abs ` R ) < 1')
    PG = '( j e. NN0 |-> ( R ^ j ) )'; G = '( j e. NN |-> ( B x. ( R ^ j ) ) )'; F = 'F'; FA = '( j e. NN |-> ( abs ` ( F ` j ) ) )'
    def fvc(FN, bj, bk, dom, A_, kin, vcl):
        e = w.s([], 'id', '( j = k -> j = k )')
        if bj == '( R ^ j )':
            sub = w.s([], 'oveq2', '( j = k -> ( R ^ j ) = ( R ^ k ) )')
        elif bj == '( B x. ( R ^ j ) )':
            sub = w.s([w.s([], 'oveq2', '( j = k -> ( R ^ j ) = ( R ^ k ) )')], 'oveq2d', '( j = k -> ( B x. ( R ^ j ) ) = ( B x. ( R ^ k ) ) )')
        else:
            sub = w.s([w.s([], 'fveq2', '( j = k -> ( F ` j ) = ( F ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( F ` j ) ) = ( abs ` ( F ` k ) ) )')
        fm = w.s([sub, w.s([], 'eqid', '%s = %s' % (FN, FN)), w.s([], 'ovex' if bk[2:5] in ('R ^', 'B x') else 'fvex', '%s e. _V' % bk)], 'fvmpt', '( k e. %s -> ( %s ` k ) = %s )' % (dom, FN, bk))
        return w.s([kin, fm], 'syl', '( %s -> ( %s ` k ) = %s )' % (A_, FN, bk))
    kP = w.s([], 'simpr', '( %s -> k e. NN )' % P1)
    kc1 = D(w, P1, 'nnnn0d', [kP], 'k e. NN0')
    rk1 = D(w, P1, 'reexpcld', [w.s([rr], 'adantr', '( %s -> R e. RR )' % P1), kc1], '( R ^ k ) e. RR')
    brk1 = D(w, P1, 'remulcld', [w.s([br], 'adantr', '( %s -> B e. RR )' % P1), rk1], '( B x. ( R ^ k ) ) e. RR')
    kn0U = D(w, PU, 'nnnn0d', [kN], 'k e. NN0')
    pgv = fvc(PG, '( R ^ j )', '( R ^ k )', 'NN0', PU, kn0U, None)
    gl = w.s([rc, ra, cst(w, ph, '1nn0', '1 e. NN0'), pgv], 'geolim2', '( ph -> seq 1 ( + , %s ) ~~> ( ( R ^ 1 ) / ( 1 - R ) ) )' % PG)
    gvP = fvc(G, '( B x. ( R ^ j ) )', '( B x. ( R ^ k ) )', 'NN', P1, kP, None)
    gvU = fromNN(gvP, '( %s ` k ) = ( B x. ( R ^ k ) )' % G)
    pgc = D(w, PU, 'eqeltrd', [pgv, D(w, PU, 'recnd', [D(w, PU, 'reexpcld', [w.s([rr], 'adantr', '( %s -> R e. RR )' % PU), kn0U], '( R ^ k ) e. RR')], '( R ^ k ) e. CC')], '( %s ` k ) e. CC' % PG)
    gm = D(w, PU, 'eqtr4d', [gvU, D(w, PU, 'oveq2d', [pgv], '( B x. ( %s ` k ) ) = ( B x. ( R ^ k ) )' % PG)], '( %s ` k ) = ( B x. ( %s ` k ) )' % (G, PG))
    gs = w.s([w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), bc, gl, pgc, gm], 'isermulc2', '( ph -> seq 1 ( + , %s ) ~~> ( B x. ( ( R ^ 1 ) / ( 1 - R ) ) ) )' % G)
    rel = w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> ( B x. ( ( R ^ 1 ) / ( 1 - R ) ) ) -> seq 1 ( + , %s ) e. dom ~~> )' % (G, G))
    gdm = w.s([gs, rel], 'syl', '( ph -> seq 1 ( + , %s ) e. dom ~~> )' % G)
    grU = D(w, PU, 'eqeltrd', [gvU, fromNN(brk1, '( B x. ( R ^ k ) ) e. RR')], '( %s ` k ) e. RR' % G)
    grP = D(w, P1, 'eqeltrd', [gvP, brk1], '( %s ` k ) e. RR' % G)
    one1 = cst(w, PU, '1re', '1 e. RR')
    m1g = D(w, PU, 'eqtrd', [D(w, PU, 'mullidd', [D(w, PU, 'recnd', [grU], '( %s ` k ) e. CC' % G)], '( 1 x. ( %s ` k ) ) = ( %s ` k )' % (G, G)), gvU], '( 1 x. ( %s ` k ) ) = ( B x. ( R ^ k ) )' % G)
    cmpU = D(w, PU, 'breqtrrd', [fromNN(abd, '( abs ` ( F ` k ) ) <_ ( B x. ( R ^ k ) )'), m1g], '( abs ` ( F ` k ) ) <_ ( 1 x. ( %s ` k ) )' % G)
    one_in = D(w, ph, 'eleqtrd', [cst(w, ph, '1nn', '1 e. NN'), w.s([nnu], 'a1i', '( ph -> NN = ( ZZ>= ` 1 ) )')], '1 e. ( ZZ>= ` 1 )')
    oneN = cst(w, ph, '1nn', '1 e. NN')
    fdm = w.s([nnu, oneN, grP, acc, gdm, cst(w, ph, '1re', '1 e. RR'), cmpU], 'cvgcmpce', '( ph -> seq 1 ( + , F ) e. dom ~~> )')
    aar = D(w, P1, 'abscld', [acc], '( abs ` ( F ` k ) ) e. RR')
    faP = fvc(FA, '( abs ` ( F ` j ) )', '( abs ` ( F ` k ) )', 'NN', P1, kP, None)
    facP = D(w, P1, 'recnd', [D(w, P1, 'eqeltrd', [faP, aar], '( %s ` k ) e. RR' % FA)], '( %s ` k ) e. CC' % FA)
    aa = D(w, P1, 'eqtrd', [D(w, P1, 'fveq2d', [faP], '( abs ` ( %s ` k ) ) = ( abs ` ( abs ` ( F ` k ) ) )' % FA), D(w, P1, 'absidd', [aar, D(w, P1, 'absge0d', [acc], '0 <_ ( abs ` ( F ` k ) )')], '( abs ` ( abs ` ( F ` k ) ) ) = ( abs ` ( F ` k ) )')],
           '( abs ` ( %s ` k ) ) = ( abs ` ( F ` k ) )' % FA)
    cmpA = D(w, PU, 'breqtrrd', [fromNN(D(w, P1, 'eqbrtrd', [aa, abd], '( abs ` ( %s ` k ) ) <_ ( B x. ( R ^ k ) )' % FA), '( abs ` ( %s ` k ) ) <_ ( B x. ( R ^ k ) )' % FA), m1g],
               '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (FA, G))
    fadm = w.s([nnu, oneN, grP, facP, gdm, cst(w, ph, '1re', '1 e. RR'), cmpA], 'cvgcmpce', '( ph -> seq 1 ( + , %s ) e. dom ~~> )' % FA)
    one_z = cst(w, ph, '1z', '1 e. ZZ')
    fid = D(w, P1, 'eqidd', [], '( F ` k ) = ( F ` k )')
    s1 = w.s([nnu, one_z, fid, acc, fdm], 'isumclim2', '( ph -> seq 1 ( + , F ) ~~> sum_ k e. NN ( F ` k ) )')
    s2 = w.s([nnu, one_z, faP, D(w, P1, 'recnd', [aar], '( abs ` ( F ` k ) ) e. CC'), fadm], 'isumclim2', '( ph -> seq 1 ( + , %s ) ~~> sum_ k e. NN ( abs ` ( F ` k ) ) )' % FA)
    ab = w.s([nnu, s1, s2, one_z, acc, faP], 'iserabs', '( ph -> ( abs ` sum_ k e. NN ( F ` k ) ) <_ sum_ k e. NN ( abs ` ( F ` k ) ) )')
    le = w.s([nnu, one_z, faP, aar, gvP, brk1, abd, fadm, gdm], 'isumle', '( ph -> sum_ k e. NN ( abs ` ( F ` k ) ) <_ sum_ k e. NN ( B x. ( R ^ k ) ) )')
    gi = w.s([bc, rc, ra, w.inst('geoisum1c')], 'syl3anc', '( ph -> sum_ k e. NN ( B x. ( R ^ k ) ) = ( ( B x. R ) / ( 1 - R ) ) )')
    bnd = D(w, ph, 'breqtrd', [D(w, ph, 'letrd', [D(w, ph, 'abscld', [w.s([nnu, one_z, fid, acc, fdm], 'isumcl', '( ph -> sum_ k e. NN ( F ` k ) e. CC )')], '( abs ` sum_ k e. NN ( F ` k ) ) e. RR'),
                                                   w.s([nnu, one_z, faP, aar, fadm], 'isumrecl', '( ph -> sum_ k e. NN ( abs ` ( F ` k ) ) e. RR )'),
                                                   w.s([nnu, one_z, gvP, brk1, gdm], 'isumrecl', '( ph -> sum_ k e. NN ( B x. ( R ^ k ) ) e. RR )'), ab, le],
                                    '( abs ` sum_ k e. NN ( F ` k ) ) <_ sum_ k e. NN ( B x. ( R ^ k ) )'), gi], '( abs ` sum_ k e. NN ( F ` k ) ) <_ ( ( B x. R ) / ( 1 - R ) )')
    w.qed([fdm, bnd], 'jca', S['zl3mser'])
    if not only or w.label in only: runh(w)


# ---------------------------------------------------------------- zl3eseg / zl3edge common context
EDGA_L = '( ( ( C e. RR /\\ A e. RR ) /\\ ( A x. C ) < 0 )'
GB = 'A. b e. RR ( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` b ) ) )' % CP('C', 'b')
PVb = lambda b: '( ( ( G ` %s ) x. ( exp ` ( A x. %s ) ) ) / ( 1 - ( exp ` ( A x. %s ) ) ) )' % (CP('C', b), CP('C', b), CP('C', b))
PV = 'A. b e. RR ( P ` %s ) = %s' % (CP('C', 'b'), PVb('b'))
EDGA_R = '( ( ( G e. ( CC -cn-> CC ) /\\ K e. RR+ ) /\\ %s ) /\\ ( P e. V /\\ %s ) )' % (GB, PV)
assert EDGA == '( ( ( C e. RR /\\ A e. RR ) /\\ ( A x. C ) < 0 ) /\\ %s )' % EDGA_R
RR_ = '( exp ` ( A x. C ) )'


def edga_ctx(w, ph, src):
    d = {}
    l = w.s([src, w.inst('simpl')], 'syl', '( %s -> ( ( C e. RR /\\ A e. RR ) /\\ ( A x. C ) < 0 ) )' % ph)
    r = w.s([src, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, EDGA_R))
    ca = w.s([l, w.inst('simpl')], 'syl', '( %s -> ( C e. RR /\\ A e. RR ) )' % ph)
    d['cr'] = w.s([ca, w.inst('simpl')], 'syl', '( %s -> C e. RR )' % ph)
    d['ar'] = w.s([ca, w.inst('simpr')], 'syl', '( %s -> A e. RR )' % ph)
    d['ac0'] = w.s([l, w.inst('simpr')], 'syl', '( %s -> ( A x. C ) < 0 )' % ph)
    r1 = w.s([r, w.inst('simpl')], 'syl', '( %s -> ( ( G e. ( CC -cn-> CC ) /\\ K e. RR+ ) /\\ %s ) )' % (ph, GB))
    r2 = w.s([r, w.inst('simpr')], 'syl', '( %s -> ( P e. V /\\ %s ) )' % (ph, PV))
    gk = w.s([r1, w.inst('simpl')], 'syl', '( %s -> ( G e. ( CC -cn-> CC ) /\\ K e. RR+ ) )' % ph)
    d['gcn'] = w.s([gk, w.inst('simpl')], 'syl', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    d['krp'] = w.s([gk, w.inst('simpr')], 'syl', '( %s -> K e. RR+ )' % ph)
    d['gb'] = w.s([r1, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, GB))
    d['pv'] = w.s([r2, w.inst('simpl')], 'syl', '( %s -> P e. V )' % ph)
    d['pval'] = w.s([r2, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, PV))
    d['kr'] = D(w, ph, 'rpred', [d['krp']], 'K e. RR')
    acr = D(w, ph, 'remulcld', [d['ar'], d['cr']], '( A x. C ) e. RR')
    d['acr'] = acr
    d['rr'] = w.s([acr, w.inst('reefcl')], 'syl', '( %s -> %s e. RR )' % (ph, RR_))
    d['r0lt'] = w.s([acr, w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (ph, RR_))
    d['r0'] = D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), d['rr'], d['r0lt']], '0 <_ %s' % RR_)
    el = w.s([acr, cst(w, ph, '0re', '0 e. RR'), w.inst('eflt')], 'syl2anc', '( %s -> ( ( A x. C ) < 0 <-> %s < ( exp ` 0 ) ) )' % (ph, RR_))
    d['r1'] = D(w, ph, 'breqtrd', [D(w, ph, 'mpbid', [d['ac0'], el], '%s < ( exp ` 0 )' % RR_), cst(w, ph, 'ef0', '( exp ` 0 ) = 1')], '%s < 1' % RR_)
    return d


def gb_at(w, A_, gb_A, bexpr, bre):
    """( A_ -> ( abs ` ( G ` CP(C, bexpr) ) ) <_ ( K x. ( 2 ^c -u ( abs ` bexpr ) ) ) )"""
    E = 'b = %s' % bexpr
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    cpe = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [e], '( _i x. b ) = ( _i x. %s )' % bexpr)], '%s = %s' % (CP('C', 'b'), CP('C', bexpr)))
    l = D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [cpe], '( G ` %s ) = ( G ` %s )' % (CP('C', 'b'), CP('C', bexpr)))], '( abs ` ( G ` %s ) ) = ( abs ` ( G ` %s ) )' % (CP('C', 'b'), CP('C', bexpr)))
    r = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [e], '( abs ` b ) = ( abs ` %s )' % bexpr)], '-u ( abs ` b ) = -u ( abs ` %s )' % bexpr)],
                                           '( 2 ^c -u ( abs ` b ) ) = ( 2 ^c -u ( abs ` %s ) )' % bexpr)], '( K x. ( 2 ^c -u ( abs ` b ) ) ) = ( K x. ( 2 ^c -u ( abs ` %s ) ) )' % bexpr)
    eq = D(w, E, 'breq12d', [l, r], '( ( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` b ) ) ) <-> ( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` %s ) ) ) )' % (CP('C', 'b'), CP('C', bexpr), bexpr))
    rs = w.s([eq], 'rspcv', '( %s e. RR -> ( %s -> ( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` %s ) ) ) ) )' % (bexpr, GB, CP('C', bexpr), bexpr))
    return w.s([bre, gb_A, rs], 'sylc', '( %s -> ( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` %s ) ) ) )' % (A_, CP('C', bexpr), bexpr))


def pv_at(w, A_, pv_A, bexpr, bre):
    E = 'b = %s' % bexpr
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    cpe = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [e], '( _i x. b ) = ( _i x. %s )' % bexpr)], '%s = %s' % (CP('C', 'b'), CP('C', bexpr)))
    gq = D(w, E, 'fveq2d', [cpe], '( G ` %s ) = ( G ` %s )' % (CP('C', 'b'), CP('C', bexpr)))
    ex = D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [cpe], '( A x. %s ) = ( A x. %s )' % (CP('C', 'b'), CP('C', bexpr)))], '( exp ` ( A x. %s ) ) = ( exp ` ( A x. %s ) )' % (CP('C', 'b'), CP('C', bexpr)))
    rhs = D(w, E, 'oveq12d', [D(w, E, 'oveq12d', [gq, ex], '( ( G ` %s ) x. ( exp ` ( A x. %s ) ) ) = ( ( G ` %s ) x. ( exp ` ( A x. %s ) ) )' % (CP('C', 'b'), CP('C', 'b'), CP('C', bexpr), CP('C', bexpr))),
                              D(w, E, 'oveq2d', [ex], '( 1 - ( exp ` ( A x. %s ) ) ) = ( 1 - ( exp ` ( A x. %s ) ) )' % (CP('C', 'b'), CP('C', bexpr)))], '%s = %s' % (PVb('b'), PVb(bexpr)))
    eq = D(w, E, 'eqeq12d', [D(w, E, 'fveq2d', [cpe], '( P ` %s ) = ( P ` %s )' % (CP('C', 'b'), CP('C', bexpr))), rhs], '( ( P ` %s ) = %s <-> ( P ` %s ) = %s )' % (CP('C', 'b'), PVb('b'), CP('C', bexpr), PVb(bexpr)))
    rs = w.s([eq], 'rspcv', '( %s e. RR -> ( %s -> ( P ` %s ) = %s ) )' % (bexpr, PV, CP('C', bexpr), PVb(bexpr)))
    return w.s([bre, pv_A, rs], 'sylc', '( %s -> ( P ` %s ) = %s )' % (A_, CP('C', bexpr), PVb(bexpr)))


def seg_ctx(w, ph, d, T, tr, tpos):
    """the vertical segment U = ( CP(C,-T) cseg CP(C,T) ): points, crect inclusion"""
    Lo, Hi = CP('C', '-u %s' % T), CP('C', T)
    ntr = D(w, ph, 'renegcld', [tr], '-u %s e. RR' % T)
    loc = cpcl(w, ph, 'C', '-u %s' % T, d['cr'], ntr); hic = cpcl(w, ph, 'C', T, d['cr'], tr)
    reL, imL = reim_cp(w, ph, 'C', '-u %s' % T, d['cr'], ntr); reH, imH = reim_cp(w, ph, 'C', T, d['cr'], tr)
    ab = D(w, ph, 'jca', [loc, hic], '( %s e. CC /\\ %s e. CC )' % (Lo, Hi))
    le1 = D(w, ph, '3brtr4d', [D(w, ph, 'leidd', [d['cr']], 'C <_ C'), reL, reH], '( Re ` %s ) <_ ( Re ` %s )' % (Lo, Hi))
    ntlt = D(w, ph, 'lttrd', [ntr, cst(w, ph, '0re', '0 e. RR'), tr, D(w, ph, 'mpbid', [tpos, D(w, ph, 'lt0neg2d', [tr], '( 0 < %s <-> -u %s < 0 )' % (T, T))], '-u %s < 0' % T), tpos], '-u %s < %s' % (T, T))
    le2 = D(w, ph, '3brtr4d', [D(w, ph, 'ltled', [ntr, tr, ntlt], '-u %s <_ %s' % (T, T)), imL, imH], '( Im ` %s ) <_ ( Im ` %s )' % (Lo, Hi))
    abg = D(w, ph, 'jca', [ab, D(w, ph, 'jca', [le1, le2], '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (Lo, Hi, Lo, Hi))],
            '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (Lo, Hi, Lo, Hi, Lo, Hi))
    lin = w.s([abg, w.inst('crectcnr1')], 'syl', '( %s -> %s e. ( %s crect %s ) )' % (ph, Lo, Lo, Hi))
    hin = w.s([abg, w.inst('crectcnr3')], 'syl', '( %s -> %s e. ( %s crect %s ) )' % (ph, Hi, Lo, Hi))
    cvx = w.s([ab, D(w, ph, 'jca', [lin, hin], '( %s e. ( %s crect %s ) /\\ %s e. ( %s crect %s ) )' % (Lo, Lo, Hi, Hi, Lo, Hi)), w.inst('crectcvx')], 'syl2anc',
              '( %s -> ( %s cseg %s ) C_ ( %s crect %s ) )' % (ph, Lo, Hi, Lo, Hi))
    crc = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( %s crect %s ) C_ CC )' % (ph, Lo, Hi))
    uc = D(w, ph, 'sstrd', [cvx, crc], '( %s cseg %s ) C_ CC' % (Lo, Hi))
    return dict(Lo=Lo, Hi=Hi, loc=loc, hic=hic, ab=ab, cvx=cvx, uc=uc, reL=reL, reH=reH, U='( %s cseg %s )' % (Lo, Hi))


def on_line(w, A_, s, z, zU, lift):
    """z in the segment: ( A_ -> z e. CC ), ( A_ -> ( Re ` z ) = C ), ( A_ -> z = CP(C, Im z) ), ( A_ -> ( Im ` z ) e. RR )"""
    Lo, Hi = s['Lo'], s['Hi']
    zr = D(w, A_, 'sseldd', [lift(s['cvx'], '( %s cseg %s ) C_ ( %s crect %s )' % (Lo, Hi, Lo, Hi)), zU], '%s e. ( %s crect %s )' % (z, Lo, Hi))
    ec = w.s([lift(s['ab'], '( %s e. CC /\\ %s e. CC )' % (Lo, Hi)), w.inst('elcrect')], 'syl',
             '( %s -> ( %s e. ( %s crect %s ) <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A_, z, Lo, Hi, z, z, Lo, Hi, z, Lo, Hi))
    e3 = D(w, A_, 'mpbid', [zr, ec], '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (z, z, Lo, Hi, z, Lo, Hi))
    zc = w.s([e3, w.inst('simp1')], 'syl', '( %s -> %s e. CC )' % (A_, z))
    ri = D(w, A_, 'oveq12d', [lift(s['reL'], '( Re ` %s ) = C' % Lo), lift(s['reH'], '( Re ` %s ) = C' % Hi)], '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( C [,] C )' % (Lo, Hi))
    zre = D(w, A_, 'eleqtrd', [w.s([e3, w.inst('simp2')], 'syl', '( %s -> ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A_, z, Lo, Hi)), ri], '( Re ` %s ) e. ( C [,] C )' % z)
    cr = lift(None, None) if False else None
    return zc, zre, e3


if __name__ == '__main__' and (not only or 'zl3eseg' in only):
    w = W('zl3eseg', 'On a vertical segment of ` Re w = C ` the integral of ` G Q / ( 1 - Q ) ` with ` Q = e ^ ( A w ) ` is the sum of the integrals of the terms ` G e ^ ( k A w ) ` of its geometric expansion.')
    ph, concl = ante_of(S['zl3eseg'])
    e0 = w.s([], 'simpl', '( %s -> %s )' % (ph, EDGA))
    trp = w.s([], 'simpr', '( %s -> T e. RR+ )' % ph)
    d = edga_ctx(w, ph, e0)
    tr = D(w, ph, 'rpred', [trp], 'T e. RR'); tpos = D(w, ph, 'rpgt0d', [trp], '0 < T')
    s = seg_ctx(w, ph, d, 'T', tr, tpos)
    Lo, Hi, U = s['Lo'], s['Hi'], s['U']
    FAMB = lambda n, v: '( ( G ` %s ) x. ( exp ` ( ( %s x. A ) x. %s ) ) )' % (v, n, v)
    FAMn = lambda n: '( v e. %s |-> %s )' % (U, FAMB(n, 'v'))
    FAM = '( n e. NN |-> %s )' % FAMn('n')
    M = '( n e. NN |-> ( K x. ( %s ^ n ) ) )' % RR_
    # generic point facts on the segment
    def point(A_, z, zU, lift):
        zc, zre, e3 = on_line(w, A_, s, z, zU, lift)
        crA = lift(d['cr'], 'C e. RR')
        zre3 = D(w, A_, 'mpbid', [zre, w.s([crA, crA, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` %s ) e. ( C [,] C ) <-> ( ( Re ` %s ) e. RR /\\ C <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ C ) ) )' % (A_, z, z, z, z))],
                 '( ( Re ` %s ) e. RR /\\ C <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ C )' % (z, z, z))
        rzr = w.s([zre3, w.inst('simp1')], 'syl', '( %s -> ( Re ` %s ) e. RR )' % (A_, z))
        rez = D(w, A_, 'mpbird', [D(w, A_, 'jca', [w.s([zre3, w.inst('simp3')], 'syl', '( %s -> ( Re ` %s ) <_ C )' % (A_, z)), w.s([zre3, w.inst('simp2')], 'syl', '( %s -> C <_ ( Re ` %s ) )' % (A_, z))],
                                        '( ( Re ` %s ) <_ C /\\ C <_ ( Re ` %s ) )' % (z, z)), D(w, A_, 'letri3d', [rzr, crA], '( ( Re ` %s ) = C <-> ( ( Re ` %s ) <_ C /\\ C <_ ( Re ` %s ) ) )' % (z, z, z))],
                  '( Re ` %s ) = C' % z)
        izr = D(w, A_, 'imcld', [zc], '( Im ` %s ) e. RR' % z)
        zeq = D(w, A_, 'eqtrd', [D(w, A_, 'replimd', [zc], '%s = ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (z, z, z)), D(w, A_, 'oveq1d', [rez], '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) = %s' % (z, z, CP('C', '( Im ` %s )' % z)))],
                '%s = %s' % (z, CP('C', '( Im ` %s )' % z)))
        return dict(zc=zc, rez=rez, izr=izr, zeq=zeq)
    def expabs(A_, cN, NN_, z, pz, lift):
        """( A_ -> ( abs ` ( exp ` ( ( N x. A ) x. z ) ) ) = ( R ^ N ) ) for N a step name proving N e. NN"""
        Nn = cN
        nz = D(w, A_, 'nnzd', [NN_], '%s e. ZZ' % Nn); nr = D(w, A_, 'zred', [nz], '%s e. RR' % Nn); nc_ = D(w, A_, 'zcnd', [nz], '%s e. CC' % Nn)
        arA = lift(d['ar'], 'A e. RR'); crA = lift(d['cr'], 'C e. RR')
        nar = D(w, A_, 'remulcld', [nr, arA], '( %s x. A ) e. RR' % Nn)
        arg = '( ( %s x. A ) x. %s )' % (Nn, z)
        argc = D(w, A_, 'mulcld', [D(w, A_, 'recnd', [nar], '( %s x. A ) e. CC' % Nn), pz['zc']], '%s e. CC' % arg)
        a1 = w.s([argc, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` %s ) ) = ( exp ` ( Re ` %s ) ) )' % (A_, arg, arg))
        a2 = w.s([nar, pz['zc'], w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( %s x. A ) x. ( Re ` %s ) ) )' % (A_, arg, Nn, z))
        a3 = D(w, A_, 'oveq2d', [pz['rez']], '( ( %s x. A ) x. ( Re ` %s ) ) = ( ( %s x. A ) x. C )' % (Nn, z, Nn))
        a4 = D(w, A_, 'mulassd', [nc_, D(w, A_, 'recnd', [arA], 'A e. CC'), D(w, A_, 'recnd', [crA], 'C e. CC')], '( ( %s x. A ) x. C ) = ( %s x. ( A x. C ) )' % (Nn, Nn))
        a5 = w.s([D(w, A_, 'recnd', [lift(d['acr'], '( A x. C ) e. RR')], '( A x. C ) e. CC'), nz, w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` ( %s x. ( A x. C ) ) ) = ( %s ^ %s ) )' % (A_, Nn, RR_, Nn))
        re = chain_eq(w, A_, '( Re ` %s )' % arg, [(a2, '( ( %s x. A ) x. ( Re ` %s ) )' % (Nn, z)), (a3, '( ( %s x. A ) x. C )' % Nn), (a4, '( %s x. ( A x. C ) )' % Nn)])
        return chain_eq(w, A_, '( abs ` ( exp ` %s ) )' % arg, [(a1, '( exp ` ( Re ` %s ) )' % arg), (D(w, A_, 'fveq2d', [re], '( exp ` ( Re ` %s ) ) = ( exp ` ( %s x. ( A x. C ) ) )' % (arg, Nn)), '( exp ` ( %s x. ( A x. C ) ) )' % Nn),
                                                                     (a5, '( %s ^ %s )' % (RR_, Nn))])
    # value of the family
    def famval(A_, J, Y, jN, yU):
        E = 'n = %s' % J
        sb = w.s([D(w, E, 'oveq2d', [D(w, E, 'fveq2d', [D(w, E, 'oveq1d', [D(w, E, 'oveq1d', [w.s([], 'id', '( %s -> %s )' % (E, E))], '( n x. A ) = ( %s x. A )' % J)],
                                                                         '( ( n x. A ) x. v ) = ( ( %s x. A ) x. v )' % J)], '( exp ` ( ( n x. A ) x. v ) ) = ( exp ` ( ( %s x. A ) x. v ) )' % J)],
                                     '%s = %s' % (FAMB('n', 'v'), FAMB(J, 'v')))], 'mpteq2dv', '( %s -> %s = %s )' % (E, FAMn('n'), FAMn(J)))
        f1 = w.s([sb, w.s([], 'eqid', '%s = %s' % (FAM, FAM)), w.s([w.s([], 'ovex', '%s e. _V' % U)], 'mptex', '%s e. _V' % FAMn(J))], 'fvmpt', '( %s e. NN -> ( %s ` %s ) = %s )' % (J, FAM, J, FAMn(J)))
        E2_ = 'v = %s' % Y
        e = w.s([], 'id', '( %s -> %s )' % (E2_, E2_))
        sb2 = D(w, E2_, 'oveq12d', [D(w, E2_, 'fveq2d', [e], '( G ` v ) = ( G ` %s )' % Y), D(w, E2_, 'fveq2d', [D(w, E2_, 'oveq2d', [e], '( ( %s x. A ) x. v ) = ( ( %s x. A ) x. %s )' % (J, J, Y))],
                                                                                         '( exp ` ( ( %s x. A ) x. v ) ) = ( exp ` ( ( %s x. A ) x. %s ) )' % (J, J, Y))], '%s = %s' % (FAMB(J, 'v'), FAMB(J, Y)))
        f2 = w.s([sb2, w.s([], 'eqid', '%s = %s' % (FAMn(J), FAMn(J))), w.s([], 'ovex', '%s e. _V' % FAMB(J, Y))], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (Y, U, FAMn(J), Y, FAMB(J, Y)))
        v1 = w.s([jN, f1], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, FAM, J, FAMn(J)))
        v2 = D(w, A_, 'fveq1d', [v1], '( ( %s ` %s ) ` %s ) = ( %s ` %s )' % (FAM, J, Y, FAMn(J), Y))
        return D(w, A_, 'eqtrd', [v2, w.s([yU, f2], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, FAMn(J), Y, FAMB(J, Y)))], '( ( %s ` %s ) ` %s ) = %s' % (FAM, J, Y, FAMB(J, Y)))
    # ---- the M-test hypotheses of z6lsum
    A2 = '( %s /\\ n e. NN )' % ph
    l2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    uc2 = l2(s['uc'], '%s C_ CC' % U)
    idU = w.s([uc2, cst(w, A2, 'ssid', 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( %s -> ( v e. %s |-> v ) e. ( %s -cn-> CC ) )' % (A2, U, U))
    gU = w.s([l2(d['gcn'], 'G e. ( CC -cn-> CC )'), idU], 'cncfmpt1f', '( %s -> ( v e. %s |-> ( G ` v ) ) e. ( %s -cn-> CC ) )' % (A2, U, U))
    nN2 = w.s([], 'simpr', '( %s -> n e. NN )' % A2)
    nac = D(w, A2, 'mulcld', [D(w, A2, 'nncnd', [nN2], 'n e. CC'), D(w, A2, 'recnd', [l2(d['ar'], 'A e. RR')], 'A e. CC')], '( n x. A ) e. CC')
    cU = w.s([nac, uc2, cst(w, A2, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( %s -> ( v e. %s |-> ( n x. A ) ) e. ( %s -cn-> CC ) )' % (A2, U, U))
    lU = w.s([cU, idU], 'mulcncf', '( %s -> ( v e. %s |-> ( ( n x. A ) x. v ) ) e. ( %s -cn-> CC ) )' % (A2, U, U))
    eU = w.s([cst(w, A2, 'efcn', 'exp e. ( CC -cn-> CC )'), lU], 'cncfmpt1f', '( %s -> ( v e. %s |-> ( exp ` ( ( n x. A ) x. v ) ) ) e. ( %s -cn-> CC ) )' % (A2, U, U))
    pU = w.s([gU, eU], 'mulcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (A2, FAMn('n'), U))
    famf = w.s([pU, w.s([], 'eqid', '%s = %s' % (FAM, FAM))], 'fmptd', '( %s -> %s : NN --> ( %s -cn-> CC ) )' % (ph, FAM, U))
    rn2 = D(w, A2, 'reexpcld', [l2(d['rr'], '%s e. RR' % RR_), D(w, A2, 'nnnn0d', [nN2], 'n e. NN0')], '( %s ^ n ) e. RR' % RR_)
    krn = D(w, A2, 'remulcld', [l2(d['kr'], 'K e. RR'), rn2], '( K x. ( %s ^ n ) ) e. RR' % RR_)
    mf = w.s([krn, w.s([], 'eqid', '%s = %s' % (M, M))], 'fmptd', '( %s -> %s : NN --> RR )' % (ph, M))
    # values of M
    P1 = '( %s /\\ k e. NN )' % ph
    kN = w.s([], 'simpr', '( %s -> k e. NN )' % P1)
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (P1, f))
    rk = D(w, P1, 'reexpcld', [l1(d['rr'], '%s e. RR' % RR_), D(w, P1, 'nnnn0d', [kN], 'k e. NN0')], '( %s ^ k ) e. RR' % RR_)
    krk = D(w, P1, 'remulcld', [l1(d['kr'], 'K e. RR'), rk], '( K x. ( %s ^ k ) ) e. RR' % RR_)
    mv = w.s([kN, w.s([w.s([w.s([], 'oveq2', '( n = k -> ( %s ^ n ) = ( %s ^ k ) )' % (RR_, RR_))], 'oveq2d', '( n = k -> ( K x. ( %s ^ n ) ) = ( K x. ( %s ^ k ) ) )' % (RR_, RR_)),
                      w.s([], 'eqid', '%s = %s' % (M, M)), w.s([], 'ovex', '( K x. ( %s ^ k ) ) e. _V' % RR_)], 'fvmpt', '( k e. NN -> ( %s ` k ) = ( K x. ( %s ^ k ) ) )' % (M, RR_))],
             'syl', '( %s -> ( %s ` k ) = ( K x. ( %s ^ k ) ) )' % (P1, M, RR_))
    krk0 = D(w, P1, 'mulge0d', [l1(d['kr'], 'K e. RR'), rk, D(w, P1, 'rpge0d', [l1(d['krp'], 'K e. RR+')], '0 <_ K'),
                                D(w, P1, 'expge0d', [l1(d['rr'], '%s e. RR' % RR_), D(w, P1, 'nnnn0d', [kN], 'k e. NN0'), l1(d['r0'], '0 <_ %s' % RR_)], '0 <_ ( %s ^ k )' % RR_)], '0 <_ ( K x. ( %s ^ k ) )' % RR_)
    mab = D(w, P1, 'eqtrd', [D(w, P1, 'fveq2d', [mv], '( abs ` ( %s ` k ) ) = ( abs ` ( K x. ( %s ^ k ) ) )' % (M, RR_)), D(w, P1, 'absidd', [krk, krk0], '( abs ` ( K x. ( %s ^ k ) ) ) = ( K x. ( %s ^ k ) )' % (RR_, RR_))],
            '( abs ` ( %s ` k ) ) = ( K x. ( %s ^ k ) )' % (M, RR_))
    mser = w.s([d['kr'], d['rr'], d['r0'], d['r1'], D(w, P1, 'recnd', [D(w, P1, 'eqeltrd', [mv, krk], '( %s ` k ) e. RR' % M)], '( %s ` k ) e. CC' % M),
                D(w, P1, 'eqbrtrd', [mab, D(w, P1, 'leidd', [krk], '( K x. ( %s ^ k ) ) <_ ( K x. ( %s ^ k ) )' % (RR_, RR_))], '( abs ` ( %s ` k ) ) <_ ( K x. ( %s ^ k ) )' % (M, RR_))],
               'zl3mser', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( K x. %s ) / ( 1 - %s ) ) ) )' % (ph, M, M, RR_, RR_))
    mdm = w.s([mser, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, M))
    # the bound
    A3 = '( ( %s /\\ j e. NN ) /\\ y e. %s )' % (ph, U)
    l3 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A3, f))
    jN = w.s([], 'simplr', '( %s -> j e. NN )' % A3); yU = w.s([], 'simpr', '( %s -> y e. %s )' % (A3, U))
    py = point(A3, 'y', yU, l3)
    fv3 = famval(A3, 'j', 'y', jN, yU)
    gyb = gb_at(w, A3, l3(d['gb'], GB), '( Im ` y )', py['izr'])
    gy = D(w, A3, 'eqtrd', [D(w, A3, 'fveq2d', [py['zeq']], '( G ` y ) = ( G ` %s )' % CP('C', '( Im ` y )')), D(w, A3, 'eqidd', [], '( G ` %s ) = ( G ` %s )' % (CP('C', '( Im ` y )'), CP('C', '( Im ` y )')))],
           '( G ` y ) = ( G ` %s )' % CP('C', '( Im ` y )'))
    gyb2 = D(w, A3, 'eqbrtrd', [D(w, A3, 'fveq2d', [gy], '( abs ` ( G ` y ) ) = ( abs ` ( G ` %s ) )' % CP('C', '( Im ` y )')), gyb], '( abs ` ( G ` y ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` y ) ) ) )')
    kr3 = l3(d['kr'], 'K e. RR')
    iya = D(w, A3, 'abscld', [D(w, A3, 'recnd', [py['izr']], '( Im ` y ) e. CC')], '( abs ` ( Im ` y ) ) e. RR')
    p2 = D(w, A3, 'rpred', [D(w, A3, 'rpcxpcld', [cst(w, A3, '2rp', '2 e. RR+'), D(w, A3, 'renegcld', [iya], '-u ( abs ` ( Im ` y ) ) e. RR')], '( 2 ^c -u ( abs ` ( Im ` y ) ) ) e. RR+')],
           '( 2 ^c -u ( abs ` ( Im ` y ) ) ) e. RR')
    le1 = D(w, A3, 'mpbid', [D(w, A3, 'mpbid', [D(w, A3, 'absge0d', [D(w, A3, 'recnd', [py['izr']], '( Im ` y ) e. CC')], '0 <_ ( abs ` ( Im ` y ) )'),
                                                D(w, A3, 'le0neg2d', [iya], '( 0 <_ ( abs ` ( Im ` y ) ) <-> -u ( abs ` ( Im ` y ) ) <_ 0 )')], '-u ( abs ` ( Im ` y ) ) <_ 0'),
                             w.s([w.s([cst(w, A3, '2re', '2 e. RR'), cst(w, A3, '1lt2', '1 < 2')], 'jca', '( %s -> ( 2 e. RR /\\ 1 < 2 ) )' % A3),
                                  w.s([D(w, A3, 'renegcld', [iya], '-u ( abs ` ( Im ` y ) ) e. RR'), cst(w, A3, '0re', '0 e. RR')], 'jca', '( %s -> ( -u ( abs ` ( Im ` y ) ) e. RR /\\ 0 e. RR ) )' % A3), w.inst('cxple')],
                                 'syl2anc', '( %s -> ( -u ( abs ` ( Im ` y ) ) <_ 0 <-> ( 2 ^c -u ( abs ` ( Im ` y ) ) ) <_ ( 2 ^c 0 ) ) )' % A3)],
              '( 2 ^c -u ( abs ` ( Im ` y ) ) ) <_ ( 2 ^c 0 )')
    le2 = D(w, A3, 'breqtrd', [le1, w.s([cst(w, A3, '2cn', '2 e. CC'), w.inst('cxp0')], 'syl', '( %s -> ( 2 ^c 0 ) = 1 )' % A3)], '( 2 ^c -u ( abs ` ( Im ` y ) ) ) <_ 1')
    k0 = D(w, A3, 'rpge0d', [l3(d['krp'], 'K e. RR+')], '0 <_ K')
    le3 = D(w, A3, 'lemul2ad' if False else 'lemul2ad', [p2, cst(w, A3, '1re', '1 e. RR'), kr3, k0, le2], '( K x. ( 2 ^c -u ( abs ` ( Im ` y ) ) ) ) <_ ( K x. 1 )') if False else None
    le3 = D(w, A3, 'eqbrtrd' if False else 'breqtrd', [D(w, A3, 'lemul2ad', [p2, cst(w, A3, '1re', '1 e. RR'), kr3, k0, le2], '( K x. ( 2 ^c -u ( abs ` ( Im ` y ) ) ) ) <_ ( K x. 1 )'),
                                                        D(w, A3, 'mulridd', [D(w, A3, 'recnd', [kr3], 'K e. CC')], '( K x. 1 ) = K')], '( K x. ( 2 ^c -u ( abs ` ( Im ` y ) ) ) ) <_ K')
    gyK = D(w, A3, 'letrd', [D(w, A3, 'abscld', [D(w, A3, 'ffvelcdmd', [w.s([l3(d['gcn'], 'G e. ( CC -cn-> CC )'), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % A3), py['zc']], '( G ` y ) e. CC')],
                                          '( abs ` ( G ` y ) ) e. RR'), D(w, A3, 'remulcld', [kr3, p2], '( K x. ( 2 ^c -u ( abs ` ( Im ` y ) ) ) ) e. RR'), kr3, gyb2, le3], '( abs ` ( G ` y ) ) <_ K')
    ea = expabs(A3, 'j', jN, 'y', py, l3)
    gyc = D(w, A3, 'ffvelcdmd', [w.s([l3(d['gcn'], 'G e. ( CC -cn-> CC )'), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % A3), py['zc']], '( G ` y ) e. CC')
    jz = D(w, A3, 'nnzd', [jN], 'j e. ZZ')
    eyc = w.s([D(w, A3, 'mulcld', [D(w, A3, 'mulcld', [D(w, A3, 'zcnd', [jz], 'j e. CC'), D(w, A3, 'recnd', [l3(d['ar'], 'A e. RR')], 'A e. CC')], '( j x. A ) e. CC'), py['zc']],
                              '( ( j x. A ) x. y ) e. CC'), w.inst('efcl')], 'syl', '( %s -> ( exp ` ( ( j x. A ) x. y ) ) e. CC )' % A3)
    fa = D(w, A3, 'eqtrd', [D(w, A3, 'fveq2d', [fv3], '( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s )' % (FAM, FAMB('j', 'y'))), D(w, A3, 'absmuld', [gyc, eyc], '( abs ` %s ) = ( ( abs ` ( G ` y ) ) x. ( abs ` ( exp ` ( ( j x. A ) x. y ) ) ) )' % FAMB('j', 'y'))],
           '( abs ` ( ( %s ` j ) ` y ) ) = ( ( abs ` ( G ` y ) ) x. ( abs ` ( exp ` ( ( j x. A ) x. y ) ) ) )' % FAM)
    rj = D(w, A3, 'reexpcld', [l3(d['rr'], '%s e. RR' % RR_), D(w, A3, 'nnnn0d', [jN], 'j e. NN0')], '( %s ^ j ) e. RR' % RR_)
    fb = D(w, A3, 'lemul12ad', [D(w, A3, 'abscld', [gyc], '( abs ` ( G ` y ) ) e. RR'), kr3, D(w, A3, 'abscld', [eyc], '( abs ` ( exp ` ( ( j x. A ) x. y ) ) ) e. RR'), rj,
                                D(w, A3, 'absge0d', [gyc], '0 <_ ( abs ` ( G ` y ) )'), D(w, A3, 'absge0d', [eyc], '0 <_ ( abs ` ( exp ` ( ( j x. A ) x. y ) ) )'), gyK,
                                D(w, A3, 'eqled', [ea], '( abs ` ( exp ` ( ( j x. A ) x. y ) ) ) <_ ( %s ^ j )' % RR_)],
           '( ( abs ` ( G ` y ) ) x. ( abs ` ( exp ` ( ( j x. A ) x. y ) ) ) ) <_ ( K x. ( %s ^ j ) )' % RR_)
    mvj = w.s([jN, w.s([w.s([w.s([], 'oveq2', '( n = j -> ( %s ^ n ) = ( %s ^ j ) )' % (RR_, RR_))], 'oveq2d', '( n = j -> ( K x. ( %s ^ n ) ) = ( K x. ( %s ^ j ) ) )' % (RR_, RR_)),
                       w.s([], 'eqid', '%s = %s' % (M, M)), w.s([], 'ovex', '( K x. ( %s ^ j ) ) e. _V' % RR_)], 'fvmpt', '( j e. NN -> ( %s ` j ) = ( K x. ( %s ^ j ) ) )' % (M, RR_))],
              'syl', '( %s -> ( %s ` j ) = ( K x. ( %s ^ j ) ) )' % (A3, M, RR_))
    bnd = D(w, A3, 'breqtrrd', [D(w, A3, 'eqbrtrd', [fa, fb], '( abs ` ( ( %s ` j ) ` y ) ) <_ ( K x. ( %s ^ j ) )' % (FAM, RR_)), mvj], '( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (FAM, M))
    allb = w.s([w.s([bnd], 'anasss', '( ( %s /\\ ( j e. NN /\\ y e. %s ) ) -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (ph, U, FAM, M))], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (ph, U, FAM, M))
    Z = '( z e. %s |-> sum_ k e. NN ( ( %s ` k ) ` z ) )' % (U, FAM)
    ls = w.s([s['ab'], D(w, ph, 'jca', [D(w, ph, 'ssidd', [], '%s C_ %s' % (U, U)), D(w, ph, 'jca', [famf, w.s([mf, mdm, allb], '3jca', '( %s -> ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) ) )' % (ph, M, M, U, FAM, M))],
                                                                                         '( %s : NN --> ( %s -cn-> CC ) /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) ) )' % (FAM, U, M, M, U, FAM, M))],
                                   '( %s C_ %s /\\ ( %s : NN --> ( %s -cn-> CC ) /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) ) ) )' % (U, U, FAM, U, M, M, U, FAM, M)),
               w.inst('z6lsum')], 'syl2anc',
              '( %s -> seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> ( %s lint <. %s , %s >. ) )' % (ph, FAM, Lo, Hi, Z, Lo, Hi))
    # (i) the terms
    GK = GKE('G', 'A')
    A4 = '( ( %s /\\ k e. NN ) /\\ z e. %s )' % (ph, U)
    l4 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A4, f))
    kN4 = w.s([], 'simplr', '( %s -> k e. NN )' % A4); zU4 = w.s([], 'simpr', '( %s -> z e. %s )' % (A4, U))
    pz4 = point(A4, 'z', zU4, l4)
    fz4 = famval(A4, 'k', 'z', kN4, zU4)
    E_ = 'y = z'
    gke = w.s([D(w, E_, 'oveq12d', [D(w, E_, 'fveq2d', [w.s([], 'id', '( y = z -> y = z )')], '( G ` y ) = ( G ` z )'),
                                    D(w, E_, 'fveq2d', [D(w, E_, 'oveq2d', [w.s([], 'id', '( y = z -> y = z )')], '( ( k x. A ) x. y ) = ( ( k x. A ) x. z )')], '( exp ` ( ( k x. A ) x. y ) ) = ( exp ` ( ( k x. A ) x. z ) )')],
                        '( ( G ` y ) x. ( exp ` ( ( k x. A ) x. y ) ) ) = ( ( G ` z ) x. ( exp ` ( ( k x. A ) x. z ) ) )'), w.s([], 'eqid', '%s = %s' % (GK, GK)),
               w.s([], 'ovex', '( ( G ` z ) x. ( exp ` ( ( k x. A ) x. z ) ) ) e. _V')], 'fvmpt', '( z e. CC -> ( %s ` z ) = ( ( G ` z ) x. ( exp ` ( ( k x. A ) x. z ) ) ) )' % GK)
    gz4 = w.s([pz4['zc'], gke], 'syl', '( %s -> ( %s ` z ) = ( ( G ` z ) x. ( exp ` ( ( k x. A ) x. z ) ) ) )' % (A4, GK))
    te = D(w, A4, 'eqtr4d', [fz4, gz4], '( ( %s ` k ) ` z ) = ( %s ` z )' % (FAM, GK))
    tall = w.s([te], 'ralrimiva', '( ( %s /\\ k e. NN ) -> A. z e. %s ( ( %s ` k ) ` z ) = ( %s ` z ) )' % (ph, U, FAM, GK))
    P2 = '( %s /\\ k e. NN )' % ph
    lq = w.s([w.s([w.s([s['ab']], 'adantr', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (P2, Lo, Hi)), D(w, P2, 'jca', [cst(w, P2, 'fvex', '( %s ` k ) e. _V' % FAM), cst(w, P2, 'cnex', 'CC e. _V') if False else w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'mptex', '%s e. _V' % GK)], 'a1i', '( %s -> %s e. _V )' % (P2, GK))],
                                                                                                         '( ( %s ` k ) e. _V /\\ %s e. _V )' % (FAM, GK))], 'jca',
                   '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( %s ` k ) e. _V /\\ %s e. _V ) ) )' % (P2, Lo, Hi, FAM, GK)), tall, w.inst('linteq')], 'syl2anc',
             '( %s -> ( ( %s ` k ) lint <. %s , %s >. ) = %s )' % (P2, FAM, Lo, Hi, LT(GK, 'C', 'T')))
    meq = w.s([lq], 'mpteq2dva', '( %s -> ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) = ( k e. NN |-> %s ) )' % (ph, FAM, Lo, Hi, LT(GK, 'C', 'T')))
    # (ii) the sum function equals P on the segment
    A5 = '( %s /\\ z e. %s )' % (ph, U)
    l5 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A5, f))
    zU5 = w.s([], 'simpr', '( %s -> z e. %s )' % (A5, U))
    pz5 = point(A5, 'z', zU5, l5)
    AZ = '( A x. z )'; QZ = '( exp ` %s )' % AZ
    A6 = '( %s /\\ k e. NN )' % A5
    kN6 = w.s([], 'simpr', '( %s -> k e. NN )' % A6)
    zU6 = w.s([zU5], 'adantr', '( %s -> z e. %s )' % (A6, U))
    fz6 = famval(A6, 'k', 'z', kN6, zU6)
    kc6 = D(w, A6, 'nncnd', [kN6], 'k e. CC'); ac6 = D(w, A6, 'recnd', [w.s([l5(d['ar'], 'A e. RR')], 'adantr', '( %s -> A e. RR )' % A6)], 'A e. CC')
    zc6 = w.s([pz5['zc']], 'adantr', '( %s -> z e. CC )' % A6)
    x1 = D(w, A6, 'mulassd', [kc6, ac6, zc6], '( ( k x. A ) x. z ) = ( k x. %s )' % AZ)
    x2 = w.s([D(w, A6, 'mulcld', [ac6, zc6], '%s e. CC' % AZ), D(w, A6, 'nnzd', [kN6], 'k e. ZZ'), w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` ( k x. %s ) ) = ( %s ^ k ) )' % (A6, AZ, QZ))
    x3 = D(w, A6, 'eqtrd', [D(w, A6, 'fveq2d', [x1], '( exp ` ( ( k x. A ) x. z ) ) = ( exp ` ( k x. %s ) )' % AZ), x2], '( exp ` ( ( k x. A ) x. z ) ) = ( %s ^ k )' % QZ)
    x4 = D(w, A6, 'eqtrd', [fz6, D(w, A6, 'oveq2d', [x3], '( ( G ` z ) x. ( exp ` ( ( k x. A ) x. z ) ) ) = ( ( G ` z ) x. ( %s ^ k ) )' % QZ)], '( ( %s ` k ) ` z ) = ( ( G ` z ) x. ( %s ^ k ) )' % (FAM, QZ))
    se = w.s([x4], 'sumeq2dv', '( %s -> sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN ( ( G ` z ) x. ( %s ^ k ) ) )' % (A5, FAM, QZ))
    gzc = D(w, A5, 'ffvelcdmd', [w.s([l5(d['gcn'], 'G e. ( CC -cn-> CC )'), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % A5), pz5['zc']], '( G ` z ) e. CC')
    azc = D(w, A5, 'mulcld', [D(w, A5, 'recnd', [l5(d['ar'], 'A e. RR')], 'A e. CC'), pz5['zc']], '%s e. CC' % AZ)
    qzc = w.s([azc, w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A5, QZ))
    qa1 = w.s([azc, w.inst('absef')], 'syl', '( %s -> ( abs ` %s ) = ( exp ` ( Re ` %s ) ) )' % (A5, QZ, AZ))
    qa2 = w.s([l5(d['ar'], 'A e. RR'), pz5['zc'], w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` %s ) = ( A x. ( Re ` z ) ) )' % (A5, AZ))
    qa3 = D(w, A5, 'oveq2d', [pz5['rez']], '( A x. ( Re ` z ) ) = ( A x. C )')
    qa = chain_eq(w, A5, '( abs ` %s )' % QZ, [(qa1, '( exp ` ( Re ` %s ) )' % AZ), (D(w, A5, 'fveq2d', [D(w, A5, 'eqtrd', [qa2, qa3], '( Re ` %s ) = ( A x. C )' % AZ)], '( exp ` ( Re ` %s ) ) = %s' % (AZ, RR_)), RR_)])
    qlt = D(w, A5, 'eqbrtrd', [qa, l5(d['r1'], '%s < 1' % RR_)], '( abs ` %s ) < 1' % QZ)
    geo = w.s([gzc, qzc, qlt, w.inst('geoisum1c')], 'syl3anc', '( %s -> sum_ k e. NN ( ( G ` z ) x. ( %s ^ k ) ) = ( ( ( G ` z ) x. %s ) / ( 1 - %s ) ) )' % (A5, QZ, QZ, QZ))
    ZB = 'sum_ k e. NN ( ( %s ` k ) ` z )' % FAM
    zsum = D(w, A5, 'eqtrd', [se, geo], '%s = ( ( ( G ` z ) x. %s ) / ( 1 - %s ) )' % (ZB, QZ, QZ))
    zv = w.s([zU5, w.s([w.s([], 'id', '( z = z -> z = z )')] if False else [], 'eqid', 'x') if False else None, None], 'x', 'x') if False else None
    zfv = w.s([zU5, w.s([], 'eqid', '%s = %s' % (Z, Z)), w.inst('fvmpt2')], 'x', 'x') if False else None
    Za = '( a e. %s |-> sum_ k e. NN ( ( %s ` k ) ` a ) )' % (U, FAM)
    Ea = 'a = z'
    Ek = '( a = z /\\ k e. NN )'
    subk = D(w, Ek, 'fveq2d', [w.s([w.s([], 'id', '( a = z -> a = z )')], 'adantr', '( %s -> a = z )' % Ek)], '( ( %s ` k ) ` a ) = ( ( %s ` k ) ` z )' % (FAM, FAM))
    suba = w.s([subk], 'sumeq2dv', '( a = z -> sum_ k e. NN ( ( %s ` k ) ` a ) = %s )' % (FAM, ZB))
    zfv = w.s([zU5, w.s([suba, w.s([], 'eqid', '%s = %s' % (Za, Za)), w.s([], 'sumex', '%s e. _V' % ZB)], 'fvmpt', '( z e. %s -> ( %s ` z ) = %s )' % (U, Za, ZB))], 'syl',
              '( %s -> ( %s ` z ) = %s )' % (A5, Za, ZB))
    Z0 = Z
    Z = Za
    pvz = pv_at(w, A5, l5(d['pval'], PV), '( Im ` z )', pz5['izr'])
    zc_ = CP('C', '( Im ` z )')
    pz_ = D(w, A5, 'eqtrd', [D(w, A5, 'fveq2d', [pz5['zeq']], '( P ` z ) = ( P ` %s )' % zc_), pvz], '( P ` z ) = %s' % PVb('( Im ` z )'))
    # rewrite PVb(Im z) back to z
    zq = D(w, A5, 'eqcomd', [pz5['zeq']], '%s = z' % zc_)
    b1 = D(w, A5, 'fveq2d', [zq], '( G ` %s ) = ( G ` z )' % zc_)
    b2 = D(w, A5, 'fveq2d', [D(w, A5, 'oveq2d', [zq], '( A x. %s ) = %s' % (zc_, AZ))], '( exp ` ( A x. %s ) ) = %s' % (zc_, QZ))
    b3 = D(w, A5, 'oveq12d', [D(w, A5, 'oveq12d', [b1, b2], '( ( G ` %s ) x. ( exp ` ( A x. %s ) ) ) = ( ( G ` z ) x. %s )' % (zc_, zc_, QZ)), D(w, A5, 'oveq2d', [b2], '( 1 - ( exp ` ( A x. %s ) ) ) = ( 1 - %s )' % (zc_, QZ))],
           '%s = ( ( ( G ` z ) x. %s ) / ( 1 - %s ) )' % (PVb('( Im ` z )'), QZ, QZ))
    pzz = D(w, A5, 'eqtrd', [pz_, b3], '( P ` z ) = ( ( ( G ` z ) x. %s ) / ( 1 - %s ) )' % (QZ, QZ))
    zp = D(w, A5, 'eqtr4d', [D(w, A5, 'eqtrd', [zfv, zsum], '( %s ` z ) = ( ( ( G ` z ) x. %s ) / ( 1 - %s ) )' % (Z, QZ, QZ)), pzz], '( %s ` z ) = ( P ` z )' % Z)
    zall = w.s([zp], 'ralrimiva', '( %s -> A. z e. %s ( %s ` z ) = ( P ` z ) )' % (ph, U, Z))
    zlq = w.s([D(w, ph, 'jca', [s['ab'], D(w, ph, 'jca', [w.s([w.s([w.s([], 'ovex', '%s e. _V' % U)], 'mptex', '%s e. _V' % Z)], 'a1i', '( %s -> %s e. _V )' % (ph, Z)), w.s([d['pv'], w.inst('elex')], 'syl', '( %s -> P e. _V )' % ph)],
                                                           '( %s e. _V /\\ P e. _V )' % Z)], '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ P e. _V ) )' % (Lo, Hi, Z)), zall, w.inst('linteq')], 'syl2anc',
              '( %s -> ( %s lint <. %s , %s >. ) = %s )' % (ph, Z, Lo, Hi, LT('P', 'C', 'T')))
    subz = D(w, 'z = a', 'fveq2d', [w.s([], 'id', '( z = a -> z = a )')], '( ( %s ` k ) ` z ) = ( ( %s ` k ) ` a )' % (FAM, FAM)) if False else None
    Ekz = '( z = a /\\ k e. NN )'
    subkz = D(w, Ekz, 'fveq2d', [w.s([w.s([], 'id', '( z = a -> z = a )')], 'adantr', '( %s -> z = a )' % Ekz)], '( ( %s ` k ) ` z ) = ( ( %s ` k ) ` a )' % (FAM, FAM))
    cbz = w.s([w.s([subkz], 'sumeq2dv', '( z = a -> %s = sum_ k e. NN ( ( %s ` k ) ` a ) )' % (ZB, FAM))], 'cbvmptv', '%s = %s' % (Z0, Za))
    ls2 = D(w, ph, 'breqtrd', [ls, D(w, ph, 'oveq1d', [w.s([cbz], 'a1i', '( %s -> %s = %s )' % (ph, Z0, Za))], '( %s lint <. %s , %s >. ) = ( %s lint <. %s , %s >. )' % (Z0, Lo, Hi, Za, Lo, Hi))],
            'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> ( %s lint <. %s , %s >. )' % (FAM, Lo, Hi, Za, Lo, Hi))
    ls = ls2
    fin = D(w, ph, 'mpbid', [ls, D(w, ph, 'breq12d', [D(w, ph, 'seqeq3d', [meq], 'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) = seq 1 ( + , ( k e. NN |-> %s ) )' % (FAM, Lo, Hi, LT(GK, 'C', 'T'))), zlq],
                                                      '( seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> ( %s lint <. %s , %s >. ) <-> seq 1 ( + , ( k e. NN |-> %s ) ) ~~> %s )' % (FAM, Lo, Hi, Z, Lo, Hi, LT(GK, 'C', 'T'), LT('P', 'C', 'T')))],
            'seq 1 ( + , ( k e. NN |-> %s ) ) ~~> %s' % (LT(GK, 'C', 'T'), LT('P', 'C', 'T')))
    w.qed([fin], 'idi', S['zl3eseg'])
    go(w, only)


# ---------------------------------------------------------------- zl3edgb
def lt_sub(w, E, e_step, G, C, x_old, x_new):
    """( E -> LT(G,C,x_old) = LT(G,C,x_new) ) from e_step: ( E -> x_old = x_new )"""
    ne = D(w, E, 'negeqd', [e_step], '-u %s = -u %s' % (x_old, x_new))
    lo = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [ne], '( _i x. -u %s ) = ( _i x. -u %s )' % (x_old, x_new))], '%s = %s' % (CP(C, '-u %s' % x_old), CP(C, '-u %s' % x_new)))
    hi = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [e_step], '( _i x. %s ) = ( _i x. %s )' % (x_old, x_new))], '%s = %s' % (CP(C, x_old), CP(C, x_new)))
    return D(w, E, 'oveq2d', [D(w, E, 'opeq12d', [lo, hi], '<. %s , %s >. = <. %s , %s >.' % (CP(C, '-u %s' % x_old), CP(C, x_old), CP(C, '-u %s' % x_new), CP(C, x_new)))],
             '%s = %s' % (LT(G, C, x_old), LT(G, C, x_new)))


def vl_e(G, C):
    return '( ~~>r ` ( e e. RR+ |-> %s ) )' % LT(G, C, 'e')


def vl_te(w, G, C):
    """closed: VL(G,C) = vl_e(G,C)"""
    cb = w.s([lt_sub(w, 't = e', w.s([], 'id', '( t = e -> t = e )'), G, C, 't', 'e')], 'cbvmptv', '( t e. RR+ |-> %s ) = ( e e. RR+ |-> %s )' % (LT(G, C, 't'), LT(G, C, 'e')))
    return w.s([cb], 'fveq2i', '%s = %s' % (VL(G, C), vl_e(G, C)))


if __name__ == '__main__' and (not only or 'zl3edgb' in only):
    w = W('zl3edgb', 'The long side ` Re w = C ` of ` R_N ` at height ` T `: the integral of ` G Q / ( 1 - Q ) ` differs from the sum of the vertical-line integrals of the geometric terms by ` O ( 2 ^ ( -T / 4 ) ) `.')
    ph, concl = ante_of(S['zl3edgb'])
    e0 = w.s([], 'simpl', '( %s -> %s )' % (ph, EDGA))
    tt = w.s([], 'simpr', '( %s -> ( T e. RR+ /\\ 1 <_ T ) )' % ph)
    trp = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR+ )' % ph); t1 = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 1 <_ T )' % ph)
    d = edga_ctx(w, ph, e0)
    GK = GKE('G', 'A'); GKj = GKE('G', 'A', 'j')
    VLk = VL(GK, 'C'); VLj = VL(GKj, 'C'); LTk = LT(GK, 'C', 'T'); LTj = LT(GKj, 'C', 'T')
    P1 = '( %s /\\ k e. NN )' % ph
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (P1, f))
    kN = w.s([], 'simpr', '( %s -> k e. NN )' % P1)
    kz = D(w, P1, 'nnzd', [kN], 'k e. ZZ'); kc = D(w, P1, 'zcnd', [kz], 'k e. CC'); kn0 = D(w, P1, 'nnnn0d', [kN], 'k e. NN0')
    arP = l1(d['ar'], 'A e. RR'); crP = l1(d['cr'], 'C e. RR'); krP = l1(d['kr'], 'K e. RR')
    kar = D(w, P1, 'remulcld', [D(w, P1, 'zred', [kz], 'k e. RR'), arP], '( k x. A ) e. RR')
    # continuity of the k-th term
    cc_ = cst(w, P1, 'ssid', 'CC C_ CC')
    idC = w.s([cc_, cc_, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( y e. CC |-> y ) e. ( CC -cn-> CC ) )' % P1)
    gC = w.s([l1(d['gcn'], 'G e. ( CC -cn-> CC )'), idC], 'cncfmpt1f', '( %s -> ( y e. CC |-> ( G ` y ) ) e. ( CC -cn-> CC ) )' % P1)
    cC = w.s([D(w, P1, 'recnd', [kar], '( k x. A ) e. CC'), cc_, cc_, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( y e. CC |-> ( k x. A ) ) e. ( CC -cn-> CC ) )' % P1)
    lC = w.s([cC, idC], 'mulcncf', '( %s -> ( y e. CC |-> ( ( k x. A ) x. y ) ) e. ( CC -cn-> CC ) )' % P1)
    eC = w.s([cst(w, P1, 'efcn', 'exp e. ( CC -cn-> CC )'), lC], 'cncfmpt1f', '( %s -> ( y e. CC |-> ( exp ` ( ( k x. A ) x. y ) ) ) e. ( CC -cn-> CC ) )' % P1)
    gkC = w.s([gC, eC], 'mulcncf', '( %s -> %s e. ( CC -cn-> CC ) )' % (P1, GK))
    # the line lies in CC
    P2 = '( %s /\\ u e. RR )' % P1
    l2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (P2, f))
    uR = w.s([], 'simpr', '( %s -> u e. RR )' % P2)
    w0 = CP('C', 'u')
    w0c = cpcl(w, P2, 'C', 'u', l2(crP, 'C e. RR'), uR)
    linC = w.s([w0c], 'ralrimiva', '( %s -> A. u e. RR %s e. CC )' % (P1, w0))
    # the bound on the line
    ew = w.s([w.s([], 'id', '( y = %s -> y = %s )' % (w0, w0))], 'x', 'x') if False else None
    Ey = 'y = %s' % w0
    ey = w.s([], 'id', '( %s -> %s )' % (Ey, Ey))
    sub = D(w, Ey, 'oveq12d', [D(w, Ey, 'fveq2d', [ey], '( G ` y ) = ( G ` %s )' % w0), D(w, Ey, 'fveq2d', [D(w, Ey, 'oveq2d', [ey], '( ( k x. A ) x. y ) = ( ( k x. A ) x. %s )' % w0)], '( exp ` ( ( k x. A ) x. y ) ) = ( exp ` ( ( k x. A ) x. %s ) )' % w0)],
            '( ( G ` y ) x. ( exp ` ( ( k x. A ) x. y ) ) ) = ( ( G ` %s ) x. ( exp ` ( ( k x. A ) x. %s ) ) )' % (w0, w0))
    gkv = w.s([w0c, w.s([sub, w.s([], 'eqid', '%s = %s' % (GK, GK)), w.s([], 'ovex', '( ( G ` %s ) x. ( exp ` ( ( k x. A ) x. %s ) ) ) e. _V' % (w0, w0))], 'fvmpt',
                        '( %s e. CC -> ( %s ` %s ) = ( ( G ` %s ) x. ( exp ` ( ( k x. A ) x. %s ) ) ) )' % (w0, GK, w0, w0, w0))], 'syl',
              '( %s -> ( %s ` %s ) = ( ( G ` %s ) x. ( exp ` ( ( k x. A ) x. %s ) ) ) )' % (P2, GK, w0, w0, w0))
    arg = '( ( k x. A ) x. %s )' % w0
    argc = D(w, P2, 'mulcld', [D(w, P2, 'recnd', [l2(kar, '( k x. A ) e. RR')], '( k x. A ) e. CC'), w0c], '%s e. CC' % arg)
    x1 = w.s([argc, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` %s ) ) = ( exp ` ( Re ` %s ) ) )' % (P2, arg, arg))
    x2 = w.s([l2(kar, '( k x. A ) e. RR'), w0c, w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( k x. A ) x. ( Re ` %s ) ) )' % (P2, arg, w0))
    rw, iw = reim_cp(w, P2, 'C', 'u', l2(crP, 'C e. RR'), uR)
    x3 = D(w, P2, 'oveq2d', [rw], '( ( k x. A ) x. ( Re ` %s ) ) = ( ( k x. A ) x. C )' % w0)
    x4 = D(w, P2, 'mulassd', [l2(kc, 'k e. CC'), D(w, P2, 'recnd', [l2(arP, 'A e. RR')], 'A e. CC'), D(w, P2, 'recnd', [l2(crP, 'C e. RR')], 'C e. CC')], '( ( k x. A ) x. C ) = ( k x. ( A x. C ) )')
    x5 = w.s([D(w, P2, 'recnd', [l2(l1(d['acr'], '( A x. C ) e. RR'), '( A x. C ) e. RR')], '( A x. C ) e. CC'), l2(kz, 'k e. ZZ'), w.inst('efexp')], 'syl2anc',
             '( %s -> ( exp ` ( k x. ( A x. C ) ) ) = ( %s ^ k ) )' % (P2, RR_))
    rea = chain_eq(w, P2, '( Re ` %s )' % arg, [(x2, '( ( k x. A ) x. ( Re ` %s ) )' % w0), (x3, '( ( k x. A ) x. C )'), (x4, '( k x. ( A x. C ) )')])
    eab = chain_eq(w, P2, '( abs ` ( exp ` %s ) )' % arg, [(x1, '( exp ` ( Re ` %s ) )' % arg), (D(w, P2, 'fveq2d', [rea], '( exp ` ( Re ` %s ) ) = ( exp ` ( k x. ( A x. C ) ) )' % arg), '( exp ` ( k x. ( A x. C ) ) )'),
                                                          (x5, '( %s ^ k )' % RR_)])
    gb = gb_at(w, P2, l2(l1(d['gb'], GB), GB), 'u', uR)
    gwc = D(w, P2, 'ffvelcdmd', [w.s([l2(l1(d['gcn'], 'G e. ( CC -cn-> CC )'), 'G e. ( CC -cn-> CC )'), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % P2), w0c], '( G ` %s ) e. CC' % w0)
    ewc = w.s([argc, w.inst('efcl')], 'syl', '( %s -> ( exp ` %s ) e. CC )' % (P2, arg))
    au = D(w, P2, 'abscld', [D(w, P2, 'recnd', [uR], 'u e. CC')], '( abs ` u ) e. RR')
    P3 = '( %s /\\ 1 <_ ( abs ` u ) )' % P2
    l3 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (P3, f))
    u1 = w.s([], 'simpr', '( %s -> 1 <_ ( abs ` u ) )' % P3)
    au3 = l3(au, '( abs ` u ) e. RR')
    aurp = D(w, P3, 'elrpd', [au3, D(w, P3, 'ltletrd', [cst(w, P3, '0re', '0 e. RR'), cst(w, P3, '1re', '1 e. RR'), au3, cst(w, P3, '0lt1', '0 < 1'), u1], '0 < ( abs ` u )')], '( abs ` u ) e. RR+')
    q4 = D(w, P3, 'mpd', [D(w, P3, 'leidd', [au3], '( abs ` u ) <_ ( abs ` u )'),
                          w.s([au3, aurp, w.s([cst(w, P3, '4re', '4 e. RR') if False else cst(w, P3, '4pos', '0 < 4') if False else None, None], 'x', 'x') if False else
                               D(w, P3, 'jca', [cst(w, P3, '4rp', '4 e. RR+'), D(w, P3, 'ltled', [cst(w, P3, '1re', '1 e. RR'), cst(w, P3, '4re', '4 e. RR'), cst(w, P3, '1lt4', '1 < 4')], '1 <_ 4')], '( 4 e. RR+ /\\ 1 <_ 4 )'),
                               w.inst('ledivge1le')], 'syl3anc', '( %s -> ( ( abs ` u ) <_ ( abs ` u ) -> ( ( abs ` u ) / 4 ) <_ ( abs ` u ) ) )' % P3)], '( ( abs ` u ) / 4 ) <_ ( abs ` u )')
    au4 = D(w, P3, 'rerpdivcld', [au3, cst(w, P3, '4rp', '4 e. RR+')], '( ( abs ` u ) / 4 ) e. RR')
    q5 = D(w, P3, 'mpbid', [q4, D(w, P3, 'lenegd', [au4, au3], '( ( ( abs ` u ) / 4 ) <_ ( abs ` u ) <-> -u ( abs ` u ) <_ -u ( ( abs ` u ) / 4 ) )')], '-u ( abs ` u ) <_ -u ( ( abs ` u ) / 4 )')
    q6 = D(w, P3, 'mpbid', [q5, w.s([w.s([cst(w, P3, '2re', '2 e. RR'), cst(w, P3, '1lt2', '1 < 2')], 'jca', '( %s -> ( 2 e. RR /\\ 1 < 2 ) )' % P3),
                                     D(w, P3, 'jca', [D(w, P3, 'renegcld', [au3], '-u ( abs ` u ) e. RR'), D(w, P3, 'renegcld', [au4], '-u ( ( abs ` u ) / 4 ) e. RR')],
                                       '( -u ( abs ` u ) e. RR /\\ -u ( ( abs ` u ) / 4 ) e. RR )'), w.inst('cxple')], 'syl2anc',
                                    '( %s -> ( -u ( abs ` u ) <_ -u ( ( abs ` u ) / 4 ) <-> ( 2 ^c -u ( abs ` u ) ) <_ ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) )' % P3)],
            '( 2 ^c -u ( abs ` u ) ) <_ ( 2 ^c -u ( ( abs ` u ) / 4 ) )')
    E1 = '( 2 ^c -u ( abs ` u ) )'; E4 = '( 2 ^c -u ( ( abs ` u ) / 4 ) )'
    e1r = D(w, P3, 'rpred', [D(w, P3, 'rpcxpcld', [cst(w, P3, '2rp', '2 e. RR+'), D(w, P3, 'renegcld', [au3], '-u ( abs ` u ) e. RR')], '%s e. RR+' % E1)], '%s e. RR' % E1)
    e4r = D(w, P3, 'rpred', [D(w, P3, 'rpcxpcld', [cst(w, P3, '2rp', '2 e. RR+'), D(w, P3, 'renegcld', [au4], '-u ( ( abs ` u ) / 4 ) e. RR')], '%s e. RR+' % E4)], '%s e. RR' % E4)
    kr3 = l3(l2(krP, 'K e. RR'), 'K e. RR'); k03 = D(w, P3, 'rpge0d', [l3(l2(l1(d['krp'], 'K e. RR+'), 'K e. RR+'), 'K e. RR+')], '0 <_ K')
    gb3 = D(w, P3, 'letrd', [D(w, P3, 'abscld', [l3(gwc, '( G ` %s ) e. CC' % w0)], '( abs ` ( G ` %s ) ) e. RR' % w0), D(w, P3, 'remulcld', [kr3, e1r], '( K x. %s ) e. RR' % E1),
                             D(w, P3, 'remulcld', [kr3, e4r], '( K x. %s ) e. RR' % E4), l3(gb, '( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` u ) ) )' % w0),
                             D(w, P3, 'lemul2ad', [e1r, e4r, kr3, k03, q6], '( K x. %s ) <_ ( K x. %s )' % (E1, E4))], '( abs ` ( G ` %s ) ) <_ ( K x. %s )' % (w0, E4))
    rk3 = D(w, P3, 'reexpcld', [l3(l2(l1(d['rr'], '%s e. RR' % RR_), '%s e. RR' % RR_), '%s e. RR' % RR_), l3(l2(kn0, 'k e. NN0'), 'k e. NN0')], '( %s ^ k ) e. RR' % RR_)
    M_ = '( K x. ( %s ^ k ) )' % RR_
    fab = D(w, P3, 'eqtrd', [D(w, P3, 'fveq2d', [l3(gkv, '( %s ` %s ) = ( ( G ` %s ) x. ( exp ` %s ) )' % (GK, w0, w0, arg))], '( abs ` ( %s ` %s ) ) = ( abs ` ( ( G ` %s ) x. ( exp ` %s ) ) )' % (GK, w0, w0, arg)),
                             D(w, P3, 'absmuld', [l3(gwc, '( G ` %s ) e. CC' % w0), l3(ewc, '( exp ` %s ) e. CC' % arg)], '( abs ` ( ( G ` %s ) x. ( exp ` %s ) ) ) = ( ( abs ` ( G ` %s ) ) x. ( abs ` ( exp ` %s ) ) )' % (w0, arg, w0, arg))],
            '( abs ` ( %s ` %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( abs ` ( exp ` %s ) ) )' % (GK, w0, w0, arg))
    fb = D(w, P3, 'lemul12ad', [D(w, P3, 'abscld', [l3(gwc, '( G ` %s ) e. CC' % w0)], '( abs ` ( G ` %s ) ) e. RR' % w0), D(w, P3, 'remulcld', [kr3, e4r], '( K x. %s ) e. RR' % E4),
                                D(w, P3, 'abscld', [l3(ewc, '( exp ` %s ) e. CC' % arg)], '( abs ` ( exp ` %s ) ) e. RR' % arg), rk3,
                                D(w, P3, 'absge0d', [l3(gwc, '( G ` %s ) e. CC' % w0)], '0 <_ ( abs ` ( G ` %s ) )' % w0), D(w, P3, 'absge0d', [l3(ewc, '( exp ` %s ) e. CC' % arg)], '0 <_ ( abs ` ( exp ` %s ) )' % arg),
                                gb3, D(w, P3, 'eqled', [l3(eab, '( abs ` ( exp ` %s ) ) = ( %s ^ k )' % (arg, RR_))], '( abs ` ( exp ` %s ) ) <_ ( %s ^ k )' % (arg, RR_))],
           '( ( abs ` ( G ` %s ) ) x. ( abs ` ( exp ` %s ) ) ) <_ ( ( K x. %s ) x. ( %s ^ k ) )' % (w0, arg, E4, RR_))
    mm = D(w, P3, 'mul32d', [D(w, P3, 'recnd', [kr3], 'K e. CC'), D(w, P3, 'recnd', [e4r], '%s e. CC' % E4), D(w, P3, 'recnd', [rk3], '( %s ^ k ) e. CC' % RR_)],
           '( ( K x. %s ) x. ( %s ^ k ) ) = ( %s x. %s )' % (E4, RR_, M_, E4))
    bu = D(w, P3, 'breqtrd', [D(w, P3, 'eqbrtrd', [fab, fb], '( abs ` ( %s ` %s ) ) <_ ( ( K x. %s ) x. ( %s ^ k ) )' % (GK, w0, E4, RR_)), mm], '( abs ` ( %s ` %s ) ) <_ ( %s x. %s )' % (GK, w0, M_, E4))
    ball = w.s([w.s([bu], 'ex', '( %s -> ( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) )' % (P2, GK, w0, M_, E4))], 'ralrimiva',
               '( %s -> A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) )' % (P1, GK, w0, M_, E4))
    mr = D(w, P1, 'remulcld', [krP, D(w, P1, 'reexpcld', [l1(d['rr'], '%s e. RR' % RR_), kn0], '( %s ^ k ) e. RR' % RR_)], '%s e. RR' % M_)
    V6 = ('( ( C e. RR /\\ ( %s e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) ) /\\ ( ( %s e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) ) )'
          % (GK, w0, M_, GK, w0, M_, E4))
    v6a = D(w, P1, 'jca', [D(w, P1, 'jca', [crP, D(w, P1, 'jca', [gkC, linC], '( %s e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC )' % (GK, w0))], '( C e. RR /\\ ( %s e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) )' % (GK, w0)),
                           D(w, P1, 'jca', [D(w, P1, 'jca', [mr, cst(w, P1, '1rp', '1 e. RR+')], '( %s e. RR /\\ 1 e. RR+ )' % M_), ball],
                             '( ( %s e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) )' % (M_, GK, w0, M_, E4))], V6)
    TB = lambda t: '( ( ( 8 x. %s ) / ( log ` 2 ) ) x. ( 2 ^c -u ( %s / 4 ) ) )' % (M_, t)
    ALLT = 'A. t e. RR+ ( 1 <_ t -> ( abs ` ( %s - %s ) ) <_ %s )' % (VLk, LT(GK, 'C', 't'), TB('t'))
    vc = w.s([v6a, w.inst('z6vlcvg')], 'syl', '( %s -> ( ( t e. RR+ |-> %s ) ~~>r %s /\\ %s ) )' % (P1, LT(GK, 'C', 't'), VLk, ALLT))
    vlc = w.s([w.s([vc, w.inst('simpl')], 'syl', '( %s -> ( t e. RR+ |-> %s ) ~~>r %s )' % (P1, LT(GK, 'C', 't'), VLk)), w.inst('rlimcl')], 'syl', '( %s -> %s e. CC )' % (P1, VLk))
    allt = w.s([vc, w.inst('simpr')], 'syl', '( %s -> %s )' % (P1, ALLT))
    # rename the inner binder of VL and specialize t := T
    VLe = vl_e(GK, 'C')
    vte = vl_te(w, GK, 'C')
    body = lambda X, t: '( 1 <_ %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (t, X, LT(GK, 'C', t), TB(t))
    bi = w.s([w.s([w.s([w.s([vte], 'oveq1i', '( %s - %s ) = ( %s - %s )' % (VLk, LT(GK, 'C', 't'), VLe, LT(GK, 'C', 't')))], 'fveq2i', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (VLk, LT(GK, 'C', 't'), VLe, LT(GK, 'C', 't')))],
                   'breq1i', '( ( abs ` ( %s - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s )' % (VLk, LT(GK, 'C', 't'), TB('t'), VLe, LT(GK, 'C', 't'), TB('t')))], 'imbi2i',
             '( %s <-> %s )' % (body(VLk, 't'), body(VLe, 't')))
    allte = D(w, P1, 'sylib' if False else 'mpbid', [allt, cst(w, P1, 'ralbii', 'x') if False else w.s([w.s([bi], 'ralbii', '( %s <-> A. t e. RR+ %s )' % (ALLT, body(VLe, 't')))], 'a1i', '( %s -> ( %s <-> A. t e. RR+ %s ) )' % (P1, ALLT, body(VLe, 't')))],
                  'A. t e. RR+ %s' % body(VLe, 't'))
    Et = 't = T'
    et = w.s([], 'id', '( %s -> %s )' % (Et, Et))
    ltT = lt_sub(w, Et, et, GK, 'C', 't', 'T')
    tbT = D(w, Et, 'oveq2d', [D(w, Et, 'oveq2d', [D(w, Et, 'negeqd', [D(w, Et, 'oveq1d', [et], '( t / 4 ) = ( T / 4 )')], '-u ( t / 4 ) = -u ( T / 4 )')], '( 2 ^c -u ( t / 4 ) ) = ( 2 ^c -u ( T / 4 ) )')], '%s = %s' % (TB('t'), TB('T')))
    bsub = D(w, Et, 'imbi12d', [D(w, Et, 'breq2d', [et], '( 1 <_ t <-> 1 <_ T )'),
                                D(w, Et, 'breq12d', [D(w, Et, 'fveq2d', [D(w, Et, 'oveq2d', [ltT], '( %s - %s ) = ( %s - %s )' % (VLe, LT(GK, 'C', 't'), VLe, LTk))], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (VLe, LT(GK, 'C', 't'), VLe, LTk)), tbT],
                                  '( ( abs ` ( %s - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s )' % (VLe, LT(GK, 'C', 't'), TB('t'), VLe, LTk, TB('T')))], '( %s <-> %s )' % (body(VLe, 't'), body(VLe, 'T')))
    spT = w.s([l1(trp, 'T e. RR+'), allte, w.s([bsub], 'rspcv', '( T e. RR+ -> ( A. t e. RR+ %s -> %s ) )' % (body(VLe, 't'), body(VLe, 'T')))], 'sylc', '( %s -> %s )' % (P1, body(VLe, 'T')))
    bT0 = D(w, P1, 'mpd', [l1(t1, '1 <_ T'), spT], '( abs ` ( %s - %s ) ) <_ %s' % (VLe, LTk, TB('T')))
    vtep = w.s([vte], 'a1i', '( %s -> %s = %s )' % (P1, VLk, VLe))
    bT = D(w, P1, 'eqbrtrd', [D(w, P1, 'fveq2d', [D(w, P1, 'oveq1d', [vtep], '( %s - %s ) = ( %s - %s )' % (VLk, LTk, VLe, LTk))], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (VLk, LTk, VLe, LTk)), bT0],
           '( abs ` ( %s - %s ) ) <_ %s' % (VLk, LTk, TB('T')))
    # rewrite the bound as B R ^ k
    BB = '( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( 2 ^c -u ( T / 4 ) ) )'
    kc_ = D(w, P1, 'recnd', [krP], 'K e. CC'); rkc = D(w, P1, 'recnd', [D(w, P1, 'reexpcld', [l1(d['rr'], '%s e. RR' % RR_), kn0], '( %s ^ k ) e. RR' % RR_)], '( %s ^ k ) e. CC' % RR_)
    l2rp = cst(w, P1, 'rplogcl' if False else 'log2rp' if False else 'x', 'x') if False else w.s([cst(w, P1, '2re', '2 e. RR'), cst(w, P1, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % P1)
    l2c = D(w, P1, 'rpcnd', [l2rp], '( log ` 2 ) e. CC'); l2n = D(w, P1, 'rpne0d', [l2rp], '( log ` 2 ) =/= 0')
    c8 = cst(w, P1, '8cn', '8 e. CC')
    trT = D(w, P1, 'rpred', [l1(trp, 'T e. RR+')], 'T e. RR')
    p4c = D(w, P1, 'rpcnd', [D(w, P1, 'rpcxpcld', [cst(w, P1, '2rp', '2 e. RR+'), D(w, P1, 'renegcld', [D(w, P1, 'rerpdivcld', [trT, cst(w, P1, '4rp', '4 e. RR+')], '( T / 4 ) e. RR')], '-u ( T / 4 ) e. RR')],
                                 '( 2 ^c -u ( T / 4 ) ) e. RR+')], '( 2 ^c -u ( T / 4 ) ) e. CC')
    r1_ = D(w, P1, 'oveq1d', [D(w, P1, 'eqcomd', [D(w, P1, 'mulassd', [c8, kc_, rkc], '( ( 8 x. K ) x. ( %s ^ k ) ) = ( 8 x. %s )' % (RR_, M_))], '( 8 x. %s ) = ( ( 8 x. K ) x. ( %s ^ k ) )' % (M_, RR_))],
            '( ( 8 x. %s ) / ( log ` 2 ) ) = ( ( ( 8 x. K ) x. ( %s ^ k ) ) / ( log ` 2 ) )' % (M_, RR_))
    c8k = D(w, P1, 'mulcld', [c8, kc_], '( 8 x. K ) e. CC')
    r2_ = D(w, P1, 'div23d', [c8k, rkc, l2c, l2n], '( ( ( 8 x. K ) x. ( %s ^ k ) ) / ( log ` 2 ) ) = ( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( %s ^ k ) )' % (RR_, RR_))
    q_ = D(w, P1, 'divcld', [c8k, l2c, l2n], '( ( 8 x. K ) / ( log ` 2 ) ) e. CC')
    r3_ = D(w, P1, 'mul32d', [q_, rkc, p4c], '( ( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( %s ^ k ) ) x. ( 2 ^c -u ( T / 4 ) ) ) = ( %s x. ( %s ^ k ) )' % (RR_, BB, RR_))
    tbe = chain_eq(w, P1, TB('T'), [(D(w, P1, 'oveq1d', [D(w, P1, 'eqtrd', [r1_, r2_], '( ( 8 x. %s ) / ( log ` 2 ) ) = ( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( %s ^ k ) )' % (M_, RR_))],
                                                  '%s = ( ( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( %s ^ k ) ) x. ( 2 ^c -u ( T / 4 ) ) )' % (TB('T'), RR_)), '( ( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( %s ^ k ) ) x. ( 2 ^c -u ( T / 4 ) ) )' % RR_),
                                    (r3_, '( %s x. ( %s ^ k ) )' % (BB, RR_))])
    bk = D(w, P1, 'breqtrd', [bT, tbe], '( abs ` ( %s - %s ) ) <_ ( %s x. ( %s ^ k ) )' % (VLk, LTk, BB, RR_))
    # the difference series
    DF = '( j e. NN |-> ( %s - %s ) )' % (VLj, LTj)
    def jk_sub(bodyj, bodyk, pieces):
        return pieces
    Ejk = 'j = k'
    ejk = w.s([], 'id', '( %s -> %s )' % (Ejk, Ejk))
    gkj = w.s([D(w, Ejk, 'oveq2d', [D(w, Ejk, 'fveq2d', [D(w, Ejk, 'oveq1d', [D(w, Ejk, 'oveq1d', [ejk], '( j x. A ) = ( k x. A )')], '( ( j x. A ) x. y ) = ( ( k x. A ) x. y )')],
                                                      '( exp ` ( ( j x. A ) x. y ) ) = ( exp ` ( ( k x. A ) x. y ) )')], '( ( G ` y ) x. ( exp ` ( ( j x. A ) x. y ) ) ) = ( ( G ` y ) x. ( exp ` ( ( k x. A ) x. y ) ) )')],
              'mpteq2dv', '( %s -> %s = %s )' % (Ejk, GKj, GK))
    ltjk = D(w, Ejk, 'oveq1d', [gkj], '%s = %s' % (LTj, LTk))
    vljk = D(w, Ejk, 'fveq2d', [w.s([w.s([D(w, '( %s /\\ t e. RR+ )' % Ejk, 'oveq1d', [w.s([gkj], 'adantr', '( ( %s /\\ t e. RR+ ) -> %s = %s )' % (Ejk, GKj, GK))], '%s = %s' % (LT(GKj, 'C', 't'), LT(GK, 'C', 't')))], 'mpteq2dva',
                                     '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (Ejk, LT(GKj, 'C', 't'), LT(GK, 'C', 't')))], 'idi', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (Ejk, LT(GKj, 'C', 't'), LT(GK, 'C', 't')))],
           '%s = %s' % (VLj, VLk))
    dsub = D(w, Ejk, 'oveq12d', [vljk, ltjk], '( %s - %s ) = ( %s - %s )' % (VLj, LTj, VLk, LTk))
    dfv = w.s([kN, w.s([dsub, w.s([], 'eqid', '%s = %s' % (DF, DF)), w.s([], 'ovex', '( %s - %s ) e. _V' % (VLk, LTk))], 'fvmpt', '( k e. NN -> ( %s ` k ) = ( %s - %s ) )' % (DF, VLk, LTk))], 'syl',
              '( %s -> ( %s ` k ) = ( %s - %s ) )' % (P1, DF, VLk, LTk))
    GKC = lambda A_: None
    ltkc = w.s([w.s([w.s([w.s([cpcl(w, P1, 'C', '-u T', crP, D(w, P1, 'renegcld', [trT], '-u T e. RR')), cpcl(w, P1, 'C', 'T', crP, trT)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (P1, CP('C', '-u T'), CP('C', 'T')))], 'idi',
                          '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (P1, CP('C', '-u T'), CP('C', 'T'))), D(w, P1, 'jca', [gkC, cst(w, P1, 'ssid', '( %s cseg %s ) C_ CC' % (CP('C', '-u T'), CP('C', 'T'))) if False else
                                                                                                                         w.s([w.s([cpcl(w, P1, 'C', '-u T', crP, D(w, P1, 'renegcld', [trT], '-u T e. RR')), cpcl(w, P1, 'C', 'T', crP, trT)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (P1, CP('C', '-u T'), CP('C', 'T'))), w.inst('csegcl')], 'syl',
                                                                                                                             '( %s -> ( %s cseg %s ) C_ CC )' % (P1, CP('C', '-u T'), CP('C', 'T')))],
                                                                                                           '( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC )' % (GK, CP('C', '-u T'), CP('C', 'T')))], 'jca',
                    '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (P1, CP('C', '-u T'), CP('C', 'T'), GK, CP('C', '-u T'), CP('C', 'T'))), w.inst('lintcl')], 'syl',
               '( %s -> %s e. CC )' % (P1, LTk))
    dkc = D(w, P1, 'subcld', [vlc, ltkc], '( %s - %s ) e. CC' % (VLk, LTk))
    BBr = D(w, ph, 'remulcld', [D(w, ph, 'redivcld' if False else 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), d['kr']], '( 8 x. K ) e. RR'),
                                                                               w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)], '( ( 8 x. K ) / ( log ` 2 ) ) e. RR'),
                                 D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'rerpdivcld', [D(w, ph, 'rpred', [trp], 'T e. RR'), cst(w, ph, '4rp', '4 e. RR+')], '( T / 4 ) e. RR')], '-u ( T / 4 ) e. RR')],
                                                     '( 2 ^c -u ( T / 4 ) ) e. RR+')], '( 2 ^c -u ( T / 4 ) ) e. RR')], '%s e. RR' % BB)
    ms = w.s([BBr, d['rr'], d['r0'], d['r1'], D(w, P1, 'eqeltrd', [dfv, dkc], '( %s ` k ) e. CC' % DF), D(w, P1, 'eqbrtrd', [D(w, P1, 'fveq2d', [dfv], '( abs ` ( %s ` k ) ) = ( abs ` ( %s - %s ) )' % (DF, VLk, LTk)), bk],
                                                                                                              '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ^ k ) )' % (DF, BB, RR_))], 'zl3mser',
             '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) ) ) )' % (ph, DF, DF, BB, RR_, RR_))
    dfdm = w.s([ms, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, DF))
    dfb = w.s([ms, w.inst('simpr')], 'syl', '( %s -> ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) ) )' % (ph, DF, BB, RR_, RR_))
    # the segment series (zl3eseg), in the j-form
    es = w.s([e0, trp, w.inst('zl3eseg')], 'syl2anc', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) ~~> %s )' % (ph, LTk, LT('P', 'C', 'T')))
    LTF = '( j e. NN |-> %s )' % LTj
    cbl = w.s([w.s([], 'eqcom', 'x') if False else D(w, 'k = j', 'oveq1d', [w.s([w.s([w.s([], 'eqcom', '( k = j <-> j = k )')], 'biimpi', '( k = j -> j = k )'), gkj], 'syl', '( k = j -> %s = %s )' % (GKj, GK))],
                                                             '%s = %s' % (LTj, LTk)) if False else None], 'x', 'x') if False else None
    kj = w.s([w.s([], 'equcomi', '( k = j -> j = k )'), ltjk], 'syl', '( k = j -> %s = %s )' % (LTj, LTk))
    cb = w.s([w.s([kj], 'eqcomd', '( k = j -> %s = %s )' % (LTk, LTj))], 'cbvmptv', '( k e. NN |-> %s ) = %s' % (LTk, LTF))
    es2 = D(w, ph, 'breqtrd' if False else 'mpbid', [es, D(w, ph, 'breq1d', [D(w, ph, 'seqeq3d', [w.s([cb], 'a1i', '( %s -> ( k e. NN |-> %s ) = %s )' % (ph, LTk, LTF))],
                                                                                       'seq 1 ( + , ( k e. NN |-> %s ) ) = seq 1 ( + , %s )' % (LTk, LTF))],
                                                                     '( seq 1 ( + , ( k e. NN |-> %s ) ) ~~> %s <-> seq 1 ( + , %s ) ~~> %s )' % (LTk, LT('P', 'C', 'T'), LTF, LT('P', 'C', 'T')))],
              'seq 1 ( + , %s ) ~~> %s' % (LTF, LT('P', 'C', 'T')))
    ltfv = w.s([kN, w.s([ltjk, w.s([], 'eqid', '%s = %s' % (LTF, LTF)), w.s([], 'ovex', '%s e. _V' % LTk)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (LTF, LTk))], 'syl', '( %s -> ( %s ` k ) = %s )' % (P1, LTF, LTk))
    rel = w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> %s -> seq 1 ( + , %s ) e. dom ~~> )' % (LTF, LT('P', 'C', 'T'), LTF))
    ltdm = w.s([es2, rel], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, LTF))
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); one_z = cst(w, ph, '1z', '1 e. ZZ')
    sadd = w.s([nnu, one_z, ltfv, ltkc, dfv, dkc, ltdm, dfdm], 'isumadd', '( %s -> sum_ k e. NN ( %s + ( %s - %s ) ) = ( sum_ k e. NN %s + sum_ k e. NN ( %s - %s ) ) )' % (ph, LTk, VLk, LTk, LTk, VLk, LTk))
    pc_ = D(w, P1, 'pncan3d', [ltkc, vlc], '( %s + ( %s - %s ) ) = %s' % (LTk, VLk, LTk, VLk))
    s_vl = w.s([pc_], 'sumeq2dv', '( %s -> sum_ k e. NN ( %s + ( %s - %s ) ) = sum_ k e. NN %s )' % (ph, LTk, VLk, LTk, VLk))
    slt = w.s([nnu, one_z, ltfv, ltkc, es2], 'isumclim', '( %s -> sum_ k e. NN %s = %s )' % (ph, LTk, LT('P', 'C', 'T')))
    sdf = w.s([D(w, P1, 'eqcomd', [dfv], '( %s - %s ) = ( %s ` k )' % (VLk, LTk, DF))], 'sumeq2dv', '( %s -> sum_ k e. NN ( %s - %s ) = sum_ k e. NN ( %s ` k ) )' % (ph, VLk, LTk, DF))
    SVL = 'sum_ k e. NN %s' % VLk; SD = 'sum_ k e. NN ( %s ` k )' % DF; LP = LT('P', 'C', 'T')
    sv = D(w, ph, 'eqtr3d', [s_vl, D(w, ph, 'oveq12d', [slt, sdf], '( sum_ k e. NN %s + sum_ k e. NN ( %s - %s ) ) = ( %s + %s )' % (LTk, VLk, LTk, LP, SD)) if False else
                             D(w, ph, 'eqtrd', [sadd, D(w, ph, 'oveq12d', [slt, sdf], '( sum_ k e. NN %s + sum_ k e. NN ( %s - %s ) ) = ( %s + %s )' % (LTk, VLk, LTk, LP, SD))],
                               'sum_ k e. NN ( %s + ( %s - %s ) ) = ( %s + %s )' % (LTk, VLk, LTk, LP, SD))], '%s = ( %s + %s )' % (SVL, LP, SD))
    lpc = w.s([w.s([], 'climcl', 'x')], 'x', 'x') if False else w.s([es2, w.inst('climcl')], 'syl', '( %s -> %s e. CC )' % (ph, LP))
    sdc = w.s([nnu, one_z, D(w, P1, 'eqidd', [], '( %s ` k ) = ( %s ` k )' % (DF, DF)), D(w, P1, 'eqeltrd', [dfv, dkc], '( %s ` k ) e. CC' % DF), dfdm], 'isumcl', '( %s -> %s e. CC )' % (ph, SD))
    df1 = D(w, ph, 'oveq2d', [sv], '( %s - %s ) = ( %s - ( %s + %s ) )' % (LP, SVL, LP, LP, SD))
    df2 = D(w, ph, 'eqtrd', [D(w, ph, 'subsub4d' if False else 'sub2d' if False else 'eqcomd', [D(w, ph, 'negsubd' if False else 'eqtr3d' if False else 'eqcomd', [D(w, ph, 'negsubd', [lpc, D(w, ph, 'addcld', [lpc, sdc], '( %s + %s ) e. CC' % (LP, SD))], '( %s + -u ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD))],
                                                                                                                                                              '( %s - ( %s + %s ) ) = ( %s + -u ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD))],
                                                                                                     '( %s + -u ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD))], '( %s + -u ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD)) if False else None
    df2 = D(w, ph, 'eqtrd', [D(w, ph, 'subsub4d' if False else 'pncan2d' if False else 'eqcomd', [D(w, ph, 'eqtrd', [D(w, ph, 'negsubdi2d' if False else 'subsubd' if False else 'mvlladdd' if False else 'nncand' if False else 'eqidd', [], '( %s - ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD)),
                                                                                                                                         D(w, ph, 'eqidd', [], '( %s - ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD))], '( %s - ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD))],
                                                                                           '( %s - ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD)), D(w, ph, 'eqidd', [], '( %s - ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD))],
            '( %s - ( %s + %s ) ) = ( %s - ( %s + %s ) )' % (LP, LP, SD, LP, LP, SD)) if False else None
    # ( LP - ( LP + SD ) ) = -u SD
    df3 = D(w, ph, 'eqtrd', [D(w, ph, 'subsub4d' if False else 'eqcomd', [D(w, ph, 'pnncand' if False else 'eqtrd', [D(w, ph, 'negeqd', [D(w, ph, 'pncan2d', [lpc, sdc], '( ( %s + %s ) - %s ) = %s' % (LP, SD, LP, SD))], '-u ( ( %s + %s ) - %s ) = -u %s' % (LP, SD, LP, SD)),
                                                                                                    D(w, ph, 'eqidd', [], '-u %s = -u %s' % (SD, SD))], '-u ( ( %s + %s ) - %s ) = -u %s' % (LP, SD, LP, SD))], '-u %s = -u ( ( %s + %s ) - %s )' % (SD, LP, SD, LP)),
                              D(w, ph, 'negsubdi2d', [D(w, ph, 'addcld', [lpc, sdc], '( %s + %s ) e. CC' % (LP, SD)), lpc], '-u ( ( %s + %s ) - %s ) = ( %s - ( %s + %s ) )' % (LP, SD, LP, LP, LP, SD))],
            '-u %s = ( %s - ( %s + %s ) )' % (SD, LP, LP, SD))
    dd = D(w, ph, 'eqtr4d', [df1, df3], '( %s - %s ) = -u %s' % (LP, SVL, SD))
    ab1 = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [dd], '( abs ` ( %s - %s ) ) = ( abs ` -u %s )' % (LP, SVL, SD)), D(w, ph, 'absnegd', [sdc], '( abs ` -u %s ) = ( abs ` %s )' % (SD, SD))],
            '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (LP, SVL, SD))
    # ( ( BB x. R ) / ( 1 - R ) ) = EBND
    rc_ = D(w, ph, 'recnd', [d['rr']], '%s e. CC' % RR_)
    omr = D(w, ph, 'subcld', [cst(w, ph, 'ax-1cn', '1 e. CC'), rc_], '( 1 - %s ) e. CC' % RR_)
    omn = D(w, ph, 'gt0ne0d', [D(w, ph, 'mpbid', [d['r1'], D(w, ph, 'posdifd', [d['rr'], cst(w, ph, '1re', '1 e. RR')], '( %s < 1 <-> 0 < ( 1 - %s ) )' % (RR_, RR_))], '0 < ( 1 - %s )' % RR_)], '( 1 - %s ) =/= 0' % RR_)
    bbc = D(w, ph, 'recnd', [BBr], '%s e. CC' % BB)
    q8 = '( ( 8 x. K ) / ( log ` 2 ) )'; p4 = '( 2 ^c -u ( T / 4 ) )'
    q8c = D(w, ph, 'recnd', [D(w, ph, 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), d['kr']], '( 8 x. K ) e. RR'), w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)],
                                  '%s e. RR' % q8)], '%s e. CC' % q8)
    p4c_ = D(w, ph, 'rpcnd', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'rerpdivcld', [D(w, ph, 'rpred', [trp], 'T e. RR'), cst(w, ph, '4rp', '4 e. RR+')], '( T / 4 ) e. RR')], '-u ( T / 4 ) e. RR')],
                                   '%s e. RR+' % p4)], '%s e. CC' % p4)
    g1 = D(w, ph, 'divassd', [bbc, rc_, omr, omn], '( ( %s x. %s ) / ( 1 - %s ) ) = ( %s x. ( %s / ( 1 - %s ) ) )' % (BB, RR_, RR_, BB, RR_, RR_))
    rq = D(w, ph, 'divcld', [rc_, omr, omn], '( %s / ( 1 - %s ) ) e. CC' % (RR_, RR_))
    g2 = D(w, ph, 'mulassd', [q8c, p4c_, rq], '( %s x. ( %s / ( 1 - %s ) ) ) = %s' % (BB, RR_, RR_, EBND('T')))
    ge = D(w, ph, 'eqtrd', [g1, g2], '( ( %s x. %s ) / ( 1 - %s ) ) = %s' % (BB, RR_, RR_, EBND('T')))
    bound = D(w, ph, 'breqtrd', [D(w, ph, 'eqbrtrd', [ab1, dfb], '( abs ` ( %s - %s ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) )' % (LP, SVL, BB, RR_, RR_)), ge], '( abs ` ( %s - %s ) ) <_ %s' % (LP, SVL, EBND('T')))
    # convergence of the VL series: seradd + climadd
    VLF = '( j e. NN |-> %s )' % VLj
    vlfv = w.s([kN, w.s([vljk, w.s([], 'eqid', '%s = %s' % (VLF, VLF)), w.s([], 'fvex', '%s e. _V' % VLk)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (VLF, VLk))], 'syl', '( %s -> ( %s ` k ) = %s )' % (P1, VLF, VLk))
    P4 = '( %s /\\ n e. ( ZZ>= ` 1 ) )' % ph
    nU = w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` 1 ) )' % P4)
    P5 = '( %s /\\ k e. ( 1 ... n ) )' % P4
    kN5 = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... n ) )' % P5), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % P5)
    toP1 = lambda st, f: w.s([w.s([], 'simpll', '( %s -> %s )' % (P5, ph)), kN5, st], 'syl2anc', '( %s -> %s )' % (P5, f))
    ltfc = D(w, P1, 'eqeltrd', [ltfv, ltkc], '( %s ` k ) e. CC' % LTF)
    dfc = D(w, P1, 'eqeltrd', [dfv, dkc], '( %s ` k ) e. CC' % DF)
    vsum = D(w, P1, 'eqtrd', [vlfv, D(w, P1, 'eqtr4d', [D(w, P1, 'eqcomd', [pc_], '%s = ( %s + ( %s - %s ) )' % (VLk, LTk, VLk, LTk)),
                                                        D(w, P1, 'oveq12d', [ltfv, dfv], '( ( %s ` k ) + ( %s ` k ) ) = ( %s + ( %s - %s ) )' % (LTF, DF, LTk, VLk, LTk))], '%s = ( ( %s ` k ) + ( %s ` k ) )' % (VLk, LTF, DF))],
               '( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) )' % (VLF, LTF, DF))
    sr = w.s([nU, toP1(ltfc, '( %s ` k ) e. CC' % LTF), toP1(dfc, '( %s ` k ) e. CC' % DF), toP1(vsum, '( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) )' % (VLF, LTF, DF))], 'seradd',
             '( %s -> ( seq 1 ( + , %s ) ` n ) = ( ( seq 1 ( + , %s ) ` n ) + ( seq 1 ( + , %s ) ` n ) ) )' % (P4, VLF, LTF, DF))
    def fcU(F, fcP1):
        P7 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % ph
        kN7 = D(w, P7, 'eleqtrrd', [w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % P7), w.s([nnu], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % P7)], 'k e. NN')
        return w.s([w.s([], 'simpl', '( %s -> %s )' % (P7, ph)), kN7, fcP1], 'syl2anc', '( %s -> ( %s ` k ) e. CC )' % (P7, F))
    zu = w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )')
    serLT = w.s([zu, one_z, fcU(LTF, ltfc)], 'serf', '( %s -> seq 1 ( + , %s ) : ( ZZ>= ` 1 ) --> CC )' % (ph, LTF))
    serDF = w.s([zu, one_z, fcU(DF, dfc)], 'serf', '( %s -> seq 1 ( + , %s ) : ( ZZ>= ` 1 ) --> CC )' % (ph, DF))
    cLT = D(w, P4, 'ffvelcdmd', [w.s([serLT], 'adantr', '( %s -> seq 1 ( + , %s ) : ( ZZ>= ` 1 ) --> CC )' % (P4, LTF)), nU], '( seq 1 ( + , %s ) ` n ) e. CC' % LTF)
    cDF = D(w, P4, 'ffvelcdmd', [w.s([serDF], 'adantr', '( %s -> seq 1 ( + , %s ) : ( ZZ>= ` 1 ) --> CC )' % (P4, DF)), nU], '( seq 1 ( + , %s ) ` n ) e. CC' % DF)
    sdl = w.s([nnu, one_z, D(w, P1, 'eqidd', [], '( %s ` k ) = ( %s ` k )' % (DF, DF)), dfc, dfdm], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (ph, DF, SD))
    cadd = w.s([zu, one_z, es2, w.s([w.s([], 'seqex', 'seq 1 ( + , %s ) e. _V' % VLF)], 'a1i', '( %s -> seq 1 ( + , %s ) e. _V )' % (ph, VLF)), sdl, cLT, cDF, sr], 'climadd',
               '( %s -> seq 1 ( + , %s ) ~~> ( %s + %s ) )' % (ph, VLF, LP, SD))
    rel2 = w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> ( %s + %s ) -> seq 1 ( + , %s ) e. dom ~~> )' % (VLF, LP, SD, VLF))
    vdm = w.s([cadd, rel2], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, VLF))
    kjv = w.s([w.s([], 'equcomi', '( k = j -> j = k )'), vljk], 'syl', '( k = j -> %s = %s )' % (VLj, VLk))
    cbv = w.s([w.s([kjv], 'eqcomd', '( k = j -> %s = %s )' % (VLk, VLj))], 'cbvmptv', '( k e. NN |-> %s ) = %s' % (VLk, VLF))
    vdm2 = D(w, ph, 'eleqtrrd' if False else 'mpbird', [vdm, D(w, ph, 'eleq1d', [D(w, ph, 'seqeq3d', [w.s([cbv], 'a1i', '( %s -> ( k e. NN |-> %s ) = %s )' % (ph, VLk, VLF))],
                                                                                     'seq 1 ( + , ( k e. NN |-> %s ) ) = seq 1 ( + , %s )' % (VLk, VLF))],
                                                                   '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (VLk, VLF))],
             'seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~>' % VLk)
    svc = D(w, ph, 'eqeltrd', [sv, D(w, ph, 'addcld', [lpc, sdc], '( %s + %s ) e. CC' % (LP, SD))], '%s e. CC' % SVL)
    w.qed([D(w, ph, 'jca', [vdm2, svc], '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ %s e. CC )' % (VLk, SVL)), bound], 'jca', S['zl3edgb'])
    go(w, only)


# ---------------------------------------------------------------- zl3edge
if __name__ == '__main__' and (not only or 'zl3edge' in only):
    w = W('zl3edge', 'The long side ` Re w = C ` of ` R_N `: uniform version of ~ zl3edgb in the height.')
    ph = EDGA
    GK = GKE('G', 'A'); VLk = VL(GK, 'C'); SVL = 'sum_ k e. NN %s' % VLk
    CONV = '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ sum_ k e. NN %s e. CC )' % (VLk, VLk)
    B = lambda T: '( abs ` ( %s - %s ) ) <_ %s' % (LT('P', 'C', T), SVL, EBND(T))
    o = w.s([w.s([cst(w, ph, '1rp', '1 e. RR+'), D(w, ph, 'leidd', [cst(w, ph, '1re', '1 e. RR')], '1 <_ 1')], 'jca', '( %s -> ( 1 e. RR+ /\\ 1 <_ 1 ) )' % ph)], 'idi', '( %s -> ( 1 e. RR+ /\\ 1 <_ 1 ) )' % ph)
    e1 = w.s([w.s([], 'id', '( %s -> %s )' % (ph, ph)), o, w.inst('zl3edgb')], 'syl2anc', '( %s -> ( %s /\\ %s ) )' % (ph, CONV, B('1')))
    cv = w.s([e1, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, CONV))
    A1 = '( ( %s /\\ s e. RR+ ) /\\ 1 <_ s )' % ph
    es = w.s([w.s([], 'simpll', '( %s -> %s )' % (A1, ph)), D(w, A1, 'jca', [w.s([], 'simplr', '( %s -> s e. RR+ )' % A1), w.s([], 'simpr', '( %s -> 1 <_ s )' % A1)], '( s e. RR+ /\\ 1 <_ s )'), w.inst('zl3edgb')],
             'syl2anc', '( %s -> ( %s /\\ %s ) )' % (A1, CONV, B('s')))
    bs = w.s([es, w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, B('s')))
    al = w.s([w.s([bs], 'ex', '( ( %s /\\ s e. RR+ ) -> ( 1 <_ s -> %s ) )' % (ph, B('s')))], 'ralrimiva', '( %s -> A. s e. RR+ ( 1 <_ s -> %s ) )' % (ph, B('s')))
    w.qed([cv, al], 'jca', S['zl3edge'])
    go(w, only)


# ---------------------------------------------------------------- zl3shv
def pow4(w, A_, X, xr, x1):
    """( A_ -> ( 2 ^c -u X ) <_ ( 2 ^c -u ( X / 4 ) ) ) from xr: X e. RR, x1: 1 <_ X"""
    xrp = D(w, A_, 'elrpd', [xr, D(w, A_, 'ltletrd', [cst(w, A_, '0re', '0 e. RR'), cst(w, A_, '1re', '1 e. RR'), xr, cst(w, A_, '0lt1', '0 < 1'), x1], '0 < %s' % X)], '%s e. RR+' % X)
    q4 = D(w, A_, 'mpd', [D(w, A_, 'leidd', [xr], '%s <_ %s' % (X, X)),
                          w.s([xr, xrp, D(w, A_, 'jca', [cst(w, A_, '4rp', '4 e. RR+'), D(w, A_, 'ltled', [cst(w, A_, '1re', '1 e. RR'), cst(w, A_, '4re', '4 e. RR'), cst(w, A_, '1lt4', '1 < 4')], '1 <_ 4')], '( 4 e. RR+ /\\ 1 <_ 4 )'),
                               w.inst('ledivge1le')], 'syl3anc', '( %s -> ( %s <_ %s -> ( %s / 4 ) <_ %s ) )' % (A_, X, X, X, X))], '( %s / 4 ) <_ %s' % (X, X))
    x4 = D(w, A_, 'rerpdivcld', [xr, cst(w, A_, '4rp', '4 e. RR+')], '( %s / 4 ) e. RR' % X)
    q5 = D(w, A_, 'mpbid', [q4, D(w, A_, 'lenegd', [x4, xr], '( ( %s / 4 ) <_ %s <-> -u %s <_ -u ( %s / 4 ) )' % (X, X, X, X))], '-u %s <_ -u ( %s / 4 )' % (X, X))
    return D(w, A_, 'mpbid', [q5, w.s([w.s([cst(w, A_, '2re', '2 e. RR'), cst(w, A_, '1lt2', '1 < 2')], 'jca', '( %s -> ( 2 e. RR /\\ 1 < 2 ) )' % A_),
                                       D(w, A_, 'jca', [D(w, A_, 'renegcld', [xr], '-u %s e. RR' % X), D(w, A_, 'renegcld', [x4], '-u ( %s / 4 ) e. RR' % X)], '( -u %s e. RR /\\ -u ( %s / 4 ) e. RR )' % (X, X)),
                                       w.inst('cxple')], 'syl2anc', '( %s -> ( -u %s <_ -u ( %s / 4 ) <-> ( 2 ^c -u %s ) <_ ( 2 ^c -u ( %s / 4 ) ) ) )' % (A_, X, X, X, X))],
             '( 2 ^c -u %s ) <_ ( 2 ^c -u ( %s / 4 ) )' % (X, X))


SHH = 'A. b e. CC ( ( A <_ ( Re ` b ) /\\ ( Re ` b ) <_ B ) -> ( abs ` ( G ` b ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) )'


def shh_at(w, A_, shh_A, Z, zc):
    """( A_ -> ( ( A <_ Re Z /\\ Re Z <_ B ) -> | G Z | <_ M 2 ^ -| Im Z | ) )"""
    body = lambda c: '( ( A <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ B ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) )' % (c, c, c, c)
    E = 'b = %s' % Z
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    re_ = D(w, E, 'fveq2d', [e], '( Re ` b ) = ( Re ` %s )' % Z)
    l = D(w, E, 'anbi12d', [D(w, E, 'breq2d', [re_], '( A <_ ( Re ` b ) <-> A <_ ( Re ` %s ) )' % Z), D(w, E, 'breq1d', [re_], '( ( Re ` b ) <_ B <-> ( Re ` %s ) <_ B )' % Z)],
          '( ( A <_ ( Re ` b ) /\\ ( Re ` b ) <_ B ) <-> ( A <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ B ) )' % (Z, Z))
    r = D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( G ` b ) = ( G ` %s )' % Z)], '( abs ` ( G ` b ) ) = ( abs ` ( G ` %s ) )' % Z),
                            D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Im ` b ) = ( Im ` %s )' % Z)], '( abs ` ( Im ` b ) ) = ( abs ` ( Im ` %s ) )' % Z)],
                                                                        '-u ( abs ` ( Im ` b ) ) = -u ( abs ` ( Im ` %s ) )' % Z)], '( 2 ^c -u ( abs ` ( Im ` b ) ) ) = ( 2 ^c -u ( abs ` ( Im ` %s ) ) )' % Z)],
                              '( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) = ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % Z)],
          '( ( abs ` ( G ` b ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) <-> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) )' % (Z, Z))
    eq = D(w, E, 'imbi12d', [l, r], '( %s <-> %s )' % (body('b'), body(Z)))
    return w.s([zc, shh_A, w.s([eq], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (Z, SHH, body(Z)))], 'sylc', '( %s -> %s )' % (A_, body(Z)))


if __name__ == '__main__' and (not only or 'zl3shv' in only):
    w = W('zl3shv', 'Shift of a vertical-line integral across a strip on which an entire function decays like ` 2 ^ -| Im | ` (no poles: ~ z6shift with ` K = 0 `).')
    ph, concl = ante_of(S['zl3shv'])
    L0 = '( ( A e. RR /\\ B e. RR ) /\\ A < B )'
    R0 = '( ( G e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D G ) ) /\\ ( M e. RR /\\ %s ) )' % SHH
    l0 = w.s([], 'simpl', '( %s -> %s )' % (ph, L0)); r0 = w.s([], 'simpr', '( %s -> %s )' % (ph, R0))
    ab = w.s([l0, w.inst('simpl')], 'syl', '( %s -> ( A e. RR /\\ B e. RR ) )' % ph)
    ar = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. RR )' % ph); br = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. RR )' % ph)
    alb = w.s([l0, w.inst('simpr')], 'syl', '( %s -> A < B )' % ph)
    gh = w.s([r0, w.inst('simpl')], 'syl', '( %s -> ( G e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D G ) ) )' % ph)
    gcn = w.s([gh, w.inst('simpl')], 'syl', '( %s -> G e. ( CC -cn-> CC ) )' % ph); gdv = w.s([gh, w.inst('simpr')], 'syl', '( %s -> CC C_ dom ( CC _D G ) )' % ph)
    mh = w.s([r0, w.inst('simpr')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (ph, SHH))
    mr = w.s([mh, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % ph); shh = w.s([mh, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, SHH))
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % ph)
    # M >_ 0 from the point A
    acA = D(w, ph, 'recnd', [ar], 'A e. CC')
    b0 = shh_at(w, ph, shh, 'A', acA)
    reA = w.s([ar, w.inst('rere')], 'syl', '( %s -> ( Re ` A ) = A )' % ph)
    aa = D(w, ph, 'jca', [D(w, ph, 'eqbrtrrd' if False else 'breqtrrd', [D(w, ph, 'leidd', [ar], 'A <_ A'), reA], 'A <_ ( Re ` A )'),
                          D(w, ph, 'eqbrtrd', [reA, D(w, ph, 'ltled', [ar, br, alb], 'A <_ B')], '( Re ` A ) <_ B')], '( A <_ ( Re ` A ) /\\ ( Re ` A ) <_ B )')
    ga = D(w, ph, 'mpd', [aa, b0], '( abs ` ( G ` A ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` A ) ) ) )')
    pA = D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'abscld', [D(w, ph, 'recnd', [D(w, ph, 'imcld', [acA], '( Im ` A ) e. RR')], '( Im ` A ) e. CC')], '( abs ` ( Im ` A ) ) e. RR')], '-u ( abs ` ( Im ` A ) ) e. RR')],
           '( 2 ^c -u ( abs ` ( Im ` A ) ) ) e. RR+')
    m0 = D(w, ph, 'prodge0ld', [mr, pA, D(w, ph, 'letrd', [cst(w, ph, '0re', '0 e. RR'), D(w, ph, 'abscld', [D(w, ph, 'ffvelcdmd', [gf, acA], '( G ` A ) e. CC')], '( abs ` ( G ` A ) ) e. RR'),
                                                            D(w, ph, 'remulcld', [mr, D(w, ph, 'rpred', [pA], '( 2 ^c -u ( abs ` ( Im ` A ) ) ) e. RR')], '( M x. ( 2 ^c -u ( abs ` ( Im ` A ) ) ) ) e. RR'),
                                                            D(w, ph, 'absge0d', [D(w, ph, 'ffvelcdmd', [gf, acA], '( G ` A ) e. CC')], '0 <_ ( abs ` ( G ` A ) )'), ga], '0 <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` A ) ) ) )')],
           '0 <_ M')
    # generic: strip bound with 1 <_ | Im z |
    def sb(A_, z, zc, lo, hi, i1, lift):
        bz = shh_at(w, A_, lift(shh, SHH), z, zc)
        g1 = D(w, A_, 'mpd', [D(w, A_, 'jca', [lo, hi], '( A <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ B )' % (z, z)), bz], '( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % (z, z))
        X = '( abs ` ( Im ` %s ) )' % z
        xr = D(w, A_, 'abscld', [D(w, A_, 'recnd', [D(w, A_, 'imcld', [zc], '( Im ` %s ) e. RR' % z)], '( Im ` %s ) e. CC' % z)], '%s e. RR' % X)
        p4 = pow4(w, A_, X, xr, i1)
        e1r = D(w, A_, 'rpred', [D(w, A_, 'rpcxpcld', [cst(w, A_, '2rp', '2 e. RR+'), D(w, A_, 'renegcld', [xr], '-u %s e. RR' % X)], '( 2 ^c -u %s ) e. RR+' % X)], '( 2 ^c -u %s ) e. RR' % X)
        e4r = D(w, A_, 'rpred', [D(w, A_, 'rpcxpcld', [cst(w, A_, '2rp', '2 e. RR+'), D(w, A_, 'renegcld', [D(w, A_, 'rerpdivcld', [xr, cst(w, A_, '4rp', '4 e. RR+')], '( %s / 4 ) e. RR' % X)], '-u ( %s / 4 ) e. RR' % X)],
                                         '( 2 ^c -u ( %s / 4 ) ) e. RR+' % X)], '( 2 ^c -u ( %s / 4 ) ) e. RR' % X)
        mA = lift(mr, 'M e. RR')
        return D(w, A_, 'letrd', [D(w, A_, 'abscld', [D(w, A_, 'ffvelcdmd', [lift(gf, 'G : CC --> CC'), zc], '( G ` %s ) e. CC' % z)], '( abs ` ( G ` %s ) ) e. RR' % z),
                                  D(w, A_, 'remulcld', [mA, e1r], '( M x. ( 2 ^c -u %s ) ) e. RR' % X), D(w, A_, 'remulcld', [mA, e4r], '( M x. ( 2 ^c -u ( %s / 4 ) ) ) e. RR' % X), g1,
                                  D(w, A_, 'lemul2ad', [e1r, e4r, mA, lift(m0, '0 <_ M'), p4], '( M x. ( 2 ^c -u %s ) ) <_ ( M x. ( 2 ^c -u ( %s / 4 ) ) )' % (X, X))],
                 '( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( %s / 4 ) ) )' % (z, X))
    # z6shift hypotheses
    A1 = '( %s /\\ z e. CC )' % ph
    zc1 = w.s([], 'simpr', '( %s -> z e. CC )' % A1)
    dmem = w.s([w.s([zc1], 'a1d', '( %s -> ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ ( ( ( Re ` z ) = A \\/ ( Re ` z ) = B ) \\/ 1 <_ ( abs ` ( Im ` z ) ) ) ) -> z e. CC ) )' % A1)], 'ralrimiva',
               '( %s -> A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ ( ( ( Re ` z ) = A \\/ ( Re ` z ) = B ) \\/ 1 <_ ( abs ` ( Im ` z ) ) ) ) -> z e. CC ) )' % ph)
    A2 = '( %s /\\ ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ 1 <_ ( abs ` ( Im ` z ) ) ) )' % A1
    l2 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A2, f))
    c2 = w.s([], 'simpr', '( %s -> ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ 1 <_ ( abs ` ( Im ` z ) ) ) )' % A2)
    lohi = w.s([c2, w.inst('simpl')], 'syl', '( %s -> ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) )' % A2)
    sbz = sb(A2, 'z', w.s([zc1], 'adantr', '( %s -> z e. CC )' % A2), w.s([lohi, w.inst('simpl')], 'syl', '( %s -> A <_ ( Re ` z ) )' % A2), w.s([lohi, w.inst('simpr')], 'syl', '( %s -> ( Re ` z ) <_ B )' % A2),
             w.s([c2, w.inst('simpr')], 'syl', '( %s -> 1 <_ ( abs ` ( Im ` z ) ) )' % A2), l2)
    sball = w.s([w.s([sbz], 'ex', '( %s -> ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ 1 <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( G ` z ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` ( Im ` z ) ) / 4 ) ) ) ) )' % A1)],
                'ralrimiva', '( %s -> A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ 1 <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( G ` z ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` ( Im ` z ) ) / 4 ) ) ) ) )' % ph)
    # rectangles: Goursat
    A3 = '( %s /\\ t e. RR+ )' % ph
    l3 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A3, f))
    t3 = D(w, A3, 'rpred', [w.s([], 'simpr', '( %s -> t e. RR+ )' % A3)], 't e. RR'); nt3 = D(w, A3, 'renegcld', [t3], '-u t e. RR')
    a3 = l3(ar, 'A e. RR'); b3 = l3(br, 'B e. RR')
    P_, Q_ = CP('A', '-u t'), CP('B', 't')
    pc = cpcl(w, A3, 'A', '-u t', a3, nt3); qc = cpcl(w, A3, 'B', 't', b3, t3)
    rP, iP = reim_cp(w, A3, 'A', '-u t', a3, nt3); rQ, iQ = reim_cp(w, A3, 'B', 't', b3, t3)
    g1_ = D(w, A3, '3brtr4d', [D(w, A3, 'ltled', [a3, b3, l3(alb, 'A < B')], 'A <_ B'), rP, rQ], '( Re ` %s ) <_ ( Re ` %s )' % (P_, Q_))
    tpos = D(w, A3, 'rpgt0d', [w.s([], 'simpr', '( %s -> t e. RR+ )' % A3)], '0 < t')
    g2_ = D(w, A3, '3brtr4d', [D(w, A3, 'ltled', [nt3, t3, D(w, A3, 'lttrd', [nt3, cst(w, A3, '0re', '0 e. RR'), t3, D(w, A3, 'mpbid', [tpos, D(w, A3, 'lt0neg2d', [t3], '( 0 < t <-> -u t < 0 )')], '-u t < 0'), tpos], '-u t < t')], '-u t <_ t'),
                               iP, iQ], '( Im ` %s ) <_ ( Im ` %s )' % (P_, Q_))
    crs = D(w, A3, 'sstrd', [w.s([D(w, A3, 'jca', [pc, qc], '( %s e. CC /\\ %s e. CC )' % (P_, Q_)), w.inst('crectss')], 'syl', '( %s -> ( %s crect %s ) C_ CC )' % (A3, P_, Q_)), l3(gdv, 'CC C_ dom ( CC _D G )')],
            '( %s crect %s ) C_ dom ( CC _D G )' % (P_, Q_))
    gour = w.s([D(w, A3, 'jca', [pc, qc], '( %s e. CC /\\ %s e. CC )' % (P_, Q_)), D(w, A3, 'jca', [g1_, g2_], '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (P_, Q_, P_, Q_)),
                D(w, A3, 'jca', [l3(gcn, 'G e. ( CC -cn-> CC )'), crs], '( G e. ( CC -cn-> CC ) /\\ ( %s crect %s ) C_ dom ( CC _D G ) )' % (P_, Q_)), w.inst('rectintgour')], 'syl3anc',
               '( %s -> ( G rectint <. %s , %s >. ) = 0 )' % (A3, P_, Q_))
    rall = w.s([w.s([gour], 'a1d', '( %s -> ( 1 <_ t -> ( G rectint <. %s , %s >. ) = 0 ) )' % (A3, P_, Q_))], 'ralrimiva', '( %s -> A. t e. RR+ ( 1 <_ t -> ( G rectint <. %s , %s >. ) = 0 ) )' % (ph, P_, Q_))
    SH = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ A < B ) /\\ ( ( G e. ( CC -cn-> CC ) /\\ A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ ( ( ( Re ` z ) = A \\/ ( Re ` z ) = B ) \\/ 1 <_ ( abs ` ( Im ` z ) ) ) ) -> z e. CC ) ) /\\ '
          '( ( M e. RR /\\ 1 e. RR+ ) /\\ A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ 1 <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( G ` z ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` ( Im ` z ) ) / 4 ) ) ) ) ) ) ) /\\ '
          '( 0 e. CC /\\ A. t e. RR+ ( 1 <_ t -> ( G rectint <. %s , %s >. ) = 0 ) ) )' % (P_, Q_))
    DM = 'A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ ( ( ( Re ` z ) = A \\/ ( Re ` z ) = B ) \\/ 1 <_ ( abs ` ( Im ` z ) ) ) ) -> z e. CC )'
    BD = 'A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ 1 <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( G ` z ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` ( Im ` z ) ) / 4 ) ) ) )'
    X1 = '( G e. ( CC -cn-> CC ) /\\ %s )' % DM
    X2 = '( ( M e. RR /\\ 1 e. RR+ ) /\\ %s )' % BD
    RT = 'A. t e. RR+ ( 1 <_ t -> ( G rectint <. %s , %s >. ) = 0 )' % (P_, Q_)
    x1 = D(w, ph, 'jca', [gcn, dmem], X1)
    x2 = D(w, ph, 'jca', [D(w, ph, 'jca', [mr, cst(w, ph, '1rp', '1 e. RR+')], '( M e. RR /\\ 1 e. RR+ )'), sball], X2)
    big = D(w, ph, 'jca', [l0, D(w, ph, 'jca', [x1, x2], '( %s /\\ %s )' % (X1, X2))], '( %s /\\ ( %s /\\ %s ) )' % (L0, X1, X2))
    kk = D(w, ph, 'jca', [cst(w, ph, '0cn', '0 e. CC'), rall], '( 0 e. CC /\\ %s )' % RT)
    sh = w.s([l0, D(w, ph, 'jca', [x1, x2], '( %s /\\ %s )' % (X1, X2)), kk, w.inst('z6shift')], 'syl3anc', '( %s -> ( %s - %s ) = 0 )' % (ph, VL('G', 'B'), VL('G', 'A')))
    # both line integrals converge (z6vlcvg on Re = A and Re = B)
    def vlc(C0, c0r, loC, hiC):
        A4 = '( %s /\\ u e. RR )' % ph
        l4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A4, f))
        uR = w.s([], 'simpr', '( %s -> u e. RR )' % A4)
        z = CP(C0, 'u')
        zc = cpcl(w, A4, C0, 'u', l4(c0r, '%s e. RR' % C0), uR)
        rz, iz = reim_cp(w, A4, C0, 'u', l4(c0r, '%s e. RR' % C0), uR)
        linm = w.s([zc], 'ralrimiva', '( %s -> A. u e. RR %s e. CC )' % (ph, z))
        A5 = '( %s /\\ 1 <_ ( abs ` u ) )' % A4
        l5 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A5, f))
        i1 = D(w, A5, 'eqbrtrrd' if False else 'breqtrrd', [w.s([], 'simpr', '( %s -> 1 <_ ( abs ` u ) )' % A5), D(w, A5, 'fveq2d', [w.s([iz], 'adantr', '( %s -> ( Im ` %s ) = u )' % (A5, z))], '( abs ` ( Im ` %s ) ) = ( abs ` u )' % z)],
               '1 <_ ( abs ` ( Im ` %s ) )' % z)
        lo = D(w, A5, 'breqtrrd', [l5(loC, 'A <_ %s' % C0), w.s([rz], 'adantr', '( %s -> ( Re ` %s ) = %s )' % (A5, z, C0))], 'A <_ ( Re ` %s )' % z)
        hi = D(w, A5, 'eqbrtrd', [w.s([rz], 'adantr', '( %s -> ( Re ` %s ) = %s )' % (A5, z, C0)), l5(hiC, '%s <_ B' % C0)], '( Re ` %s ) <_ B' % z)
        bz = sb(A5, z, w.s([zc], 'adantr', '( %s -> %s e. CC )' % (A5, z)), lo, hi, i1, l5)
        bz2 = D(w, A5, 'breqtrd', [bz, D(w, A5, 'oveq2d', [D(w, A5, 'oveq2d', [D(w, A5, 'negeqd', [D(w, A5, 'oveq1d', [D(w, A5, 'fveq2d', [w.s([iz], 'adantr', '( %s -> ( Im ` %s ) = u )' % (A5, z))], '( abs ` ( Im ` %s ) ) = ( abs ` u )' % z)],
                                                                                                    '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % z)], '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % z)],
                                                          '( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) = ( 2 ^c -u ( ( abs ` u ) / 4 ) )' % z)], '( M x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) ) = ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) )' % z)],
                  '( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) )' % z)
        ball = w.s([w.s([bz2], 'ex', '( %s -> ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % (A4, z))], 'ralrimiva',
                   '( %s -> A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % (ph, z))
        V6 = ('( ( %s e. RR /\\ ( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) ) /\\ ( ( M e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) ) )'
              % (C0, z, z))
        v6 = D(w, ph, 'jca', [D(w, ph, 'jca', [c0r, D(w, ph, 'jca', [gcn, linm], '( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC )' % z)], '( %s e. RR /\\ ( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) )' % (C0, z)),
                              D(w, ph, 'jca', [D(w, ph, 'jca', [mr, cst(w, ph, '1rp', '1 e. RR+')], '( M e. RR /\\ 1 e. RR+ )'), ball],
                                '( ( M e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % z)], V6)
        vc = w.s([v6, w.inst('z6vlcvg')], 'syl', '( %s -> ( ( t e. RR+ |-> %s ) ~~>r %s /\\ A. t e. RR+ ( 1 <_ t -> ( abs ` ( %s - %s ) ) <_ ( ( ( 8 x. M ) / ( log ` 2 ) ) x. ( 2 ^c -u ( t / 4 ) ) ) ) ) )'
                 % (ph, LT('G', C0, 't'), VL('G', C0), VL('G', C0), LT('G', C0, 't')))
        return w.s([w.s([vc, w.inst('simpl')], 'syl', '( %s -> ( t e. RR+ |-> %s ) ~~>r %s )' % (ph, LT('G', C0, 't'), VL('G', C0))), w.inst('rlimcl')], 'syl', '( %s -> %s e. CC )' % (ph, VL('G', C0)))
    leAB = D(w, ph, 'ltled', [ar, br, alb], 'A <_ B')
    vA = vlc('A', ar, D(w, ph, 'leidd', [ar], 'A <_ A'), leAB)
    vB = vlc('B', br, leAB, D(w, ph, 'leidd', [br], 'B <_ B'))
    eqv = D(w, ph, 'subeq0d', [vB, vA, sh], '%s = %s' % (VL('G', 'B'), VL('G', 'A'))) if False else D(w, ph, 'subeq0d', [sh], '%s = %s' % (VL('G', 'B'), VL('G', 'A')))
    w.qed([eqv, vA], 'jca', S['zl3shv'])
    go(w, only)


# ---------------------------------------------------------------- zl3vl0
if __name__ == '__main__' and (not only or 'zl3vl0' in only):
    w = W('zl3vl0', 'The vertical-line integral on ` Re w = 0 ` is ` i ` times the improper real integral of ` G ( i x ) `.')
    ph, concl = ante_of(S['zl3vl0'])
    HB = 'A. b e. RR ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` b ) ) )' % CP('0', 'b')
    gm = w.s([], 'simpl', '( %s -> ( G e. ( CC -cn-> CC ) /\\ M e. RR ) )' % ph)
    gcn = w.s([gm, w.inst('simpl')], 'syl', '( %s -> G e. ( CC -cn-> CC ) )' % ph); mr = w.s([gm, w.inst('simpr')], 'syl', '( %s -> M e. RR )' % ph)
    hb = w.s([], 'simpr', '( %s -> %s )' % (ph, HB))
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % ph)
    def hb_at(A_, hbA, bexpr, bre):
        E = 'b = %s' % bexpr
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        cpe = D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [e], '( _i x. b ) = ( _i x. %s )' % bexpr)], '%s = %s' % (CP('0', 'b'), CP('0', bexpr)))
        eq = D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [cpe], '( G ` %s ) = ( G ` %s )' % (CP('0', 'b'), CP('0', bexpr)))], '( abs ` ( G ` %s ) ) = ( abs ` ( G ` %s ) )' % (CP('0', 'b'), CP('0', bexpr))),
                                 D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [e], '( abs ` b ) = ( abs ` %s )' % bexpr)], '-u ( abs ` b ) = -u ( abs ` %s )' % bexpr)],
                                                                   '( 2 ^c -u ( abs ` b ) ) = ( 2 ^c -u ( abs ` %s ) )' % bexpr)], '( M x. ( 2 ^c -u ( abs ` b ) ) ) = ( M x. ( 2 ^c -u ( abs ` %s ) ) )' % bexpr)],
                 '( ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` b ) ) ) <-> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` %s ) ) ) )' % (CP('0', 'b'), CP('0', bexpr), bexpr))
        return w.s([bre, hbA, w.s([eq], 'rspcv', '( %s e. RR -> ( %s -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` %s ) ) ) ) )' % (bexpr, HB, CP('0', bexpr), bexpr))], 'sylc',
                   '( %s -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` %s ) ) ) )' % (A_, CP('0', bexpr), bexpr))
    # M >_ 0
    z0 = cst(w, ph, '0re', '0 e. RR')
    h0 = hb_at(ph, hb, '0', z0)
    p0 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [D(w, ph, 'eqtrd', [D(w, ph, 'negeqd', [cst(w, ph, 'abs0', '( abs ` 0 ) = 0')], '-u ( abs ` 0 ) = -u 0'), cst(w, ph, 'neg0', '-u 0 = 0')], '-u ( abs ` 0 ) = 0')],
                                        '( 2 ^c -u ( abs ` 0 ) ) = ( 2 ^c 0 )'), w.s([cst(w, ph, '2cn', '2 e. CC'), w.inst('cxp0')], 'syl', '( %s -> ( 2 ^c 0 ) = 1 )' % ph)], '( 2 ^c -u ( abs ` 0 ) ) = 1')
    mm1 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [p0], '( M x. ( 2 ^c -u ( abs ` 0 ) ) ) = ( M x. 1 )'), D(w, ph, 'mulridd', [D(w, ph, 'recnd', [mr], 'M e. CC')], '( M x. 1 ) = M')], '( M x. ( 2 ^c -u ( abs ` 0 ) ) ) = M')
    g0c = D(w, ph, 'ffvelcdmd', [gf, cpcl(w, ph, '0', '0', z0, z0)], '( G ` %s ) e. CC' % CP('0', '0'))
    m0 = D(w, ph, 'letrd', [cst(w, ph, '0re', '0 e. RR'), D(w, ph, 'abscld', [g0c], '( abs ` ( G ` %s ) ) e. RR' % CP('0', '0')), mr, D(w, ph, 'absge0d', [g0c], '0 <_ ( abs ` ( G ` %s ) )' % CP('0', '0')),
                            D(w, ph, 'breqtrd', [h0, mm1], '( abs ` ( G ` %s ) ) <_ M' % CP('0', '0'))], '0 <_ M')
    # z6vlcvg on Re = 0
    from zl3b_d4 import pow4 as _p4
    A4 = '( %s /\\ u e. RR )' % ph
    l4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A4, f))
    uR = w.s([], 'simpr', '( %s -> u e. RR )' % A4)
    z = CP('0', 'u')
    zc = cpcl(w, A4, '0', 'u', cst(w, A4, '0re', '0 e. RR'), uR)
    linm = w.s([zc], 'ralrimiva', '( %s -> A. u e. RR %s e. CC )' % (ph, z))
    A5 = '( %s /\\ 1 <_ ( abs ` u ) )' % A4
    l5 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A5, f))
    X = '( abs ` u )'
    xr = D(w, A5, 'abscld', [D(w, A5, 'recnd', [w.s([uR], 'adantr', '( %s -> u e. RR )' % A5)], 'u e. CC')], '%s e. RR' % X)
    p4 = _p4(w, A5, X, xr, w.s([], 'simpr', '( %s -> 1 <_ ( abs ` u ) )' % A5))
    hz = hb_at(A5, l5(hb, HB), 'u', w.s([uR], 'adantr', '( %s -> u e. RR )' % A5))
    e1r = D(w, A5, 'rpred', [D(w, A5, 'rpcxpcld', [cst(w, A5, '2rp', '2 e. RR+'), D(w, A5, 'renegcld', [xr], '-u %s e. RR' % X)], '( 2 ^c -u %s ) e. RR+' % X)], '( 2 ^c -u %s ) e. RR' % X)
    e4r = D(w, A5, 'rpred', [D(w, A5, 'rpcxpcld', [cst(w, A5, '2rp', '2 e. RR+'), D(w, A5, 'renegcld', [D(w, A5, 'rerpdivcld', [xr, cst(w, A5, '4rp', '4 e. RR+')], '( %s / 4 ) e. RR' % X)], '-u ( %s / 4 ) e. RR' % X)],
                                     '( 2 ^c -u ( %s / 4 ) ) e. RR+' % X)], '( 2 ^c -u ( %s / 4 ) ) e. RR' % X)
    m5 = l5(mr, 'M e. RR')
    gz = D(w, A5, 'ffvelcdmd', [l5(gf, 'G : CC --> CC'), w.s([zc], 'adantr', '( %s -> %s e. CC )' % (A5, z))], '( G ` %s ) e. CC' % z)
    bz = D(w, A5, 'letrd', [D(w, A5, 'abscld', [gz], '( abs ` ( G ` %s ) ) e. RR' % z), D(w, A5, 'remulcld', [m5, e1r], '( M x. ( 2 ^c -u %s ) ) e. RR' % X),
                            D(w, A5, 'remulcld', [m5, e4r], '( M x. ( 2 ^c -u ( %s / 4 ) ) ) e. RR' % X), hz, D(w, A5, 'lemul2ad', [e1r, e4r, m5, l5(m0, '0 <_ M'), p4], '( M x. ( 2 ^c -u %s ) ) <_ ( M x. ( 2 ^c -u ( %s / 4 ) ) )' % (X, X))],
            '( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( %s / 4 ) ) )' % (z, X))
    ball = w.s([w.s([bz], 'ex', '( %s -> ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % (A4, z))], 'ralrimiva',
               '( %s -> A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % (ph, z))
    V6 = ('( ( 0 e. RR /\\ ( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) ) /\\ ( ( M e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) ) )' % (z, z))
    v6 = D(w, ph, 'jca', [D(w, ph, 'jca', [z0, D(w, ph, 'jca', [gcn, linm], '( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC )' % z)], '( 0 e. RR /\\ ( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) )' % z),
                          D(w, ph, 'jca', [D(w, ph, 'jca', [mr, cst(w, ph, '1rp', '1 e. RR+')], '( M e. RR /\\ 1 e. RR+ )'), ball],
                            '( ( M e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % z)], V6)
    VL0 = VL('G', '0'); LTt = LT('G', '0', 't')
    vc = w.s([v6, w.inst('z6vlcvg')], 'syl', '( %s -> ( ( t e. RR+ |-> %s ) ~~>r %s /\\ A. t e. RR+ ( 1 <_ t -> ( abs ` ( %s - %s ) ) <_ ( ( ( 8 x. M ) / ( log ` 2 ) ) x. ( 2 ^c -u ( t / 4 ) ) ) ) ) )'
             % (ph, LTt, VL0, VL0, LTt))
    lim = w.s([vc, w.inst('simpl')], 'syl', '( %s -> ( t e. RR+ |-> %s ) ~~>r %s )' % (ph, LTt, VL0))
    # z6lvert for each t
    A6 = '( %s /\\ t e. RR+ )' % ph
    l6 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A6, f))
    trp = w.s([], 'simpr', '( %s -> t e. RR+ )' % A6)
    tr = D(w, A6, 'rpred', [trp], 't e. RR')
    lo = cpcl(w, A6, '0', '-u t', cst(w, A6, '0re', '0 e. RR'), D(w, A6, 'renegcld', [tr], '-u t e. RR')); hi = cpcl(w, A6, '0', 't', cst(w, A6, '0re', '0 e. RR'), tr)
    segc = w.s([D(w, A6, 'jca', [lo, hi], '( %s e. CC /\\ %s e. CC )' % (CP('0', '-u t'), CP('0', 't'))), w.inst('csegcl')], 'syl', '( %s -> ( %s cseg %s ) C_ CC )' % (A6, CP('0', '-u t'), CP('0', 't')))
    lv = w.s([D(w, A6, 'jca', [cst(w, A6, '0re', '0 e. RR'), trp], '( 0 e. RR /\\ t e. RR+ )'), D(w, A6, 'jca', [l6(gcn, 'G e. ( CC -cn-> CC )'), segc], '( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC )' % (CP('0', '-u t'), CP('0', 't'))),
              w.inst('z6lvert')], 'syl2anc', '( %s -> ( ( u e. ( -u t (,) t ) |-> ( G ` %s ) ) e. L^1 /\\ %s = ( _i x. S. ( -u t (,) t ) ( G ` %s ) _d u ) ) )' % (A6, z, LTt, z))
    lv2 = w.s([lv, w.inst('simpr')], 'syl', '( %s -> %s = ( _i x. S. ( -u t (,) t ) ( G ` %s ) _d u ) )' % (A6, LTt, z))
    IX = 'S. ( -u t (,) t ) ( G ` %s ) _d x' % CP('0', 'x')
    cbi = w.s([w.s([w.s([w.s([], 'oveq2', '( u = x -> ( _i x. u ) = ( _i x. x ) )')], 'oveq2d', '( u = x -> %s = %s )' % (z, CP('0', 'x')))], 'fveq2d', '( u = x -> ( G ` %s ) = ( G ` %s ) )' % (z, CP('0', 'x')))],
              'cbvitgv', 'S. ( -u t (,) t ) ( G ` %s ) _d u = %s' % (z, IX))
    lv3 = D(w, A6, 'eqtrd', [lv2, D(w, A6, 'oveq2d', [w.s([cbi], 'a1i', '( %s -> S. ( -u t (,) t ) ( G ` %s ) _d u = %s )' % (A6, z, IX))], '( _i x. S. ( -u t (,) t ) ( G ` %s ) _d u ) = ( _i x. %s )' % (z, IX))],
            '%s = ( _i x. %s )' % (LTt, IX))
    ltc = w.s([D(w, A6, 'jca', [D(w, A6, 'jca', [lo, hi], '( %s e. CC /\\ %s e. CC )' % (CP('0', '-u t'), CP('0', 't'))), D(w, A6, 'jca', [l6(gcn, 'G e. ( CC -cn-> CC )'), segc], '( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC )' % (CP('0', '-u t'), CP('0', 't')))],
                     '( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (CP('0', '-u t'), CP('0', 't'), CP('0', '-u t'), CP('0', 't'))), w.inst('lintcl')], 'syl',
              '( %s -> %s e. CC )' % (A6, LTt))
    ic6 = cst(w, A6, 'ax-icn', '_i e. CC'); nic6 = D(w, A6, 'negcld', [ic6], '-u _i e. CC')
    # -i LT = I
    ixc = D(w, A6, 'eqeltrrd' if False else 'mulcld', [nic6, ltc], '( -u _i x. %s ) e. CC' % LTt)
    q1 = D(w, A6, 'oveq2d', [lv3], '( -u _i x. %s ) = ( -u _i x. ( _i x. %s ) )' % (LTt, IX))
    ii1 = D(w, A6, 'eqtrd', [D(w, A6, 'eqtrd', [D(w, A6, 'mulneg1d', [ic6, ic6], '( -u _i x. _i ) = -u ( _i x. _i )'), D(w, A6, 'negeqd', [cst(w, A6, 'ixi', '( _i x. _i ) = -u 1')], '-u ( _i x. _i ) = -u -u 1')],
                                                '( -u _i x. _i ) = -u -u 1'), D(w, A6, 'negnegd', [cst(w, A6, 'ax-1cn', '1 e. CC')], '-u -u 1 = 1')], '( -u _i x. _i ) = 1')
    ixc2 = w.s([lv, w.s([], 'x', 'x')], 'x', 'x') if False else None
    # I e. CC via itgcl from L^1 (u-form), then cbv
    iuc = w.s([w.s([lv, w.inst('simpl')], 'syl', '( %s -> ( u e. ( -u t (,) t ) |-> ( G ` %s ) ) e. L^1 )' % (A6, z)),
               D(w, '( %s /\\ u e. ( -u t (,) t ) )' % A6, 'ffvelcdmd', [w.s([l6(gf, 'G : CC --> CC')], 'adantr', '( ( %s /\\ u e. ( -u t (,) t ) ) -> G : CC --> CC )' % A6),
                                                                          cpcl(w, '( %s /\\ u e. ( -u t (,) t ) )' % A6, '0', 'u', cst(w, '( %s /\\ u e. ( -u t (,) t ) )' % A6, '0re', '0 e. RR'),
                                                                               w.s([w.s([], 'simpr', '( ( %s /\\ u e. ( -u t (,) t ) ) -> u e. ( -u t (,) t ) )' % A6), w.inst('elioore')], 'syl', '( ( %s /\\ u e. ( -u t (,) t ) ) -> u e. RR )' % A6))],
                 '( G ` %s ) e. CC' % z)], 'itgcl', '( %s -> S. ( -u t (,) t ) ( G ` %s ) _d u e. CC )' % (A6, z))
    ixcc = D(w, A6, 'eqeltrrd', [w.s([cbi], 'a1i', '( %s -> S. ( -u t (,) t ) ( G ` %s ) _d u = %s )' % (A6, z, IX)), iuc], '%s e. CC' % IX)
    q2 = D(w, A6, 'eqtr3d', [D(w, A6, 'mulassd', [nic6, ic6, ixcc], '( ( -u _i x. _i ) x. %s ) = ( -u _i x. ( _i x. %s ) )' % (IX, IX)), D(w, A6, 'eqtrd', [D(w, A6, 'oveq1d', [ii1], '( ( -u _i x. _i ) x. %s ) = ( 1 x. %s )' % (IX, IX)), D(w, A6, 'mullidd', [ixcc], '( 1 x. %s ) = %s' % (IX, IX))],
                                                                                                                              '( ( -u _i x. _i ) x. %s ) = %s' % (IX, IX))], '( -u _i x. ( _i x. %s ) ) = %s' % (IX, IX))
    q3 = D(w, A6, 'eqtrd', [q1, q2], '( -u _i x. %s ) = %s' % (LTt, IX))
    meq = w.s([q3], 'mpteq2dva', '( %s -> ( t e. RR+ |-> ( -u _i x. %s ) ) = ( t e. RR+ |-> %s ) )' % (ph, LTt, IX))
    rc = w.s([w.s([cst(w, ph, 'rpssre', 'RR+ C_ RR'), D(w, ph, 'negcld', [cst(w, ph, 'ax-icn', '_i e. CC')], '-u _i e. CC'), w.inst('rlimconst')], 'syl2anc', '( %s -> ( t e. RR+ |-> -u _i ) ~~>r -u _i )' % ph)], 'idi',
             '( %s -> ( t e. RR+ |-> -u _i ) ~~>r -u _i )' % ph)
    VLe = vl_e('G', '0'); vte = vl_te(w, 'G', '0')
    lime = D(w, ph, 'breqtrd', [lim, w.s([vte], 'a1i', '( %s -> %s = %s )' % (ph, VL0, VLe))], '( t e. RR+ |-> %s ) ~~>r %s' % (LTt, VLe))
    rm = w.s([nic6, ltc, rc, lime], 'rlimmul', '( %s -> ( t e. RR+ |-> ( -u _i x. %s ) ) ~~>r ( -u _i x. %s ) )' % (ph, LTt, VLe))
    ri = D(w, ph, 'mpbid', [rm, D(w, ph, 'breq1d', [meq], '( ( t e. RR+ |-> ( -u _i x. %s ) ) ~~>r ( -u _i x. %s ) <-> ( t e. RR+ |-> %s ) ~~>r ( -u _i x. %s ) )' % (LTt, VLe, IX, VLe))],
           '( t e. RR+ |-> %s ) ~~>r ( -u _i x. %s )' % (IX, VLe))
    IF = '( t e. RR+ |-> %s )' % IX
    dm = w.s([ri, w.s([w.s([], 'rlimrel', 'Rel ~~>r')], 'releldmi', '( %s ~~>r ( -u _i x. %s ) -> %s e. dom ~~>r )' % (IF, VLe, IF))], 'syl', '( %s -> %s e. dom ~~>r )' % (ph, IF))
    iff = w.s([ixcc, w.s([], 'eqid', '%s = %s' % (IF, IF))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (ph, IF))
    sup = cst(w, ph, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    rv = D(w, ph, 'mpbid', [dm, w.s([iff, sup], 'rlimdm', '( %s -> ( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) ) )' % (ph, IF, IF, IF))], '%s ~~>r ( ~~>r ` %s )' % (IF, IF))
    un = w.s([iff, sup, rv, ri], 'rlimuni', '( %s -> ( ~~>r ` %s ) = ( -u _i x. %s ) )' % (ph, IF, VLe))
    vlc = w.s([lime, w.inst('rlimcl')], 'syl', '( %s -> %s e. CC )' % (ph, VLe))
    ic = cst(w, ph, 'ax-icn', '_i e. CC')
    f1 = D(w, ph, 'oveq2d', [un], '( _i x. ( ~~>r ` %s ) ) = ( _i x. ( -u _i x. %s ) )' % (IF, VLe))
    f2 = D(w, ph, 'mulassd', [ic, D(w, ph, 'negcld', [ic], '-u _i e. CC'), vlc], '( ( _i x. -u _i ) x. %s ) = ( _i x. ( -u _i x. %s ) )' % (VLe, VLe))
    f3 = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [D(w, ph, 'mulneg2d', [ic, ic], '( _i x. -u _i ) = -u ( _i x. _i )'), D(w, ph, 'negeqd', [cst(w, ph, 'ixi', '( _i x. _i ) = -u 1')], '-u ( _i x. _i ) = -u -u 1')],
                                              '( _i x. -u _i ) = -u -u 1'), D(w, ph, 'negnegd', [cst(w, ph, 'ax-1cn', '1 e. CC')], '-u -u 1 = 1')], '( _i x. -u _i ) = 1')
    f4 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq1d', [f3], '( ( _i x. -u _i ) x. %s ) = ( 1 x. %s )' % (VLe, VLe)), D(w, ph, 'mullidd', [vlc], '( 1 x. %s ) = %s' % (VLe, VLe))], '( ( _i x. -u _i ) x. %s ) = %s' % (VLe, VLe))
    fin0 = D(w, ph, 'eqtrd', [f1, D(w, ph, 'eqtr3d', [f2, f4], '( _i x. ( -u _i x. %s ) ) = %s' % (VLe, VLe))], '( _i x. ( ~~>r ` %s ) ) = %s' % (IF, VLe))
    fin = D(w, ph, 'eqtr4d', [fin0, w.s([vte], 'a1i', '( %s -> %s = %s )' % (ph, VL0, VLe))], '( _i x. ( ~~>r ` %s ) ) = %s' % (IF, VL0))
    ifc = D(w, ph, 'eqeltrd', [un, D(w, ph, 'mulcld', [D(w, ph, 'negcld', [cst(w, ph, 'ax-icn', '_i e. CC')], '-u _i e. CC'), vlc], '( -u _i x. %s ) e. CC' % VLe)], '( ~~>r ` %s ) e. CC' % IF)
    w.qed([D(w, ph, 'jca', [dm, ifc], '( %s e. dom ~~>r /\\ ( ~~>r ` %s ) e. CC )' % (IF, IF)), D(w, ph, 'eqcomd', [fin], '%s = ( _i x. ( ~~>r ` %s ) )' % (VL0, IF))], 'jca', S['zl3vl0'])
    go(w, only)


# ---------------------------------------------------------------- zl3eaw
if __name__ == '__main__' and (not only or 'zl3eaw' in only):
    w = W('zl3eaw', '` e ^ ( A y ) ` is an entire function of ` y `.')
    A0 = 'A e. CC'; A1 = '( A e. CC /\\ y e. CC )'; A2 = '( A e. CC /\\ x e. CC )'
    ARG = '( A x. y )'; EY = '( exp ` %s )' % ARG
    EF_ = '( y e. CC |-> %s )' % EY
    ce = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % A1)
    did = w.s([ce], 'dvmptid', '( %s -> ( CC _D ( y e. CC |-> y ) ) = ( y e. CC |-> 1 ) )' % A0)
    one1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % A1)
    ac0 = w.s([], 'id', '( A e. CC -> A e. CC )')
    dcm = w.s([ce, yc, one1, did, ac0], 'dvmptcmul', '( %s -> ( CC _D ( y e. CC |-> %s ) ) = ( y e. CC |-> ( A x. 1 ) ) )' % (A0, ARG))
    ac1 = w.s([], 'simpl', '( %s -> A e. CC )' % A1)
    argc = D(w, A1, 'mulcld', [ac1, yc], '%s e. CC' % ARG)
    a1c = D(w, A1, 'mulcld', [ac1, one1], '( A x. 1 ) e. CC')
    xc = w.s([], 'simpr', '( %s -> x e. CC )' % A2)
    exc = w.s([xc, w.inst('efcl')], 'syl', '( %s -> ( exp ` x ) e. CC )' % A2)
    efm = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC')], 'a1i', '( %s -> exp : CC --> CC )' % A0)], 'feqmptd', '( %s -> exp = ( x e. CC |-> ( exp ` x ) ) )' % A0)
    dvefd = w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'a1i', '( %s -> ( CC _D exp ) = exp )' % A0)
    d1 = w.s([w.s([efm], 'oveq2d', '( %s -> ( CC _D exp ) = ( CC _D ( x e. CC |-> ( exp ` x ) ) ) )' % A0)], 'eqcomd', '( %s -> ( CC _D ( x e. CC |-> ( exp ` x ) ) ) = ( CC _D exp ) )' % A0)
    dcy = w.s([w.s([d1, dvefd], 'eqtrd', '( %s -> ( CC _D ( x e. CC |-> ( exp ` x ) ) ) = exp )' % A0), efm], 'eqtrd', '( %s -> ( CC _D ( x e. CC |-> ( exp ` x ) ) ) = ( x e. CC |-> ( exp ` x ) ) )' % A0)
    sty = w.s([], 'fveq2', '( x = %s -> ( exp ` x ) = %s )' % (ARG, EY))
    dco = w.s([ce, ce, argc, a1c, exc, exc, dcm, dcy, sty, sty], 'dvmptco', '( %s -> ( CC _D %s ) = ( y e. CC |-> ( %s x. ( A x. 1 ) ) ) )' % (A0, EF_, EY))
    ewc = w.s([argc, w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A1, EY))
    dvc = D(w, A1, 'mulcld', [ewc, a1c], '( %s x. ( A x. 1 ) ) e. CC' % EY)
    dm = w.s([w.s([], 'eqid', '( y e. CC |-> ( %s x. ( A x. 1 ) ) ) = ( y e. CC |-> ( %s x. ( A x. 1 ) ) )' % (EY, EY)), dvc], 'dmmptd', '( %s -> dom ( y e. CC |-> ( %s x. ( A x. 1 ) ) ) = CC )' % (A0, EY))
    dmv = D(w, A0, 'eqtrd', [D(w, A0, 'dmeqd', [dco], 'dom ( CC _D %s ) = dom ( y e. CC |-> ( %s x. ( A x. 1 ) ) )' % (EF_, EY)), dm], 'dom ( CC _D %s ) = CC' % EF_)
    ff = w.s([ewc, w.s([], 'eqid', '%s = %s' % (EF_, EF_))], 'fmptd', '( %s -> %s : CC --> CC )' % (A0, EF_))
    ss = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    cn = w.s([w.s([ss, ff, ss], '3jca', '( %s -> ( CC C_ CC /\\ %s : CC --> CC /\\ CC C_ CC ) )' % (A0, EF_)), dmv, w.inst('dvcn')], 'syl2anc', '( %s -> %s e. ( CC -cn-> CC ) )' % (A0, EF_))
    w.qed([cn, D(w, A0, 'eqimssd', [D(w, A0, 'eqcomd', [dmv], 'CC = dom ( CC _D %s )' % EF_)], 'CC C_ dom ( CC _D %s )' % EF_)], 'jca', S['zl3eaw'])
    go(w, only)


# ---------------------------------------------------------------- zl3gkr / zl3gkl
def hol_expmul(w, ph, Ftxt, fhol, Acoef, acc, bnd='y'):
    """( ph -> HOL ( bnd e. CC |-> ( ( F ` bnd ) x. ( exp ` ( Acoef x. bnd ) ) ) ) ) from fhol: ( ph -> HOL(F, CC) ), acc: ( ph -> Acoef e. CC )"""
    EAW = '( y e. CC |-> ( exp ` ( %s x. y ) ) )' % Acoef
    HOLt = lambda f: '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (f, f)
    ea = w.s([acc, w.inst('zl3eaw')], 'syl', '( %s -> %s )' % (ph, HOLt(EAW)))
    Hz = '( z e. CC |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (Ftxt, EAW)
    hm = w.s([fhol, ea, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (ph, HOLt(Hz)))
    Hz2 = '( z e. CC |-> ( ( %s ` z ) x. ( exp ` ( %s x. z ) ) ) )' % (Ftxt, Acoef)
    Hb = '( %s e. CC |-> ( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) )' % (bnd, Ftxt, bnd, Acoef, bnd)
    A1 = '( %s /\\ z e. CC )' % ph
    ev = w.s([w.s([], 'simpr', '( %s -> z e. CC )' % A1), w.s([w.s([w.s([w.s([], 'oveq2', '( y = z -> ( %s x. y ) = ( %s x. z ) )' % (Acoef, Acoef))], 'fveq2d', '( y = z -> ( exp ` ( %s x. y ) ) = ( exp ` ( %s x. z ) ) )' % (Acoef, Acoef))],
                                                                  'idi', '( y = z -> ( exp ` ( %s x. y ) ) = ( exp ` ( %s x. z ) ) )' % (Acoef, Acoef)), w.s([], 'eqid', '%s = %s' % (EAW, EAW)), w.s([], 'fvex', '( exp ` ( %s x. z ) ) e. _V' % Acoef)],
                                                            'fvmpt', '( z e. CC -> ( %s ` z ) = ( exp ` ( %s x. z ) ) )' % (EAW, Acoef))], 'syl', '( %s -> ( %s ` z ) = ( exp ` ( %s x. z ) ) )' % (A1, EAW, Acoef))
    m1 = w.s([D(w, A1, 'oveq2d', [ev], '( ( %s ` z ) x. ( %s ` z ) ) = ( ( %s ` z ) x. ( exp ` ( %s x. z ) ) )' % (Ftxt, EAW, Ftxt, Acoef))], 'mpteq2dva', '( %s -> %s = %s )' % (ph, Hz, Hz2))
    Ez = 'z = %s' % bnd
    ez = w.s([], 'id', '( %s -> %s )' % (Ez, Ez))
    cb = w.s([D(w, Ez, 'oveq12d', [D(w, Ez, 'fveq2d', [ez], '( %s ` z ) = ( %s ` %s )' % (Ftxt, Ftxt, bnd)), D(w, Ez, 'fveq2d', [D(w, Ez, 'oveq2d', [ez], '( %s x. z ) = ( %s x. %s )' % (Acoef, Acoef, bnd))],
                                                                                                                  '( exp ` ( %s x. z ) ) = ( exp ` ( %s x. %s ) )' % (Acoef, Acoef, bnd))],
                        '( ( %s ` z ) x. ( exp ` ( %s x. z ) ) ) = ( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) )' % (Ftxt, Acoef, Ftxt, bnd, Acoef, bnd))], 'cbvmptv', '%s = %s' % (Hz2, Hb))
    eq = D(w, ph, 'eqtrd', [m1, w.s([cb], 'a1i', '( %s -> %s = %s )' % (ph, Hz2, Hb))], '%s = %s' % (Hz, Hb))
    h1 = D(w, ph, 'eleq1d', [eq], '( %s e. ( CC -cn-> CC ) <-> %s e. ( CC -cn-> CC ) )' % (Hz, Hb))
    h2 = D(w, ph, 'sseq2d', [D(w, ph, 'dmeqd', [D(w, ph, 'oveq2d', [eq], '( CC _D %s ) = ( CC _D %s )' % (Hz, Hb))], 'dom ( CC _D %s ) = dom ( CC _D %s )' % (Hz, Hb))],
            '( CC C_ dom ( CC _D %s ) <-> CC C_ dom ( CC _D %s ) )' % (Hz, Hb))
    return D(w, ph, 'mpbid', [hm, D(w, ph, 'anbi12d', [h1, h2], '( %s <-> %s )' % (HOLt(Hz), HOLt(Hb)))], HOLt(Hb))


def fv_expmul(w, A_, Ftxt, Acoef, bnd, Z, zc):
    """( A_ -> ( MPT ` Z ) = ( ( F ` Z ) x. ( exp ` ( Acoef x. Z ) ) ) ) for MPT = ( bnd e. CC |-> ... )"""
    M = '( %s e. CC |-> ( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) )' % (bnd, Ftxt, bnd, Acoef, bnd)
    E = '%s = %s' % (bnd, Z)
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    sub = D(w, E, 'oveq12d', [D(w, E, 'fveq2d', [e], '( %s ` %s ) = ( %s ` %s )' % (Ftxt, bnd, Ftxt, Z)), D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [e], '( %s x. %s ) = ( %s x. %s )' % (Acoef, bnd, Acoef, Z))],
                                                                                                      '( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. %s ) )' % (Acoef, bnd, Acoef, Z))],
            '( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) = ( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) )' % (Ftxt, bnd, Acoef, bnd, Ftxt, Z, Acoef, Z))
    f = w.s([sub, w.s([], 'eqid', '%s = %s' % (M, M)), w.s([], 'ovex', '( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) e. _V' % (Ftxt, Z, Acoef, Z))], 'fvmpt',
            '( %s e. CC -> ( %s ` %s ) = ( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) )' % (Z, M, Z, Ftxt, Z, Acoef, Z))
    return w.s([zc, f], 'syl', '( %s -> ( %s ` %s ) = ( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) )' % (A_, M, Z, Ftxt, Z, Acoef, Z))


def abs_exp(w, A_, coef, coefr, Z, zc):
    """( A_ -> ( abs ` ( exp ` ( coef x. Z ) ) ) = ( exp ` ( coef x. ( Re ` Z ) ) ) ), coef real"""
    arg = '( %s x. %s )' % (coef, Z)
    a1 = w.s([D(w, A_, 'mulcld', [D(w, A_, 'recnd', [coefr], '%s e. CC' % coef), zc], '%s e. CC' % arg), w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` %s ) ) = ( exp ` ( Re ` %s ) ) )' % (A_, arg, arg))
    a2 = w.s([coefr, zc, w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` %s ) = ( %s x. ( Re ` %s ) ) )' % (A_, arg, coef, Z))
    return D(w, A_, 'eqtrd', [a1, D(w, A_, 'fveq2d', [a2], '( exp ` ( Re ` %s ) ) = ( exp ` ( %s x. ( Re ` %s ) ) )' % (arg, coef, Z))], '( abs ` ( exp ` %s ) ) = ( exp ` ( %s x. ( Re ` %s ) ) )' % (arg, coef, Z))


def gk_lemma(side):
    R = side == 'R'
    lab = 'zl3gkr' if R else 'zl3gkl'
    w = W(lab, ('The right' if R else 'The left') + ' long side of ` R_N `: each geometric term moves to the imaginary axis and is ` i ` times a Fourier coefficient.')
    ph, concl = ante_of(S[lab])
    hc_ = w.s([], 'simpl', '( %s -> %s )' % (ph, HCTX))
    hent, krp, hdec = hctx(w, ph, hc_)
    kN = w.s([], 'simpr', '( %s -> k e. NN )' % ph)
    kr = D(w, ph, 'nnred', [kN], 'k e. RR'); kc = D(w, ph, 'nncnd', [kN], 'k e. CC')
    tpr = D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), cst(w, ph, 'pire', '_pi e. RR')], '( 2 x. _pi ) e. RR')
    tpc = D(w, ph, 'recnd', [tpr], '( 2 x. _pi ) e. CC')
    ntp = TPN; ntpr = D(w, ph, 'renegcld', [tpr], '%s e. RR' % ntp); ntpc = D(w, ph, 'recnd', [ntpr], '%s e. CC' % ntp)
    HOLt = lambda f: '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (f, f)
    if R:
        Ft = 'H'; fhol = hent; Aco = '( k x. %s )' % ntp; acr = D(w, ph, 'remulcld', [kr, ntpr], '%s e. RR' % Aco); lo, hi = '0', '1'
    else:
        glh = hol_expmul(w, ph, 'H', hent, ntp, ntpc, 'w')
        Ft = GL; fhol = glh; Aco = '( k x. ( 2 x. _pi ) )'; acr = D(w, ph, 'remulcld', [kr, tpr], '%s e. RR' % Aco); lo, hi = '-u 1', '0'
    acc = D(w, ph, 'recnd', [acr], '%s e. CC' % Aco)
    G = '( y e. CC |-> ( ( %s ` y ) x. ( exp ` ( %s x. y ) ) ) )' % (Ft, Aco)
    assert G == GKE(Ft if not R else 'H', ntp if R else '( 2 x. _pi )')
    gh = hol_expmul(w, ph, Ft, fhol, Aco, acc, 'y')
    gcn = w.s([gh, w.inst('simpl')], 'syl', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, G))
    # strip bound
    A1 = '( %s /\\ b e. CC )' % ph
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
    bc = w.s([], 'simpr', '( %s -> b e. CC )' % A1)
    A2 = '( %s /\\ ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) )' % (A1, lo, hi)
    l2 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A2, f))
    bc2 = w.s([bc], 'adantr', '( %s -> b e. CC )' % A2)
    lh = w.s([], 'simpr', '( %s -> ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) )' % (A2, lo, hi))
    blo = w.s([lh, w.inst('simpl')], 'syl', '( %s -> %s <_ ( Re ` b ) )' % (A2, lo)); bhi = w.s([lh, w.inst('simpr')], 'syl', '( %s -> ( Re ` b ) <_ %s )' % (A2, hi))
    rb = D(w, A2, 'recld', [bc2], '( Re ` b ) e. RR')
    m1 = cst(w, A2, 'neg1rr', '-u 1 e. RR'); p1 = cst(w, A2, '1re', '1 e. RR'); z0 = cst(w, A2, '0re', '0 e. RR')
    if R:
        m1lo = D(w, A2, 'letrd', [m1, z0, rb, D(w, A2, 'ltled', [m1, z0, cst(w, A2, 'neg1lt0', '-u 1 < 0')], '-u 1 <_ 0'), blo], '-u 1 <_ ( Re ` b )')
        hi1 = bhi
    else:
        m1lo = blo
        hi1 = D(w, A2, 'letrd', [rb, z0, p1, bhi, D(w, A2, 'ltled', [z0, p1, cst(w, A2, '0lt1', '0 < 1')], '0 <_ 1')], '( Re ` b ) <_ 1')
    rab = D(w, A2, 'mpbird', [D(w, A2, 'jca', [m1lo, hi1], '( -u 1 <_ ( Re ` b ) /\\ ( Re ` b ) <_ 1 )'), w.s([rb, p1, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` ( Re ` b ) ) <_ 1 <-> ( -u 1 <_ ( Re ` b ) /\\ ( Re ` b ) <_ 1 ) ) )' % A2)],
            '( abs ` ( Re ` b ) ) <_ 1')
    hb = D(w, A2, 'mpd', [rab, w.s([bc2, l2(hdec, HDEC), hdec_at(w, A2, None, 'b')], 'sylc', '( %s -> ( ( abs ` ( Re ` b ) ) <_ 1 -> ( abs ` ( H ` b ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) ) )' % A2)],
           '( abs ` ( H ` b ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) )')
    hf2 = w.s([w.s([l2(hent, HENT), w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % A2), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % A2)
    hbc = D(w, A2, 'ffvelcdmd', [hf2, bc2], '( H ` b ) e. CC')
    kr2 = l2(kr, 'k e. RR'); tpr2 = l2(tpr, '( 2 x. _pi ) e. RR')
    k0 = D(w, A2, 'ltled', [z0, kr2, D(w, A2, 'nngt0d', [l2(kN, 'k e. NN')], '0 < k')], '0 <_ k')
    tp0 = D(w, A2, 'ltled', [z0, tpr2, D(w, A2, 'mulgt0d' if False else 'remulgt0d' if False else 'x', [], 'x')], 'x') if False else None
    tp0 = D(w, A2, 'rpge0d', [D(w, A2, 'rpmulcld', [cst(w, A2, '2rp', '2 e. RR+'), cst(w, A2, 'pirp', '_pi e. RR+')], '( 2 x. _pi ) e. RR+')], '0 <_ ( 2 x. _pi )')
    k2p0 = D(w, A2, 'mulge0d', [kr2, tpr2, k0, tp0], '0 <_ ( k x. ( 2 x. _pi ) )')
    kt = '( k x. ( 2 x. _pi ) )'; ktr = D(w, A2, 'remulcld', [kr2, tpr2], '%s e. RR' % kt)
    MB = '( K x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) )'
    iba = D(w, A2, 'abscld', [D(w, A2, 'recnd', [D(w, A2, 'imcld', [bc2], '( Im ` b ) e. RR')], '( Im ` b ) e. CC')], '( abs ` ( Im ` b ) ) e. RR')
    pbr = D(w, A2, 'rpred', [D(w, A2, 'rpcxpcld', [cst(w, A2, '2rp', '2 e. RR+'), D(w, A2, 'renegcld', [iba], '-u ( abs ` ( Im ` b ) ) e. RR')], '( 2 ^c -u ( abs ` ( Im ` b ) ) ) e. RR+')], '( 2 ^c -u ( abs ` ( Im ` b ) ) ) e. RR')
    kK = D(w, A2, 'rpred', [l2(krp, 'K e. RR+')], 'K e. RR')
    mbr = D(w, A2, 'remulcld', [kK, pbr], '%s e. RR' % MB)
    # | exp ( Aco b ) | <_ 1
    acr2 = l2(acr, '%s e. RR' % Aco)
    ea = abs_exp(w, A2, Aco, acr2, 'b', bc2)
    if R:
        # ( k x. -2pi ) x. Re b = -u ( ( k x. 2pi ) x. Re b ) <_ 0
        e0 = D(w, A2, 'mulneg2d', [l2(kc, 'k e. CC'), l2(tpc, '( 2 x. _pi ) e. CC')], '( k x. %s ) = -u %s' % (ntp, kt))
        e1 = D(w, A2, 'eqtrd', [D(w, A2, 'oveq1d', [e0], '( %s x. ( Re ` b ) ) = ( -u %s x. ( Re ` b ) )' % (Aco, kt)), D(w, A2, 'mulneg1d', [D(w, A2, 'recnd', [ktr], '%s e. CC' % kt), D(w, A2, 'recnd', [rb], '( Re ` b ) e. CC')],
                                                                                                                          '( -u %s x. ( Re ` b ) ) = -u ( %s x. ( Re ` b ) )' % (kt, kt))], '( %s x. ( Re ` b ) ) = -u ( %s x. ( Re ` b ) )' % (Aco, kt))
        pp = D(w, A2, 'mulge0d', [ktr, rb, k2p0, blo], '0 <_ ( %s x. ( Re ` b ) )' % kt)
        le0 = D(w, A2, 'breqtrrd' if False else 'eqbrtrd', [e1, D(w, A2, 'mpbid', [pp, D(w, A2, 'le0neg2d', [D(w, A2, 'remulcld', [ktr, rb], '( %s x. ( Re ` b ) ) e. RR' % kt)], '( 0 <_ ( %s x. ( Re ` b ) ) <-> -u ( %s x. ( Re ` b ) ) <_ 0 )' % (kt, kt))],
                                                                  '-u ( %s x. ( Re ` b ) ) <_ 0' % kt)], '( %s x. ( Re ` b ) ) <_ 0' % Aco)
    else:
        nrb = D(w, A2, 'mpbid', [bhi, D(w, A2, 'le0neg2d' if False else 'x', [], 'x')], 'x') if False else None
        # ( k 2pi ) Re b <_ 0 since Re b <_ 0: -u Re b >_ 0
        nb0 = D(w, A2, 'mpbid', [bhi, D(w, A2, 'le0neg1d' if False else 'lenegcon1d' if False else 'x', [], 'x')], 'x') if False else None
        nb = D(w, A2, 'mpbid', [bhi, D(w, A2, 'lenegd', [rb, z0], '( ( Re ` b ) <_ 0 <-> -u 0 <_ -u ( Re ` b ) )')], '-u 0 <_ -u ( Re ` b )')
        nb2 = D(w, A2, 'breqtrrd' if False else 'eqbrtrrd', [cst(w, A2, 'neg0', '-u 0 = 0'), nb], '0 <_ -u ( Re ` b )')
        pp = D(w, A2, 'mulge0d', [ktr, D(w, A2, 'renegcld', [rb], '-u ( Re ` b ) e. RR'), k2p0, nb2], '0 <_ ( %s x. -u ( Re ` b ) )' % kt)
        e1 = D(w, A2, 'mulneg2d', [D(w, A2, 'recnd', [ktr], '%s e. CC' % kt), D(w, A2, 'recnd', [rb], '( Re ` b ) e. CC')], '( %s x. -u ( Re ` b ) ) = -u ( %s x. ( Re ` b ) )' % (kt, kt))
        le0 = D(w, A2, 'mpbid', [D(w, A2, 'breqtrd', [pp, e1], '0 <_ -u ( %s x. ( Re ` b ) )' % kt), D(w, A2, 'le0neg1d' if False else 'x', [], 'x')], 'x') if False else None
        le0 = D(w, A2, 'mpbird', [D(w, A2, 'breqtrd', [pp, e1], '0 <_ -u ( %s x. ( Re ` b ) )' % kt),
                                  D(w, A2, 'le0neg1d', [D(w, A2, 'remulcld', [ktr, rb], '( %s x. ( Re ` b ) ) e. RR' % kt)], '( ( %s x. ( Re ` b ) ) <_ 0 <-> 0 <_ -u ( %s x. ( Re ` b ) ) )' % (kt, kt))],
              '( %s x. ( Re ` b ) ) <_ 0' % Aco)
    are = D(w, A2, 'remulcld', [acr2, rb], '( %s x. ( Re ` b ) ) e. RR' % Aco)
    exle = D(w, A2, 'mpbid', [le0, w.s([are, z0, w.inst('efle')], 'syl2anc', '( %s -> ( ( %s x. ( Re ` b ) ) <_ 0 <-> ( exp ` ( %s x. ( Re ` b ) ) ) <_ ( exp ` 0 ) ) )' % (A2, Aco, Aco))],
             '( exp ` ( %s x. ( Re ` b ) ) ) <_ ( exp ` 0 )' % Aco)
    ex1 = D(w, A2, 'breqtrd', [D(w, A2, 'eqbrtrd', [ea, exle], '( abs ` ( exp ` ( %s x. b ) ) ) <_ ( exp ` 0 )' % Aco), cst(w, A2, 'ef0', '( exp ` 0 ) = 1')], '( abs ` ( exp ` ( %s x. b ) ) ) <_ 1' % Aco)
    exc = D(w, A2, 'efcld', [D(w, A2, 'mulcld', [l2(acc, '%s e. CC' % Aco), bc2], '( %s x. b ) e. CC' % Aco)], '( exp ` ( %s x. b ) ) e. CC' % Aco)
    gv = fv_expmul(w, A2, Ft, Aco, 'y', 'b', bc2)
    if R:
        Mfin = 'K'; fb = hb; fbc = hbc
        FB = '( abs ` ( H ` b ) )'
        fbound = MB
    else:
        # | GL ( b ) | <_ ( K x. ( exp ` ( 2 x. _pi ) ) ) x. 2 ^ -| Im b |
        glv = fv_expmul(w, A2, 'H', ntp, 'w', 'b', bc2)
        ea2 = abs_exp(w, A2, ntp, l2(ntpr, '%s e. RR' % ntp), 'b', bc2)
        # -2pi Re b <_ 2pi  <=>  -u ( 2pi Re b ) <_ 2pi  <= -1 <_ Re b
        q0 = D(w, A2, 'mulneg1d', [l2(tpc, '( 2 x. _pi ) e. CC'), D(w, A2, 'recnd', [rb], '( Re ` b ) e. CC')], '( %s x. ( Re ` b ) ) = -u ( ( 2 x. _pi ) x. ( Re ` b ) )' % ntp)
        q1 = D(w, A2, 'lemul2ad', [m1, rb, tpr2, tp0, blo], '( ( 2 x. _pi ) x. -u 1 ) <_ ( ( 2 x. _pi ) x. ( Re ` b ) )')
        q2 = D(w, A2, 'eqtrd', [D(w, A2, 'mulneg2d', [l2(tpc, '( 2 x. _pi ) e. CC'), cst(w, A2, 'ax-1cn', '1 e. CC')], '( ( 2 x. _pi ) x. -u 1 ) = -u ( ( 2 x. _pi ) x. 1 )'),
                                D(w, A2, 'negeqd', [D(w, A2, 'mulridd', [l2(tpc, '( 2 x. _pi ) e. CC')], '( ( 2 x. _pi ) x. 1 ) = ( 2 x. _pi )')], '-u ( ( 2 x. _pi ) x. 1 ) = -u ( 2 x. _pi )')],
                '( ( 2 x. _pi ) x. -u 1 ) = -u ( 2 x. _pi )')
        q3 = D(w, A2, 'eqbrtrrd', [q2, q1], '-u ( 2 x. _pi ) <_ ( ( 2 x. _pi ) x. ( Re ` b ) )')
        tprb = D(w, A2, 'remulcld', [tpr2, rb], '( ( 2 x. _pi ) x. ( Re ` b ) ) e. RR')
        q4 = D(w, A2, 'mpbid', [q3, w.s([tpr2, tprb, w.inst('lenegcon1')], 'syl2anc', '( %s -> ( -u ( 2 x. _pi ) <_ ( ( 2 x. _pi ) x. ( Re ` b ) ) <-> -u ( ( 2 x. _pi ) x. ( Re ` b ) ) <_ ( 2 x. _pi ) ) )' % A2)],
                '-u ( ( 2 x. _pi ) x. ( Re ` b ) ) <_ ( 2 x. _pi )')
        q5 = D(w, A2, 'eqbrtrd', [q0, q4], '( %s x. ( Re ` b ) ) <_ ( 2 x. _pi )' % ntp)
        ex2 = D(w, A2, 'mpbid', [q5, w.s([D(w, A2, 'remulcld', [l2(ntpr, '%s e. RR' % ntp), rb], '( %s x. ( Re ` b ) ) e. RR' % ntp), tpr2, w.inst('efle')], 'syl2anc',
                                        '( %s -> ( ( %s x. ( Re ` b ) ) <_ ( 2 x. _pi ) <-> ( exp ` ( %s x. ( Re ` b ) ) ) <_ ( exp ` ( 2 x. _pi ) ) ) )' % (A2, ntp, ntp))],
                '( exp ` ( %s x. ( Re ` b ) ) ) <_ ( exp ` ( 2 x. _pi ) )' % ntp)
        ex2b = D(w, A2, 'eqbrtrd', [ea2, ex2], '( abs ` ( exp ` ( %s x. b ) ) ) <_ ( exp ` ( 2 x. _pi ) )' % ntp)
        e2c = D(w, A2, 'efcld', [D(w, A2, 'mulcld', [l2(ntpc, '%s e. CC' % ntp), bc2], '( %s x. b ) e. CC' % ntp)], '( exp ` ( %s x. b ) ) e. CC' % ntp)
        etp = w.s([tpr2, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( 2 x. _pi ) ) e. RR )' % A2)
        glb = D(w, A2, 'eqtrd', [D(w, A2, 'fveq2d', [glv], '( abs ` ( %s ` b ) ) = ( abs ` ( ( H ` b ) x. ( exp ` ( %s x. b ) ) ) )' % (GL, ntp)),
                                 D(w, A2, 'absmuld', [hbc, e2c], '( abs ` ( ( H ` b ) x. ( exp ` ( %s x. b ) ) ) ) = ( ( abs ` ( H ` b ) ) x. ( abs ` ( exp ` ( %s x. b ) ) ) )' % (ntp, ntp))],
                '( abs ` ( %s ` b ) ) = ( ( abs ` ( H ` b ) ) x. ( abs ` ( exp ` ( %s x. b ) ) ) )' % (GL, ntp))
        gl2 = D(w, A2, 'lemul12ad', [D(w, A2, 'abscld', [hbc], '( abs ` ( H ` b ) ) e. RR'), mbr, D(w, A2, 'abscld', [e2c], '( abs ` ( exp ` ( %s x. b ) ) ) e. RR' % ntp), etp,
                                     D(w, A2, 'absge0d', [hbc], '0 <_ ( abs ` ( H ` b ) )'), D(w, A2, 'absge0d', [e2c], '0 <_ ( abs ` ( exp ` ( %s x. b ) ) )' % ntp), hb, ex2b],
                '( ( abs ` ( H ` b ) ) x. ( abs ` ( exp ` ( %s x. b ) ) ) ) <_ ( %s x. ( exp ` ( 2 x. _pi ) ) )' % (ntp, MB))
        Mfin = '( K x. ( exp ` ( 2 x. _pi ) ) )'
        mf = D(w, A2, 'mul32d', [D(w, A2, 'recnd', [kK], 'K e. CC'), D(w, A2, 'recnd', [pbr], '( 2 ^c -u ( abs ` ( Im ` b ) ) ) e. CC'), D(w, A2, 'recnd', [etp], '( exp ` ( 2 x. _pi ) ) e. CC')],
                '( %s x. ( exp ` ( 2 x. _pi ) ) ) = ( %s x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) )' % (MB, Mfin))
        fbound = '( %s x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) )' % Mfin
        fb = D(w, A2, 'breqtrd', [D(w, A2, 'eqbrtrd', [glb, gl2], '( abs ` ( %s ` b ) ) <_ ( %s x. ( exp ` ( 2 x. _pi ) ) )' % (GL, MB)), mf], '( abs ` ( %s ` b ) ) <_ %s' % (GL, fbound))
        fbc = D(w, A2, 'ffvelcdmd', [w.s([w.s([l2(glh, HOLt(GL)), w.inst('simpl')], 'syl', '( %s -> %s e. ( CC -cn-> CC ) )' % (A2, GL)), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (A2, GL)), bc2], '( %s ` b ) e. CC' % GL)
        FB = '( abs ` ( %s ` b ) )' % GL
    fbr = D(w, A2, 'remulcld', [D(w, A2, 'rpred', [l2(krp, 'K e. RR+')], 'K e. RR') if R else D(w, A2, 'remulcld', [kK, D(w, A2, 'reefcl' if False else 'rpred' if False else 'x', [], 'x')], 'x') if False else
                                D(w, A2, 'remulcld', [kK, w.s([tpr2, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( 2 x. _pi ) ) e. RR )' % A2)], '%s e. RR' % Mfin), pbr], '%s e. RR' % fbound) if not R else mbr
    gb = D(w, A2, 'eqtrd', [D(w, A2, 'fveq2d', [gv], '( abs ` ( %s ` b ) ) = ( abs ` ( ( %s ` b ) x. ( exp ` ( %s x. b ) ) ) )' % (G, Ft, Aco)),
                            D(w, A2, 'absmuld', [fbc, exc], '( abs ` ( ( %s ` b ) x. ( exp ` ( %s x. b ) ) ) ) = ( %s x. ( abs ` ( exp ` ( %s x. b ) ) ) )' % (Ft, Aco, FB, Aco))],
           '( abs ` ( %s ` b ) ) = ( %s x. ( abs ` ( exp ` ( %s x. b ) ) ) )' % (G, FB, Aco))
    gb2 = D(w, A2, 'lemul12ad', [D(w, A2, 'abscld', [fbc], '%s e. RR' % FB), fbr, D(w, A2, 'abscld', [exc], '( abs ` ( exp ` ( %s x. b ) ) ) e. RR' % Aco), cst(w, A2, '1re', '1 e. RR'),
                                 D(w, A2, 'absge0d', [fbc], '0 <_ %s' % FB), D(w, A2, 'absge0d', [exc], '0 <_ ( abs ` ( exp ` ( %s x. b ) ) )' % Aco), fb, ex1],
            '( %s x. ( abs ` ( exp ` ( %s x. b ) ) ) ) <_ ( %s x. 1 )' % (FB, Aco, fbound))
    gb3 = D(w, A2, 'breqtrd', [D(w, A2, 'eqbrtrd', [gb, gb2], '( abs ` ( %s ` b ) ) <_ ( %s x. 1 )' % (G, fbound)), D(w, A2, 'mulridd', [D(w, A2, 'recnd', [fbr], '%s e. CC' % fbound)], '( %s x. 1 ) = %s' % (fbound, fbound))],
            '( abs ` ( %s ` b ) ) <_ %s' % (G, fbound))
    SHHb = 'A. b e. CC ( ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) -> ( abs ` ( %s ` b ) ) <_ %s )' % (lo, hi, G, fbound.replace('( Im ` b )', '( Im ` b )'))
    sall = w.s([w.s([gb3], 'ex', '( %s -> ( ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) -> ( abs ` ( %s ` b ) ) <_ %s ) )' % (A1, lo, hi, G, fbound))], 'ralrimiva', '( %s -> %s )' % (ph, SHHb))
    mfr = D(w, ph, 'rpred', [krp], 'K e. RR') if R else D(w, ph, 'remulcld', [D(w, ph, 'rpred', [krp], 'K e. RR'), w.s([tpr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( 2 x. _pi ) ) e. RR )' % ph)], '%s e. RR' % Mfin)
    lor = cst(w, ph, '0re', '0 e. RR') if R else cst(w, ph, 'neg1rr', '-u 1 e. RR')
    hir = cst(w, ph, '1re', '1 e. RR') if R else cst(w, ph, '0re', '0 e. RR')
    lthi = cst(w, ph, '0lt1', '0 < 1') if R else cst(w, ph, 'neg1lt0', '-u 1 < 0')
    sh = w.s([D(w, ph, 'jca', [D(w, ph, 'jca', [lor, hir], '( %s e. RR /\\ %s e. RR )' % (lo, hi)), lthi], '( ( %s e. RR /\\ %s e. RR ) /\\ %s < %s )' % (lo, hi, lo, hi)),
              D(w, ph, 'jca', [gh, D(w, ph, 'jca', [mfr, sall], '( %s e. RR /\\ %s )' % (Mfin, SHHb))], '( %s /\\ ( %s e. RR /\\ %s ) )' % (HOLt(G), Mfin, SHHb)), w.inst('zl3shv')], 'syl2anc',
             '( %s -> ( %s = %s /\\ %s e. CC ) )' % (ph, VL(G, hi), VL(G, lo), VL(G, lo)))
    vls = w.s([sh, w.inst('simpl')], 'syl', '( %s -> %s = %s )' % (ph, VL(G, hi), VL(G, lo)))
    other = '1' if R else '-u 1'
    VLo = VL(G, other); VL0 = VL(G, '0')
    ve = vls if R else D(w, ph, 'eqcomd', [vls], '%s = %s' % (VL(G, lo), VL(G, hi)))
    # zl3vl0 at the imaginary axis
    A3 = '( %s /\\ b e. RR )' % ph
    l3 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A3, f))
    bR = w.s([], 'simpr', '( %s -> b e. RR )' % A3)
    z0b = CP('0', 'b')
    zbc = cpcl(w, A3, '0', 'b', cst(w, A3, '0re', '0 e. RR'), bR)
    r0, i0 = reim_cp(w, A3, '0', 'b', cst(w, A3, '0re', '0 e. RR'), bR)
    inr = D(w, A3, 'jca', [D(w, A3, 'eqbrtrrd' if R else 'eqbrtrd', [r0, D(w, A3, 'leidd', [cst(w, A3, '0re', '0 e. RR')], '0 <_ 0')] if False else [], 'x'), None], 'x') if False else None
    lo3 = (D(w, A3, 'eqbrtrrd' if False else 'breqtrrd', [D(w, A3, 'leidd', [cst(w, A3, '0re', '0 e. RR')], '0 <_ 0'), r0], '0 <_ ( Re ` %s )' % z0b) if R else
           D(w, A3, 'breqtrrd', [D(w, A3, 'ltled', [cst(w, A3, 'neg1rr', '-u 1 e. RR'), cst(w, A3, '0re', '0 e. RR'), cst(w, A3, 'neg1lt0', '-u 1 < 0')], '-u 1 <_ 0'), r0], '-u 1 <_ ( Re ` %s )' % z0b))
    hi3 = (D(w, A3, 'eqbrtrd', [r0, D(w, A3, 'ltled', [cst(w, A3, '0re', '0 e. RR'), cst(w, A3, '1re', '1 e. RR'), cst(w, A3, '0lt1', '0 < 1')], '0 <_ 1')], '( Re ` %s ) <_ 1' % z0b) if R else
           D(w, A3, 'eqbrtrd', [r0, D(w, A3, 'leidd', [cst(w, A3, '0re', '0 e. RR')], '0 <_ 0')], '( Re ` %s ) <_ 0' % z0b))
    body = lambda c: '( ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) -> ( abs ` ( %s ` %s ) ) <_ %s )' % (lo, c, c, hi, G, c, fbound.replace('( Im ` b )', '( Im ` %s )' % c))
    Mq = Mfin
    def body_eq(v, X):
        E = '%s = %s' % (v, X)
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        ree = D(w, E, 'fveq2d', [e], '( Re ` %s ) = ( Re ` %s )' % (v, X))
        return D(w, E, 'imbi12d', [D(w, E, 'anbi12d', [D(w, E, 'breq2d', [ree], '( %s <_ ( Re ` %s ) <-> %s <_ ( Re ` %s ) )' % (lo, v, lo, X)), D(w, E, 'breq1d', [ree], '( ( Re ` %s ) <_ %s <-> ( Re ` %s ) <_ %s )' % (v, hi, X, hi))],
                                                   '( ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) <-> ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) )' % (lo, v, v, hi, lo, X, X, hi)),
                                  D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( %s ` %s ) = ( %s ` %s )' % (G, v, G, X))], '( abs ` ( %s ` %s ) ) = ( abs ` ( %s ` %s ) )' % (G, v, G, X)),
                                                      D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Im ` %s ) = ( Im ` %s )' % (v, X))], '( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) )' % (v, X))],
                                                                                                    '-u ( abs ` ( Im ` %s ) ) = -u ( abs ` ( Im ` %s ) )' % (v, X))], '( 2 ^c -u ( abs ` ( Im ` %s ) ) ) = ( 2 ^c -u ( abs ` ( Im ` %s ) ) )' % (v, X))],
                                                        '( %s x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) = ( %s x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % (Mq, v, Mq, X))],
                                    '( ( abs ` ( %s ` %s ) ) <_ %s <-> ( abs ` ( %s ` %s ) ) <_ %s )' % (G, v, fbound.replace('( Im ` b )', '( Im ` %s )' % v), G, X, fbound.replace('( Im ` b )', '( Im ` %s )' % X)))],
                 '( %s <-> %s )' % (body(v), body(X)))
    SHHa = 'A. a e. CC %s' % body('a')
    cbr = w.s([body_eq('b', 'a')], 'cbvralvw', '( %s <-> %s )' % (SHHb, SHHa))
    salla = D(w, ph, 'mpbid', [sall, w.s([cbr], 'a1i', '( %s -> ( %s <-> %s ) )' % (ph, SHHb, SHHa))], SHHa)
    bz0 = w.s([zbc, l3(salla, SHHa), w.s([body_eq('a', z0b)], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (z0b, SHHa, body(z0b)))], 'sylc', '( %s -> %s )' % (A3, body(z0b)))
    bz1 = D(w, A3, 'mpd', [D(w, A3, 'jca', [lo3, hi3], '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s )' % (lo, z0b, z0b, hi)), bz0], '( abs ` ( %s ` %s ) ) <_ %s' % (G, z0b, fbound.replace('( Im ` b )', '( Im ` %s )' % z0b)))
    bz2 = D(w, A3, 'breqtrd', [bz1, D(w, A3, 'oveq2d', [D(w, A3, 'oveq2d', [D(w, A3, 'negeqd', [D(w, A3, 'fveq2d', [i0], '( abs ` ( Im ` %s ) ) = ( abs ` b )' % z0b)], '-u ( abs ` ( Im ` %s ) ) = -u ( abs ` b )' % z0b)],
                                                                 '( 2 ^c -u ( abs ` ( Im ` %s ) ) ) = ( 2 ^c -u ( abs ` b ) )' % z0b)], '%s = ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (fbound.replace('( Im ` b )', '( Im ` %s )' % z0b), Mq))],
            '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (G, z0b, Mq))
    ball = w.s([bz2], 'ralrimiva', '( %s -> A. b e. RR ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) ) )' % (ph, G, z0b, Mq))
    IF = '( t e. RR+ |-> S. ( -u t (,) t ) ( %s ` %s ) _d x )' % (G, CP('0', 'x'))
    v0 = w.s([D(w, ph, 'jca', [gcn, mfr], '( %s e. ( CC -cn-> CC ) /\\ %s e. RR )' % (G, Mq)), ball, w.inst('zl3vl0')], 'syl2anc',
             '( %s -> ( ( %s e. dom ~~>r /\\ ( ~~>r ` %s ) e. CC ) /\\ %s = ( _i x. ( ~~>r ` %s ) ) ) )' % (ph, IF, IF, VL0, IF))
    ifcc = w.s([w.s([v0, w.inst('simpl')], 'syl', '( %s -> ( %s e. dom ~~>r /\\ ( ~~>r ` %s ) e. CC ) )' % (ph, IF, IF)), w.inst('simpr')], 'syl', '( %s -> ( ~~>r ` %s ) e. CC )' % (ph, IF))
    v0e = w.s([v0, w.inst('simpr')], 'syl', '( %s -> %s = ( _i x. ( ~~>r ` %s ) ) )' % (ph, VL0, IF))
    # the integrand on the imaginary axis equals the Fourier kernel
    NK = 'k' if R else '( 1 - k )'
    INT = '( ( H ` ( _i x. x ) ) x. ( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. x ) ) ) )' % NK
    A4 = '( ( %s /\\ t e. RR+ ) /\\ x e. ( -u t (,) t ) )' % ph
    l4 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (A4, f))
    xr = w.s([w.s([], 'simpr', '( %s -> x e. ( -u t (,) t ) )' % A4), w.inst('elioore')], 'syl', '( %s -> x e. RR )' % A4)
    xc = D(w, A4, 'recnd', [xr], 'x e. CC')
    ic = cst(w, A4, 'ax-icn', '_i e. CC')
    ixc = D(w, A4, 'mulcld', [ic, xc], '( _i x. x ) e. CC')
    zx = D(w, A4, 'addlidd', [ixc], '%s = ( _i x. x )' % CP('0', 'x'))
    zxc = cpcl(w, A4, '0', 'x', cst(w, A4, '0re', '0 e. RR'), xr)
    gzx = fv_expmul(w, A4, Ft, Aco, 'y', CP('0', 'x'), zxc)
    gzx2 = D(w, A4, 'eqtrd', [gzx, D(w, A4, 'oveq12d', [D(w, A4, 'fveq2d', [zx], '( %s ` %s ) = ( %s ` ( _i x. x ) )' % (Ft, CP('0', 'x'), Ft)),
                                                        D(w, A4, 'fveq2d', [D(w, A4, 'oveq2d', [zx], '( %s x. %s ) = ( %s x. ( _i x. x ) )' % (Aco, CP('0', 'x'), Aco))], '( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. ( _i x. x ) ) )' % (Aco, CP('0', 'x'), Aco))],
                                        '( ( %s ` %s ) x. ( exp ` ( %s x. %s ) ) ) = ( ( %s ` ( _i x. x ) ) x. ( exp ` ( %s x. ( _i x. x ) ) ) )' % (Ft, CP('0', 'x'), Aco, CP('0', 'x'), Ft, Aco))],
               '( %s ` %s ) = ( ( %s ` ( _i x. x ) ) x. ( exp ` ( %s x. ( _i x. x ) ) ) )' % (G, CP('0', 'x'), Ft, Aco))
    kc4 = l4(kc, 'k e. CC'); tpc4 = l4(tpc, '( 2 x. _pi ) e. CC'); pc4 = cst(w, A4, 'picn', '_pi e. CC'); c24 = cst(w, A4, '2cn', '2 e. CC')
    TIP = '( 2 x. ( _i x. _pi ) )'
    # ( i x. ( 2 x. _pi ) ) = TIP
    itp = D(w, A4, 'eqcomd', [D(w, A4, 'mul12d', [c24, ic, pc4], '%s = ( _i x. ( 2 x. _pi ) )' % TIP)], '( _i x. ( 2 x. _pi ) ) = %s' % TIP)
    def ring(coef_expr, coef_sign, N_expr):
        """( A4 -> ( ( coef_expr ) x. ( _i x. x ) ) = -u ( TIP x. ( N_expr x. x ) ) ) for coef = ( k x. -u 2pi ) (N=k)"""
        pass
    if R:
        # ( k x. -u 2pi ) ( i x ) = -u ( ( k x. 2pi ) ( i x ) ) ; ( k 2pi ) ( i x ) = TIP ( k x )
        s1 = D(w, A4, 'oveq1d', [D(w, A4, 'mulneg2d', [kc4, tpc4], '( k x. %s ) = -u ( k x. ( 2 x. _pi ) )' % ntp)], '( %s x. ( _i x. x ) ) = ( -u ( k x. ( 2 x. _pi ) ) x. ( _i x. x ) )' % Aco)
        s2 = D(w, A4, 'mulneg1d', [D(w, A4, 'mulcld', [kc4, tpc4], '( k x. ( 2 x. _pi ) ) e. CC'), ixc], '( -u ( k x. ( 2 x. _pi ) ) x. ( _i x. x ) ) = -u ( ( k x. ( 2 x. _pi ) ) x. ( _i x. x ) )')
        P = '( ( k x. ( 2 x. _pi ) ) x. ( _i x. x ) )'
        N_ = 'k'; nc4 = kc4
    else:
        # ( k 2pi ) ( i x ) + ( -2pi ) ( i x ) = ( ( k - 1 ) 2pi ) ( i x ) = -u ( TIP ( ( 1 - k ) x ) )
        pass
    # common: ( c x. ( 2 x. _pi ) ) x. ( _i x. x ) = TIP x. ( c x. x ) for c complex
    def core(c, cc):
        t1 = D(w, A4, 'mulassd', [cc, tpc4, ixc], '( ( %s x. ( 2 x. _pi ) ) x. ( _i x. x ) ) = ( %s x. ( ( 2 x. _pi ) x. ( _i x. x ) ) )' % (c, c))
        t2 = D(w, A4, 'mul12d', [tpc4, ic, xc], '( ( 2 x. _pi ) x. ( _i x. x ) ) = ( _i x. ( ( 2 x. _pi ) x. x ) )')
        t3 = D(w, A4, 'oveq2d', [t2], '( %s x. ( ( 2 x. _pi ) x. ( _i x. x ) ) ) = ( %s x. ( _i x. ( ( 2 x. _pi ) x. x ) ) )' % (c, c))
        tpx = D(w, A4, 'mulcld', [tpc4, xc], '( ( 2 x. _pi ) x. x ) e. CC')
        t4 = D(w, A4, 'mul12d', [cc, ic, tpx], '( %s x. ( _i x. ( ( 2 x. _pi ) x. x ) ) ) = ( _i x. ( %s x. ( ( 2 x. _pi ) x. x ) ) )' % (c, c))
        t5 = D(w, A4, 'mul12d', [cc, tpc4, xc], '( %s x. ( ( 2 x. _pi ) x. x ) ) = ( ( 2 x. _pi ) x. ( %s x. x ) )' % (c, c))
        t6 = D(w, A4, 'oveq2d', [t5], '( _i x. ( %s x. ( ( 2 x. _pi ) x. x ) ) ) = ( _i x. ( ( 2 x. _pi ) x. ( %s x. x ) ) )' % (c, c))
        cx = D(w, A4, 'mulcld', [cc, xc], '( %s x. x ) e. CC' % c)
        t7 = D(w, A4, 'eqcomd', [D(w, A4, 'mulassd', [ic, tpc4, cx], '( ( _i x. ( 2 x. _pi ) ) x. ( %s x. x ) ) = ( _i x. ( ( 2 x. _pi ) x. ( %s x. x ) ) )' % (c, c))],
                '( _i x. ( ( 2 x. _pi ) x. ( %s x. x ) ) ) = ( ( _i x. ( 2 x. _pi ) ) x. ( %s x. x ) )' % (c, c))
        t8 = D(w, A4, 'oveq1d', [itp], '( ( _i x. ( 2 x. _pi ) ) x. ( %s x. x ) ) = ( %s x. ( %s x. x ) )' % (c, TIP, c))
        return chain_eq(w, A4, '( ( %s x. ( 2 x. _pi ) ) x. ( _i x. x ) )' % c,
                        [(t1, '( %s x. ( ( 2 x. _pi ) x. ( _i x. x ) ) )' % c), (t3, '( %s x. ( _i x. ( ( 2 x. _pi ) x. x ) ) )' % c), (t4, '( _i x. ( %s x. ( ( 2 x. _pi ) x. x ) ) )' % c),
                         (t6, '( _i x. ( ( 2 x. _pi ) x. ( %s x. x ) ) )' % c), (t7, '( ( _i x. ( 2 x. _pi ) ) x. ( %s x. x ) )' % c), (t8, '( %s x. ( %s x. x ) )' % (TIP, c))])
    if R:
        cr_ = core('k', kc4)
        arg_eq = chain_eq(w, A4, '( %s x. ( _i x. x ) )' % Aco, [(s1, '( -u ( k x. ( 2 x. _pi ) ) x. ( _i x. x ) )'), (s2, '-u %s' % P), (D(w, A4, 'negeqd', [cr_], '-u %s = -u ( %s x. ( k x. x ) )' % (P, TIP)), '-u ( %s x. ( k x. x ) )' % TIP)])
        val = D(w, A4, 'eqtrd', [gzx2, D(w, A4, 'oveq2d', [D(w, A4, 'fveq2d', [arg_eq], '( exp ` ( %s x. ( _i x. x ) ) ) = ( exp ` -u ( %s x. ( k x. x ) ) )' % (Aco, TIP))],
                                                        '( ( H ` ( _i x. x ) ) x. ( exp ` ( %s x. ( _i x. x ) ) ) ) = %s' % (Aco, INT))], '( %s ` %s ) = %s' % (G, CP('0', 'x'), INT))
    else:
        # GL ( i x ) = H ( i x ) exp ( -2pi ( i x ) )
        glx = fv_expmul(w, A4, 'H', ntp, 'w', '( _i x. x )', ixc)
        a1_ = '( %s x. ( _i x. x ) )' % ntp; a2_ = '( %s x. ( _i x. x ) )' % Aco
        a1c = D(w, A4, 'mulcld', [l4(ntpc, '%s e. CC' % ntp), ixc], '%s e. CC' % a1_); a2c = D(w, A4, 'mulcld', [l4(acc, '%s e. CC' % Aco), ixc], '%s e. CC' % a2_)
        hxc = D(w, A4, 'ffvelcdmd', [w.s([w.s([l4(hent, HENT), w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % A4), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % A4), ixc], '( H ` ( _i x. x ) ) e. CC')
        u1 = D(w, A4, 'oveq1d', [glx], '( ( %s ` ( _i x. x ) ) x. ( exp ` %s ) ) = ( ( ( H ` ( _i x. x ) ) x. ( exp ` %s ) ) x. ( exp ` %s ) )' % (GL, a2_, a1_, a2_))
        u2 = D(w, A4, 'mulassd', [hxc, D(w, A4, 'efcld', [a1c], '( exp ` %s ) e. CC' % a1_), D(w, A4, 'efcld', [a2c], '( exp ` %s ) e. CC' % a2_)],
               '( ( ( H ` ( _i x. x ) ) x. ( exp ` %s ) ) x. ( exp ` %s ) ) = ( ( H ` ( _i x. x ) ) x. ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (a1_, a2_, a1_, a2_))
        u3 = D(w, A4, 'eqcomd', [w.s([a1c, a2c, w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (A4, a1_, a2_, a1_, a2_))],
               '( ( exp ` %s ) x. ( exp ` %s ) ) = ( exp ` ( %s + %s ) )' % (a1_, a2_, a1_, a2_))
        # a1 + a2 = ( ( k - 1 ) x. ( 2 x. _pi ) ) ( i x ) = -u ( TIP x. ( ( 1 - k ) x. x ) )
        km1 = '( k - 1 )'
        km1c = D(w, A4, 'subcld', [kc4, cst(w, A4, 'ax-1cn', '1 e. CC')], '%s e. CC' % km1)
        v1 = D(w, A4, 'eqcomd', [D(w, A4, 'adddird' if False else 'adddirp1d' if False else 'x', [], 'x')], 'x') if False else None
        # ( -2pi ) = ( -u 1 x. 2pi ); a1 + a2 = ( ( -u 1 x. 2pi ) + ( k x. 2pi ) ) ( i x ) = ( ( -u 1 + k ) 2pi ) ( i x )
        v1 = D(w, A4, 'eqcomd', [D(w, A4, 'mulm1d', [tpc4], '( -u 1 x. ( 2 x. _pi ) ) = %s' % ntp)], '%s = ( -u 1 x. ( 2 x. _pi ) )' % ntp)
        v2 = D(w, A4, 'adddird', [l4(ntpc, '%s e. CC' % ntp), l4(acc, '%s e. CC' % Aco), ixc], '( ( %s + %s ) x. ( _i x. x ) ) = ( %s + %s )' % (ntp, Aco, a1_, a2_))
        n1 = cst(w, A4, 'neg1cn', '-u 1 e. CC')
        v3 = D(w, A4, 'eqtrd', [D(w, A4, 'oveq1d', [v1], '( %s + %s ) = ( ( -u 1 x. ( 2 x. _pi ) ) + %s )' % (ntp, Aco, Aco)),
                                D(w, A4, 'eqcomd', [D(w, A4, 'adddird', [n1, kc4, tpc4], '( ( -u 1 + k ) x. ( 2 x. _pi ) ) = ( ( -u 1 x. ( 2 x. _pi ) ) + %s )' % Aco)], '( ( -u 1 x. ( 2 x. _pi ) ) + %s ) = ( ( -u 1 + k ) x. ( 2 x. _pi ) )' % Aco)],
                '( %s + %s ) = ( ( -u 1 + k ) x. ( 2 x. _pi ) )' % (ntp, Aco))
        v4 = D(w, A4, 'eqtrd', [D(w, A4, 'addcomd', [n1, kc4], '( -u 1 + k ) = ( k + -u 1 )'), D(w, A4, 'negsubd', [kc4, cst(w, A4, 'ax-1cn', '1 e. CC')], '( k + -u 1 ) = ( k - 1 )')], '( -u 1 + k ) = ( k - 1 )')
        v5 = D(w, A4, 'eqtrd', [v3, D(w, A4, 'oveq1d', [v4], '( ( -u 1 + k ) x. ( 2 x. _pi ) ) = ( %s x. ( 2 x. _pi ) )' % km1)], '( %s + %s ) = ( %s x. ( 2 x. _pi ) )' % (ntp, Aco, km1))
        v6 = D(w, A4, 'eqtr3d', [v2, D(w, A4, 'oveq1d', [v5], '( ( %s + %s ) x. ( _i x. x ) ) = ( ( %s x. ( 2 x. _pi ) ) x. ( _i x. x ) )' % (ntp, Aco, km1))], '( %s + %s ) = ( ( %s x. ( 2 x. _pi ) ) x. ( _i x. x ) )' % (a1_, a2_, km1))
        cr_ = core(km1, km1c)
        omk = '( 1 - k )'
        v7 = D(w, A4, 'negsubdi2d', [kc4, cst(w, A4, 'ax-1cn', '1 e. CC')], '-u %s = %s' % (km1, omk))
        v8 = D(w, A4, 'eqtrd', [D(w, A4, 'oveq1d', [D(w, A4, 'eqcomd', [v7], '%s = -u %s' % (omk, km1))], '( %s x. x ) = ( -u %s x. x )' % (omk, km1)), D(w, A4, 'mulneg1d', [km1c, xc], '( -u %s x. x ) = -u ( %s x. x )' % (km1, km1))],
                '( %s x. x ) = -u ( %s x. x )' % (omk, km1))
        tipc = D(w, A4, 'mulcld', [c24, D(w, A4, 'mulcld', [ic, pc4], '( _i x. _pi ) e. CC')], '%s e. CC' % TIP)
        v9 = D(w, A4, 'eqtrd', [D(w, A4, 'oveq2d', [v8], '( %s x. ( %s x. x ) ) = ( %s x. -u ( %s x. x ) )' % (TIP, omk, TIP, km1)), D(w, A4, 'mulneg2d', [tipc, D(w, A4, 'mulcld', [km1c, xc], '( %s x. x ) e. CC' % km1)],
                                                                                                                                                   '( %s x. -u ( %s x. x ) ) = -u ( %s x. ( %s x. x ) )' % (TIP, km1, TIP, km1))],
                '( %s x. ( %s x. x ) ) = -u ( %s x. ( %s x. x ) )' % (TIP, omk, TIP, km1))
        v10 = D(w, A4, 'eqtr4d', [D(w, A4, 'eqtrd', [v6, cr_], '( %s + %s ) = ( %s x. ( %s x. x ) )' % (a1_, a2_, TIP, km1)),
                                  D(w, A4, 'eqtrd', [D(w, A4, 'negeqd', [v9], '-u ( %s x. ( %s x. x ) ) = -u -u ( %s x. ( %s x. x ) )' % (TIP, omk, TIP, km1)),
                                                     D(w, A4, 'negnegd', [D(w, A4, 'mulcld', [tipc, D(w, A4, 'mulcld', [km1c, xc], '( %s x. x ) e. CC' % km1)], '( %s x. ( %s x. x ) ) e. CC' % (TIP, km1))], '-u -u ( %s x. ( %s x. x ) ) = ( %s x. ( %s x. x ) )' % (TIP, km1, TIP, km1))],
                                    '-u ( %s x. ( %s x. x ) ) = ( %s x. ( %s x. x ) )' % (TIP, omk, TIP, km1))], '( %s + %s ) = -u ( %s x. ( %s x. x ) )' % (a1_, a2_, TIP, omk))
        u4 = D(w, A4, 'fveq2d', [v10], '( exp ` ( %s + %s ) ) = ( exp ` -u ( %s x. ( %s x. x ) ) )' % (a1_, a2_, TIP, omk))
        val0 = chain_eq(w, A4, '( ( %s ` ( _i x. x ) ) x. ( exp ` %s ) )' % (GL, a2_),
                        [(u1, '( ( ( H ` ( _i x. x ) ) x. ( exp ` %s ) ) x. ( exp ` %s ) )' % (a1_, a2_)), (u2, '( ( H ` ( _i x. x ) ) x. ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (a1_, a2_)),
                         (D(w, A4, 'oveq2d', [D(w, A4, 'eqtrd', [u3, u4], '( ( exp ` %s ) x. ( exp ` %s ) ) = ( exp ` -u ( %s x. ( %s x. x ) ) )' % (a1_, a2_, TIP, omk))],
                            '( ( H ` ( _i x. x ) ) x. ( ( exp ` %s ) x. ( exp ` %s ) ) ) = %s' % (a1_, a2_, INT)), INT)])
        val = D(w, A4, 'eqtrd', [gzx2, val0], '( %s ` %s ) = %s' % (G, CP('0', 'x'), INT))
    ieq = w.s([val], 'itgeq2dv', '( ( %s /\\ t e. RR+ ) -> S. ( -u t (,) t ) ( %s ` %s ) _d x = S. ( -u t (,) t ) %s _d x )' % (ph, G, CP('0', 'x'), INT))
    INTF = '( t e. RR+ |-> S. ( -u t (,) t ) %s _d x )' % INT
    meq = w.s([ieq], 'mpteq2dva', '( %s -> %s = %s )' % (ph, IF, INTF))
    lv = D(w, ph, 'fveq2d', [meq], '( ~~>r ` %s ) = ( ~~>r ` %s )' % (IF, INTF))
    # HT at NK
    if R:
        htv = w.s([D(w, ph, 'nnzd', [kN], 'k e. ZZ'), w.s([w.s([], 'fvex', '( ~~>r ` %s ) e. _V' % INTF)], 'a1i', '( %s -> ( ~~>r ` %s ) e. _V )' % (ph, INTF)),
                   w.s([w.s([], 'eqid', '%s = %s' % (HT, HT))], 'fvmpt2', '( ( k e. ZZ /\\ ( ~~>r ` %s ) e. _V ) -> ( %s ` k ) = ( ~~>r ` %s ) )' % (INTF, HT, INTF))], 'syl2anc',
                  '( %s -> ( %s ` k ) = ( ~~>r ` %s ) )' % (ph, HT, INTF))
    else:
        HTj = HT.replace('( k e. ZZ |->', '( j e. ZZ |->').replace('( k x. x )', '( j x. x )')
        INTj = lambda c: '( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. x ) ) ) ) _d x ) )' % c
        Ekj = 'k = j'
        # body(k) = body(j)
        def bsub(E, a, b_):
            A5 = '( %s /\\ t e. RR+ )' % E
            A6 = '( %s /\\ x e. ( -u t (,) t ) )' % A5
            ee = w.s([w.s([], 'id', '( %s -> %s )' % (E, E))], 'ad2antrr', '( %s -> %s )' % (A6, E))
            inner = D(w, A6, 'oveq2d', [D(w, A6, 'fveq2d', [D(w, A6, 'negeqd', [D(w, A6, 'oveq2d', [D(w, A6, 'oveq1d', [ee], '( %s x. x ) = ( %s x. x )' % (a, b_))],
                                                                                                 '( %s x. ( %s x. x ) ) = ( %s x. ( %s x. x ) )' % (TIP, a, TIP, b_))],
                                                                              '-u ( %s x. ( %s x. x ) ) = -u ( %s x. ( %s x. x ) )' % (TIP, a, TIP, b_))],
                                                          '( exp ` -u ( %s x. ( %s x. x ) ) ) = ( exp ` -u ( %s x. ( %s x. x ) ) )' % (TIP, a, TIP, b_))],
                        '( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) = ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) )' % (TIP, a, TIP, b_))
            ig = w.s([inner], 'itgeq2dv', '( %s -> S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x = S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x )' % (A5, TIP, a, TIP, b_))
            mq = w.s([ig], 'mpteq2dva', '( %s -> ( t e. RR+ |-> S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x ) = ( t e. RR+ |-> S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x ) )' % (E, TIP, a, TIP, b_))
            return D(w, E, 'fveq2d', [mq], '%s = %s' % (INTj(a), INTj(b_)))
        cbh = w.s([bsub(Ekj, 'k', 'j')], 'cbvmptv', '%s = %s' % (HT, HTj))
        Ej1 = 'j = ( 1 - k )'
        fj = w.s([bsub(Ej1, 'j', '( 1 - k )'), w.s([], 'eqid', '%s = %s' % (HTj, HTj)), w.s([], 'fvex', '%s e. _V' % INTj('( 1 - k )'))], 'fvmpt', '( ( 1 - k ) e. ZZ -> ( %s ` ( 1 - k ) ) = %s )' % (HTj, INTj('( 1 - k )')))
        omz = w.s([cst(w, ph, '1z', '1 e. ZZ'), D(w, ph, 'nnzd', [kN], 'k e. ZZ'), w.inst('zsubcl')], 'syl2anc', '( %s -> ( 1 - k ) e. ZZ )' % ph)
        htv = D(w, ph, 'eqtrd', [D(w, ph, 'fveq1d', [w.s([cbh], 'a1i', '( %s -> %s = %s )' % (ph, HT, HTj))], '( %s ` ( 1 - k ) ) = ( %s ` ( 1 - k ) )' % (HT, HTj)), w.s([omz, fj], 'syl', '( %s -> ( %s ` ( 1 - k ) ) = %s )' % (ph, HTj, INTj('( 1 - k )')))],
                '( %s ` ( 1 - k ) ) = %s' % (HT, INTj('( 1 - k )')))
    v1_ = D(w, ph, 'eqtrd', [v0e, D(w, ph, 'oveq2d', [D(w, ph, 'eqtr4d', [lv, htv], '( ~~>r ` %s ) = ( %s ` %s )' % (IF, HT, NK))], '( _i x. ( ~~>r ` %s ) ) = ( _i x. ( %s ` %s ) )' % (IF, HT, NK))],
            '%s = ( _i x. ( %s ` %s ) )' % (VL0, HT, NK))
    vloc = w.s([sh, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (ph, VL(G, lo)))
    voc = vloc if not R else D(w, ph, 'eqeltrd', [vls, vloc], '%s e. CC' % VL(G, hi))
    htc_ = D(w, ph, 'eqeltrrd', [D(w, ph, 'eqtr4d', [lv, htv], '( ~~>r ` %s ) = ( %s ` %s )' % (IF, HT, NK)), ifcc], '( %s ` %s ) e. CC' % (HT, NK))
    w.qed([D(w, ph, 'jca', [ve, voc], '( %s = %s /\\ %s e. CC )' % (VLo, VL0, VLo)), D(w, ph, 'jca', [v1_, htc_], '( %s = ( _i x. ( %s ` %s ) ) /\\ ( %s ` %s ) e. CC )' % (VL0, HT, NK, HT, NK))], 'jca', S[lab])
    go(w, only)


if __name__ == '__main__' and (not only or 'zl3gkr' in only):
    gk_lemma('R')
if __name__ == '__main__' and (not only or 'zl3gkl' in only):
    gk_lemma('L')


# ---------------------------------------------------------------- zl3lrn
if __name__ == '__main__' and (not only or 'zl3lrn' in only):
    w = W('zl3lrn', 'Reversing a segment and negating the integrand leaves the line integral unchanged.')
    ph, concl = ante_of(S['zl3lrn'])
    L = '( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )'
    R_ = '( G e. V /\\ A. b e. ( A cseg B ) ( G ` b ) = -u ( F ` b ) )'
    l = w.s([], 'simpl', '( %s -> %s )' % (ph, L)); r = w.s([], 'simpr', '( %s -> %s )' % (ph, R_))
    fcn = w.s([l, w.inst('simprl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % ph)
    sd = w.s([l, w.inst('simprr')], 'syl', '( %s -> ( A cseg B ) C_ D )' % ph)
    ab = w.s([l, w.inst('simpl')], 'syl', '( %s -> ( A e. CC /\\ B e. CC ) )' % ph)
    rev = w.s([l, w.inst('lintrev')], 'syl', '( %s -> ( F lint <. B , A >. ) = -u ( F lint <. A , B >. ) )' % ph)
    m1 = cst(w, ph, 'neg1cn', '-u 1 e. CC')
    OF = '( ( D X. { -u 1 } ) oF x. F )'
    lm = w.s([l, m1, w.inst('lintmulc')], 'syl2anc', '( %s -> ( %s lint <. A , B >. ) = ( -u 1 x. ( F lint <. A , B >. ) ) )' % (ph, OF))
    ltc = w.s([l, w.inst('lintcl')], 'syl', '( %s -> ( F lint <. A , B >. ) e. CC )' % ph)
    lm2 = D(w, ph, 'eqtrd', [lm, D(w, ph, 'mulm1d', [ltc], '( -u 1 x. ( F lint <. A , B >. ) ) = -u ( F lint <. A , B >. )')], '( %s lint <. A , B >. ) = -u ( F lint <. A , B >. )' % OF)
    # pointwise: OF ` z = G ` z on the segment
    A1 = '( %s /\\ z e. ( A cseg B ) )' % ph
    zin = w.s([], 'simpr', '( %s -> z e. ( A cseg B ) )' % A1)
    bD = D(w, A1, 'sseldd', [w.s([sd], 'adantr', '( %s -> ( A cseg B ) C_ D )' % A1), zin], 'z e. D')
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % ph)
    dv = w.s([dcc, cst(w, ph, 'cnex', 'CC e. _V'), w.inst('ssexg')], 'syl2anc', '( %s -> D e. _V )' % ph)
    ffn = w.s([w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % ph), w.inst('ffn')], 'syl', '( %s -> F Fn D )' % ph)
    P2 = '( %s /\\ z e. D )' % ph
    oc = w.s([dv, m1, ffn, D(w, P2, 'eqidd', [], '( F ` z ) = ( F ` z )')], 'ofc1', '( %s -> ( %s ` z ) = ( -u 1 x. ( F ` z ) ) )' % (P2, OF))
    oc1 = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ph)), bD, oc], 'syl2anc', '( %s -> ( %s ` z ) = ( -u 1 x. ( F ` z ) ) )' % (A1, OF))
    fbc = D(w, A1, 'ffvelcdmd', [w.s([w.s([fcn], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % A1), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A1), bD], '( F ` z ) e. CC')
    oc2 = D(w, A1, 'eqtrd', [oc1, D(w, A1, 'mulm1d', [fbc], '( -u 1 x. ( F ` z ) ) = -u ( F ` z )')], '( %s ` z ) = -u ( F ` z )' % OF)
    beq = w.s([w.s([], 'fveq2', '( b = z -> ( G ` b ) = ( G ` z ) )'), w.s([w.s([], 'fveq2', '( b = z -> ( F ` b ) = ( F ` z ) )')], 'negeqd', '( b = z -> -u ( F ` b ) = -u ( F ` z ) )')], 'eqeq12d',
              '( b = z -> ( ( G ` b ) = -u ( F ` b ) <-> ( G ` z ) = -u ( F ` z ) ) )')
    gb = w.s([zin, w.s([w.s([r, w.inst('simpr')], 'syl', '( %s -> A. b e. ( A cseg B ) ( G ` b ) = -u ( F ` b ) )' % ph)], 'adantr', '( %s -> A. b e. ( A cseg B ) ( G ` b ) = -u ( F ` b ) )' % A1),
              w.s([beq], 'rspcv', '( z e. ( A cseg B ) -> ( A. b e. ( A cseg B ) ( G ` b ) = -u ( F ` b ) -> ( G ` z ) = -u ( F ` z ) ) )')], 'sylc', '( %s -> ( G ` z ) = -u ( F ` z ) )' % A1)
    eqb = D(w, A1, 'eqtr4d', [oc2, gb], '( %s ` z ) = ( G ` z )' % OF)
    ofv = w.s([w.s([], 'ovex', '%s e. _V' % OF)], 'a1i', '( %s -> %s e. _V )' % (ph, OF))
    gv = w.s([w.s([r, w.inst('simpl')], 'syl', '( %s -> G e. V )' % ph), w.inst('elex')], 'syl', '( %s -> G e. _V )' % ph)
    allz = w.s([eqb], 'ralrimiva', '( %s -> A. z e. ( A cseg B ) ( %s ` z ) = ( G ` z ) )' % (ph, OF))
    le = w.s([D(w, ph, 'jca', [ab, D(w, ph, 'jca', [ofv, gv], '( %s e. _V /\\ G e. _V )' % OF)], '( ( A e. CC /\\ B e. CC ) /\\ ( %s e. _V /\\ G e. _V ) )' % OF), allz, w.inst('linteq')], 'syl2anc',
             '( %s -> ( %s lint <. A , B >. ) = ( G lint <. A , B >. ) )' % (ph, OF))
    w.qed([rev, D(w, ph, 'eqtr3d', [lm2, le], '-u ( F lint <. A , B >. ) = ( G lint <. A , B >. )')], 'eqtrd', S['zl3lrn'])
    go(w, only)


# ---------------------------------------------------------------- zl3fzs
def SUMH(lo, hi):
    return 'sum_ n e. ( %s ... %s ) ( H ` ( _i x. n ) )' % (lo, hi)


PAIR = '( ( H ` ( _i x. n ) ) + ( H ` ( _i x. -u n ) ) )'


def SUMP(hi):
    return 'sum_ n e. ( 1 ... %s ) %s' % (hi, PAIR)


if __name__ == '__main__' and (not only or 'zl3fzs' in only):
    w = W('zl3fzs', 'A symmetric finite sum over ` -u N ... N ` is the central term plus the sum of the pairs ` n `, ` -u n `.')
    ph, concl = ante_of(S['zl3fzs'])
    HF = 'H : CC --> CC'
    EQ = lambda T: '%s = ( ( H ` ( _i x. 0 ) ) + %s )' % (SUMH('-u %s' % T, T), SUMP(T))
    PK = lambda T: '( %s -> %s )' % (HF, EQ(T))
    def subst(T):
        E = 'k = %s' % T
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        fz = D(w, E, 'oveq12d', [D(w, E, 'negeqd', [e], '-u k = -u %s' % T), e], '( -u k ... k ) = ( -u %s ... %s )' % (T, T))
        l = D(w, E, 'sumeq1d', [fz], '%s = %s' % (SUMH('-u k', 'k'), SUMH('-u %s' % T, T)))
        r = D(w, E, 'oveq2d', [D(w, E, 'sumeq1d', [D(w, E, 'oveq2d', [e], '( 1 ... k ) = ( 1 ... %s )' % T)], '%s = %s' % (SUMP('k'), SUMP(T)))],
              '( ( H ` ( _i x. 0 ) ) + %s ) = ( ( H ` ( _i x. 0 ) ) + %s )' % (SUMP('k'), SUMP(T)))
        return D(w, E, 'imbi2d', [D(w, E, 'eqeq12d', [l, r], '( %s <-> %s )' % (EQ('k'), EQ(T)))], '( %s <-> %s )' % (PK('k'), PK(T)))
    h1 = subst('0'); h2 = subst('m'); h3 = subst('( m + 1 )'); h4 = subst('N')
    # base
    B0 = HF
    i0c = D(w, B0, 'mulcld', [cst(w, B0, 'ax-icn', '_i e. CC'), cst(w, B0, '0cn', '0 e. CC')], '( _i x. 0 ) e. CC')
    h0c = D(w, B0, 'ffvelcdmd', [w.s([], 'id', '( %s -> %s )' % (B0, B0)), i0c], '( H ` ( _i x. 0 ) ) e. CC')
    fz0 = D(w, B0, 'eqtrd', [D(w, B0, 'oveq1d', [cst(w, B0, 'neg0', '-u 0 = 0')], '( -u 0 ... 0 ) = ( 0 ... 0 )'), w.s([cst(w, B0, '0z', '0 e. ZZ'), w.inst('fzsn')], 'syl', '( %s -> ( 0 ... 0 ) = { 0 } )' % B0)],
            '( -u 0 ... 0 ) = { 0 }')
    ssn = w.s([cst(w, B0, 'c0ex', '0 e. _V'), h0c, w.s([w.s([w.s([], 'oveq2', '( n = 0 -> ( _i x. n ) = ( _i x. 0 ) )')], 'fveq2d', '( n = 0 -> ( H ` ( _i x. n ) ) = ( H ` ( _i x. 0 ) ) )')], 'sumsn',
                                                                           '( ( 0 e. _V /\\ ( H ` ( _i x. 0 ) ) e. CC ) -> sum_ n e. { 0 } ( H ` ( _i x. n ) ) = ( H ` ( _i x. 0 ) ) )')], 'syl2anc',
              '( %s -> sum_ n e. { 0 } ( H ` ( _i x. n ) ) = ( H ` ( _i x. 0 ) ) )' % B0)
    l0 = D(w, B0, 'eqtrd', [D(w, B0, 'sumeq1d', [fz0], '%s = sum_ n e. { 0 } ( H ` ( _i x. n ) )' % SUMH('-u 0', '0')), ssn], '%s = ( H ` ( _i x. 0 ) )' % SUMH('-u 0', '0'))
    r0 = D(w, B0, 'eqtrd', [D(w, B0, 'oveq2d', [D(w, B0, 'eqtrd', [D(w, B0, 'sumeq1d', [cst(w, B0, 'fz10', '( 1 ... 0 ) = (/)')], '%s = sum_ n e. (/) %s' % (SUMP('0'), PAIR)), cst(w, B0, 'sum0', 'sum_ n e. (/) %s = 0' % PAIR)],
                                                  '%s = 0' % SUMP('0'))], '( ( H ` ( _i x. 0 ) ) + %s ) = ( ( H ` ( _i x. 0 ) ) + 0 )' % SUMP('0')), D(w, B0, 'addridd', [h0c], '( ( H ` ( _i x. 0 ) ) + 0 ) = ( H ` ( _i x. 0 ) )')],
            '( ( H ` ( _i x. 0 ) ) + %s ) = ( H ` ( _i x. 0 ) )' % SUMP('0'))
    base = D(w, B0, 'eqtr4d', [l0, r0], EQ('0'))
    # step
    A = '( m e. NN0 /\\ %s )' % HF
    m0 = w.s([], 'simpl', '( %s -> m e. NN0 )' % A); hf = w.s([], 'simpr', '( %s -> %s )' % (A, HF))
    mz = D(w, A, 'nn0zd', [m0], 'm e. ZZ'); mr = D(w, A, 'nn0red', [m0], 'm e. RR'); mc = D(w, A, 'nn0cnd', [m0], 'm e. CC')
    one = cst(w, A, 'ax-1cn', '1 e. CC')
    m1 = '( m + 1 )'
    m1z = D(w, A, 'peano2zd', [mz], '%s e. ZZ' % m1); m1r = D(w, A, 'zred', [m1z], '%s e. RR' % m1); m1c = D(w, A, 'zcnd', [m1z], '%s e. CC' % m1)
    X_ = '-u %s' % m1; nm = '-u m'
    x_z = D(w, A, 'znegcld', [m1z], '%s e. ZZ' % X_); x_r = D(w, A, 'zred', [x_z], '%s e. RR' % X_); x_c = D(w, A, 'zcnd', [x_z], '%s e. CC' % X_)
    nmz = D(w, A, 'znegcld', [mz], '%s e. ZZ' % nm); nmr = D(w, A, 'zred', [nmz], '%s e. RR' % nm)
    def hval(lo, hi, neg=False):
        Bq = '( %s /\\ n e. ( %s ... %s ) )' % (A, lo, hi)
        nz_ = w.s([w.s([], 'simpr', '( %s -> n e. ( %s ... %s ) )' % (Bq, lo, hi)), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % Bq)
        nc_ = D(w, Bq, 'zcnd', [nz_], 'n e. CC')
        ic = cst(w, Bq, 'ax-icn', '_i e. CC')
        hb = w.s([hf], 'adantr', '( %s -> %s )' % (Bq, HF))
        a = D(w, Bq, 'ffvelcdmd', [hb, D(w, Bq, 'mulcld', [ic, nc_], '( _i x. n ) e. CC')], '( H ` ( _i x. n ) ) e. CC')
        if not neg:
            return a
        b = D(w, Bq, 'ffvelcdmd', [hb, D(w, Bq, 'mulcld', [ic, D(w, Bq, 'negcld', [nc_], '-u n e. CC')], '( _i x. -u n ) e. CC')], '( H ` ( _i x. -u n ) ) e. CC')
        return D(w, Bq, 'addcld', [a, b], '%s e. CC' % PAIR)
    def hsub(T):
        return w.s([w.s([], 'oveq2', '( n = %s -> ( _i x. n ) = ( _i x. %s ) )' % (T, T))], 'fveq2d', '( n = %s -> ( H ` ( _i x. n ) ) = ( H ` ( _i x. %s ) ) )' % (T, T))
    def uz(lo, hi, loz, hiz, le):
        return w.s([w.s([loz, hiz, le], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (A, lo, hi, lo, hi)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (hi, lo, lo, hi, lo, hi))],
                   'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (A, hi, lo))
    p0 = D(w, A, 'nngt0d', [w.s([m0, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A, m1))], '0 < %s' % m1)
    lex = D(w, A, 'ltled', [x_r, m1r, D(w, A, 'lttrd', [x_r, cst(w, A, '0re', '0 e. RR'), m1r, D(w, A, 'mpbid', [p0, D(w, A, 'lt0neg2d', [m1r], '( 0 < %s <-> %s < 0 )' % (m1, X_))], '%s < 0' % X_), p0], '%s < %s' % (X_, m1))],
            '%s <_ %s' % (X_, m1))
    f1 = w.s([uz(X_, m1, x_z, m1z, lex), hval(X_, m1), hsub(X_)], 'fsum1p', '( %s -> %s = ( ( H ` ( _i x. %s ) ) + %s ) )' % (A, SUMH(X_, m1), X_, SUMH('( %s + 1 )' % X_, m1)))
    xp1 = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [w.s([mc, one, w.inst('negdi2')], 'syl2anc', '( %s -> %s = ( %s - 1 ) )' % (A, X_, nm))], '( %s + 1 ) = ( ( %s - 1 ) + 1 )' % (X_, nm)),
                            w.s([D(w, A, 'negcld', [mc], '%s e. CC' % nm), one, w.inst('npcan')], 'syl2anc', '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (A, nm, nm))], '( %s + 1 ) = %s' % (X_, nm))
    f2 = D(w, A, 'sumeq1d', [D(w, A, 'oveq1d', [xp1], '( ( %s + 1 ) ... %s ) = ( %s ... %s )' % (X_, m1, nm, m1))], '%s = %s' % (SUMH('( %s + 1 )' % X_, m1), SUMH(nm, m1)))
    lem = D(w, A, 'letrd', [nmr, cst(w, A, '0re', '0 e. RR'), mr, D(w, A, 'mpbid', [D(w, A, 'nn0ge0d', [m0], '0 <_ m'), D(w, A, 'le0neg2d', [mr], '( 0 <_ m <-> %s <_ 0 )' % nm)], '%s <_ 0' % nm), D(w, A, 'nn0ge0d', [m0], '0 <_ m')],
            '%s <_ m' % nm)
    f3 = w.s([uz(nm, 'm', nmz, mz, lem), hval(nm, m1), hsub(m1)], 'fsump1', '( %s -> %s = ( %s + ( H ` ( _i x. %s ) ) ) )' % (A, SUMH(nm, m1), SUMH(nm, 'm'), m1))
    HB = '( H ` ( _i x. %s ) )' % X_; HT_ = '( H ` ( _i x. %s ) )' % m1; SM = SUMH(nm, 'm')
    lstep = D(w, A, 'eqtrd', [f1, D(w, A, 'oveq2d', [D(w, A, 'eqtrd', [f2, f3], '%s = ( %s + %s )' % (SUMH('( %s + 1 )' % X_, m1), SM, HT_))],
                                                     '( %s + %s ) = ( %s + ( %s + %s ) )' % (HB, SUMH('( %s + 1 )' % X_, m1), HB, SM, HT_))], '%s = ( %s + ( %s + %s ) )' % (SUMH(X_, m1), HB, SM, HT_))
    # right side: ( 1 ... ( m + 1 ) ) = ( ( 1 ... m ) u. { ( m + 1 ) } )
    uz0 = D(w, A, 'eleqtrrd', [w.s([m0, w.inst('nn0uz')], 'x', 'x') if False else D(w, A, 'eleqtrd', [m0, cst(w, A, 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'm e. ( ZZ>= ` 0 )'),
                               D(w, A, 'fveq2d', [cst(w, A, '1m1e0', '( 1 - 1 ) = 0')], '( ZZ>= ` ( 1 - 1 ) ) = ( ZZ>= ` 0 )')], 'm e. ( ZZ>= ` ( 1 - 1 ) )')
    fs2 = w.s([cst(w, A, '1z', '1 e. ZZ'), uz0, w.inst('fzsuc2')], 'syl2anc', '( %s -> ( 1 ... %s ) = ( ( 1 ... m ) u. { %s } ) )' % (A, m1, m1))
    PD = '( ( H ` ( _i x. %s ) ) + ( H ` ( _i x. -u %s ) ) )' % (m1, m1)
    pdc = D(w, A, 'addcld', [D(w, A, 'ffvelcdmd', [hf, D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), m1c], '( _i x. %s ) e. CC' % m1)], '( H ` ( _i x. %s ) ) e. CC' % m1),
                             D(w, A, 'ffvelcdmd', [hf, D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), x_c], '( _i x. -u %s ) e. CC' % m1)], '( H ` ( _i x. -u %s ) ) e. CC' % m1)], '%s e. CC' % PD)
    psub = w.s([hsub(m1), w.s([w.s([w.s([], 'negeq', '( n = %s -> -u n = -u %s )' % (m1, m1))], 'oveq2d', '( n = %s -> ( _i x. -u n ) = ( _i x. -u %s ) )' % (m1, m1))], 'fveq2d',
                             '( n = %s -> ( H ` ( _i x. -u n ) ) = ( H ` ( _i x. -u %s ) ) )' % (m1, m1))], 'oveq12d', '( n = %s -> %s = %s )' % (m1, PAIR, PD))
    fsn = w.s([w.s([], 'nfv', 'F/ n %s' % A), w.s([], 'nfcv', 'F/_ n %s' % PD), w.s([], 'fzfid', '( %s -> ( 1 ... m ) e. Fin )' % A), w.s([m1z, w.inst('elexd')] if False else [], 'x', 'x') if False else
               w.s([m1z, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A, m1)), cst(w, A, 'fzp1nel', '-. %s e. ( 1 ... m )' % m1), hval('1', 'm', True), psub, pdc], 'fsumsplitsn',
              '( %s -> sum_ n e. ( ( 1 ... m ) u. { %s } ) %s = ( %s + %s ) )' % (A, m1, PAIR, SUMP('m'), PD))
    rstep = D(w, A, 'eqtrd', [D(w, A, 'sumeq1d', [fs2], '%s = sum_ n e. ( ( 1 ... m ) u. { %s } ) %s' % (SUMP(m1), m1, PAIR)), fsn], '%s = ( %s + %s )' % (SUMP(m1), SUMP('m'), PD))
    # combine with the hypothesis
    A2 = '( %s /\\ %s )' % (A, EQ('m'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (A2, EQ('m')))
    lA = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    H0 = '( H ` ( _i x. 0 ) )'
    h0c2 = lA(D(w, A, 'ffvelcdmd', [hf, D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), cst(w, A, '0cn', '0 e. CC')], '( _i x. 0 ) e. CC')], '%s e. CC' % H0), '%s e. CC' % H0)
    spc = lA(w.s([w.s([], 'fzfid', '( %s -> ( 1 ... m ) e. Fin )' % A), hval('1', 'm', True)], 'fsumcl', '( %s -> %s e. CC )' % (A, SUMP('m'))), '%s e. CC' % SUMP('m'))
    hbc = lA(D(w, A, 'ffvelcdmd', [hf, D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), x_c], '( _i x. %s ) e. CC' % X_)], '%s e. CC' % HB), '%s e. CC' % HB)
    htc = lA(D(w, A, 'ffvelcdmd', [hf, D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), m1c], '( _i x. %s ) e. CC' % m1)], '%s e. CC' % HT_), '%s e. CC' % HT_)
    # LHS(m+1) = HB + ( ( H0 + SP ) + HT ) ; RHS(m+1) = H0 + ( SP + ( HT + HB ) )
    L1 = D(w, A2, 'eqtrd', [lA(lstep, '%s = ( %s + ( %s + %s ) )' % (SUMH(X_, m1), HB, SM, HT_)), D(w, A2, 'oveq2d', [D(w, A2, 'oveq1d', [ih], '( %s + %s ) = ( ( %s + %s ) + %s )' % (SM, HT_, H0, SUMP('m'), HT_))],
                                                                                                      '( %s + ( %s + %s ) ) = ( %s + ( ( %s + %s ) + %s ) )' % (HB, SM, HT_, HB, H0, SUMP('m'), HT_))],
            '%s = ( %s + ( ( %s + %s ) + %s ) )' % (SUMH(X_, m1), HB, H0, SUMP('m'), HT_))
    SP = SUMP('m')
    # normalize both sides with CxSum
    from c0b_lib import CxSum, rn
    cc = {HB: hbc, H0: h0c2, SP: spc, HT_: htc}
    cs = CxSum(w, A2, cc, {H0: 0, SP: 1, HT_: 2, HB: 3})
    nL, aL = cs.nf(('+', HB, ('+', ('+', H0, SP), HT_)))
    nR, aR = cs.nf(('+', H0, ('+', SP, ('+', HT_, HB))))
    assert aL == aR
    R1 = D(w, A2, 'oveq2d', [lA(rstep, '%s = ( %s + %s )' % (SUMP(m1), SP, PD))], '( %s + %s ) = ( %s + ( %s + %s ) )' % (H0, SUMP(m1), H0, SP, PD))
    fin = D(w, A2, 'eqtr4d', [D(w, A2, 'eqtrd', [L1, nL], '%s = %s' % (SUMH(X_, m1), rn(aL))), D(w, A2, 'eqtrd', [R1, nR], '( %s + %s ) = %s' % (H0, SUMP(m1), rn(aR)))], EQ(m1))
    st1 = w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (A, EQ('m'), EQ(m1)))
    st2 = w.s([st1], 'ex', '( m e. NN0 -> ( %s -> ( %s -> %s ) ) )' % (HF, EQ('m'), EQ(m1)))
    st3 = w.s([st2], 'a2d', '( m e. NN0 -> ( %s -> %s ) )' % (PK('m'), PK(m1)))
    ind = w.s([h1, h2, h3, h4, base, st3], 'nn0ind', '( N e. NN0 -> %s )' % PK('N'))
    w.qed([ind], 'impcom', S['zl3fzs'])
    go(w, only)


# ---------------------------------------------------------------- zl3sqz
if __name__ == '__main__' and (not only or 'zl3sqz' in only):
    w = W('zl3sqz', 'A sequence within ` C R ^ n ` of ` L ` (with ` 0 <_ R < 1 `) converges to ` L `.')
    ph, concl = ante_of(S['zl3sqz'])
    t1 = w.s([], 'simp1', '( %s -> ( L e. CC /\\ C e. RR ) )' % ph)
    t2 = w.s([], 'simp2', '( %s -> ( R e. RR /\\ ( 0 <_ R /\\ R < 1 ) ) )' % ph)
    ALL = 'A. n e. NN ( ( S ` n ) e. CC /\\ ( abs ` ( ( S ` n ) - L ) ) <_ ( C x. ( R ^ n ) ) )'
    t3 = w.s([], 'simp3', '( %s -> ( S e. V /\\ %s ) )' % (ph, ALL))
    lc = w.s([t1, w.inst('simpl')], 'syl', '( %s -> L e. CC )' % ph); cr = w.s([t1, w.inst('simpr')], 'syl', '( %s -> C e. RR )' % ph)
    rr = w.s([t2, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % ph)
    r01 = w.s([t2, w.inst('simpr')], 'syl', '( %s -> ( 0 <_ R /\\ R < 1 ) )' % ph)
    r0 = w.s([r01, w.inst('simpl')], 'syl', '( %s -> 0 <_ R )' % ph); r1 = w.s([r01, w.inst('simpr')], 'syl', '( %s -> R < 1 )' % ph)
    sv = w.s([t3, w.inst('simpl')], 'syl', '( %s -> S e. V )' % ph); al = w.s([t3, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, ALL))
    rc = D(w, ph, 'recnd', [rr], 'R e. CC')
    ra = D(w, ph, 'eqbrtrd', [D(w, ph, 'absidd', [rr, r0], '( abs ` R ) = R'), r1], '( abs ` R ) < 1')
    F0 = '( n e. NN0 |-> ( R ^ n ) )'
    f0 = w.s([rc, ra], 'expcnv', '( %s -> %s ~~> 0 )' % (ph, F0))
    Z = '( ZZ>= ` 1 )'
    zeq = w.s([], 'eqid', '%s = %s' % (Z, Z))
    one_z = cst(w, ph, '1z', '1 e. ZZ')
    PU = '( %s /\\ k e. %s )' % (ph, Z)
    kN = D(w, PU, 'eleqtrrd', [w.s([], 'simpr', '( %s -> k e. %s )' % (PU, Z)), cst(w, PU, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'k e. NN')
    kn0 = D(w, PU, 'nnnn0d', [kN], 'k e. NN0')
    rk = D(w, PU, 'reexpcld', [w.s([rr], 'adantr', '( %s -> R e. RR )' % PU), kn0], '( R ^ k ) e. RR')
    f0v = w.s([kn0, w.s([w.s([], 'oveq2', '( n = k -> ( R ^ n ) = ( R ^ k ) )'), w.s([], 'eqid', '%s = %s' % (F0, F0)), w.s([], 'ovex', '( R ^ k ) e. _V')], 'fvmpt', '( k e. NN0 -> ( %s ` k ) = ( R ^ k ) )' % F0)], 'syl',
              '( %s -> ( %s ` k ) = ( R ^ k ) )' % (PU, F0))
    F1 = '( n e. NN |-> ( C x. ( R ^ n ) ) )'
    crk = D(w, PU, 'remulcld', [w.s([cr], 'adantr', '( %s -> C e. RR )' % PU), rk], '( C x. ( R ^ k ) ) e. RR')
    f1v = w.s([kN, w.s([w.s([w.s([], 'oveq2', '( n = k -> ( R ^ n ) = ( R ^ k ) )')], 'oveq2d', '( n = k -> ( C x. ( R ^ n ) ) = ( C x. ( R ^ k ) ) )'), w.s([], 'eqid', '%s = %s' % (F1, F1)),
                        w.s([], 'ovex', '( C x. ( R ^ k ) ) e. _V')], 'fvmpt', '( k e. NN -> ( %s ` k ) = ( C x. ( R ^ k ) ) )' % F1)], 'syl', '( %s -> ( %s ` k ) = ( C x. ( R ^ k ) ) )' % (PU, F1))
    f1l = w.s([zeq, one_z, f0, D(w, ph, 'recnd', [cr], 'C e. CC'), w.s([w.s([], 'nnex', 'NN e. _V')], 'x', 'x') if False else w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % F1)], 'a1i', '( %s -> %s e. _V )' % (ph, F1)),
               D(w, PU, 'eqeltrd', [f0v, D(w, PU, 'recnd', [rk], '( R ^ k ) e. CC')], '( %s ` k ) e. CC' % F0),
               D(w, PU, 'eqtr4d', [f1v, D(w, PU, 'oveq2d', [f0v], '( C x. ( %s ` k ) ) = ( C x. ( R ^ k ) )' % F0)], '( %s ` k ) = ( C x. ( %s ` k ) )' % (F1, F0))], 'climmulc2',
              '( %s -> %s ~~> ( C x. 0 ) )' % (ph, F1))
    f1l0 = D(w, ph, 'breqtrd', [f1l, D(w, ph, 'mul01d', [D(w, ph, 'recnd', [cr], 'C e. CC')], '( C x. 0 ) = 0')], '%s ~~> 0' % F1)
    # the values of S at k
    body = lambda c: '( ( S ` %s ) e. CC /\\ ( abs ` ( ( S ` %s ) - L ) ) <_ ( C x. ( R ^ %s ) ) )' % (c, c, c)
    E = 'n = k'
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    sn = D(w, E, 'fveq2d', [e], '( S ` n ) = ( S ` k )')
    beq = D(w, E, 'anbi12d', [D(w, E, 'eleq1d', [sn], '( ( S ` n ) e. CC <-> ( S ` k ) e. CC )'),
                              D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'oveq1d', [sn], '( ( S ` n ) - L ) = ( ( S ` k ) - L )')], '( abs ` ( ( S ` n ) - L ) ) = ( abs ` ( ( S ` k ) - L ) )'),
                                                  D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [e], '( R ^ n ) = ( R ^ k )')], '( C x. ( R ^ n ) ) = ( C x. ( R ^ k ) )')],
                                '( ( abs ` ( ( S ` n ) - L ) ) <_ ( C x. ( R ^ n ) ) <-> ( abs ` ( ( S ` k ) - L ) ) <_ ( C x. ( R ^ k ) ) )')], '( %s <-> %s )' % (body('n'), body('k')))
    bk = w.s([kN, w.s([al], 'adantr', '( %s -> %s )' % (PU, ALL)), w.s([beq], 'rspcv', '( k e. NN -> ( %s -> %s ) )' % (ALL, body('k')))], 'sylc', '( %s -> %s )' % (PU, body('k')))
    skc = w.s([bk, w.inst('simpl')], 'syl', '( %s -> ( S ` k ) e. CC )' % PU)
    skb = w.s([bk, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( ( S ` k ) - L ) ) <_ ( C x. ( R ^ k ) ) )' % PU)
    E_ = '( n e. NN |-> ( ( S ` n ) - L ) )'; DA = '( n e. NN |-> ( abs ` ( ( S ` n ) - L ) ) )'
    dkc = D(w, PU, 'subcld', [skc, w.s([lc], 'adantr', '( %s -> L e. CC )' % PU)], '( ( S ` k ) - L ) e. CC')
    ev = w.s([kN, w.s([w.s([sn], 'oveq1d', '( n = k -> ( ( S ` n ) - L ) = ( ( S ` k ) - L ) )'), w.s([], 'eqid', '%s = %s' % (E_, E_)), w.s([], 'ovex', '( ( S ` k ) - L ) e. _V')], 'fvmpt',
                       '( k e. NN -> ( %s ` k ) = ( ( S ` k ) - L ) )' % E_)], 'syl', '( %s -> ( %s ` k ) = ( ( S ` k ) - L ) )' % (PU, E_))
    dv_ = w.s([kN, w.s([w.s([w.s([sn], 'oveq1d', '( n = k -> ( ( S ` n ) - L ) = ( ( S ` k ) - L ) )')], 'fveq2d', '( n = k -> ( abs ` ( ( S ` n ) - L ) ) = ( abs ` ( ( S ` k ) - L ) ) )'),
                        w.s([], 'eqid', '%s = %s' % (DA, DA)), w.s([], 'fvex', '( abs ` ( ( S ` k ) - L ) ) e. _V')], 'fvmpt', '( k e. NN -> ( %s ` k ) = ( abs ` ( ( S ` k ) - L ) ) )' % DA)], 'syl',
              '( %s -> ( %s ` k ) = ( abs ` ( ( S ` k ) - L ) ) )' % (PU, DA))
    dar = D(w, PU, 'abscld', [dkc], '( abs ` ( ( S ` k ) - L ) ) e. RR')
    sq = w.s([zeq, one_z, f1l0, w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % DA)], 'a1i', '( %s -> %s e. _V )' % (ph, DA)),
              D(w, PU, 'eqeltrd', [f1v, crk], '( %s ` k ) e. RR' % F1), D(w, PU, 'eqeltrd', [dv_, dar], '( %s ` k ) e. RR' % DA),
              D(w, PU, 'breqtrrd', [D(w, PU, 'eqbrtrd', [dv_, skb], '( %s ` k ) <_ ( C x. ( R ^ k ) )' % DA), f1v], '( %s ` k ) <_ ( %s ` k )' % (DA, F1)),
              D(w, PU, 'breqtrrd', [D(w, PU, 'absge0d', [dkc], '0 <_ ( abs ` ( ( S ` k ) - L ) )'), dv_], '0 <_ ( %s ` k )' % DA)], 'climsqz2', '( %s -> %s ~~> 0 )' % (ph, DA))
    ab0 = w.s([zeq, one_z, w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % E_)], 'a1i', '( %s -> %s e. _V )' % (ph, E_)), w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % DA)], 'a1i', '( %s -> %s e. _V )' % (ph, DA)),
               D(w, PU, 'eqeltrd', [ev, dkc], '( %s ` k ) e. CC' % E_), D(w, PU, 'eqtr4d', [dv_, D(w, PU, 'fveq2d', [ev], '( abs ` ( %s ` k ) ) = ( abs ` ( ( S ` k ) - L ) )' % E_)], '( %s ` k ) = ( abs ` ( %s ` k ) )' % (DA, E_))],
              'climabs0', '( %s -> ( %s ~~> 0 <-> %s ~~> 0 ) )' % (ph, E_, DA))
    e0 = D(w, ph, 'mpbird', [sq, ab0], '%s ~~> 0' % E_)
    sk = D(w, PU, 'eqcomd', [D(w, PU, 'eqtrd', [D(w, PU, 'oveq1d', [ev], '( ( %s ` k ) + L ) = ( ( ( S ` k ) - L ) + L )' % E_), D(w, PU, 'npcand', [skc, w.s([lc], 'adantr', '( %s -> L e. CC )' % PU)], '( ( ( S ` k ) - L ) + L ) = ( S ` k )')],
                                               '( ( %s ` k ) + L ) = ( S ` k )' % E_)], '( S ` k ) = ( ( %s ` k ) + L )' % E_)
    cl = w.s([zeq, one_z, e0, lc, sv, D(w, PU, 'eqeltrd', [ev, dkc], '( %s ` k ) e. CC' % E_), sk], 'climaddc1', '( %s -> S ~~> ( 0 + L ) )' % ph)
    w.qed([cl, D(w, ph, 'addlidd', [lc], '( 0 + L ) = L')], 'breqtrd', S['zl3sqz'])
    go(w, only)


# ---------------------------------------------------------------- zl3d0
if __name__ == '__main__' and (not only or 'zl3d0' in only):
    w = W('zl3d0', 'Off the imaginary axis ` e ^ ( 2 pi w ) =/= 1 `.')
    ph, concl = ante_of(S['zl3d0'])
    ac = w.s([], 'simpl', '( %s -> A e. CC )' % ph); rn = w.s([], 'simpr', '( %s -> ( Re ` A ) =/= 0 )' % ph)
    B = '( %s /\\ %s = 1 )' % (ph, E2('A'))
    ez = w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % B), w.s([], 'simpr', '( %s -> %s = 1 )' % (B, E2('A'))), w.inst('zl3ez')], 'syl2anc', '( %s -> ( ( Re ` A ) = 0 /\\ ( Im ` A ) e. ZZ ) )' % B)
    r0 = w.s([ez, w.inst('simpl')], 'syl', '( %s -> ( Re ` A ) = 0 )' % B)
    imp = w.s([r0], 'ex', '( %s -> ( %s = 1 -> ( Re ` A ) = 0 ) )' % (ph, E2('A')))
    ne = D(w, ph, 'necon3d', [imp], '( ( Re ` A ) =/= 0 -> %s =/= 1 )' % E2('A'))
    ne1 = D(w, ph, 'mpd', [rn, ne], '%s =/= 1' % E2('A'))
    w.qed([d0_mem(w, ph, 'A', ac, ne1)], 'idi', S['zl3d0'])
    go(w, only)
