"""ZL3b D1: the kernel e ^ ( 2 pi w ) - 1 (zeros, derivative) and the open Im-strips.
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_d1.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *

only = sys.argv[1:]
S = STATEMENTS


def ante_of(st):
    """antecedent text of '( ANTE -> CONCL )' (top-level split)"""
    assert st.startswith('( ')
    depth = 0; toks = st[2:-2].split(' ')
    for i, t in enumerate(toks):
        if t == '(':
            depth += 1
        elif t == ')':
            depth -= 1
        elif t == '->' and depth == 0:
            return ' '.join(toks[:i]), ' '.join(toks[i + 1:])
    raise ValueError(st)


TP = '( 2 x. _pi )'


def twopi(w, ph):
    """steps ( ph -> ( 2 x. _pi ) e. CC ), ( ph -> ( 2 x. _pi ) =/= 0 )"""
    c2 = D(w, ph, '2cnd', [], '2 e. CC')
    pc = w.s([w.s([], 'picn', '_pi e. CC')], 'a1i', '( %s -> _pi e. CC )' % ph)
    tc = D(w, ph, 'mulcld', [c2, pc], '%s e. CC' % TP)
    n2 = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % ph)
    np = w.s([w.s([], 'pine0', '_pi =/= 0')], 'a1i', '( %s -> _pi =/= 0 )' % ph)
    tn = D(w, ph, 'mulne0d', [c2, pc, n2, np], '%s =/= 0' % TP)
    return tc, tn


# ---------------------------------------------------------------- zl3ez
if __name__ == '__main__' and (not only or 'zl3ez' in only):
    w = W('zl3ez', 'A zero of ` e ^ ( 2 pi w ) - 1 ` lies on the imaginary axis at an integer height.')
    ph, concl = ante_of(S['zl3ez'])
    ac = w.s([], 'simpl', '( %s -> A e. CC )' % ph)
    e1 = w.s([], 'simpr', '( %s -> %s = 1 )' % (ph, E2('A')))
    tc, tn = twopi(w, ph)
    X = '( %s x. A )' % TP
    xc = D(w, ph, 'mulcld', [tc, ac], '%s e. CC' % X)
    IT = '( _i x. %s )' % TP
    q = '( %s / %s )' % (X, IT)
    eq1 = w.s([xc, w.inst('efeq1')], 'syl', '( %s -> ( ( exp ` %s ) = 1 <-> %s e. ZZ ) )' % (ph, X, q))
    qz = w.s([e1, eq1], 'mpbid', '( %s -> %s e. ZZ )' % (ph, q))
    qr = D(w, ph, 'zred', [qz], '%s e. RR' % q)
    qc = D(w, ph, 'recnd', [qr], '%s e. CC' % q)
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ph)
    inz = w.s([w.s([], 'ine0', '_i =/= 0')], 'a1i', '( %s -> _i =/= 0 )' % ph)
    itc = D(w, ph, 'mulcld', [ic, tc], '%s e. CC' % IT)
    itn = D(w, ph, 'mulne0d', [ic, tc, inz, tn], '%s =/= 0' % IT)
    dc = D(w, ph, 'divcan1d', [xc, itc, itn], '( %s x. %s ) = %s' % (q, IT, X))
    # q ( i 2pi ) = 2pi ( i q )
    r1 = D(w, ph, 'mulcomd', [qc, itc], '( %s x. %s ) = ( %s x. %s )' % (q, IT, IT, q))
    r2 = D(w, ph, 'mulcomd', [ic, tc], '%s = ( %s x. _i )' % (IT, TP))
    r3 = D(w, ph, 'oveq1d', [r2], '( %s x. %s ) = ( ( %s x. _i ) x. %s )' % (IT, q, TP, q))
    r4 = D(w, ph, 'mulassd', [tc, ic, qc], '( ( %s x. _i ) x. %s ) = ( %s x. ( _i x. %s ) )' % (TP, q, TP, q))
    r5 = D(w, ph, 'eqtrd', [r1, r3], '( %s x. %s ) = ( ( %s x. _i ) x. %s )' % (q, IT, TP, q))
    r6 = D(w, ph, 'eqtrd', [r5, r4], '( %s x. %s ) = ( %s x. ( _i x. %s ) )' % (q, IT, TP, q))
    r7 = D(w, ph, 'eqtr3d', [dc, r6], '%s = ( %s x. ( _i x. %s ) )' % (X, TP, q))
    iqc = D(w, ph, 'mulcld', [ic, qc], '( _i x. %s ) e. CC' % q)
    aeq = D(w, ph, 'mulcanad', [ac, iqc, tc, tn, r7], 'A = ( _i x. %s )' % q)
    z0 = w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % ph)
    a0 = D(w, ph, 'addlidd', [iqc], '( 0 + ( _i x. %s ) ) = ( _i x. %s )' % (q, q))
    aeq2 = D(w, ph, 'eqtr4d', [aeq, a0], 'A = ( 0 + ( _i x. %s ) )' % q)
    re1 = D(w, ph, 'fveq2d', [aeq2], '( Re ` A ) = ( Re ` ( 0 + ( _i x. %s ) ) )' % q)
    re2 = w.s([z0, qr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` ( 0 + ( _i x. %s ) ) ) = 0 )' % (ph, q))
    re3 = D(w, ph, 'eqtrd', [re1, re2], '( Re ` A ) = 0')
    im1 = D(w, ph, 'fveq2d', [aeq2], '( Im ` A ) = ( Im ` ( 0 + ( _i x. %s ) ) )' % q)
    im2 = w.s([z0, qr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` ( 0 + ( _i x. %s ) ) ) = %s )' % (ph, q, q))
    im3 = D(w, ph, 'eqtrd', [im1, im2], '( Im ` A ) = %s' % q)
    imz = D(w, ph, 'eqeltrd', [im3, qz], '( Im ` A ) e. ZZ')
    w.qed([re3, imz], 'jca', S['zl3ez'])
    go(w, only)

# ---------------------------------------------------------------- zl3ezn
if __name__ == '__main__' and (not only or 'zl3ezn' in only):
    w = W('zl3ezn', 'The only zero of ` e ^ ( 2 pi w ) - 1 ` in the strip ` N - 1 < Im w < N + 1 ` is ` i N `.')
    ph, concl = ante_of(S['zl3ezn'])
    nz = w.s([], 'simp1', '( %s -> N e. ZZ )' % ph)
    st = w.s([], 'simp2', '( %s -> ( A e. CC /\\ ( ( N - 1 ) < ( Im ` A ) /\\ ( Im ` A ) < ( N + 1 ) ) ) )' % ph)
    e1 = w.s([], 'simp3', '( %s -> %s = 1 )' % (ph, E2('A')))
    ac = w.s([st, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % ph)
    lo = w.s([st, w.inst('simprl')], 'syl', '( %s -> ( N - 1 ) < ( Im ` A ) )' % ph)
    hi = w.s([st, w.inst('simprr')], 'syl', '( %s -> ( Im ` A ) < ( N + 1 ) )' % ph)
    ez = w.s([ac, e1, w.inst('zl3ez')], 'syl2anc', '( %s -> ( ( Re ` A ) = 0 /\\ ( Im ` A ) e. ZZ ) )' % ph)
    re0 = w.s([ez, w.inst('simpl')], 'syl', '( %s -> ( Re ` A ) = 0 )' % ph)
    imz = w.s([ez, w.inst('simpr')], 'syl', '( %s -> ( Im ` A ) e. ZZ )' % ph)
    n1z = w.s([nz, w.inst('peano2zm')], 'syl', '( %s -> ( N - 1 ) e. ZZ )' % ph)
    b1 = w.s([n1z, imz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( ( N - 1 ) < ( Im ` A ) <-> ( ( N - 1 ) + 1 ) <_ ( Im ` A ) ) )' % ph)
    l1 = D(w, ph, 'mpbid', [lo, b1], '( ( N - 1 ) + 1 ) <_ ( Im ` A )')
    nc = D(w, ph, 'zcnd', [nz], 'N e. CC')
    c1 = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph)
    np = w.s([nc, c1, w.inst('npcan')], 'syl2anc', '( %s -> ( ( N - 1 ) + 1 ) = N )' % ph)
    l2 = D(w, ph, 'eqbrtrrd', [np, l1], 'N <_ ( Im ` A )')
    b2 = w.s([imz, nz, w.inst('zleltp1')], 'syl2anc', '( %s -> ( ( Im ` A ) <_ N <-> ( Im ` A ) < ( N + 1 ) ) )' % ph)
    l3 = D(w, ph, 'mpbird', [hi, b2], '( Im ` A ) <_ N')
    imr = D(w, ph, 'zred', [imz], '( Im ` A ) e. RR')
    nr = D(w, ph, 'zred', [nz], 'N e. RR')
    tr = D(w, ph, 'letri3d', [imr, nr], '( ( Im ` A ) = N <-> ( ( Im ` A ) <_ N /\\ N <_ ( Im ` A ) ) )')
    ime = D(w, ph, 'mpbir2and', [l3, l2, tr], '( Im ` A ) = N')
    rp = D(w, ph, 'replimd', [ac], 'A = ( ( Re ` A ) + ( _i x. ( Im ` A ) ) )')
    t1 = D(w, ph, 'oveq2d', [ime], '( _i x. ( Im ` A ) ) = ( _i x. N )')
    t2 = D(w, ph, 'oveq12d', [re0, t1], '( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) = ( 0 + ( _i x. N ) )')
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ph)
    inc = D(w, ph, 'mulcld', [ic, nc], '( _i x. N ) e. CC')
    t3 = D(w, ph, 'addlidd', [inc], '( 0 + ( _i x. N ) ) = ( _i x. N )')
    t4 = D(w, ph, 'eqtrd', [rp, t2], 'A = ( 0 + ( _i x. N ) )')
    w.qed([t4, t3], 'eqtrd', S['zl3ezn'])
    go(w, only)

# ---------------------------------------------------------------- zl3imopn
if __name__ == '__main__' and (not only or 'zl3imopn' in only):
    w = W('zl3imopn', 'An open horizontal strip ` A < Im z < B ` is an open set of the complex plane.')
    s1 = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    s2 = w.s([], 'cnrestid', '( ( TopOpen ` CCfld ) |`t CC ) = ( TopOpen ` CCfld )')
    s3 = w.s([s2], 'eqcomi', '( TopOpen ` CCfld ) = ( ( TopOpen ` CCfld ) |`t CC )')
    s4 = w.s([], 'tgioo4', '( topGen ` ran (,) ) = ( ( TopOpen ` CCfld ) |`t RR )')
    s5 = w.s([], 'ssid', 'CC C_ CC')
    s6 = w.s([], 'ax-resscn', 'RR C_ CC')
    s7 = w.s([s1, s3, s4], 'cncfcn', '( ( CC C_ CC /\\ RR C_ CC ) -> ( CC -cn-> RR ) = ( ( TopOpen ` CCfld ) Cn ( topGen ` ran (,) ) ) )')
    s8 = w.s([s5, s6, s7], 'mp2an', '( CC -cn-> RR ) = ( ( TopOpen ` CCfld ) Cn ( topGen ` ran (,) ) )')
    s9 = w.s([], 'imcncf', 'Im e. ( CC -cn-> RR )')
    s10 = w.s([s9, s8], 'eleqtri', 'Im e. ( ( TopOpen ` CCfld ) Cn ( topGen ` ran (,) ) )')
    s11 = w.s([], 'iooretop', '( A (,) B ) e. ( topGen ` ran (,) )')
    w.qed([s10, s11, w.inst('cnima')], 'mp2an', S['zl3imopn'])
    go(w, only)

# ---------------------------------------------------------------- zl3dve
def MP(x, X, B):
    return '( %s e. %s |-> %s )' % (x, X, B)


if __name__ == '__main__' and (not only or 'zl3dve' in only):
    w = W('zl3dve', '` e ^ ( 2 pi w ) - 1 ` is continuous with derivative ` 2 pi e ^ ( 2 pi w ) `.')
    A0 = 'T.'; A1 = '( T. /\\ w e. CC )'; A2 = '( T. /\\ y e. CC )'
    ARG = '( %s x. w )' % TP; EW = E2('w')
    ce = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( T. -> CC e. { RR , CC } )')
    wc = w.s([], 'simpr', '( %s -> w e. CC )' % A1)
    did = w.s([ce], 'dvmptid', '( T. -> ( CC _D %s ) = %s )' % (MP('w', 'CC', 'w'), MP('w', 'CC', '1')))
    tc0, tn0 = twopi(w, A0)
    tc1, tn1 = twopi(w, A1)
    one1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % A1)
    dcm = w.s([ce, wc, one1, did, tc0], 'dvmptcmul', '( T. -> ( CC _D %s ) = %s )' % (MP('w', 'CC', ARG), MP('w', 'CC', '( %s x. 1 )' % TP)))
    argc = D(w, A1, 'mulcld', [tc1, wc], '%s e. CC' % ARG)
    t1c = D(w, A1, 'mulcld', [tc1, one1], '( %s x. 1 ) e. CC' % TP)
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % A2)
    eyc = w.s([yc, w.inst('efcl')], 'syl', '( %s -> ( exp ` y ) e. CC )' % A2)
    efm = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC')], 'a1i', '( T. -> exp : CC --> CC )')], 'feqmptd', '( T. -> exp = %s )' % MP('y', 'CC', '( exp ` y )'))
    dvefd = w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'a1i', '( T. -> ( CC _D exp ) = exp )')
    d1 = w.s([w.s([efm], 'oveq2d', '( T. -> ( CC _D exp ) = ( CC _D %s ) )' % MP('y', 'CC', '( exp ` y )'))], 'eqcomd',
             '( T. -> ( CC _D %s ) = ( CC _D exp ) )' % MP('y', 'CC', '( exp ` y )'))
    dcy = w.s([w.s([d1, dvefd], 'eqtrd', '( T. -> ( CC _D %s ) = exp )' % MP('y', 'CC', '( exp ` y )')), efm], 'eqtrd',
              '( T. -> ( CC _D %s ) = %s )' % (MP('y', 'CC', '( exp ` y )'), MP('y', 'CC', '( exp ` y )')))
    sty = w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = %s )' % (ARG, EW))
    dco = w.s([ce, ce, argc, t1c, eyc, eyc, dcm, dcy, sty, sty], 'dvmptco',
              '( T. -> ( CC _D %s ) = %s )' % (MP('w', 'CC', EW), MP('w', 'CC', '( %s x. ( %s x. 1 ) )' % (EW, TP))))
    ewc = w.s([argc, w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A1, EW))
    bc = D(w, A1, 'mulcld', [ewc, t1c], '( %s x. ( %s x. 1 ) ) e. CC' % (EW, TP))
    z1 = w.s([], '0cnd', '( %s -> 0 e. CC )' % A1)
    dc1 = w.s([ce, w.s([], '1cnd', '( T. -> 1 e. CC )')], 'dvmptc', '( T. -> ( CC _D %s ) = %s )' % (MP('w', 'CC', '1'), MP('w', 'CC', '0')))
    dsb = w.s([ce, ewc, bc, dco, one1, z1, dc1], 'dvmptsub',
              '( T. -> ( CC _D %s ) = %s )' % (EF, MP('w', 'CC', '( ( %s x. ( %s x. 1 ) ) - 0 )' % (EW, TP))))
    s1 = D(w, A1, 'subid1d', [bc], '( ( %s x. ( %s x. 1 ) ) - 0 ) = ( %s x. ( %s x. 1 ) )' % (EW, TP, EW, TP))
    s2 = D(w, A1, 'mulridd', [tc1], '( %s x. 1 ) = %s' % (TP, TP))
    s3 = D(w, A1, 'oveq2d', [s2], '( %s x. ( %s x. 1 ) ) = ( %s x. %s )' % (EW, TP, EW, TP))
    s4 = D(w, A1, 'mulcomd', [ewc, tc1], '( %s x. %s ) = ( %s x. %s )' % (EW, TP, TP, EW))
    s5 = D(w, A1, 'eqtrd', [s1, s3], '( ( %s x. ( %s x. 1 ) ) - 0 ) = ( %s x. %s )' % (EW, TP, EW, TP))
    s6 = D(w, A1, 'eqtrd', [s5, s4], '( ( %s x. ( %s x. 1 ) ) - 0 ) = ( %s x. %s )' % (EW, TP, TP, EW))
    s7 = w.s([s6], 'mpteq2dva', '( T. -> %s = %s )' % (MP('w', 'CC', '( ( %s x. ( %s x. 1 ) ) - 0 )' % (EW, TP)), MP('w', 'CC', '( %s x. %s )' % (TP, EW))))
    dv = w.s([dsb, s7], 'eqtrd', '( T. -> ( CC _D %s ) = %s )' % (EF, MP('w', 'CC', '( %s x. %s )' % (TP, EW))))
    # continuity
    rc = D(w, A1, 'mulcld', [tc1, ewc], '( %s x. %s ) e. CC' % (TP, EW))
    dmd = w.s([w.s([], 'eqid', '%s = %s' % (MP('w', 'CC', '( %s x. %s )' % (TP, EW)), MP('w', 'CC', '( %s x. %s )' % (TP, EW)))), rc], 'dmmptd',
              '( T. -> dom %s = CC )' % MP('w', 'CC', '( %s x. %s )' % (TP, EW)))
    dmv = w.s([w.s([dv], 'dmeqd', '( T. -> dom ( CC _D %s ) = dom %s )' % (EF, MP('w', 'CC', '( %s x. %s )' % (TP, EW)))), dmd], 'eqtrd',
              '( T. -> dom ( CC _D %s ) = CC )' % EF)
    vc = D(w, A1, 'subcld', [ewc, one1], '( %s - 1 ) e. CC' % EW)
    ff = w.s([vc, w.s([], 'eqid', '%s = %s' % (EF, EF))], 'fmptd', '( T. -> %s : CC --> CC )' % EF)
    ss = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( T. -> CC C_ CC )')
    tri = w.s([ss, ff, ss], '3jca', '( T. -> ( CC C_ CC /\\ %s : CC --> CC /\\ CC C_ CC ) )' % EF)
    cn = w.s([tri, dmv, w.inst('dvcn')], 'syl2anc', '( T. -> %s e. ( CC -cn-> CC ) )' % EF)
    fin = w.s([cn, dv], 'jca', '( T. -> %s )' % S['zl3dve'])
    w.qed([fin], 'mptru', S['zl3dve'])
    go(w, only)
