"""Sortie A4c, batch 5b: the length bound across one DP step."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DS = '( ( L DpStep P ) ` T )'
DS1 = '( 1st ` %s )' % DS
T3 = '( L e. NN /\\ P e. NN0 /\\ T e. Tbl )'
def RBS(v, g):
    return '( ( ( T ` %s ) =/= %s /\\ %s = ( ( %s x. P ) mod L ) ) /\\ ( 2nd ` ( %s ` %s ) ) = ( <" P "> ++ ( 2nd ` ( T ` %s ) ) ) )' % (v, NONE, g, v, DS1, g, v)

def paystep(w, A, ttst, cst, nnst, x):
    """( A -> ( 2nd ` ( T ` x ) ) e. Word NN0 ) from T e. Tbl, x e. NN0, ( T ` x ) =/= NONE"""
    p = w.s([w.s([w.s([ttst, cst], 'jca', '( %s -> ( T e. Tbl /\\ %s e. NN0 ) )' % (A, x)), nnst], 'jca',
                 '( %s -> ( ( T e. Tbl /\\ %s e. NN0 ) /\\ ( T ` %s ) =/= %s ) )' % (A, x, x, NONE)), w.inst('tblpay')], 'syl',
             '( %s -> ( ( 2nd ` ( T ` %s ) ) e. Word NN0 /\\ ( T ` %s ) = ( inl ` ( 2nd ` ( T ` %s ) ) ) ) )' % (A, x, x, x))
    return w.s([p], 'simpld', '( %s -> ( 2nd ` ( T ` %s ) ) e. Word NN0 )' % (A, x))

def lenre(w, A, wst, x):
    return w.s([w.s([wst, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A, x))], 'nn0red',
               '( %s -> ( # ` %s ) e. RR )' % (A, x))

if not only or 'tblbnds' in only:
    w = W('tblbnds', 'A DP step raises the length bound by one (Lean: tblBounded_dpStep).')
    A = '( %s /\\ ( K e. NN0 /\\ %s ) )' % (T3, TB('T', 'K'))
    ll = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, T3))], 'simp1d', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, T3))], 'simp2d', '( %s -> P e. NN0 )' % A)
    tt = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, T3))], 'simp3d', '( %s -> T e. Tbl )' % A)
    dpo = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A), tt], 'jca', '( %s -> %s )' % (A, DPO))
    kk = w.s([], 'simprl', '( %s -> K e. NN0 )' % A)
    tb = w.s([], 'simprr', '( %s -> %s )' % (A, TB('T', 'K')))
    B = '( %s /\\ g e. NN0 )' % A
    U = '( %s /\\ ( %s ` g ) =/= %s )' % (B, DS1, NONE)
    up = lambda st, f: w.s([w.s([st], 'adantr', '( %s -> %s )' % (B, f))], 'adantr', '( %s -> %s )' % (U, f))
    gg = w.s([w.s([], 'simpr', '( %s -> g e. NN0 )' % B)], 'adantr', '( %s -> g e. NN0 )' % U)
    hyp = w.s([], 'simpr', '( %s -> ( %s ` g ) =/= %s )' % (U, DS1, NONE))
    dpoU = up(dpo, DPO); ppU = up(pp, 'P e. NN0'); ttU = up(tt, 'T e. Tbl')
    kkU = up(kk, 'K e. NN0'); tbU = up(tb, TB('T', 'K'))
    HL = '( # ` ( 2nd ` ( %s ` g ) ) )' % DS1
    GOAL = '%s <_ ( K + 1 )' % HL
    NEW = '( g = ( P mod L ) /\\ ( 2nd ` ( %s ` g ) ) = <" P "> )' % DS1
    CONC = '( ( T ` g ) = ( %s ` g ) \\/ ( %s \\/ E. r e. ( 0 ..^ L ) %s ) )' % (DS1, NEW, RBS('r', 'g'))
    cas = w.s([w.s([dpoU, w.s([gg, hyp], 'jca', '( %s -> ( g e. NN0 /\\ ( %s ` g ) =/= %s ) )' % (U, DS1, NONE))], 'jca',
                   '( %s -> ( %s /\\ ( g e. NN0 /\\ ( %s ` g ) =/= %s ) ) )' % (U, DPO, DS1, NONE)),
               w.inst('dpstepcases')], 'syl', '( %s -> %s )' % (U, CONC))
    # ---- case 1: the old entry
    L1 = '( %s /\\ ( T ` g ) = ( %s ` g ) )' % (U, DS1)
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L1, f))
    eq = w.s([], 'simpr', '( %s -> ( T ` g ) = ( %s ` g ) )' % (L1, DS1))
    tgnn = w.s([eq, l1(hyp, '( %s ` g ) =/= %s' % (DS1, NONE))], 'eqnetrd', '( %s -> ( T ` g ) =/= %s )' % (L1, NONE))
    ihb, _ = inst1(w, L1, l1(tbU, TB('T', 'K')), 'd', 'NN0',
                   '( ( T ` d ) =/= %s -> ( # ` ( 2nd ` ( T ` d ) ) ) <_ K )' % NONE, 'g', l1(gg, 'g e. NN0'))
    le1 = w.s([ihb, tgnn], 'mpd', '( %s -> ( # ` ( 2nd ` ( T ` g ) ) ) <_ K )' % L1)
    hq = w.s([eq], 'fveq2d', '( %s -> ( 2nd ` ( T ` g ) ) = ( 2nd ` ( %s ` g ) ) )' % (L1, DS1))
    le2 = w.s([w.s([hq], 'fveq2d', '( %s -> ( # ` ( 2nd ` ( T ` g ) ) ) = %s )' % (L1, HL)), le1],
              'eqbrtrrd', '( %s -> %s <_ K )' % (L1, HL))
    wds = w.s([w.s([hq], 'eqcomd', '( %s -> ( 2nd ` ( %s ` g ) ) = ( 2nd ` ( T ` g ) ) )' % (L1, DS1)),
               paystep(w, L1, l1(ttU, 'T e. Tbl'), l1(gg, 'g e. NN0'), tgnn, 'g')], 'eqeltrd',
              '( %s -> ( 2nd ` ( %s ` g ) ) e. Word NN0 )' % (L1, DS1))
    hlen = lenre(w, L1, wds, '( 2nd ` ( %s ` g ) )' % DS1)
    kr1 = w.s([l1(kkU, 'K e. NN0')], 'nn0red', '( %s -> K e. RR )' % L1)
    c1 = lin.linarith(w, L1, [le2], GOAL, leaves={HL: hlen, 'K': kr1})
    # ---- case 2: the new prime
    L2 = '( %s /\\ %s )' % (U, NEW)
    l2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L2, f))
    e2 = w.s([w.s([], 'simpr', '( %s -> %s )' % (L2, NEW))], 'simprd', '( %s -> ( 2nd ` ( %s ` g ) ) = <" P "> )' % (L2, DS1))
    h2 = w.s([w.s([e2], 'fveq2d', '( %s -> %s = ( # ` <" P "> ) )' % (L2, HL)),
              w.s([w.s([], 's1len', '( # ` <" P "> ) = 1')], 'a1i', '( %s -> ( # ` <" P "> ) = 1 )' % L2)], 'eqtrd',
             '( %s -> %s = 1 )' % (L2, HL))
    kr2 = w.s([l2(kkU, 'K e. NN0')], 'nn0red', '( %s -> K e. RR )' % L2)
    k0 = w.s([l2(kkU, 'K e. NN0')], 'nn0ge0d', '( %s -> 0 <_ K )' % L2)
    a2 = lin.linarith(w, L2, [k0], '1 <_ ( K + 1 )', leaves={'K': kr2})
    c2 = w.s([h2, a2], 'eqbrtrd', '( %s -> %s )' % (L2, GOAL))
    # ---- case 3: an extension
    V = '( %s /\\ r e. ( 0 ..^ L ) )' % U
    l3 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (V, f))
    L3 = '( %s /\\ %s )' % (V, RBS('r', 'g'))
    l4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L3, f))
    rn = w.s([w.s([], 'simpr', '( %s -> r e. ( 0 ..^ L ) )' % V), w.inst('elfzonn0')], 'syl', '( %s -> r e. NN0 )' % V)
    rb = w.s([], 'simpr', '( %s -> %s )' % (L3, RBS('r', 'g')))
    trnn = w.s([w.s([rb], 'simpld', '( %s -> ( ( T ` r ) =/= %s /\\ g = ( ( r x. P ) mod L ) ) )' % (L3, NONE))], 'simpld',
               '( %s -> ( T ` r ) =/= %s )' % (L3, NONE))
    hcat = w.s([rb], 'simprd', '( %s -> ( 2nd ` ( %s ` g ) ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) )' % (L3, DS1))
    wtr = paystep(w, L3, l4(l3(ttU, 'T e. Tbl'), 'T e. Tbl'), l4(rn, 'r e. NN0'), trnn, 'r')
    lc = w.s([l4(l3(ppU, 'P e. NN0'), 'P e. NN0'), wtr, w.inst('alglencs')], 'syl2anc',
             '( %s -> ( # ` ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) ) = ( ( # ` ( 2nd ` ( T ` r ) ) ) + 1 ) )' % L3)
    h3 = w.s([w.s([hcat], 'fveq2d', '( %s -> %s = ( # ` ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) ) )' % (L3, HL)), lc], 'eqtrd',
             '( %s -> %s = ( ( # ` ( 2nd ` ( T ` r ) ) ) + 1 ) )' % (L3, HL))
    ihr, _ = inst1(w, L3, l4(l3(tbU, TB('T', 'K')), TB('T', 'K')), 'd', 'NN0',
                   '( ( T ` d ) =/= %s -> ( # ` ( 2nd ` ( T ` d ) ) ) <_ K )' % NONE, 'r', l4(rn, 'r e. NN0'))
    le3 = w.s([ihr, trnn], 'mpd', '( %s -> ( # ` ( 2nd ` ( T ` r ) ) ) <_ K )' % L3)
    trr = lenre(w, L3, wtr, '( 2nd ` ( T ` r ) )')
    kr3 = w.s([l4(l3(kkU, 'K e. NN0'), 'K e. NN0')], 'nn0red', '( %s -> K e. RR )' % L3)
    a3 = lin.linarith(w, L3, [le3], '( ( # ` ( 2nd ` ( T ` r ) ) ) + 1 ) <_ ( K + 1 )',
                      leaves={'( # ` ( 2nd ` ( T ` r ) ) )': trr, 'K': kr3})
    c3 = w.s([h3, a3], 'eqbrtrd', '( %s -> %s )' % (L3, GOAL))
    rex = w.s([w.s([c3], 'ex', '( %s -> ( %s -> %s ) )' % (V, RBS('r', 'g'), GOAL))], 'rexlimdva',
              '( %s -> ( E. r e. ( 0 ..^ L ) %s -> %s ) )' % (U, RBS('r', 'g'), GOAL))
    inner = w.s([w.s([c2], 'ex', '( %s -> ( %s -> %s ) )' % (U, NEW, GOAL)), rex], 'jaod',
                '( %s -> ( ( %s \\/ E. r e. ( 0 ..^ L ) %s ) -> %s ) )' % (U, NEW, RBS('r', 'g'), GOAL))
    fin = w.s([cas, w.s([c1], 'ex', '( %s -> ( ( T ` g ) = ( %s ` g ) -> %s ) )' % (U, DS1, GOAL)), inner], 'mpjaod',
              '( %s -> %s )' % (U, GOAL))
    imp = w.s([fin], 'ex', '( %s -> ( ( %s ` g ) =/= %s -> %s ) )' % (B, DS1, NONE, GOAL))
    gen = w.s([imp], 'ralrimiva', '( %s -> %s )' % (A, TB(DS1, '( K + 1 )', 'g')))
    cv = ralconv(w, 'NN0', 'd', 'g', TB(DS1, '( K + 1 )', 'd')[len('A. d e. NN0 '):])
    w.qed([gen, w.s([cv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, TB(DS1, '( K + 1 )', 'g'), TB(DS1, '( K + 1 )')))], 'mpbid',
          '( %s -> %s )' % (A, TB(DS1, '( K + 1 )')))
    run(w)
