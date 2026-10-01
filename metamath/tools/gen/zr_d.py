"""Sortie ZR: zrl2 (log 2 bounds), zrcos (cos bound away from 0), zrgvk (the shifted pole identities)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift


def gen_l2():
    w = W('zrl2', 'Bounds ` 1 / 3 < log 2 < 1 ` ( ~ eflegeo at ` 1 / 3 ` , ~ eflt , ~ log2ub ).')
    A0 = '2 e. RR+'
    c = Ctx(w, A0)
    L = L2
    lr = c([c([], 'id', A0)], 'relogcld', '%s e. RR' % L)
    th = numst8(w, A0, '( 1 / 3 )', 'RR')
    h0 = lin8(w, A0, [], '0 <_ ( 1 / 3 )', {})
    h1 = lin8(w, A0, [], '( 1 / 3 ) < 1', {})
    eg = c([th, h0, h1], 'eflegeo', '( exp ` ( 1 / 3 ) ) <_ ( 1 / ( 1 - ( 1 / 3 ) ) )')
    Y = '( 1 / ( 1 - ( 1 / 3 ) ) )'
    omc = c([c([], '1cnd', '1 e. CC'), numst8(w, A0, '( 1 / 3 )', 'CC')], 'subcld', '( 1 - ( 1 / 3 ) ) e. CC')
    om0 = c([lin8(w, A0, [], '0 < ( 1 - ( 1 / 3 ) )', {})], 'gt0ne0d', '( 1 - ( 1 / 3 ) ) =/= 0')
    yv = c([c([], '1cnd', '1 e. CC'), omc, om0], 'divcan1d', '( %s x. ( 1 - ( 1 / 3 ) ) ) = 1' % Y)
    yr = c([c([], '1red', '1 e. RR'), c([c([], '1red', '1 e. RR'), th], 'resubcld', '( 1 - ( 1 / 3 ) ) e. RR'), om0], 'redivcld', '%s e. RR' % Y)
    ex = c([th], 'reefcld', '( exp ` ( 1 / 3 ) ) e. RR')
    lt2 = lin8(w, A0, [eg, yv], '( exp ` ( 1 / 3 ) ) < 2', {Y: yr, '( exp ` ( 1 / 3 ) )': ex}, products=True)
    e2 = c([c([], 'id', A0), w.inst('reeflog')], 'syl', '( exp ` %s ) = 2' % L)
    lt = c([lt2, c([e2], 'eqcomd', '2 = ( exp ` %s )' % L)], 'breqtrd', '( exp ` ( 1 / 3 ) ) < ( exp ` %s )' % L)
    lo = c([lt, c([th, lr, w.inst('eflt')], 'syl2anc', '( ( 1 / 3 ) < %s <-> ( exp ` ( 1 / 3 ) ) < ( exp ` %s ) )' % (L, L))], 'mpbird', '( 1 / 3 ) < %s' % L)
    ub = c.a1(w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L), '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L)
    hi = lin8(w, A0, [ub], '%s < 1' % L, {L: lr})
    t = c([lo, hi], 'jca', S['zrl2'])
    two = w.s([], '2rp', '2 e. RR+')
    w.qed([two, t], 'ax-mp', S['zrl2'])
    return run8(w)


def gen_cos():
    w = W('zrcos', 'For ` 1 / 2 <_ abs P <_ pi ` , ` cos P < 11 / 12 ` ( ~ cosord , ~ cos01bnd at ` 1 / 2 ` ).')
    A0 = ante_of(S['zrcos'])[0]
    c = Ctx(w, A0)
    pr = c.g('P e. RR'); h1 = c.g('( 1 / 2 ) <_ ( abs ` P )'); h2 = c.g('( abs ` P ) <_ _pi')
    pc = c([pr], 'recnd', 'P e. CC')
    a = '( abs ` P )'
    ar = c([pc], 'abscld', '%s e. RR' % a)
    ao = c([pr, w.inst('absor')], 'syl', '( %s = P \\/ %s = -u P )' % (a, a))
    c1 = w.s([w.s([], 'fveq2', '( %s = P -> ( cos ` %s ) = ( cos ` P ) )' % (a, a))], 'a1i', '( %s -> ( %s = P -> ( cos ` %s ) = ( cos ` P ) ) )' % (A0, a, a))
    A2 = '( %s /\\ %s = -u P )' % (A0, a)
    c2a = w.s([w.s([], 'simpr', '( %s -> %s = -u P )' % (A2, a))], 'fveq2d', '( %s -> ( cos ` %s ) = ( cos ` -u P ) )' % (A2, a))
    c2b = w.s([lift(w, pc, A2), w.inst('cosneg')], 'syl', '( %s -> ( cos ` -u P ) = ( cos ` P ) )' % A2)
    c2 = w.s([w.s([c2a, c2b], 'eqtrd', '( %s -> ( cos ` %s ) = ( cos ` P ) )' % (A2, a))], 'ex', '( %s -> ( %s = -u P -> ( cos ` %s ) = ( cos ` P ) ) )' % (A0, a, a))
    ca = c([ao, c([c1, c2], 'jaod', '( ( %s = P \\/ %s = -u P ) -> ( cos ` %s ) = ( cos ` P ) )' % (a, a, a))], 'mpd', '( cos ` %s ) = ( cos ` P )' % a)
    pir = c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
    pgt = c.a1(w.s([w.s([], 'pigt2lt4', '( 2 < _pi /\\ _pi < 4 )')], 'simpli', '2 < _pi'), '2 < _pi')
    half = numst8(w, A0, '( 1 / 2 )', 'RR')
    lv = {a: ar, '_pi': pir}
    def icc(x, xr, lo, hi):
        return c([c([xr, lo, hi], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ _pi )' % (x, x, x)), c([c([], '0red', '0 e. RR'), pir, w.inst('elicc2')], 'syl2anc', '( %s e. ( 0 [,] _pi ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ _pi ) )' % (x, x, x, x))],
                 'mpbird', '%s e. ( 0 [,] _pi )' % x)
    ai = icc(a, ar, c([pc], 'absge0d', '0 <_ %s' % a), h2)
    hi = icc('( 1 / 2 )', half, lin8(w, A0, [], '0 <_ ( 1 / 2 )', {}), lin8(w, A0, [pgt], '( 1 / 2 ) <_ _pi', lv))
    co = c([ai, hi, w.inst('cosord')], 'syl2anc', '( %s < ( 1 / 2 ) <-> ( cos ` ( 1 / 2 ) ) < ( cos ` %s ) )' % (a, a))
    nl = c([h1, c([half, ar], 'lenltd', '( ( 1 / 2 ) <_ %s <-> -. %s < ( 1 / 2 ) )' % (a, a))], 'mpbid', '-. %s < ( 1 / 2 )' % a)
    nc = c([nl, co], 'mtbid', '-. ( cos ` ( 1 / 2 ) ) < ( cos ` %s )' % a)
    car = c([ar], 'recoscld', '( cos ` %s ) e. RR' % a)
    chr_ = c([half], 'recoscld', '( cos ` ( 1 / 2 ) ) e. RR')
    le = c([nc, c([car, chr_], 'lenltd', '( ( cos ` %s ) <_ ( cos ` ( 1 / 2 ) ) <-> -. ( cos ` ( 1 / 2 ) ) < ( cos ` %s ) )' % (a, a))], 'mpbird', '( cos ` %s ) <_ ( cos ` ( 1 / 2 ) )' % a)
    hio = c([c([half, lin8(w, A0, [], '0 < ( 1 / 2 )', {}), lin8(w, A0, [], '( 1 / 2 ) <_ 1', {})], '3jca', '( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 1 )'),
             c([c.a1(w.s([], '0xr', '0 e. RR*'), '0 e. RR*'), c([], '1red', '1 e. RR'), w.inst('elioc2')], 'syl2anc', '( ( 1 / 2 ) e. ( 0 (,] 1 ) <-> ( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 1 ) )')],
            'mpbird', '( 1 / 2 ) e. ( 0 (,] 1 )')
    CB = '( ( 1 - ( 2 x. ( ( ( 1 / 2 ) ^ 2 ) / 3 ) ) ) < ( cos ` ( 1 / 2 ) ) /\\ ( cos ` ( 1 / 2 ) ) < ( 1 - ( ( ( 1 / 2 ) ^ 2 ) / 3 ) ) )'
    cb = c([c([hio, w.inst('cos01bnd')], 'syl', CB)], 'simprd', '( cos ` ( 1 / 2 ) ) < ( 1 - ( ( ( 1 / 2 ) ^ 2 ) / 3 ) )')
    fin = lin8(w, A0, [c([ca], 'eqcomd', '( cos ` P ) = ( cos ` %s )' % a), le, cb], '( cos ` P ) < ( ; 1 1 / ; 1 2 )',
               {'( cos ` P )': c([pr], 'recoscld', '( cos ` P ) e. RR'), '( cos ` %s )' % a: car, '( cos ` ( 1 / 2 ) )': chr_}, products=True)
    w.qed([fin], 'idi', S['zrcos'])
    return run8(w)


def gen_gvk():
    w = W('zrgvk', 'The pole ` s_K = 1 + 2 pi i K / log 2 ` of ` g \' / g ` : ` ( S - s_K ) log 2 = W log 2 + i phi ` with ` phi = T log 2 - 2 pi K ` , and ` exp ( ( S - 1 ) log 2 ) = exp ( ( S - s_K ) log 2 ) ` ( ~ efper ).')
    A0 = ante_of(S['zrgvk'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); wr = c.g('W e. RR'); kz = c.g('K e. ZZ')
    L = L2
    two = numst8(w, A0, '2', 'RR+')
    lrp = c([numst8(w, A0, '2', 'RR'), c.a1(w.s([], '1lt2', '1 < 2'), '1 < 2')], 'rplogcld', '%s e. RR+' % L)
    lc = c([c([lrp], 'rpred', '%s e. RR' % L)], 'recnd', '%s e. CC' % L)
    l0 = c([lrp], 'rpne0d', '%s =/= 0' % L)
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    pic = c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')
    kc = c([kz], 'zcnd', 'K e. CC')
    N2 = '( 2 x. ( _pi x. K ) )'
    n2c = c([c([], '2cnd', '2 e. CC'), c([pic, kc], 'mulcld', '( _pi x. K ) e. CC')], 'mulcld', '%s e. CC' % N2)
    D = '( %s / %s )' % (N2, L)
    dc = c([n2c, lc, l0], 'divcld', '%s e. CC' % D)
    dl = c([n2c, lc, l0], 'divcan1d', '( %s x. %s ) = %s' % (D, L, N2))
    cl = Closure(w, A0, {'W': ('CC', c([wr], 'recnd', 'W e. CC')), 'T': ('CC', c([tr], 'recnd', 'T e. CC')), L: ('CC', lc), '_i': ('CC', ic), D: ('CC', dc), '_pi': ('CC', pic), 'K': ('CC', kc)})
    for a in ('W', 'T', L, '_i', D, '_pi', 'K'):
        cl.atom(a)
    SKK = SK('K')
    LHS = '( ( %s - %s ) x. %s )' % (SW, SKK, L)
    r1 = ringeq(w, A0, LHS, '( ( W x. %s ) + ( _i x. ( ( T x. %s ) - ( %s x. %s ) ) ) )' % (L, L, D, L), cl)
    r1b = c([r1, c([c([c([dl], 'oveq2d', '( ( T x. %s ) - ( %s x. %s ) ) = %s' % (L, D, L, PHI('K')))], 'oveq2d', '( _i x. ( ( T x. %s ) - ( %s x. %s ) ) ) = ( _i x. %s )' % (L, D, L, PHI('K')))],
                'oveq2d', '( ( W x. %s ) + ( _i x. ( ( T x. %s ) - ( %s x. %s ) ) ) ) = ( ( W x. %s ) + ( _i x. %s ) )' % (L, L, D, L, L, PHI('K')))], 'eqtrd',
            '%s = ( ( W x. %s ) + ( _i x. %s ) )' % (LHS, L, PHI('K')))
    L1 = '( ( %s - 1 ) x. %s )' % (SW, L)
    TP = '( ( _i x. ( 2 x. _pi ) ) x. K )'
    r2 = ringeq(w, A0, L1, '( %s + ( _i x. ( %s x. %s ) ) )' % (LHS, D, L), cl)
    r3 = ringeq(w, A0, '( _i x. %s )' % N2, TP, cl)
    r4 = c([c([dl], 'oveq2d', '( _i x. ( %s x. %s ) ) = ( _i x. %s )' % (D, L, N2)), r3], 'eqtrd', '( _i x. ( %s x. %s ) ) = %s' % (D, L, TP))
    r5 = c([r2, c([r4], 'oveq2d', '( %s + ( _i x. ( %s x. %s ) ) ) = ( %s + %s )' % (LHS, D, L, LHS, TP))], 'eqtrd', '%s = ( %s + %s )' % (L1, LHS, TP))
    lhc = cl.mem(LHS, 'CC')
    ep = c([c([r5], 'fveq2d', '( exp ` %s ) = ( exp ` ( %s + %s ) )' % (L1, LHS, TP)), c([lhc, kz, w.inst('efper')], 'syl2anc', '( exp ` ( %s + %s ) ) = ( exp ` %s )' % (LHS, TP, LHS))],
           'eqtrd', '( exp ` %s ) = ( exp ` %s )' % (L1, LHS))
    fin = c([r1b, ep], 'jca', ante_of(S['zrgvk'])[1])
    w.qed([fin], 'idi', S['zrgvk'])
    return run8(w)


GENS = {'zrl2': gen_l2, 'zrcos': gen_cos, 'zrgvk': gen_gvk}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
