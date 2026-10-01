"""Sortie T21b: t21zse (zeroFinset_trivChar_eq, zeroSum_trivChar_eq)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *

ZA = ZF(EN, HALF, 'T')
ZB = ZF(E1, HALF, 'T')
BQ = '( ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T )' % HALF


def CND(e):
    return '( q e. CC /\\ %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (BQ, e)


def gen_zse():
    w = W('t21zse', 'The zero sum of the principal character mod ` N ` over ` [ 1 / 2 , 1 ] x. [ - T , T ] ` is that of ` E1 ` ( zeta ): same zeros, same orders (Lean ` zeroFinset_trivChar_eq ` , ` zeroSum_trivChar_eq ` ; ~ zc1tord , ~ t21zfel ).')
    A0, concl = split_imp(SB['t21zse'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    nn = u['N e. NN']; xb = u['X e. ( Base ` ( DChr ` N ) )']; x0 = u['X = %s' % U0]; tr = u['T e. RR']; yc = u['Y e. CC']
    half = s([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF)
    ela = ap(w, A0, [half, tr], 't21zfel', '( q e. %s <-> %s )' % (ZA, CND(EN)))
    elb = ap(w, A0, [half, tr], 't21zfel', '( q e. %s <-> %s )' % (ZB, CND(E1)))
    PS = '( q e. CC /\\ %s )' % BQ
    Ap = '( %s /\\ %s )' % (A0, PS)
    sp = S_(w, Ap)
    qc = sp([], 'simprl', 'q e. CC')
    rl = sp([sp([sp([], 'simprr', BQ)], 'simpld', '( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )' % HALF)], 'simpld', '%s <_ ( Re ` q )' % HALF)
    rer = sp([qc], 'recld', '( Re ` q ) e. RR')
    r0 = lin.linarith(w, Ap, [rl], '0 < ( Re ` q )', leaves={'( Re ` q )': rer})
    qh = sp([sp([qc, r0], 'jca', '( q e. CC /\\ 0 < ( Re ` q ) )'), sp([sp([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbird', 'q e. %s' % HP0)
    TO = '( ( %s holord q ) = ( %s holord q ) /\\ ( ( %s ` q ) = 0 <-> ( %s ` q ) = 0 ) )' % (EN, E1, EN, E1)
    L = lambda st: lift(w, st, Ap)
    tord = ap(w, Ap, [L(nn), L(xb), L(x0), qh], 'zc1tord', TO)
    zi = sp([tord], 'simprd', '( ( %s ` q ) = 0 <-> ( %s ` q ) = 0 )' % (EN, E1))
    zi2 = sp([zi], 'anbi2d', '( ( q =/= 1 /\\ ( %s ` q ) = 0 ) <-> ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (EN, E1))
    b1 = w.s([zi2], 'pm5.32da', '( %s -> ( ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) <-> ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) ) )' % (A0, PS, EN, PS, E1))
    d1 = s([w.s([], 'df-3an', '( %s <-> ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (CND(EN), PS, EN))], 'a1i', '( %s <-> ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (CND(EN), PS, EN))
    d2 = s([w.s([], 'df-3an', '( %s <-> ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (CND(E1), PS, E1))], 'a1i', '( %s <-> ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (CND(E1), PS, E1))
    cb = s([s([d1, b1], 'bitrd', '( %s <-> ( %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (CND(EN), PS, E1)), d2], 'bitr4d', '( %s <-> %s )' % (CND(EN), CND(E1)))
    el = s([s([ela, cb], 'bitrd', '( q e. %s <-> %s )' % (ZA, CND(E1))), elb], 'bitr4d', '( q e. %s <-> q e. %s )' % (ZA, ZB))
    zeq = s([el], 'eqrdv', '%s = %s' % (ZA, ZB))
    BODY = lambda e: '( ( %s holord q ) x. ( ( Y ^c q ) / q ) )' % e
    s1 = s([zeq], 'sumeq1d', '%s = sum_ q e. %s %s' % (SC(EN, 'T', 'Y'), ZB, BODY(EN)))
    Aq = '( %s /\\ q e. %s )' % (A0, ZB)
    sq = S_(w, Aq)
    cq = sq([sq([], 'simpr', 'q e. %s' % ZB), lift(w, elb, Aq)], 'mpbid', CND(E1))
    qc2 = sq([cq], 'simp1d', 'q e. CC')
    bq = sq([cq], 'simp2d', BQ)
    qps = sq([qc2, bq], 'jca', PS)
    # reuse the Ap facts through syl on ( Aq -> Ap )
    ap_ = sq([sq([], 'simpl', A0), qps], 'jca', Ap)
    oe = sq([ap_, w.s([tord], 'simpld', '( %s -> ( %s holord q ) = ( %s holord q ) )' % (Ap, EN, E1))], 'syl', '( %s holord q ) = ( %s holord q )' % (EN, E1))
    be = sq([oe], 'oveq1d', '%s = %s' % (BODY(EN), BODY(E1)))
    s2 = s([be], 'sumeq2dv', 'sum_ q e. %s %s = %s' % (ZB, BODY(EN), SC(E1, 'T', 'Y')))
    w.qed([s1, s2], 'eqtrd', SB['t21zse'])
    return go(w)


if __name__ == '__main__':
    gen_zse()
