"""Sortie ZR: zre1n (E1 has no zero on Re > 1), zrgv (g'/g = log 2 / ( 2 ^ ( s - 1 ) - 1 ))."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift
from zc1_f import gval


def hp_of(w, A0, sc, s1, S_):
    """( A0 -> S_ e. HP0 ) from S_ e. CC and 1 < Re S_ (elhp2 at 0)"""
    c = Ctx(w, A0)
    r = c([sc], 'recld', '( Re ` %s ) e. RR' % S_)
    z = lin8(w, A0, [s1], '0 < ( Re ` %s )' % S_, {'( Re ` %s )' % S_: r})
    return c([c([sc, z], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (S_, S_)), c([c([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (S_, HP0, S_, S_))],
             'mpbird', '%s e. %s' % (S_, HP0))


def ne1_of(w, A0, sc, s1, S_):
    """( A0 -> S_ =/= 1 ) from 1 < Re S_"""
    c = Ctx(w, A0)
    r = c([sc], 'recld', '( Re ` %s ) e. RR' % S_)
    ne = c([c([], '1red', '1 e. RR'), s1], 'ltned', '1 =/= ( Re ` %s )' % S_)
    # S = 1 -> Re S = 1
    A1 = '( %s /\\ %s = 1 )' % (A0, S_)
    e = w.s([w.s([w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, S_))], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` 1 ) )' % (A1, S_)),
             w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A1)], 'eqtrd', '( %s -> ( Re ` %s ) = 1 )' % (A1, S_))
    e2 = w.s([e], 'eqcomd', '( %s -> 1 = ( Re ` %s ) )' % (A1, S_))
    ex = w.s([e2], 'ex', '( %s -> ( %s = 1 -> 1 = ( Re ` %s ) ) )' % (A0, S_, S_))
    return c([ne, c([ex], 'necon3d', '( 1 =/= ( Re ` %s ) -> %s =/= 1 )' % (S_, S_))], 'mpd', '%s =/= 1' % S_)


CHA = '( a e. NN |-> ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` a ) ) )' % U1


def gen_e1n():
    w = W('zre1n', 'The continued zeta function ` E1 ( s ) = ( s - 1 ) zeta ( s ) ` has no zero on ` 1 < Re s ` ( ~ zl1dser , ~ lchrne0 at the character mod ` 1 ` ).')
    A0 = ante_of(S['zre1n'])[0]
    c = Ctx(w, A0)
    sc = c.g('S e. CC'); s1 = c.g('1 < ( Re ` S )')
    sh = hp_of(w, A0, sc, s1, 'S')
    nx = nx1(w, A0)
    BODY = '( 1 < ( Re ` s ) -> ( %s ` s ) = ( ( s - 1 ) x. sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u s ) ) ) )' % (E1, CHA)
    ds = c([nx, w.inst('zl1dser')], 'syl', 'A. s e. %s %s' % (HP0, BODY))
    ins, new = ral_at(w, A0, ds, 's', 'S', BODY, sh)
    SM1 = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u S ) )' % CHA
    SM2 = 'sum_ k e. NN ( ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) ) x. ( k ^c -u S ) )' % U1
    ev = c([s1, ins], 'mpd', '( %s ` S ) = ( ( S - 1 ) x. %s )' % (E1, SM1))
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    CK = '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) )' % U1
    ub = ck([lift(w, nx, Ak)], 'simprd', '%s e. ( Base ` ( DChr ` 1 ) )' % U1)
    x1 = ck([ub, ck([kn], 'nnzd', 'k e. ZZ'), w.inst('zc1x1')], 'syl2anc', '%s = 1' % CK)
    ckc = ck([x1, ck([], '1cnd', '1 e. CC')], 'eqeltrd', '%s e. CC' % CK)
    import congr as _cg
    mv_, _ = _cg.mptval(w, Ak, 'a', 'NN', '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` a ) )' % U1, 'k', kn, exs=ck([ckc], 'elexd', '%s e. _V' % CK), gen=w.g)
    t1 = ck([mv_], 'oveq1d', '( ( %s ` k ) x. ( k ^c -u S ) ) = ( %s x. ( k ^c -u S ) )' % (CHA, CK))
    se = c([t1], 'sumeq2dv', '%s = %s' % (SM1, SM2))
    ne = c([c([nx, c([sc, s1], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % U1), w.inst('lchrne0')],
           'syl', '%s =/= 0' % SM2)
    ne1 = c([se, ne], 'eqnetrd', '%s =/= 0' % SM1)
    s1n = c([sc, c([], '1cnd', '1 e. CC'), ne1_of(w, A0, sc, s1, 'S')], 'subne0d', '( S - 1 ) =/= 0')
    smc = c([sc, c([], '1cnd', '1 e. CC')], 'subcld', '( S - 1 ) e. CC')
    NXZ = '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % U1
    ch = c([c([nx, c([sc, s1], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', NXZ), w.inst('zl2chs')], 'syl', tsub(ante_of(stmt('zl2chs'))[1], {'N': '1', 'X': U1, 'Z': 'S'}))
    smcc = c([ch], 'simpld', '%s e. CC' % SM1)
    pn = c([smc, smcc, s1n, ne1], 'mulne0d', '( ( S - 1 ) x. %s ) =/= 0' % SM1)
    fin = c([ev, pn], 'eqnetrd', '( %s ` S ) =/= 0' % E1)
    w.qed([fin], 'idi', S['zre1n'])
    return run8(w)


def gen_gv():
    w = W('zrgv', 'Lean ` logDeriv_gFun_eq ` : on ` 1 < Re s ` , ` g \' / g ( s ) = log 2 / ( exp ( ( s - 1 ) log 2 ) - 1 ) ` for ` g ( s ) = 1 - 2 ^ ( 1 - s ) ` ( ~ ef5gd , ~ gfunne0 , ~ cxpefd ).')
    A0 = ante_of(S['zrgv'])[0]
    c = Ctx(w, A0)
    sc = c.g('S e. CC'); s1 = c.g('1 < ( Re ` S )')
    sh = hp_of(w, A0, sc, s1, 'S')
    L = '( log ` 2 )'
    two = numst8(w, A0, '2', 'RR+')
    lr = c([two], 'relogcld', '%s e. RR' % L); lc = c([lr], 'recnd', '%s e. CC' % L)
    P = '( 2 ^c ( 1 - S ) )'
    oms = c([c([], '1cnd', '1 e. CC'), sc], 'subcld', '( 1 - S ) e. CC')
    smo = c([sc, c([], '1cnd', '1 e. CC')], 'subcld', '( S - 1 ) e. CC')
    pc = c([c([], '2cnd', '2 e. CC'), oms], 'cxpcld', '%s e. CC' % P)
    A_, B_ = '( ( 1 - S ) x. %s )' % L, '( ( S - 1 ) x. %s )' % L
    E = '( exp ` %s )' % B_
    ac = c([oms, lc], 'mulcld', '%s e. CC' % A_); bc = c([smo, lc], 'mulcld', '%s e. CC' % B_)
    ec = c([bc], 'efcld', '%s e. CC' % E)
    pe = c([c([], '2cnd', '2 e. CC'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0'), oms], 'cxpefd', '%s = ( exp ` %s )' % (P, A_))
    cl = Closure(w, A0, {'S': ('CC', sc), L: ('CC', lc)})
    cl.atom('S'); cl.atom(L)
    z = ringeq(w, A0, '( %s + %s )' % (A_, B_), '0', cl)
    ea = c([ac, bc, w.inst('efadd')], 'syl2anc', '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. %s )' % (A_, B_, A_, E))
    e0 = c([c([z], 'fveq2d', '( exp ` ( %s + %s ) ) = ( exp ` 0 )' % (A_, B_)), c.a1(w.s([], 'ef0', '( exp ` 0 ) = 1'), '( exp ` 0 ) = 1')], 'eqtrd', '( exp ` ( %s + %s ) ) = 1' % (A_, B_))
    pE1 = c([c([pe], 'oveq1d', '( %s x. %s ) = ( ( exp ` %s ) x. %s )' % (P, E, A_, E)), c([ea, e0], 'eqtr3d', '( ( exp ` %s ) x. %s ) = 1' % (A_, E))], 'eqtrd', '( %s x. %s ) = 1' % (P, E))
    EM = '( %s - 1 )' % E
    emc = c([ec, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % EM)
    pm = c([c([pc, ec, c([], '1cnd', '1 e. CC')], 'subdid', '( %s x. %s ) = ( ( %s x. %s ) - ( %s x. 1 ) )' % (P, EM, P, E, P)),
            c([pE1, c([pc], 'mulridd', '( %s x. 1 ) = %s' % (P, P))], 'oveq12d', '( ( %s x. %s ) - ( %s x. 1 ) ) = ( 1 - %s )' % (P, E, P, P))], 'eqtrd', '( %s x. %s ) = ( 1 - %s )' % (P, EM, P))
    gn = c([sc, s1, w.inst('gfunne0')], 'syl2anc', '( 1 - %s ) =/= 0' % P)
    pmn = c([pm, gn], 'eqnetrd', '( %s x. %s ) =/= 0' % (P, EM))
    emn = c([pc, emc, pmn], 'mulne0bbd', '%s =/= 0' % EM)
    gd = c([sh, w.inst('ef5gd')], 'syl', '( ( CC _D %s ) ` S ) = ( %s x. %s )' % (GF, L, P))
    gv_, VAL = gval(w, A0, sh, 'S')
    q = c([gd, gv_], 'oveq12d', '%s = ( ( %s x. %s ) / ( 1 - %s ) )' % (LDF(GF, 'S'), L, P, P))
    lpc = c([lc, pc], 'mulcld', '( %s x. %s ) e. CC' % (L, P))
    ompc = c([c([], '1cnd', '1 e. CC'), pc], 'subcld', '( 1 - %s ) e. CC' % P)
    dq = c([lpc, ompc, lc, emc, gn, emn], 'divmuleqd', '( ( ( %s x. %s ) / ( 1 - %s ) ) = ( %s / %s ) <-> ( ( %s x. %s ) x. %s ) = ( %s x. ( 1 - %s ) ) )' % (L, P, P, L, EM, L, P, EM, L, P))
    m = c([c([lc, pc, emc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (L, P, EM, L, P, EM)), c([pm], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( 1 - %s ) )' % (L, P, EM, L, P))],
          'eqtrd', '( ( %s x. %s ) x. %s ) = ( %s x. ( 1 - %s ) )' % (L, P, EM, L, P))
    qq = c([m, dq], 'mpbird', '( ( %s x. %s ) / ( 1 - %s ) ) = ( %s / %s )' % (L, P, P, L, EM))
    fin = c([emn, c([q, qq], 'eqtrd', '%s = ( %s / %s )' % (LDF(GF, 'S'), L, EM))], 'jca', ante_of(S['zrgv'])[1])
    w.qed([fin], 'idi', S['zrgv'])
    return run8(w)


def eta_nz(w, A, zc, z1, Z):
    """( A -> ( ETA ` Z ) =/= 0 ) from Z e. CC and 1 < Re Z (ef2dde's last clause)"""
    c = Ctx(w, A)
    d = stmt('ef2dde')
    P = top_and(d)
    Q = top_and(P[2])
    dd = c.a1(w.s([], 'ef2dde', d), d)
    q2 = c([c([dd], 'simp3d', P[2])], 'simprd', Q[1])
    body = Q[1][len('A. w e. %s ' % HP0):]
    zh = hp_of(w, A, zc, z1, Z)
    ins, new = ral_at(w, A, q2, 'w', Z, body, zh)
    return c([z1, ins], 'mpd', '( %s ` %s ) =/= 0' % (ETA, Z))


def gen_zs():
    from ef4_g import elrab_unpack
    w = W('zrzs', 'A zero of the eta function in the square ` SQ ( 2 + i T , 13 / 8 ) ` lies in the half-plane and has ` 3 / 8 <_ Re <_ 1 ` ( ~ ef2reb , ~ ef2dde ).')
    A0 = ante_of(S['zrzs'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); qin = c.g('Q e. %s' % ZSE('T'))
    qsq, qz, _ = elrab_unpack(w, A0, 'r', SQ13('T'), '( %s ` r ) = 0' % ETA, 'Q', qin)
    rb = c([tr, qin, w.inst('ef2reb')], 'syl2anc', tsub(ante_of(stmt('ef2reb'))[1], {'P': 'Q', 'F': ETA}))
    r38 = c([rb], 'simp1d', '( 3 / 8 ) <_ ( Re ` Q )')
    rim = c([rb], 'simp3d', '( abs ` ( ( Im ` Q ) - T ) ) <_ ( ; 1 3 / 8 )')
    cl = Closure(w, A0, {'T': ('RR', tr), '_i': ('CC', c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'))})
    cl.atom('T'); cl.atom('_i')
    SA = '( %s - ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('T')
    SB = '( %s + ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('T')
    ss = c([cl.mem(SA, 'CC'), cl.mem(SB, 'CC'), w.inst('crectss')], 'syl2anc', '%s C_ CC' % SQ13('T'))
    qc = c([ss, qsq], 'sseldd', 'Q e. CC')
    rq = c([qc], 'recld', '( Re ` Q ) e. RR')
    lv = {'( Re ` Q )': rq}
    # Re Q <_ 1: otherwise eta ( Q ) =/= 0
    A1 = '( %s /\\ 1 < ( Re ` Q ) )' % A0
    nz = eta_nz(w, A1, lift(w, qc, A1), w.s([], 'simpr', '( %s -> 1 < ( Re ` Q ) )' % A1), 'Q')
    ng = w.s([nz], 'neneqd', '( %s -> -. ( %s ` Q ) = 0 )' % (A1, ETA))
    nl = c([lift(w, qz, A1), ng], 'pm2.65da', '-. 1 < ( Re ` Q )')
    r1 = c([nl, c([rq, c([], '1red', '1 e. RR')], 'lenltd', '( ( Re ` Q ) <_ 1 <-> -. 1 < ( Re ` Q ) )')], 'mpbird', '( Re ` Q ) <_ 1')
    q0 = lin8(w, A0, [r38], '0 < ( Re ` Q )', lv)
    qh = c([c([qc, q0], 'jca', '( Q e. CC /\\ 0 < ( Re ` Q ) )'), c([c([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( Q e. %s <-> ( Q e. CC /\\ 0 < ( Re ` Q ) ) )' % HP0)], 'mpbird', 'Q e. %s' % HP0)
    G = ante_of(S['zrzs'])[1]
    P = top_and(G)
    fin = c([c([qh, qz], 'jca', P[0]), c([r38, r1], 'jca', P[1]), rim], '3jca', G)
    w.qed([fin], 'idi', S['zrzs'])
    return run8(w)


GENS = {'zre1n': gen_e1n, 'zrgv': gen_gv, 'zrzs': gen_zs}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()

