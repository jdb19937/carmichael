"""Sortie EF3: the sigma pigeonhole (Lean exists_good_sigma): the total weight of the left-edge squares (ef3sgw),
the regularised average (ef3sgi), the pointwise conversion (ef3sgp), the assembly (ef3sgt, ef3sig)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
from c10_f import crfacts
import lin
lin.FASTPATH = True
import ef3_a, ef3_c, ef3_e

WSUM = 'sum_ j e. ( 0 ..^ M ) sum_ q e. %s %s' % (ZK(), WQ())
S['ef3sgw'] = '( ( %s /\\ %s ) -> %s <_ ( ; ; ; ; 1 2 0 0 0 x. ( %s ^ 2 ) ) )' % (DD(), SGH, WSUM, LT4)
AT4 = '( A x. ( T + 4 ) )'


def sgh_parts(w, A, sgh):
    s = St(w, A)
    t, p, m = conj_split(w, A, sgh)
    tr, t2 = conj_split(w, A, t)
    pr, pp = conj_split(w, A, p); p1, p0 = conj_split(w, A, pp)
    mn, mm = conj_split(w, A, m); m0, m2 = conj_split(w, A, mm)
    return dict(tr=tr, t2=t2, pr=pr, p1=p1, p0=p0, mn=mn, m0=m0, m2=m2)


def lt4_facts(w, A, ar, a1, tr, t2):
    """AT4 e. RR+, LT4 e. RR, 0 <_ LT4, 1 <_ AT4-type facts; closure with atoms A, T"""
    s = St(w, A)
    cl = Closure(w, A, {'A': ('RR', ar), 'T': ('RR', tr)}); cl.atom('A'); cl.atom('T')
    atr = s([ar, s([tr, numst(w, A, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')], 'remulcld', '%s e. RR' % AT4)
    a6 = lin.linarith(w, A, [a1, t2], '6 <_ %s' % AT4, closure=cl, products=True)
    atp = s([atr, lin8(w, A, [a6], '0 < %s' % AT4, {AT4: atr})], 'elrpd', '%s e. RR+' % AT4)
    lr = s([atp], 'relogcld', '%s e. RR' % LT4)
    l0 = s([atr, lin8(w, A, [a6], '1 <_ %s' % AT4, {AT4: atr})], 'logge0d', '0 <_ %s' % LT4)
    return dict(cl=cl, atr=atr, a6=a6, atp=atp, lr=lr, l0=l0)


def gen_sgw():
    w = W('ef3sgw', 'Lean ` exists_good_sigma ` ( ` hW ` , ` hharm ` ): the total weight ` sum_j sum_q m_q / ( 1 + abs Im q ) ` of the squares about the window centres is at most ` 12000 log ^ 2 ( A ( T + 4 ) ) ` .')
    A0, G = ante_of(S['ef3sgw'])
    s = St(w, A0)
    dd = s([], 'simpl', DD()); sgh = s([], 'simpr', SGH)
    d = sgh_parts(w, A0, sgh)
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    f = lt4_facts(w, A0, ar, a1, d['tr'], d['t2'])
    Ak = '( %s /\\ j e. ( 0 ..^ M ) )' % A0
    sk = St(w, Ak)
    Lk = lambda st: lift(w, st, Ak)
    jin = sk([], 'simpr', 'j e. ( 0 ..^ M )')
    jn = sk([jin, w.inst('elfzonn0')], 'syl', 'j e. NN0')
    jr = sk([jn], 'nn0red', 'j e. RR')
    j1 = sk([sk([jin, w.inst('fzofzp1')], 'syl', '( j + 1 ) e. ( 0 ... M )'), w.inst('elfzle2')], 'syl', '( j + 1 ) <_ M')
    t0 = T0()
    t0r = sk([sk([Lk(d['pr']), sk([jr, numst(w, Ak, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '%s e. RR' % WLO()), numst(w, Ak, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % t0)
    zwa = tsub(ante_of(S['ef3zw'])[0], {'T': t0, 'G': ZK()})
    zw = sk([sk([sk([Lk(dd), t0r], 'jca', '( %s /\\ %s e. RR )' % (DD(), t0)), sk([w.s([], 'ssid', '%s C_ %s' % (ZK(), ZK()))], 'a1i', '%s C_ %s' % (ZK(), ZK()))], 'jca', zwa), w.inst('ef3zw')], 'syl',
            tsub(ante_of(S['ef3zw'])[1], {'T': t0, 'G': ZK()}))
    at0 = sk([sk([t0r], 'recnd', '%s e. CC' % t0)], 'abscld', '( abs ` %s ) e. RR' % t0)
    mr = sk([Lk(d['mn'])], 'nn0red', 'M e. RR')
    lvj = {'j': jr, 'P': Lk(d['pr']), 'T': Lk(d['tr']), 'M': mr}
    ab = sk([sk([lin8(w, Ak, [Lk(d['p1']), sk([jn], 'nn0ge0d', '0 <_ j')], '-u ( T + 2 ) <_ %s' % t0, lvj), lin8(w, Ak, [j1, Lk(d['m2'])], '%s <_ ( T + 2 )' % t0, lvj)], 'jca', '( -u ( T + 2 ) <_ %s /\\ %s <_ ( T + 2 ) )' % (t0, t0)),
             sk([t0r, sk([Lk(d['tr']), numst(w, Ak, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')], 'absled', '( ( abs ` %s ) <_ ( T + 2 ) <-> ( -u ( T + 2 ) <_ %s /\\ %s <_ ( T + 2 ) ) )' % (t0, t0, t0))], 'mpbird', '( abs ` %s ) <_ ( T + 2 )' % t0)
    X1 = XA(t0)
    a0 = lin8(w, Ak, [Lk(a1)], '0 <_ A', {'A': Lk(ar)})
    x1le = sk([sk([at0, numst(w, Ak, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % t0), sk([Lk(d['tr']), numst(w, Ak, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), Lk(ar), a0,
               lin8(w, Ak, [ab], '( ( abs ` %s ) + 2 ) <_ ( T + 4 )' % t0, {'( abs ` %s )' % t0: at0, 'T': Lk(d['tr'])})], 'lemul2ad', '%s <_ %s' % (X1, AT4))
    x1r = sk([Lk(ar), sk([at0, numst(w, Ak, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % t0)], 'remulcld', '%s e. RR' % X1)
    x1p = sk([x1r, lin.linarith(w, Ak, [Lk(a1), sk([sk([t0r], 'recnd', '%s e. CC' % t0)], 'absge0d', '0 <_ ( abs ` %s )' % t0)], '0 < %s' % X1,
                                  closure=Closure(w, Ak, {'A': ('RR', Lk(ar)), '( abs ` %s )' % t0: ('RR', at0)}), products=True)], 'elrpd', '%s e. RR+' % X1)
    lx = sk([x1le, sk([x1p, Lk(f['atp'])], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ %s )' % (X1, AT4, X1, LT4))], 'mpbid', '( log ` %s ) <_ %s' % (X1, LT4))
    b = '( 1 + ( abs ` %s ) )' % t0
    bp = sk([sk([numst(w, Ak, '1', 'RR'), at0], 'readdcld', '%s e. RR' % b), lin8(w, Ak, [sk([sk([t0r], 'recnd', '%s e. CC' % t0)], 'absge0d', '0 <_ ( abs ` %s )' % t0)], '0 < %s' % b, {'( abs ` %s )' % t0: at0})], 'elrpd', '%s e. RR+' % b)
    N1 = '( ; ; ; 2 4 0 0 x. ( log ` %s ) )' % X1
    N2 = '( ; ; ; 2 4 0 0 x. %s )' % LT4
    lx1 = sk([x1p], 'relogcld', '( log ` %s ) e. RR' % X1)
    nle = lin8(w, Ak, [lx], '%s <_ %s' % (N1, N2), {'( log ` %s )' % X1: lx1, LT4: Lk(f['lr'])})
    n1r = sk([numst(w, Ak, '; ; ; 2 4 0 0', 'RR'), lx1], 'remulcld', '%s e. RR' % N1)
    n2r = sk([numst(w, Ak, '; ; ; 2 4 0 0', 'RR'), Lk(f['lr'])], 'remulcld', '%s e. RR' % N2)
    dle = sk([n1r, n2r, bp, nle], 'lediv1dd', '( %s / %s ) <_ ( %s / %s )' % (N1, b, N2, b))
    SB = 'sum_ q e. %s %s' % (ZK(), WQ())
    RB = '( %s x. ( 1 / %s ) )' % (N2, b)
    dr1 = sk([sk([n2r], 'recnd', '%s e. CC' % N2), sk([sk([bp], 'rpred', '%s e. RR' % b)], 'recnd', '%s e. CC' % b), sk([bp], 'rpne0d', '%s =/= 0' % b)], 'divrecd', '( %s / %s ) = %s' % (N2, b, RB))
    # WQ real on ZK
    Akq = '( %s /\\ q e. %s )' % (Ak, ZK())
    sq = St(w, Akq)
    Lq = lambda st: lift(w, st, Akq)
    zs = sk([sk([Lk(dd), t0r], 'jca', '( %s /\\ %s e. RR )' % (DD(), t0)), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': t0}))
    zf, zo, _ = conj_split(w, Ak, zs)
    qin = sq([], 'simpr', 'q e. %s' % ZK())
    on = sq([Lq(zo), qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    z = zs_unpack(w, Akq, 'F', t0, Lq(t0r), 'q', qin)
    iq = sq([z['cc']], 'imcld', '( Im ` q ) e. RR')
    aq = sq([sq([iq], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    apq = sq([sq([numst(w, Akq, '1', 'RR'), aq], 'readdcld', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR'), lin8(w, Akq, [sq([sq([iq], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < ( 1 + ( abs ` ( Im ` q ) ) )', {'( abs ` ( Im ` q ) )': aq})], 'elrpd', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR+')
    wqr = sq([sq([on], 'nnred', '( F holord q ) e. RR'), apq], 'rerpdivcld', '%s e. RR' % WQ())
    sbr = sk([zf, wqr], 'fsumrecl', '%s e. RR' % SB)
    d1r = sk([n1r, bp], 'rerpdivcld', '( %s / %s ) e. RR' % (N1, b))
    d2r = sk([n2r, bp], 'rerpdivcld', '( %s / %s ) e. RR' % (N2, b))
    p1 = sk([sbr, d1r, d2r, zw, dle], 'letrd', '%s <_ ( %s / %s )' % (SB, N2, b))
    pf = sk([p1, dr1], 'breqtrd', '%s <_ %s' % (SB, RB))
    fz = s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin')
    XB = '( 1 / %s )' % b
    xbr = sk([bp], 'rpreccld', '%s e. RR+' % XB)
    rbr = sk([n2r, sk([xbr], 'rpred', '%s e. RR' % XB)], 'remulcld', '%s e. RR' % RB)
    t1 = s([fz, sbr, rbr, pf], 'fsumle', '%s <_ sum_ j e. ( 0 ..^ M ) %s' % (WSUM, RB))
    HS = 'sum_ j e. ( 0 ..^ M ) %s' % XB
    n20 = s([numst(w, A0, '; ; ; 2 4 0 0', 'RR'), f['lr']], 'remulcld', '%s e. RR' % N2)
    t2 = s([fz, s([n20], 'recnd', '%s e. CC' % N2), sk([sk([xbr], 'rpred', '%s e. RR' % XB)], 'recnd', '%s e. CC' % XB)], 'fsummulc2', '( %s x. %s ) = sum_ j e. ( 0 ..^ M ) %s' % (N2, HS, RB))
    W2 = '( T + 2 )'
    HA = tsub(ante_of(S['ef3hm'])[0], {'W': W2})
    ha1, ha2 = top_and(HA)
    lv0 = {'P': d['pr'], 'T': d['tr']}
    hm = s([s([s([d['pr'], d['mn'], s([d['tr'], numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % W2)], '3jca', ha1),
               s([s([d['p0'], d['m0']], 'jca', top_and(ha2)[0]), s([lin8(w, A0, [d['p1']], '-u %s <_ P' % W2, lv0), d['m2']], 'jca', top_and(ha2)[1])], 'jca', ha2)], 'jca', HA), w.inst('ef3hm')], 'syl',
           tsub(ante_of(S['ef3hm'])[1], {'W': W2}))
    L1W = '( log ` ( 1 + %s ) )' % W2
    w1p = s([s([numst(w, A0, '1', 'RR'), s([d['tr'], numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % W2)], 'readdcld', '( 1 + %s ) e. RR' % W2), lin8(w, A0, [d['t2']], '0 < ( 1 + %s )' % W2, {'T': d['tr']})], 'elrpd', '( 1 + %s ) e. RR+' % W2)
    au = lin.linarith(w, A0, [a1, d['t2']], '( 1 + %s ) <_ %s' % (W2, AT4), closure=f['cl'], products=True)
    lw = s([au, s([w1p, f['atp']], 'logled', '( ( 1 + %s ) <_ %s <-> %s <_ %s )' % (W2, AT4, L1W, LT4))], 'mpbid', '%s <_ %s' % (L1W, LT4))
    hsr = s([fz, sk([xbr], 'rpred', '%s e. RR' % XB)], 'fsumrecl', '%s e. RR' % HS)
    hs5 = lin8(w, A0, [hm, lw], '%s <_ ( 5 x. %s )' % (HS, LT4), {HS: hsr, L1W: s([w1p], 'relogcld', '%s e. RR' % L1W), LT4: f['lr']})
    k0 = lin8(w, A0, [f['l0']], '0 <_ %s' % N2, {LT4: f['lr']})
    t3 = s([hsr, s([numst(w, A0, '5', 'RR'), f['lr']], 'remulcld', '( 5 x. %s ) e. RR' % LT4), n20, k0, hs5], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 5 x. %s ) )' % (N2, HS, N2, LT4))
    cl1 = Closure(w, A0, {LT4: ('RR', f['lr'])}); cl1.atom(LT4)
    sqv = s([s([f['lr']], 'recnd', '%s e. CC' % LT4)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (LT4, LT4, LT4))
    K12 = '; ; ; ; 1 2 0 0 0'
    e1 = ringeq(w, A0, '( %s x. ( 5 x. %s ) )' % (N2, LT4), '( %s x. ( %s x. %s ) )' % (K12, LT4, LT4), cl1)
    e2 = s([e1, s([sqv], 'oveq2d', '( %s x. ( %s ^ 2 ) ) = ( %s x. ( %s x. %s ) )' % (K12, LT4, K12, LT4, LT4))], 'eqtr4d', '( %s x. ( 5 x. %s ) ) = ( %s x. ( %s ^ 2 ) )' % (N2, LT4, K12, LT4))
    t4 = s([t3, e2], 'breqtrd', '( %s x. %s ) <_ ( %s x. ( %s ^ 2 ) )' % (N2, HS, K12, LT4))
    t5 = s([t1, t2], 'breqtrrd', '%s <_ ( %s x. %s )' % (WSUM, N2, HS))
    ssr = s([fz, sbr], 'fsumrecl', '%s e. RR' % WSUM)
    w.qed([ssr, s([n20, hsr], 'remulcld', '( %s x. %s ) e. RR' % (N2, HS)), s([numst(w, A0, K12, 'RR'), s([f['lr']], 'resqcld', '( %s ^ 2 ) e. RR' % LT4)], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (K12, LT4)), t5, t4], 'letrd', S['ef3sgw'])
    return run8(w)


IS = '( ( 9 / ; 1 6 ) (,) ( 5 / 8 ) )'
BASE = lambda d, q='q', E='E': '( ( ( abs ` ( %s - ( Re ` %s ) ) ) + %s ) ^c -u ( 1 / 2 ) )' % (d, q, E)
HT = lambda d, q='q', E='E': '( %s x. %s )' % (WQ(q), BASE(d, q, E))
HE = lambda d, E='E': 'sum_ j e. ( 0 ..^ M ) sum_ q e. %s %s' % (ZK(), HT(d, 'q', E))
S['ef3sgi'] = ('( ( ( %s /\\ %s ) /\\ ( E e. RR+ /\\ E <_ ( ; 1 5 / ; 1 6 ) ) ) -> ( ( d e. %s |-> %s ) e. L^1 /\\ S. %s %s _d d <_ ( 8 x. %s ) ) )') % (
    DD(), SGH, IS, HE('d'), IS, HE('d'), WSUM)


def zk_facts(w, A, dd, pr, jr, qin):
    """under A (with j real, q e. ZK): dict wqr (WQ e. RR), wq0 (0 <_ WQ), rer (Re q e. RR), rlo, rhi (3/8 <_ Re q <_ 29/8), iq, t0r"""
    sA = St(w, A)
    t0 = T0()
    t0r = sA([sA([pr, sA([jr, numst(w, A, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '%s e. RR' % WLO()), numst(w, A, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % t0)
    zs = sA([sA([dd, t0r], 'jca', '( %s /\\ %s e. RR )' % (DD(), t0)), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': t0}))
    zf, zo, _ = conj_split(w, A, zs)
    on = sA([zo, qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    z = zs_unpack(w, A, 'F', t0, t0r, 'q', qin)
    reb = sA([sA([t0r, qin], 'jca', '( %s e. RR /\\ q e. %s )' % (t0, ZK())), w.inst('ef2reb')], 'syl', tsub(ante_of(stmt('ef2reb'))[1], {'P': 'q', 'T': t0}))
    rlo, rhi, imb = conj_split(w, A, reb)
    iq = sA([z['cc']], 'imcld', '( Im ` q ) e. RR')
    aq = sA([sA([iq], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    apq = sA([sA([numst(w, A, '1', 'RR'), aq], 'readdcld', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR'), lin8(w, A, [sA([sA([iq], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < ( 1 + ( abs ` ( Im ` q ) ) )', {'( abs ` ( Im ` q ) )': aq})], 'elrpd', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR+')
    mr = sA([on], 'nnred', '( F holord q ) e. RR')
    wqr = sA([mr, apq], 'rerpdivcld', '%s e. RR' % WQ())
    m0 = lin8(w, A, [sA([on], 'nnge1d', '1 <_ ( F holord q )')], '0 <_ ( F holord q )', {'( F holord q )': mr})
    wq0 = sA([mr, apq, m0], 'divge0d', '0 <_ %s' % WQ())
    return dict(wqr=wqr, wq0=wq0, rer=sA([z['cc']], 'recld', '( Re ` q ) e. RR'), rlo=rlo, rhi=rhi, iq=iq, aq=aq, apq=apq, on=on, mr=mr, imb=imb, t0r=t0r, zf=zf, cc=z['cc'])


def zk_t0r(w, A, pr, jr, j='j'):
    sA = St(w, A)
    return sA([sA([pr, sA([jr, numst(w, A, '2', 'RR+')], 'rerpdivcld', '( %s / 2 ) e. RR' % j)], 'readdcld', '%s e. RR' % WLO(j)), numst(w, A, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % T0(j))


def zk_facts_v(w, A, dd, pr, jr, qin, q='q', j='j'):
    """zk_facts for element letter q and window index j"""
    sA = St(w, A)
    t0 = T0(j)
    t0r = zk_t0r(w, A, pr, jr, j)
    Z = ZS('F', t0)
    zs = sA([sA([dd, t0r], 'jca', '( %s /\\ %s e. RR )' % (DD(), t0)), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': t0}))
    zf, zo, _ = conj_split(w, A, zs)
    eqq = w.s([w.s([], 'oveq2', '( q = %s -> ( F holord q ) = ( F holord %s ) )' % (q, q))], 'eleq1d', '( q = %s -> ( ( F holord q ) e. NN <-> ( F holord %s ) e. NN ) )' % (q, q))
    on = sA([eqq, zo, qin], 'rspcdva', '( F holord %s ) e. NN' % q) if q != 'q' else sA([zo, qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    z = zs_unpack(w, A, 'F', t0, t0r, q, qin)
    reb = sA([sA([t0r, qin], 'jca', '( %s e. RR /\\ %s e. %s )' % (t0, q, Z)), w.inst('ef2reb')], 'syl', tsub(ante_of(stmt('ef2reb'))[1], {'P': q, 'T': t0}))
    rlo, rhi, imb = conj_split(w, A, reb)
    iq = sA([z['cc']], 'imcld', '( Im ` %s ) e. RR' % q)
    aq = sA([sA([iq], 'recnd', '( Im ` %s ) e. CC' % q)], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % q)
    a = '( 1 + ( abs ` ( Im ` %s ) ) )' % q
    apq = sA([sA([numst(w, A, '1', 'RR'), aq], 'readdcld', '%s e. RR' % a), lin8(w, A, [sA([sA([iq], 'recnd', '( Im ` %s ) e. CC' % q)], 'absge0d', '0 <_ ( abs ` ( Im ` %s ) )' % q)], '0 < %s' % a, {'( abs ` ( Im ` %s ) )' % q: aq})], 'elrpd', '%s e. RR+' % a)
    mr = sA([on], 'nnred', '( F holord %s ) e. RR' % q)
    wqr = sA([mr, apq], 'rerpdivcld', '%s e. RR' % WQ(q))
    m0 = lin8(w, A, [sA([on], 'nnge1d', '1 <_ ( F holord %s )' % q)], '0 <_ ( F holord %s )' % q, {'( F holord %s )' % q: mr})
    wq0 = sA([mr, apq, m0], 'divge0d', '0 <_ %s' % WQ(q))
    return dict(wqr=wqr, wq0=wq0, rer=sA([z['cc']], 'recld', '( Re ` %s ) e. RR' % q), rlo=rlo, rhi=rhi, iq=iq, aq=aq, apq=apq, on=on, mr=mr, imb=imb, t0r=t0r, zf=zf, cc=z['cc'])


def gen_sgi():
    w = W('ef3sgi', 'Lean ` exists_good_sigma ` ( ` havg ` ): the regularised functional ` sum w_q ( abs ( d - Re q ) + E ) ^ ( -1/2 ) ` is integrable on ` ( 9 / 16 , 5 / 8 ) ` with integral at most ` 8 ` times the total weight ( ~ ef1ir with ` D = 49 / 16 ` , ` E <_ 15 / 16 ` ).')
    A0, G = ante_of(S['ef3sgi'])
    s = St(w, A0)
    ds = s([], 'simpl', '( %s /\\ %s )' % (DD(), SGH))
    dd, sgh = conj_split(w, A0, ds)
    ee = s([], 'simpr', '( E e. RR+ /\\ E <_ ( ; 1 5 / ; 1 6 ) )')
    ep, e15 = conj_split(w, A0, ee)
    d = sgh_parts(w, A0, sgh)
    Aj = '( %s /\\ j e. ( 0 ..^ M ) )' % A0
    sj = St(w, Aj)
    Lj = lambda st: lift(w, st, Aj)
    jr = sj([sj([sj([], 'simpr', 'j e. ( 0 ..^ M )'), w.inst('elfzonn0')], 'syl', 'j e. NN0')], 'nn0red', 'j e. RR')
    Ajq = '( %s /\\ q e. %s )' % (Aj, ZK())
    sq = St(w, Ajq)
    Lq = lambda st: lift(w, st, Ajq)
    qin = sq([], 'simpr', 'q e. %s' % ZK())
    zk = zk_facts(w, Ajq, Lq(Lj(dd)), Lq(Lj(d['pr'])), Lq(jr), qin)
    zfj = conj_split(w, Aj, sj([sj([Lj(dd), zk_t0(w, Aj, Lj(d['pr']), jr) if False else sj([sj([Lj(d['pr']), sj([jr, numst(w, Aj, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '%s e. RR' % WLO()), numst(w, Aj, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % T0())], 'jca', '( %s /\\ %s e. RR )' % (DD(), T0())), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': T0()})))[0]
    # ef1ir
    IRA = tsub(ante_of(stmt('ef1ir'))[0], {'B': '( Re ` q )', 'P': '( 9 / ; 1 6 )', 'Q': '( 5 / 8 )', 'D': '( ; 4 9 / ; 1 6 )', 't': 'd'})
    IRC = tsub(ante_of(stmt('ef1ir'))[1], {'B': '( Re ` q )', 'P': '( 9 / ; 1 6 )', 'Q': '( 5 / 8 )', 'D': '( ; 4 9 / ; 1 6 )', 't': 'd'})
    i1, i2 = top_and(IRA)
    i2a, i2b = top_and(i2)
    lvq = {'( Re ` q )': zk['rer']}
    ira = sq([sq([zk['rer'], Lq(Lj(ep))], 'jca', i1), sq([sq([numst(w, Ajq, '( 9 / ; 1 6 )', 'RR'), numst(w, Ajq, '( 5 / 8 )', 'RR'), lin8(w, Ajq, [], '( 9 / ; 1 6 ) <_ ( 5 / 8 )', {})], '3jca', i2a),
                                                        sq([numst(w, Ajq, '( ; 4 9 / ; 1 6 )', 'RR'), lin8(w, Ajq, [zk['rlo']], '( ( 5 / 8 ) - ( Re ` q ) ) <_ ( ; 4 9 / ; 1 6 )', lvq), lin8(w, Ajq, [zk['rhi']], '( ( Re ` q ) - ( 9 / ; 1 6 ) ) <_ ( ; 4 9 / ; 1 6 )', lvq)], '3jca', i2b)], 'jca', i2)],
            'jca', IRA)
    ir = sq([ira, w.inst('ef1ir')], 'syl', IRC)
    ibb, ile = conj_split(w, Ajq, ir)
    IB = 'S. %s %s _d d' % (IS, BASE('d'))
    # ( 49/16 + E ) ^c ( 1 / 2 ) <_ 2
    DE = '( ( ; 4 9 / ; 1 6 ) + E )'
    er = Lq(Lj(s([ep], 'rpred', 'E e. RR')))
    der = sq([numst(w, Ajq, '( ; 4 9 / ; 1 6 )', 'RR'), er], 'readdcld', '%s e. RR' % DE)
    lvE = {'E': er}
    c2 = sq([sq([sq([der, lin8(w, Ajq, [Lq(Lj(s([ep], 'rpge0d', '0 <_ E')))], '0 <_ %s' % DE, lvE)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (DE, DE)),
                  sq([numst(w, Ajq, '4', 'RR'), lin8(w, Ajq, [], '0 <_ 4', {})], 'jca', '( 4 e. RR /\\ 0 <_ 4 )'), numst(w, Ajq, '( 1 / 2 )', 'RR+')], '3jca',
                 '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( 4 e. RR /\\ 0 <_ 4 ) /\\ ( 1 / 2 ) e. RR+ )' % (DE, DE)), w.inst('cxple2')], 'syl', '( %s <_ 4 <-> ( %s ^c ( 1 / 2 ) ) <_ ( 4 ^c ( 1 / 2 ) ) )' % (DE, DE))
    c3 = sq([lin8(w, Ajq, [Lq(Lj(e15))], '%s <_ 4' % DE, lvE), c2], 'mpbid', '( %s ^c ( 1 / 2 ) ) <_ ( 4 ^c ( 1 / 2 ) )' % DE)
    s4 = w.s([w.s([w.s([], '4cn', '4 e. CC'), w.inst('cxpsqrt')], 'ax-mp', '( 4 ^c ( 1 / 2 ) ) = ( sqrt ` 4 )'), w.s([], 'sqrt4', '( sqrt ` 4 ) = 2')], 'eqtri', '( 4 ^c ( 1 / 2 ) ) = 2')
    c4 = sq([c3, sq([s4], 'a1i', '( 4 ^c ( 1 / 2 ) ) = 2')], 'breqtrd', '( %s ^c ( 1 / 2 ) ) <_ 2' % DE)
    dh = sq([sq([der, lin8(w, Ajq, [Lq(Lj(s([ep], 'rpge0d', '0 <_ E')))], '0 < %s' % DE, lvE)], 'elrpd', '%s e. RR+' % DE), numst(w, Ajq, '( 1 / 2 )', 'RR')], 'rpcxpcld', '( %s ^c ( 1 / 2 ) ) e. RR+' % DE)
    # base pointwise real, under ( Ajq /\ d e. IS )
    Ad = '( %s /\\ d e. %s )' % (Ajq, IS)
    sd = St(w, Ad)
    Ld = lambda st: lift(w, st, Ad)
    dr = sd([sd([w.s([], 'ioossre', '%s C_ RR' % IS)], 'a1i', '%s C_ RR' % IS), sd([], 'simpr', 'd e. %s' % IS)], 'sseldd', 'd e. RR')
    adr = sd([sd([sd([dr, Ld(zk['rer'])], 'resubcld', '( d - ( Re ` q ) ) e. RR')], 'recnd', '( d - ( Re ` q ) ) e. CC')], 'abscld', '( abs ` ( d - ( Re ` q ) ) ) e. RR')
    ade = sd([adr, Ld(er)], 'readdcld', '( ( abs ` ( d - ( Re ` q ) ) ) + E ) e. RR')
    adp = sd([ade, lin8(w, Ad, [sd([sd([sd([dr, Ld(zk['rer'])], 'resubcld', '( d - ( Re ` q ) ) e. RR')], 'recnd', '( d - ( Re ` q ) ) e. CC')], 'absge0d', '0 <_ ( abs ` ( d - ( Re ` q ) ) )'), Ld(Lq(Lj(s([ep], 'rpgt0d', '0 < E'))))],
                                '0 < ( ( abs ` ( d - ( Re ` q ) ) ) + E )', {'( abs ` ( d - ( Re ` q ) ) )': adr, 'E': Ld(er)})], 'elrpd', '( ( abs ` ( d - ( Re ` q ) ) ) + E ) e. RR+')
    br = sd([sd([adp, sd([numst(w, Ad, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % BASE('d'))], 'rpred', '%s e. RR' % BASE('d'))
    htr = sd([Ld(zk['wqr']), br], 'remulcld', '%s e. RR' % HT('d'))
    ibt = sq([sq([zk['wqr']], 'recnd', '%s e. CC' % WQ()), sd([br], 'recnd', '%s e. CC' % BASE('d')), ibb], 'iblmulc2', '( d e. %s |-> %s ) e. L^1' % (IS, HT('d')))
    ibr = sq([br, ibb], 'itgrecl', '%s e. RR' % IB)
    mc = sq([sq([zk['wqr']], 'recnd', '%s e. CC' % WQ()), sd([br], 'recnd', '%s e. CC' % BASE('d')), ibb], 'itgmulc2', '( %s x. %s ) = S. %s %s _d d' % (WQ(), IB, IS, HT('d')))
    dhr = sq([dh], 'rpred', '( %s ^c ( 1 / 2 ) ) e. RR' % DE)
    m42 = sq([dhr, numst(w, Ajq, '2', 'RR'), numst(w, Ajq, '4', 'RR'), numst(w, Ajq, '4', 'ge0'), c4], 'lemul2ad', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) <_ ( 4 x. 2 )' % DE)
    m8 = sq([m42, sq([w.s([], '4t2e8', '( 4 x. 2 ) = 8')], 'a1i', '( 4 x. 2 ) = 8')], 'breqtrd', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) <_ 8' % DE)
    b8 = sq([ibr, sq([numst(w, Ajq, '4', 'RR'), dhr], 'remulcld', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) e. RR' % DE), numst(w, Ajq, '8', 'RR'), ile, m8], 'letrd', '%s <_ 8' % IB)
    tb = sq([ibr, numst(w, Ajq, '8', 'RR'), zk['wqr'], zk['wq0'], b8], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 8 )' % (WQ(), IB, WQ()))
    IT = 'S. %s %s _d d' % (IS, HT('d'))
    tb2 = sq([mc, tb], 'eqbrtrrd', '%s <_ ( %s x. 8 )' % (IT, WQ()))
    # inner sum over q ( context Aj )
    htc_d = sd([htr], 'recnd', '%s e. CC' % HT('d'))
    htc_x = w.s([w.s([htc_d], 'anasss', '( ( %s /\\ ( q e. %s /\\ d e. %s ) ) -> %s e. CC )' % (Aj, ZK(), IS, HT('d')))], 'ancom2s', '( ( %s /\\ ( d e. %s /\\ q e. %s ) ) -> %s e. CC )' % (Aj, IS, ZK(), HT('d')))
    isv = sj([w.s([], 'ioombl', '%s e. dom vol' % IS)], 'a1i', '%s e. dom vol' % IS)
    SQH = 'sum_ q e. %s %s' % (ZK(), HT('d'))
    inner = sj([isv, zfj, htc_x, ibt], 'itgfsum', '( ( d e. %s |-> %s ) e. L^1 /\\ S. %s %s _d d = sum_ q e. %s %s )' % (IS, SQH, IS, SQH, ZK(), IT))
    in1, in2 = conj_split(w, Aj, inner)
    itr = sq([br and htr and sq([sd([htr], 'id', 'x') if False else None], 'id', 'x') if False else None], 'id', 'x') if False else sq([htr, ibt], 'itgrecl', '%s e. RR' % IT)
    SW = 'sum_ q e. %s %s' % (ZK(), WQ())
    w8r = sq([zk['wqr'], numst(w, Ajq, '8', 'RR')], 'remulcld', '( %s x. 8 ) e. RR' % WQ())
    ib1 = sj([zfj, itr, w8r, tb2], 'fsumle', 'sum_ q e. %s %s <_ sum_ q e. %s ( %s x. 8 )' % (ZK(), IT, ZK(), WQ()))
    mc1 = sj([zfj, numst(w, Aj, '8', 'CC'), sq([zk['wqr']], 'recnd', '%s e. CC' % WQ())], 'fsummulc1', '( %s x. 8 ) = sum_ q e. %s ( %s x. 8 )' % (SW, ZK(), WQ()))
    ib2 = sj([ib1, mc1], 'breqtrrd', 'sum_ q e. %s %s <_ ( %s x. 8 )' % (ZK(), IT, SW))
    # outer sum over j ( context A0 )
    htr_q = w.s([htr], 'an32s', '( ( ( %s /\\ d e. %s ) /\\ q e. %s ) -> %s e. RR )' % (Aj, IS, ZK(), HT('d')))
    Adj = '( %s /\\ d e. %s )' % (Aj, IS)
    sqc = St(w, Adj)([lift(w, zfj, Adj), St(w, '( %s /\\ q e. %s )' % (Adj, ZK()))([htr_q], 'recnd', '%s e. CC' % HT('d'))], 'fsumcl', '%s e. CC' % SQH)
    sqc_x = w.s([w.s([sqc], 'anasss', '( ( %s /\\ ( j e. ( 0 ..^ M ) /\\ d e. %s ) ) -> %s e. CC )' % (A0, IS, SQH))], 'ancom2s', '( ( %s /\\ ( d e. %s /\\ j e. ( 0 ..^ M ) ) ) -> %s e. CC )' % (A0, IS, SQH))
    fz = s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin')
    ISV = s([w.s([], 'ioombl', '%s e. dom vol' % IS)], 'a1i', '%s e. dom vol' % IS)
    IS2 = 'S. %s %s _d d' % (IS, SQH)
    outer = s([ISV, fz, sqc_x, in1], 'itgfsum', '( ( d e. %s |-> %s ) e. L^1 /\\ S. %s %s _d d = sum_ j e. ( 0 ..^ M ) %s )' % (IS, HE('d'), IS, HE('d'), IS2))
    ou1, ou2 = conj_split(w, A0, outer)
    SSI = 'sum_ j e. ( 0 ..^ M ) sum_ q e. %s %s' % (ZK(), IT)
    se = s([in2], 'sumeq2dv', 'sum_ j e. ( 0 ..^ M ) %s = %s' % (IS2, SSI))
    swr = sj([zfj, zk_wq_lift(w) if False else sq([zk['wqr']], 'id', 'x') if False else zk['wqr']], 'fsumrecl', '%s e. RR' % SW)
    sir = sj([zfj, itr], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (ZK(), IT))
    ob1 = s([fz, sir, sj([swr, numst(w, Aj, '8', 'RR')], 'remulcld', '( %s x. 8 ) e. RR' % SW), ib2], 'fsumle', '%s <_ sum_ j e. ( 0 ..^ M ) ( %s x. 8 )' % (SSI, SW))
    mc2 = s([fz, numst(w, A0, '8', 'CC'), sj([swr], 'recnd', '%s e. CC' % SW)], 'fsummulc1', '( %s x. 8 ) = sum_ j e. ( 0 ..^ M ) ( %s x. 8 )' % (WSUM, SW))
    ob2 = s([ob1, mc2], 'breqtrrd', '%s <_ ( %s x. 8 )' % (SSI, WSUM))
    wsr = s([fz, swr], 'fsumrecl', '%s e. RR' % WSUM)
    ob3 = s([ob2, s([s([wsr], 'recnd', '%s e. CC' % WSUM), numst(w, A0, '8', 'CC')], 'mulcomd', '( %s x. 8 ) = ( 8 x. %s )' % (WSUM, WSUM))], 'breqtrd', '%s <_ ( 8 x. %s )' % (SSI, WSUM))
    fin = s([s([ou2, se], 'eqtrd', 'S. %s %s _d d = %s' % (IS, HE('d'), SSI)), ob3], 'eqbrtrd', 'S. %s %s _d d <_ ( 8 x. %s )' % (IS, HE('d'), WSUM))
    w.qed([ou1, fin], 'jca', S['ef3sgi'])
    return run8(w)


EK = lambda K='K', N='N': '( 1 / ( 2 x. ( ( %s x. %s ) ^ 2 ) ) )' % (K, N)
S['ef3sgp'] = ('( ( ( X e. RR /\\ 0 <_ X ) /\\ ( K e. RR+ /\\ N e. RR+ /\\ W e. RR ) /\\ ( 1 <_ ( K x. W ) /\\ ( W x. ( ( X + %s ) ^c -u ( 1 / 2 ) ) ) <_ N ) ) -> '
               '( 0 < X /\\ ( X ^c -u ( 1 / 2 ) ) <_ ( ( 3 / 2 ) x. ( ( X + %s ) ^c -u ( 1 / 2 ) ) ) ) )') % (EK(), EK())


def negcxp(w, A, Yv, yp):
    """( A -> ( Y ^c -u ( 1 / 2 ) ) = ( 1 / ( sqrt ` Y ) ) ) from yp : Y e. RR+"""
    sA = St(w, A)
    yc = sA([sA([yp], 'rpred', '%s e. RR' % Yv)], 'recnd', '%s e. CC' % Yv)
    e1 = sA([yc, sA([yp], 'rpne0d', '%s =/= 0' % Yv), numst(w, A, '( 1 / 2 )', 'CC'), w.inst('cxpneg')], 'syl3anc', '( %s ^c -u ( 1 / 2 ) ) = ( 1 / ( %s ^c ( 1 / 2 ) ) )' % (Yv, Yv))
    e2 = sA([sA([yc, w.inst('cxpsqrt')], 'syl', '( %s ^c ( 1 / 2 ) ) = ( sqrt ` %s )' % (Yv, Yv))], 'oveq2d', '( 1 / ( %s ^c ( 1 / 2 ) ) ) = ( 1 / ( sqrt ` %s ) )' % (Yv, Yv))
    return sA([e1, e2], 'eqtrd', '( %s ^c -u ( 1 / 2 ) ) = ( 1 / ( sqrt ` %s ) )' % (Yv, Yv))


def gen_sgp():
    w = W('ef3sgp', 'The regularisation trick of EF1 section 6: if one term ` W ( X + E ) ^ ( -1/2 ) ` of the pigeonholed functional is at most ` N ` , ` W >_ 1 / K ` and ` E = 1 / ( 2 ( K N ) ^ 2 ) ` , then ` X >_ E > 0 ` and ` X ^ ( -1/2 ) <_ ( 3 / 2 ) ( X + E ) ^ ( -1/2 ) ` .')
    A0, G = ante_of(S['ef3sgp'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    xr, x0 = conj_split(w, A0, s([], 'simp1', H1))
    kp, np_, wr = conj_split(w, A0, s([], 'simp2', H2))
    kw1, tn = conj_split(w, A0, s([], 'simp3', H3))
    E_ = EK()
    Q = '( K x. N )'
    qp = s([kp, np_], 'rpmulcld', '%s e. RR+' % Q)
    Q2 = '( %s ^ 2 )' % Q
    q2p = s([qp, numst(w, A0, '2', 'ZZ')], 'rpexpcld', '%s e. RR+' % Q2)
    Z = '( 1 / %s )' % Q2
    zp = s([q2p], 'rpreccld', '%s e. RR+' % Z)
    zr = s([zp], 'rpred', '%s e. RR' % Z)
    q2c = s([s([q2p], 'rpred', '%s e. RR' % Q2)], 'recnd', '%s e. CC' % Q2)
    ek1 = s([numst(w, A0, '1', 'CC'), numst(w, A0, '2', 'CC'), q2c, s([numst(w, A0, '2', 'RR+')], 'rpne0d', '2 =/= 0'), s([q2p], 'rpne0d', '%s =/= 0' % Q2)], 'divdiv1d', '( ( 1 / 2 ) / %s ) = %s' % (Q2, E_))
    ek2 = s([numst(w, A0, '( 1 / 2 )', 'CC'), q2c, s([q2p], 'rpne0d', '%s =/= 0' % Q2)], 'divrecd', '( ( 1 / 2 ) / %s ) = ( ( 1 / 2 ) x. %s )' % (Q2, Z))
    ekz = s([s([ek1], 'eqcomd', '%s = ( ( 1 / 2 ) / %s )' % (E_, Q2)), ek2], 'eqtrd', '%s = ( ( 1 / 2 ) x. %s )' % (E_, Z))
    Y = '( X + %s )' % E_
    ekr = s([ekz, s([numst(w, A0, '( 1 / 2 )', 'RR'), zr], 'remulcld', '( ( 1 / 2 ) x. %s ) e. RR' % Z)], 'eqeltrd', '%s e. RR' % E_)
    lv = {'X': xr, Z: zr, E_: ekr}
    yr = s([xr, ekr], 'readdcld', '%s e. RR' % Y)
    yp = s([yr, lin8(w, A0, [x0, ekz, s([zp], 'rpgt0d', '0 < %s' % Z)], '0 < %s' % Y, lv)], 'elrpd', '%s e. RR+' % Y)
    sY = '( sqrt ` %s )' % Y
    syr = s([yr, s([yp], 'rpge0d', '0 <_ %s' % Y)], 'resqrtcld', '%s e. RR' % sY)
    syp = s([syr, s([yp], 'sqrtgt0d', '0 < %s' % sY)], 'elrpd', '%s e. RR+' % sY)
    ny = negcxp(w, A0, Y, yp)
    # W / sY <_ N  ->  W <_ sY N
    t1 = s([tn, s([ny], 'oveq2d', '( W x. ( %s ^c -u ( 1 / 2 ) ) ) = ( W x. ( 1 / %s ) )' % (Y, sY))], 'eqbrtrrd' if False else 'id', 'x') if False else \
        s([s([ny], 'oveq2d', '( W x. ( %s ^c -u ( 1 / 2 ) ) ) = ( W x. ( 1 / %s ) )' % (Y, sY)), tn], 'eqbrtrrd', '( W x. ( 1 / %s ) ) <_ N' % sY)
    dv = s([s([wr], 'recnd', 'W e. CC'), s([syr], 'recnd', '%s e. CC' % sY), s([syp], 'rpne0d', '%s =/= 0' % sY)], 'divrecd', '( W / %s ) = ( W x. ( 1 / %s ) )' % (sY, sY))
    t2 = s([dv, t1], 'eqbrtrd', '( W / %s ) <_ N' % sY)
    nr = s([np_], 'rpred', 'N e. RR')
    t3 = s([t2, s([wr, nr, syp], 'ledivmuld', '( ( W / %s ) <_ N <-> W <_ ( %s x. N ) )' % (sY, sY))], 'mpbid', 'W <_ ( %s x. N )' % sY)
    kr = s([kp], 'rpred', 'K e. RR')
    t4 = s([wr, s([syr, nr], 'remulcld', '( %s x. N ) e. RR' % sY), kr, s([kp], 'rpge0d', '0 <_ K'), t3], 'lemul2ad', '( K x. W ) <_ ( K x. ( %s x. N ) )' % sY)
    cl = Closure(w, A0, {'K': ('RR', kr), 'N': ('RR', nr), sY: ('RR', syr)})
    for a in ('K', 'N', sY):
        cl.atom(a)
    e4 = ringeq(w, A0, '( K x. ( %s x. N ) )' % sY, '( %s x. %s )' % (Q, sY), cl)
    t5 = s([kw1, s([t4, e4], 'breqtrd', '( K x. W ) <_ ( %s x. %s )' % (Q, sY))], 'id', 'x') if False else None
    qr = s([qp], 'rpred', '%s e. RR' % Q)
    kwr = s([kr, wr], 'remulcld', '( K x. W ) e. RR')
    qsr = s([qr, syr], 'remulcld', '( %s x. %s ) e. RR' % (Q, sY))
    t5 = s([numst(w, A0, '1', 'RR'), kwr, qsr, kw1, s([t4, e4], 'breqtrd', '( K x. W ) <_ ( %s x. %s )' % (Q, sY))], 'letrd', '1 <_ ( %s x. %s )' % (Q, sY))
    # square
    sq1 = s([t5, s([numst(w, A0, '1', 'RR'), qsr, numst(w, A0, '1', 'ge0'), s([qr, syr, s([qp], 'rpge0d', '0 <_ %s' % Q), s([syp], 'rpge0d', '0 <_ %s' % sY)], 'mulge0d', '0 <_ ( %s x. %s )' % (Q, sY))], 'le2sqd',
                    '( 1 <_ ( %s x. %s ) <-> ( 1 ^ 2 ) <_ ( ( %s x. %s ) ^ 2 ) )' % (Q, sY, Q, sY))], 'mpbid', '( 1 ^ 2 ) <_ ( ( %s x. %s ) ^ 2 )' % (Q, sY))
    e5 = s([s([qr], 'recnd', '%s e. CC' % Q), s([syr], 'recnd', '%s e. CC' % sY)], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( %s x. ( %s ^ 2 ) )' % (Q, sY, Q2, sY))
    e6 = s([s([yr, s([yp], 'rpge0d', '0 <_ %s' % Y)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (Y, Y)), w.inst('resqrtth')], 'syl', '( %s ^ 2 ) = %s' % (sY, Y))
    e7 = s([e5, s([e6], 'oveq2d', '( %s x. ( %s ^ 2 ) ) = ( %s x. %s )' % (Q2, sY, Q2, Y))], 'eqtrd', '( ( %s x. %s ) ^ 2 ) = ( %s x. %s )' % (Q, sY, Q2, Y))
    sq2 = s([s([s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1'), sq1], 'eqbrtrrd', '1 <_ ( ( %s x. %s ) ^ 2 )' % (Q, sY)), e7], 'breqtrd', '1 <_ ( %s x. %s )' % (Q2, Y))
    sq3 = s([sq2, s([numst(w, A0, '1', 'RR'), yr, q2p], 'ledivmuld', '( ( 1 / %s ) <_ %s <-> 1 <_ ( %s x. %s ) )' % (Q2, Y, Q2, Y))], 'mpbird', '%s <_ %s' % (Z, Y))
    xpos = lin8(w, A0, [sq3, ekz, s([zp], 'rpgt0d', '0 < %s' % Z)], '0 < X', lv)
    y2x = lin8(w, A0, [sq3, ekz], '%s <_ ( 2 x. X )' % Y, lv)
    # sY <_ ( 3 / 2 ) sX
    sX = '( sqrt ` X )'
    xp = s([xr, xpos], 'elrpd', 'X e. RR+')
    sxr = s([xr, x0], 'resqrtcld', '%s e. RR' % sX)
    sxp = s([sxr, s([xp], 'sqrtgt0d', '0 < %s' % sX)], 'elrpd', '%s e. RR+' % sX)
    H = '( ( 3 / 2 ) x. %s )' % sX
    hr = s([numst(w, A0, '( 3 / 2 )', 'RR'), sxr], 'remulcld', '%s e. RR' % H)
    e8 = s([numst(w, A0, '( 3 / 2 )', 'CC'), s([sxr], 'recnd', '%s e. CC' % sX)], 'sqmuld', '( %s ^ 2 ) = ( ( ( 3 / 2 ) ^ 2 ) x. ( %s ^ 2 ) )' % (H, sX))
    e9 = s([s([xr, x0], 'jca', '( X e. RR /\\ 0 <_ X )'), w.inst('resqrtth')], 'syl', '( %s ^ 2 ) = X' % sX)
    cl2 = Closure(w, A0, {'X': ('RR', xr)}); cl2.atom('X')
    e10 = s([s([e8, s([e9], 'oveq2d', '( ( ( 3 / 2 ) ^ 2 ) x. ( %s ^ 2 ) ) = ( ( ( 3 / 2 ) ^ 2 ) x. X )' % sX)], 'eqtrd', '( %s ^ 2 ) = ( ( ( 3 / 2 ) ^ 2 ) x. X )' % H),
             s([s([w.s([], 'sq3halves' if False else 'id', 'x') if False else numst(w, A0, '( 3 / 2 )', 'CC')], 'sqvald', '( ( 3 / 2 ) ^ 2 ) = ( ( 3 / 2 ) x. ( 3 / 2 ) )')], 'oveq1d', '( ( ( 3 / 2 ) ^ 2 ) x. X ) = ( ( ( 3 / 2 ) x. ( 3 / 2 ) ) x. X )')], 'eqtrd',
            '( %s ^ 2 ) = ( ( ( 3 / 2 ) x. ( 3 / 2 ) ) x. X )' % H)
    h2 = s([e10, ringeq(w, A0, '( ( ( 3 / 2 ) x. ( 3 / 2 ) ) x. X )', '( ( 9 / 4 ) x. X )', cl2)], 'eqtrd', '( %s ^ 2 ) = ( ( 9 / 4 ) x. X )' % H)
    y94 = lin8(w, A0, [y2x, x0], '%s <_ ( ( 9 / 4 ) x. X )' % Y, lv)
    s2le = s([s([e6, y94], 'eqbrtrd', '( %s ^ 2 ) <_ ( ( 9 / 4 ) x. X )' % sY), h2], 'breqtrrd', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (sY, H))
    syh = s([s2le, s([syr, hr, s([syp], 'rpge0d', '0 <_ %s' % sY), s([numst(w, A0, '( 3 / 2 )', 'RR'), sxr, numst(w, A0, '( 3 / 2 )', 'ge0'), s([sxp], 'rpge0d', '0 <_ %s' % sX)], 'mulge0d', '0 <_ %s' % H)], 'le2sqd',
                          '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (sY, H, sY, H))], 'mpbird', '%s <_ %s' % (sY, H))
    hp = s([numst(w, A0, '( 3 / 2 )', 'RR+'), sxp], 'rpmulcld', '%s e. RR+' % H)
    f1 = s([syp, hp, numst(w, A0, '( 3 / 2 )', 'RR'), numst(w, A0, '( 3 / 2 )', 'ge0'), syh], 'lediv2ad', '( ( 3 / 2 ) / %s ) <_ ( ( 3 / 2 ) / %s )' % (H, sY))
    f2 = s([numst(w, A0, '1', 'CC'), s([sxr], 'recnd', '%s e. CC' % sX), numst(w, A0, '( 3 / 2 )', 'CC'), s([sxp], 'rpne0d', '%s =/= 0' % sX), s([numst(w, A0, '( 3 / 2 )', 'RR+')], 'rpne0d', '( 3 / 2 ) =/= 0')], 'divcan5d',
           '( ( ( 3 / 2 ) x. 1 ) / %s ) = ( 1 / %s )' % (H, sX))
    f3 = s([s([s([numst(w, A0, '( 3 / 2 )', 'CC')], 'mulridd', '( ( 3 / 2 ) x. 1 ) = ( 3 / 2 )')], 'oveq1d', '( ( ( 3 / 2 ) x. 1 ) / %s ) = ( ( 3 / 2 ) / %s )' % (H, H)), f2], 'eqtr3d', '( ( 3 / 2 ) / %s ) = ( 1 / %s )' % (H, sX))
    f4 = s([numst(w, A0, '( 3 / 2 )', 'CC'), s([syr], 'recnd', '%s e. CC' % sY), s([syp], 'rpne0d', '%s =/= 0' % sY)], 'divrecd', '( ( 3 / 2 ) / %s ) = ( ( 3 / 2 ) x. ( 1 / %s ) )' % (sY, sY))
    f5 = s([s([f3, f1], 'eqbrtrrd', '( 1 / %s ) <_ ( ( 3 / 2 ) / %s )' % (sX, sY)), f4], 'breqtrd', '( 1 / %s ) <_ ( ( 3 / 2 ) x. ( 1 / %s ) )' % (sX, sY))
    nx = negcxp(w, A0, 'X', xp)
    f6 = s([s([nx, f5], 'eqbrtrd', '( X ^c -u ( 1 / 2 ) ) <_ ( ( 3 / 2 ) x. ( 1 / %s ) )' % sY), s([ny], 'oveq2d', '( ( 3 / 2 ) x. ( %s ^c -u ( 1 / 2 ) ) ) = ( ( 3 / 2 ) x. ( 1 / %s ) )' % (Y, sY))], 'breqtrrd',
           '( X ^c -u ( 1 / 2 ) ) <_ ( ( 3 / 2 ) x. ( %s ^c -u ( 1 / 2 ) ) )' % Y)
    w.qed([xpos, f6], 'jca', S['ef3sgp'])
    return run8(w)


KT = '( T + 6 )'
ET = EK(KT, 'N')
I_ = '( 0 ..^ M )'
HEio = 'sum_ i e. %s sum_ o e. %s %s' % (I_, ZK('i'), HT('X', 'o', ET))
HSGT = ['( ph -> ( %s /\\ %s ) )' % (DD(), SGH), '( ph -> X e. RR )', '( ph -> N e. RR+ )', '( ph -> %s <_ N )' % HEio]
S['ef3sgt'] = '( ph -> ( A. j e. %s A. q e. %s ( Re ` q ) =/= X /\\ %s <_ ( ( 3 / 2 ) x. N ) ) )' % (I_, ZK(), PHI('X'))


def gen_sgt():
    from c0lib import hyp
    w = W('ef3sgt', 'Lean ` exists_good_sigma ` , the pointwise step: at a point ` X ` where the regularised functional with ` E = 1 / ( 2 ( ( T + 6 ) N ) ^ 2 ) ` is at most ` N ` , no zero of the window squares has real part ` X ` and Lean\'s functional is at most ` ( 3 / 2 ) N ` ( ~ ef3sgp on each term).')
    h = [hyp(w, str(n + 1), 'ef3sgt.%d' % (n + 1), f) for n, f in enumerate(HSGT)]
    h = [w.s([x], 'idi', f) for x, f in zip(h, HSGT)]
    A0 = 'ph'
    s = St(w, A0)
    dd, sgh = conj_split(w, A0, h[0])
    xr, np_, hn = h[1], h[2], h[3]
    d = sgh_parts(w, A0, sgh)
    I = I_
    fz0 = s([w.s([], 'fzofi', '%s e. Fin' % I)], 'a1i', '%s e. Fin' % I)
    kp = s([s([d['tr'], numst(w, A0, '6', 'RR')], 'readdcld', '%s e. RR' % KT), lin8(w, A0, [d['t2']], '0 < %s' % KT, {'T': d['tr']})], 'elrpd', '%s e. RR+' % KT)
    q2 = s([s([kp, np_], 'rpmulcld', '( %s x. N ) e. RR+' % KT), numst(w, A0, '2', 'ZZ')], 'rpexpcld', '( ( %s x. N ) ^ 2 ) e. RR+' % KT)
    etp = s([s([numst(w, A0, '2', 'RR+'), q2], 'rpmulcld', '( 2 x. ( ( %s x. N ) ^ 2 ) ) e. RR+' % KT)], 'rpreccld', '%s e. RR+' % ET)

    def ht_real(A, qv, zkq):
        sA = St(w, A)
        ad = '( abs ` ( X - ( Re ` %s ) ) )' % qv
        xq = sA([sA([lift(w, xr, A), zkq['rer']], 'resubcld', '( X - ( Re ` %s ) ) e. RR' % qv)], 'recnd', '( X - ( Re ` %s ) ) e. CC' % qv)
        adr = sA([xq], 'abscld', '%s e. RR' % ad)
        ad0 = sA([xq], 'absge0d', '0 <_ %s' % ad)
        er = sA([lift(w, etp, A)], 'rpred', '%s e. RR' % ET)
        yp = sA([sA([adr, er], 'readdcld', '( %s + %s ) e. RR' % (ad, ET)), lin8(w, A, [ad0, sA([lift(w, etp, A)], 'rpgt0d', '0 < %s' % ET)], '0 < ( %s + %s )' % (ad, ET), {ad: adr, ET: er})], 'elrpd', '( %s + %s ) e. RR+' % (ad, ET))
        bp = sA([yp, sA([numst(w, A, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % BASE('X', qv, ET))
        br = sA([bp], 'rpred', '%s e. RR' % BASE('X', qv, ET))
        hr = sA([zkq['wqr'], br], 'remulcld', '%s e. RR' % HT('X', qv, ET))
        h0 = sA([zkq['wqr'], br, zkq['wq0'], sA([bp], 'rpge0d', '0 <_ %s' % BASE('X', qv, ET))], 'mulge0d', '0 <_ %s' % HT('X', qv, ET))
        return hr, h0, adr, ad0, bp
    def win(A, v):
        sA = St(w, A)
        vin = sA([], 'simpr', '%s e. %s' % (v, I))
        vr = sA([sA([vin, w.inst('elfzonn0')], 'syl', '%s e. NN0' % v)], 'nn0red', '%s e. RR' % v)
        zs = sA([sA([lift(w, dd, A), zk_t0r(w, A, lift(w, d['pr'], A), vr, v)], 'jca', '( %s /\\ %s e. RR )' % (DD(), T0(v))), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': T0(v)}))
        return vin, vr, conj_split(w, A, zs)[0]
    A1 = '( %s /\\ j e. %s )' % (A0, I)
    s1 = St(w, A1)
    L1 = lambda st: lift(w, st, A1)
    jin, jr, zfin = win(A1, 'j')
    A2 = '( %s /\\ q e. %s )' % (A1, ZK())
    s2 = St(w, A2)
    L2 = lambda st: lift(w, st, A2)
    qin = s2([], 'simpr', 'q e. %s' % ZK())
    zk = zk_facts_v(w, A2, L2(L1(dd)), L2(L1(d['pr'])), L2(jr), qin)
    htr, ht0, adr, ad0, bp = ht_real(A2, 'q', zk)
    # rename the hypothesis sum to letters c , g
    SGc = lambda c: 'sum_ g e. %s %s' % (ZK(c), HT('X', 'g', ET))
    HEcg = 'sum_ c e. %s %s' % (I, SGc('c'))
    SOi = 'sum_ o e. %s %s' % (ZK('i'), HT('X', 'o', ET))
    e_ic, _ = w.congr(SOi, {'i': 'c'}, 'i = c', {'i': w.s([], 'id', '( i = c -> i = c )')})
    r1 = w.s([e_ic], 'cbvsumv', '%s = sum_ c e. %s sum_ o e. %s %s' % (HEio, I, ZK('c'), HT('X', 'o', ET)))
    e_og, _ = w.congr(HT('X', 'o', ET), {'o': 'g'}, 'o = g', {'o': w.s([], 'id', '( o = g -> o = g )')})
    r2 = w.s([w.s([w.s([e_og], 'cbvsumv', 'sum_ o e. %s %s = %s' % (ZK('c'), HT('X', 'o', ET), SGc('c')))], 'a1i', '( c e. %s -> sum_ o e. %s %s = %s )' % (I, ZK('c'), HT('X', 'o', ET), SGc('c')))], 'sumeq2i',
             'sum_ c e. %s sum_ o e. %s %s = %s' % (I, ZK('c'), HT('X', 'o', ET), HEcg))
    rr = w.s([r1, r2], 'eqtri', '%s = %s' % (HEio, HEcg))
    # term <_ inner sum ( fsumge1 over g )
    A3 = '( %s /\\ g e. %s )' % (A2, ZK())
    s3 = St(w, A3)
    zkg = zk_facts_v(w, A3, lift(w, dd, A3), lift(w, d['pr'], A3), lift(w, jr, A3), s3([], 'simpr', 'g e. %s' % ZK()), 'g')
    hrg, h0g, _, _, _ = ht_real(A3, 'g', zkg)
    e_gq, _ = w.congr(HT('X', 'g', ET), {'g': 'q'}, 'g = q', {'g': w.s([], 'id', '( g = q -> g = q )')})
    g1 = s2([L2(zfin), hrg, h0g, e_gq, qin], 'fsumge1', '%s <_ %s' % (HT('X', 'q', ET), SGc('j')))
    # inner sum <_ outer sum ( fsumge1 over c )
    A4 = '( %s /\\ c e. %s )' % (A1, I)
    s4 = St(w, A4)
    cin, cr, zfc = win(A4, 'c')
    A5 = '( %s /\\ g e. %s )' % (A4, ZK('c'))
    s5 = St(w, A5)
    zkc = zk_facts_v(w, A5, lift(w, dd, A5), lift(w, d['pr'], A5), lift(w, cr, A5), s5([], 'simpr', 'g e. %s' % ZK('c')), 'g', 'c')
    hrc, h0c, _, _, _ = ht_real(A5, 'g', zkc)
    sgcr = s4([zfc, hrc], 'fsumrecl', '%s e. RR' % SGc('c'))
    sgc0 = s4([zfc, hrc, h0c], 'fsumge0', '0 <_ %s' % SGc('c'))
    e_cj, _ = w.congr(SGc('c'), {'c': 'j'}, 'c = j', {'c': w.s([], 'id', '( c = j -> c = j )')})
    g2 = s1([L1(fz0), sgcr, sgc0, e_cj, jin], 'fsumge1', '%s <_ %s' % (SGc('j'), HEcg))
    # chain to N
    A3j = '( %s /\\ g e. %s )' % (A1, ZK())
    zkj = zk_facts_v(w, A3j, lift(w, dd, A3j), lift(w, d['pr'], A3j), lift(w, jr, A3j), St(w, A3j)([], 'simpr', 'g e. %s' % ZK()), 'g')
    hrj, _, _, _, _ = ht_real(A3j, 'g', zkj)
    sgjr = s1([zfin, hrj], 'fsumrecl', '%s e. RR' % SGc('j'))
    A0c = '( %s /\\ c e. %s )' % (A0, I)
    cin0, cr0, zfc0 = win(A0c, 'c')
    A0cg = '( %s /\\ g e. %s )' % (A0c, ZK('c'))
    zk0 = zk_facts_v(w, A0cg, lift(w, dd, A0cg), lift(w, d['pr'], A0cg), lift(w, cr0, A0cg), St(w, A0cg)([], 'simpr', 'g e. %s' % ZK('c')), 'g', 'c')
    hr0, _, _, _, _ = ht_real(A0cg, 'g', zk0)
    her = s([fz0, St(w, A0c)([zfc0, hr0], 'fsumrecl', '%s e. RR' % SGc('c'))], 'fsumrecl', '%s e. RR' % HEcg)
    hn2 = s([s([rr], 'a1i', '%s = %s' % (HEio, HEcg)), hn], 'eqbrtrrd', '%s <_ N' % HEcg)
    nr = s([np_], 'rpred', 'N e. RR')
    tn = s2([htr, L2(sgjr), lift(w, her, A2), g1, L2(g2)], 'letrd', '%s <_ %s' % (HT('X', 'q', ET), HEcg))
    tn2 = s2([htr, lift(w, her, A2), lift(w, nr, A2), tn, lift(w, hn2, A2)], 'letrd', '%s <_ N' % HT('X', 'q', ET))
    # the conclusion's sum with letters j , q
    SQ_ = 'sum_ q e. %s %s' % (ZK(), HT('X', 'q', ET))
    sqr = s1([zfin, htr], 'fsumrecl', '%s e. RR' % SQ_)
    herjq = s([fz0, sqr], 'fsumrecl', '%s e. RR' % HE('X', ET))
    e_ji, _ = w.congr(SQ_, {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    q1 = w.s([e_ji], 'cbvsumv', '%s = sum_ i e. %s sum_ q e. %s %s' % (HE('X', ET), I, ZK('i'), HT('X', 'q', ET)))
    e_qo, _ = w.congr(HT('X', 'q', ET), {'q': 'o'}, 'q = o', {'q': w.s([], 'id', '( q = o -> q = o )')})
    q2_ = w.s([w.s([w.s([e_qo], 'cbvsumv', 'sum_ q e. %s %s = %s' % (ZK('i'), HT('X', 'q', ET), SOi))], 'a1i', '( i e. %s -> sum_ q e. %s %s = %s )' % (I, ZK('i'), HT('X', 'q', ET), SOi))], 'sumeq2i',
              'sum_ i e. %s sum_ q e. %s %s = %s' % (I, ZK('i'), HT('X', 'q', ET), HEio))
    hnjq = s([s([w.s([q1, q2_], 'eqtri', '%s = %s' % (HE('X', ET), HEio))], 'a1i', '%s = %s' % (HE('X', ET), HEio)), hn], 'eqbrtrd', '%s <_ N' % HE('X', ET))
    # 1 <_ K WQ
    t0 = T0()
    t0r = zk['t0r']
    at0 = s2([s2([t0r], 'recnd', '%s e. CC' % t0)], 'abscld', '( abs ` %s ) e. RR' % t0)
    jn = lift(w, s1([s1([], 'simpr', 'j e. %s' % I), w.inst('elfzonn0')], 'syl', 'j e. NN0'), A2)
    j1 = lift(w, s1([s1([s1([], 'simpr', 'j e. %s' % I), w.inst('fzofzp1')], 'syl', '( j + 1 ) e. ( 0 ... M )'), w.inst('elfzle2')], 'syl', '( j + 1 ) <_ M'), A2)
    mr_ = s2([L2(L1(d['mn']))], 'nn0red', 'M e. RR')
    lvj = {'j': L2(jr), 'P': L2(L1(d['pr'])), 'T': L2(L1(d['tr'])), 'M': mr_}
    ab = s2([s2([lin8(w, A2, [L2(L1(d['p1'])), s2([jn], 'nn0ge0d', '0 <_ j')], '-u ( T + 2 ) <_ %s' % t0, lvj), lin8(w, A2, [j1, L2(L1(d['m2']))], '%s <_ ( T + 2 )' % t0, lvj)], 'jca', '( -u ( T + 2 ) <_ %s /\\ %s <_ ( T + 2 ) )' % (t0, t0)),
             s2([t0r, s2([L2(L1(d['tr'])), numst(w, A2, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')], 'absled', '( ( abs ` %s ) <_ ( T + 2 ) <-> ( -u ( T + 2 ) <_ %s /\\ %s <_ ( T + 2 ) ) )' % (t0, t0, t0))], 'mpbird', '( abs ` %s ) <_ ( T + 2 )' % t0)
    iqc = s2([zk['iq']], 'recnd', '( Im ` q ) e. CC')
    d1 = s2([iqc, s2([t0r], 'recnd', '%s e. CC' % t0)], 'abs2difd', '( ( abs ` ( Im ` q ) ) - ( abs ` %s ) ) <_ ( abs ` ( ( Im ` q ) - %s ) )' % (t0, t0))
    dqr = s2([s2([s2([zk['iq'], t0r], 'resubcld', '( ( Im ` q ) - %s ) e. RR' % t0)], 'recnd', '( ( Im ` q ) - %s ) e. CC' % t0)], 'abscld', '( abs ` ( ( Im ` q ) - %s ) ) e. RR' % t0)
    a = '( 1 + ( abs ` ( Im ` q ) ) )'
    lva = {'( abs ` ( Im ` q ) )': zk['aq'], '( abs ` %s )' % t0: at0, '( abs ` ( ( Im ` q ) - %s ) )' % t0: dqr, 'T': L2(L1(d['tr'])), '( F holord q )': zk['mr']}
    ak = lin8(w, A2, [d1, zk['imb'], ab], '%s <_ %s' % (a, KT), lva)
    m1 = s2([zk['on']], 'nnge1d', '1 <_ ( F holord q )')
    kr = s2([lift(w, kp, A2)], 'rpred', '%s e. RR' % KT)
    km = s2([kr, zk['mr'], w.inst('id') if False else s2([lift(w, kp, A2)], 'rpge0d', '0 <_ %s' % KT), m1], 'id', 'x') if False else None
    kmle = s2([numst(w, A2, '1', 'RR'), zk['mr'], kr, s2([lift(w, kp, A2)], 'rpge0d', '0 <_ %s' % KT), m1], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. ( F holord q ) )' % (KT, KT))
    k1 = s2([s2([kr], 'recnd', '%s e. CC' % KT)], 'mulridd', '( %s x. 1 ) = %s' % (KT, KT))
    akm = s2([s2([ak, s2([k1, kmle], 'eqbrtrrd', '%s <_ ( %s x. ( F holord q ) )' % (KT, KT))], 'id', 'x') if False else None], 'id', 'x') if False else None
    ar_ = s2([zk['apq']], 'rpred', '%s e. RR' % a)
    kmr = s2([kr, zk['mr']], 'remulcld', '( %s x. ( F holord q ) ) e. RR' % KT)
    akm = s2([ar_, kr, kmr, ak, s2([k1, kmle], 'eqbrtrrd', '%s <_ ( %s x. ( F holord q ) )' % (KT, KT))], 'letrd', '%s <_ ( %s x. ( F holord q ) )' % (a, KT))
    dd1 = s2([ar_, kmr, zk['apq'], akm], 'lediv1dd', '( %s / %s ) <_ ( ( %s x. ( F holord q ) ) / %s )' % (a, a, KT, a))
    dv1 = s2([s2([s2([ar_], 'recnd', '%s e. CC' % a), s2([zk['apq']], 'rpne0d', '%s =/= 0' % a)], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (a, a)), w.inst('divid')], 'syl', '( %s / %s ) = 1' % (a, a))
    dv2 = s2([s2([kr], 'recnd', '%s e. CC' % KT), s2([zk['mr']], 'recnd', '( F holord q ) e. CC'), s2([ar_], 'recnd', '%s e. CC' % a), s2([zk['apq']], 'rpne0d', '%s =/= 0' % a)], 'divassd',
             '( ( %s x. ( F holord q ) ) / %s ) = ( %s x. %s )' % (KT, a, KT, WQ()))
    kw = s2([s2([dv1, dd1], 'eqbrtrrd', '1 <_ ( ( %s x. ( F holord q ) ) / %s )' % (KT, a)), dv2], 'breqtrd', '1 <_ ( %s x. %s )' % (KT, WQ()))
    # ef3sgp
    AD = '( abs ` ( X - ( Re ` q ) ) )'
    SPA = tsub(ante_of(S['ef3sgp'])[0], {'X': AD, 'K': KT, 'W': WQ()})
    SPC = tsub(ante_of(S['ef3sgp'])[1], {'X': AD, 'K': KT, 'W': WQ()})
    p1, p2, p3 = top_and(SPA)
    sp = s2([s2([s2([adr, ad0], 'jca', p1), s2([lift(w, kp, A2), lift(w, np_, A2), zk['wqr']], '3jca', p2), s2([kw, tn2], 'jca', p3)], '3jca', SPA), w.inst('ef3sgp')], 'syl', SPC)
    pos, rsb = conj_split(w, A2, sp)
    xq = s2([lift(w, xr, A2), zk['rer']], 'resubcld', '( X - ( Re ` q ) ) e. RR')
    ne1 = s2([pos, s2([s2([xq], 'recnd', '( X - ( Re ` q ) ) e. CC'), w.inst('absgt0')], 'syl', '( ( X - ( Re ` q ) ) =/= 0 <-> 0 < %s )' % AD)], 'mpbird', '( X - ( Re ` q ) ) =/= 0')
    sq0 = s2([s2([lift(w, xr, A2)], 'recnd', 'X e. CC'), s2([zk['rer']], 'recnd', '( Re ` q ) e. CC')], 'subeq0ad', '( ( X - ( Re ` q ) ) = 0 <-> X = ( Re ` q ) )')
    ne2 = s2([ne1, s2([sq0], 'necon3bid', '( ( X - ( Re ` q ) ) =/= 0 <-> X =/= ( Re ` q ) )')], 'mpbid', 'X =/= ( Re ` q )')
    ne3 = s2([ne2], 'necomd', '( Re ` q ) =/= X')
    rsr = s2([s2([adr, ad0, s2([pos], 'gt0ne0d', '%s =/= 0' % AD) if False else None], 'id', 'x') if False else None], 'id', 'x') if False else None
    adp = s2([adr, pos], 'elrpd', '%s e. RR+' % AD)
    rsr = s2([s2([adp, s2([numst(w, A2, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % RS('X'))], 'rpred', '%s e. RR' % RS('X'))
    b32 = s2([numst(w, A2, '( 3 / 2 )', 'RR'), s2([bp], 'rpred', '%s e. RR' % BASE('X', 'q', ET))], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % BASE('X', 'q', ET))
    tl = s2([rsr, b32, zk['wqr'], zk['wq0'], rsb], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( ( 3 / 2 ) x. %s ) )' % (WQ(), RS('X'), WQ(), BASE('X', 'q', ET)))
    clq = Closure(w, A2, {WQ(): ('RR', zk['wqr']), BASE('X', 'q', ET): ('RR', s2([bp], 'rpred', '%s e. RR' % BASE('X', 'q', ET)))})
    clq.atom(WQ()); clq.atom(BASE('X', 'q', ET))
    te = ringeq(w, A2, '( %s x. ( ( 3 / 2 ) x. %s ) )' % (WQ(), BASE('X', 'q', ET)), '( ( 3 / 2 ) x. %s )' % HT('X', 'q', ET), clq)
    tq = s2([tl, te], 'breqtrd', '( %s x. %s ) <_ ( ( 3 / 2 ) x. %s )' % (WQ(), RS('X'), HT('X', 'q', ET)))
    # assemble
    al1 = s([s1([ne3], 'ralrimiva', 'A. q e. %s ( Re ` q ) =/= X' % ZK())], 'ralrimiva', 'A. j e. %s A. q e. %s ( Re ` q ) =/= X' % (I, ZK()))
    trm = s2([zk['wqr'], rsr], 'remulcld', '( %s x. %s ) e. RR' % (WQ(), RS('X')))
    h32 = s2([numst(w, A2, '( 3 / 2 )', 'RR'), htr], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % HT('X', 'q', ET))
    PHq = 'sum_ q e. %s ( %s x. %s )' % (ZK(), WQ(), RS('X'))
    i1 = s1([zfin, trm, h32, tq], 'fsumle', '%s <_ sum_ q e. %s ( ( 3 / 2 ) x. %s )' % (PHq, ZK(), HT('X', 'q', ET)))
    i2 = s1([zfin, numst(w, A1, '( 3 / 2 )', 'CC'), s2([htr], 'recnd', '%s e. CC' % HT('X', 'q', ET))], 'fsummulc2', '( ( 3 / 2 ) x. %s ) = sum_ q e. %s ( ( 3 / 2 ) x. %s )' % (SQ_, ZK(), HT('X', 'q', ET)))
    i3 = s1([i1, i2], 'breqtrrd', '%s <_ ( ( 3 / 2 ) x. %s )' % (PHq, SQ_))
    phr = s1([zfin, trm], 'fsumrecl', '%s e. RR' % PHq)
    o1 = s([fz0, phr, s1([numst(w, A1, '( 3 / 2 )', 'RR'), sqr], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % SQ_), i3], 'fsumle', '%s <_ sum_ j e. %s ( ( 3 / 2 ) x. %s )' % (PHI('X'), I, SQ_))
    o2 = s([fz0, numst(w, A0, '( 3 / 2 )', 'CC'), s1([sqr], 'recnd', '%s e. CC' % SQ_)], 'fsummulc2', '( ( 3 / 2 ) x. %s ) = sum_ j e. %s ( ( 3 / 2 ) x. %s )' % (HE('X', ET), I, SQ_))
    o3 = s([o1, o2], 'breqtrrd', '%s <_ ( ( 3 / 2 ) x. %s )' % (PHI('X'), HE('X', ET)))
    o4 = s([herjq, s([np_], 'rpred', 'N e. RR'), numst(w, A0, '( 3 / 2 )', 'RR'), numst(w, A0, '( 3 / 2 )', 'ge0'), hnjq], 'lemul2ad', '( ( 3 / 2 ) x. %s ) <_ ( ( 3 / 2 ) x. N )' % HE('X', ET))
    phX = s([fz0, phr], 'fsumrecl', '%s e. RR' % PHI('X'))
    o5 = s([phX, s([numst(w, A0, '( 3 / 2 )', 'RR'), herjq], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % HE('X', ET)), s([numst(w, A0, '( 3 / 2 )', 'RR'), s([np_], 'rpred', 'N e. RR')], 'remulcld', '( ( 3 / 2 ) x. N ) e. RR'), o3, o4], 'letrd',
           '%s <_ ( ( 3 / 2 ) x. N )' % PHI('X'))
    w.qed([al1, o5], 'jca', S['ef3sgt'])
    return run8(w)


def lt4_ge1(w, A, atr, a6):
    """( A -> 1 <_ LT4 ) from atr : AT4 e. RR and a6 : 6 <_ AT4"""
    sA = St(w, A)
    er = sA([w.s([], 'ere', '_e e. RR')], 'a1i', '_e e. RR')
    e3 = sA([w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )'), w.inst('simpri')], 'ax-mp', '_e < 3') if False else w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')], 'a1i', '_e < 3')
    ele = lin8(w, A, [e3, a6], '_e <_ %s' % AT4, {'_e': er, AT4: atr})
    ep = sA([w.s([], 'epr', '_e e. RR+')], 'a1i', '_e e. RR+')
    atp = sA([atr, lin8(w, A, [a6], '0 < %s' % AT4, {AT4: atr})], 'elrpd', '%s e. RR+' % AT4)
    l1 = sA([ele, sA([ep, atp], 'logled', '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (AT4, LT4))], 'mpbid', '( log ` _e ) <_ %s' % LT4)
    return sA([sA([w.s([], 'loge', '( log ` _e ) = 1')], 'a1i', '( log ` _e ) = 1'), l1], 'eqbrtrrd', '1 <_ %s' % LT4)


def gen_sig():
    w = W('ef3sig', 'Lean ` exists_good_sigma ` : off any finite set ` B ` there is ` a e. [ 9 / 16 , 5 / 8 ] ` avoiding the real parts of the zeros of the window squares at which Lean\'s functional ` sum_j sum_q m_q / ( 1 + abs Im q ) abs ( a - Re q ) ^ ( -1/2 ) ` is at most ` 2304000 log ^ 2 ( A ( T + 4 ) ) ` (regularised pigeonhole ~ ef1pgh , ~ ef3sgi , ~ ef3sgt ).')
    A0, G = ante_of(S['ef3sig'])
    s = St(w, A0)
    dd, sgh, bf = conj_split(w, A0, s([], 'id', A0)) if False else (s([], 'simp1', DD()), s([], 'simp2', SGH), s([], 'simp3', 'B e. Fin'))
    d = sgh_parts(w, A0, sgh)
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    f = lt4_facts(w, A0, ar, a1, d['tr'], d['t2'])
    l1 = lt4_ge1(w, A0, f['atr'], f['a6'])
    L2_ = '( %s ^ 2 )' % LT4
    l2r = s([f['lr']], 'resqcld', '%s e. RR' % L2_)
    l21 = s([numst(w, A0, '1', 'RR'), f['lr'], numst(w, A0, '1', 'ge0'), lin8(w, A0, [l1], '0 <_ %s' % LT4, {LT4: f['lr']})], 'le2sqd', '( 1 <_ %s <-> ( 1 ^ 2 ) <_ %s )' % (LT4, L2_))
    l2g = s([s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1'), s([l1, l21], 'mpbid', '( 1 ^ 2 ) <_ %s' % L2_)], 'eqbrtrrd', '1 <_ %s' % L2_)
    MB = '( %s x. %s )' % (KMB, L2_)
    lvm = {L2_: l2r}
    mbr = s([numst(w, A0, KMB, 'RR'), l2r], 'remulcld', '%s e. RR' % MB)
    mbp = s([mbr, lin8(w, A0, [l2g], '0 < %s' % MB, lvm)], 'elrpd', '%s e. RR+' % MB)
    Q = '( %s x. %s )' % (KT, MB)
    ktr = s([d['tr'], numst(w, A0, '6', 'RR')], 'readdcld', '%s e. RR' % KT)
    clq = Closure(w, A0, {KT: ('RR', ktr), MB: ('RR', mbr)}); clq.atom(KT); clq.atom(MB)
    mb1 = lin8(w, A0, [l2g], '1 <_ %s' % MB, lvm)
    q1 = lin.linarith(w, A0, [mb1, lin8(w, A0, [d['t2']], '1 <_ %s' % KT, {'T': d['tr']})], '1 <_ %s' % Q, closure=clq, products=True)
    qr = s([ktr, mbr], 'remulcld', '%s e. RR' % Q)
    Q2 = '( %s ^ 2 )' % Q
    q21 = s([s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1'), s([q1, s([numst(w, A0, '1', 'RR'), qr, numst(w, A0, '1', 'ge0'), lin8(w, A0, [q1], '0 <_ %s' % Q, {Q: qr})], 'le2sqd', '( 1 <_ %s <-> ( 1 ^ 2 ) <_ %s )' % (Q, Q2))], 'mpbid', '( 1 ^ 2 ) <_ %s' % Q2)], 'eqbrtrrd', '1 <_ %s' % Q2)
    q2r = s([qr], 'resqcld', '%s e. RR' % Q2)
    E_ = EK(KT, MB)
    D2 = '( 2 x. %s )' % Q2
    d2p = s([s([numst(w, A0, '2', 'RR'), q2r], 'remulcld', '%s e. RR' % D2), lin8(w, A0, [q21], '0 < %s' % D2, {Q2: q2r})], 'elrpd', '%s e. RR+' % D2)
    ep = s([d2p], 'rpreccld', '%s e. RR+' % E_)
    ele = s([numst(w, A0, '2', 'RR+'), d2p, numst(w, A0, '1', 'RR'), numst(w, A0, '1', 'ge0'), lin8(w, A0, [q21], '2 <_ %s' % D2, {Q2: q2r})], 'lediv2ad', '%s <_ ( 1 / 2 )' % E_)
    e15 = lin8(w, A0, [ele], '%s <_ ( ; 1 5 / ; 1 6 )' % E_, {E_: s([ep], 'rpred', '%s e. RR' % E_)})
    # ef3sgi, ef3sgw
    SIA = tsub(ante_of(S['ef3sgi'])[0], {'E': E_})
    sgi = s([s([s([dd, sgh], 'jca', '( %s /\\ %s )' % (DD(), SGH)), s([ep, e15], 'jca', '( %s e. RR+ /\\ %s <_ ( ; 1 5 / ; 1 6 ) )' % (E_, E_))], 'jca', SIA), w.inst('ef3sgi')], 'syl', tsub(ante_of(S['ef3sgi'])[1], {'E': E_}))
    ib, il = conj_split(w, A0, sgi)
    sgw = s([s([dd, sgh], 'jca', '( %s /\\ %s )' % (DD(), SGH)), w.inst('ef3sgw')], 'syl', ante_of(S['ef3sgw'])[1])
    HEd = HE('d', E_)
    HMAP = '( d e. %s |-> %s )' % (IS, HEd)
    # pointwise real
    Ad = '( %s /\\ d e. %s )' % (A0, IS)
    sd = St(w, Ad)
    dr = sd([sd([w.s([], 'ioossre', '%s C_ RR' % IS)], 'a1i', '%s C_ RR' % IS), sd([], 'simpr', 'd e. %s' % IS)], 'sseldd', 'd e. RR')
    Adj = '( %s /\\ j e. ( 0 ..^ M ) )' % Ad
    sj = St(w, Adj)
    jin = sj([], 'simpr', 'j e. ( 0 ..^ M )')
    jr = sj([sj([jin, w.inst('elfzonn0')], 'syl', 'j e. NN0')], 'nn0red', 'j e. RR')
    zsj = sj([sj([lift(w, dd, Adj), zk_t0r(w, Adj, lift(w, d['pr'], Adj), jr)], 'jca', '( %s /\\ %s e. RR )' % (DD(), T0())), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': T0()}))
    zfj = conj_split(w, Adj, zsj)[0]
    Adq = '( %s /\\ q e. %s )' % (Adj, ZK())
    sq = St(w, Adq)
    zk = zk_facts_v(w, Adq, lift(w, dd, Adq), lift(w, d['pr'], Adq), lift(w, jr, Adq), sq([], 'simpr', 'q e. %s' % ZK()))
    AD = '( abs ` ( d - ( Re ` q ) ) )'
    xq = sq([sq([lift(w, dr, Adq), zk['rer']], 'resubcld', '( d - ( Re ` q ) ) e. RR')], 'recnd', '( d - ( Re ` q ) ) e. CC')
    er = sq([lift(w, ep, Adq)], 'rpred', '%s e. RR' % E_)
    yp = sq([sq([sq([xq], 'abscld', '%s e. RR' % AD), er], 'readdcld', '( %s + %s ) e. RR' % (AD, E_)), lin8(w, Adq, [sq([xq], 'absge0d', '0 <_ %s' % AD), sq([lift(w, ep, Adq)], 'rpgt0d', '0 < %s' % E_)], '0 < ( %s + %s )' % (AD, E_), {AD: sq([xq], 'abscld', '%s e. RR' % AD), E_: er})], 'elrpd', '( %s + %s ) e. RR+' % (AD, E_))
    bpr = sq([sq([yp, sq([numst(w, Adq, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % BASE('d', 'q', E_))], 'rpred', '%s e. RR' % BASE('d', 'q', E_))
    htr = sq([zk['wqr'], bpr], 'remulcld', '%s e. RR' % HT('d', 'q', E_))
    her = sd([sd([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin'), sj([zfj, htr], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (ZK(), HT('d', 'q', E_)))], 'fsumrecl', '%s e. RR' % HEd)
    IH_ = 'S. %s %s _d d' % (IS, HEd)
    ihr = s([her, ib], 'itgrecl', '%s e. RR' % IH_)
    WS = WSUM
    Aj0 = '( %s /\\ j e. ( 0 ..^ M ) )' % A0
    sj0 = St(w, Aj0)
    jr0 = sj0([sj0([sj0([], 'simpr', 'j e. ( 0 ..^ M )'), w.inst('elfzonn0')], 'syl', 'j e. NN0')], 'nn0red', 'j e. RR')
    zf0 = conj_split(w, Aj0, sj0([sj0([lift(w, dd, Aj0), zk_t0r(w, Aj0, lift(w, d['pr'], Aj0), jr0)], 'jca', '( %s /\\ %s e. RR )' % (DD(), T0())), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': T0()})))[0]
    Aq0 = '( %s /\\ q e. %s )' % (Aj0, ZK())
    zkq0 = zk_facts_v(w, Aq0, lift(w, dd, Aq0), lift(w, d['pr'], Aq0), lift(w, jr0, Aq0), St(w, Aq0)([], 'simpr', 'q e. %s' % ZK()))
    fz = s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin')
    wsr = s([fz, sj0([zf0, zkq0['wqr']], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (ZK(), WQ()))], 'fsumrecl', '%s e. RR' % WS)
    # integral <_ Mb ( 5/8 - 9/16 )
    W8 = '( 8 x. %s )' % WS
    MQ = '( %s x. ( ( 5 / 8 ) - ( 9 / ; 1 6 ) ) )' % MB
    cl9 = Closure(w, A0, {L2_: ('RR', l2r)}); cl9.atom(L2_)
    mq9 = ringeq(w, A0, MQ, '( ; ; ; ; 9 6 0 0 0 x. %s )' % L2_, cl9)
    w8 = s([lin8(w, A0, [sgw], '%s <_ ( ; ; ; ; 9 6 0 0 0 x. %s )' % (W8, L2_), {WS: wsr, L2_: l2r}), mq9], 'breqtrrd', '%s <_ %s' % (W8, MQ))
    ile = s([ihr, s([numst(w, A0, '8', 'RR'), wsr], 'remulcld', '%s e. RR' % W8), s([mbr, s([numst(w, A0, '( 5 / 8 )', 'RR'), numst(w, A0, '( 9 / ; 1 6 )', 'RR')], 'resubcld', '( ( 5 / 8 ) - ( 9 / ; 1 6 ) ) e. RR')], 'remulcld', '%s e. RR' % MQ), il, w8], 'letrd',
            '%s <_ %s' % (IH_, MQ))
    # ef1pgh
    fv = sd([sd([], 'simpr', 'd e. %s' % IS), her, w.s([], 'eqid', '%s = %s' % (HMAP, HMAP)) if False else None], 'id', 'x') if False else None
    fvd = sd([sd([], 'simpr', 'd e. %s' % IS), her, w.inst('fvmpt2')], 'syl2anc', '( %s ` d ) = %s' % (HMAP, HEd)) if False else None
    fvm = w.s([w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fvmpt2', '( ( d e. %s /\\ %s e. RR ) -> ( %s ` d ) = %s )' % (IS, HEd, HMAP, HEd))
    fvd = sd([sd([sd([], 'simpr', 'd e. %s' % IS), her], 'jca', '( d e. %s /\\ %s e. RR )' % (IS, HEd)), fvm], 'syl', '( %s ` d ) = %s' % (HMAP, HEd))
    ieq = s([fvd], 'itgeq2dv', 'S. %s ( %s ` d ) _d d = S. %s %s _d d' % (IS, HMAP, IS, HEd))
    HMY = '( y e. %s |-> %s )' % (IS, HE('y', E_))
    e_dy, _ = w.congr(HEd, {'d': 'y'}, 'd = y', {'d': w.s([], 'id', '( d = y -> d = y )')})
    eqm = w.s([e_dy], 'cbvmptv', '%s = %s' % (HMAP, HMY))
    PGA = tsub(ante_of(stmt('ef1pgh'))[0], {'P': '( 9 / ; 1 6 )', 'Q': '( 5 / 8 )', 'F': HMY, 'M': MB, 'S': 'B', 't': 'd'})
    PGC = tsub(ante_of(stmt('ef1pgh'))[1], {'P': '( 9 / ; 1 6 )', 'Q': '( 5 / 8 )', 'F': HMY, 'M': MB, 'S': 'B', 't': 'd'})
    pa1, pa2, pa3 = top_and(PGA)
    fm = s([her], 'fmpttd', '%s : %s --> RR' % (HMAP, IS))
    fmy = s([fm, s([s([eqm], 'a1i', '%s = %s' % (HMAP, HMY)), w.inst('feq1d') if False else None], 'id', 'x') if False else None], 'id', 'x') if False else None
    eqm_a = s([eqm], 'a1i', '%s = %s' % (HMAP, HMY))
    fmy = s([fm, s([eqm_a], 'feq1d', '( %s : %s --> RR <-> %s : %s --> RR )' % (HMAP, IS, HMY, IS))], 'mpbid', '%s : %s --> RR' % (HMY, IS))
    iby = s([eqm_a, ib], 'eqeltrrd', '%s e. L^1' % HMY)
    fyd = sd([lift(w, s([eqm_a], 'eqcomd', '%s = %s' % (HMY, HMAP)), Ad)], 'fveq1d', '( %s ` d ) = ( %s ` d )' % (HMY, HMAP))
    ieq2 = s([sd([fyd, fvd], 'eqtrd', '( %s ` d ) = %s' % (HMY, HEd))], 'itgeq2dv', 'S. %s ( %s ` d ) _d d = S. %s %s _d d' % (IS, HMY, IS, HEd))
    pg = s([s([s([numst(w, A0, '( 9 / ; 1 6 )', 'RR'), numst(w, A0, '( 5 / 8 )', 'RR'), lin8(w, A0, [], '( 9 / ; 1 6 ) < ( 5 / 8 )', {})], '3jca', pa1), s([fmy, iby], 'jca', pa2),
               s([s([mbr, s([ieq2, ile], 'eqbrtrd', 'S. %s ( %s ` d ) _d d <_ %s' % (IS, HMY, MQ))], 'jca', top_and(pa3)[0]), bf], 'jca', pa3)], '3jca', PGA), w.inst('ef1pgh')], 'syl', PGC)
    # the pointwise step, in a context without the functional's letters
    HEio_d = 'sum_ i e. ( 0 ..^ M ) sum_ o e. %s %s' % (ZK('i'), HT('d', 'o', E_))
    Cp = '( %s /\\ %s <_ %s )' % (Ad, HEio_d, MB)
    sc = St(w, Cp)
    Lc = lambda st: lift(w, st, Cp)
    sgt = sc([sc([Lc(dd), Lc(sgh)], 'jca', '( %s /\\ %s )' % (DD(), SGH)), Lc(dr), Lc(mbp), sc([], 'simpr', '%s <_ %s' % (HEio_d, MB))], 'ef3sgt',
             ante_of(tsub(S['ef3sgt'], {'ph': Cp, 'X': 'd', 'N': MB}))[1])
    C2 = '( %s /\\ ( -. d e. B /\\ ( %s ` d ) <_ %s ) )' % (Ad, HMY, MB)
    s2 = St(w, C2)
    L2 = lambda st: lift(w, st, C2)
    nb, hm = conj_split(w, C2, s2([], 'simpr', '( -. d e. B /\\ ( %s ` d ) <_ %s )' % (HMY, MB)))
    he1 = s2([L2(sd([fyd, fvd], 'eqtrd', '( %s ` d ) = %s' % (HMY, HEd))), hm], 'eqbrtrrd', '%s <_ %s' % (HEd, MB))
    SQd = 'sum_ q e. %s %s' % (ZK(), HT('d', 'q', E_))
    SOi = 'sum_ o e. %s %s' % (ZK('i'), HT('d', 'o', E_))
    e_ji, _ = w.congr(SQd, {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    r1 = w.s([e_ji], 'cbvsumv', '%s = sum_ i e. ( 0 ..^ M ) sum_ q e. %s %s' % (HEd, ZK('i'), HT('d', 'q', E_)))
    e_qo, _ = w.congr(HT('d', 'q', E_), {'q': 'o'}, 'q = o', {'q': w.s([], 'id', '( q = o -> q = o )')})
    r2 = w.s([w.s([w.s([e_qo], 'cbvsumv', 'sum_ q e. %s %s = %s' % (ZK('i'), HT('d', 'q', E_), SOi))], 'a1i', '( i e. ( 0 ..^ M ) -> sum_ q e. %s %s = %s )' % (ZK('i'), HT('d', 'q', E_), SOi))], 'sumeq2i',
             'sum_ i e. ( 0 ..^ M ) sum_ q e. %s %s = %s' % (ZK('i'), HT('d', 'q', E_), HEio_d))
    rr = w.s([r1, r2], 'eqtri', '%s = %s' % (HEd, HEio_d))
    he2 = s2([s2([rr], 'a1i', '%s = %s' % (HEd, HEio_d)), he1], 'eqbrtrrd', '%s <_ %s' % (HEio_d, MB))
    cpf = s2([s2([], 'simpl', Ad), he2], 'jca', Cp)
    SGC = ante_of(tsub(S['ef3sgt'], {'ph': Cp, 'X': 'd', 'N': MB}))[1]
    res = s2([cpf, w.s([sgt], 'id', '( %s -> %s )' % (Cp, SGC)) if False else sgt], 'syl', SGC)
    ral_, phb = conj_split(w, C2, res)
    cl2 = Closure(w, C2, {L2_: ('RR', L2(l2r))}); cl2.atom(L2_)
    k32 = ringeq(w, C2, '( ( 3 / 2 ) x. %s )' % MB, '( %s x. %s )' % (KS, L2_), cl2)
    phk = s2([phb, k32], 'breqtrd', '%s <_ ( %s x. %s )' % (PHI('d'), KS, L2_))
    BOD = lambda a: '( -. %s e. B /\\ ( A. j e. ( 0 ..^ M ) A. q e. %s ( Re ` q ) =/= %s /\\ %s <_ ( %s x. %s ) ) )' % (a, ZK(), a, PHI(a), KS, L2_)
    bd = s2([nb, s2([ral_, phk], 'jca', top_and(BOD('d'))[1])], 'jca', BOD('d'))
    din = s2([s2([w.s([], 'ioossicc', '%s C_ ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) )' % IS)], 'a1i', '%s C_ ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) )' % IS), L2(sd([], 'simpr', 'd e. %s' % IS))], 'sseldd', 'd e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) )')
    eqa, _ = w.wcongr(BOD('a'), {'a': 'd'}, 'a = d', {'a': w.s([], 'id', '( a = d -> a = d )')})
    ex = s2([s2([din, bd], 'jca', '( d e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) /\\ %s )' % BOD('d')), w.s([eqa], 'rspcev', '( ( d e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) /\\ %s ) -> E. a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) %s )' % (BOD('d'), BOD('a')))],
            'syl', 'E. a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) %s' % BOD('a'))
    GL = 'E. a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) %s' % BOD('a')
    rl = s([w.s([ex], 'ex', '( %s -> ( ( -. d e. B /\\ ( %s ` d ) <_ %s ) -> %s ) )' % (Ad, HMY, MB, GL))], 'rexlimdva', '( E. d e. %s ( -. d e. B /\\ ( %s ` d ) <_ %s ) -> %s )' % (IS, HMY, MB, GL))
    w.qed([pg, rl], 'mpd', S['ef3sig'])
    return run8(w)


if __name__ == '__main__':
    gen_sgw()
    gen_sgi()
    gen_sgp()
    gen_sgt()
    gen_sig()
