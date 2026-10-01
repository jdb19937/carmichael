"""Sortie ZC1: the sharp von Mangoldt bound sum Lam ( k ) k ^ - ( 1 + u ) <_ ( 5 / 4 ) / u + 5 (vmsharp; Census tsum_vonMangoldt_rpow_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
import cl as _cl
from c8_o import numst
import zc1_c, zc1_w
from zc1_c import u1base, U1, L1
import lin
lin.FASTPATH = True

UU = '( U e. RR+ /\\ U <_ 1 )'
SG = '( 1 + U )'
S4 = '( 1 + ( ( 4 / 5 ) x. U ) )'
EE = '( U / 5 )'
C5 = '( 5 / U )'
LA = lambda k: '( ( Lam ` %s ) x. ( %s ^c -u %s ) )' % (k, k, SG)
S['vmsharp'] = '( %s -> sum_ k e. NN %s <_ ( ( ( 5 / 4 ) / U ) + 5 ) )' % (UU, LA('k'))


def clo_atoms(w, A0, lv):
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    return c


def gen_vmsharp():
    w = W('vmsharp', 'Sharp von Mangoldt series bound (Lean Census ` tsum_vonMangoldt_rpow_le ` has ` 1 / u + 2 ` ): ` sum Lam ( k ) k ^ - ( 1 + u ) <_ ( 5 / 4 ) / u + 5 ` for ` 0 < u <_ 1 ` : ` ( sum Lam k ^ -s ) zeta ( s ) = sum log k k ^ -s ` ( ~ lchrconv at the character mod 1), ` log k <_ ( k ^ e - 1 ) / e ` at ` e = u / 5 ` , ~ zserbnd at ` 1 + 4 u / 5 ` , ~ zetalb .')
    A0 = UU
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    uu = s([], 'id', UU)
    up = s([uu, w.inst('simpl')], 'syl', 'U e. RR+'); u1 = s([uu, w.inst('simpr')], 'syl', 'U <_ 1')
    ur = s([up], 'rpred', 'U e. RR'); uc = s([up], 'rpcnd', 'U e. CC'); une = s([up], 'rpne0d', 'U =/= 0')
    sgr = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), ur], 'readdcld', '%s e. RR' % SG)
    s4r = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), s([numst(w, A0, '( 4 / 5 )', 'RR'), ur], 'remulcld', '( ( 4 / 5 ) x. U ) e. RR')], 'readdcld', '%s e. RR' % S4)
    lvu = {'U': ur}
    sg1 = lin8(w, A0, [s([up], 'rpgt0d', '0 < U')], '1 < %s' % SG, lvu)
    s41 = lin8(w, A0, [s([up], 'rpgt0d', '0 < U')], '1 < %s' % S4, lvu)
    c5p = s([numst(w, A0, '5', 'RR+'), up], 'rpdivcld', '%s e. RR+' % C5)
    c5r = s([c5p], 'rpred', '%s e. RR' % C5); c5c = s([c5p], 'rpcnd', '%s e. CC' % C5)
    ep = s([up, numst(w, A0, '5', 'RR+')], 'rpdivcld', '%s e. RR+' % EE)
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = s([], '1zzd', '1 e. ZZ')
    # termwise facts in context Ak
    Ak = '( %s /\\ k e. NN )' % A0
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    Lk = lambda st: lift(w, st, Ak)
    kn = sk([], 'simpr', 'k e. NN'); kp = sk([kn], 'nnrpd', 'k e. RR+'); kc = sk([kn], 'nncnd', 'k e. CC'); kne = sk([kn], 'nnne0d', 'k =/= 0')
    LK = '( log ` k )'
    lkr = sk([kp], 'relogcld', '%s e. RR' % LK)
    lk0 = sk([sk([kn], 'nnred', 'k e. RR'), sk([kn], 'nnge1d', '1 <_ k'), w.inst('logge0')], 'syl2anc', '0 <_ %s' % LK)
    P = '( k ^c %s )' % EE; Q = '( k ^c -u %s )' % SG; R = '( k ^c -u %s )' % S4
    pp = sk([kp, sk([Lk(ep)], 'rpred', '%s e. RR' % EE)], 'rpcxpcld', '%s e. RR+' % P)
    qp = sk([kp, sk([Lk(sgr)], 'renegcld', '-u %s e. RR' % SG)], 'rpcxpcld', '%s e. RR+' % Q)
    rp = sk([kp, sk([Lk(s4r)], 'renegcld', '-u %s e. RR' % S4)], 'rpcxpcld', '%s e. RR+' % R)
    EL = '( %s x. %s )' % (EE, LK)
    elr = sk([sk([Lk(ep)], 'rpred', '%s e. RR' % EE), lkr], 'remulcld', '%s e. RR' % EL)
    el0 = sk([sk([Lk(ep)], 'rpred', '%s e. RR' % EE), lkr, sk([Lk(ep)], 'rpge0d', '0 <_ %s' % EE), lk0], 'mulge0d', '0 <_ %s' % EL)
    ef = sk([sk([elr, el0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (EL, EL)), w.inst('bvefge1p')], 'syl', '( 1 + %s ) <_ ( exp ` %s )' % (EL, EL))
    pe = sk([sk([kc, kne, sk([Lk(ep)], 'rpcnd', '%s e. CC' % EE)], '3jca', '( k e. CC /\\ k =/= 0 /\\ %s e. CC )' % EE), w.inst('cxpef')], 'syl', '%s = ( exp ` %s )' % (P, EL))
    pe1 = sk([ef, sk([pe], 'eqcomd', '( exp ` %s ) = %s' % (EL, P))], 'breqtrd', '( 1 + %s ) <_ %s' % (EL, P))
    xa = sk([kc, kne, sk([Lk(ep)], 'rpcnd', '%s e. CC' % EE), sk([sk([Lk(sgr)], 'recnd', '%s e. CC' % SG)], 'negcld', '-u %s e. CC' % SG)], 'cxpaddd',
            '( k ^c ( %s + -u %s ) ) = ( %s x. %s )' % (EE, SG, P, Q))
    eqx = lin.lineq(w, Ak, '( %s + -u %s )' % (EE, SG), '-u %s' % S4, closure=clo_atoms(w, Ak, {'U': Lk(ur)}))
    pq = sk([sk([sk([eqx], 'oveq2d', '( k ^c ( %s + -u %s ) ) = %s' % (EE, SG, R)), xa], 'eqtr3d', '%s = ( %s x. %s )' % (R, P, Q))], 'eqcomd', '( %s x. %s ) = %s' % (P, Q, R))
    # U ( lk Q + c5 Q ) <_ U ( c5 R )
    lv = {LK: lkr, P: sk([pp], 'rpred', '%s e. RR' % P), Q: sk([qp], 'rpred', '%s e. RR' % Q), R: sk([rp], 'rpred', '%s e. RR' % R), 'U': Lk(ur), C5: Lk(c5r)}
    c = clo_atoms(w, Ak, lv)
    uc5 = sk([Lk(uc), Lk(une), numst(w, Ak, '5', 'CC')], 'divcan2d', '( U x. %s ) = 5' % C5)
    fQ = sk([sk([Lk(uc), Lk(c5c), sk([qp], 'rpcnd', '%s e. CC' % Q)], 'mulassd', '( ( U x. %s ) x. %s ) = ( U x. ( %s x. %s ) )' % (C5, Q, C5, Q))], 'x', 'x') if False else None
    fQ = sk([sk([sk([Lk(uc), Lk(c5c), sk([qp], 'rpcnd', '%s e. CC' % Q)], 'mulassd', '( ( U x. %s ) x. %s ) = ( U x. ( %s x. %s ) )' % (C5, Q, C5, Q))], 'eqcomd',
                '( U x. ( %s x. %s ) ) = ( ( U x. %s ) x. %s )' % (C5, Q, C5, Q)), sk([uc5], 'oveq1d', '( ( U x. %s ) x. %s ) = ( 5 x. %s )' % (C5, Q, Q))], 'eqtrd', '( U x. ( %s x. %s ) ) = ( 5 x. %s )' % (C5, Q, Q))
    fR = sk([sk([sk([Lk(uc), Lk(c5c), sk([rp], 'rpcnd', '%s e. CC' % R)], 'mulassd', '( ( U x. %s ) x. %s ) = ( U x. ( %s x. %s ) )' % (C5, R, C5, R))], 'eqcomd',
                '( U x. ( %s x. %s ) ) = ( ( U x. %s ) x. %s )' % (C5, R, C5, R)), sk([uc5], 'oveq1d', '( ( U x. %s ) x. %s ) = ( 5 x. %s )' % (C5, R, R))], 'eqtrd', '( U x. ( %s x. %s ) ) = ( 5 x. %s )' % (C5, R, R))
    ul = lin.linarith(w, Ak, [pe1], '( U x. %s ) <_ ( ( 5 x. %s ) - 5 )' % (LK, P), closure=c, products=True)
    hint = sk([c.mem('( ( ( 5 x. %s ) - 5 ) - ( U x. %s ) )' % (P, LK), 'RR'), lv[Q], lin.linarith(w, Ak, [ul], '0 <_ ( ( ( 5 x. %s ) - 5 ) - ( U x. %s ) )' % (P, LK), closure=c, products=True),
               sk([qp], 'rpge0d', '0 <_ %s' % Q)], 'mulge0d', '0 <_ ( ( ( ( 5 x. %s ) - 5 ) - ( U x. %s ) ) x. %s )' % (P, LK, Q))
    T3 = '( ( %s x. %s ) + ( %s x. %s ) )' % (LK, Q, C5, Q)
    T4 = '( %s x. %s )' % (C5, R)
    mu = lin.linarith(w, Ak, [hint, pq, fQ, fR], '( U x. %s ) <_ ( U x. %s )' % (T3, T4), closure=c, products=True)
    t3r = c.mem(T3, 'RR'); t4r = c.mem(T4, 'RR')
    tle = sk([mu, sk([t3r, t4r, Lk(up)], 'lemul2d', '( %s <_ %s <-> ( U x. %s ) <_ ( U x. %s ) )' % (T3, T4, T3, T4))], 'mpbird', '%s <_ %s' % (T3, T4))
    t30 = lin.linarith(w, Ak, [sk([lkr, lv[Q], lk0, sk([qp], 'rpge0d', '0 <_ %s' % Q)], 'mulge0d', '0 <_ ( %s x. %s )' % (LK, Q)), sk([Lk(c5r), lv[Q], sk([Lk(c5p)], 'rpge0d', '0 <_ %s' % C5), sk([qp], 'rpge0d', '0 <_ %s' % Q)], 'mulge0d', '0 <_ ( %s x. %s )' % (C5, Q))],
                       '0 <_ %s' % T3, closure=c, products=True)
    W_ = '( %s x. %s )' % (LK, Q)
    w0 = sk([lkr, lv[Q], lk0, sk([qp], 'rpge0d', '0 <_ %s' % Q)], 'mulge0d', '0 <_ %s' % W_)
    wle = lin.linarith(w, Ak, [tle, sk([Lk(c5r), lv[Q], sk([Lk(c5p)], 'rpge0d', '0 <_ %s' % C5), sk([qp], 'rpge0d', '0 <_ %s' % Q)], 'mulge0d', '0 <_ ( %s x. %s )' % (C5, Q))], '%s <_ %s' % (W_, T4), closure=c, products=True)
    # mappings and their values
    def mv(body_n, val, extra=''):
        return _cg.mptval(w, Ak, 'n', 'NN', body_n, 'k', kn, exs=sk([w.s([], 'ovex', '%s e. _V' % val)], 'a1i', '%s e. _V' % val), gen=w.g)[0]
    n_ = lambda f: f.replace('k', 'n') if False else None
    B3 = '( ( ( log ` n ) x. ( n ^c -u %s ) ) + ( %s x. ( n ^c -u %s ) ) )' % (SG, C5, SG)
    B4 = '( %s x. ( n ^c -u %s ) )' % (C5, S4)
    BW = '( ( log ` n ) x. ( n ^c -u %s ) )' % SG
    B5 = '( %s x. ( n ^c -u %s ) )' % (C5, SG)
    M3, M4, MW, M5 = ['( n e. NN |-> %s )' % b for b in (B3, B4, BW, B5)]
    v3 = mv(B3, T3); v4 = mv(B4, T4); vW = mv(BW, W_); v5 = mv(B5, '( %s x. %s )' % (C5, Q))
    cv4 = s([s([s([s4r, s41], 'jca', '( %s e. RR /\\ 1 < %s )' % (S4, S4)), c5c], 'jca', '( ( %s e. RR /\\ 1 < %s ) /\\ %s e. CC )' % (S4, S4, C5)), w.inst('zsercvgc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % M4)
    cv5 = s([s([s([sgr, sg1], 'jca', '( %s e. RR /\\ 1 < %s )' % (SG, SG)), c5c], 'jca', '( ( %s e. RR /\\ 1 < %s ) /\\ %s e. CC )' % (SG, SG, C5)), w.inst('zsercvgc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % M5)
    r4 = sk([v4, t4r], 'eqeltrd', '( %s ` k ) e. RR' % M4); r3 = sk([v3, t3r], 'eqeltrd', '( %s ` k ) e. RR' % M3); rW = sk([vW, c.mem(W_, 'RR')], 'eqeltrd', '( %s ` k ) e. RR' % MW)
    Akz = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A0
    tonn = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Akz, A0)), w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Akz), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr',
                                                                     '( %s -> k e. NN )' % Akz)], 'jca', '( %s -> %s )' % (Akz, Ak))], 'x', 'x') if False else \
        w.s([w.s([], 'simpl', '( %s -> %s )' % (Akz, A0)), w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Akz), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> k e. NN )' % Akz)],
            'jca', '( %s -> %s )' % (Akz, Ak))
    z0 = lambda st, f: w.s([tonn, st], 'syl', '( %s -> %s )' % (Akz, f))
    n1 = s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    g3 = z0(sk([t30, sk([v3], 'eqcomd', '%s = ( %s ` k )' % (T3, M3))], 'breqtrd', '0 <_ ( %s ` k )' % M3), '0 <_ ( %s ` k )' % M3)
    g34 = z0(sk([sk([v3, tle], 'eqbrtrd', '( %s ` k ) <_ %s' % (M3, T4)), sk([v4], 'eqcomd', '%s = ( %s ` k )' % (T4, M4))], 'breqtrd', '( %s ` k ) <_ ( %s ` k )' % (M3, M4)), '( %s ` k ) <_ ( %s ` k )' % (M3, M4))
    cv3 = w.s([nnuz, n1, r4, r3, cv4, g3, g34], 'cvgcmp', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, M3))
    gW = z0(sk([w0, sk([vW], 'eqcomd', '%s = ( %s ` k )' % (W_, MW))], 'breqtrd', '0 <_ ( %s ` k )' % MW), '0 <_ ( %s ` k )' % MW)
    gW4 = z0(sk([sk([vW, wle], 'eqbrtrd', '( %s ` k ) <_ %s' % (MW, T4)), sk([v4], 'eqcomd', '%s = ( %s ` k )' % (T4, M4))], 'breqtrd', '( %s ` k ) <_ ( %s ` k )' % (MW, M4)), '( %s ` k ) <_ ( %s ` k )' % (MW, M4))
    cvW = w.s([nnuz, n1, r4, rW, cv4, gW, gW4], 'cvgcmp', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MW))
    S3 = 'sum_ k e. NN %s' % T3; S4s = 'sum_ k e. NN %s' % T4; SW = 'sum_ k e. NN %s' % W_; SQ5 = 'sum_ k e. NN ( %s x. %s )' % (C5, Q)
    ile = s([nnuz, one, v3, t3r, v4, t4r, tle, cv3, cv4], 'isumle', '%s <_ %s' % (S3, S4s))
    iad = s([nnuz, one, vW, sk([c.mem(W_, 'RR')], 'recnd', '%s e. CC' % W_), v5, sk([c.mem('( %s x. %s )' % (C5, Q), 'RR')], 'recnd', '( %s x. %s ) e. CC' % (C5, Q)), cvW, cv5], 'isumadd',
            '%s = ( %s + %s )' % (S3, SW, SQ5))
    # c5 x. zeta sums
    Zm = '( t e. NN |-> ( t ^c -u %s ) )'
    ZSG = 'sum_ k e. NN %s' % Q; ZS4 = 'sum_ k e. NN %s' % R
    def zv(S_, sr, s1_, val):
        tv = _cg.mptval(w, Ak, 't', 'NN', '( t ^c -u %s )' % S_, 'k', kn, exs=sk([w.s([], 'ovex', '%s e. _V' % val)], 'a1i', '%s e. _V' % val), gen=w.g)[0]
        cvg = s([s([sr, s1_], 'jca', '( %s e. RR /\\ 1 < %s )' % (S_, S_)), w.inst('zetacvg1')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % (Zm % S_))
        return tv, cvg
    tq, cq = zv(SG, sgr, sg1, Q); tr_, cr = zv(S4, s4r, s41, R)
    m5 = s([nnuz, one, tq, sk([qp], 'rpcnd', '%s e. CC' % Q), cq, c5c], 'isummulc2', '( %s x. %s ) = %s' % (C5, ZSG, SQ5))
    m4 = s([nnuz, one, tr_, sk([rp], 'rpcnd', '%s e. CC' % R), cr, c5c], 'isummulc2', '( %s x. %s ) = %s' % (C5, ZS4, S4s))
    # w + c5 z <_ c5 z4
    zsr = s([nnuz, one, tq, sk([qp], 'rpred', '%s e. RR' % Q), cq], 'isumrecl', '%s e. RR' % ZSG)
    z4r = s([nnuz, one, tr_, sk([rp], 'rpred', '%s e. RR' % R), cr], 'isumrecl', '%s e. RR' % ZS4)
    swr = s([nnuz, one, vW, c.mem(W_, 'RR'), cvW], 'isumrecl', '%s e. RR' % SW)
    key = s([s([s([iad, s([m5], 'eqcomd', '%s = ( %s x. %s )' % (SQ5, C5, ZSG))], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    k1 = s([s([iad, s([s([m5], 'eqcomd', '%s = ( %s x. %s )' % (SQ5, C5, ZSG))], 'oveq2d', '( %s + %s ) = ( %s + ( %s x. %s ) )' % (SW, SQ5, SW, C5, ZSG))], 'eqtrd',
              '%s = ( %s + ( %s x. %s ) )' % (S3, SW, C5, ZSG)), s([ile, s([m4], 'eqcomd', '%s = ( %s x. %s )' % (S4s, C5, ZS4))], 'breqtrd', '%s <_ ( %s x. %s )' % (S3, C5, ZS4))],
           'eqbrtrrd', '( %s + ( %s x. %s ) ) <_ ( %s x. %s )' % (SW, C5, ZSG, C5, ZS4))
    # a z = w: lchrconv at the character mod 1
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    rsg = s([sgr], 'rered', '( Re ` %s ) = %s' % (SG, SG))
    zz = s([s([sgr], 'recnd', '%s e. CC' % SG), s([sg1, s([rsg], 'eqcomd', '%s = ( Re ` %s )' % (SG, SG))], 'breqtrd', '1 < ( Re ` %s )' % SG)], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SG, SG))
    LC = tsub(stmt('lchrconv'), {'N': '1', 'X': U1, 'Z': SG})
    lca, lcc = ante_of(LC)
    lc = s([s([nx1, zz], 'jca', lca), w.inst('lchrconv')], 'syl', lcc)
    XK = '( %s ` ( %s ` k ) )' % (U1, L1)
    x1 = sk([sk([Lk(ub), sk([kn], 'nnzd', 'k e. ZZ')], 'jca', '( %s e. ( Base ` ( DChr ` 1 ) ) /\\ k e. ZZ )' % U1), w.inst('zc1x1')], 'syl', '%s = 1' % XK)
    lamr = sk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')
    def rw1(inner, innerv):
        """( ( XK x. inner ) x. Q ) = ( inner x. Q ) with innerv : ( Ak -> inner e. CC )"""
        a1 = sk([sk([x1], 'oveq1d', '( %s x. %s ) = ( 1 x. %s )' % (XK, inner, inner)), sk([innerv], 'mullidd', '( 1 x. %s ) = %s' % (inner, inner))], 'eqtrd', '( %s x. %s ) = %s' % (XK, inner, inner))
        return sk([a1], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (XK, inner, Q, inner, Q))
    ra = rw1('( Lam ` k )', sk([lamr], 'recnd', '( Lam ` k ) e. CC'))
    rl = rw1(LK, sk([lkr], 'recnd', '%s e. CC' % LK))
    rz = sk([sk([x1], 'oveq1d', '( %s x. %s ) = ( 1 x. %s )' % (XK, Q, Q)), sk([sk([qp], 'rpcnd', '%s e. CC' % Q)], 'mullidd', '( 1 x. %s ) = %s' % (Q, Q))], 'eqtrd', '( %s x. %s ) = %s' % (XK, Q, Q))
    SAX = 'sum_ k e. NN ( ( %s x. ( Lam ` k ) ) x. %s )' % (XK, Q)
    SZX = 'sum_ k e. NN ( %s x. %s )' % (XK, Q)
    SWX = 'sum_ k e. NN ( ( %s x. %s ) x. %s )' % (XK, LK, Q)
    SA = 'sum_ k e. NN %s' % LA('k')
    ea = s([ra], 'sumeq2dv', '%s = %s' % (SAX, SA)); ez = s([rz], 'sumeq2dv', '%s = %s' % (SZX, ZSG)); ew = s([rl], 'sumeq2dv', '%s = %s' % (SWX, SW))
    az = s([s([s([ea, ez], 'oveq12d', '( %s x. %s ) = ( %s x. %s )' % (SAX, SZX, SA, ZSG))], 'eqcomd', '( %s x. %s ) = ( %s x. %s )' % (SA, ZSG, SAX, SZX)), s([lc, ew], 'eqtrd', '( %s x. %s ) = %s' % (SAX, SZX, SW))],
            'eqtrd', '( %s x. %s ) = %s' % (SA, ZSG, SW))
    ML = '( n e. NN |-> ( ( Lam ` n ) x. ( n ^c -u %s ) ) )' % SG
    cvl = s([s([sgr, sg1], 'jca', '( %s e. RR /\\ 1 < %s )' % (SG, SG)), w.inst('vmsercvg')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % ML)
    vl = mv('( ( Lam ` n ) x. ( n ^c -u %s ) )' % SG, LA('k'))
    lar = sk([lamr, lv[Q]], 'remulcld', '%s e. RR' % LA('k'))
    la0 = sk([lamr, lv[Q], sk([kn, w.inst('vmage0')], 'syl', '0 <_ ( Lam ` k )'), sk([qp], 'rpge0d', '0 <_ %s' % Q)], 'mulge0d', '0 <_ %s' % LA('k'))
    sar = s([nnuz, one, vl, lar, cvl], 'isumrecl', '%s e. RR' % SA)
    sa0 = s([nnuz, one, vl, lar, cvl, la0], 'isumge0', '0 <_ %s' % SA)
    # U z >_ 1 ; U z4 <_ U + 5 / 4
    zl = s([uu, w.inst('zetalb')], 'syl', '( 1 / U ) <_ %s' % ZSG)
    uz = s([s([s([uc, une], 'recidd', '( U x. ( 1 / U ) ) = 1')], 'eqcomd', '1 = ( U x. ( 1 / U ) )'), s([zl, s([s([up], 'rpreccld', '( 1 / U ) e. RR+'), zsr, up], 'x', 'x') if False else
            s([s([s([up], 'rpreccld', '( 1 / U ) e. RR+')], 'rpred', '( 1 / U ) e. RR'), zsr, up], 'lemul2d', '( ( 1 / U ) <_ %s <-> ( U x. ( 1 / U ) ) <_ ( U x. %s ) )' % (ZSG, ZSG))], 'mpbid',
                                                                          '( U x. ( 1 / U ) ) <_ ( U x. %s )' % ZSG)], 'eqbrtrd', '1 <_ ( U x. %s )' % ZSG)
    zb = s([s([s4r, s41], 'jca', '( %s e. RR /\\ 1 < %s )' % (S4, S4)), w.inst('zserbnd')], 'syl', '%s <_ ( 1 + ( 1 / ( %s - 1 ) ) )' % (ZS4, S4))
    D4 = '( %s - 1 )' % S4
    d4p = s([s([s4r, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '%s e. RR' % D4), lin8(w, A0, [s41], '0 < %s' % D4, {S4: s4r})], 'elrpd', '%s e. RR+' % D4)
    RB = '( 1 + ( 1 / %s ) )' % D4
    rbr = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), s([s([d4p], 'rpreccld', '( 1 / %s ) e. RR+' % D4)], 'rpred', '( 1 / %s ) e. RR' % D4)], 'readdcld', '%s e. RR' % RB)
    zb2 = s([zb, s([z4r, rbr, d4p], 'lemul2d', '( %s <_ %s <-> ( %s x. %s ) <_ ( %s x. %s ) )' % (ZS4, RB, D4, ZS4, D4, RB))], 'mpbid', '( %s x. %s ) <_ ( %s x. %s )' % (D4, ZS4, D4, RB))
    rid = s([s([d4p], 'rpcnd', '%s e. CC' % D4), s([d4p], 'rpne0d', '%s =/= 0' % D4)], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (D4, D4))
    lvf = {'U': ur, ZSG: zsr, ZS4: z4r, '( 1 / %s )' % D4: s([s([d4p], 'rpreccld', '( 1 / %s ) e. RR+' % D4)], 'rpred', '( 1 / %s ) e. RR' % D4)}
    cf = clo_atoms(w, A0, lvf)
    uz4 = lin.linarith(w, A0, [zb2, rid], '( U x. %s ) <_ ( U + ( 5 / 4 ) )' % ZS4, closure=cf, products=True)
    # the algebra
    uc5 = s([uc, une, numst(w, A0, '5', 'CC')], 'divcan2d', '( U x. %s ) = 5' % C5)
    def uc5x(Xs, xc):
        return s([s([s([uc, c5c, xc], 'mulassd', '( ( U x. %s ) x. %s ) = ( U x. ( %s x. %s ) )' % (C5, Xs, C5, Xs))], 'eqcomd', '( U x. ( %s x. %s ) ) = ( ( U x. %s ) x. %s )' % (C5, Xs, C5, Xs)),
                  s([uc5], 'oveq1d', '( ( U x. %s ) x. %s ) = ( 5 x. %s )' % (C5, Xs, Xs))], 'eqtrd', '( U x. ( %s x. %s ) ) = ( 5 x. %s )' % (C5, Xs, Xs))
    fz = uc5x(ZSG, s([zsr], 'recnd', '%s e. CC' % ZSG)); fz4 = uc5x(ZS4, s([z4r], 'recnd', '%s e. CC' % ZS4))
    LHS = '( %s + ( %s x. %s ) )' % (SW, C5, ZSG); RHS = '( %s x. %s )' % (C5, ZS4)
    lvg = {'U': ur, ZSG: zsr, ZS4: z4r, SW: swr, SA: sar, C5: c5r}
    cg = clo_atoms(w, A0, lvg)
    k2 = s([k1, s([cg.mem(LHS, 'RR'), cg.mem(RHS, 'RR'), up], 'lemul2d', '( %s <_ %s <-> ( U x. %s ) <_ ( U x. %s ) )' % (LHS, RHS, LHS, RHS))], 'mpbid', '( U x. %s ) <_ ( U x. %s )' % (LHS, RHS))
    uaz = s([az], 'oveq2d', '( U x. ( %s x. %s ) ) = ( U x. %s )' % (SA, ZSG, SW))
    k3 = lin.linarith(w, A0, [k2, fz, fz4, uaz], '( U x. ( %s x. %s ) ) <_ ( ( 5 x. %s ) - ( 5 x. %s ) )' % (SA, ZSG, ZS4, ZSG), closure=cg, products=True)
    A3 = '( U x. ( %s x. %s ) )' % (SA, ZSG); B3_ = '( ( 5 x. %s ) - ( 5 x. %s ) )' % (ZS4, ZSG)
    k4 = s([k3, s([cg.mem(A3, 'RR'), cg.mem(B3_, 'RR'), up], 'lemul2d', '( %s <_ %s <-> ( U x. %s ) <_ ( U x. %s ) )' % (A3, B3_, A3, B3_))], 'mpbid', '( U x. %s ) <_ ( U x. %s )' % (A3, B3_))
    h1 = s([cg.mem('( U x. %s )' % SA, 'RR'), cg.mem('( ( U x. %s ) - 1 )' % ZSG, 'RR'), s([ur, sar, s([up], 'rpge0d', '0 <_ U'), sa0], 'mulge0d', '0 <_ ( U x. %s )' % SA),
            lin.linarith(w, A0, [uz], '0 <_ ( ( U x. %s ) - 1 )' % ZSG, closure=cg, products=True)], 'mulge0d', '0 <_ ( ( U x. %s ) x. ( ( U x. %s ) - 1 ) )' % (SA, ZSG))
    fin0 = lin.linarith(w, A0, [k4, h1, uz, uz4], '( U x. %s ) <_ ( ( 5 / 4 ) + ( 5 x. U ) )' % SA, closure=cg, products=True)
    GB = '( ( ( 5 / 4 ) / U ) + 5 )'
    ug = s([s([s([uc, s([s([numst(w, A0, '( 5 / 4 )', 'RR'), up], 'rerpdivcld', '( ( 5 / 4 ) / U ) e. RR')], 'recnd', '( ( 5 / 4 ) / U ) e. CC'), numst(w, A0, '5', 'CC')], 'adddid',
                  '( U x. %s ) = ( ( U x. ( ( 5 / 4 ) / U ) ) + ( U x. 5 ) )' % GB), s([s([uc, une, numst(w, A0, '( 5 / 4 )', 'CC')], 'divcan2d', '( U x. ( ( 5 / 4 ) / U ) ) = ( 5 / 4 )'),
                  s([uc, numst(w, A0, '5', 'CC')], 'mulcomd', '( U x. 5 ) = ( 5 x. U )')], 'oveq12d', '( ( U x. ( ( 5 / 4 ) / U ) ) + ( U x. 5 ) ) = ( ( 5 / 4 ) + ( 5 x. U ) )')], 'eqtrd',
               '( U x. %s ) = ( ( 5 / 4 ) + ( 5 x. U ) )' % GB)], 'eqcomd', '( ( 5 / 4 ) + ( 5 x. U ) ) = ( U x. %s )' % GB)
    fin1 = s([fin0, ug], 'breqtrd', '( U x. %s ) <_ ( U x. %s )' % (SA, GB))
    gbr = s([s([numst(w, A0, '( 5 / 4 )', 'RR'), up], 'rerpdivcld', '( ( 5 / 4 ) / U ) e. RR'), numst(w, A0, '5', 'RR')], 'readdcld', '%s e. RR' % GB)
    fin = s([fin1, s([sar, gbr, up], 'lemul2d', '( %s <_ %s <-> ( U x. %s ) <_ ( U x. %s ) )' % (SA, GB, SA, GB))], 'mpbird', '%s <_ %s' % (SA, GB))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['vmsharp']))
    return run8(w)


if __name__ == '__main__':
    gen_vmsharp()
