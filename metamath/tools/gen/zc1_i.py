"""Sortie ZC1: orders add under products (holordml); finite order with a factorisation at every point of the
right half-plane (hp0ordf)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
from c9_b import decode
from c10_f import crfacts, clo
import lin
lin.FASTPATH = True

FAC = lambda F, P, N, g, D='D', z='z': 'A. %s e. %s ( %s ` %s ) = ( ( ( %s - %s ) ^ %s ) x. ( %s ` %s ) )' % (z, D, F, z, z, P, N, g, z)
S['holordml'] = ('( ( ( F e. ( D -cn-> CC ) /\\ P e. D ) /\\ ( ( M e. NN0 /\\ %s /\\ ( G ` P ) =/= 0 ) /\\ ( N e. NN0 /\\ %s /\\ ( H ` P ) =/= 0 ) ) /\\ '
                 'A. v e. D ( F ` v ) = ( ( ( ( v - P ) ^ M ) x. ( G ` v ) ) x. ( ( ( v - P ) ^ N ) x. ( H ` v ) ) ) ) -> ( F holord P ) = ( M + N ) )') % (HOLF('G', 'D'), HOLF('H', 'D'))
S['hp0ordf'] = ('( ( ( %s /\\ ( F ` 2 ) =/= 0 ) /\\ P e. %s ) -> ( ( F holord P ) e. NN0 /\\ E. g ( %s /\\ ( g ` P ) =/= 0 /\\ %s ) ) )') % (
    HOLF('F', HP0), HP0, HOLF('g', HP0), FAC('F', 'P', '( F holord P )', 'g', HP0))


def encode(w, A0, uc, ac, bc, a, b, U, lr, hr, li, hi):
    """( A0 -> U e. ( a crect b ) ) from U e. CC and the four bounds"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ivs = []
    for part, lo, hi_, lem in (('Re', lr, hr, 'recld'), ('Im', li, hi, 'imcld')):
        x_, a_, b_ = '( %s ` %s )' % (part, U), '( %s ` %s )' % (part, a), '( %s ` %s )' % (part, b)
        e2 = s([s([ac], lem, '%s e. RR' % a_), s([bc], lem, '%s e. RR' % b_), w.inst('elicc2')], 'syl2anc',
               '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (x_, a_, b_, x_, a_, x_, x_, b_))
        ivs.append(s([s([s([uc], lem, '%s e. RR' % x_), lo, hi_], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (x_, a_, x_, x_, b_)), e2], 'mpbird', '%s e. ( %s [,] %s )' % (x_, a_, b_)))
    EL = '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (U, U, a, b, U, a, b)
    ec = s([s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (a, b)), w.inst('elcrect')], 'syl', '( %s e. ( %s crect %s ) <-> %s )' % (U, a, b, EL))
    return s([s([uc, ivs[0], ivs[1]], '3jca', EL), ec], 'mpbird', '%s e. ( %s crect %s )' % (U, a, b))


def gen_holordml():
    w = W('holordml', 'Orders add under products: if ` F ( z ) = ( ( z - P ) ^ M g ( z ) ) ( ( z - P ) ^ N h ( z ) ) ` on the open set ` D ` with ` g , h ` holomorphic and nonzero at ` P ` , then ` ( F holord P ) = M + N ` (Mathlib ` analyticOrderAt_mul ` ; ~ holordeq , ~ holmul ).')
    A0, GC = ante_of(S['holordml'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2, X3 = top_and(A0)
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2); fac = s([], 'simp3', X3)
    fcn = s([x1, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )'); pd = s([x1, w.inst('simpr')], 'syl', 'P e. D')
    G1, G2 = top_and(X2)
    g1 = s([x2, w.inst('simpl')], 'syl', G1); g2 = s([x2, w.inst('simpr')], 'syl', G2)
    mn = s([g1, w.inst('simp1')], 'syl', 'M e. NN0'); gh = s([g1, w.inst('simp2')], 'syl', HOLF('G', 'D')); gp = s([g1, w.inst('simp3')], 'syl', '( G ` P ) =/= 0')
    nn = s([g2, w.inst('simp1')], 'syl', 'N e. NN0'); hh = s([g2, w.inst('simp2')], 'syl', HOLF('H', 'D')); hp = s([g2, w.inst('simp3')], 'syl', '( H ` P ) =/= 0')
    GH = '( u e. D |-> ( ( G ` u ) x. ( H ` u ) ) )'
    hm = s([s([gh, hh], 'jca', '( %s /\\ %s )' % (HOLF('G', 'D'), HOLF('H', 'D'))), w.inst('holmul')], 'syl', HOLF(GH, 'D'))
    op = s([gh, w.inst('holopn')], 'syl', 'D e. ( TopOpen ` CCfld )')
    gf = s([s([gh, w.inst('simpl')], 'syl', 'G e. ( D -cn-> CC )'), w.inst('cncff')], 'syl', 'G : D --> CC')
    hf = s([s([hh, w.inst('simpl')], 'syl', 'H e. ( D -cn-> CC )'), w.inst('cncff')], 'syl', 'H : D --> CC')
    def ghval(ante, U, ust):
        VAL = '( ( G ` %s ) x. ( H ` %s ) )' % (U, U)
        vx = w.s([w.s([], 'ovex', '%s e. _V' % VAL)], 'a1i', '( %s -> %s e. _V )' % (ante, VAL))
        fv, _ = _cg.mptval(w, ante, 'u', 'D', '( ( G ` u ) x. ( H ` u ) )', U, ust, exs=vx, gen=w.g)
        return fv, VAL
    fvp, VP = ghval(A0, 'P', pd)
    gp0 = s([fvp, s([s([gf, pd], 'ffvelcdmd', '( G ` P ) e. CC'), s([hf, pd], 'ffvelcdmd', '( H ` P ) e. CC'), gp, hp], 'mulne0d', '%s =/= 0' % VP)], 'eqnetrd', '( %s ` P ) =/= 0' % GH)
    Az = '( %s /\\ z e. D )' % A0
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zd = sz([], 'simpr', 'z e. D')
    fvz, VZ = ghval(Az, 'z', zd)
    BV = X3[len('A. v e. D '):]
    BZ = tsub(BV, {'v': 'z'})
    eqv = w.wcongr(BV, {'v': 'z'}, 'v = z', {'v': w.s([], 'id', '( v = z -> v = z )')})[0]
    fz = w.s([eqv, lift(w, fac, Az), zd], 'rspcdva', '( %s -> %s )' % (Az, BZ))
    dcc = sz([lift(w, s([s([gh, w.inst('simpl')], 'syl', 'G e. ( D -cn-> CC )'), w.inst('cncfrss')], 'syl', 'D C_ CC'), Az), zd], 'sseldd', 'z e. CC')
    zp = sz([dcc, sz([lift(w, s([s([s([gh, w.inst('simpl')], 'syl', 'G e. ( D -cn-> CC )'), w.inst('cncfrss')], 'syl', 'D C_ CC'), pd], 'sseldd', 'P e. CC'), Az)], 'x', 'x') if False else
                    lift(w, s([s([s([gh, w.inst('simpl')], 'syl', 'G e. ( D -cn-> CC )'), w.inst('cncfrss')], 'syl', 'D C_ CC'), pd], 'sseldd', 'P e. CC'), Az)], 'subcld', '( z - P ) e. CC')
    em = sz([zp, lift(w, mn, Az)], 'expcld', '( ( z - P ) ^ M ) e. CC'); en = sz([zp, lift(w, nn, Az)], 'expcld', '( ( z - P ) ^ N ) e. CC')
    gz = sz([lift(w, gf, Az), zd], 'ffvelcdmd', '( G ` z ) e. CC'); hz = sz([lift(w, hf, Az), zd], 'ffvelcdmd', '( H ` z ) e. CC')
    m4 = sz([em, gz, en, hz], 'mul4d', '( ( ( ( z - P ) ^ M ) x. ( G ` z ) ) x. ( ( ( z - P ) ^ N ) x. ( H ` z ) ) ) = ( ( ( ( z - P ) ^ M ) x. ( ( z - P ) ^ N ) ) x. ( ( G ` z ) x. ( H ` z ) ) )')
    ea = sz([zp, lift(w, nn, Az), lift(w, mn, Az)], 'expaddd', '( ( z - P ) ^ ( M + N ) ) = ( ( ( z - P ) ^ M ) x. ( ( z - P ) ^ N ) )')
    r = sz([sz([ea], 'eqcomd', '( ( ( z - P ) ^ M ) x. ( ( z - P ) ^ N ) ) = ( ( z - P ) ^ ( M + N ) )'), sz([fvz], 'eqcomd', '%s = ( %s ` z )' % (VZ, GH))], 'oveq12d',
           '( ( ( ( z - P ) ^ M ) x. ( ( z - P ) ^ N ) ) x. ( ( G ` z ) x. ( H ` z ) ) ) = ( ( ( z - P ) ^ ( M + N ) ) x. ( %s ` z ) )' % GH)
    fz2 = sz([sz([fz, m4], 'eqtrd', '( F ` z ) = ( ( ( ( z - P ) ^ M ) x. ( ( z - P ) ^ N ) ) x. ( ( G ` z ) x. ( H ` z ) ) )'), r], 'eqtrd', '( F ` z ) = ( ( ( z - P ) ^ ( M + N ) ) x. ( %s ` z ) )' % GH)
    fall = s([fz2], 'ralrimiva', 'A. z e. D ( F ` z ) = ( ( ( z - P ) ^ ( M + N ) ) x. ( %s ` z ) )' % GH)
    HE = tsub(stmt('holordeq'), {'V': '( D -cn-> CC )', 'E': 'D', 'G': GH, 'N': '( M + N )'})
    ha, hc = ante_of(HE)
    Y1, Y2, Y3 = top_and(ha)
    w.qed([s([s([fcn, s([op, pd], 'jca', top_and(Y1)[1])], 'jca', Y1), s([hm, gp0], 'jca', Y2), s([s([mn, nn], 'nn0addcld', '( M + N ) e. NN0'), fall], 'jca', Y3)], '3jca', ha), w.inst('holordeq')], 'syl', S['holordml'])
    return run8(w)


def gen_hp0ordf():
    w = W('hp0ordf', 'Finite order and the local factorisation at every point of the right half-plane, for ` F ` holomorphic there with ` F ( 2 ) =/= 0 ` ( ~ holordfinr on the rectangle ` [ a , Re P + 2 ] x. [ - abs Im P , abs Im P ] ` , ` a = Re P / ( Re P + 1 ) ` , margin ` a / 2 ` ).')
    A0, GC = ante_of(S['hp0ordf'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    x1 = s([], 'simpl', '( %s /\\ ( F ` 2 ) =/= 0 )' % HOLF('F', HP0))
    hol = s([x1, w.inst('simpl')], 'syl', HOLF('F', HP0)); f2 = s([x1, w.inst('simpr')], 'syl', '( F ` 2 ) =/= 0')
    ph = s([], 'simpr', 'P e. %s' % HP0)
    el = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( P e. %s <-> ( P e. CC /\\ 0 < ( Re ` P ) ) )' % HP0)
    pp = s([ph, el], 'mpbid', '( P e. CC /\\ 0 < ( Re ` P ) )')
    pc = s([pp, w.inst('simpl')], 'syl', 'P e. CC'); rp0 = s([pp, w.inst('simpr')], 'syl', '0 < ( Re ` P )')
    RP, IP = '( Re ` P )', '( Im ` P )'
    rpr = s([pc], 'recld', '%s e. RR' % RP); ipr = s([pc], 'imcld', '%s e. RR' % IP)
    AI = '( abs ` %s )' % IP
    air = s([s([ipr], 'recnd', '%s e. CC' % IP)], 'abscld', '%s e. RR' % AI)
    RP1 = '( %s + 1 )' % RP
    rp1 = s([rpr, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'readdcld', '%s e. RR' % RP1)
    rp1p = s([rp1, lin8(w, A0, [rp0], '0 < %s' % RP1, {RP: rpr})], 'elrpd', '%s e. RR+' % RP1)
    a_ = '( %s / %s )' % (RP, RP1)
    ar = s([rpr, rp1p], 'rerpdivcld', '%s e. RR' % a_)
    rpp = s([rpr, rp0], 'elrpd', '%s e. RR+' % RP)
    ap = s([rpp, rp1p], 'rpdivcld', '%s e. RR+' % a_)
    lvp = {RP: rpr}
    hint = s([rpr, rpr, lin8(w, A0, [rp0], '0 <_ %s' % RP, lvp), lin8(w, A0, [rp0], '0 <_ %s' % RP, lvp)], 'mulge0d', '0 <_ ( %s x. %s )' % (RP, RP))
    import cl as _cl
    c = _cl.Closure(w, A0, lvp); c.atom(RP)
    le1 = s([lin.linarith(w, A0, [hint], '%s <_ ( %s x. %s )' % (RP, RP1, RP), closure=c, products=True),
             s([rpr, rpr, rp1p], 'ledivmuld', '( %s <_ %s <-> %s <_ ( %s x. %s ) )' % (a_, RP, RP, RP1, RP))], 'mpbird', '%s <_ %s' % (a_, RP))
    le2 = s([lin8(w, A0, [], '%s <_ ( %s x. 1 )' % (RP, RP1), lvp), s([rpr, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), rp1p], 'ledivmuld',
             '( %s <_ 1 <-> %s <_ ( %s x. 1 ) )' % (a_, RP, RP1))], 'mpbird', '%s <_ 1' % a_)
    R_ = '( %s / 2 )' % a_
    rr = s([ap, w.inst('rphalfcld')], 'syl', '%s e. RR+' % R_)
    A = '( %s + ( _i x. -u %s ) )' % (a_, AI)
    B = '( ( %s + 2 ) + ( _i x. %s ) )' % (RP, AI)
    nai = s([air], 'renegcld', '-u %s e. RR' % AI)
    rp2 = s([rpr, numst(w, A0, '2', 'RR')], 'readdcld', '( %s + 2 ) e. RR' % RP)
    ac, reA, imA = crfacts(w, A0, a_, '-u %s' % AI, ar, nai)
    bc, reB, imB = crfacts(w, A0, '( %s + 2 )' % RP, AI, rp2, air)
    lv = {RP: rpr, IP: ipr, AI: air, a_: ar}
    for e, st in (('( Re ` %s )' % A, ac), ('( Im ` %s )' % A, ac), ('( Re ` %s )' % B, bc), ('( Im ` %s )' % B, bc)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    ag0 = s([s([ipr], 'recnd', '%s e. CC' % IP)], 'absge0d', '0 <_ %s' % AI)
    lt = s([ipr], 'leabsd', '%s <_ %s' % (IP, AI))
    nt = s([s([s([ipr], 'renegcld', '-u %s e. RR' % IP)], 'leabsd', '-u %s <_ ( abs ` -u %s )' % (IP, IP)), s([s([ipr], 'recnd', '%s e. CC' % IP)], 'absnegd', '( abs ` -u %s ) = %s' % (IP, AI))],
            'breqtrd', '-u %s <_ %s' % (IP, AI))
    hy = [reA, imA, reB, imB, le1, le2, ag0, lt, nt, rp0]
    geo = s([lin8(w, A0, hy, '( Re ` %s ) <_ ( Re ` %s )' % (A, B), lv), lin8(w, A0, hy, '( Im ` %s ) <_ ( Im ` %s )' % (A, B), lv)], 'jca', GEOG(A, B))
    # the fattened rectangle lies in HP0
    RR_ = '( %s + ( _i x. %s ) )' % (R_, R_)
    A2, B2 = '( %s - %s )' % (A, RR_), '( %s + %s )' % (B, RR_)
    rrc = s([s([rr], 'rpcnd', '%s e. CC' % R_), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([rr], 'rpcnd', '%s e. CC' % R_)], 'mulcld', '( _i x. %s ) e. CC' % R_)], 'addcld', '%s e. CC' % RR_)
    a2c = s([ac, rrc], 'subcld', '%s e. CC' % A2); b2c = s([bc, rrc], 'addcld', '%s e. CC' % B2)
    ra2 = s([ac, rrc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (A2, A, RR_))
    rrr = s([s([rr], 'rpred', '%s e. RR' % R_), s([rr], 'rpred', '%s e. RR' % R_)], 'crred', '( Re ` %s ) = %s' % (RR_, R_))
    RECT = '( %s crect %s )' % (A2, B2)
    Ax = '( %s /\\ x e. %s )' % (A0, RECT)
    L = lambda st: lift(w, st, Ax)
    dx = decode(w, Ax, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, RECT)), L(a2c), L(b2c), A2, B2, RECT, U='x')
    xc = dx[0]
    lvx = {'( Re ` x )': w.s([xc], 'recld', '( %s -> ( Re ` x ) e. RR )' % Ax), '( Re ` %s )' % A2: w.s([L(a2c)], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, A2)),
           '( Re ` %s )' % A: L(lv['( Re ` %s )' % A]), '( Re ` %s )' % RR_: w.s([L(rrc)], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, RR_)), a_: L(ar)}
    ahalf = lin8(w, A0, [], '0 < %s' % a_, {a_: ar}) if False else s([ap], 'rpgt0d', '0 < %s' % a_)
    rx = lin8(w, Ax, [dx[1], L(ra2), L(rrr), L(reA), L(ahalf)], '0 < ( Re ` x )', lvx)
    elx = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Ax), w.inst('elhp2')], 'syl', '( %s -> ( x e. %s <-> ( x e. CC /\\ 0 < ( Re ` x ) ) ) )' % (Ax, HP0))
    xh = w.s([w.s([xc, rx], 'jca', '( %s -> ( x e. CC /\\ 0 < ( Re ` x ) ) )' % Ax), elx], 'mpbird', '( %s -> x e. %s )' % (Ax, HP0))
    sub = s([w.s([xh], 'ex', '( %s -> ( x e. %s -> x e. %s ) )' % (A0, RECT, HP0))], 'ssrdv', '%s C_ %s' % (RECT, HP0))
    # P and 2 in the rectangle
    pin = encode(w, A0, pc, ac, bc, A, B, 'P', lin8(w, A0, hy, '( Re ` %s ) <_ %s' % (A, RP), lv), lin8(w, A0, hy, '%s <_ ( Re ` %s )' % (RP, B), lv),
                 lin8(w, A0, hy, '( Im ` %s ) <_ %s' % (A, IP), lv), lin8(w, A0, hy, '%s <_ ( Im ` %s )' % (IP, B), lv))
    two = s([], '2cnd', '2 e. CC')
    re2 = s([w.s([], 're2' if False else 'rei', '( Re ` 2 ) = 2')], 'a1i', '( Re ` 2 ) = 2') if False else s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    im2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'reim0d', '( Im ` 2 ) = 0')
    lv2 = dict(lv); lv2['( Re ` 2 )'] = s([two], 'recld', '( Re ` 2 ) e. RR'); lv2['( Im ` 2 )'] = s([two], 'imcld', '( Im ` 2 ) e. RR')
    hy2 = hy + [re2, im2]
    tin = encode(w, A0, two, ac, bc, A, B, '2', lin8(w, A0, hy2, '( Re ` %s ) <_ ( Re ` 2 )' % A, lv2), lin8(w, A0, hy2, '( Re ` 2 ) <_ ( Re ` %s )' % B, lv2),
                 lin8(w, A0, hy2, '( Im ` %s ) <_ ( Im ` 2 )' % A, lv2), lin8(w, A0, hy2, '( Im ` 2 ) <_ ( Im ` %s )' % B, lv2))
    H = tsub(stmt('holordfinr'), {'A': A, 'B': B, 'R': R_, 'D': HP0, 'X': 'P'})
    ha_, hc = ante_of(H)
    P0, PX = top_and(ha_)
    P1, P2 = top_and(P0)
    Q1, Q2, Q3 = top_and(P1)
    q1 = s([hol, s([s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (A, B)), geo], 'jca', Q2), s([rr, sub], 'jca', Q3)], '3jca', P1)
    subw = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ w = 2 ) -> w = 2 )' % A0)], 'fveq2d', '( ( %s /\\ w = 2 ) -> ( F ` w ) = ( F ` 2 ) )' % A0)], 'neeq1d',
               '( ( %s /\\ w = 2 ) -> ( ( F ` w ) =/= 0 <-> ( F ` 2 ) =/= 0 ) )' % A0)
    ex = s([f2, s([tin, subw], 'rspcedv', '( ( F ` 2 ) =/= 0 -> %s )' % P2)], 'mpd', P2)
    w.qed([s([s([q1, ex], 'jca', P0), pin], 'jca', ha_), w.inst('holordfinr')], 'syl', S['hp0ordf'])
    return run8(w)


if __name__ == '__main__':
    gen_holordml()
    gen_hp0ordf()
