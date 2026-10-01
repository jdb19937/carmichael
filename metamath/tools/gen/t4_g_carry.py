"""Sortie T4, group G: the carry of A + B + C position by position, and the closed form of the majBit fold (T4-blueprint 3.5)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AZ = '( ( A e. ZZ /\\ B e. ZZ /\\ C e. 2o ) /\\ I e. NN0 )'
MA = lambda I: '( A mod ( 2 ^ %s ) )' % I
MB = lambda I: '( B mod ( 2 ^ %s ) )' % I
RI = lambda I: '( ( %s + %s ) + ( bToNat ` C ) )' % (MA(I), MB(I))
KI = lambda I: 'if ( ( 2 ^ %s ) <_ %s , 1o , (/) )' % (I, RI(I))
PK = '( 2 ^ I )'; PK1 = '( 2 ^ ( I + 1 ) )'; I1 = '( I + 1 )'
BNC = '( bToNat ` C )'
Sx = '( ( A + B ) + ( bToNat ` C ) )'
R = '( %s - ( %s x. ( bToNat ` %s ) ) )' % (RI('I'), PK, KI('I'))
a_ = BIT('A', 'I'); b_ = BIT('B', 'I'); k_ = KI('I')
s_ = OP3(a_, 'sumBit', b_, k_); m_ = OP3(a_, 'majBit', b_, k_)
CARRY = lambda I: FOLD('majBit', 'A', 'B', 'C', I)


def base(w, ante=AZ):
    a = w.s([], 'simpl1', '( %s -> A e. ZZ )' % ante); b = w.s([], 'simpl2', '( %s -> B e. ZZ )' % ante)
    c = w.s([], 'simpl3', '( %s -> C e. 2o )' % ante); i = w.s([], 'simpr', '( %s -> I e. NN0 )' % ante)
    cl = Cl(w, ante, {'A': ('ZZ', a), 'B': ('ZZ', b), 'C': ('2o', c), 'I': ('NN0', i)})
    return cl


def modfacts(w, cl, X, I, ante):
    """( X mod 2^I ) e. NN0, < 2^I, <_ 2^I - 1 ; returns (n0, lt, le1)"""
    M = '( %s mod ( 2 ^ %s ) )' % (X, I); P = '( 2 ^ %s )' % I
    n0 = cl.mem(M, 'NN0')
    lt = w.s([cl.mem(X, 'RR'), cl.mem(P, 'RR+'), w.inst('modlt')], 'syl2anc', '( %s -> %s < %s )' % (ante, M, P))
    le1 = w.s([cl.mem(M, 'ZZ'), cl.mem(P, 'ZZ'), w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (ante, M, P, M, P))
    le = w.s([lt, le1], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (ante, M, P))
    return n0, lt, le


def prodK(w, cl, ante, K, P, val):
    """( ante -> ( P x. ( bToNat ` K ) ) = P ) when val == '1o' else ( ... ) = 0, given ( ante -> K = val )"""
    raise NotImplementedError


if __name__ == '__main__':
    if want('bwaddlem1'):
        w = W('bwaddlem1', 'Lemma for the carry: the low part of the partial sum, the partial sum less the carry weight, lies in [ 0 , 2 ^ I ).')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR'))
        na, lta, lea = modfacts(w, cl, 'A', 'I', AZ); nb, ltb, leb = modfacts(w, cl, 'B', 'I', AZ)
        cl.atom(MA('I')); cl.atom(MB('I'))
        bn = cl.mem(BNC, 'NN0'); bnle = w.s([cl.mem('C', '2o'), w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AZ, BNC)); bng = cl.ge0(BNC)
        cl.atom(BNC)
        PR = '( %s x. ( bToNat ` %s ) )' % (PK, k_)
        concl = '( 0 <_ %s /\\ %s < %s )' % (R, R, PK)
        cond = '( 2 ^ I ) <_ %s' % RI('I')
        for case in (True, False):
            a2 = '( %s /\\ %s )' % (AZ, cond) if case else '( %s /\\ -. %s )' % (AZ, cond)
            h = w.s([], 'simpr', '( %s -> %s )' % (a2, cond if case else '-. ' + cond))
            c2 = Cl(w, a2, {}); c2.parent = cl
            for E, T in ((PK, 'RR'), (MA('I'), 'RR'), (MB('I'), 'RR'), (BNC, 'RR'), (PR, 'RR')):
                c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
            if case:
                it = w.s([h], 'iftrued', '( %s -> %s = 1o )' % (a2, k_))
                f = w.s([it], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` 1o ) )' % (a2, k_)); c1 = w.s([], 'bwbn1', '( bToNat ` 1o ) = 1')
                f2 = w.s([f, c1], 'eqtrdi', '( %s -> ( bToNat ` %s ) = 1 )' % (a2, k_))
                o = w.s([f2], 'oveq2d', '( %s -> %s = ( %s x. 1 ) )' % (a2, PR, PK)); m = w.s([lift(w, cl.mem(PK, 'CC'), a2)], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (a2, PK, PK))
                pe = w.s([o, m], 'eqtrd', '( %s -> %s = %s )' % (a2, PR, PK))
                hyps = [h, pe, lift(w, lea, a2), lift(w, leb, a2), lift(w, bnle, a2)]
            else:
                ln = w.s([lift(w, cl.mem(RI('I'), 'RR'), a2), lift(w, cl.mem(PK, 'RR'), a2), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s ) )' % (a2, RI('I'), PK, cond))
                lt = w.s([h, ln], 'mpbird', '( %s -> %s < %s )' % (a2, RI('I'), PK))
                it = w.s([h], 'iffalsed', '( %s -> %s = (/) )' % (a2, k_))
                f = w.s([it], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` (/) ) )' % (a2, k_)); c0 = w.s([], 'bwbn0', '( bToNat ` (/) ) = 0')
                f2 = w.s([f, c0], 'eqtrdi', '( %s -> ( bToNat ` %s ) = 0 )' % (a2, k_))
                o = w.s([f2], 'oveq2d', '( %s -> %s = ( %s x. 0 ) )' % (a2, PR, PK)); m = w.s([lift(w, cl.mem(PK, 'CC'), a2)], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (a2, PK))
                pe = w.s([o, m], 'eqtrd', '( %s -> %s = 0 )' % (a2, PR))
                hyps = [lt, pe, lift(w, cl.ge0(MA('I')), a2), lift(w, cl.ge0(MB('I')), a2), lift(w, bng, a2)]
            g1 = linarith(w, a2, hyps, '0 <_ %s' % R, closure=c2)
            g2 = linarith(w, a2, hyps, '%s < %s' % (R, PK), closure=c2)
            j = w.s([g1, g2], 'jca', '( %s -> %s )' % (a2, concl))
            if case:
                jt = j
            else:
                jf = j
        w.qed([jt, jf], 'pm2.61dan', '( %s -> %s )' % (AZ, concl)); w.run()

    if want('bwaddlem2'):
        w = W('bwaddlem2', 'Lemma for the carry: the residue of the sum modulo 2 ^ I is the low part of the partial sum.')
        cl = base(w)
        ar = cl.mem('A', 'RR'); br = cl.mem('B', 'RR'); pr = cl.mem(PK, 'RR+')
        ma = cl.mem(MA('I'), 'RR'); mb = cl.mem(MB('I'), 'RR'); cr = cl.mem(BNC, 'RR')
        ab = w.s([ar, br, pr, w.inst('modaddabs')], 'syl3anc', '( %s -> ( ( %s + %s ) mod %s ) = ( ( A + B ) mod %s ) )' % (AZ, MA('I'), MB('I'), PK, PK))
        sm = cl.mem('( %s + %s )' % (MA('I'), MB('I')), 'RR'); s2 = cl.mem('( A + B )', 'RR')
        cc = w.s([], 'eqidd', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, BNC, PK, BNC, PK))
        m12 = w.s([sm, s2, cr, cr, pr, ab, cc], 'modadd12d', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, RI('I'), PK, Sx, PK))
        rr = cl.mem(RI('I'), 'RR'); kz = cl.mem('( bToNat ` %s )' % k_, 'ZZ')
        mc = w.s([rr, pr, kz, w.inst('modcyc2')], 'syl3anc', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, R, PK, RI('I'), PK))
        l1 = w.s([], 'bwaddlem1', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (AZ, R, R, PK))
        rrr = cl.mem(R, 'RR')
        j = w.s([rrr, pr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (AZ, R, PK))
        mi = w.s([j, l1, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (AZ, R, PK, R))
        m12r = w.s([m12], 'eqcomd', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, Sx, PK, RI('I'), PK))
        w.qed([m12r, mc, mi], '3eqtr2d', '( %s -> ( %s mod %s ) = %s )' % (AZ, Sx, PK, R)); w.run()

    if want('bwaddlem3'):
        w = W('bwaddlem3', 'Lemma for the carry: the partial sum at I + 1 is the low part plus the sum bit at its weight plus the carry bit at the next weight.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR'))
        for E in (MA('I'), MB('I'), BNC, '( bToNat ` %s )' % a_, '( bToNat ` %s )' % b_, '( bToNat ` %s )' % k_, '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        pa = w.s([cl.mem('A', 'ZZ'), cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, MA(I1), MA('I'), PK, a_))
        pb = w.s([cl.mem('B', 'ZZ'), cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, MB(I1), MB('I'), PK, b_))
        fa = w.s([cl.mem(a_, '2o'), cl.mem(b_, '2o'), cl.mem(k_, '2o'), w.inst('bwfulladd')], 'syl3anc',
                 '( %s -> ( ( ( bToNat ` %s ) + ( bToNat ` %s ) ) + ( bToNat ` %s ) ) = ( ( bToNat ` %s ) + ( 2 x. ( bToNat ` %s ) ) ) )' % (AZ, a_, b_, k_, s_, m_))
        mfa = w.s([fa], 'oveq2d', '( %s -> ( %s x. ( ( ( bToNat ` %s ) + ( bToNat ` %s ) ) + ( bToNat ` %s ) ) ) = ( %s x. ( ( bToNat ` %s ) + ( 2 x. ( bToNat ` %s ) ) ) ) )' % (AZ, PK, a_, b_, k_, PK, s_, m_))
        goal_rhs = '( ( %s + ( %s x. ( bToNat ` %s ) ) ) + ( ( %s x. 2 ) x. ( bToNat ` %s ) ) )' % (R, PK, s_, PK, m_)
        lineq(w, AZ, RI(I1), goal_rhs, hyps=[pa, pb, mfa], closure=cl, products=True, name='qed'); w.run()

    if want('bwaddlem4'):
        w = W('bwaddlem4', 'Lemma for the carry: the carry into position I + 1 is the majority of the two digits at I and the carry into I.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR'))
        for E in (R, '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_, '( %s x. ( bToNat ` %s ) )' % (PK, s_), RI(I1)):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        l1 = w.s([], 'bwaddlem1', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (AZ, R, R, PK))
        r0 = w.s([l1], 'simpld', '( %s -> 0 <_ %s )' % (AZ, R)); r1 = w.s([l1], 'simprd', '( %s -> %s < %s )' % (AZ, R, PK))
        rz = cl.mem(R, 'ZZ'); pz = cl.mem(PK, 'ZZ')
        r2 = w.s([rz, pz, w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (AZ, R, PK, R, PK)); r3 = w.s([r1, r2], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (AZ, R, PK))
        l3 = w.s([], 'bwaddlem3', '( %s -> %s = ( ( %s + ( %s x. ( bToNat ` %s ) ) ) + ( ( %s x. 2 ) x. ( bToNat ` %s ) ) ) )' % (AZ, RI(I1), R, PK, s_, PK, m_))
        sle = w.s([cl.mem(s_, '2o'), w.inst('bwbnle1')], 'syl', '( %s -> ( bToNat ` %s ) <_ 1 )' % (AZ, s_))
        sg = cl.ge0('( bToNat ` %s )' % s_)
        ps = w.s([cl.mem('( bToNat ` %s )' % s_, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % AZ), cl.mem(PK, 'RR'), cl.ge0(PK), sle], 'lemul2ad', '( %s -> ( %s x. ( bToNat ` %s ) ) <_ ( %s x. 1 ) )' % (AZ, PK, s_, PK))
        p1 = w.s([cl.mem(PK, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AZ, PK, PK)); ps2 = w.s([ps, p1], 'breqtrd', '( %s -> ( %s x. ( bToNat ` %s ) ) <_ %s )' % (AZ, PK, s_, PK))
        psg = w.s([cl.mem(PK, 'RR'), cl.mem('( bToNat ` %s )' % s_, 'RR'), cl.ge0(PK), sg], 'mulge0d', '( %s -> 0 <_ ( %s x. ( bToNat ` %s ) ) )' % (AZ, PK, s_))
        ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % AZ), cl.mem('I', 'NN0'), w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (AZ, PK1, PK))
        cl.leaf(PK1, 'RR', cl.mem(PK1, 'RR'))
        concl = '%s = %s' % (KI(I1), m_)
        mm = cl.mem(m_, '2o')

        def body(a2, eq, v):
            f = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` %s ) )' % (a2, m_, v))
            c = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, '1' if v == '1o' else '0'))
            f2 = w.s([f, c], 'eqtrdi', '( %s -> ( bToNat ` %s ) = %s )' % (a2, m_, '1' if v == '1o' else '0'))
            PM = '( ( %s x. 2 ) x. ( bToNat ` %s ) )' % (PK, m_)
            o2 = w.s([f2], 'oveq2d', '( %s -> %s = ( ( %s x. 2 ) x. %s ) )' % (a2, PM, PK, '1' if v == '1o' else '0'))
            p2c = lift(w, cl.mem('( %s x. 2 )' % PK, 'CC'), a2)
            if v == '1o':
                mv = w.s([p2c], 'mulridd', '( %s -> ( ( %s x. 2 ) x. 1 ) = ( %s x. 2 ) )' % (a2, PK, PK))
            else:
                mv = w.s([p2c], 'mul01d', '( %s -> ( ( %s x. 2 ) x. 0 ) = 0 )' % (a2, PK))
            f2 = w.s([o2, mv], 'eqtrd', '( %s -> %s = %s )' % (a2, PM, ('( %s x. 2 )' % PK) if v == '1o' else '0'))
            c2 = Cl(w, a2, {}); c2.parent = cl
            c2.leaf(PM, 'RR', lift(w, cl.mem(PM, 'RR'), a2))
            for E in (R, '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_, '( %s x. ( bToNat ` %s ) )' % (PK, s_), RI(I1), PK, PK1):
                c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
            hyps = [lift(w, x, a2) for x in (r0, r3, l3, ps2, psg, ep)] + [f2]
            if v == '1o':
                g = linarith(w, a2, hyps, '%s <_ %s' % (PK1, RI(I1)), closure=c2)
                it = w.s([g], 'iftrued', '( %s -> %s = 1o )' % (a2, KI(I1)))
            else:
                g = linarith(w, a2, hyps, '%s < %s' % (RI(I1), PK1), closure=c2)
                ln = w.s([lift(w, cl.mem(RI(I1), 'RR'), a2), lift(w, cl.mem(PK1, 'RR'), a2), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (a2, RI(I1), PK1, PK1, RI(I1)))
                ng = w.s([g, ln], 'mpbid', '( %s -> -. %s <_ %s )' % (a2, PK1, RI(I1)))
                it = w.s([ng], 'iffalsed', '( %s -> %s = (/) )' % (a2, KI(I1)))
            return w.s([it, eq], 'eqtr4d', '( %s -> %s )' % (a2, concl))
        st = cases2o(w, AZ, m_, mm, body, concl); promote(w, st); w.run()

    if want('bwaddlem5'):
        w = W('bwaddlem5', 'Lemma for the carry: the residue of the sum modulo 2 ^ ( I + 1 ) is the low part plus the sum bit at its weight.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR')); cl.leaf(PK1, 'RR', cl.mem(PK1, 'RR'))
        X = '( %s + ( %s x. ( bToNat ` %s ) ) )' % (R, PK, s_)
        for E in (R, '( bToNat ` %s )' % s_, '( %s x. ( bToNat ` %s ) )' % (PK, s_)):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        cl.have(X, 'RR', cl.mem(X, 'RR'))
        i1 = cl.mem(I1, 'NN0')
        # S mod 2^(I+1) = RI(I+1) mod 2^(I+1), as in bwaddlem2 at I + 1
        ar = cl.mem('A', 'RR'); br = cl.mem('B', 'RR'); pr = cl.mem(PK1, 'RR+')
        ab = w.s([ar, br, pr, w.inst('modaddabs')], 'syl3anc', '( %s -> ( ( %s + %s ) mod %s ) = ( ( A + B ) mod %s ) )' % (AZ, MA(I1), MB(I1), PK1, PK1))
        sm = cl.mem('( %s + %s )' % (MA(I1), MB(I1)), 'RR'); s2 = cl.mem('( A + B )', 'RR'); cr = cl.mem(BNC, 'RR')
        cc = w.s([], 'eqidd', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, BNC, PK1, BNC, PK1))
        m12 = w.s([sm, s2, cr, cr, pr, ab, cc], 'modadd12d', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, RI(I1), PK1, Sx, PK1))
        l3 = w.s([], 'bwaddlem3', '( %s -> %s = ( %s + ( ( %s x. 2 ) x. ( bToNat ` %s ) ) ) )' % (AZ, RI(I1), X, PK, m_))
        ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % AZ), cl.mem('I', 'NN0'), w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (AZ, PK1, PK))
        ep2 = w.s([ep], 'oveq1d', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( ( %s x. 2 ) x. ( bToNat ` %s ) ) )' % (AZ, PK1, m_, PK, m_))
        ep3 = w.s([ep2], 'oveq2d', '( %s -> ( %s + ( %s x. ( bToNat ` %s ) ) ) = ( %s + ( ( %s x. 2 ) x. ( bToNat ` %s ) ) ) )' % (AZ, X, PK1, m_, X, PK, m_))
        l3b = w.s([l3, ep3], 'eqtr4d', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, RI(I1), X, PK1, m_))
        # ( X + ( PK1 x. bn m ) ) mod PK1 = X mod PK1 : modcyc with ( N x. B ) = ( bn m x. PK1 )
        mz = cl.mem('( bToNat ` %s )' % m_, 'ZZ')
        mc = w.s([cl.mem(X, 'RR'), pr, mz, w.inst('modcyc')], 'syl3anc', '( %s -> ( ( %s + ( ( bToNat ` %s ) x. %s ) ) mod %s ) = ( %s mod %s ) )' % (AZ, X, m_, PK1, PK1, X, PK1))
        com = w.s([cl.mem(PK1, 'CC'), cl.mem('( bToNat ` %s )' % m_, 'CC')], 'mulcomd', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( ( bToNat ` %s ) x. %s ) )' % (AZ, PK1, m_, m_, PK1))
        com2 = w.s([com], 'oveq2d', '( %s -> ( %s + ( %s x. ( bToNat ` %s ) ) ) = ( %s + ( ( bToNat ` %s ) x. %s ) ) )' % (AZ, X, PK1, m_, X, m_, PK1))
        l3c = w.s([l3b, com2], 'eqtrd', '( %s -> %s = ( %s + ( ( bToNat ` %s ) x. %s ) ) )' % (AZ, RI(I1), X, m_, PK1))
        o = w.s([l3c], 'oveq1d', '( %s -> ( %s mod %s ) = ( ( %s + ( ( bToNat ` %s ) x. %s ) ) mod %s ) )' % (AZ, RI(I1), PK1, X, m_, PK1, PK1))
        # X in [0, PK1)
        l1 = w.s([], 'bwaddlem1', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (AZ, R, R, PK))
        r0 = w.s([l1], 'simpld', '( %s -> 0 <_ %s )' % (AZ, R)); r1 = w.s([l1], 'simprd', '( %s -> %s < %s )' % (AZ, R, PK))
        rz = cl.mem(R, 'ZZ'); pz = cl.mem(PK, 'ZZ')
        r2 = w.s([rz, pz, w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (AZ, R, PK, R, PK)); r3 = w.s([r1, r2], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (AZ, R, PK))
        sle = w.s([cl.mem(s_, '2o'), w.inst('bwbnle1')], 'syl', '( %s -> ( bToNat ` %s ) <_ 1 )' % (AZ, s_)); sg = cl.ge0('( bToNat ` %s )' % s_)
        ps = w.s([cl.mem('( bToNat ` %s )' % s_, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % AZ), cl.mem(PK, 'RR'), cl.ge0(PK), sle], 'lemul2ad', '( %s -> ( %s x. ( bToNat ` %s ) ) <_ ( %s x. 1 ) )' % (AZ, PK, s_, PK))
        p1 = w.s([cl.mem(PK, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AZ, PK, PK)); ps2 = w.s([ps, p1], 'breqtrd', '( %s -> ( %s x. ( bToNat ` %s ) ) <_ %s )' % (AZ, PK, s_, PK))
        psg = w.s([cl.mem(PK, 'RR'), cl.mem('( bToNat ` %s )' % s_, 'RR'), cl.ge0(PK), sg], 'mulge0d', '( %s -> 0 <_ ( %s x. ( bToNat ` %s ) ) )' % (AZ, PK, s_))
        g0 = linarith(w, AZ, [r0, psg], '0 <_ %s' % X, closure=cl)
        g1 = linarith(w, AZ, [r3, ps2, ep], '%s < %s' % (X, PK1), closure=cl)
        j = w.s([cl.mem(X, 'RR'), pr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (AZ, X, PK1)); j2 = w.s([g0, g1], 'jca', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (AZ, X, X, PK1))
        mi = w.s([j, j2, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (AZ, X, PK1, X))
        ch = w.s([o, mc, mi], '3eqtrd', '( %s -> ( %s mod %s ) = %s )' % (AZ, RI(I1), PK1, X))
        w.qed([m12, ch], 'eqtr3d', '( %s -> ( %s mod %s ) = %s )' % (AZ, Sx, PK1, X)); w.run()

    if want('bwadddig'):
        w = W('bwadddig', 'The I-th digit of A + B + C is the sum bit of the two digits at I and the carry into I.')
        cl = base(w)
        sz = cl.mem(Sx, 'ZZ')
        p1 = w.s([sz, cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> ( %s mod %s ) = ( ( %s mod %s ) + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Sx, PK1, Sx, PK, PK, BIT(Sx, 'I')))
        l2 = w.s([], 'bwaddlem2', '( %s -> ( %s mod %s ) = %s )' % (AZ, Sx, PK, R))
        o = w.s([l2], 'oveq1d', '( %s -> ( ( %s mod %s ) + ( %s x. ( bToNat ` %s ) ) ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Sx, PK, PK, BIT(Sx, 'I'), R, PK, BIT(Sx, 'I')))
        l5 = w.s([], 'bwaddlem5', '( %s -> ( %s mod %s ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Sx, PK1, R, PK, s_))
        po = w.s([p1, o], 'eqtrd', '( %s -> ( %s mod %s ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Sx, PK1, R, PK, BIT(Sx, 'I')))
        e = w.s([po, l5], 'eqtr3d', '( %s -> ( %s + ( %s x. ( bToNat ` %s ) ) ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, R, PK, BIT(Sx, 'I'), R, PK, s_))
        rc = cl.mem(R, 'CC'); x1 = cl.mem('( %s x. ( bToNat ` %s ) )' % (PK, BIT(Sx, 'I')), 'CC'); x2 = cl.mem('( %s x. ( bToNat ` %s ) )' % (PK, s_), 'CC')
        ac = w.s([rc, x1, x2], 'addcand', '( %s -> ( ( %s + ( %s x. ( bToNat ` %s ) ) ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) <-> ( %s x. ( bToNat ` %s ) ) = ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, R, PK, BIT(Sx, 'I'), R, PK, s_, PK, BIT(Sx, 'I'), PK, s_))
        e2 = w.s([e, ac], 'mpbid', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( %s x. ( bToNat ` %s ) ) )' % (AZ, PK, BIT(Sx, 'I'), PK, s_))
        b1 = cl.mem('( bToNat ` %s )' % BIT(Sx, 'I'), 'CC'); b2 = cl.mem('( bToNat ` %s )' % s_, 'CC'); pc = cl.mem(PK, 'CC'); pne = cl.ne0(PK)
        mc = w.s([b1, b2, pc, pne], 'mulcand', '( %s -> ( ( %s x. ( bToNat ` %s ) ) = ( %s x. ( bToNat ` %s ) ) <-> ( bToNat ` %s ) = ( bToNat ` %s ) ) )' % (AZ, PK, BIT(Sx, 'I'), PK, s_, BIT(Sx, 'I'), s_))
        e3 = w.s([e2, mc], 'mpbid', '( %s -> ( bToNat ` %s ) = ( bToNat ` %s ) )' % (AZ, BIT(Sx, 'I'), s_))
        inj = w.s([cl.mem(BIT(Sx, 'I'), '2o'), cl.mem(s_, '2o'), w.inst('bwbn11')], 'syl2anc', '( %s -> ( ( bToNat ` %s ) = ( bToNat ` %s ) <-> %s = %s ) )' % (AZ, BIT(Sx, 'I'), s_, BIT(Sx, 'I'), s_))
        e4 = w.s([e3, inj], 'mpbid', '( %s -> %s = %s )' % (AZ, BIT(Sx, 'I'), s_))
        e5 = w.s([e4], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (AZ, BIT(Sx, 'I'), s_))
        n0 = w.s([], '1n0', '1o =/= (/)'); tb = w.s([n0, w.inst('iftrueb')], 'ax-mp', '( %s = 1o <-> I e. ( bits ` %s ) )' % (BIT(Sx, 'I'), Sx))
        tbd = w.s([tb], 'a1i', '( %s -> ( %s = 1o <-> I e. ( bits ` %s ) ) )' % (AZ, BIT(Sx, 'I'), Sx))
        w.qed([tbd, e5], 'bitr3d', '( %s -> ( I e. ( bits ` %s ) <-> %s = 1o ) )' % (AZ, Sx, s_)); w.run()

    # ---- the closed form of the carry fold, by induction on the position
    AZ0 = '( A e. ZZ /\\ B e. ZZ /\\ C e. 2o )'
    if want('bwcarry'):
        w = W('bwcarry', 'The majBit fold is the carry: the carry into position I of A + B + C is set exactly when the low I bits overflow.')
        FSET = '~P ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) )'
        P = lambda I: '%s = %s' % (CARRY(I), KI(I))
        # substitution instances of the induction property
        x0 = w.s([], 'id', '( x = 0 -> x = 0 )'); h1, _ = w.wcongr(P('x'), {'x': '0'}, 'x = 0', {'x': x0})
        xy = w.s([], 'id', '( x = y -> x = y )'); h2, _ = w.wcongr(P('x'), {'x': 'y'}, 'x = y', {'x': xy})
        xy1 = w.s([], 'id', '( x = ( y + 1 ) -> x = ( y + 1 ) )'); h3, _ = w.wcongr(P('x'), {'x': '( y + 1 )'}, 'x = ( y + 1 )', {'x': xy1})
        xI = w.s([], 'id', '( x = I -> x = I )'); h4, _ = w.wcongr(P('x'), {'x': 'I'}, 'x = I', {'x': xI})
        # base
        a = w.s([], 'simp1', '( %s -> A e. ZZ )' % AZ0); b = w.s([], 'simp2', '( %s -> B e. ZZ )' % AZ0); c = w.s([], 'simp3', '( %s -> C e. 2o )' % AZ0)
        cl0 = Cl(w, AZ0, {'A': ('ZZ', a), 'B': ('ZZ', b), 'C': ('2o', c)})
        fs = w.s([], 'majfs', 'majBit e. %s' % FSET); fsd = w.s([fs], 'a1i', '( %s -> majBit e. %s )' % (AZ0, FSET))
        c3 = cl0.mem('C', '3o')
        jab = w.s([a, b], 'jca', '( %s -> ( A e. ZZ /\\ B e. ZZ ) )' % AZ0); jfc = w.s([fsd, c3], 'jca', '( %s -> ( majBit e. %s /\\ C e. 3o ) )' % (AZ0, FSET))
        af = w.s([jab, jfc], 'jca', '( %s -> ( ( A e. ZZ /\\ B e. ZZ ) /\\ ( majBit e. %s /\\ C e. 3o ) ) )' % (AZ0, FSET))
        f0 = w.s([af, w.inst('bwfold0')], 'syl', '( %s -> %s = C )' % (AZ0, CARRY('0')))
        # KI(0) = C : 2^0 = 1, A mod 1 = 0, B mod 1 = 0
        ma0 = w.s([a, w.inst('zmod10')], 'syl', '( %s -> ( A mod 1 ) = 0 )' % AZ0); mb0 = w.s([b, w.inst('zmod10')], 'syl', '( %s -> ( B mod 1 ) = 0 )' % AZ0)
        tc = w.s([], '2cn', '2 e. CC'); e0 = w.s([tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % AZ0)
        oa = w.s([e0d], 'oveq2d', '( %s -> ( A mod ( 2 ^ 0 ) ) = ( A mod 1 ) )' % AZ0); oa2 = w.s([oa, ma0], 'eqtrd', '( %s -> ( A mod ( 2 ^ 0 ) ) = 0 )' % AZ0)
        ob = w.s([e0d], 'oveq2d', '( %s -> ( B mod ( 2 ^ 0 ) ) = ( B mod 1 ) )' % AZ0); ob2 = w.s([ob, mb0], 'eqtrd', '( %s -> ( B mod ( 2 ^ 0 ) ) = 0 )' % AZ0)
        s0 = w.s([oa2, ob2], 'oveq12d', '( %s -> ( %s + %s ) = ( 0 + 0 ) )' % (AZ0, MA('0'), MB('0'))); z00 = w.s([], '00id', '( 0 + 0 ) = 0'); s0b = w.s([s0, z00], 'eqtrdi', '( %s -> ( %s + %s ) = 0 )' % (AZ0, MA('0'), MB('0')))
        r0 = w.s([s0b], 'oveq1d', '( %s -> %s = ( 0 + %s ) )' % (AZ0, RI('0'), BNC)); bc = cl0.mem(BNC, 'CC'); r0b = w.s([r0, w.s([bc], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AZ0, BNC, BNC))], 'eqtrd', '( %s -> %s = %s )' % (AZ0, RI('0'), BNC))
        br = w.s([e0d, r0b], 'breq12d', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> 1 <_ %s ) )' % (AZ0, RI('0'), BNC))
        # 1 <_ bn C <-> C = 1o
        bn0 = cl0.mem(BNC, 'NN0'); bnle = w.s([c, w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AZ0, BNC))
        bnr = cl0.mem(BNC, 'RR'); onr = w.s([], '1red', '( %s -> 1 e. RR )' % AZ0)
        t3 = w.s([onr, bnr, w.inst('letri3')], 'syl2anc', '( %s -> ( 1 = %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AZ0, BNC, BNC, BNC))
        bt = w.s([bnle], 'biantrud', '( %s -> ( 1 <_ %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AZ0, BNC, BNC, BNC))
        b13 = w.s([bt, t3], 'bitr4d', '( %s -> ( 1 <_ %s <-> 1 = %s ) )' % (AZ0, BNC, BNC))
        ec = w.s([], 'eqcom', '( 1 = %s <-> %s = 1 )' % (BNC, BNC)); ecd = w.s([ec], 'a1i', '( %s -> ( 1 = %s <-> %s = 1 ) )' % (AZ0, BNC, BNC))
        bq = w.s([c, w.inst('bwbneq1')], 'syl', '( %s -> ( %s = 1 <-> C = 1o ) )' % (AZ0, BNC))
        cond0 = w.s([br, b13, ecd, bq], '4bitrd' if False else 'bitrd', '') if False else None
        bb1 = w.s([br, b13], 'bitrd', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> 1 = %s ) )' % (AZ0, RI('0'), BNC)); bb2 = w.s([bb1, ecd], 'bitrd', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> %s = 1 ) )' % (AZ0, RI('0'), BNC)); bb3 = w.s([bb2, bq], 'bitrd', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> C = 1o ) )' % (AZ0, RI('0')))
        ib = w.s([bb3], 'ifbid', '( %s -> %s = if ( C = 1o , 1o , (/) ) )' % (AZ0, KI('0')))
        cb = bool_from_bi(w, AZ0, 'C', 'C = 1o', w.s([], 'biidd', '( %s -> ( C = 1o <-> C = 1o ) )' % AZ0), c)
        k0 = w.s([ib, cb], 'eqtr4d', '( %s -> %s = C )' % (AZ0, KI('0')))
        base_ = w.s([f0, k0], 'eqtr4d', '( %s -> %s )' % (AZ0, P('0')))
        # step
        AY = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (AZ0, P('y'))
        ih = w.s([], 'simpr', '( %s -> %s )' % (AY, P('y'))); yn = w.s([], 'simplr', '( %s -> y e. NN0 )' % AY); az = w.s([], 'simpll', '( %s -> %s )' % (AY, AZ0))
        azy = w.s([az, yn], 'jca', '( %s -> ( %s /\\ y e. NN0 ) )' % (AY, AZ0))
        AZy = '( %s /\\ y e. NN0 )' % AZ0
        cly = Cl(w, AY, {'A': ('ZZ', lift(w, a, AY)), 'B': ('ZZ', lift(w, b, AY)), 'C': ('2o', lift(w, c, AY)), 'y': ('NN0', yn)})
        KIy = KI('y'); KIy1 = KI('( y + 1 )')
        ky2 = cly.mem(KIy, '2o'); ky3 = cly.mem(KIy, '3o')
        lv3 = w.s([ih, ky3], 'eqeltrd', '( %s -> %s e. 3o )' % (AY, CARRY('y')))
        aff = w.s([az, af], 'syl', '( %s -> ( ( A e. ZZ /\\ B e. ZZ ) /\\ ( majBit e. %s /\\ C e. 3o ) ) )' % (AY, FSET))
        jy = w.s([yn, lv3], 'jca', '( %s -> ( y e. NN0 /\\ %s e. 3o ) )' % (AY, CARRY('y')))
        p1 = w.s([aff, jy, w.inst('bwfoldp1')], 'syl2anc', '( %s -> %s = ( ( %s majBit %s ) ` %s ) )' % (AY, CARRY('( y + 1 )'), BIT('A', 'y'), BIT('B', 'y'), CARRY('y')))
        f = w.s([ih], 'fveq2d', '( %s -> ( ( %s majBit %s ) ` %s ) = ( ( %s majBit %s ) ` %s ) )' % (AY, BIT('A', 'y'), BIT('B', 'y'), CARRY('y'), BIT('A', 'y'), BIT('B', 'y'), KIy))
        l4 = w.s([azy, w.inst('bwaddlem4')], 'syl', '( %s -> %s = ( ( %s majBit %s ) ` %s ) )' % (AY, KIy1, BIT('A', 'y'), BIT('B', 'y'), KIy))
        step = w.s([p1, f, l4], '3eqtr4d', '( %s -> %s )' % (AY, P('( y + 1 )')))
        st = w.s([h1, h2, h3, h4, base_, step], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (AZ0, P('I')))
        promote(w, st); w.run()

    if want('bwcarrycl'):
        w = W('bwcarrycl', 'The carry is a Boolean.')
        cl = base(w)
        v = w.s([], 'bwcarry', '( %s -> %s = %s )' % (AZ, CARRY('I'), KI('I'))); m = cl.mem(KI('I'), '2o')
        w.qed([v, m], 'eqeltrd', '( %s -> %s e. 2o )' % (AZ, CARRY('I'))); w.run()
    if want('bwcarryp1'):
        w = W('bwcarryp1', 'The carry into position I + 1 is the majority of the two digits at I and the carry into I (the recursive form, unconditionally).')
        cl = base(w)
        i1 = cl.mem(I1, 'NN0'); az0 = w.s([], 'simpl', '( %s -> %s )' % (AZ, AZ0))
        v1 = w.s([az0, i1, w.inst('bwcarry')], 'syl2anc', '( %s -> %s = %s )' % (AZ, CARRY(I1), KI(I1)))
        l4 = w.s([], 'bwaddlem4', '( %s -> %s = %s )' % (AZ, KI(I1), m_))
        v0 = w.s([], 'bwcarry', '( %s -> %s = %s )' % (AZ, CARRY('I'), KI('I')))
        f = w.s([v0], 'fveq2d', '( %s -> ( ( %s majBit %s ) ` %s ) = %s )' % (AZ, a_, b_, CARRY('I'), m_))
        e = w.s([v1, l4], 'eqtrd', '( %s -> %s = %s )' % (AZ, CARRY(I1), m_))
        w.qed([e, f], 'eqtr4d', '( %s -> %s = ( ( %s majBit %s ) ` %s ) )' % (AZ, CARRY(I1), a_, b_, CARRY('I'))); w.run()
