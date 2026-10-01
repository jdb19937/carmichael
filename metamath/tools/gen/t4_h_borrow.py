"""Sortie T4, group H: the borrow of A - B - C position by position, and the closed form of the borrow fold (T4-blueprint 3.5)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AZ = '( ( A e. ZZ /\\ B e. ZZ /\\ C e. 2o ) /\\ I e. NN0 )'
AZ0 = '( A e. ZZ /\\ B e. ZZ /\\ C e. 2o )'
MA = lambda I: '( A mod ( 2 ^ %s ) )' % I
MB = lambda I: '( B mod ( 2 ^ %s ) )' % I
BNC = '( bToNat ` C )'
RS = lambda I: '( %s - ( %s + ( bToNat ` C ) ) )' % (MA(I), MB(I))
BI = lambda I: 'if ( %s < ( %s + ( bToNat ` C ) ) , 1o , (/) )' % (MA(I), MB(I))
PK = '( 2 ^ I )'; PK1 = '( 2 ^ ( I + 1 ) )'; I1 = '( I + 1 )'
Dx = '( A - ( B + ( bToNat ` C ) ) )'
R = '( %s + ( %s x. ( bToNat ` %s ) ) )' % (RS('I'), PK, BI('I'))
a_ = BIT('A', 'I'); b_ = BIT('B', 'I'); k_ = BI('I')
s_ = OP3(a_, 'sumBit', b_, k_); m_ = OP3(a_, 'borrow', b_, k_)
BOR = lambda I: FOLD('borrow', 'A', 'B', 'C', I)
FSET = '~P ( ( 2o X. 2o ) X. ~P ( 3o X. 3o ) )'


def base(w, ante=AZ):
    a = w.s([], 'simpl1', '( %s -> A e. ZZ )' % ante); b = w.s([], 'simpl2', '( %s -> B e. ZZ )' % ante)
    c = w.s([], 'simpl3', '( %s -> C e. 2o )' % ante); i = w.s([], 'simpr', '( %s -> I e. NN0 )' % ante)
    return Cl(w, ante, {'A': ('ZZ', a), 'B': ('ZZ', b), 'C': ('2o', c), 'I': ('NN0', i)})


def modfacts(w, cl, X, I, ante):
    M = '( %s mod ( 2 ^ %s ) )' % (X, I); P = '( 2 ^ %s )' % I
    n0 = cl.mem(M, 'NN0')
    lt = w.s([cl.mem(X, 'RR'), cl.mem(P, 'RR+'), w.inst('modlt')], 'syl2anc', '( %s -> %s < %s )' % (ante, M, P))
    le1 = w.s([cl.mem(M, 'ZZ'), cl.mem(P, 'ZZ'), w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (ante, M, P, M, P))
    le = w.s([lt, le1], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (ante, M, P))
    return n0, lt, le


def bnval(w, a2, K, eq, v):
    """( a2 -> ( bToNat ` K ) = lit ) from ( a2 -> K = v )"""
    f = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` %s ) )' % (a2, K, v))
    c = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, '1' if v == '1o' else '0'))
    return w.s([f, c], 'eqtrdi', '( %s -> ( bToNat ` %s ) = %s )' % (a2, K, '1' if v == '1o' else '0'))


def prodval(w, a2, P, K, bnstep, v, pcc):
    """( a2 -> ( P x. ( bToNat ` K ) ) = P or 0 )"""
    PR = '( %s x. ( bToNat ` %s ) )' % (P, K)
    o = w.s([bnstep], 'oveq2d', '( %s -> %s = ( %s x. %s ) )' % (a2, PR, P, '1' if v == '1o' else '0'))
    if v == '1o':
        m = w.s([pcc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (a2, P, P))
        return w.s([o, m], 'eqtrd', '( %s -> %s = %s )' % (a2, PR, P))
    m = w.s([pcc], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (a2, P))
    return w.s([o, m], 'eqtrd', '( %s -> %s = 0 )' % (a2, PR))


if __name__ == '__main__':
    if want('bwsublem1'):
        w = W('bwsublem1', 'Lemma for the borrow: the partial difference plus the borrow weight lies in [ 0 , 2 ^ I ).')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR'))
        na, lta, lea = modfacts(w, cl, 'A', 'I', AZ); nb, ltb, leb = modfacts(w, cl, 'B', 'I', AZ)
        cl.atom(MA('I')); cl.atom(MB('I'))
        bnle = w.s([cl.mem('C', '2o'), w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AZ, BNC)); bng = cl.ge0(BNC); cl.atom(BNC)
        PR = '( %s x. ( bToNat ` %s ) )' % (PK, k_)
        concl = '( 0 <_ %s /\\ %s < %s )' % (R, R, PK)
        cond = '%s < ( %s + ( bToNat ` C ) )' % (MA('I'), MB('I'))
        outs = []
        for case in (True, False):
            a2 = '( %s /\\ %s )' % (AZ, cond) if case else '( %s /\\ -. %s )' % (AZ, cond)
            h = w.s([], 'simpr', '( %s -> %s )' % (a2, cond if case else '-. ' + cond))
            c2 = Cl(w, a2, {}); c2.parent = cl
            for E in (PK, MA('I'), MB('I'), BNC, PR):
                c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
            pcc = lift(w, cl.mem(PK, 'CC'), a2)
            if case:
                it = w.s([h], 'iftrued', '( %s -> %s = 1o )' % (a2, k_))
                pe = prodval(w, a2, PK, k_, bnval(w, a2, k_, it, '1o'), '1o', pcc)
                hyps = [h, pe, lift(w, leb, a2), lift(w, bnle, a2), lift(w, cl.ge0(MA('I')), a2)]
            else:
                ln = w.s([lift(w, cl.mem('( %s + ( bToNat ` C ) )' % MB('I'), 'RR'), a2), lift(w, cl.mem(MA('I'), 'RR'), a2), w.inst('lenlt')], 'syl2anc', '( %s -> ( ( %s + ( bToNat ` C ) ) <_ %s <-> -. %s ) )' % (a2, MB('I'), MA('I'), cond))
                ge = w.s([h, ln], 'mpbird', '( %s -> ( %s + ( bToNat ` C ) ) <_ %s )' % (a2, MB('I'), MA('I')))
                it = w.s([h], 'iffalsed', '( %s -> %s = (/) )' % (a2, k_))
                pe = prodval(w, a2, PK, k_, bnval(w, a2, k_, it, '(/)'), '(/)', pcc)
                hyps = [ge, pe, lift(w, lta, a2), lift(w, cl.ge0(MB('I')), a2), lift(w, bng, a2)]
            g1 = linarith(w, a2, hyps, '0 <_ %s' % R, closure=c2)
            g2 = linarith(w, a2, hyps, '%s < %s' % (R, PK), closure=c2)
            outs.append(w.s([g1, g2], 'jca', '( %s -> %s )' % (a2, concl)))
        w.qed(outs, 'pm2.61dan', '( %s -> %s )' % (AZ, concl)); w.run()

    def dmod(w, cl, ante, I, P):
        """( ante -> ( Dx mod P ) = ( RS(I) mod P ) )"""
        ar = cl.mem('A', 'RR'); br = cl.mem('B', 'RR'); pr = cl.mem(P, 'RR+'); cr = cl.mem(BNC, 'RR')
        ma = cl.mem(MA(I), 'RR'); mb = cl.mem(MB(I), 'RR')
        aa = w.s([ar, pr, w.inst('modabs2')], 'syl2anc', '( %s -> ( %s mod %s ) = ( A mod %s ) )' % (ante, MA(I), P, P))
        bb = w.s([br, cr, pr, w.inst('modaddmod')], 'syl3anc', '( %s -> ( ( %s + %s ) mod %s ) = ( ( B + %s ) mod %s ) )' % (ante, MB(I), BNC, P, BNC, P))
        s1 = cl.mem('( %s + %s )' % (MB(I), BNC), 'RR'); s2 = cl.mem('( B + %s )' % BNC, 'RR')
        m = w.s([ma, ar, s1, s2, pr, aa, bb], 'modsub12d', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (ante, RS(I), P, Dx, P))
        return w.s([m], 'eqcomd', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (ante, Dx, P, RS(I), P))

    if want('bwsublem2'):
        w = W('bwsublem2', 'Lemma for the borrow: the residue of the difference modulo 2 ^ I is the partial difference plus the borrow weight.')
        cl = base(w)
        dm = dmod(w, cl, AZ, 'I', PK)
        pr = cl.mem(PK, 'RR+'); kz = cl.mem('( bToNat ` %s )' % k_, 'ZZ'); rs = cl.mem(RS('I'), 'RR')
        mc = w.s([rs, pr, kz, w.inst('modcyc')], 'syl3anc', '( %s -> ( ( %s + ( ( bToNat ` %s ) x. %s ) ) mod %s ) = ( %s mod %s ) )' % (AZ, RS('I'), k_, PK, PK, RS('I'), PK))
        com = w.s([cl.mem(PK, 'CC'), cl.mem('( bToNat ` %s )' % k_, 'CC')], 'mulcomd', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( ( bToNat ` %s ) x. %s ) )' % (AZ, PK, k_, k_, PK))
        com2 = w.s([com], 'oveq2d', '( %s -> %s = ( %s + ( ( bToNat ` %s ) x. %s ) ) )' % (AZ, R, RS('I'), k_, PK))
        com3 = w.s([com2], 'oveq1d', '( %s -> ( %s mod %s ) = ( ( %s + ( ( bToNat ` %s ) x. %s ) ) mod %s ) )' % (AZ, R, PK, RS('I'), k_, PK, PK))
        l1 = w.s([], 'bwsublem1', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (AZ, R, R, PK))
        j = w.s([cl.mem(R, 'RR'), pr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (AZ, R, PK))
        mi = w.s([j, l1, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (AZ, R, PK, R))
        ch = w.s([com3, mc], 'eqtrd', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (AZ, R, PK, RS('I'), PK))
        ch2 = w.s([ch, mi], 'eqtr3d', '( %s -> ( %s mod %s ) = %s )' % (AZ, RS('I'), PK, R))
        w.qed([dm, ch2], 'eqtrd', '( %s -> ( %s mod %s ) = %s )' % (AZ, Dx, PK, R)); w.run()

    X = '( %s + ( %s x. ( bToNat ` %s ) ) )' % (R, PK, s_)
    if want('bwsublem3'):
        w = W('bwsublem3', 'Lemma for the borrow: the partial difference at I + 1 is the low part plus the difference bit at its weight minus the borrow bit at the next weight.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR'))
        for E in (MA('I'), MB('I'), BNC, '( bToNat ` %s )' % a_, '( bToNat ` %s )' % b_, '( bToNat ` %s )' % k_, '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        pa = w.s([cl.mem('A', 'ZZ'), cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, MA(I1), MA('I'), PK, a_))
        pb = w.s([cl.mem('B', 'ZZ'), cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> %s = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, MB(I1), MB('I'), PK, b_))
        fs = w.s([cl.mem(a_, '2o'), cl.mem(b_, '2o'), cl.mem(k_, '2o'), w.inst('bwfullsub')], 'syl3anc',
                 '( %s -> ( ( ( bToNat ` %s ) - ( bToNat ` %s ) ) - ( bToNat ` %s ) ) = ( ( bToNat ` %s ) - ( 2 x. ( bToNat ` %s ) ) ) )' % (AZ, a_, b_, k_, s_, m_))
        mfs = w.s([fs], 'oveq2d', '( %s -> ( %s x. ( ( ( bToNat ` %s ) - ( bToNat ` %s ) ) - ( bToNat ` %s ) ) ) = ( %s x. ( ( bToNat ` %s ) - ( 2 x. ( bToNat ` %s ) ) ) ) )' % (AZ, PK, a_, b_, k_, PK, s_, m_))
        goal_rhs = '( %s - ( ( %s x. 2 ) x. ( bToNat ` %s ) ) )' % (X, PK, m_)
        lineq(w, AZ, RS(I1), goal_rhs, hyps=[pa, pb, mfs], closure=cl, products=True, name='qed'); w.run()

    def xbounds(w, cl, ante):
        """steps: 0 <_ R, R <_ PK - 1, ( PK x. bns ) <_ PK, 0 <_ ( PK x. bns ), PK1 = PK x. 2"""
        l1 = w.s([], 'bwsublem1', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (ante, R, R, PK))
        r0 = w.s([l1], 'simpld', '( %s -> 0 <_ %s )' % (ante, R)); r1 = w.s([l1], 'simprd', '( %s -> %s < %s )' % (ante, R, PK))
        r2 = w.s([cl.mem(R, 'ZZ'), cl.mem(PK, 'ZZ'), w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (ante, R, PK, R, PK)); r3 = w.s([r1, r2], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (ante, R, PK))
        sle = w.s([cl.mem(s_, '2o'), w.inst('bwbnle1')], 'syl', '( %s -> ( bToNat ` %s ) <_ 1 )' % (ante, s_)); sg = cl.ge0('( bToNat ` %s )' % s_)
        ps = w.s([cl.mem('( bToNat ` %s )' % s_, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % ante), cl.mem(PK, 'RR'), cl.ge0(PK), sle], 'lemul2ad', '( %s -> ( %s x. ( bToNat ` %s ) ) <_ ( %s x. 1 ) )' % (ante, PK, s_, PK))
        p1 = w.s([cl.mem(PK, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (ante, PK, PK)); ps2 = w.s([ps, p1], 'breqtrd', '( %s -> ( %s x. ( bToNat ` %s ) ) <_ %s )' % (ante, PK, s_, PK))
        psg = w.s([cl.mem(PK, 'RR'), cl.mem('( bToNat ` %s )' % s_, 'RR'), cl.ge0(PK), sg], 'mulge0d', '( %s -> 0 <_ ( %s x. ( bToNat ` %s ) ) )' % (ante, PK, s_))
        ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ante), cl.mem('I', 'NN0'), w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ante, PK1, PK))
        return r0, r3, ps2, psg, ep

    if want('bwsublem4'):
        w = W('bwsublem4', 'Lemma for the borrow: the borrow into position I + 1 is the borrow of the two digits at I and the borrow into I.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR')); cl.leaf(PK1, 'RR', cl.mem(PK1, 'RR'))
        for E in (R, '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_, '( %s x. ( bToNat ` %s ) )' % (PK, s_), MA(I1), MB(I1), BNC):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        r0, r3, ps2, psg, ep = xbounds(w, cl, AZ)
        l3 = w.s([], 'bwsublem3', '( %s -> %s = ( %s - ( ( %s x. 2 ) x. ( bToNat ` %s ) ) ) )' % (AZ, RS(I1), X, PK, m_))
        concl = '%s = %s' % (BI(I1), m_)
        mm = cl.mem(m_, '2o')
        cond1 = '%s < ( %s + ( bToNat ` C ) )' % (MA(I1), MB(I1))

        def body(a2, eq, v):
            PM = '( ( %s x. 2 ) x. ( bToNat ` %s ) )' % (PK, m_)
            f2 = prodval(w, a2, '( %s x. 2 )' % PK, m_, bnval(w, a2, m_, eq, v), v, lift(w, cl.mem('( %s x. 2 )' % PK, 'CC'), a2))
            c2 = Cl(w, a2, {}); c2.parent = cl
            for E in (R, '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_, '( %s x. ( bToNat ` %s ) )' % (PK, s_), MA(I1), MB(I1), BNC, PK, PK1, PM):
                c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
            hyps = [lift(w, x, a2) for x in (r0, r3, l3, ps2, psg, ep)] + [f2]
            if v == '1o':
                g = linarith(w, a2, hyps, cond1, closure=c2)
                it = w.s([g], 'iftrued', '( %s -> %s = 1o )' % (a2, BI(I1)))
            else:
                g = linarith(w, a2, hyps, '( %s + ( bToNat ` C ) ) <_ %s' % (MB(I1), MA(I1)), closure=c2)
                ln = w.s([lift(w, cl.mem('( %s + ( bToNat ` C ) )' % MB(I1), 'RR'), a2), lift(w, cl.mem(MA(I1), 'RR'), a2), w.inst('lenlt')], 'syl2anc', '( %s -> ( ( %s + ( bToNat ` C ) ) <_ %s <-> -. %s ) )' % (a2, MB(I1), MA(I1), cond1))
                ng = w.s([g, ln], 'mpbid', '( %s -> -. %s )' % (a2, cond1))
                it = w.s([ng], 'iffalsed', '( %s -> %s = (/) )' % (a2, BI(I1)))
            return w.s([it, eq], 'eqtr4d', '( %s -> %s )' % (a2, concl))
        st = cases2o(w, AZ, m_, mm, body, concl); promote(w, st); w.run()

    if want('bwsublem5'):
        w = W('bwsublem5', 'Lemma for the borrow: the residue of the difference modulo 2 ^ ( I + 1 ) is the low part plus the difference bit at its weight.')
        cl = base(w)
        cl.atom(PK); cl.leaf(PK, 'RR', cl.mem(PK, 'RR')); cl.leaf(PK1, 'RR', cl.mem(PK1, 'RR'))
        for E in (R, '( bToNat ` %s )' % s_, '( %s x. ( bToNat ` %s ) )' % (PK, s_)):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        cl.have(X, 'RR', cl.mem(X, 'RR'))
        dm = dmod(w, cl, AZ, I1, PK1)
        l3 = w.s([], 'bwsublem3', '( %s -> %s = ( %s - ( ( %s x. 2 ) x. ( bToNat ` %s ) ) ) )' % (AZ, RS(I1), X, PK, m_))
        r0, r3, ps2, psg, ep = xbounds(w, cl, AZ)
        ep2 = w.s([ep], 'oveq1d', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( ( %s x. 2 ) x. ( bToNat ` %s ) ) )' % (AZ, PK1, m_, PK, m_))
        ep3 = w.s([ep2], 'oveq2d', '( %s -> ( %s - ( %s x. ( bToNat ` %s ) ) ) = ( %s - ( ( %s x. 2 ) x. ( bToNat ` %s ) ) ) )' % (AZ, X, PK1, m_, X, PK, m_))
        l3b = w.s([l3, ep3], 'eqtr4d', '( %s -> %s = ( %s - ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, RS(I1), X, PK1, m_))
        pr = cl.mem(PK1, 'RR+'); mz = cl.mem('( bToNat ` %s )' % m_, 'ZZ')
        mc = w.s([cl.mem(X, 'RR'), pr, mz, w.inst('modcyc2')], 'syl3anc', '( %s -> ( ( %s - ( %s x. ( bToNat ` %s ) ) ) mod %s ) = ( %s mod %s ) )' % (AZ, X, PK1, m_, PK1, X, PK1))
        o = w.s([l3b], 'oveq1d', '( %s -> ( %s mod %s ) = ( ( %s - ( %s x. ( bToNat ` %s ) ) ) mod %s ) )' % (AZ, RS(I1), PK1, X, PK1, m_, PK1))
        g0 = linarith(w, AZ, [r0, psg], '0 <_ %s' % X, closure=cl)
        g1 = linarith(w, AZ, [r3, ps2, ep], '%s < %s' % (X, PK1), closure=cl)
        j = w.s([cl.mem(X, 'RR'), pr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (AZ, X, PK1)); j2 = w.s([g0, g1], 'jca', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (AZ, X, X, PK1))
        mi = w.s([j, j2, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (AZ, X, PK1, X))
        ch = w.s([o, mc, mi], '3eqtrd', '( %s -> ( %s mod %s ) = %s )' % (AZ, RS(I1), PK1, X))
        w.qed([dm, ch], 'eqtrd', '( %s -> ( %s mod %s ) = %s )' % (AZ, Dx, PK1, X)); w.run()

    if want('bwsubdig'):
        w = W('bwsubdig', 'The I-th digit of A - B - C is the sum bit of the two digits at I and the borrow into I.')
        cl = base(w)
        dz = cl.mem(Dx, 'ZZ')
        p1 = w.s([dz, cl.mem('I', 'NN0'), w.inst('bwmodp1')], 'syl2anc', '( %s -> ( %s mod %s ) = ( ( %s mod %s ) + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Dx, PK1, Dx, PK, PK, BIT(Dx, 'I')))
        l2 = w.s([], 'bwsublem2', '( %s -> ( %s mod %s ) = %s )' % (AZ, Dx, PK, R))
        o = w.s([l2], 'oveq1d', '( %s -> ( ( %s mod %s ) + ( %s x. ( bToNat ` %s ) ) ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Dx, PK, PK, BIT(Dx, 'I'), R, PK, BIT(Dx, 'I')))
        l5 = w.s([], 'bwsublem5', '( %s -> ( %s mod %s ) = %s )' % (AZ, Dx, PK1, X))
        po = w.s([p1, o], 'eqtrd', '( %s -> ( %s mod %s ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, Dx, PK1, R, PK, BIT(Dx, 'I')))
        e = w.s([po, l5], 'eqtr3d', '( %s -> ( %s + ( %s x. ( bToNat ` %s ) ) ) = %s )' % (AZ, R, PK, BIT(Dx, 'I'), X))
        rc = cl.mem(R, 'CC'); x1 = cl.mem('( %s x. ( bToNat ` %s ) )' % (PK, BIT(Dx, 'I')), 'CC'); x2 = cl.mem('( %s x. ( bToNat ` %s ) )' % (PK, s_), 'CC')
        ac = w.s([rc, x1, x2], 'addcand', '( %s -> ( ( %s + ( %s x. ( bToNat ` %s ) ) ) = %s <-> ( %s x. ( bToNat ` %s ) ) = ( %s x. ( bToNat ` %s ) ) ) )' % (AZ, R, PK, BIT(Dx, 'I'), X, PK, BIT(Dx, 'I'), PK, s_))
        e2 = w.s([e, ac], 'mpbid', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( %s x. ( bToNat ` %s ) ) )' % (AZ, PK, BIT(Dx, 'I'), PK, s_))
        b1 = cl.mem('( bToNat ` %s )' % BIT(Dx, 'I'), 'CC'); b2 = cl.mem('( bToNat ` %s )' % s_, 'CC'); pc = cl.mem(PK, 'CC'); pne = cl.ne0(PK)
        mc = w.s([b1, b2, pc, pne], 'mulcand', '( %s -> ( ( %s x. ( bToNat ` %s ) ) = ( %s x. ( bToNat ` %s ) ) <-> ( bToNat ` %s ) = ( bToNat ` %s ) ) )' % (AZ, PK, BIT(Dx, 'I'), PK, s_, BIT(Dx, 'I'), s_))
        e3 = w.s([e2, mc], 'mpbid', '( %s -> ( bToNat ` %s ) = ( bToNat ` %s ) )' % (AZ, BIT(Dx, 'I'), s_))
        inj = w.s([cl.mem(BIT(Dx, 'I'), '2o'), cl.mem(s_, '2o'), w.inst('bwbn11')], 'syl2anc', '( %s -> ( ( bToNat ` %s ) = ( bToNat ` %s ) <-> %s = %s ) )' % (AZ, BIT(Dx, 'I'), s_, BIT(Dx, 'I'), s_))
        e4 = w.s([e3, inj], 'mpbid', '( %s -> %s = %s )' % (AZ, BIT(Dx, 'I'), s_))
        e5 = w.s([e4], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (AZ, BIT(Dx, 'I'), s_))
        n0 = w.s([], '1n0', '1o =/= (/)'); tb = w.s([n0, w.inst('iftrueb')], 'ax-mp', '( %s = 1o <-> I e. ( bits ` %s ) )' % (BIT(Dx, 'I'), Dx))
        tbd = w.s([tb], 'a1i', '( %s -> ( %s = 1o <-> I e. ( bits ` %s ) ) )' % (AZ, BIT(Dx, 'I'), Dx))
        w.qed([tbd, e5], 'bitr3d', '( %s -> ( I e. ( bits ` %s ) <-> %s = 1o ) )' % (AZ, Dx, s_)); w.run()

    if want('bwborrow'):
        w = W('bwborrow', 'The borrow fold is the borrow: the borrow into position I of A - B - C is set exactly when the low I bits of A fall short.')
        P = lambda I: '%s = %s' % (BOR(I), BI(I))
        x0 = w.s([], 'id', '( x = 0 -> x = 0 )'); h1, _ = w.wcongr(P('x'), {'x': '0'}, 'x = 0', {'x': x0})
        xy = w.s([], 'id', '( x = y -> x = y )'); h2, _ = w.wcongr(P('x'), {'x': 'y'}, 'x = y', {'x': xy})
        xy1 = w.s([], 'id', '( x = ( y + 1 ) -> x = ( y + 1 ) )'); h3, _ = w.wcongr(P('x'), {'x': '( y + 1 )'}, 'x = ( y + 1 )', {'x': xy1})
        xI = w.s([], 'id', '( x = I -> x = I )'); h4, _ = w.wcongr(P('x'), {'x': 'I'}, 'x = I', {'x': xI})
        a = w.s([], 'simp1', '( %s -> A e. ZZ )' % AZ0); b = w.s([], 'simp2', '( %s -> B e. ZZ )' % AZ0); c = w.s([], 'simp3', '( %s -> C e. 2o )' % AZ0)
        cl0 = Cl(w, AZ0, {'A': ('ZZ', a), 'B': ('ZZ', b), 'C': ('2o', c)})
        fs = w.s([], 'borrowfs', 'borrow e. %s' % FSET); fsd = w.s([fs], 'a1i', '( %s -> borrow e. %s )' % (AZ0, FSET))
        c3 = cl0.mem('C', '3o')
        jab = w.s([a, b], 'jca', '( %s -> ( A e. ZZ /\\ B e. ZZ ) )' % AZ0); jfc = w.s([fsd, c3], 'jca', '( %s -> ( borrow e. %s /\\ C e. 3o ) )' % (AZ0, FSET))
        af = w.s([jab, jfc], 'jca', '( %s -> ( ( A e. ZZ /\\ B e. ZZ ) /\\ ( borrow e. %s /\\ C e. 3o ) ) )' % (AZ0, FSET))
        f0 = w.s([af, w.inst('bwfold0')], 'syl', '( %s -> %s = C )' % (AZ0, BOR('0')))
        ma0 = w.s([a, w.inst('zmod10')], 'syl', '( %s -> ( A mod 1 ) = 0 )' % AZ0); mb0 = w.s([b, w.inst('zmod10')], 'syl', '( %s -> ( B mod 1 ) = 0 )' % AZ0)
        tc = w.s([], '2cn', '2 e. CC'); e0 = w.s([tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % AZ0)
        oa = w.s([e0d], 'oveq2d', '( %s -> ( A mod ( 2 ^ 0 ) ) = ( A mod 1 ) )' % AZ0); oa2 = w.s([oa, ma0], 'eqtrd', '( %s -> ( A mod ( 2 ^ 0 ) ) = 0 )' % AZ0)
        ob = w.s([e0d], 'oveq2d', '( %s -> ( B mod ( 2 ^ 0 ) ) = ( B mod 1 ) )' % AZ0); ob2 = w.s([ob, mb0], 'eqtrd', '( %s -> ( B mod ( 2 ^ 0 ) ) = 0 )' % AZ0)
        bc = cl0.mem(BNC, 'CC'); s0 = w.s([ob2], 'oveq1d', '( %s -> ( %s + %s ) = ( 0 + %s ) )' % (AZ0, MB('0'), BNC, BNC)); s0b = w.s([s0, w.s([bc], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AZ0, BNC, BNC))], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (AZ0, MB('0'), BNC, BNC))
        br = w.s([oa2, s0b], 'breq12d', '( %s -> ( %s < ( %s + %s ) <-> 0 < %s ) )' % (AZ0, MA('0'), MB('0'), BNC, BNC))
        # 0 < bn C <-> C = 1o
        bn0 = cl0.mem(BNC, 'NN0')
        g1 = w.s([bn0], 'nn0zd', '( %s -> %s e. ZZ )' % (AZ0, BNC)); zg = w.s([g1, w.inst('zgt0ge1')], 'syl', '( %s -> ( 0 < %s <-> 1 <_ %s ) )' % (AZ0, BNC, BNC))
        bnle = w.s([c, w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AZ0, BNC))
        bnr = cl0.mem(BNC, 'RR'); onr = w.s([], '1red', '( %s -> 1 e. RR )' % AZ0)
        t3 = w.s([onr, bnr, w.inst('letri3')], 'syl2anc', '( %s -> ( 1 = %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AZ0, BNC, BNC, BNC))
        bt = w.s([bnle], 'biantrud', '( %s -> ( 1 <_ %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AZ0, BNC, BNC, BNC))
        b13 = w.s([bt, t3], 'bitr4d', '( %s -> ( 1 <_ %s <-> 1 = %s ) )' % (AZ0, BNC, BNC))
        ec = w.s([], 'eqcom', '( 1 = %s <-> %s = 1 )' % (BNC, BNC)); ecd = w.s([ec], 'a1i', '( %s -> ( 1 = %s <-> %s = 1 ) )' % (AZ0, BNC, BNC))
        bq = w.s([c, w.inst('bwbneq1')], 'syl', '( %s -> ( %s = 1 <-> C = 1o ) )' % (AZ0, BNC))
        bb1 = w.s([br, zg], 'bitrd', '( %s -> ( %s < ( %s + %s ) <-> 1 <_ %s ) )' % (AZ0, MA('0'), MB('0'), BNC, BNC))
        bb2 = w.s([bb1, b13], 'bitrd', '( %s -> ( %s < ( %s + %s ) <-> 1 = %s ) )' % (AZ0, MA('0'), MB('0'), BNC, BNC))
        bb3 = w.s([bb2, ecd], 'bitrd', '( %s -> ( %s < ( %s + %s ) <-> %s = 1 ) )' % (AZ0, MA('0'), MB('0'), BNC, BNC))
        bb4 = w.s([bb3, bq], 'bitrd', '( %s -> ( %s < ( %s + %s ) <-> C = 1o ) )' % (AZ0, MA('0'), MB('0'), BNC))
        ib = w.s([bb4], 'ifbid', '( %s -> %s = if ( C = 1o , 1o , (/) ) )' % (AZ0, BI('0')))
        cb = bool_from_bi(w, AZ0, 'C', 'C = 1o', w.s([], 'biidd', '( %s -> ( C = 1o <-> C = 1o ) )' % AZ0), c)
        k0 = w.s([ib, cb], 'eqtr4d', '( %s -> %s = C )' % (AZ0, BI('0')))
        base_ = w.s([f0, k0], 'eqtr4d', '( %s -> %s )' % (AZ0, P('0')))
        AY = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (AZ0, P('y'))
        ih = w.s([], 'simpr', '( %s -> %s )' % (AY, P('y'))); yn = w.s([], 'simplr', '( %s -> y e. NN0 )' % AY); az = w.s([], 'simpll', '( %s -> %s )' % (AY, AZ0))
        azy = w.s([az, yn], 'jca', '( %s -> ( %s /\\ y e. NN0 ) )' % (AY, AZ0))
        cly = Cl(w, AY, {'A': ('ZZ', lift(w, a, AY)), 'B': ('ZZ', lift(w, b, AY)), 'C': ('2o', lift(w, c, AY)), 'y': ('NN0', yn)})
        ky3 = cly.mem(BI('y'), '3o')
        lv3 = w.s([ih, ky3], 'eqeltrd', '( %s -> %s e. 3o )' % (AY, BOR('y')))
        aff = w.s([az, af], 'syl', '( %s -> ( ( A e. ZZ /\\ B e. ZZ ) /\\ ( borrow e. %s /\\ C e. 3o ) ) )' % (AY, FSET))
        jy = w.s([yn, lv3], 'jca', '( %s -> ( y e. NN0 /\\ %s e. 3o ) )' % (AY, BOR('y')))
        p1 = w.s([aff, jy, w.inst('bwfoldp1')], 'syl2anc', '( %s -> %s = ( ( %s borrow %s ) ` %s ) )' % (AY, BOR('( y + 1 )'), BIT('A', 'y'), BIT('B', 'y'), BOR('y')))
        f = w.s([ih], 'fveq2d', '( %s -> ( ( %s borrow %s ) ` %s ) = ( ( %s borrow %s ) ` %s ) )' % (AY, BIT('A', 'y'), BIT('B', 'y'), BOR('y'), BIT('A', 'y'), BIT('B', 'y'), BI('y')))
        l4 = w.s([azy, w.inst('bwsublem4')], 'syl', '( %s -> %s = ( ( %s borrow %s ) ` %s ) )' % (AY, BI('( y + 1 )'), BIT('A', 'y'), BIT('B', 'y'), BI('y')))
        step = w.s([p1, f, l4], '3eqtr4d', '( %s -> %s )' % (AY, P('( y + 1 )')))
        st = w.s([h1, h2, h3, h4, base_, step], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (AZ0, P('I')))
        promote(w, st); w.run()

    if want('bwborrowcl'):
        w = W('bwborrowcl', 'The borrow is a Boolean.')
        cl = base(w)
        v = w.s([], 'bwborrow', '( %s -> %s = %s )' % (AZ, BOR('I'), BI('I'))); m = cl.mem(BI('I'), '2o')
        w.qed([v, m], 'eqeltrd', '( %s -> %s e. 2o )' % (AZ, BOR('I'))); w.run()
    if want('bwborrowp1'):
        w = W('bwborrowp1', 'The borrow into position I + 1 is the borrow of the two digits at I and the borrow into I (the recursive form, unconditionally).')
        cl = base(w)
        i1 = cl.mem(I1, 'NN0'); az0 = w.s([], 'simpl', '( %s -> %s )' % (AZ, AZ0))
        v1 = w.s([az0, i1, w.inst('bwborrow')], 'syl2anc', '( %s -> %s = %s )' % (AZ, BOR(I1), BI(I1)))
        l4 = w.s([], 'bwsublem4', '( %s -> %s = %s )' % (AZ, BI(I1), m_))
        v0 = w.s([], 'bwborrow', '( %s -> %s = %s )' % (AZ, BOR('I'), BI('I')))
        f = w.s([v0], 'fveq2d', '( %s -> ( ( %s borrow %s ) ` %s ) = %s )' % (AZ, a_, b_, BOR('I'), m_))
        e = w.s([v1, l4], 'eqtrd', '( %s -> %s = %s )' % (AZ, BOR(I1), m_))
        w.qed([e, f], 'eqtr4d', '( %s -> %s = ( ( %s borrow %s ) ` %s ) )' % (AZ, BOR(I1), a_, b_, BOR('I'))); w.run()
