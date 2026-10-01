"""Sortie T4b, group A: toNat of concatenations, prefixes, suffixes, the words
of ones and of zeros, the parity lemma, bl of a power of two (T4b-blueprint 1.1)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4blib import *
from lin import linarith, lineq
import a4alib
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AL = 'L e. Word 2o'
AB = 'B e. 2o'
AE = 'E e. NN0'
REP0 = lambda N: '( (/) repeatS %s )' % N
REP1 = lambda N: '( 1o repeatS %s )' % N


def exp0_1(w, ante):
    """( ante -> ( 2 ^ 0 ) = 1 )"""
    tc = num.closed(w, [], '2cn', '2 e. CC'); e0 = num.closed(w, [tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')
    return w.s([e0], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % ante)


def pow_len0(w, ante):
    """( ante -> ( 2 ^ ( # ` (/) ) ) = 1 )"""
    h0 = w.s([num.closed(w, [], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ante)
    p0 = w.s([h0], 'oveq2d', '( %s -> ( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 ) )' % ante)
    return w.s([p0, exp0_1(w, ante)], 'eqtrd', '( %s -> ( 2 ^ ( # ` (/) ) ) = 1 )' % ante)


if __name__ == '__main__':
    if want('tonats1'):
        w = W('tonats1', 'The value of a one-letter bit word is the value of its letter.')
        b = w.s([], 'id', '( %s -> B e. 2o )' % AB)
        cl = Cl(w, AB, {'B': ('2o', b)})
        S1 = '<" B ">'; BNB = BN('B')
        e1 = w.s([cl.mem(S1, 'Word 2o'), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (AB, S1, S1))
        ts = w.s([cl.mem('(/)', 'Word 2o'), b, w.inst('tonatsnoc')], 'syl2anc', '( %s -> ( toNat ` ( (/) ++ %s ) ) = ( ( toNat ` (/) ) + ( %s x. ( 2 ^ ( # ` (/) ) ) ) ) )' % (AB, S1, BNB))
        t0 = w.s([num.closed(w, [], 'tonat0', '( toNat ` (/) ) = 0')], 'a1i', '( %s -> ( toNat ` (/) ) = 0 )' % AB)
        p1 = pow_len0(w, AB)
        m = w.s([p1], 'oveq2d', '( %s -> ( %s x. ( 2 ^ ( # ` (/) ) ) ) = ( %s x. 1 ) )' % (AB, BNB, BNB))
        m1 = w.s([cl.mem(BNB, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AB, BNB, BNB))
        m2 = w.s([m, m1], 'eqtrd', '( %s -> ( %s x. ( 2 ^ ( # ` (/) ) ) ) = %s )' % (AB, BNB, BNB))
        ad = w.s([t0, m2], 'oveq12d', '( %s -> ( ( toNat ` (/) ) + ( %s x. ( 2 ^ ( # ` (/) ) ) ) ) = ( 0 + %s ) )' % (AB, BNB, BNB))
        a0 = w.s([cl.mem(BNB, 'CC')], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AB, BNB, BNB))
        val = w.s([ts, ad, a0], '3eqtrd', '( %s -> ( toNat ` ( (/) ++ %s ) ) = %s )' % (AB, S1, BNB))
        f = w.s([e1], 'fveq2d', '( %s -> ( toNat ` ( (/) ++ %s ) ) = ( toNat ` %s ) )' % (AB, S1, S1))
        w.qed([f, val], 'eqtr3d', '( %s -> ( toNat ` %s ) = %s )' % (AB, S1, BNB)); w.run()

    AK = 'K e. Word 2o'
    PHI = lambda s: '( K e. Word 2o -> ( toNat ` ( %s ++ K ) ) = ( ( toNat ` %s ) + ( ( 2 ^ ( # ` %s ) ) x. ( toNat ` K ) ) ) )' % (s, s, s)
    if want('tonatccatlem1'):
        w = W('tonatccatlem1', 'Lemma for tonatccat: the empty first word.')
        k = w.s([], 'id', '( %s -> K e. Word 2o )' % AK)
        cl = Cl(w, AK, {'K': ('Word 2o', k)})
        TK = TN('K')
        e1 = w.s([k, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ K ) = K )' % AK)
        f = w.s([e1], 'fveq2d', '( %s -> ( toNat ` ( (/) ++ K ) ) = ( toNat ` K ) )' % AK)
        t0 = w.s([num.closed(w, [], 'tonat0', '( toNat ` (/) ) = 0')], 'a1i', '( %s -> ( toNat ` (/) ) = 0 )' % AK)
        p1 = pow_len0(w, AK)
        m = w.s([p1], 'oveq1d', '( %s -> ( ( 2 ^ ( # ` (/) ) ) x. %s ) = ( 1 x. %s ) )' % (AK, TK, TK))
        m1 = w.s([cl.mem(TK, 'CC')], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (AK, TK, TK))
        m2 = w.s([m, m1], 'eqtrd', '( %s -> ( ( 2 ^ ( # ` (/) ) ) x. %s ) = %s )' % (AK, TK, TK))
        ad = w.s([t0, m2], 'oveq12d', '( %s -> ( ( toNat ` (/) ) + ( ( 2 ^ ( # ` (/) ) ) x. %s ) ) = ( 0 + %s ) )' % (AK, TK, TK))
        a0 = w.s([cl.mem(TK, 'CC')], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AK, TK, TK))
        r = w.s([ad, a0], 'eqtrd', '( %s -> ( ( toNat ` (/) ) + ( ( 2 ^ ( # ` (/) ) ) x. %s ) ) = %s )' % (AK, TK, TK))
        w.qed([f, r], 'eqtr4d', PHI('(/)')); w.run()

    if want('tonatccatlem2'):
        A3 = '( a e. Word 2o /\\ b e. 2o /\\ %s )' % PHI('a')
        A4 = '( %s /\\ K e. Word 2o )' % A3
        w = W('tonatccatlem2', 'Lemma for tonatccat: the induction step, a letter prepended to the first word.')
        aw = w.s([], 'simpl1', '( %s -> a e. Word 2o )' % A4); bb = w.s([], 'simpl2', '( %s -> b e. 2o )' % A4)
        ih0 = w.s([], 'simpl3', '( %s -> %s )' % (A4, PHI('a'))); kw = w.s([], 'simpr', '( %s -> K e. Word 2o )' % A4)
        cl = Cl(w, A4, {'a': ('Word 2o', aw), 'b': ('2o', bb), 'K': ('Word 2o', kw)})
        TA = TN('a'); TK = TN('K'); P = P2(LEN('a')); BNB = BN('b')
        ih = w.s([kw, ih0], 'mpd', '( %s -> ( toNat ` ( a ++ K ) ) = ( %s + ( %s x. %s ) ) )' % (A4, TA, P, TK))
        CA = CONS('b', 'a'); AK_ = '( a ++ K )'
        ca = w.s([cl.mem('<" b ">', 'Word 2o'), aw, kw, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ K ) = ( <" b "> ++ %s ) )' % (A4, CA, AK_))
        tc1 = w.s([bb, cl.mem(AK_, 'Word 2o'), w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` ( <" b "> ++ %s ) ) = ( %s + ( 2 x. ( toNat ` %s ) ) ) )' % (A4, AK_, BNB, AK_))
        tc2 = w.s([bb, aw, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( %s + ( 2 x. %s ) ) )' % (A4, CA, BNB, TA))
        ln = conslen(w, cl, A4, 'b', 'a')
        pe = w.s([ln], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = ( 2 ^ ( ( # ` a ) + 1 ) ) )' % (A4, CA))
        ep = exp_p1(w, cl, A4, LEN('a'))
        pe2 = w.s([pe, ep], 'eqtrd', '( %s -> ( 2 ^ ( # ` %s ) ) = ( %s x. 2 ) )' % (A4, CA, P))
        # LHS
        f1 = w.s([ca], 'fveq2d', '( %s -> ( toNat ` ( %s ++ K ) ) = ( toNat ` ( <" b "> ++ %s ) ) )' % (A4, CA, AK_))
        Q = '( %s x. %s )' % (P, TK)
        o1 = w.s([ih], 'oveq2d', '( %s -> ( 2 x. ( toNat ` %s ) ) = ( 2 x. ( %s + %s ) ) )' % (A4, AK_, TA, Q))
        o2 = w.s([o1], 'oveq2d', '( %s -> ( %s + ( 2 x. ( toNat ` %s ) ) ) = ( %s + ( 2 x. ( %s + %s ) ) ) )' % (A4, BNB, AK_, BNB, TA, Q))
        lhs = w.s([f1, tc1, o2], '3eqtrd', '( %s -> ( toNat ` ( %s ++ K ) ) = ( %s + ( 2 x. ( %s + %s ) ) ) )' % (A4, CA, BNB, TA, Q))
        # RHS
        pr = w.s([pe2], 'oveq1d', '( %s -> ( ( 2 ^ ( # ` %s ) ) x. %s ) = ( ( %s x. 2 ) x. %s ) )' % (A4, CA, TK, P, TK))
        pc = cl.mem(P, 'CC'); tkc = cl.mem(TK, 'CC'); twoc = w.s([], '2cnd', '( %s -> 2 e. CC )' % A4)
        m32 = w.s([pc, twoc, tkc], 'mul32d', '( %s -> ( ( %s x. 2 ) x. %s ) = ( ( %s x. %s ) x. 2 ) )' % (A4, P, TK, P, TK))
        mc = w.s([cl.mem(Q, 'CC'), twoc], 'mulcomd', '( %s -> ( %s x. 2 ) = ( 2 x. %s ) )' % (A4, Q, Q))
        pr2 = w.s([pr, m32, mc], '3eqtrd', '( %s -> ( ( 2 ^ ( # ` %s ) ) x. %s ) = ( 2 x. %s ) )' % (A4, CA, TK, Q))
        rhs = w.s([tc2, pr2], 'oveq12d', '( %s -> ( ( toNat ` %s ) + ( ( 2 ^ ( # ` %s ) ) x. %s ) ) = ( ( %s + ( 2 x. %s ) ) + ( 2 x. %s ) ) )' % (A4, CA, CA, TK, BNB, TA, Q))
        for E in (BNB, TA, Q):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        idn = lineq(w, A4, '( %s + ( 2 x. ( %s + %s ) ) )' % (BNB, TA, Q), '( ( %s + ( 2 x. %s ) ) + ( 2 x. %s ) )' % (BNB, TA, Q), closure=cl)
        both = w.s([lhs, idn, rhs], '3eqtr4d', '( %s -> ( toNat ` ( %s ++ K ) ) = ( ( toNat ` %s ) + ( ( 2 ^ ( # ` %s ) ) x. %s ) ) )' % (A4, CA, CA, CA, TK))
        w.qed([both], 'ex', '( %s -> %s )' % (A3, PHI(CA))); w.run()

    if want('tonatccat'):
        w = W('tonatccat', 'The value of a concatenation of bit words: the second word counts 2 to the length of the first (Lean: toNat_replicate_false_append generalised).')
        phi = PHI('s')
        st, phit = a4alib.wrdind(w, phi, 'L', 'tonatccatlem1', 'tonatccatlem2', svar='s', alpha='2o', a='a', b='b')
        assert phit == PHI('L'), phit
        w.qed([st], 'imp', '( ( L e. Word 2o /\\ K e. Word 2o ) -> ( toNat ` ( L ++ K ) ) = ( ( toNat ` L ) + ( ( 2 ^ ( # ` L ) ) x. ( toNat ` K ) ) ) )'); w.run()

    A3 = '( L e. Word 2o /\\ M e. NN0 /\\ M <_ ( # ` L ) )'
    def split_setup(w):
        """the common prefix/suffix split of L at M"""
        l = w.s([], 'simp1', '( %s -> L e. Word 2o )' % A3); m = w.s([], 'simp2', '( %s -> M e. NN0 )' % A3); le = w.s([], 'simp3', '( %s -> M <_ ( # ` L ) )' % A3)
        cl = Cl(w, A3, {'L': ('Word 2o', l), 'M': ('NN0', m)})
        H = LEN('L'); Pf = PFX('L', 'M'); Sf = SWRD('L', 'M', H)
        hn = cl.mem(H, 'NN0')
        mfz = w.s([m, hn, le, w.inst('elfz2nn0')], 'syl3anbrc', '( %s -> M e. ( 0 ... %s ) )' % (A3, H))
        hle = w.s([cl.mem(H, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (A3, H, H))
        hfz = w.s([hn, hn, hle, w.inst('elfz2nn0')], 'syl3anbrc', '( %s -> %s e. ( 0 ... %s ) )' % (A3, H, H))
        cp = w.s([l, mfz, hfz, w.inst('ccatpfx')], 'syl3anc', '( %s -> ( %s ++ %s ) = %s )' % (A3, Pf, Sf, PFX('L', H)))
        pid = w.s([l, w.inst('pfxid')], 'syl', '( %s -> %s = L )' % (A3, PFX('L', H)))
        sp = w.s([cp, pid], 'eqtrd', '( %s -> ( %s ++ %s ) = L )' % (A3, Pf, Sf))
        pw = cl.mem(Pf, 'Word 2o'); sw = cl.mem(Sf, 'Word 2o')
        tc = w.s([pw, sw, w.inst('tonatccat')], 'syl2anc', '( %s -> ( toNat ` ( %s ++ %s ) ) = ( ( toNat ` %s ) + ( ( 2 ^ ( # ` %s ) ) x. ( toNat ` %s ) ) ) )' % (A3, Pf, Sf, Pf, Pf, Sf))
        pl = w.s([l, mfz, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = M )' % (A3, Pf))
        TP = TN(Pf); TS = TN(Sf); PM = P2('M')
        o = w.s([pl], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = %s )' % (A3, Pf, PM))
        o2 = w.s([o], 'oveq1d', '( %s -> ( ( 2 ^ ( # ` %s ) ) x. %s ) = ( %s x. %s ) )' % (A3, Pf, TS, PM, TS))
        o3 = w.s([o2], 'oveq2d', '( %s -> ( %s + ( ( 2 ^ ( # ` %s ) ) x. %s ) ) = ( %s + ( %s x. %s ) ) )' % (A3, TP, Pf, TS, TP, PM, TS))
        f = w.s([sp], 'fveq2d', '( %s -> ( toNat ` ( %s ++ %s ) ) = ( toNat ` L ) )' % (A3, Pf, Sf))
        val = w.s([f, tc, o3], '3eqtr3d', '( %s -> ( toNat ` L ) = ( %s + ( %s x. %s ) ) )' % (A3, TP, PM, TS))
        # TP < 2 ^ M
        lt = w.s([pw, w.inst('tonatlt')], 'syl', '( %s -> %s < ( 2 ^ ( # ` %s ) ) )' % (A3, TP, Pf))
        lt2 = w.s([lt, o], 'breqtrd', '( %s -> %s < %s )' % (A3, TP, PM))
        return cl, l, m, Pf, Sf, TP, TS, PM, val, lt2

    if want('tonatpfx'):
        w = W('tonatpfx', 'The value of a prefix of a bit word is the value modulo 2 to the prefix length.')
        cl, l, m, Pf, Sf, TP, TS, PM, val, lt2 = split_setup(w)
        T = TN('L')
        mc = w.s([cl.mem(PM, 'CC'), cl.mem(TS, 'CC')], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A3, PM, TS, TS, PM))
        v2 = w.s([mc], 'oveq2d', '( %s -> ( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) ) )' % (A3, TP, PM, TS, TP, TS, PM))
        v3 = w.s([val, v2], 'eqtrd', '( %s -> %s = ( %s + ( %s x. %s ) ) )' % (A3, T, TP, TS, PM))
        o = w.s([v3], 'oveq1d', '( %s -> ( %s mod %s ) = ( ( %s + ( %s x. %s ) ) mod %s ) )' % (A3, T, PM, TP, TS, PM, PM))
        cy = w.s([cl.mem(TP, 'RR'), cl.mem(PM, 'RR+'), cl.mem(TS, 'ZZ'), w.inst('modcyc')], 'syl3anc', '( %s -> ( ( %s + ( %s x. %s ) ) mod %s ) = ( %s mod %s ) )' % (A3, TP, TS, PM, PM, TP, PM))
        j1 = w.s([cl.mem(TP, 'RR'), cl.mem(PM, 'RR+')], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (A3, TP, PM))
        j2 = w.s([cl.ge0(TP), lt2], 'jca', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (A3, TP, TP, PM))
        mi = w.s([j1, j2, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (A3, TP, PM, TP))
        ch = w.s([o, cy, mi], '3eqtrd', '( %s -> ( %s mod %s ) = %s )' % (A3, T, PM, TP))
        w.qed([ch], 'eqcomd', '( %s -> ( toNat ` %s ) = ( %s mod %s ) )' % (A3, Pf, T, PM)); w.run()

    if want('tonatswrd'):
        w = W('tonatswrd', 'The value of a suffix of a bit word is the value divided by 2 to the start position, rounded down.')
        cl, l, m, Pf, Sf, TP, TS, PM, val, lt2 = split_setup(w)
        T = TN('L')
        o = w.s([val], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s + ( %s x. %s ) ) / %s ) )' % (A3, T, PM, TP, PM, TS, PM))
        pc = cl.mem(PM, 'CC'); pne = cl.ne0(PM); tpc = cl.mem(TP, 'CC'); tsc = cl.mem(TS, 'CC'); prc = cl.mem('( %s x. %s )' % (PM, TS), 'CC')
        dd = w.s([tpc, prc, pc, pne], 'divdird', '( %s -> ( ( %s + ( %s x. %s ) ) / %s ) = ( ( %s / %s ) + ( ( %s x. %s ) / %s ) ) )' % (A3, TP, PM, TS, PM, TP, PM, PM, TS, PM))
        dc = w.s([tsc, pc, pne], 'divcan3d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (A3, PM, TS, PM, TS))
        o2 = w.s([dc], 'oveq2d', '( %s -> ( ( %s / %s ) + ( ( %s x. %s ) / %s ) ) = ( ( %s / %s ) + %s ) )' % (A3, TP, PM, PM, TS, PM, TP, PM, TS))
        ac = w.s([cl.mem('( %s / %s )' % (TP, PM), 'CC'), tsc], 'addcomd', '( %s -> ( ( %s / %s ) + %s ) = ( %s + ( %s / %s ) ) )' % (A3, TP, PM, TS, TS, TP, PM))
        ch = w.s([o, dd, o2, ac], '4eqtrd' if False else '3eqtrd', '( %s -> ( %s / %s ) = ( ( %s / %s ) + %s ) )' % (A3, T, PM, TP, PM, TS)) if False else None
        c1 = w.s([o, dd], 'eqtrd', '( %s -> ( %s / %s ) = ( ( %s / %s ) + ( ( %s x. %s ) / %s ) ) )' % (A3, T, PM, TP, PM, PM, TS, PM))
        c2 = w.s([c1, o2, ac], '3eqtrd', '( %s -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (A3, T, PM, TS, TP, PM))
        f = w.s([c2], 'fveq2d', '( %s -> ( |_ ` ( %s / %s ) ) = ( |_ ` ( %s + ( %s / %s ) ) ) )' % (A3, T, PM, TS, TP, PM))
        ad = w.s([cl.mem(TS, 'ZZ'), cl.mem(TP, 'NN0'), cl.mem(PM, 'NN'), w.inst('adddivflid')], 'syl3anc', '( %s -> ( %s < %s <-> ( |_ ` ( %s + ( %s / %s ) ) ) = %s ) )' % (A3, TP, PM, TS, TP, PM, TS))
        fl = w.s([lt2, ad], 'mpbid', '( %s -> ( |_ ` ( %s + ( %s / %s ) ) ) = %s )' % (A3, TS, TP, PM, TS))
        ch = w.s([f, fl], 'eqtrd', '( %s -> ( |_ ` ( %s / %s ) ) = %s )' % (A3, T, PM, TS))
        w.qed([ch], 'eqcomd', '( %s -> ( toNat ` %s ) = ( |_ ` ( %s / %s ) ) )' % (A3, Sf, T, PM)); w.run()

    A2 = '( L e. Word 2o /\\ N e. NN0 )'
    if want('tonatrep0c'):
        w = W('tonatrep0c', 'Zero letters appended do not change the value of a bit word (Lean: toNat_append_replicate_false).')
        l = w.s([], 'simpl', '( %s -> L e. Word 2o )' % A2); n = w.s([], 'simpr', '( %s -> N e. NN0 )' % A2)
        cl = Cl(w, A2, {'L': ('Word 2o', l), 'N': ('NN0', n)})
        R = REP0('N'); T = TN('L'); P = P2(LEN('L'))
        tc = w.s([l, cl.mem(R, 'Word 2o'), w.inst('tonatccat')], 'syl2anc', '( %s -> ( toNat ` ( L ++ %s ) ) = ( %s + ( %s x. ( toNat ` %s ) ) ) )' % (A2, R, T, P, R))
        t0 = w.s([n, w.inst('tonatrep0')], 'syl', '( %s -> ( toNat ` %s ) = 0 )' % (A2, R))
        o = w.s([t0], 'oveq2d', '( %s -> ( %s x. ( toNat ` %s ) ) = ( %s x. 0 ) )' % (A2, P, R, P))
        m0 = w.s([cl.mem(P, 'CC')], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (A2, P))
        o2 = w.s([o, m0], 'eqtrd', '( %s -> ( %s x. ( toNat ` %s ) ) = 0 )' % (A2, P, R))
        o3 = w.s([o2], 'oveq2d', '( %s -> ( %s + ( %s x. ( toNat ` %s ) ) ) = ( %s + 0 ) )' % (A2, T, P, R, T))
        a0 = w.s([cl.mem(T, 'CC')], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A2, T, T))
        w.qed([tc, o3, a0], '3eqtrd', '( %s -> ( toNat ` ( L ++ %s ) ) = %s )' % (A2, R, T)); w.run()

    if want('tonatrep0a'):
        w = W('tonatrep0a', 'Zero letters prepended multiply the value of a bit word by 2 to their number (Lean: toNat_replicate_false_append).')
        l = w.s([], 'simpl', '( %s -> L e. Word 2o )' % A2); n = w.s([], 'simpr', '( %s -> N e. NN0 )' % A2)
        cl = Cl(w, A2, {'L': ('Word 2o', l), 'N': ('NN0', n)})
        R = REP0('N'); T = TN('L'); PN = P2('N')
        tc = w.s([cl.mem(R, 'Word 2o'), l, w.inst('tonatccat')], 'syl2anc', '( %s -> ( toNat ` ( %s ++ L ) ) = ( ( toNat ` %s ) + ( ( 2 ^ ( # ` %s ) ) x. %s ) ) )' % (A2, R, R, R, T))
        t0 = w.s([n, w.inst('tonatrep0')], 'syl', '( %s -> ( toNat ` %s ) = 0 )' % (A2, R))
        rl = w.s([cl.mem('(/)', '_V'), n, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` %s ) = N )' % (A2, R))
        o = w.s([rl], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = %s )' % (A2, R, PN))
        o2 = w.s([o], 'oveq1d', '( %s -> ( ( 2 ^ ( # ` %s ) ) x. %s ) = ( %s x. %s ) )' % (A2, R, T, PN, T))
        o3 = w.s([t0, o2], 'oveq12d', '( %s -> ( ( toNat ` %s ) + ( ( 2 ^ ( # ` %s ) ) x. %s ) ) = ( 0 + ( %s x. %s ) ) )' % (A2, R, R, T, PN, T))
        a0 = w.s([cl.mem('( %s x. %s )' % (PN, T), 'CC')], 'addlidd', '( %s -> ( 0 + ( %s x. %s ) ) = ( %s x. %s ) )' % (A2, PN, T, PN, T))
        w.qed([tc, o3, a0], '3eqtrd', '( %s -> ( toNat ` ( %s ++ L ) ) = ( %s x. %s ) )' % (A2, R, PN, T)); w.run()

    if want('bwrep1'):
        w = W('bwrep1', 'The word of E true letters is the digits word of -1 (m1bits).')
        e = w.s([], 'id', '( %s -> E e. NN0 )' % AE)
        cl = Cl(w, AE, {'E': ('NN0', e)})
        R = BWRD('-u 1', 'E')
        m1z = w.s([num.closed(w, [], 'neg1z', '-u 1 e. ZZ')], 'a1i', '( %s -> -u 1 e. ZZ )' % AE)
        cl.have('-u 1', 'ZZ', m1z)
        rw = w.s([m1z, e, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (AE, R))
        rl = w.s([m1z, e, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = E )' % (AE, R))
        a2 = '( %s /\\ i e. ( 0 ..^ E ) )' % AE
        ist = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ E ) )' % a2)
        fv = w.s([lift(w, m1z, a2), lift(w, e, a2), ist, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, R, BIT('-u 1', 'i')))
        inn = w.s([ist, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % a2)
        mb = num.closed(w, [], 'm1bits', '( bits ` -u 1 ) = NN0')
        mbd = w.s([mb], 'a1i', '( %s -> ( bits ` -u 1 ) = NN0 )' % a2)
        el = w.s([inn, mbd], 'eleqtrrd', '( %s -> i e. ( bits ` -u 1 ) )' % a2)
        it = w.s([el], 'iftrued', '( %s -> %s = 1o )' % (a2, BIT('-u 1', 'i')))
        lt = w.s([fv, it], 'eqtrd', '( %s -> ( %s ` i ) = 1o )' % (a2, R))
        al = w.s([lt], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ E ) ( %s ` i ) = 1o )' % (AE, R))
        j = w.s([rw, rl, al], '3jca', '( %s -> ( %s e. Word 2o /\\ ( # ` %s ) = E /\\ A. i e. ( 0 ..^ E ) ( %s ` i ) = 1o ) )' % (AE, R, R, R))
        one = w.s([num.closed(w, [], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % AE)
        df = w.s([one, e, w.inst('repsdf2')], 'syl2anc', '( %s -> ( %s = %s <-> ( %s e. Word 2o /\\ ( # ` %s ) = E /\\ A. i e. ( 0 ..^ E ) ( %s ` i ) = 1o ) ) )' % (AE, R, REP1('E'), R, R, R))
        eq = w.s([j, df], 'mpbird', '( %s -> %s = %s )' % (AE, R, REP1('E')))
        w.qed([eq], 'eqcomd', '( %s -> %s = %s )' % (AE, REP1('E'), R)); w.run()

    if want('tonatrep1'):
        w = W('tonatrep1', 'The value of a word of E true letters is 2 ^ E - 1.')
        e = w.s([], 'id', '( %s -> E e. NN0 )' % AE)
        cl = Cl(w, AE, {'E': ('NN0', e)})
        R = BWRD('-u 1', 'E'); PE = P2('E')
        r = w.s([], 'bwrep1', '( %s -> %s = %s )' % (AE, REP1('E'), R))
        f = w.s([r], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AE, REP1('E'), R))
        m1z = w.s([num.closed(w, [], 'neg1z', '-u 1 e. ZZ')], 'a1i', '( %s -> -u 1 e. ZZ )' % AE)
        t = w.s([m1z, e, w.inst('tonatbwrd')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( -u 1 mod %s ) )' % (AE, R, PE))
        m = w.s([cl.mem(PE, 'NN'), w.inst('m1modnnsub1')], 'syl', '( %s -> ( -u 1 mod %s ) = ( %s - 1 ) )' % (AE, PE, PE))
        w.qed([f, t, m], '3eqtrd', '( %s -> ( toNat ` %s ) = ( %s - 1 ) )' % (AE, REP1('E'), PE)); w.run()

    if want('bwoddne'):
        A = '( A e. ZZ /\\ B e. ZZ )'
        w = W('bwoddne', 'An odd integer is not an even one.')
        a = w.s([], 'simpl', '( %s -> A e. ZZ )' % A); b = w.s([], 'simpr', '( %s -> B e. ZZ )' % A)
        OD = '( ( 2 x. A ) + 1 )'; EV = '( 2 x. B )'
        eq = w.s([], 'eqidd', '( %s -> %s = %s )' % (A, OD, OD))
        od = w.s([a, eq, w.inst('2tp1odd')], 'syl2anc', '( %s -> -. 2 || %s )' % (A, OD))
        tz = w.s([num.closed(w, [], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A)
        ev = w.s([tz, b, w.inst('dvdsmul1')], 'syl2anc', '( %s -> 2 || %s )' % (A, EV))
        e1 = w.s([], 'breq2', '( %s = %s -> ( 2 || %s <-> 2 || %s ) )' % (OD, EV, OD, EV))
        r = w.s([ev, e1], 'syl5ibrcom', '( %s -> ( %s = %s -> 2 || %s ) )' % (A, OD, EV, OD))
        w.qed([od, r], 'mtod', '( %s -> -. %s = %s )' % (A, OD, EV)); w.run()

    if want('blp2'):
        w = W('blp2', 'The bit length of 2 ^ E is E + 1.')
        e = w.s([], 'id', '( %s -> E e. NN0 )' % AE)
        cl = Cl(w, AE, {'E': ('NN0', e)})
        P = P2('E')
        pn = cl.mem(P, 'NN'); e1n = cl.mem('( E + 1 )', 'NN')
        pc = w.s([cl.mem('E', 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % AE)], 'pncand', '( %s -> ( ( E + 1 ) - 1 ) = E )' % AE)
        o = w.s([pc], 'oveq2d', '( %s -> ( 2 ^ ( ( E + 1 ) - 1 ) ) = %s )' % (AE, P))
        li = w.s([cl.mem(P, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (AE, P, P))
        h1 = w.s([o, li], 'eqbrtrd', '( %s -> ( 2 ^ ( ( E + 1 ) - 1 ) ) <_ %s )' % (AE, P))
        ltE = w.s([cl.mem('E', 'RR')], 'ltp1d', '( %s -> E < ( E + 1 ) )' % AE)
        le2 = ltexp2(w, AE, cl, 'E', '( E + 1 )')
        h2 = w.s([ltE, le2], 'mpbid', '( %s -> %s < ( 2 ^ ( E + 1 ) ) )' % (AE, P))
        j1 = w.s([pn, e1n], 'jca', '( %s -> ( %s e. NN /\\ ( E + 1 ) e. NN ) )' % (AE, P))
        j2 = w.s([h1, h2], 'jca', '( %s -> ( ( 2 ^ ( ( E + 1 ) - 1 ) ) <_ %s /\\ %s < ( 2 ^ ( E + 1 ) ) ) )' % (AE, P, P))
        w.qed([j1, j2, w.inst('blchar')], 'syl2anc', '( %s -> ( bl ` %s ) = ( E + 1 ) )' % (AE, P)); w.run()
