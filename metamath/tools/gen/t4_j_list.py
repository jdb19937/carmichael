"""Sortie T4, group J: addBits, subBits, subBorrow, subTrunc, cmpBits (T4-blueprint 3.6): values, closures, lengths, the toNat identities, the fold forms, the empty clauses."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AXY = '( X e. Word 2o /\\ Y e. Word 2o /\\ C e. 2o )'
AXY3 = '( X e. Word 2o /\\ Y e. Word 2o /\\ C e. 3o )'
A = TN('X'); B = TN('Y'); NX = LEN('X'); NY = LEN('Y')
MX = MAX('X', 'Y')
S = SUM('X', 'Y', 'C'); D = DIF('X', 'Y', 'C'); BNC = '( bToNat ` C )'
PN = '( 2 ^ %s )' % MX
K = 'if ( %s <_ %s , 1o , (/) )' % (PN, S)
ADDV = '( %s ++ ( addCarry ` %s ) )' % (BWRD(S, MX), K)
SUBV = BWRD(D, MX)
BORV = 'if ( %s < ( %s + %s ) , 1o , (/) )' % (A, B, BNC)
TRV = 'if ( ( ( X subBorrow Y ) ` C ) = 1o , (/) , ( ( X subBits Y ) ` C ) )'
CMPV = 'if ( %s = %s , C , ( %s Ncmp %s ) )' % (A, B, A, B)
ADD = '( ( X addBits Y ) ` C )'; SUB = '( ( X subBits Y ) ` C )'; BOR = '( ( X subBorrow Y ) ` C )'; TR = '( ( X subTrunc Y ) ` C )'; CMP = '( ( X cmpBits Y ) ` C )'


def base(w, ante=AXY, kc='2o'):
    return Cl(w, ante, conj_leaves(w, ante, [('X', 'Word 2o'), ('Y', 'Word 2o'), ('C', kc)]))


def maxfacts(w, cl, ante):
    """( # X ) <_ MX, ( # Y ) <_ MX, MX e. NN0, A < 2^MX, B < 2^MX (steps)"""
    ml = w.s([cl.mem(NX, 'RR'), cl.mem(NY, 'RR'), w.inst('bwmaxle')], 'syl2anc', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ante, NX, MX, NY, MX))
    lx = w.s([ml], 'simpld', '( %s -> %s <_ %s )' % (ante, NX, MX)); ly = w.s([ml], 'simprd', '( %s -> %s <_ %s )' % (ante, NY, MX))
    mn = cl.mem(MX, 'NN0')
    ltx = w.s([cl.mem('X', 'Word 2o'), mn, lx, w.inst('tonatltpow')], 'syl3anc', '( %s -> %s < %s )' % (ante, A, PN))
    lty = w.s([cl.mem('Y', 'Word 2o'), mn, ly, w.inst('tonatltpow')], 'syl3anc', '( %s -> %s < %s )' % (ante, B, PN))
    return lx, ly, mn, ltx, lty


if __name__ == '__main__':
    # ---- helpers on max
    if want('bwmaxle'):
        A2 = '( M e. RR /\\ N e. RR )'
        w = W('bwmaxle', 'Both arguments are at most the larger one, written as an if.')
        m = w.s([], 'simpl', '( %s -> M e. RR )' % A2); n = w.s([], 'simpr', '( %s -> N e. RR )' % A2)
        MX2 = 'if ( M <_ N , N , M )'
        a1 = '( %s /\\ M <_ N )' % A2; h1 = w.s([], 'simpr', '( %s -> M <_ N )' % a1)
        i1 = w.s([h1], 'iftrued', '( %s -> %s = N )' % (a1, MX2)); n1 = w.s([n], 'adantr', '( %s -> N e. RR )' % a1)
        li = w.s([n1], 'leidd', '( %s -> N <_ N )' % a1)
        c1a = w.s([h1, i1], 'breqtrrd', '( %s -> M <_ %s )' % (a1, MX2)); c1b = w.s([li, i1], 'breqtrrd', '( %s -> N <_ %s )' % (a1, MX2))
        c1 = w.s([c1a, c1b], 'jca', '( %s -> ( M <_ %s /\\ N <_ %s ) )' % (a1, MX2, MX2))
        a2 = '( %s /\\ -. M <_ N )' % A2; h2 = w.s([], 'simpr', '( %s -> -. M <_ N )' % a2)
        i2 = w.s([h2], 'iffalsed', '( %s -> %s = M )' % (a2, MX2)); m2 = w.s([m], 'adantr', '( %s -> M e. RR )' % a2); n2 = w.s([n], 'adantr', '( %s -> N e. RR )' % a2)
        lt = w.s([n2, m2, w.inst('ltnle')], 'syl2anc', '( %s -> ( N < M <-> -. M <_ N ) )' % a2); lt2 = w.s([h2, lt], 'mpbird', '( %s -> N < M )' % a2)
        le2 = w.s([n2, m2, lt2], 'ltled', '( %s -> N <_ M )' % a2); li2 = w.s([m2], 'leidd', '( %s -> M <_ M )' % a2)
        c2a = w.s([li2, i2], 'breqtrrd', '( %s -> M <_ %s )' % (a2, MX2)); c2b = w.s([le2, i2], 'breqtrrd', '( %s -> N <_ %s )' % (a2, MX2))
        c2 = w.s([c2a, c2b], 'jca', '( %s -> ( M <_ %s /\\ N <_ %s ) )' % (a2, MX2, MX2))
        w.qed([c1, c2], 'pm2.61dan', '( %s -> ( M <_ %s /\\ N <_ %s ) )' % (A2, MX2, MX2)); w.run()
    if want('tonatltpow'):
        A3 = '( X e. Word 2o /\\ N e. NN0 /\\ ( # ` X ) <_ N )'
        w = W('tonatltpow', 'The value of a bit word is below 2 to any bound on its length.')
        x = w.s([], 'simp1', '( %s -> X e. Word 2o )' % A3); n = w.s([], 'simp2', '( %s -> N e. NN0 )' % A3); le = w.s([], 'simp3', '( %s -> ( # ` X ) <_ N )' % A3)
        cl = Cl(w, A3, {'X': ('Word 2o', x), 'N': ('NN0', n)})
        lt = w.s([x, w.inst('tonatlt')], 'syl', '( %s -> %s < ( 2 ^ %s ) )' % (A3, A, NX))
        lz = cl.mem(NX, 'ZZ'); nz = cl.mem('N', 'ZZ')
        j = w.s([lz, nz, le], '3jca', '( %s -> ( ( # ` X ) e. ZZ /\\ N e. ZZ /\\ ( # ` X ) <_ N ) )' % A3)
        uz = w.s([j, w.inst('eluz2')], 'sylibr', '( %s -> N e. ( ZZ>= ` ( # ` X ) ) )' % A3)
        r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A3); l2 = w.s([w.s([], '1le2', '1 <_ 2')], 'a1i', '( %s -> 1 <_ 2 )' % A3)
        le2 = w.s([r2, l2, uz, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ %s ) <_ ( 2 ^ N ) )' % (A3, NX))
        w.qed([cl.mem(A, 'RR'), cl.mem('( 2 ^ %s )' % NX, 'RR'), cl.mem('( 2 ^ N )', 'RR'), lt, le2], 'ltletrd', '( %s -> %s < ( 2 ^ N ) )' % (A3, A)); w.run()

    # ---- addBits
    if want('addbitsval'):
        w = W('addbitsval', 'Value of addBits: the max-length low digits of the sum, followed by the carry out of them (Lean: addBits, by its clauses addbitsnil, addbitscons).')
        cl = base(w)
        st, val = defval(w, cl, 'df-addbits', 'addBits', ['X', 'Y', 'C']); assert val == ADDV, val
        promote(w, st); w.run()
    if want('addbitscl'):
        w = W('addbitscl', 'Closure of addBits: a bit word.')
        cl = base(w); v = w.s([], 'addbitsval', '( %s -> %s = %s )' % (AXY, ADD, ADDV)); m = cl.mem(ADDV, 'Word 2o')
        w.qed([v, m], 'eqeltrd', '( %s -> %s e. Word 2o )' % (AXY, ADD)); w.run()
    if want('addbitslen'):
        w = W('addbitslen', 'The sum has at most one more digit than the longer summand (Lean: addBits_length).')
        cl = base(w); v = w.s([], 'addbitsval', '( %s -> %s = %s )' % (AXY, ADD, ADDV))
        h = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AXY, ADD, ADDV))
        cc = w.s([cl.mem(BWRD(S, MX), 'Word 2o'), cl.mem('( addCarry ` %s )' % K, 'Word 2o'), w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` ( addCarry ` %s ) ) ) )' % (AXY, ADDV, BWRD(S, MX), K))
        lb = w.s([cl.mem(S, 'ZZ'), cl.mem(MX, 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AXY, BWRD(S, MX), MX))
        la = w.s([cl.mem(K, '2o'), w.inst('addcarrylen')], 'syl', '( %s -> ( # ` ( addCarry ` %s ) ) = ( bToNat ` %s ) )' % (AXY, K, K))
        o = w.s([lb, la], 'oveq12d', '( %s -> ( ( # ` %s ) + ( # ` ( addCarry ` %s ) ) ) = ( %s + ( bToNat ` %s ) ) )' % (AXY, BWRD(S, MX), K, MX, K))
        e = w.s([h, cc, o], '3eqtrd', '( %s -> ( # ` %s ) = ( %s + ( bToNat ` %s ) ) )' % (AXY, ADD, MX, K))
        le1 = w.s([cl.mem(K, '2o'), w.inst('bwbnle1')], 'syl', '( %s -> ( bToNat ` %s ) <_ 1 )' % (AXY, K))
        ad = w.s([cl.mem('( bToNat ` %s )' % K, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % AXY), cl.mem(MX, 'RR'), le1], 'leadd2dd', '( %s -> ( %s + ( bToNat ` %s ) ) <_ ( %s + 1 ) )' % (AXY, MX, K, MX))
        w.qed([e, ad], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( %s + 1 ) )' % (AXY, ADD, MX)); w.run()
    if want('addbitslt'):
        w = W('addbitslt', 'Lemma for addBits: the sum is below 2 ^ ( max + 1 ).')
        cl = base(w)
        lx, ly, mn, ltx, lty = maxfacts(w, cl, AXY)
        cl.atom(PN); cl.leaf(PN, 'RR', cl.mem(PN, 'RR')); cl.leaf('( 2 ^ ( %s + 1 ) )' % MX, 'RR', cl.mem('( 2 ^ ( %s + 1 ) )' % MX, 'RR'))
        for E in (A, B, BNC):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        pz = cl.mem(PN, 'ZZ')
        zx = w.s([cl.mem(A, 'ZZ'), pz, w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (AXY, A, PN, A, PN)); lex = w.s([ltx, zx], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (AXY, A, PN))
        zy = w.s([cl.mem(B, 'ZZ'), pz, w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (AXY, B, PN, B, PN)); ley = w.s([lty, zy], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (AXY, B, PN))
        le1 = w.s([cl.mem('C', '2o'), w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AXY, BNC))
        ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % AXY), mn, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( %s x. 2 ) )' % (AXY, MX, PN))
        linarith(w, AXY, [lex, ley, le1, ep], '%s < ( 2 ^ ( %s + 1 ) )' % (S, MX), closure=cl, name='qed'); w.run()
    if want('tonataddbits'):
        w = W('tonataddbits', 'The value of the sum word is the sum of the values plus the carry-in (Lean: toNat_addBits).')
        cl = base(w)
        v = w.s([], 'addbitsval', '( %s -> %s = %s )' % (AXY, ADD, ADDV))
        tv = w.s([v], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AXY, ADD, ADDV))
        mn = cl.mem(MX, 'NN0'); sz = cl.mem(S, 'ZZ'); sn = cl.mem(S, 'NN0')
        tb = w.s([sz, mn, w.inst('tonatbwrd')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( %s mod %s ) )' % (AXY, BWRD(S, MX), S, PN))
        lt2 = w.s([], 'addbitslt', '( %s -> %s < ( 2 ^ ( %s + 1 ) ) )' % (AXY, S, MX))
        ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % AXY), mn, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( %s x. 2 ) )' % (AXY, MX, PN))
        com = w.s([cl.mem(PN, 'CC'), w.s([], '2cnd', '( %s -> 2 e. CC )' % AXY)], 'mulcomd', '( %s -> ( %s x. 2 ) = ( 2 x. %s ) )' % (AXY, PN, PN))
        lt3 = w.s([lt2, ep], 'breqtrd', '( %s -> %s < ( %s x. 2 ) )' % (AXY, S, PN)); lt4 = w.s([lt3, com], 'breqtrd', '( %s -> %s < ( 2 x. %s ) )' % (AXY, S, PN))
        clB = cl.mem(BWRD(S, MX), 'Word 2o')
        cond = '%s <_ %s' % (PN, S)
        # case carry
        a1 = '( %s /\\ %s )' % (AXY, cond); h1 = w.s([], 'simpr', '( %s -> %s )' % (a1, cond))
        it = w.s([h1], 'iftrued', '( %s -> %s = 1o )' % (a1, K)); f = w.s([it], 'fveq2d', '( %s -> ( addCarry ` %s ) = ( addCarry ` 1o ) )' % (a1, K))
        c1 = w.s([], 'addcarry1', '( addCarry ` 1o ) = <" 1o ">'); f2 = w.s([f, c1], 'eqtrdi', '( %s -> ( addCarry ` %s ) = <" 1o "> )' % (a1, K))
        o = w.s([f2], 'oveq2d', '( %s -> %s = ( %s ++ <" 1o "> ) )' % (a1, ADDV, BWRD(S, MX)))
        one = w.s([], '1oel2o', '1o e. 2o'); oned = w.s([one], 'a1i', '( %s -> 1o e. 2o )' % a1)
        ts = w.s([lift(w, clB, a1), oned, w.inst('tonatsnoc')], 'syl2anc', '( %s -> ( toNat ` ( %s ++ <" 1o "> ) ) = ( ( toNat ` %s ) + ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` %s ) ) ) ) )' % (a1, BWRD(S, MX), BWRD(S, MX), BWRD(S, MX)))
        lb = w.s([lift(w, sz, a1), lift(w, mn, a1), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (a1, BWRD(S, MX), MX))
        pe = w.s([lb], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = %s )' % (a1, BWRD(S, MX), PN))
        b1 = w.s([w.s([], 'bwbn1', '( bToNat ` 1o ) = 1')], 'a1i', '( %s -> ( bToNat ` 1o ) = 1 )' % a1)
        mm = w.s([b1, pe], 'oveq12d', '( %s -> ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` %s ) ) ) = ( 1 x. %s ) )' % (a1, BWRD(S, MX), PN)); m1 = w.s([lift(w, cl.mem(PN, 'CC'), a1)], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (a1, PN, PN))
        mm2 = w.s([mm, m1], 'eqtrd', '( %s -> ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` %s ) ) ) = %s )' % (a1, BWRD(S, MX), PN))
        j = w.s([lift(w, cl.mem(S, 'RR'), a1), lift(w, cl.mem(PN, 'RR+'), a1)], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (a1, S, PN)); j2 = w.s([h1, lift(w, lt4, a1)], 'jca', '( %s -> ( %s <_ %s /\\ %s < ( 2 x. %s ) ) )' % (a1, PN, S, S, PN))
        sm = w.s([j, j2, w.inst('2submod')], 'syl2anc', '( %s -> ( %s mod %s ) = ( %s - %s ) )' % (a1, S, PN, S, PN))
        tb1 = w.s([lift(w, tb, a1), sm], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s - %s ) )' % (a1, BWRD(S, MX), S, PN))
        ad = w.s([tb1, mm2], 'oveq12d', '( %s -> ( ( toNat ` %s ) + ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` %s ) ) ) ) = ( ( %s - %s ) + %s ) )' % (a1, BWRD(S, MX), BWRD(S, MX), S, PN, PN))
        np = w.s([lift(w, cl.mem(S, 'CC'), a1), lift(w, cl.mem(PN, 'CC'), a1)], 'npcand', '( %s -> ( ( %s - %s ) + %s ) = %s )' % (a1, S, PN, PN, S))
        t1 = w.s([o], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` ( %s ++ <" 1o "> ) ) )' % (a1, ADDV, BWRD(S, MX)))
        r1 = w.s([t1, ts, ad, np], '4eqtrd' if False else 'eqtrd', '') if False else None
        r1a = w.s([t1, ts], 'eqtrd', '( %s -> ( toNat ` %s ) = ( ( toNat ` %s ) + ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` %s ) ) ) ) )' % (a1, ADDV, BWRD(S, MX), BWRD(S, MX)))
        r1b = w.s([r1a, ad, np], '3eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (a1, ADDV, S))
        # case no carry
        a2 = '( %s /\\ -. %s )' % (AXY, cond); h2 = w.s([], 'simpr', '( %s -> -. %s )' % (a2, cond))
        it2 = w.s([h2], 'iffalsed', '( %s -> %s = (/) )' % (a2, K)); f = w.s([it2], 'fveq2d', '( %s -> ( addCarry ` %s ) = ( addCarry ` (/) ) )' % (a2, K))
        c0 = w.s([], 'addcarry0', '( addCarry ` (/) ) = (/)'); f2 = w.s([f, c0], 'eqtrdi', '( %s -> ( addCarry ` %s ) = (/) )' % (a2, K))
        o = w.s([f2], 'oveq2d', '( %s -> %s = ( %s ++ (/) ) )' % (a2, ADDV, BWRD(S, MX)))
        cr = w.s([lift(w, clB, a2), w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (a2, BWRD(S, MX), BWRD(S, MX)))
        o2 = w.s([o, cr], 'eqtrd', '( %s -> %s = %s )' % (a2, ADDV, BWRD(S, MX)))
        t2 = w.s([o2], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (a2, ADDV, BWRD(S, MX)))
        ln = w.s([lift(w, cl.mem(S, 'RR'), a2), lift(w, cl.mem(PN, 'RR'), a2), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s ) )' % (a2, S, PN, cond)); lt = w.s([h2, ln], 'mpbird', '( %s -> %s < %s )' % (a2, S, PN))
        tb2 = w.s([lift(w, sn, a2), lift(w, mn, a2), lt, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (a2, BWRD(S, MX), S))
        r2 = w.s([t2, tb2], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (a2, ADDV, S))
        r = w.s([r1b, r2], 'pm2.61dan', '( %s -> ( toNat ` %s ) = %s )' % (AXY, ADDV, S))
        w.qed([tv, r], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (AXY, ADD, S)); w.run()
    if want('addbitsfold'):
        w = W('addbitsfold', 'The carry out of the sum word is the majBit fold at the max length: the form the loop assembly instantiates.')
        cl = base(w)
        lx, ly, mn, ltx, lty = maxfacts(w, cl, AXY)
        v = w.s([], 'addbitsval', '( %s -> %s = %s )' % (AXY, ADD, ADDV))
        az = cl.mem(A, 'ZZ'); bz = cl.mem(B, 'ZZ'); c2 = cl.mem('C', '2o')
        j = w.s([az, bz, c2], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ C e. 2o ) )' % (AXY, A, B))
        F = FOLD('majBit', A, B, 'C', MX)
        KI = 'if ( %s <_ ( ( ( %s mod %s ) + ( %s mod %s ) ) + %s ) , 1o , (/) )' % (PN, A, PN, B, PN, BNC)
        cf = w.s([j, mn, w.inst('bwcarry')], 'syl2anc', '( %s -> %s = %s )' % (AXY, F, KI))
        pn = cl.mem(PN, 'NN')
        mx = w.s([az, pn, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( ( %s mod %s ) = %s <-> %s e. ( 0 ..^ %s ) ) )' % (AXY, A, PN, A, A, PN))
        ex = w.s([cl.mem(A, 'NN0'), cl.mem(PN, 'ZZ'), ltx, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (AXY, A, PN)); mx2 = w.s([ex, mx], 'mpbird', '( %s -> ( %s mod %s ) = %s )' % (AXY, A, PN, A))
        my = w.s([bz, pn, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( ( %s mod %s ) = %s <-> %s e. ( 0 ..^ %s ) ) )' % (AXY, B, PN, B, B, PN))
        ey = w.s([cl.mem(B, 'NN0'), cl.mem(PN, 'ZZ'), lty, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (AXY, B, PN)); my2 = w.s([ey, my], 'mpbird', '( %s -> ( %s mod %s ) = %s )' % (AXY, B, PN, B))
        o = w.s([mx2, my2], 'oveq12d', '( %s -> ( ( %s mod %s ) + ( %s mod %s ) ) = ( %s + %s ) )' % (AXY, A, PN, B, PN, A, B))
        o2 = w.s([o], 'oveq1d', '( %s -> ( ( ( %s mod %s ) + ( %s mod %s ) ) + %s ) = %s )' % (AXY, A, PN, B, PN, BNC, S))
        br = w.s([o2], 'breq2d', '( %s -> ( %s <_ ( ( ( %s mod %s ) + ( %s mod %s ) ) + %s ) <-> %s <_ %s ) )' % (AXY, PN, A, PN, B, PN, BNC, PN, S))
        ib = w.s([br], 'ifbid', '( %s -> %s = %s )' % (AXY, KI, K))
        cf2 = w.s([cf, ib], 'eqtrd', '( %s -> %s = %s )' % (AXY, F, K))
        fa = w.s([cf2], 'fveq2d', '( %s -> ( addCarry ` %s ) = ( addCarry ` %s ) )' % (AXY, F, K))
        oc = w.s([fa], 'oveq2d', '( %s -> ( %s ++ ( addCarry ` %s ) ) = %s )' % (AXY, BWRD(S, MX), F, ADDV))
        w.qed([v, oc], 'eqtr4d', '( %s -> %s = ( %s ++ ( addCarry ` %s ) ) )' % (AXY, ADD, BWRD(S, MX), F)); w.run()

    # ---- subBits, subBorrow, subTrunc
    for lab, dlab, const, VAL, APP, desc in (('subbitsval', 'df-subbits', 'subBits', SUBV, SUB, 'Value of subBits: the max-length low digits of the integer difference (Lean: subBits, by its clauses).'),
                                            ('subborrowval', 'df-subborrow', 'subBorrow', BORV, BOR, 'Value of subBorrow: set exactly when the subtraction falls short (Lean: subBorrow, by its clauses).'),
                                            ('subtruncval', 'df-subtrunc', 'subTrunc', TRV, TR, 'Value of subTrunc (Lean: subTrunc).')):
        if want(lab):
            w = W(lab, desc); cl = base(w)
            st, val = defval(w, cl, dlab, const, ['X', 'Y', 'C']); assert val == VAL, (val, VAL)
            promote(w, st); w.run()
    if want('cmpbitsval'):
        w = W('cmpbitsval', 'Value of cmpBits: the start verdict when the values agree, else their comparison (Lean: cmpBits_eq).')
        cl = base(w, AXY3, '3o'); st, val = defval(w, cl, 'df-cmpbits', 'cmpBits', ['X', 'Y', 'C']); assert val == CMPV, val
        promote(w, st); w.run()
    for lab, vl, APP, VAL, T, ante, kc in (('subbitscl', 'subbitsval', SUB, SUBV, 'Word 2o', AXY, '2o'), ('subborrowcl', 'subborrowval', BOR, BORV, '2o', AXY, '2o'),
                                          ('subtrunccl', 'subtruncval', TR, TRV, 'Word 2o', AXY, '2o'), ('cmpbitscl', 'cmpbitsval', CMP, CMPV, '3o', AXY3, '3o')):
        if want(lab):
            w = W(lab, 'Closure of %s.' % lab[:-2]); cl = base(w, ante, kc)
            v = w.s([], vl, '( %s -> %s = %s )' % (ante, APP, VAL)); m = cl.mem(VAL, T)
            w.qed([v, m], 'eqeltrd', '( %s -> %s e. %s )' % (ante, APP, T)); w.run()
    if want('subbitslen'):
        w = W('subbitslen', 'The difference word has the length of the longer operand (Lean: subBits_length).')
        cl = base(w); v = w.s([], 'subbitsval', '( %s -> %s = %s )' % (AXY, SUB, SUBV))
        h = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AXY, SUB, SUBV))
        lb = w.s([cl.mem(D, 'ZZ'), cl.mem(MX, 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AXY, SUBV, MX))
        w.qed([h, lb], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (AXY, SUB, MX)); w.run()
    if want('subborroweq0'):
        w = W('subborroweq0', 'No borrow runs off the end exactly when the subtraction is exact (Lean: subBorrow_eq_false_iff).')
        cl = base(w); v = w.s([], 'subborrowval', '( %s -> %s = %s )' % (AXY, BOR, BORV))
        e = w.s([v], 'eqeq1d', '( %s -> ( %s = (/) <-> %s = (/) ) )' % (AXY, BOR, BORV))
        n0 = w.s([], '1n0', '1o =/= (/)'); n1 = w.s([n0], 'necomi', '(/) =/= 1o')
        cond = '%s < ( %s + %s )' % (A, B, BNC)
        # if ( cond , 1o , (/) ) = (/) <-> -. cond : by iffalse / iftrue
        a1 = '( %s /\\ %s )' % (AXY, cond); h1 = w.s([], 'simpr', '( %s -> %s )' % (a1, cond)); i1 = w.s([h1], 'iftrued', '( %s -> %s = 1o )' % (a1, BORV))
        ne1 = w.s([n0], 'a1i', '( %s -> 1o =/= (/) )' % a1); ne2 = w.s([i1, ne1], 'eqnetrd', '( %s -> %s =/= (/) )' % (a1, BORV)); nq1 = w.s([ne2], 'neneqd', '( %s -> -. %s = (/) )' % (a1, BORV))
        nn1 = w.s([h1], 'notnotd', '( %s -> -. -. %s )' % (a1, cond)); c1 = w.s([nq1, nn1], '2falsed', '( %s -> ( %s = (/) <-> -. %s ) )' % (a1, BORV, cond))
        a2 = '( %s /\\ -. %s )' % (AXY, cond); h2 = w.s([], 'simpr', '( %s -> -. %s )' % (a2, cond)); i2 = w.s([h2], 'iffalsed', '( %s -> %s = (/) )' % (a2, BORV))
        c2 = w.s([i2, h2], '2thd', '( %s -> ( %s = (/) <-> -. %s ) )' % (a2, BORV, cond))
        c = w.s([c1, c2], 'pm2.61dan', '( %s -> ( %s = (/) <-> -. %s ) )' % (AXY, BORV, cond))
        ln = w.s([cl.mem('( %s + %s )' % (B, BNC), 'RR'), cl.mem(A, 'RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( ( %s + %s ) <_ %s <-> -. %s ) )' % (AXY, B, BNC, A, cond))
        w.qed([e, c, ln], '3bitr4d', '( %s -> ( %s = (/) <-> ( %s + %s ) <_ %s ) )' % (AXY, BOR, B, BNC, A)); w.run()
    if want('tonatsubbits'):
        w = W('tonatsubbits', 'The subtractor identity: the difference word plus the subtrahend plus the borrow-in is the minuend plus the borrow-out at the weight of the length (Lean: toNat_subBits).')
        cl = base(w)
        lx, ly, mn, ltx, lty = maxfacts(w, cl, AXY)
        cl.atom(PN); cl.leaf(PN, 'RR', cl.mem(PN, 'RR'))
        for E in (A, B, BNC):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        v = w.s([], 'subbitsval', '( %s -> %s = %s )' % (AXY, SUB, SUBV)); bv = w.s([], 'subborrowval', '( %s -> %s = %s )' % (AXY, BOR, BORV))
        tv = w.s([v], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AXY, SUB, SUBV))
        tb = w.s([cl.mem(D, 'ZZ'), mn, w.inst('tonatbwrd')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( %s mod %s ) )' % (AXY, SUBV, D, PN))
        tD = w.s([tv, tb], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s mod %s ) )' % (AXY, SUB, D, PN))
        le1 = w.s([cl.mem('C', '2o'), w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AXY, BNC)); g0 = cl.ge0(BNC); ga = cl.ge0(A); gb = cl.ge0(B)
        pz = cl.mem(PN, 'ZZ')
        zy = w.s([cl.mem(B, 'ZZ'), pz, w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (AXY, B, PN, B, PN)); ley = w.s([lty, zy], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (AXY, B, PN))
        cond = '%s < ( %s + %s )' % (A, B, BNC)
        concl = '( ( ( toNat ` %s ) + %s ) + %s ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (SUB, B, BNC, A, PN, BOR)
        concl = '( ( ( toNat ` %s ) + %s ) + %s ) = ( %s + ( %s x. ( bToNat ` %s ) ) )' % (SUB, B, BNC, A, PN, BOR)
        outs = []
        for case in (True, False):
            a2 = '( %s /\\ %s )' % (AXY, cond) if case else '( %s /\\ -. %s )' % (AXY, cond)
            h = w.s([], 'simpr', '( %s -> %s )' % (a2, cond if case else '-. ' + cond))
            c2 = Cl(w, a2, {}); c2.parent = cl
            for E in (PN, A, B, BNC):
                c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
            bv2 = lift(w, bv, a2)
            if case:
                it = w.s([h], 'iftrued', '( %s -> %s = 1o )' % (a2, BORV)); bo = w.s([bv2, it], 'eqtrd', '( %s -> %s = 1o )' % (a2, BOR))
                f = w.s([bo], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` 1o ) )' % (a2, BOR)); f2 = w.s([f, w.s([], 'bwbn1', '( bToNat ` 1o ) = 1')], 'eqtrdi', '( %s -> ( bToNat ` %s ) = 1 )' % (a2, BOR))
                pv = w.s([f2], 'oveq2d', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( %s x. 1 ) )' % (a2, PN, BOR, PN)); pv2 = w.s([pv, w.s([lift(w, cl.mem(PN, 'CC'), a2)], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (a2, PN, PN))], 'eqtrd', '( %s -> ( %s x. ( bToNat ` %s ) ) = %s )' % (a2, PN, BOR, PN))
                # D mod PN = D + PN : ( D + PN ) mod PN = D mod PN (modcyc with N=1) and D + PN in [0, PN)
                DP = '( %s + %s )' % (D, PN)
                one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % a2)
                mc = w.s([lift(w, cl.mem(D, 'RR'), a2), lift(w, cl.mem(PN, 'RR+'), a2), one, w.inst('modcyc')], 'syl3anc', '( %s -> ( ( %s + ( 1 x. %s ) ) mod %s ) = ( %s mod %s ) )' % (a2, D, PN, PN, D, PN))
                m1 = w.s([lift(w, cl.mem(PN, 'CC'), a2)], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (a2, PN, PN)); m2 = w.s([m1], 'oveq2d', '( %s -> ( %s + ( 1 x. %s ) ) = %s )' % (a2, D, PN, DP)); m3 = w.s([m2], 'oveq1d', '( %s -> ( ( %s + ( 1 x. %s ) ) mod %s ) = ( %s mod %s ) )' % (a2, D, PN, PN, DP, PN))
                mc2 = w.s([m3, mc], 'eqtr3d', '( %s -> ( %s mod %s ) = ( %s mod %s ) )' % (a2, DP, PN, D, PN))
                g1 = linarith(w, a2, [lift(w, ley, a2), lift(w, le1, a2), lift(w, ga, a2)], '0 <_ %s' % DP, closure=c2)
                g2 = linarith(w, a2, [h], '%s < %s' % (DP, PN), closure=c2)
                j = w.s([lift(w, cl.mem(DP, 'RR'), a2), lift(w, cl.mem(PN, 'RR+'), a2)], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (a2, DP, PN)); j2 = w.s([g1, g2], 'jca', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (a2, DP, DP, PN))
                mi = w.s([j, j2, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (a2, DP, PN, DP))
                dm = w.s([mc2, mi], 'eqtr3d', '( %s -> ( %s mod %s ) = %s )' % (a2, D, PN, DP))
                tD2 = w.s([lift(w, tD, a2), dm], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (a2, SUB, DP))
                c2.leaf('( toNat ` %s )' % SUB, 'RR', lift(w, cl.mem('( toNat ` %s )' % SUB, 'RR'), a2)); c2.leaf('( %s x. ( bToNat ` %s ) )' % (PN, BOR), 'RR', lift(w, cl.mem('( %s x. ( bToNat ` %s ) )' % (PN, BOR), 'RR'), a2))
                outs.append(lineq(w, a2, '( ( ( toNat ` %s ) + %s ) + %s )' % (SUB, B, BNC), '( %s + ( %s x. ( bToNat ` %s ) ) )' % (A, PN, BOR), hyps=[tD2, pv2], closure=c2))
            else:
                it = w.s([h], 'iffalsed', '( %s -> %s = (/) )' % (a2, BORV)); bo = w.s([bv2, it], 'eqtrd', '( %s -> %s = (/) )' % (a2, BOR))
                f = w.s([bo], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` (/) ) )' % (a2, BOR)); f2 = w.s([f, w.s([], 'bwbn0', '( bToNat ` (/) ) = 0')], 'eqtrdi', '( %s -> ( bToNat ` %s ) = 0 )' % (a2, BOR))
                pv = w.s([f2], 'oveq2d', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( %s x. 0 ) )' % (a2, PN, BOR, PN)); pv2 = w.s([pv, w.s([lift(w, cl.mem(PN, 'CC'), a2)], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (a2, PN))], 'eqtrd', '( %s -> ( %s x. ( bToNat ` %s ) ) = 0 )' % (a2, PN, BOR))
                ln = w.s([lift(w, cl.mem('( %s + %s )' % (B, BNC), 'RR'), a2), lift(w, cl.mem(A, 'RR'), a2), w.inst('lenlt')], 'syl2anc', '( %s -> ( ( %s + %s ) <_ %s <-> -. %s ) )' % (a2, B, BNC, A, cond)); ge = w.s([h, ln], 'mpbird', '( %s -> ( %s + %s ) <_ %s )' % (a2, B, BNC, A))
                g1 = linarith(w, a2, [ge], '0 <_ %s' % D, closure=c2)
                g2 = linarith(w, a2, [lift(w, ltx, a2), lift(w, gb, a2), lift(w, g0, a2)], '%s < %s' % (D, PN), closure=c2)
                j = w.s([lift(w, cl.mem(D, 'RR'), a2), lift(w, cl.mem(PN, 'RR+'), a2)], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (a2, D, PN)); j2 = w.s([g1, g2], 'jca', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (a2, D, D, PN))
                mi = w.s([j, j2, w.inst('modid')], 'syl2anc', '( %s -> ( %s mod %s ) = %s )' % (a2, D, PN, D))
                tD2 = w.s([lift(w, tD, a2), mi], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (a2, SUB, D))
                c2.leaf('( toNat ` %s )' % SUB, 'RR', lift(w, cl.mem('( toNat ` %s )' % SUB, 'RR'), a2)); c2.leaf('( %s x. ( bToNat ` %s ) )' % (PN, BOR), 'RR', lift(w, cl.mem('( %s x. ( bToNat ` %s ) )' % (PN, BOR), 'RR'), a2))
                outs.append(lineq(w, a2, '( ( ( toNat ` %s ) + %s ) + %s )' % (SUB, B, BNC), '( %s + ( %s x. ( bToNat ` %s ) ) )' % (A, PN, BOR), hyps=[tD2, pv2], closure=c2))
        w.qed(outs, 'pm2.61dan', '( %s -> %s )' % (AXY, concl)); w.run()
    if want('tonatsubtrunc'):
        w = W('tonatsubtrunc', 'The value of the truncated difference is the truncated difference of the values (Lean: toNat_subTrunc, with Nat subtraction written out).')
        cl = base(w)
        cond = '%s < ( %s + %s )' % (A, B, BNC)
        v = w.s([], 'subtruncval', '( %s -> %s = %s )' % (AXY, TR, TRV)); bv = w.s([], 'subborrowval', '( %s -> %s = %s )' % (AXY, BOR, BORV))
        tv = w.s([v], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AXY, TR, TRV))
        id_ = w.s([], 'tonatsubbits', '( %s -> ( ( ( toNat ` %s ) + %s ) + %s ) = ( %s + ( %s x. ( bToNat ` %s ) ) ) )' % (AXY, SUB, B, BNC, A, PN, BOR))
        concl = '( toNat ` %s ) = if ( %s , 0 , ( %s - ( %s + %s ) ) )' % (TR, cond, A, B, BNC)
        a1 = '( %s /\\ %s )' % (AXY, cond); h1 = w.s([], 'simpr', '( %s -> %s )' % (a1, cond))
        it = w.s([h1], 'iftrued', '( %s -> %s = 1o )' % (a1, BORV)); bo = w.s([lift(w, bv, a1), it], 'eqtrd', '( %s -> %s = 1o )' % (a1, BOR))
        i1 = w.s([bo], 'iftrued', '( %s -> %s = (/) )' % (a1, TRV)); t0 = w.s([i1], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` (/) ) )' % (a1, TRV)); z = w.s([], 'tonat0', '( toNat ` (/) ) = 0')
        t1 = w.s([t0, z], 'eqtrdi', '( %s -> ( toNat ` %s ) = 0 )' % (a1, TRV)); r1 = w.s([h1], 'iftrued', '( %s -> if ( %s , 0 , ( %s - ( %s + %s ) ) ) = 0 )' % (a1, cond, A, B, BNC))
        c1 = w.s([t1, r1], 'eqtr4d', '( %s -> ( toNat ` %s ) = if ( %s , 0 , ( %s - ( %s + %s ) ) ) )' % (a1, TRV, cond, A, B, BNC))
        a2 = '( %s /\\ -. %s )' % (AXY, cond); h2 = w.s([], 'simpr', '( %s -> -. %s )' % (a2, cond))
        it2 = w.s([h2], 'iffalsed', '( %s -> %s = (/) )' % (a2, BORV)); bo2 = w.s([lift(w, bv, a2), it2], 'eqtrd', '( %s -> %s = (/) )' % (a2, BOR))
        n0 = w.s([], '1n0', '1o =/= (/)'); nn = w.s([n0], 'nesymi', '-. (/) = 1o'); nnd = w.s([nn], 'a1i', '( %s -> -. (/) = 1o )' % a2)
        eq = w.s([bo2], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (a2, BOR)); nb = w.s([nnd, eq], 'mtbird', '( %s -> -. %s = 1o )' % (a2, BOR))
        i2 = w.s([nb], 'iffalsed', '( %s -> %s = %s )' % (a2, TRV, SUB)); t2 = w.s([i2], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (a2, TRV, SUB))
        f = w.s([bo2], 'fveq2d', '( %s -> ( bToNat ` %s ) = ( bToNat ` (/) ) )' % (a2, BOR)); f2 = w.s([f, w.s([], 'bwbn0', '( bToNat ` (/) ) = 0')], 'eqtrdi', '( %s -> ( bToNat ` %s ) = 0 )' % (a2, BOR))
        pv = w.s([f2], 'oveq2d', '( %s -> ( %s x. ( bToNat ` %s ) ) = ( %s x. 0 ) )' % (a2, PN, BOR, PN)); pv2 = w.s([pv, w.s([lift(w, cl.mem(PN, 'CC'), a2)], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (a2, PN))], 'eqtrd', '( %s -> ( %s x. ( bToNat ` %s ) ) = 0 )' % (a2, PN, BOR))
        c2 = Cl(w, a2, {}); c2.parent = cl
        for E in (A, B, BNC, '( toNat ` %s )' % SUB, '( %s x. ( bToNat ` %s ) )' % (PN, BOR)):
            c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
        eqv = lineq(w, a2, '( toNat ` %s )' % SUB, '( %s - ( %s + %s ) )' % (A, B, BNC), hyps=[lift(w, id_, a2), pv2], closure=c2)
        r2 = w.s([h2], 'iffalsed', '( %s -> if ( %s , 0 , ( %s - ( %s + %s ) ) ) = ( %s - ( %s + %s ) ) )' % (a2, cond, A, B, BNC, A, B, BNC))
        t3 = w.s([t2, eqv], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s - ( %s + %s ) ) )' % (a2, TRV, A, B, BNC))
        cc2 = w.s([t3, r2], 'eqtr4d', '( %s -> ( toNat ` %s ) = if ( %s , 0 , ( %s - ( %s + %s ) ) ) )' % (a2, TRV, cond, A, B, BNC))
        c = w.s([c1, cc2], 'pm2.61dan', '( %s -> ( toNat ` %s ) = if ( %s , 0 , ( %s - ( %s + %s ) ) ) )' % (AXY, TRV, cond, A, B, BNC))
        w.qed([tv, c], 'eqtrd', '( %s -> %s )' % (AXY, concl)); w.run()
    if want('subtrunclen'):
        w = W('subtrunclen', 'The truncated difference has at most the length of the longer operand (Lean: subTrunc_length).')
        cl = base(w); v = w.s([], 'subtruncval', '( %s -> %s = %s )' % (AXY, TR, TRV))
        h = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AXY, TR, TRV))
        cond = '%s = 1o' % BOR
        a1 = '( %s /\\ %s )' % (AXY, cond); h1 = w.s([], 'simpr', '( %s -> %s )' % (a1, cond)); i1 = w.s([h1], 'iftrued', '( %s -> %s = (/) )' % (a1, TRV))
        l1 = w.s([i1], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (a1, TRV)); z = w.s([], 'hash0', '( # ` (/) ) = 0'); l1b = w.s([l1, z], 'eqtrdi', '( %s -> ( # ` %s ) = 0 )' % (a1, TRV))
        g = w.s([lift(w, cl.mem(MX, 'NN0'), a1)], 'nn0ge0d', '( %s -> 0 <_ %s )' % (a1, MX)); c1 = w.s([l1b, g], 'eqbrtrd', '( %s -> ( # ` %s ) <_ %s )' % (a1, TRV, MX))
        a2 = '( %s /\\ -. %s )' % (AXY, cond); h2 = w.s([], 'simpr', '( %s -> -. %s )' % (a2, cond)); i2 = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, TRV, SUB))
        l2 = w.s([i2], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (a2, TRV, SUB)); sl = lift(w, w.s([], 'subbitslen', '( %s -> ( # ` %s ) = %s )' % (AXY, SUB, MX)), a2)
        l2b = w.s([l2, sl], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (a2, TRV, MX)); li = w.s([lift(w, cl.mem(MX, 'RR'), a2)], 'leidd', '( %s -> %s <_ %s )' % (a2, MX, MX))
        c2 = w.s([l2b, li], 'eqbrtrd', '( %s -> ( # ` %s ) <_ %s )' % (a2, TRV, MX))
        c = w.s([c1, c2], 'pm2.61dan', '( %s -> ( # ` %s ) <_ %s )' % (AXY, TRV, MX))
        w.qed([h, c], 'eqbrtrd', '( %s -> ( # ` %s ) <_ %s )' % (AXY, TR, MX)); w.run()
    if want('subborrowfold'):
        w = W('subborrowfold', 'The borrow-out is the borrow fold at the max length: the form the loop assembly instantiates.')
        cl = base(w)
        lx, ly, mn, ltx, lty = maxfacts(w, cl, AXY)
        v = w.s([], 'subborrowval', '( %s -> %s = %s )' % (AXY, BOR, BORV))
        az = cl.mem(A, 'ZZ'); bz = cl.mem(B, 'ZZ'); c2 = cl.mem('C', '2o')
        j = w.s([az, bz, c2], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ C e. 2o ) )' % (AXY, A, B))
        F = FOLD('borrow', A, B, 'C', MX)
        BI = 'if ( ( %s mod %s ) < ( ( %s mod %s ) + %s ) , 1o , (/) )' % (A, PN, B, PN, BNC)
        cf = w.s([j, mn, w.inst('bwborrow')], 'syl2anc', '( %s -> %s = %s )' % (AXY, F, BI))
        pn = cl.mem(PN, 'NN')
        mx = w.s([az, pn, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( ( %s mod %s ) = %s <-> %s e. ( 0 ..^ %s ) ) )' % (AXY, A, PN, A, A, PN))
        ex = w.s([cl.mem(A, 'NN0'), cl.mem(PN, 'ZZ'), ltx, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (AXY, A, PN)); mx2 = w.s([ex, mx], 'mpbird', '( %s -> ( %s mod %s ) = %s )' % (AXY, A, PN, A))
        my = w.s([bz, pn, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( ( %s mod %s ) = %s <-> %s e. ( 0 ..^ %s ) ) )' % (AXY, B, PN, B, B, PN))
        ey = w.s([cl.mem(B, 'NN0'), cl.mem(PN, 'ZZ'), lty, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (AXY, B, PN)); my2 = w.s([ey, my], 'mpbird', '( %s -> ( %s mod %s ) = %s )' % (AXY, B, PN, B))
        o = w.s([my2], 'oveq1d', '( %s -> ( ( %s mod %s ) + %s ) = ( %s + %s ) )' % (AXY, B, PN, BNC, B, BNC))
        br = w.s([mx2, o], 'breq12d', '( %s -> ( ( %s mod %s ) < ( ( %s mod %s ) + %s ) <-> %s < ( %s + %s ) ) )' % (AXY, A, PN, B, PN, BNC, A, B, BNC))
        ib = w.s([br], 'ifbid', '( %s -> %s = %s )' % (AXY, BI, BORV))
        cf2 = w.s([cf, ib], 'eqtrd', '( %s -> %s = %s )' % (AXY, F, BORV))
        w.qed([v, cf2], 'eqtr4d', '( %s -> %s = %s )' % (AXY, BOR, F)); w.run()
    if want('cmpbitsfold'):
        w = W('cmpbitsfold', 'The comparison is the cmpStep fold at the max length: the form the loop assembly instantiates.')
        cl = base(w, AXY3, '3o')
        lx, ly, mn, ltx, lty = maxfacts(w, cl, AXY3)
        v = w.s([], 'cmpbitsval', '( %s -> %s = %s )' % (AXY3, CMP, CMPV))
        an = cl.mem(A, 'NN0'); bn = cl.mem(B, 'NN0'); c3 = cl.mem('C', '3o')
        j = w.s([an, bn, c3], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ C e. 3o ) )' % (AXY3, A, B))
        F = FOLD('cmpStep', A, B, 'C', MX)
        VI = 'if ( ( %s mod %s ) = ( %s mod %s ) , C , ( ( %s mod %s ) Ncmp ( %s mod %s ) ) )' % (A, PN, B, PN, A, PN, B, PN)
        cf = w.s([j, mn, w.inst('bwcmpf')], 'syl2anc', '( %s -> %s = %s )' % (AXY3, F, VI))
        pn = cl.mem(PN, 'NN'); az = cl.mem(A, 'ZZ'); bz = cl.mem(B, 'ZZ')
        mx = w.s([az, pn, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( ( %s mod %s ) = %s <-> %s e. ( 0 ..^ %s ) ) )' % (AXY3, A, PN, A, A, PN))
        ex = w.s([an, cl.mem(PN, 'ZZ'), ltx, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (AXY3, A, PN)); mx2 = w.s([ex, mx], 'mpbird', '( %s -> ( %s mod %s ) = %s )' % (AXY3, A, PN, A))
        my = w.s([bz, pn, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( ( %s mod %s ) = %s <-> %s e. ( 0 ..^ %s ) ) )' % (AXY3, B, PN, B, B, PN))
        ey = w.s([bn, cl.mem(PN, 'ZZ'), lty, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (AXY3, B, PN)); my2 = w.s([ey, my], 'mpbird', '( %s -> ( %s mod %s ) = %s )' % (AXY3, B, PN, B))
        e = w.s([mx2, my2], 'eqeq12d', '( %s -> ( ( %s mod %s ) = ( %s mod %s ) <-> %s = %s ) )' % (AXY3, A, PN, B, PN, A, B))
        o = w.s([mx2, my2], 'oveq12d', '( %s -> ( ( %s mod %s ) Ncmp ( %s mod %s ) ) = ( %s Ncmp %s ) )' % (AXY3, A, PN, B, PN, A, B))
        ib = w.s([e, o], 'ifbieq2d', '( %s -> %s = %s )' % (AXY3, VI, CMPV))
        cf2 = w.s([cf, ib], 'eqtrd', '( %s -> %s = %s )' % (AXY3, F, CMPV))
        w.qed([v, cf2], 'eqtr4d', '( %s -> %s = %s )' % (AXY3, CMP, F)); w.run()
    if want('cmpbitseq'):
        w = W('cmpbitseq', 'The comparison from the neutral verdict is the comparison of the values (Lean: cmpBits_eq_compare).')
        A2 = '( X e. Word 2o /\\ Y e. Word 2o )'
        x = w.s([], 'simpl', '( %s -> X e. Word 2o )' % A2); y = w.s([], 'simpr', '( %s -> Y e. Word 2o )' % A2)
        cl = Cl(w, A2, {'X': ('Word 2o', x), 'Y': ('Word 2o', y)})
        one = w.s([w.s([], 'bw1oel3o', '1o e. 3o')], 'a1i', '( %s -> 1o e. 3o )' % A2)
        v = w.s([x, y, one, w.inst('cmpbitsval')], 'syl3anc', '( %s -> ( ( X cmpBits Y ) ` 1o ) = if ( %s = %s , 1o , ( %s Ncmp %s ) ) )' % (A2, A, B, A, B))
        an = cl.mem(A, 'NN0'); bn = cl.mem(B, 'NN0')
        ne = w.s([an, bn, w.inst('ncmpeq')], 'syl2anc', '( %s -> ( ( %s Ncmp %s ) = 1o <-> %s = %s ) )' % (A2, A, B, A, B))
        a1 = '( %s /\\ %s = %s )' % (A2, A, B); h1 = w.s([], 'simpr', '( %s -> %s = %s )' % (a1, A, B))
        i1 = w.s([h1], 'iftrued', '( %s -> if ( %s = %s , 1o , ( %s Ncmp %s ) ) = 1o )' % (a1, A, B, A, B))
        n1 = w.s([h1, lift(w, ne, a1)], 'mpbird', '( %s -> ( %s Ncmp %s ) = 1o )' % (a1, A, B)); c1 = w.s([i1, n1], 'eqtr4d', '( %s -> if ( %s = %s , 1o , ( %s Ncmp %s ) ) = ( %s Ncmp %s ) )' % (a1, A, B, A, B, A, B))
        a2 = '( %s /\\ -. %s = %s )' % (A2, A, B); h2 = w.s([], 'simpr', '( %s -> -. %s = %s )' % (a2, A, B))
        c2 = w.s([h2], 'iffalsed', '( %s -> if ( %s = %s , 1o , ( %s Ncmp %s ) ) = ( %s Ncmp %s ) )' % (a2, A, B, A, B, A, B))
        c = w.s([c1, c2], 'pm2.61dan', '( %s -> if ( %s = %s , 1o , ( %s Ncmp %s ) ) = ( %s Ncmp %s ) )' % (A2, A, B, A, B, A, B))
        w.qed([v, c], 'eqtrd', '( %s -> ( ( X cmpBits Y ) ` 1o ) = ( %s Ncmp %s ) )' % (A2, A, B)); w.run()
