"""Sortie T4, group C: toNat and the spine (T4-blueprint section 3.3, first half)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AL = 'L e. Word 2o'
SUMI = lambda L: 'sum_ i e. %s ( 2 ^ i )' % BITSET(L)
SUMN = lambda A: 'sum_ n e. %s ( 2 ^ n )' % A
DOM = lambda L: '( 0 ..^ ( # ` %s ) )' % L
AI = '( L e. Word 2o /\\ I e. ( 0 ..^ ( # ` L ) ) )'


def clL(w, ante=AL):
    return Cl(w, ante, {'L': ('Word 2o', w.s([], 'id', '( %s -> L e. Word 2o )' % ante))})


if __name__ == '__main__':
    if want('tonatval'):
        w = W('tonatval', 'Value of toNat: the sum of 2 ^ i over the positions i of L holding true (Lean: toNat, LSB first).')
        cl = clL(w)
        st, val = defval(w, cl, 'df-tonat', 'toNat', ['L'])
        assert val == SUMI('L'), val
        promote(w, st); w.run()

    if want('tonatlem1'):
        w = W('tonatlem1', 'Lemma for toNat: the set of positions holding true is a finite set of nonnegative integers.')
        cl = clL(w)
        S = BITSET('L')
        ss = w.s([], 'ssrab2', '%s C_ %s' % (S, DOM('L')))
        z = w.s([], '0nn0', '0 e. NN0'); fz = w.s([z, w.inst('fzossnn0')], 'ax-mp', '%s C_ NN0' % DOM('L'))
        s2 = w.s([ss, fz], 'sstri', '%s C_ NN0' % S)
        ex = w.s([], 'nn0ex', 'NN0 e. _V')
        pw = w.s([ex, w.inst('elpw2g')], 'ax-mp', '( %s e. ~P NN0 <-> %s C_ NN0 )' % (S, S))
        p = w.s([s2, pw], 'mpbir', '%s e. ~P NN0' % S)
        fi = w.s([], 'fzofi', '%s e. Fin' % DOM('L')); f2 = w.s([fi, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % S)
        ei = w.s([], 'elin', '( %s e. ( ~P NN0 i^i Fin ) <-> ( %s e. ~P NN0 /\\ %s e. Fin ) )' % (S, S, S))
        j = w.s([p, f2], 'pm3.2i', '( %s e. ~P NN0 /\\ %s e. Fin )' % (S, S))
        w.qed([j, ei], 'mpbir', '%s e. ( ~P NN0 i^i Fin )' % S); w.run()

    if want('bwbits'):
        w = W('bwbits', 'The binary digits of the value of a bit word are its positions holding true.')
        S = BITSET('L')
        v = w.s([], 'tonatval', '( %s -> ( toNat ` L ) = %s )' % (AL, SUMI('L')))
        r = sumren(w, AL, S, 'i', 'n')
        v2 = w.s([v, r], 'eqtrd', '( %s -> ( toNat ` L ) = %s )' % (AL, SUMN(S)))
        f = w.s([v2], 'fveq2d', '( %s -> ( bits ` ( toNat ` L ) ) = ( bits ` %s ) )' % (AL, SUMN(S)))
        l1 = w.s([], 'tonatlem1', '%s e. ( ~P NN0 i^i Fin )' % S)
        b = w.s([l1, w.inst('bitsinv2')], 'ax-mp', '( bits ` %s ) = %s' % (SUMN(S), S))
        w.qed([f, b], 'eqtrdi', '( %s -> ( bits ` ( toNat ` L ) ) = %s )' % (AL, S)); w.run()

    if want('tonatcl'):
        w = W('tonatcl', 'Closure of toNat: a nonnegative integer.')
        cl = clL(w)
        v = w.s([], 'tonatval', '( %s -> ( toNat ` L ) = %s )' % (AL, SUMI('L')))
        r = sumren(w, AL, BITSET('L'), 'i', 'n')
        v2 = w.s([v, r], 'eqtrd', '( %s -> ( toNat ` L ) = %s )' % (AL, SUMN(BITSET('L'))))
        m = cl.mem(SUMN(BITSET('L')), 'NN0')
        w.qed([v2, m], 'eqeltrd', '( %s -> ( toNat ` L ) e. NN0 )' % AL); w.run()

    if want('tonatf'):
        w = W('tonatf', 'toNat is a function from the bit words to the nonnegative integers.')
        d = w.s([], 'df-tonat', 'toNat = ( l e. Word 2o |-> %s )' % SUMI('l'))
        v = w.s([], 'tonatval', '( l e. Word 2o -> ( toNat ` l ) = %s )' % SUMI('l'))
        c = w.s([], 'tonatcl', '( l e. Word 2o -> ( toNat ` l ) e. NN0 )')
        e = w.s([v, c], 'eqeltrrd', '( l e. Word 2o -> %s e. NN0 )' % SUMI('l'))
        w.qed([d, e], 'fmpti', 'toNat : Word 2o --> NN0'); w.run()

    if want('bwbitsss'):
        w = W('bwbitsss', 'The binary digits of the value of a bit word lie below its length.')
        b = w.s([], 'bwbits', '( %s -> ( bits ` ( toNat ` L ) ) = %s )' % (AL, BITSET('L')))
        ss = w.s([], 'ssrab2', '%s C_ %s' % (BITSET('L'), DOM('L')))
        w.qed([b, ss], 'eqsstrdi', '( %s -> ( bits ` ( toNat ` L ) ) C_ %s )' % (AL, DOM('L'))); w.run()

    if want('bwfvb'):
        w = W('bwfvb', 'A letter of a bit word is true exactly when its position is a binary digit of the value.')
        l = w.s([], 'simpl', '( %s -> L e. Word 2o )' % AI); ii = w.s([], 'simpr', '( %s -> I e. %s )' % (AI, DOM('L')))
        b = w.s([l, w.inst('bwbits')], 'syl', '( %s -> ( bits ` ( toNat ` L ) ) = %s )' % (AI, BITSET('L')))
        e = w.s([b], 'eleq2d', '( %s -> ( I e. ( bits ` ( toNat ` L ) ) <-> I e. %s ) )' % (AI, BITSET('L')))
        be = bitsetel(w, AI, 'L', 'I', ii)
        bi = w.s([e, be], 'bitrd', '( %s -> ( I e. ( bits ` ( toNat ` L ) ) <-> ( L ` I ) = 1o ) )' % AI)
        w.qed([bi], 'bicomd', '( %s -> ( ( L ` I ) = 1o <-> I e. ( bits ` ( toNat ` L ) ) ) )' % AI); w.run()

    if want('bwfv'):
        w = W('bwfv', 'A letter of a bit word is the binary digit of its value at that position, as a Boolean.')
        B = BIT(TN('L'), 'I')
        sym = w.s([], 'wrdsymbcl', '( %s -> ( L ` I ) e. 2o )' % AI)
        bi = w.s([], 'bwfvb', '( %s -> ( ( L ` I ) = 1o <-> I e. ( bits ` ( toNat ` L ) ) ) )' % AI)
        a1 = '( %s /\\ ( L ` I ) = 1o )' % AI
        h1 = w.s([], 'simpr', '( %s -> ( L ` I ) = 1o )' % a1)
        bi1 = w.s([bi], 'adantr', '( %s -> ( ( L ` I ) = 1o <-> I e. ( bits ` ( toNat ` L ) ) ) )' % a1)
        m1 = w.s([h1, bi1], 'mpbid', '( %s -> I e. ( bits ` ( toNat ` L ) ) )' % a1)
        i1 = w.s([m1], 'iftrued', '( %s -> %s = 1o )' % (a1, B))
        c1 = w.s([h1, i1], 'eqtr4d', '( %s -> ( L ` I ) = %s )' % (a1, B))
        a2 = '( %s /\\ -. ( L ` I ) = 1o )' % AI
        h2 = w.s([], 'simpr', '( %s -> -. ( L ` I ) = 1o )' % a2)
        bi2 = w.s([bi], 'adantr', '( %s -> ( ( L ` I ) = 1o <-> I e. ( bits ` ( toNat ` L ) ) ) )' % a2)
        m2 = w.s([h2, bi2], 'mtbid', '( %s -> -. I e. ( bits ` ( toNat ` L ) ) )' % a2)
        i2 = w.s([m2], 'iffalsed', '( %s -> %s = (/) )' % (a2, B))
        sym2 = w.s([sym], 'adantr', '( %s -> ( L ` I ) e. 2o )' % a2)
        n2 = w.s([sym2, w.inst('bwel2on')], 'syl', '( %s -> ( -. ( L ` I ) = 1o <-> ( L ` I ) = (/) ) )' % a2)
        z2 = w.s([h2, n2], 'mpbid', '( %s -> ( L ` I ) = (/) )' % a2)
        c2 = w.s([z2, i2], 'eqtr4d', '( %s -> ( L ` I ) = %s )' % (a2, B))
        w.qed([c1, c2], 'pm2.61dan', '( %s -> ( L ` I ) = %s )' % (AI, B)); w.run()

    if want('bweqwrd'):
        w = W('bweqwrd', 'A bit word is the digits word of its value at its length: the value and the length determine the word.')
        cl = clL(w)
        R = BWRD(TN('L'), LEN('L'))
        tz = cl.mem(TN('L'), 'ZZ'); ln = cl.mem(LEN('L'), 'NN0')
        clR = cl.mem(R, 'Word 2o')
        le = w.s([tz, ln, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` L ) )' % (AL, R))
        leneq = w.s([le], 'eqcomd', '( %s -> ( # ` L ) = ( # ` %s ) )' % (AL, R))

        def letter(a2, ist):
            lhs = w.s([], 'bwfv', '( %s -> ( L ` i ) = %s )' % (a2, BIT(TN('L'), 'i')))
            tz2 = w.s([tz], 'adantr', '( %s -> %s e. ZZ )' % (a2, TN('L'))); ln2 = w.s([ln], 'adantr', '( %s -> ( # ` L ) e. NN0 )' % a2)
            rhs = w.s([tz2, ln2, ist, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, R, BIT(TN('L'), 'i')))
            return w.s([lhs, rhs], 'eqtr4d', '( %s -> ( L ` i ) = ( %s ` i ) )' % (a2, R))
        wrdeq(w, AL, 'L', R, w.s([], 'id', '( %s -> L e. Word 2o )' % AL), clR, leneq, letter, name='qed'); w.run()

    if want('bwbitsinj'):
        w = W('bwbitsinj', 'The binary digits determine the integer (set.mm\'s bitsf1).')
        A = '( X e. ZZ /\\ Y e. ZZ )'
        f = w.s([], 'bitsf1', 'bits : ZZ -1-1-> ~P NN0'); fd = w.s([f], 'a1i', '( %s -> bits : ZZ -1-1-> ~P NN0 )' % A)
        i = w.s([], 'id', '( %s -> %s )' % (A, A))
        w.qed([fd, i, w.inst('f1fveq')], 'syl2anc', '( %s -> ( ( bits ` X ) = ( bits ` Y ) <-> X = Y ) )' % A); w.run()

    if want('bwuniq'):
        w = W('bwuniq', 'Two bit words are equal exactly when they have the same length and the same value (Lean: Canon.unique, in the length form).')
        A = '( L e. Word 2o /\\ K e. Word 2o )'
        l = w.s([], 'simpl', '( %s -> L e. Word 2o )' % A); k = w.s([], 'simpr', '( %s -> K e. Word 2o )' % A)
        e1 = w.s([], 'fveq2', '( L = K -> ( # ` L ) = ( # ` K ) )'); e2 = w.s([], 'fveq2', '( L = K -> ( toNat ` L ) = ( toNat ` K ) )')
        fw = w.s([e1, e2], 'jca', '( L = K -> ( ( # ` L ) = ( # ` K ) /\\ ( toNat ` L ) = ( toNat ` K ) ) )')
        fwd = w.s([fw], 'a1i', '( %s -> ( L = K -> ( ( # ` L ) = ( # ` K ) /\\ ( toNat ` L ) = ( toNat ` K ) ) ) )' % A)
        a2 = '( %s /\\ ( ( # ` L ) = ( # ` K ) /\\ ( toNat ` L ) = ( toNat ` K ) ) )' % A
        hl = w.s([], 'simprl', '( %s -> ( # ` L ) = ( # ` K ) )' % a2); ht = w.s([], 'simprr', '( %s -> ( toNat ` L ) = ( toNat ` K ) )' % a2)
        l2 = w.s([l], 'adantr', '( %s -> L e. Word 2o )' % a2); k2 = w.s([k], 'adantr', '( %s -> K e. Word 2o )' % a2)
        wl = w.s([l2, w.inst('bweqwrd')], 'syl', '( %s -> L = %s )' % (a2, BWRD(TN('L'), LEN('L'))))
        wk = w.s([k2, w.inst('bweqwrd')], 'syl', '( %s -> K = %s )' % (a2, BWRD(TN('K'), LEN('K'))))
        o = w.s([ht, hl], 'oveq12d', '( %s -> %s = %s )' % (a2, BWRD(TN('L'), LEN('L')), BWRD(TN('K'), LEN('K'))))
        eq = w.s([wl, o, wk], '3eqtr4d', '( %s -> L = K )' % a2)
        bk = w.s([eq], 'ex', '( %s -> ( ( ( # ` L ) = ( # ` K ) /\\ ( toNat ` L ) = ( toNat ` K ) ) -> L = K ) )' % A)
        w.qed([fwd, bk], 'impbid', '( %s -> ( L = K <-> ( ( # ` L ) = ( # ` K ) /\\ ( toNat ` L ) = ( toNat ` K ) ) ) )' % A); w.run()

    AN = '( N e. ZZ /\\ M e. NN0 )'
    if want('bwrdbitset'):
        w = W('bwrdbitset', 'The positions of the digits word holding true are the binary digits of the number below the length.')
        cl = Cl(w, AN, conj_leaves(w, AN, [('N', 'ZZ'), ('M', 'NN0')]))
        Bw = BWRD('N', 'M')
        le = w.s([cl.mem('N', 'ZZ'), cl.mem('M', 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = M )' % (AN, Bw))
        o = w.s([le], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ M ) )' % (AN, Bw))
        r1 = w.s([o], 'rabeqdv', '( %s -> %s = { i e. ( 0 ..^ M ) | ( %s ` i ) = 1o } )' % (AN, BITSET(Bw), Bw))
        a2 = '( %s /\\ i e. ( 0 ..^ M ) )' % AN
        ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ M ) )' % a2)
        n2 = w.s([cl.mem('N', 'ZZ')], 'adantr', '( %s -> N e. ZZ )' % a2); m2 = w.s([cl.mem('M', 'NN0')], 'adantr', '( %s -> M e. NN0 )' % a2)
        fv = w.s([n2, m2, ii, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, Bw, BIT('N', 'i')))
        e1 = w.s([fv], 'eqeq1d', '( %s -> ( ( %s ` i ) = 1o <-> %s = 1o ) )' % (a2, Bw, BIT('N', 'i')))
        n0 = w.s([], '1n0', '1o =/= (/)'); tb = w.s([n0, w.inst('iftrueb')], 'ax-mp', '( %s = 1o <-> i e. ( bits ` N ) )' % BIT('N', 'i'))
        tbd = w.s([tb], 'a1i', '( %s -> ( %s = 1o <-> i e. ( bits ` N ) ) )' % (a2, BIT('N', 'i')))
        b = w.s([e1, tbd], 'bitrd', '( %s -> ( ( %s ` i ) = 1o <-> i e. ( bits ` N ) ) )' % (a2, Bw))
        r2 = w.s([b], 'rabbidva', '( %s -> { i e. ( 0 ..^ M ) | ( %s ` i ) = 1o } = { i e. ( 0 ..^ M ) | i e. ( bits ` N ) } )' % (AN, Bw))
        d5 = w.s([], 'dfin5', '( ( 0 ..^ M ) i^i ( bits ` N ) ) = { i e. ( 0 ..^ M ) | i e. ( bits ` N ) }')
        ic = w.s([], 'incom', '( ( 0 ..^ M ) i^i ( bits ` N ) ) = ( ( bits ` N ) i^i ( 0 ..^ M ) )')
        d6 = w.s([d5, ic], 'eqtr3i', '{ i e. ( 0 ..^ M ) | i e. ( bits ` N ) } = ( ( bits ` N ) i^i ( 0 ..^ M ) )')
        r12 = w.s([r1, r2], 'eqtrd', '( %s -> %s = { i e. ( 0 ..^ M ) | i e. ( bits ` N ) } )' % (AN, BITSET(Bw)))
        w.qed([r12, d6], 'eqtrdi', '( %s -> %s = ( ( bits ` N ) i^i ( 0 ..^ M ) ) )' % (AN, BITSET(Bw))); w.run()

    if want('tonatbwrd'):
        w = W('tonatbwrd', 'The value of the digits word of N of length M is N modulo 2 ^ M.')
        cl = Cl(w, AN, conj_leaves(w, AN, [('N', 'ZZ'), ('M', 'NN0')]))
        Bw = BWRD('N', 'M'); NM = MOD2('N', 'M')
        clB = cl.mem(Bw, 'Word 2o')
        b1 = w.s([clB, w.inst('bwbits')], 'syl', '( %s -> ( bits ` ( toNat ` %s ) ) = %s )' % (AN, Bw, BITSET(Bw)))
        b2 = w.s([], 'bwrdbitset', '( %s -> %s = ( ( bits ` N ) i^i ( 0 ..^ M ) ) )' % (AN, BITSET(Bw)))
        b3 = w.s([cl.mem('N', 'ZZ'), cl.mem('M', 'NN0'), w.inst('bitsmod')], 'syl2anc', '( %s -> ( bits ` %s ) = ( ( bits ` N ) i^i ( 0 ..^ M ) ) )' % (AN, NM))
        b4 = w.s([b1, b2, b3], '3eqtr4d', '( %s -> ( bits ` ( toNat ` %s ) ) = ( bits ` %s ) )' % (AN, Bw, NM))
        tz = cl.mem(TN(Bw), 'ZZ'); mz = cl.mem(NM, 'ZZ')
        inj = w.s([tz, mz, w.inst('bwbitsinj')], 'syl2anc', '( %s -> ( ( bits ` ( toNat ` %s ) ) = ( bits ` %s ) <-> ( toNat ` %s ) = %s ) )' % (AN, Bw, NM, Bw, NM))
        w.qed([b4, inj], 'mpbid', '( %s -> ( toNat ` %s ) = %s )' % (AN, Bw, NM)); w.run()

    if want('tonatbwrd2'):
        A = '( N e. NN0 /\\ M e. NN0 /\\ N < ( 2 ^ M ) )'
        w = W('tonatbwrd2', 'The value of the digits word of N below 2 ^ M at length M is N itself.')
        n = w.s([], 'simp1', '( %s -> N e. NN0 )' % A); m = w.s([], 'simp2', '( %s -> M e. NN0 )' % A); lt = w.s([], 'simp3', '( %s -> N < ( 2 ^ M ) )' % A)
        cl = Cl(w, A, {'N': ('NN0', n), 'M': ('NN0', m)})
        nz = cl.mem('N', 'ZZ')
        t = w.s([nz, m, w.inst('tonatbwrd')], 'syl2anc', '( %s -> ( toNat ` %s ) = %s )' % (A, BWRD('N', 'M'), MOD2('N', 'M')))
        p2 = cl.mem('( 2 ^ M )', 'NN')
        mi = w.s([nz, p2, w.inst('zmodidfzo')], 'syl2anc', '( %s -> ( %s = N <-> N e. ( 0 ..^ ( 2 ^ M ) ) ) )' % (A, MOD2('N', 'M')))
        p2z = cl.mem('( 2 ^ M )', 'ZZ')
        el = w.s([n, p2z, lt, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> N e. ( 0 ..^ ( 2 ^ M ) ) )' % A)
        mi2 = w.s([el, mi], 'mpbird', '( %s -> %s = N )' % (A, MOD2('N', 'M')))
        w.qed([t, mi2], 'eqtrd', '( %s -> ( toNat ` %s ) = N )' % (A, BWRD('N', 'M'))); w.run()

    if want('tonatlt'):
        w = W('tonatlt', 'The value of a bit word is below 2 to its length (Lean: toNat_lt_two_pow).')
        cl = clL(w)
        tz = cl.mem(TN('L'), 'ZZ'); ln = cl.mem(LEN('L'), 'NN0')
        bf = w.s([tz, ln, w.inst('bitsfzo')], 'syl2anc', '( %s -> ( ( toNat ` L ) e. ( 0 ..^ ( 2 ^ ( # ` L ) ) ) <-> ( bits ` ( toNat ` L ) ) C_ %s ) )' % (AL, DOM('L')))
        ss = w.s([], 'bwbitsss', '( %s -> ( bits ` ( toNat ` L ) ) C_ %s )' % (AL, DOM('L')))
        el = w.s([ss, bf], 'mpbird', '( %s -> ( toNat ` L ) e. ( 0 ..^ ( 2 ^ ( # ` L ) ) ) )' % AL)
        w.qed([el, w.inst('elfzolt2')], 'syl', '( %s -> ( toNat ` L ) < ( 2 ^ ( # ` L ) ) )' % AL); w.run()

    if want('tonat0'):
        w = W('tonat0', 'The value of the empty word is 0 (Lean: toNat []).')
        e = w.s([], 'wrd0', '(/) e. Word 2o'); v = w.s([], 'tonatval', '( (/) e. Word 2o -> ( toNat ` (/) ) = %s )' % SUMI('(/)'))
        v2 = w.s([e, v], 'ax-mp', '( toNat ` (/) ) = %s' % SUMI('(/)'))
        h = w.s([], 'hash0', '( # ` (/) ) = 0'); o = w.s([h], 'oveq2i', '( 0 ..^ ( # ` (/) ) ) = ( 0 ..^ 0 )'); f = w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')
        o2 = w.s([o, f], 'eqtri', '( 0 ..^ ( # ` (/) ) ) = (/)')
        r = w.s([o2], 'rabeqi', '%s = { i e. (/) | ( (/) ` i ) = 1o }' % BITSET('(/)'))
        r0 = w.s([], 'rab0', '{ i e. (/) | ( (/) ` i ) = 1o } = (/)')
        r2 = w.s([r, r0], 'eqtri', '%s = (/)' % BITSET('(/)'))
        s = w.s([r2], 'sumeq1i', '%s = sum_ i e. (/) ( 2 ^ i )' % SUMI('(/)'))
        s0 = w.s([], 'sum0', 'sum_ i e. (/) ( 2 ^ i ) = 0')
        w.qed([v2, s, s0], '3eqtri', '( toNat ` (/) ) = 0'); w.run()

    # ---- the lowest digit and the half of ( bToNat B ) + 2 M
    AB = '( B e. 2o /\\ M e. ZZ )'
    S = '( ( bToNat ` B ) + ( 2 x. M ) )'
    if want('bwbit0'):
        w = W('bwbit0', 'The lowest binary digit of bToNat B + 2 M is B.')
        b = w.s([], 'simpl', '( %s -> B e. 2o )' % AB); m = w.s([], 'simpr', '( %s -> M e. ZZ )' % AB)
        concl = '( 0 e. ( bits ` %s ) <-> B = 1o )' % S

        def body(a2, eq, v):
            m2 = w.s([m], 'adantr', '( %s -> M e. ZZ )' % a2)
            f = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` B ) = ( bToNat ` %s ) )' % (a2, v))
            c = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, '1' if v == '1o' else '0'))
            f2 = w.s([f, c], 'eqtrdi', '( %s -> ( bToNat ` B ) = %s )' % (a2, '1' if v == '1o' else '0'))
            o = w.s([f2], 'oveq1d', '( %s -> %s = ( %s + ( 2 x. M ) ) )' % (a2, S, '1' if v == '1o' else '0'))
            mc = Cl(w, a2, {'M': ('ZZ', m2)}).mem('( 2 x. M )', 'CC')
            if v == '1o':
                oc = w.s([], '1cnd', '( %s -> 1 e. CC )' % a2)
                ac = w.s([oc, mc], 'addcomd', '( %s -> ( 1 + ( 2 x. M ) ) = ( ( 2 x. M ) + 1 ) )' % a2)
                o2 = w.s([o, ac], 'eqtrd', '( %s -> %s = ( ( 2 x. M ) + 1 ) )' % (a2, S))
                e = w.s([o2], 'fveq2d', '( %s -> ( bits ` %s ) = ( bits ` ( ( 2 x. M ) + 1 ) ) )' % (a2, S))
                el = w.s([e], 'eleq2d', '( %s -> ( 0 e. ( bits ` %s ) <-> 0 e. ( bits ` ( ( 2 x. M ) + 1 ) ) ) )' % (a2, S))
                bo = w.s([m2, w.inst('bits0o')], 'syl', '( %s -> 0 e. ( bits ` ( ( 2 x. M ) + 1 ) ) )' % a2)
                lhs = w.s([bo, el], 'mpbird', '( %s -> 0 e. ( bits ` %s ) )' % (a2, S))
                return w.s([lhs, eq], '2thd', '( %s -> %s )' % (a2, concl))
            ac = w.s([mc], 'addlidd', '( %s -> ( 0 + ( 2 x. M ) ) = ( 2 x. M ) )' % a2)
            o2 = w.s([o, ac], 'eqtrd', '( %s -> %s = ( 2 x. M ) )' % (a2, S))
            e = w.s([o2], 'fveq2d', '( %s -> ( bits ` %s ) = ( bits ` ( 2 x. M ) ) )' % (a2, S))
            el = w.s([e], 'eleq2d', '( %s -> ( 0 e. ( bits ` %s ) <-> 0 e. ( bits ` ( 2 x. M ) ) ) )' % (a2, S))
            be = w.s([m2, w.inst('bits0e')], 'syl', '( %s -> -. 0 e. ( bits ` ( 2 x. M ) ) )' % a2)
            lhs = w.s([be, el], 'mtbird', '( %s -> -. 0 e. ( bits ` %s ) )' % (a2, S))
            n1 = w.s([], '1n0', '1o =/= (/)'); n2 = w.s([n1], 'nesymi', '-. (/) = 1o'); n2d = w.s([n2], 'a1i', '( %s -> -. (/) = 1o )' % a2)
            r = w.s([eq], 'eqeq1d', '( %s -> ( B = 1o <-> (/) = 1o ) )' % a2)
            rhs = w.s([n2d, r], 'mtbird', '( %s -> -. B = 1o )' % a2)
            return w.s([lhs, rhs], '2falsed', '( %s -> %s )' % (a2, concl))
        st = cases2o(w, AB, 'B', b, body, concl); promote(w, st); w.run()

    if want('bwflhalf'):
        w = W('bwflhalf', 'The integer half of bToNat B + 2 M is M.')
        b = w.s([], 'simpl', '( %s -> B e. 2o )' % AB); m = w.s([], 'simpr', '( %s -> M e. ZZ )' % AB)
        concl = '( |_ ` ( %s / 2 ) ) = M' % S

        def body(a2, eq, v):
            m2 = w.s([m], 'adantr', '( %s -> M e. ZZ )' % a2)
            cl = Cl(w, a2, {'M': ('ZZ', m2)})
            f = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` B ) = ( bToNat ` %s ) )' % (a2, v))
            lit = '1' if v == '1o' else '0'
            c = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, lit))
            f2 = w.s([f, c], 'eqtrdi', '( %s -> ( bToNat ` B ) = %s )' % (a2, lit))
            o = w.s([f2], 'oveq1d', '( %s -> %s = ( %s + ( 2 x. M ) ) )' % (a2, S, lit))
            od = w.s([o], 'oveq1d', '( %s -> ( %s / 2 ) = ( ( %s + ( 2 x. M ) ) / 2 ) )' % (a2, S, lit))
            if v == '1o':
                from lin import lineq
                ac = lineq(w, a2, '( ( 1 + ( 2 x. M ) ) / 2 )', '( M + ( 1 / 2 ) )', closure=cl)
                od2 = w.s([od, ac], 'eqtrd', '( %s -> ( %s / 2 ) = ( M + ( 1 / 2 ) ) )' % (a2, S))
                fl = w.s([od2], 'fveq2d', '( %s -> ( |_ ` ( %s / 2 ) ) = ( |_ ` ( M + ( 1 / 2 ) ) ) )' % (a2, S))
                on = w.s([], '1nn0', '1 e. NN0'); ond = w.s([on], 'a1i', '( %s -> 1 e. NN0 )' % a2)
                tn = w.s([], '2nn', '2 e. NN'); tnd = w.s([tn], 'a1i', '( %s -> 2 e. NN )' % a2)
                ad = w.s([m2, ond, tnd, w.inst('adddivflid')], 'syl3anc', '( %s -> ( 1 < 2 <-> ( |_ ` ( M + ( 1 / 2 ) ) ) = M ) )' % a2)
                lt = w.s([], '1lt2', '1 < 2'); ltd = w.s([lt], 'a1i', '( %s -> 1 < 2 )' % a2)
                fl2 = w.s([ltd, ad], 'mpbid', '( %s -> ( |_ ` ( M + ( 1 / 2 ) ) ) = M )' % a2)
                return w.s([fl, fl2], 'eqtrd', '( %s -> %s )' % (a2, concl))
            mc = cl.mem('( 2 x. M )', 'CC')
            ac = w.s([mc], 'addlidd', '( %s -> ( 0 + ( 2 x. M ) ) = ( 2 x. M ) )' % a2)
            ac2 = w.s([ac], 'oveq1d', '( %s -> ( ( 0 + ( 2 x. M ) ) / 2 ) = ( ( 2 x. M ) / 2 ) )' % a2)
            m2c = cl.mem('M', 'CC'); tc = w.s([], '2cnd', '( %s -> 2 e. CC )' % a2); tne = w.s([], '2ne0', '2 =/= 0'); tned = w.s([tne], 'a1i', '( %s -> 2 =/= 0 )' % a2)
            dc = w.s([m2c, tc, tned, w.inst('divcan3')], 'syl3anc', '( %s -> ( ( 2 x. M ) / 2 ) = M )' % a2)
            od2 = w.s([od, ac2, dc], '3eqtrd', '( %s -> ( %s / 2 ) = M )' % (a2, S))
            fl = w.s([od2], 'fveq2d', '( %s -> ( |_ ` ( %s / 2 ) ) = ( |_ ` M ) )' % (a2, S))
            fi = w.s([m2, w.inst('flid')], 'syl', '( %s -> ( |_ ` M ) = M )' % a2)
            return w.s([fl, fi], 'eqtrd', '( %s -> %s )' % (a2, concl))
        st = cases2o(w, AB, 'B', b, body, concl); promote(w, st); w.run()

    # ---- tonatcons
    if want('tonatcons'):
        A = '( B e. 2o /\\ L e. Word 2o )'
        w = W('tonatcons', 'The value of a bit word with a letter prepended (Lean: toNat (b :: l) = b.toNat + 2 * toNat l).')
        b = w.s([], 'simpl', '( %s -> B e. 2o )' % A); l = w.s([], 'simpr', '( %s -> L e. Word 2o )' % A)
        cl = Cl(w, A, {'B': ('2o', b), 'L': ('Word 2o', l)})
        T = TN('L'); Sx = '( ( bToNat ` B ) + ( 2 x. %s ) )' % T
        K = LEN('L'); K1 = '( %s + 1 )' % K
        tz = cl.mem(T, 'ZZ'); tn = cl.mem(T, 'NN0'); kn = cl.mem(K, 'NN0')
        sz = cl.mem(Sx, 'ZZ'); sn = cl.mem(Sx, 'NN0')
        # cons = ( Sx bwrd ( K + 1 ) )
        bc = w.s([sz, kn, w.inst('bwrdcons')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (A, BWRD(Sx, K1), BIT(Sx, '0'), BWRD('( |_ ` ( %s / 2 ) )' % Sx, K)))
        b0 = w.s([b, tz, w.inst('bwbit0')], 'syl2anc', '( %s -> ( 0 e. ( bits ` %s ) <-> B = 1o ) )' % (A, Sx))
        # BIT(Sx,0) = B
        a1 = '( %s /\\ B = 1o )' % A
        h1 = w.s([], 'simpr', '( %s -> B = 1o )' % a1); b01 = w.s([b0], 'adantr', '( %s -> ( 0 e. ( bits ` %s ) <-> B = 1o ) )' % (a1, Sx))
        t1 = w.s([h1, b01], 'mpbird', '( %s -> 0 e. ( bits ` %s ) )' % (a1, Sx)); i1 = w.s([t1], 'iftrued', '( %s -> %s = 1o )' % (a1, BIT(Sx, '0')))
        c1 = w.s([i1, h1], 'eqtr4d', '( %s -> %s = B )' % (a1, BIT(Sx, '0')))
        a2 = '( %s /\\ -. B = 1o )' % A
        h2 = w.s([], 'simpr', '( %s -> -. B = 1o )' % a2); b02 = w.s([b0], 'adantr', '( %s -> ( 0 e. ( bits ` %s ) <-> B = 1o ) )' % (a2, Sx))
        t2 = w.s([h2, b02], 'mtbird', '( %s -> -. 0 e. ( bits ` %s ) )' % (a2, Sx)); i2 = w.s([t2], 'iffalsed', '( %s -> %s = (/) )' % (a2, BIT(Sx, '0')))
        b2 = w.s([b], 'adantr', '( %s -> B e. 2o )' % a2)
        n2 = w.s([b2, w.inst('bwel2on')], 'syl', '( %s -> ( -. B = 1o <-> B = (/) ) )' % a2); z2 = w.s([h2, n2], 'mpbid', '( %s -> B = (/) )' % a2)
        c2 = w.s([i2, z2], 'eqtr4d', '( %s -> %s = B )' % (a2, BIT(Sx, '0')))
        bitB = w.s([c1, c2], 'pm2.61dan', '( %s -> %s = B )' % (A, BIT(Sx, '0')))
        s1e = w.s([bitB], 's1eqd', '( %s -> <" %s "> = <" B "> )' % (A, BIT(Sx, '0')))
        fh = w.s([b, tz, w.inst('bwflhalf')], 'syl2anc', '( %s -> ( |_ ` ( %s / 2 ) ) = %s )' % (A, Sx, T))
        fh2 = w.s([fh], 'oveq1d', '( %s -> %s = %s )' % (A, BWRD('( |_ ` ( %s / 2 ) )' % Sx, K), BWRD(T, K)))
        ew = w.s([l, w.inst('bweqwrd')], 'syl', '( %s -> L = %s )' % (A, BWRD(T, K)))
        fh3 = w.s([fh2, ew], 'eqtr4d', '( %s -> %s = L )' % (A, BWRD('( |_ ` ( %s / 2 ) )' % Sx, K)))
        cc = w.s([s1e, fh3], 'oveq12d', '( %s -> ( <" %s "> ++ %s ) = ( <" B "> ++ L ) )' % (A, BIT(Sx, '0'), BWRD('( |_ ` ( %s / 2 ) )' % Sx, K)))
        ceq = w.s([bc, cc], 'eqtr2d', '( %s -> ( <" B "> ++ L ) = %s )' % (A, BWRD(Sx, K1)))
        tv = w.s([ceq], 'fveq2d', '( %s -> ( toNat ` ( <" B "> ++ L ) ) = ( toNat ` %s ) )' % (A, BWRD(Sx, K1)))
        # Sx < 2 ^ ( K + 1 )
        k1n = cl.mem(K1, 'NN0')
        lt = w.s([l, w.inst('tonatlt')], 'syl', '( %s -> %s < ( 2 ^ %s ) )' % (A, T, K))
        le1 = w.s([b, w.inst('bwbnle1')], 'syl', '( %s -> ( bToNat ` B ) <_ 1 )' % A)
        pk = cl.mem('( 2 ^ %s )' % K, 'RR'); tc = w.s([], '2cnd', '( %s -> 2 e. CC )' % A)
        ep = w.s([tc, kn, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ %s ) = ( ( 2 ^ %s ) x. 2 ) )' % (A, K1, K))
        from lin import linarith
        cl.leaf('( 2 ^ %s )' % K, 'RR', pk)
        cl.have('( bToNat ` B )', 'NN0', cl.mem('( bToNat ` B )', 'NN0'))
        cl.leaf('( 2 ^ %s )' % K1, 'RR', cl.mem('( 2 ^ %s )' % K1, 'RR'))
        pkz = cl.mem('( 2 ^ %s )' % K, 'ZZ')
        zl = w.s([tz, pkz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < ( 2 ^ %s ) <-> ( %s + 1 ) <_ ( 2 ^ %s ) ) )' % (A, T, K, T, K))
        tp1 = w.s([lt, zl], 'mpbid', '( %s -> ( %s + 1 ) <_ ( 2 ^ %s ) )' % (A, T, K))
        ltS = linarith(w, A, [tp1, le1, ep], '%s < ( 2 ^ %s )' % (Sx, K1), closure=cl)
        tb = w.s([sn, k1n, ltS, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (A, BWRD(Sx, K1), Sx))
        w.qed([tv, tb], 'eqtrd', '( %s -> ( toNat ` ( <" B "> ++ L ) ) = %s )' % (A, Sx)); w.run()
