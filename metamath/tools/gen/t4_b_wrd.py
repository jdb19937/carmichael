"""Sortie T4, group B: the digits word bwrd (T4-blueprint section 3.2)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AN = '( N e. ZZ /\\ M e. NN0 )'
MPT = lambda N, M: '( i e. ( 0 ..^ %s ) |-> %s )' % (M, BIT(N, 'i'))


def base(w, ante=AN):
    lv = conj_leaves(w, ante, [('N', 'ZZ'), ('M', 'NN0')])
    return Cl(w, ante, lv)


if __name__ == '__main__':
    if want('bwrdval'):
        w = W('bwrdval', 'Value of bwrd: the word of the M low binary digits of N, least significant first.')
        cl = base(w)
        st, val = defval(w, cl, 'df-bwrd', 'bwrd', ['N', 'M'])
        assert val == MPT('N', 'M'), val
        promote(w, st); w.run()

    if want('bwrdf'):
        w = W('bwrdf', 'The digits word is a function on the positions into the Booleans.')
        cl = base(w)
        v = w.s([], 'bwrdval', '( %s -> ( N bwrd M ) = %s )' % (AN, MPT('N', 'M')))
        a2 = '( %s /\\ i e. ( 0 ..^ M ) )' % AN
        c2 = Cl(w, a2, {})
        m = c2.mem(BIT('N', 'i'), '2o')
        e = w.s([], 'eqid', '%s = %s' % (MPT('N', 'M'), MPT('N', 'M')))
        f = w.s([m, e], 'fmptd', '( %s -> %s : ( 0 ..^ M ) --> 2o )' % (AN, MPT('N', 'M')))
        bi = w.s([v], 'feq1d', '( %s -> ( ( N bwrd M ) : ( 0 ..^ M ) --> 2o <-> %s : ( 0 ..^ M ) --> 2o ) )' % (AN, MPT('N', 'M')))
        w.qed([f, bi], 'mpbird', '( %s -> ( N bwrd M ) : ( 0 ..^ M ) --> 2o )' % AN); w.run()

    if want('bwrdcl'):
        w = W('bwrdcl', 'Closure of bwrd: a word over the Booleans.')
        f = w.s([], 'bwrdf', '( %s -> ( N bwrd M ) : ( 0 ..^ M ) --> 2o )' % AN)
        i = w.inst('iswrdi'); w.qed([f, i], 'syl', '( %s -> ( N bwrd M ) e. Word 2o )' % AN); w.run()

    if want('bwrdlen'):
        w = W('bwrdlen', 'The length of the digits word is the number of digits asked for.')
        f = w.s([], 'bwrdf', '( %s -> ( N bwrd M ) : ( 0 ..^ M ) --> 2o )' % AN)
        i = w.inst('ffn'); fn = w.s([f, i], 'syl', '( %s -> ( N bwrd M ) Fn ( 0 ..^ M ) )' % AN)
        h = w.inst('hashfn'); h1 = w.s([fn, h], 'syl', '( %s -> ( # ` ( N bwrd M ) ) = ( # ` ( 0 ..^ M ) ) )' % AN)
        m = w.s([], 'simpr', '( %s -> M e. NN0 )' % AN)
        h2i = w.inst('hashfzo0'); h2 = w.s([m, h2i], 'syl', '( %s -> ( # ` ( 0 ..^ M ) ) = M )' % AN)
        w.qed([h1, h2], 'eqtrd', '( %s -> ( # ` ( N bwrd M ) ) = M )' % AN); w.run()

    A3 = '( N e. ZZ /\\ M e. NN0 /\\ I e. ( 0 ..^ M ) )'
    if want('bwrdfv'):
        w = W('bwrdfv', 'The I-th letter of the digits word is the I-th binary digit of N as a Boolean.')
        n = w.s([], 'simp1', '( %s -> N e. ZZ )' % A3); m = w.s([], 'simp2', '( %s -> M e. NN0 )' % A3)
        ii = w.s([], 'simp3', '( %s -> I e. ( 0 ..^ M ) )' % A3)
        vi = w.inst('bwrdval'); v = w.s([n, m, vi], 'syl2anc', '( %s -> ( N bwrd M ) = %s )' % (A3, MPT('N', 'M')))
        cl = Cl(w, A3, {'I': ('( 0 ..^ M )', ii)})
        f1 = w.s([v], 'fveq1d', '( %s -> ( ( N bwrd M ) ` I ) = ( %s ` I ) )' % (A3, MPT('N', 'M')))
        st, val = mptfv(w, cl, MPT('N', 'M'), 'I')
        assert val == BIT('N', 'I'), val
        w.qed([f1, st], 'eqtrd', '( %s -> ( ( N bwrd M ) ` I ) = %s )' % (A3, BIT('N', 'I'))); w.run()

    if want('bwrd0'):
        w = W('bwrd0', 'The digits word of length 0 is empty.')
        A = 'N e. ZZ'
        z = w.s([], '0nn0', '0 e. NN0'); zd = w.s([z], 'a1i', '( %s -> 0 e. NN0 )' % A)
        i = w.s([], 'id', '( %s -> N e. ZZ )' % A)
        vi = w.inst('bwrdval'); v = w.s([i, zd, vi], 'syl2anc', '( %s -> ( N bwrd 0 ) = %s )' % (A, MPT('N', '0')))
        f0 = w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')
        m = w.s([f0], 'mpteq1i', '%s = ( i e. (/) |-> %s )' % (MPT('N', '0'), BIT('N', 'i')))
        m0 = w.s([], 'mpt0', '( i e. (/) |-> %s ) = (/)' % BIT('N', 'i'))
        m2 = w.s([m, m0], 'eqtri', '%s = (/)' % MPT('N', '0'))
        w.qed([v, m2], 'eqtrdi', '( %s -> ( N bwrd 0 ) = (/) )' % A); w.run()

    # ---- bwrdp1: the snoc form
    if want('bwrdp1'):
        w = W('bwrdp1', 'One more digit: the digits word of length M + 1 is the one of length M followed by the M-th digit.')
        cl = base(w)
        L = BWRD('N', '( M + 1 )'); R = '( ( N bwrd M ) ++ <" %s "> )' % BIT('N', 'M')
        m1 = cl.mem('( M + 1 )', 'NN0')
        clL = cl.mem(L, 'Word 2o'); clM = cl.mem(BWRD('N', 'M'), 'Word 2o'); clR = cl.mem(R, 'Word 2o')
        # lengths
        l1i = w.inst('bwrdlen'); l1 = w.s([cl.mem('N', 'ZZ'), m1, l1i], 'syl2anc', '( %s -> ( # ` %s ) = ( M + 1 ) )' % (AN, L))
        lM = w.s([cl.mem('N', 'ZZ'), cl.mem('M', 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = M )' % (AN, BWRD('N', 'M')))
        cc = w.inst('ccatlen'); l2 = w.s([clM, cl.mem('<" %s ">' % BIT('N', 'M'), 'Word 2o'), cc], 'syl2anc',
                                        '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` <" %s "> ) ) )' % (AN, R, BWRD('N', 'M'), BIT('N', 'M')))
        s1 = w.s([], 's1len', '( # ` <" %s "> ) = 1' % BIT('N', 'M'))
        s1d = w.s([s1], 'a1i', '( %s -> ( # ` <" %s "> ) = 1 )' % (AN, BIT('N', 'M')))
        ad = w.s([lM, s1d], 'oveq12d', '( %s -> ( ( # ` %s ) + ( # ` <" %s "> ) ) = ( M + 1 ) )' % (AN, BWRD('N', 'M'), BIT('N', 'M')))
        l2b = w.s([l2, ad], 'eqtrd', '( %s -> ( # ` %s ) = ( M + 1 ) )' % (AN, R))
        leneq = w.s([l1, l2b], 'eqtr4d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AN, L, R))

        def letter(a2, ist):
            # ist: ( a2 -> i e. ( 0 ..^ ( # ` L ) ) )
            l1b = w.s([l1], 'adantr', '( %s -> ( # ` %s ) = ( M + 1 ) )' % (a2, L))
            o = w.s([l1b], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ ( M + 1 ) ) )' % (a2, L))
            i1 = w.s([ist, o], 'eleqtrd', '( %s -> i e. ( 0 ..^ ( M + 1 ) ) )' % a2)
            nz = w.s([cl.mem('N', 'ZZ')], 'adantr', '( %s -> N e. ZZ )' % a2)
            m1b = w.s([m1], 'adantr', '( %s -> ( M + 1 ) e. NN0 )' % a2)
            fv = w.inst('bwrdfv'); lhs = w.s([nz, m1b, i1, fv], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, L, BIT('N', 'i')))
            mn = w.s([cl.mem('M', 'NN0')], 'adantr', '( %s -> M e. NN0 )' % a2)
            uz = nn0uz(w, a2, mn, 'M')
            sp = w.inst('fzosplitsni'); spl = w.s([uz, sp], 'syl', '( %s -> ( i e. ( 0 ..^ ( M + 1 ) ) <-> ( i e. ( 0 ..^ M ) \\/ i = M ) ) )' % a2)
            dj = w.s([i1, spl], 'mpbid', '( %s -> ( i e. ( 0 ..^ M ) \\/ i = M ) )' % a2)
            # case i e. ( 0 ..^ M )
            a3 = '( %s /\\ i e. ( 0 ..^ M ) )' % a2
            h3 = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ M ) )' % a3)
            clM3 = lift(w, clM, a3)
            lM3 = lift(w, lM, a3)
            i3 = lenrw(w, a3, BWRD('N', 'M'), lM3, h3)
            cv = w.inst('ccats1val1'); r3 = w.s([clM3, i3, cv], 'syl2anc', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a3, R, BWRD('N', 'M')))
            nz3 = w.s([nz], 'adantr', '( %s -> N e. ZZ )' % a3); mn3 = w.s([mn], 'adantr', '( %s -> M e. NN0 )' % a3)
            fv3 = w.inst('bwrdfv'); r3b = w.s([nz3, mn3, h3, fv3], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a3, BWRD('N', 'M'), BIT('N', 'i')))
            r3c = w.s([r3, r3b], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (a3, R, BIT('N', 'i')))
            lhs3 = w.s([lhs], 'adantr', '( %s -> ( %s ` i ) = %s )' % (a3, L, BIT('N', 'i')))
            c3 = w.s([lhs3, r3c], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a3, L, R))
            # case i = M
            a4 = '( %s /\\ i = M )' % a2
            h4 = w.s([], 'simpr', '( %s -> i = M )' % a4)
            clM4 = lift(w, clM, a4)
            bm = Cl(w, a4, {}).mem(BIT('N', 'M'), '2o')
            lM4 = lift(w, lM, a4)
            e4 = w.s([h4, lM4], 'eqtr4d', '( %s -> i = ( # ` %s ) )' % (a4, BWRD('N', 'M')))
            cv2 = w.inst('ccats1val2'); r4 = w.s([clM4, bm, e4, cv2], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a4, R, BIT('N', 'M')))
            lhs4 = w.s([lhs], 'adantr', '( %s -> ( %s ` i ) = %s )' % (a4, L, BIT('N', 'i')))
            bc = bitcongr(w, a4, h4, 'N', 'i', 'M')
            lhs4b = w.s([lhs4, bc], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (a4, L, BIT('N', 'M')))
            c4 = w.s([lhs4b, r4], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a4, L, R))
            return w.s([c3, c4, dj], 'mpjaodan', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a2, L, R))
        wrdeq(w, AN, L, R, clL, clR, leneq, letter, name='qed'); w.run()

    # ---- bwrdcons: the cons form
    if want('bwrdcons'):
        w = W('bwrdcons', 'One more digit, at the bottom: the digits word of length M + 1 is the lowest digit of N followed by the digits word of N / 2.')
        cl = base(w)
        H = '( |_ ` ( N / 2 ) )'
        L = BWRD('N', '( M + 1 )'); R = '( <" %s "> ++ %s )' % (BIT('N', '0'), BWRD(H, 'M'))
        m1 = cl.mem('( M + 1 )', 'NN0')
        hz = cl.mem(H, 'ZZ')
        clL = cl.mem(L, 'Word 2o'); clH = cl.mem(BWRD(H, 'M'), 'Word 2o'); clR = cl.mem(R, 'Word 2o')
        b0 = cl.mem(BIT('N', '0'), '2o'); cls1 = cl.mem('<" %s ">' % BIT('N', '0'), 'Word 2o')
        l1 = w.s([cl.mem('N', 'ZZ'), m1, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( M + 1 ) )' % (AN, L))
        lH = w.s([hz, cl.mem('M', 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = M )' % (AN, BWRD(H, 'M')))
        l2 = w.s([cls1, clH, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" %s "> ) + ( # ` %s ) ) )' % (AN, R, BIT('N', '0'), BWRD(H, 'M')))
        s1 = w.s([], 's1len', '( # ` <" %s "> ) = 1' % BIT('N', '0')); s1d = w.s([s1], 'a1i', '( %s -> ( # ` <" %s "> ) = 1 )' % (AN, BIT('N', '0')))
        ad = w.s([s1d, lH], 'oveq12d', '( %s -> ( ( # ` <" %s "> ) + ( # ` %s ) ) = ( 1 + M ) )' % (AN, BIT('N', '0'), BWRD(H, 'M')))
        mc = cl.mem('M', 'CC'); ac = w.s([], '1cnd', '( %s -> 1 e. CC )' % AN)
        com = w.s([ac, mc], 'addcomd', '( %s -> ( 1 + M ) = ( M + 1 ) )' % AN)
        l2b = w.s([l2, ad, com], '3eqtrd', '( %s -> ( # ` %s ) = ( M + 1 ) )' % (AN, R))
        leneq = w.s([l1, l2b], 'eqtr4d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AN, L, R))

        def letter(a2, ist):
            l1b = w.s([l1], 'adantr', '( %s -> ( # ` %s ) = ( M + 1 ) )' % (a2, L))
            o = w.s([l1b], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ ( M + 1 ) ) )' % (a2, L))
            i1 = w.s([ist, o], 'eleqtrd', '( %s -> i e. ( 0 ..^ ( M + 1 ) ) )' % a2)
            nz = w.s([cl.mem('N', 'ZZ')], 'adantr', '( %s -> N e. ZZ )' % a2)
            m1b = w.s([m1], 'adantr', '( %s -> ( M + 1 ) e. NN0 )' % a2)
            lhs = w.s([nz, m1b, i1, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, L, BIT('N', 'i')))
            # split: i = 0 or i e. ( 1 ..^ ( M + 1 ) )
            inn = w.s([i1, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % a2)
            ez = w.s([inn, w.inst('elnn0')], 'sylib', '( %s -> ( i e. NN \\/ i = 0 ) )' % a2)
            # case i = 0
            a4 = '( %s /\\ i = 0 )' % a2
            h4 = w.s([], 'simpr', '( %s -> i = 0 )' % a4)
            lhs4 = w.s([lhs], 'adantr', '( %s -> ( %s ` i ) = %s )' % (a4, L, BIT('N', 'i')))
            bc = bitcongr(w, a4, h4, 'N', 'i', '0')
            lhs4b = w.s([lhs4, bc], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (a4, L, BIT('N', '0')))
            f0 = w.s([h4], 'fveq2d', '( %s -> ( %s ` i ) = ( %s ` 0 ) )' % (a4, R, R))
            cls14 = lift(w, cls1, a4)
            clH4 = lift(w, clH, a4)
            z1 = w.s([], 'lbfzo0', '( 0 e. ( 0 ..^ 1 ) <-> 1 e. NN )'); on = w.s([], '1nn', '1 e. NN')
            z2 = w.s([on, z1], 'mpbir', '0 e. ( 0 ..^ 1 )')
            s1b = w.s([], 's1len', '( # ` <" %s "> ) = 1' % BIT('N', '0'))
            s1o = w.s([s1b], 'oveq2i', '( 0 ..^ ( # ` <" %s "> ) ) = ( 0 ..^ 1 )' % BIT('N', '0'))
            z3 = w.s([z2, s1o], 'eleqtrri', '0 e. ( 0 ..^ ( # ` <" %s "> ) )' % BIT('N', '0'))
            z3d = w.s([z3], 'a1i', '( %s -> 0 e. ( 0 ..^ ( # ` <" %s "> ) ) )' % (a4, BIT('N', '0')))
            cv = w.s([cls14, clH4, z3d, w.inst('ccatval1')], 'syl3anc', '( %s -> ( %s ` 0 ) = ( <" %s "> ` 0 ) )' % (a4, R, BIT('N', '0')))
            b04 = lift(w, b0, a4)
            sf = w.s([b04, w.inst('s1fv')], 'syl', '( %s -> ( <" %s "> ` 0 ) = %s )' % (a4, BIT('N', '0'), BIT('N', '0')))
            r4 = w.s([f0, cv, sf], '3eqtrd', '( %s -> ( %s ` i ) = %s )' % (a4, R, BIT('N', '0')))
            c4 = w.s([lhs4b, r4], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a4, L, R))
            # case i e. NN
            a3 = '( %s /\\ i e. NN )' % a2
            h3 = w.s([], 'simpr', '( %s -> i e. NN )' % a3)
            c3cl = Cl(w, a3, {'i': ('NN', h3), 'N': ('ZZ', w.s([nz], 'adantr', '( %s -> N e. ZZ )' % a3)),
                              'M': ('NN0', lift(w, cl.mem('M', 'NN0'), a3))})
            i1b = w.s([i1], 'adantr', '( %s -> i e. ( 0 ..^ ( M + 1 ) ) )' % a3)
            lt = w.s([i1b, w.inst('elfzolt2')], 'syl', '( %s -> i < ( M + 1 ) )' % a3)
            # i e. ( 1 ..^ ( 1 + M ) )
            iz = c3cl.mem('i', 'ZZ'); mz = c3cl.mem('M', 'ZZ')
            ir = c3cl.mem('i', 'RR'); mr = c3cl.mem('M', 'RR'); onr = w.s([], '1red', '( %s -> 1 e. RR )' % a3)
            onc3 = w.s([], '1cnd', '( %s -> 1 e. CC )' % a3); mc3 = c3cl.mem('M', 'CC'); com3 = w.s([onc3, mc3], 'addcomd', '( %s -> ( 1 + M ) = ( M + 1 ) )' % a3)
            lt2 = w.s([lt, com3], 'breqtrrd', '( %s -> i < ( 1 + M ) )' % a3)
            ge1 = w.s([h3, w.inst('nnge1')], 'syl', '( %s -> 1 <_ i )' % a3)
            onz = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % a3)
            pm = c3cl.mem('( 1 + M )', 'ZZ')
            elf = w.s([iz, onz, pm, w.inst('elfzo')], 'syl3anc', '( %s -> ( i e. ( 1 ..^ ( 1 + M ) ) <-> ( 1 <_ i /\\ i < ( 1 + M ) ) ) )' % a3)
            j = w.s([ge1, lt2], 'jca', '( %s -> ( 1 <_ i /\\ i < ( 1 + M ) ) )' % a3)
            i3 = w.s([j, elf], 'mpbird', '( %s -> i e. ( 1 ..^ ( 1 + M ) ) )' % a3)
            # rewrite the range as ( ( # ` s1 ) ..^ ( ( # ` s1 ) + ( # ` H ) ) )
            s1c = w.s([s1b], 'a1i', '( %s -> ( # ` <" %s "> ) = 1 )' % (a3, BIT('N', '0')))
            lH3 = lift(w, lH, a3)
            sm = w.s([s1c, lH3], 'oveq12d', '( %s -> ( ( # ` <" %s "> ) + ( # ` %s ) ) = ( 1 + M ) )' % (a3, BIT('N', '0'), BWRD(H, 'M')))
            rg = w.s([s1c, sm], 'oveq12d', '( %s -> ( ( # ` <" %s "> ) ..^ ( ( # ` <" %s "> ) + ( # ` %s ) ) ) = ( 1 ..^ ( 1 + M ) ) )' % (a3, BIT('N', '0'), BIT('N', '0'), BWRD(H, 'M')))
            i3b = w.s([i3, rg], 'eleqtrrd', '( %s -> i e. ( ( # ` <" %s "> ) ..^ ( ( # ` <" %s "> ) + ( # ` %s ) ) ) )' % (a3, BIT('N', '0'), BIT('N', '0'), BWRD(H, 'M')))
            cls13 = lift(w, cls1, a3)
            clH3 = lift(w, clH, a3)
            cv2 = w.s([cls13, clH3, i3b, w.inst('ccatval2')], 'syl3anc', '( %s -> ( %s ` i ) = ( %s ` ( i - ( # ` <" %s "> ) ) ) )' % (a3, R, BWRD(H, 'M'), BIT('N', '0')))
            sub1 = w.s([s1c], 'oveq2d', '( %s -> ( i - ( # ` <" %s "> ) ) = ( i - 1 ) )' % (a3, BIT('N', '0')))
            f2 = w.s([sub1], 'fveq2d', '( %s -> ( %s ` ( i - ( # ` <" %s "> ) ) ) = ( %s ` ( i - 1 ) ) )' % (a3, BWRD(H, 'M'), BIT('N', '0'), BWRD(H, 'M')))
            # ( i - 1 ) e. ( 0 ..^ M )
            im1 = w.s([h3, w.inst('nnm1nn0')], 'syl', '( %s -> ( i - 1 ) e. NN0 )' % a3)
            ic = c3cl.mem('i', 'CC'); onc = w.s([], '1cnd', '( %s -> 1 e. CC )' % a3)
            lt3 = w.s([ir, onr, mr, w.inst('ltsubadd')], 'syl3anc', '( %s -> ( ( i - 1 ) < M <-> i < ( M + 1 ) ) )' % a3)
            lt4 = w.s([lt, lt3], 'mpbird', '( %s -> ( i - 1 ) < M )' % a3)
            mnn0 = c3cl.mem('M', 'NN0')
            elf2 = w.s([im1, mz, lt4, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> ( i - 1 ) e. ( 0 ..^ M ) )' % a3)
            hz3 = lift(w, hz, a3)
            fvH = w.s([hz3, mnn0, elf2, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` ( i - 1 ) ) = %s )' % (a3, BWRD(H, 'M'), BIT(H, '( i - 1 )')))
            r3 = w.s([cv2, f2, fvH], '3eqtrd', '( %s -> ( %s ` i ) = %s )' % (a3, R, BIT(H, '( i - 1 )')))
            # bitsp1: ( ( i - 1 ) + 1 ) e. bits N <-> ( i - 1 ) e. bits H
            nz3 = c3cl.mem('N', 'ZZ')
            bp = w.s([nz3, im1, w.inst('bitsp1')], 'syl2anc', '( %s -> ( ( ( i - 1 ) + 1 ) e. ( bits ` N ) <-> ( i - 1 ) e. ( bits ` %s ) ) )' % (a3, H))
            npc = w.s([ic, onc], 'npcand', '( %s -> ( ( i - 1 ) + 1 ) = i )' % a3)
            e1 = w.s([npc], 'eleq1d', '( %s -> ( ( ( i - 1 ) + 1 ) e. ( bits ` N ) <-> i e. ( bits ` N ) ) )' % a3)
            bi = w.s([e1, bp], 'bitr3d', '( %s -> ( i e. ( bits ` N ) <-> ( i - 1 ) e. ( bits ` %s ) ) )' % (a3, H))
            ifb = w.s([bi], 'ifbid', '( %s -> %s = %s )' % (a3, BIT('N', 'i'), BIT(H, '( i - 1 )')))
            lhs3 = w.s([lhs], 'adantr', '( %s -> ( %s ` i ) = %s )' % (a3, L, BIT('N', 'i')))
            lhs3b = w.s([lhs3, ifb], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (a3, L, BIT(H, '( i - 1 )')))
            c3 = w.s([lhs3b, r3], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a3, L, R))
            return w.s([c3, c4, ez], 'mpjaodan', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a2, L, R))
        wrdeq(w, AN, L, R, clL, clR, leneq, letter, name='qed'); w.run()

    # ---- bwrdmod: the digits below M of N mod 2^K, K >= M
    if want('bwrdmod'):
        A = '( N e. ZZ /\\ M e. NN0 /\\ K e. ( ZZ>= ` M ) )'
        w = W('bwrdmod', 'The low digits of a residue modulo a higher power of two are those of the number.')
        n = w.s([], 'simp1', '( %s -> N e. ZZ )' % A); m = w.s([], 'simp2', '( %s -> M e. NN0 )' % A); k = w.s([], 'simp3', '( %s -> K e. ( ZZ>= ` M ) )' % A)
        cl = Cl(w, A, {'N': ('ZZ', n), 'M': ('NN0', m)})
        kz = w.s([k, w.inst('eluzelz')], 'syl', '( %s -> K e. ZZ )' % A)
        kn = w.s([m, k, w.inst('eluznn0')], 'syl2anc', '( %s -> K e. NN0 )' % A)
        cl.have('K', 'NN0', kn)
        NM = MOD2('N', 'K')
        nm = cl.mem(NM, 'ZZ')
        L = BWRD(NM, 'M'); R = BWRD('N', 'M')
        clL = cl.mem(L, 'Word 2o'); clR = cl.mem(R, 'Word 2o')
        l1 = w.s([nm, m, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = M )' % (A, L))
        l2 = w.s([n, m, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = M )' % (A, R))
        leneq = w.s([l1, l2], 'eqtr4d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, L, R))
        bm = w.s([n, kn, w.inst('bitsmod')], 'syl2anc', '( %s -> ( bits ` %s ) = ( ( bits ` N ) i^i ( 0 ..^ K ) ) )' % (A, NM))
        ss = w.s([k, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ M ) C_ ( 0 ..^ K ) )' % A)

        def letter(a2, ist):
            l1b = w.s([l1], 'adantr', '( %s -> ( # ` %s ) = M )' % (a2, L))
            o = w.s([l1b], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ M ) )' % (a2, L))
            i1 = w.s([ist, o], 'eleqtrd', '( %s -> i e. ( 0 ..^ M ) )' % a2)
            nm2 = w.s([nm], 'adantr', '( %s -> %s e. ZZ )' % (a2, NM)); n2 = w.s([n], 'adantr', '( %s -> N e. ZZ )' % a2); m2 = w.s([m], 'adantr', '( %s -> M e. NN0 )' % a2)
            lhs = w.s([nm2, m2, i1, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, L, BIT(NM, 'i')))
            rhs = w.s([n2, m2, i1, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` i ) = %s )' % (a2, R, BIT('N', 'i')))
            bm2 = w.s([bm], 'adantr', '( %s -> ( bits ` %s ) = ( ( bits ` N ) i^i ( 0 ..^ K ) ) )' % (a2, NM))
            e1 = w.s([bm2], 'eleq2d', '( %s -> ( i e. ( bits ` %s ) <-> i e. ( ( bits ` N ) i^i ( 0 ..^ K ) ) ) )' % (a2, NM))
            ei = w.s([], 'elin', '( i e. ( ( bits ` N ) i^i ( 0 ..^ K ) ) <-> ( i e. ( bits ` N ) /\\ i e. ( 0 ..^ K ) ) )')
            eid = w.s([ei], 'a1i', '( %s -> ( i e. ( ( bits ` N ) i^i ( 0 ..^ K ) ) <-> ( i e. ( bits ` N ) /\\ i e. ( 0 ..^ K ) ) ) )' % a2)
            ss2 = w.s([ss], 'adantr', '( %s -> ( 0 ..^ M ) C_ ( 0 ..^ K ) )' % a2)
            ik = w.s([ss2, i1], 'sseldd', '( %s -> i e. ( 0 ..^ K ) )' % a2)
            ba = w.s([ik], 'biantrud', '( %s -> ( i e. ( bits ` N ) <-> ( i e. ( bits ` N ) /\\ i e. ( 0 ..^ K ) ) ) )' % a2)
            b12 = w.s([e1, eid], 'bitrd', '( %s -> ( i e. ( bits ` %s ) <-> ( i e. ( bits ` N ) /\\ i e. ( 0 ..^ K ) ) ) )' % (a2, NM)); bi = w.s([b12, ba], 'bitr4d', '( %s -> ( i e. ( bits ` %s ) <-> i e. ( bits ` N ) ) )' % (a2, NM))
            ifb = w.s([bi], 'ifbid', '( %s -> %s = %s )' % (a2, BIT(NM, 'i'), BIT('N', 'i')))
            l3 = w.s([lhs, ifb], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (a2, L, BIT('N', 'i')))
            return w.s([l3, rhs], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (a2, L, R))
        wrdeq(w, A, L, R, clL, clR, leneq, letter, name='qed'); w.run()

    if want('bwrdeq'):
        A = '( ( N e. ZZ /\\ O e. ZZ /\\ M e. NN0 ) /\\ ( N mod ( 2 ^ M ) ) = ( O mod ( 2 ^ M ) ) )'
        w = W('bwrdeq', 'Two integers with the same residue modulo 2 ^ M have the same M low digits.')
        n = w.s([], 'simpl1', '( %s -> N e. ZZ )' % A); o = w.s([], 'simpl2', '( %s -> O e. ZZ )' % A); m = w.s([], 'simpl3', '( %s -> M e. NN0 )' % A)
        h = w.s([], 'simpr', '( %s -> ( N mod ( 2 ^ M ) ) = ( O mod ( 2 ^ M ) ) )' % A)
        mz = w.s([m], 'nn0zd', '( %s -> M e. ZZ )' % A)
        uz = w.s([mz, w.inst('uzid')], 'syl', '( %s -> M e. ( ZZ>= ` M ) )' % A)
        e1 = w.s([n, m, uz, w.inst('bwrdmod')], 'syl3anc', '( %s -> ( ( N mod ( 2 ^ M ) ) bwrd M ) = ( N bwrd M ) )' % A)
        e2 = w.s([o, m, uz, w.inst('bwrdmod')], 'syl3anc', '( %s -> ( ( O mod ( 2 ^ M ) ) bwrd M ) = ( O bwrd M ) )' % A)
        e3 = w.s([h], 'oveq1d', '( %s -> ( ( N mod ( 2 ^ M ) ) bwrd M ) = ( ( O mod ( 2 ^ M ) ) bwrd M ) )' % A)
        w.qed([e1, e3, e2], '3eqtr3d', '( %s -> ( N bwrd M ) = ( O bwrd M ) )' % A); w.run()
