"""Sortie T4, group L: the cons clause of addBits (Lean clause 4), the faithfulness check of df-addbits."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


if __name__ == '__main__':
    if want('bwmaxp1'):
        A2 = '( M e. NN0 /\\ N e. NN0 )'
        w = W('bwmaxp1', 'The larger of two successors is the successor of the larger.')
        m = w.s([], 'simpl', '( %s -> M e. NN0 )' % A2); n = w.s([], 'simpr', '( %s -> N e. NN0 )' % A2)
        cl = Cl(w, A2, {'M': ('NN0', m), 'N': ('NN0', n)})
        L = 'if ( ( 1 + M ) <_ ( 1 + N ) , ( 1 + N ) , ( 1 + M ) )'; R = '( 1 + if ( M <_ N , N , M ) )'
        onr = w.s([], '1red', '( %s -> 1 e. RR )' % A2)
        la = w.s([cl.mem('M', 'RR'), cl.mem('N', 'RR'), onr, w.inst('leadd2')], 'syl3anc', '( %s -> ( M <_ N <-> ( 1 + M ) <_ ( 1 + N ) ) )' % A2)
        ib = w.s([la], 'ifbid', '( %s -> if ( M <_ N , ( 1 + N ) , ( 1 + M ) ) = %s )' % (A2, L))
        # ( 1 + if ( ph , N , M ) ) = if ( ph , ( 1 + N ) , ( 1 + M ) ) : ovif2
        ov = w.s([], 'ovif2', '( 1 + if ( M <_ N , N , M ) ) = if ( M <_ N , ( 1 + N ) , ( 1 + M ) )'); ovd = w.s([ov], 'a1i', '( %s -> %s = if ( M <_ N , ( 1 + N ) , ( 1 + M ) ) )' % (A2, R))
        w.qed([ovd, ib], 'eqtr2d', '( %s -> %s = %s )' % (A2, L, R)); w.run()

    if want('addbitscons'):
        A5 = '( ( A e. 2o /\\ B e. 2o /\\ C e. 2o ) /\\ ( X e. Word 2o /\\ Y e. Word 2o ) )'
        w = W('addbitscons', 'Lean clause 4 of addBits: the sum of two words with a letter prepended is the sum bit followed by the sum of the tails with the carry bit as carry-in.')
        a = w.s([], 'simpl1', '( %s -> A e. 2o )' % A5); b = w.s([], 'simpl2', '( %s -> B e. 2o )' % A5); c = w.s([], 'simpl3', '( %s -> C e. 2o )' % A5)
        x = w.s([], 'simprl', '( %s -> X e. Word 2o )' % A5); y = w.s([], 'simprr', '( %s -> Y e. Word 2o )' % A5)
        cl = Cl(w, A5, {'A': ('2o', a), 'B': ('2o', b), 'C': ('2o', c), 'X': ('Word 2o', x), 'Y': ('Word 2o', y)})
        XA = CONS('A', 'X'); YB = CONS('B', 'Y')
        s_ = OP3('A', 'sumBit', 'B', 'C'); m_ = OP3('A', 'majBit', 'B', 'C')
        clx = cl.mem(XA, 'Word 2o'); cly = cl.mem(YB, 'Word 2o'); mm = cl.mem(m_, '2o'); ss = cl.mem(s_, '2o')
        S1 = SUM(XA, YB, 'C'); N1 = MAX(XA, YB); K1 = 'if ( ( 2 ^ %s ) <_ %s , 1o , (/) )' % (N1, S1)
        Sm = SUM('X', 'Y', m_); Nm = MAX('X', 'Y'); Km = 'if ( ( 2 ^ %s ) <_ %s , 1o , (/) )' % (Nm, Sm)
        v1 = w.s([clx, cly, c, w.inst('addbitsval')], 'syl3anc', '( %s -> ( ( %s addBits %s ) ` C ) = ( %s ++ ( addCarry ` %s ) ) )' % (A5, XA, YB, BWRD(S1, N1), K1))
        v2 = w.s([x, y, mm, w.inst('addbitsval')], 'syl3anc', '( %s -> ( ( X addBits Y ) ` %s ) = ( %s ++ ( addCarry ` %s ) ) )' % (A5, m_, BWRD(Sm, Nm), Km))
        # S1 = bn s + 2 Sm
        ta = w.s([a, x, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( bToNat ` A ) + ( 2 x. ( toNat ` X ) ) ) )' % (A5, XA))
        tb = w.s([b, y, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( bToNat ` B ) + ( 2 x. ( toNat ` Y ) ) ) )' % (A5, YB))
        fa = w.s([a, b, c, w.inst('bwfulladd')], 'syl3anc', '( %s -> ( ( ( bToNat ` A ) + ( bToNat ` B ) ) + ( bToNat ` C ) ) = ( ( bToNat ` %s ) + ( 2 x. ( bToNat ` %s ) ) ) )' % (A5, s_, m_))
        for E in ('( toNat ` X )', '( toNat ` Y )', '( bToNat ` A )', '( bToNat ` B )', '( bToNat ` C )', '( bToNat ` %s )' % s_, '( bToNat ` %s )' % m_, '( toNat ` %s )' % XA, '( toNat ` %s )' % YB):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        SF = '( ( bToNat ` %s ) + ( 2 x. %s ) )' % (s_, Sm)
        seq = lineq(w, A5, S1, SF, hyps=[ta, tb, fa], closure=cl)
        # N1 = Nm + 1
        lx = w.s([cl.mem('<" A ">', 'Word 2o'), x, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" A "> ) + ( # ` X ) ) )' % (A5, XA))
        ly = w.s([cl.mem('<" B ">', 'Word 2o'), y, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" B "> ) + ( # ` Y ) ) )' % (A5, YB))
        s1a = w.s([w.s([], 's1len', '( # ` <" A "> ) = 1')], 'a1i', '( %s -> ( # ` <" A "> ) = 1 )' % A5); s1b = w.s([w.s([], 's1len', '( # ` <" B "> ) = 1')], 'a1i', '( %s -> ( # ` <" B "> ) = 1 )' % A5)
        lx2 = w.s([lx, w.s([s1a], 'oveq1d', '( %s -> ( ( # ` <" A "> ) + ( # ` X ) ) = ( 1 + ( # ` X ) ) )' % A5)], 'eqtrd', '( %s -> ( # ` %s ) = ( 1 + ( # ` X ) ) )' % (A5, XA))
        ly2 = w.s([ly, w.s([s1b], 'oveq1d', '( %s -> ( ( # ` <" B "> ) + ( # ` Y ) ) = ( 1 + ( # ` Y ) ) )' % A5)], 'eqtrd', '( %s -> ( # ` %s ) = ( 1 + ( # ` Y ) ) )' % (A5, YB))
        rules = {LEN(XA): ('( 1 + ( # ` X ) )', lx2), LEN(YB): ('( 1 + ( # ` Y ) )', ly2)}
        st1, N1b = w.rewrite(N1, rules, A5)
        mp = w.s([cl.mem(LEN('X'), 'NN0'), cl.mem(LEN('Y'), 'NN0'), w.inst('bwmaxp1')], 'syl2anc', '( %s -> %s = ( 1 + %s ) )' % (A5, N1b, Nm))
        com = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A5), cl.mem(Nm, 'CC')], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (A5, Nm, Nm))
        neq = w.s([st1, mp, com], '3eqtrd', '( %s -> %s = ( %s + 1 ) )' % (A5, N1, Nm))
        # the digits word
        bw1 = w.s([seq, neq], 'oveq12d', '( %s -> %s = %s )' % (A5, BWRD(S1, N1), BWRD(SF, '( %s + 1 )' % Nm)))
        sfz = cl.mem(SF, 'ZZ'); nmn = cl.mem(Nm, 'NN0')
        bc = w.s([sfz, nmn, w.inst('bwrdcons')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (A5, BWRD(SF, '( %s + 1 )' % Nm), BIT(SF, '0'), BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm)))
        smz = cl.mem(Sm, 'ZZ')
        b0 = w.s([ss, smz, w.inst('bwbit0')], 'syl2anc', '( %s -> ( 0 e. ( bits ` %s ) <-> %s = 1o ) )' % (A5, SF, s_))
        b0r = w.s([b0], 'bicomd', '( %s -> ( %s = 1o <-> 0 e. ( bits ` %s ) ) )' % (A5, s_, SF))
        sb = bool_from_bi(w, A5, s_, '0 e. ( bits ` %s )' % SF, b0r, ss)
        fh = w.s([ss, smz, w.inst('bwflhalf')], 'syl2anc', '( %s -> ( |_ ` ( %s / 2 ) ) = %s )' % (A5, SF, Sm))
        se = w.s([sb], 's1eqd', '( %s -> <" %s "> = <" %s "> )' % (A5, s_, BIT(SF, '0'))); fh2 = w.s([fh], 'oveq1d', '( %s -> %s = %s )' % (A5, BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm), BWRD(Sm, Nm)))
        se2 = w.s([se], 'eqcomd', '( %s -> <" %s "> = <" %s "> )' % (A5, BIT(SF, '0'), s_))
        cc = w.s([se2, fh2], 'oveq12d', '( %s -> ( <" %s "> ++ %s ) = ( <" %s "> ++ %s ) )' % (A5, BIT(SF, '0'), BWRD('( |_ ` ( %s / 2 ) )' % SF, Nm), s_, BWRD(Sm, Nm)))
        dw = w.s([bw1, bc, cc], '3eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (A5, BWRD(S1, N1), s_, BWRD(Sm, Nm)))
        # the carries agree
        PN = '( 2 ^ %s )' % Nm; PN1 = '( 2 ^ ( %s + 1 ) )' % Nm
        cl.leaf(PN, 'RR', cl.mem(PN, 'RR')); cl.leaf(PN1, 'RR', cl.mem(PN1, 'RR'))
        ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A5), nmn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (A5, PN1, PN))
        pe = w.s([neq], 'oveq2d', '( %s -> ( 2 ^ %s ) = %s )' % (A5, N1, PN1))
        br = w.s([pe, seq], 'breq12d', '( %s -> ( ( 2 ^ %s ) <_ %s <-> %s <_ %s ) )' % (A5, N1, S1, PN1, SF))
        sle = w.s([ss, w.inst('bwbnle1')], 'syl', '( %s -> ( bToNat ` %s ) <_ 1 )' % (A5, s_)); sg = cl.ge0('( bToNat ` %s )' % s_)
        cond = '%s <_ %s' % (PN, Sm)
        a1 = '( %s /\\ %s )' % (A5, cond); h1 = w.s([], 'simpr', '( %s -> %s )' % (a1, cond))
        c1 = Cl(w, a1, {}); c1.parent = cl
        for E in (PN, PN1, '( bToNat ` %s )' % s_, '( toNat ` X )', '( toNat ` Y )', '( bToNat ` %s )' % m_):
            c1.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a1))
        g1 = linarith(w, a1, [h1, lift(w, sg, a1), lift(w, ep, a1)], '%s <_ %s' % (PN1, SF), closure=c1)
        i1a = w.s([g1, lift(w, br, a1)], 'mpbird', '( %s -> ( 2 ^ %s ) <_ %s )' % (a1, N1, S1))
        k1a = w.s([i1a], 'iftrued', '( %s -> %s = 1o )' % (a1, K1)); kma = w.s([h1], 'iftrued', '( %s -> %s = 1o )' % (a1, Km))
        e1 = w.s([k1a, kma], 'eqtr4d', '( %s -> %s = %s )' % (a1, K1, Km))
        a2 = '( %s /\\ -. %s )' % (A5, cond); h2 = w.s([], 'simpr', '( %s -> -. %s )' % (a2, cond))
        c2 = Cl(w, a2, {}); c2.parent = cl
        for E in (PN, PN1, '( bToNat ` %s )' % s_, '( toNat ` X )', '( toNat ` Y )', '( bToNat ` %s )' % m_, Sm):
            c2.leaf(E, 'RR', lift(w, cl.mem(E, 'RR'), a2))
        ln = w.s([lift(w, cl.mem(Sm, 'RR'), a2), lift(w, cl.mem(PN, 'RR'), a2), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s ) )' % (a2, Sm, PN, cond)); lt = w.s([h2, ln], 'mpbird', '( %s -> %s < %s )' % (a2, Sm, PN))
        zl = w.s([lift(w, smz, a2), lift(w, cl.mem(PN, 'ZZ'), a2), w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ ( %s - 1 ) ) )' % (a2, Sm, PN, Sm, PN)); le = w.s([lt, zl], 'mpbid', '( %s -> %s <_ ( %s - 1 ) )' % (a2, Sm, PN))
        g2 = linarith(w, a2, [le, lift(w, sle, a2), lift(w, ep, a2)], '%s < %s' % (SF, PN1), closure=c2)
        ln2 = w.s([lift(w, cl.mem(SF, 'RR'), a2), lift(w, cl.mem(PN1, 'RR'), a2), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (a2, SF, PN1, PN1, SF)); ng = w.s([g2, ln2], 'mpbid', '( %s -> -. %s <_ %s )' % (a2, PN1, SF))
        ng2 = w.s([ng, lift(w, br, a2)], 'mtbird', '( %s -> -. ( 2 ^ %s ) <_ %s )' % (a2, N1, S1))
        k1b = w.s([ng2], 'iffalsed', '( %s -> %s = (/) )' % (a2, K1)); kmb = w.s([h2], 'iffalsed', '( %s -> %s = (/) )' % (a2, Km))
        e2 = w.s([k1b, kmb], 'eqtr4d', '( %s -> %s = %s )' % (a2, K1, Km))
        keq = w.s([e1, e2], 'pm2.61dan', '( %s -> %s = %s )' % (A5, K1, Km))
        fk = w.s([keq], 'fveq2d', '( %s -> ( addCarry ` %s ) = ( addCarry ` %s ) )' % (A5, K1, Km))
        oc = w.s([dw, fk], 'oveq12d', '( %s -> ( %s ++ ( addCarry ` %s ) ) = ( ( <" %s "> ++ %s ) ++ ( addCarry ` %s ) ) )' % (A5, BWRD(S1, N1), K1, s_, BWRD(Sm, Nm), Km))
        ca = w.s([cl.mem('<" %s ">' % s_, 'Word 2o'), cl.mem(BWRD(Sm, Nm), 'Word 2o'), cl.mem('( addCarry ` %s )' % Km, 'Word 2o'), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ ( addCarry ` %s ) ) = ( <" %s "> ++ ( %s ++ ( addCarry ` %s ) ) ) )' % (A5, s_, BWRD(Sm, Nm), Km, s_, BWRD(Sm, Nm), Km))
        o2 = w.s([v2], 'oveq2d', '( %s -> ( <" %s "> ++ ( ( X addBits Y ) ` %s ) ) = ( <" %s "> ++ ( %s ++ ( addCarry ` %s ) ) ) )' % (A5, s_, m_, s_, BWRD(Sm, Nm), Km))
        l1 = w.s([v1, oc, ca], '3eqtrd', '( %s -> ( ( %s addBits %s ) ` C ) = ( <" %s "> ++ ( %s ++ ( addCarry ` %s ) ) ) )' % (A5, XA, YB, s_, BWRD(Sm, Nm), Km))
        w.qed([l1, o2], 'eqtr4d', '( %s -> ( ( %s addBits %s ) ` C ) = ( <" %s "> ++ ( ( X addBits Y ) ` %s ) ) )' % (A5, XA, YB, s_, m_)); w.run()
