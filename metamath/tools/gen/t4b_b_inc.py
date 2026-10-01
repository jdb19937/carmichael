"""Sortie T4b, group B: incBits, carries, incRest, the run decomposition of
the carry chain, encodeNat_succ (T4b-blueprint 1.2)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4blib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AL = 'L e. Word 2o'
T = TN('L'); H = LEN('L'); T1 = '( %s + 1 )' % T; PH = P2(H)
MIv = MI(T, H); CARVv = CARV(T, H); COND = '%s = %s' % (T1, PH)
CR = '( carries ` L )'; INC = '( incBits ` L )'; IR = '( incRest ` L )'
NI = LEN(INC)
Q = '( %s / ( 2 ^ %s ) )' % (T1, CR); D = '( %s - %s )' % (NI, CR)


def base(w, ante=AL):
    """closure under ante (a conjunction whose first conjunct is AL) with
    ( T + 1 ) e. NN recorded"""
    if ante == AL:
        l = w.s([], 'id', '( %s -> L e. Word 2o )' % AL)
    else:
        l = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ante)
    cl = Cl(w, ante, {'L': ('Word 2o', l)})
    tn = cl.mem(T, 'NN0')
    cl.have(T1, 'NN', w.s([tn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (ante, T1)))
    return cl, l


def cons_setup(w, cl, ante, B):
    """for L' = ( <" B "> ++ L ): tc : ( toNat ` L' ) = ( bn B + 2 T ), ln : ( # ` L' ) = ( H + 1 ),
    and the closure entries.  Returns (L', tc, ln)."""
    LB = CONS(B, 'L')
    tc = w.s([cl.mem(B, '2o'), cl.mem('L', 'Word 2o'), w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( bToNat ` %s ) + ( 2 x. %s ) ) )' % (ante, LB, B, T))
    ln = conslen(w, cl, ante, B, 'L')
    return LB, tc, ln


def bn_lits(w, ante):
    b0 = w.s([num.closed(w, [], 'bwbn0', '( bToNat ` (/) ) = 0')], 'a1i', '( %s -> ( bToNat ` (/) ) = 0 )' % ante)
    b1 = w.s([num.closed(w, [], 'bwbn1', '( bToNat ` 1o ) = 1')], 'a1i', '( %s -> ( bToNat ` 1o ) = 1 )' % ante)
    return b0, b1


def carries_cases(w, cl, ante, v, body_t, body_f, concl):
    """case split on COND with v : ( ante -> CR = CARV ); body_t(a1, h1, eq) where eq : ( a1 -> CR = H );
    body_f(a2, h2, eq) where eq : ( a2 -> CR = ( 2 pCnt ( T + 1 ) ) )"""
    PC = '( 2 pCnt %s )' % T1
    def bt(a1, h1):
        i = w.s([h1], 'iftrued', '( %s -> %s = %s )' % (a1, CARVv, H))
        eq = w.s([lift(w, v, a1), i], 'eqtrd', '( %s -> %s = %s )' % (a1, CR, H))
        return body_t(a1, h1, eq)
    def bf(a2, h2):
        i = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, CARVv, PC))
        eq = w.s([lift(w, v, a2), i], 'eqtrd', '( %s -> %s = %s )' % (a2, CR, PC))
        return body_f(a2, h2, eq)
    return cases_if(w, ante, COND, bt, bf, concl)


if __name__ == '__main__':
    if want('incbitsval'):
        w = W('incbitsval', 'Value of incBits: the digits of toNat L + 1, at the length of L or one more when L is all ones.')
        cl, l = base(w)
        st, val = defval(w, cl, 'df-incbits', 'incBits', ['L']); assert val == BWRD(T1, MIv), val
        promote(w, st); w.run()
    if want('incbitscl'):
        w = W('incbitscl', 'Closure of incBits: a bit word.')
        cl, l = base(w)
        v = w.s([], 'incbitsval', '( %s -> %s = %s )' % (AL, INC, BWRD(T1, MIv)))
        w.qed([v, cl.mem(BWRD(T1, MIv), 'Word 2o')], 'eqeltrd', '( %s -> %s e. Word 2o )' % (AL, INC)); w.run()
    if want('incbitslen2'):
        w = W('incbitslen2', 'The length of incBits L, as an if.')
        cl, l = base(w)
        v = w.s([], 'incbitsval', '( %s -> %s = %s )' % (AL, INC, BWRD(T1, MIv)))
        f = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AL, INC, BWRD(T1, MIv)))
        bl = w.s([cl.mem(T1, 'ZZ'), cl.mem(MIv, 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AL, BWRD(T1, MIv), MIv))
        w.qed([f, bl], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (AL, INC, MIv)); w.run()
    if want('incbitslenge'):
        w = W('incbitslenge', 'incBits L is at least as long as L.')
        cl, l = base(w)
        l2 = w.s([], 'incbitslen2', '( %s -> %s = %s )' % (AL, NI, MIv))
        def bt(a1, h1):
            i = w.s([h1], 'iftrued', '( %s -> %s = ( %s + 1 ) )' % (a1, MIv, H))
            le = w.s([lift(w, cl.mem(H, 'RR'), a1)], 'lep1d', '( %s -> %s <_ ( %s + 1 ) )' % (a1, H, H))
            return w.s([le, i], 'breqtrrd', '( %s -> %s <_ %s )' % (a1, H, MIv))
        def bf(a2, h2):
            i = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, MIv, H))
            le = w.s([lift(w, cl.mem(H, 'RR'), a2)], 'leidd', '( %s -> %s <_ %s )' % (a2, H, H))
            return w.s([le, i], 'breqtrrd', '( %s -> %s <_ %s )' % (a2, H, MIv))
        c = cases_if(w, AL, COND, bt, bf, '%s <_ %s' % (H, MIv))
        w.qed([c, l2], 'breqtrrd', '( %s -> %s <_ %s )' % (AL, H, NI)); w.run()
    if want('incbitslen'):
        w = W('incbitslen', 'incBits L is at most one letter longer than L (Lean: incBits_length).')
        cl, l = base(w)
        l2 = w.s([], 'incbitslen2', '( %s -> %s = %s )' % (AL, NI, MIv))
        H1 = '( %s + 1 )' % H
        def bt(a1, h1):
            i = w.s([h1], 'iftrued', '( %s -> %s = %s )' % (a1, MIv, H1))
            le = w.s([lift(w, cl.mem(H1, 'RR'), a1)], 'leidd', '( %s -> %s <_ %s )' % (a1, H1, H1))
            return w.s([i, le], 'eqbrtrd', '( %s -> %s <_ %s )' % (a1, MIv, H1))
        def bf(a2, h2):
            i = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, MIv, H))
            le = w.s([lift(w, cl.mem(H, 'RR'), a2)], 'lep1d', '( %s -> %s <_ %s )' % (a2, H, H1))
            return w.s([i, le], 'eqbrtrd', '( %s -> %s <_ %s )' % (a2, MIv, H1))
        c = cases_if(w, AL, COND, bt, bf, '%s <_ %s' % (MIv, H1))
        w.qed([l2, c], 'eqbrtrd', '( %s -> %s <_ %s )' % (AL, NI, H1)); w.run()
    if want('tonatincbits'):
        w = W('tonatincbits', 'The value of incBits L is toNat L + 1 (Lean: toNat_incBits).')
        cl, l = base(w)
        v = w.s([], 'incbitsval', '( %s -> %s = %s )' % (AL, INC, BWRD(T1, MIv)))
        f = w.s([v], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AL, INC, BWRD(T1, MIv)))
        H1 = '( %s + 1 )' % H
        def bt(a1, h1):
            i = w.s([h1], 'iftrued', '( %s -> %s = %s )' % (a1, MIv, H1))
            o = w.s([i], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (a1, MIv, H1))
            c1 = subcl(w, cl, AL, a1)
            ltE = w.s([lift(w, cl.mem(H, 'RR'), a1)], 'ltp1d', '( %s -> %s < %s )' % (a1, H, H1))
            le2 = ltexp2(w, a1, c1, H, H1)
            lt = w.s([ltE, le2], 'mpbid', '( %s -> %s < ( 2 ^ %s ) )' % (a1, PH, H1))
            lt2 = w.s([h1, lt], 'eqbrtrd', '( %s -> %s < ( 2 ^ %s ) )' % (a1, T1, H1))
            return w.s([lt2, o], 'breqtrrd', '( %s -> %s < ( 2 ^ %s ) )' % (a1, T1, MIv))
        def bf(a2, h2):
            i = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, MIv, H))
            o = w.s([i], 'oveq2d', '( %s -> ( 2 ^ %s ) = %s )' % (a2, MIv, PH))
            ltT = w.s([lift(w, l, a2), w.inst('tonatlt')], 'syl', '( %s -> %s < %s )' % (a2, T, PH))
            zl = w.s([lift(w, cl.mem(T, 'ZZ'), a2), lift(w, cl.mem(PH, 'ZZ'), a2), w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ %s ) )' % (a2, T, PH, T1, PH))
            le = w.s([ltT, zl], 'mpbid', '( %s -> %s <_ %s )' % (a2, T1, PH))
            ne = w.s([h2], 'neqned', '( %s -> %s =/= %s )' % (a2, T1, PH)); ne2 = w.s([ne], 'necomd', '( %s -> %s =/= %s )' % (a2, PH, T1))
            j = w.s([le, ne2], 'jca', '( %s -> ( %s <_ %s /\\ %s =/= %s ) )' % (a2, T1, PH, PH, T1))
            ll = w.s([lift(w, cl.mem(T1, 'RR'), a2), lift(w, cl.mem(PH, 'RR'), a2), w.inst('ltlen')], 'syl2anc', '( %s -> ( %s < %s <-> ( %s <_ %s /\\ %s =/= %s ) ) )' % (a2, T1, PH, T1, PH, PH, T1))
            lt = w.s([j, ll], 'mpbird', '( %s -> %s < %s )' % (a2, T1, PH))
            return w.s([lt, o], 'breqtrrd', '( %s -> %s < ( 2 ^ %s ) )' % (a2, T1, MIv))
        lt = cases_if(w, AL, COND, bt, bf, '%s < ( 2 ^ %s )' % (T1, MIv))
        tb = w.s([cl.mem(T1, 'NN0'), cl.mem(MIv, 'NN0'), lt, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (AL, BWRD(T1, MIv), T1))
        w.qed([f, tb], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (AL, INC, T1)); w.run()

    if want('incbitsnil'):
        w = W('incbitsnil', 'Lean clause 1 of incBits: the increment of the empty word is the one-letter word true.')
        TT = 'T.'
        E0 = '(/)'
        v0 = w.s([], 'incbitsval', '( (/) e. Word 2o -> ( incBits ` (/) ) = %s )' % BWRD('( ( toNat ` (/) ) + 1 )', MI('( toNat ` (/) )', '( # ` (/) )')))
        w0 = num.closed(w, [], 'wrd0', '(/) e. Word 2o')
        v1 = num.closed(w, [w0, v0], 'ax-mp', '( incBits ` (/) ) = %s' % BWRD('( ( toNat ` (/) ) + 1 )', MI('( toNat ` (/) )', '( # ` (/) )')))
        vd = w.s([v1], 'a1i', '( T. -> ( incBits ` (/) ) = %s )' % BWRD('( ( toNat ` (/) ) + 1 )', MI('( toNat ` (/) )', '( # ` (/) )')))
        t0 = w.s([num.closed(w, [], 'tonat0', '( toNat ` (/) ) = 0')], 'a1i', '( T. -> ( toNat ` (/) ) = 0 )')
        h0 = w.s([num.closed(w, [], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( T. -> ( # ` (/) ) = 0 )')
        p1 = w.s([num.closed(w, [], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( T. -> ( 0 + 1 ) = 1 )')
        tc = num.closed(w, [], '2cn', '2 e. CC'); e0 = num.closed(w, [tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( T. -> ( 2 ^ 0 ) = 1 )')
        st, cur = rewrite_chain(w, TT, BWRD('( ( toNat ` (/) ) + 1 )', MI('( toNat ` (/) )', '( # ` (/) )')),
                                [{'( toNat ` (/) )': ('0', t0), '( # ` (/) )': ('0', h0)}, {'( 0 + 1 )': ('1', p1), '( 2 ^ 0 )': ('1', e0d)}])
        assert cur == '( 1 bwrd if ( 1 = 1 , 1 , 0 ) )', cur
        it = num.closed(w, [num.closed(w, [], 'eqid', '1 = 1')], 'iftruei', 'if ( 1 = 1 , 1 , 0 ) = 1')
        itd = w.s([it], 'a1i', '( T. -> if ( 1 = 1 , 1 , 0 ) = 1 )')
        st2, cur2 = w.rewrite(cur, {'if ( 1 = 1 , 1 , 0 )': ('1', itd)}, TT)
        assert cur2 == '( 1 bwrd 1 )', cur2
        v2 = w.s([vd, st, st2], '3eqtrd', '( T. -> ( incBits ` (/) ) = ( 1 bwrd 1 ) )')
        # ( 1 bwrd 1 ) = <" 1o ">
        oz = num.closed(w, [], '1z', '1 e. ZZ'); zn = num.closed(w, [], '0nn0', '0 e. NN0')
        bp = num.closed(w, [oz, zn, w.inst('bwrdp1')], 'mp2an', '( 1 bwrd ( 0 + 1 ) ) = ( ( 1 bwrd 0 ) ++ <" %s "> )' % BIT('1', '0'))
        o1 = num.closed(w, [num.closed(w, [], '0p1e1', '( 0 + 1 ) = 1')], 'oveq2i', '( 1 bwrd ( 0 + 1 ) ) = ( 1 bwrd 1 )')
        e1 = num.closed(w, [o1, bp], 'eqtr3i', '( 1 bwrd 1 ) = ( ( 1 bwrd 0 ) ++ <" %s "> )' % BIT('1', '0'))
        b0 = num.closed(w, [oz, w.inst('bwrd0')], 'ax-mp', '( 1 bwrd 0 ) = (/)')
        bi = num.closed(w, [oz, w.inst('bits0')], 'ax-mp', '( 0 e. ( bits ` 1 ) <-> -. 2 || 1 )')
        nd = num.closed(w, [], 'n2dvds1', '-. 2 || 1')
        el = num.closed(w, [nd, bi], 'mpbir', '0 e. ( bits ` 1 )')
        it1 = num.closed(w, [el], 'iftruei', '%s = 1o' % BIT('1', '0'))
        it1d = w.s([it1], 'a1i', '( T. -> %s = 1o )' % BIT('1', '0'))
        s1 = w.s([it1d], 's1eqd', '( T. -> <" %s "> = <" 1o "> )' % BIT('1', '0'))
        b0d = w.s([b0], 'a1i', '( T. -> ( 1 bwrd 0 ) = (/) )')
        cc = w.s([b0d, s1], 'oveq12d', '( T. -> ( ( 1 bwrd 0 ) ++ <" %s "> ) = ( (/) ++ <" 1o "> ) )' % BIT('1', '0'))
        s1w = num.closed(w, [num.closed(w, [], '1oel2o', '1o e. 2o'), w.inst('s1cl')], 'ax-mp', '<" 1o "> e. Word 2o')
        li = num.closed(w, [s1w, w.inst('ccatlid')], 'ax-mp', '( (/) ++ <" 1o "> ) = <" 1o ">')
        lid = w.s([li], 'a1i', '( T. -> ( (/) ++ <" 1o "> ) = <" 1o "> )')
        e1d = w.s([e1], 'a1i', '( T. -> ( 1 bwrd 1 ) = ( ( 1 bwrd 0 ) ++ <" %s "> ) )' % BIT('1', '0'))
        e2d = w.s([e1d, cc, lid], '3eqtrd', '( T. -> ( 1 bwrd 1 ) = <" 1o "> )')
        fin = w.s([v2, e2d], 'eqtrd', '( T. -> ( incBits ` (/) ) = <" 1o "> )')
        w.qed([fin], 'mptru', '( incBits ` (/) ) = <" 1o ">'); w.run()

    if want('incbitscons0'):
        w = W('incbitscons0', 'Lean clause 2 of incBits: a false letter in front becomes true, the rest is unchanged.')
        cl, l = base(w)
        L0, tc, ln = cons_setup(w, cl, AL, '(/)')
        T0 = TN(L0); H0 = LEN(L0); T01 = '( %s + 1 )' % T0
        b0, b1 = bn_lits(w, AL)
        for E in (T0, T, BN('(/)'), BN('1o')):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        Sp = '( ( 2 x. %s ) + 1 )' % T; S = '( ( bToNat ` 1o ) + ( 2 x. %s ) )' % T
        eqS1 = lineq(w, AL, T01, Sp, hyps=[tc, b0], closure=cl)
        eqS = lineq(w, AL, T01, S, hyps=[tc, b0, b1], closure=cl)
        v = w.s([cl.mem(L0, 'Word 2o'), w.inst('incbitsval')], 'syl', '( %s -> ( incBits ` %s ) = %s )' % (AL, L0, BWRD(T01, MI(T0, H0))))
        # the condition is false
        H1 = '( %s + 1 )' % H
        pe = w.s([ln], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (AL, H0, H1))
        ec = exp_p1c(w, cl, AL, H)
        pe2 = w.s([pe, ec], 'eqtrd', '( %s -> ( 2 ^ %s ) = ( 2 x. %s ) )' % (AL, H0, PH))
        ne = ne_from_oddne(w, cl, AL, T, PH)
        bi = w.s([eqS1, pe2], 'eqeq12d', '( %s -> ( %s = ( 2 ^ %s ) <-> %s = ( 2 x. %s ) ) )' % (AL, T01, H0, Sp, PH))
        nc = w.s([ne, bi], 'mtbird', '( %s -> -. %s = ( 2 ^ %s ) )' % (AL, T01, H0))
        i = w.s([nc], 'iffalsed', '( %s -> %s = %s )' % (AL, MI(T0, H0), H0))
        i2 = w.s([i, ln], 'eqtrd', '( %s -> %s = %s )' % (AL, MI(T0, H0), H1))
        o = w.s([eqS, i2], 'oveq12d', '( %s -> %s = %s )' % (AL, BWRD(T01, MI(T0, H0)), BWRD(S, H1)))
        bc = w.s([cl.mem(S, 'ZZ'), cl.mem(H, 'NN0'), w.inst('bwrdcons')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (AL, BWRD(S, H1), BIT(S, '0'), BWRD('( |_ ` ( %s / 2 ) )' % S, H)))
        one = w.s([num.closed(w, [], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % AL)
        bb = w.s([one, cl.mem(T, 'ZZ'), w.inst('bwbit0')], 'syl2anc', '( %s -> ( 0 e. ( bits ` %s ) <-> 1o = 1o ) )' % (AL, S))
        eqi = w.s([], 'eqidd', '( %s -> 1o = 1o )' % AL)
        el = w.s([eqi, bb], 'mpbird', '( %s -> 0 e. ( bits ` %s ) )' % (AL, S))
        it = w.s([el], 'iftrued', '( %s -> %s = 1o )' % (AL, BIT(S, '0')))
        se = w.s([it], 's1eqd', '( %s -> <" %s "> = <" 1o "> )' % (AL, BIT(S, '0')))
        fh = w.s([one, cl.mem(T, 'ZZ'), w.inst('bwflhalf')], 'syl2anc', '( %s -> ( |_ ` ( %s / 2 ) ) = %s )' % (AL, S, T))
        fo = w.s([fh], 'oveq1d', '( %s -> %s = %s )' % (AL, BWRD('( |_ ` ( %s / 2 ) )' % S, H), BWRD(T, H)))
        ew = w.s([l, w.inst('bweqwrd')], 'syl', '( %s -> L = %s )' % (AL, BWRD(T, H)))
        fo2 = w.s([fo, ew], 'eqtr4d', '( %s -> %s = L )' % (AL, BWRD('( |_ ` ( %s / 2 ) )' % S, H)))
        cc = w.s([se, fo2], 'oveq12d', '( %s -> ( <" %s "> ++ %s ) = ( <" 1o "> ++ L ) )' % (AL, BIT(S, '0'), BWRD('( |_ ` ( %s / 2 ) )' % S, H)))
        w.qed([v, o, bc, cc], '4eqtrd' if False else '3eqtrd', '') if False else None
        c1 = w.s([v, o, bc], '3eqtrd', '( %s -> ( incBits ` %s ) = ( <" %s "> ++ %s ) )' % (AL, L0, BIT(S, '0'), BWRD('( |_ ` ( %s / 2 ) )' % S, H)))
        w.qed([c1, cc], 'eqtrd', '( %s -> ( incBits ` %s ) = ( <" 1o "> ++ L ) )' % (AL, L0)); w.run()

    if want('incbitscons1'):
        w = W('incbitscons1', 'Lean clause 3 of incBits: a true letter in front becomes false and the rest is incremented.')
        cl, l = base(w)
        L1, tc, ln = cons_setup(w, cl, AL, '1o')
        Tb = TN(L1); Hb = LEN(L1); Tb1 = '( %s + 1 )' % Tb
        b0, b1 = bn_lits(w, AL)
        for E in (Tb, T, BN('(/)'), BN('1o')):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        D2 = '( 2 x. %s )' % T1; S = '( ( bToNat ` (/) ) + ( 2 x. %s ) )' % T1
        eqS2 = lineq(w, AL, Tb1, D2, hyps=[tc, b1], closure=cl)
        eqS = lineq(w, AL, Tb1, S, hyps=[tc, b0, b1], closure=cl)
        v = w.s([cl.mem(L1, 'Word 2o'), w.inst('incbitsval')], 'syl', '( %s -> ( incBits ` %s ) = %s )' % (AL, L1, BWRD(Tb1, MI(Tb, Hb))))
        H1 = '( %s + 1 )' % H
        pe = w.s([ln], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (AL, Hb, H1))
        ec = exp_p1c(w, cl, AL, H)
        pe2 = w.s([pe, ec], 'eqtrd', '( %s -> ( 2 ^ %s ) = ( 2 x. %s ) )' % (AL, Hb, PH))
        bi1 = w.s([eqS2, pe2], 'eqeq12d', '( %s -> ( %s = ( 2 ^ %s ) <-> %s = ( 2 x. %s ) ) )' % (AL, Tb1, Hb, D2, PH))
        twoc = w.s([], '2cnd', '( %s -> 2 e. CC )' % AL); twone = w.s([num.closed(w, [], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % AL)
        mc = w.s([cl.mem(T1, 'CC'), cl.mem(PH, 'CC'), twoc, twone], 'mulcand', '( %s -> ( ( 2 x. %s ) = ( 2 x. %s ) <-> %s = %s ) )' % (AL, T1, PH, T1, PH))
        bi = w.s([bi1, mc], 'bitrd', '( %s -> ( %s = ( 2 ^ %s ) <-> %s ) )' % (AL, Tb1, Hb, COND))
        Hb1 = '( %s + 1 )' % Hb; H11 = '( %s + 1 )' % H1
        ib = w.s([bi], 'ifbid', '( %s -> %s = if ( %s , %s , %s ) )' % (AL, MI(Tb, Hb), COND, Hb1, Hb))
        l1 = w.s([ln], 'oveq1d', '( %s -> %s = %s )' % (AL, Hb1, H11))
        ie = w.s([l1, ln], 'ifeq12d', '( %s -> if ( %s , %s , %s ) = if ( %s , %s , %s ) )' % (AL, COND, Hb1, Hb, COND, H11, H1))
        ov = w.s([num.closed(w, [], 'ovif', '( %s + 1 ) = if ( %s , %s , %s )' % (MIv, COND, H11, H1))], 'a1i', '( %s -> ( %s + 1 ) = if ( %s , %s , %s ) )' % (AL, MIv, COND, H11, H1))
        mi = w.s([w.s([ib, ie], 'eqtrd', '( %s -> %s = if ( %s , %s , %s ) )' % (AL, MI(Tb, Hb), COND, H11, H1)), ov], 'eqtr4d', '( %s -> %s = ( %s + 1 ) )' % (AL, MI(Tb, Hb), MIv))
        o = w.s([eqS, mi], 'oveq12d', '( %s -> %s = %s )' % (AL, BWRD(Tb1, MI(Tb, Hb)), BWRD(S, '( %s + 1 )' % MIv)))
        bc = w.s([cl.mem(S, 'ZZ'), cl.mem(MIv, 'NN0'), w.inst('bwrdcons')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (AL, BWRD(S, '( %s + 1 )' % MIv), BIT(S, '0'), BWRD('( |_ ` ( %s / 2 ) )' % S, MIv)))
        zero = w.s([num.closed(w, [], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % AL)
        bb = w.s([zero, cl.mem(T1, 'ZZ'), w.inst('bwbit0')], 'syl2anc', '( %s -> ( 0 e. ( bits ` %s ) <-> (/) = 1o ) )' % (AL, S))
        n1 = num.closed(w, [], '1n0', '1o =/= (/)'); nn = num.closed(w, [n1], 'nesymi', '-. (/) = 1o'); nnd = w.s([nn], 'a1i', '( %s -> -. (/) = 1o )' % AL)
        nel = w.s([nnd, bb], 'mtbird', '( %s -> -. 0 e. ( bits ` %s ) )' % (AL, S))
        it = w.s([nel], 'iffalsed', '( %s -> %s = (/) )' % (AL, BIT(S, '0')))
        se = w.s([it], 's1eqd', '( %s -> <" %s "> = <" (/) "> )' % (AL, BIT(S, '0')))
        fh = w.s([zero, cl.mem(T1, 'ZZ'), w.inst('bwflhalf')], 'syl2anc', '( %s -> ( |_ ` ( %s / 2 ) ) = %s )' % (AL, S, T1))
        fo = w.s([fh], 'oveq1d', '( %s -> %s = %s )' % (AL, BWRD('( |_ ` ( %s / 2 ) )' % S, MIv), BWRD(T1, MIv)))
        iv = w.s([], 'incbitsval', '( %s -> %s = %s )' % (AL, INC, BWRD(T1, MIv)))
        fo2 = w.s([fo, iv], 'eqtr4d', '( %s -> %s = %s )' % (AL, BWRD('( |_ ` ( %s / 2 ) )' % S, MIv), INC))
        cc = w.s([se, fo2], 'oveq12d', '( %s -> ( <" %s "> ++ %s ) = ( <" (/) "> ++ %s ) )' % (AL, BIT(S, '0'), BWRD('( |_ ` ( %s / 2 ) )' % S, MIv), INC))
        c1 = w.s([v, o, bc], '3eqtrd', '( %s -> ( incBits ` %s ) = ( <" %s "> ++ %s ) )' % (AL, L1, BIT(S, '0'), BWRD('( |_ ` ( %s / 2 ) )' % S, MIv)))
        w.qed([c1, cc], 'eqtrd', '( %s -> ( incBits ` %s ) = ( <" (/) "> ++ %s ) )' % (AL, L1, INC)); w.run()

    # ---- carries
    if want('carriesval'):
        w = W('carriesval', 'Value of carries: the 2-adic valuation of toNat L + 1, or the length when L is all ones.')
        cl, l = base(w)
        st, val = defval(w, cl, 'df-carries', 'carries', ['L']); assert val == CARVv, val
        promote(w, st); w.run()
    if want('carriescl'):
        w = W('carriescl', 'Closure of carries: a nonnegative integer.')
        cl, l = base(w)
        v = w.s([], 'carriesval', '( %s -> %s = %s )' % (AL, CR, CARVv))
        w.qed([v, cl.mem(CARVv, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (AL, CR)); w.run()
    if want('carriesle'):
        w = W('carriesle', 'The carries of an increment are at most the length (Lean: carries_le_length).')
        cl, l = base(w)
        v = w.s([], 'carriesval', '( %s -> %s = %s )' % (AL, CR, CARVv))
        PC = '( 2 pCnt %s )' % T1
        def bt(a1, h1, eq):
            le = w.s([lift(w, cl.mem(H, 'RR'), a1)], 'leidd', '( %s -> %s <_ %s )' % (a1, H, H))
            return w.s([eq, le], 'eqbrtrd', '( %s -> %s <_ %s )' % (a1, CR, H))
        def bf(a2, h2, eq):
            c2 = subcl(w, cl, AL, a2)
            tp = two_prime(w, a2)
            dv = w.s([tp, lift(w, cl.mem(T1, 'NN'), a2), w.inst('pcdvds')], 'syl2anc', '( %s -> ( 2 ^ %s ) || %s )' % (a2, PC, T1))
            dl = w.s([c2.mem(P2(PC), 'ZZ'), lift(w, cl.mem(T1, 'NN'), a2), w.inst('dvdsle')], 'syl2anc', '( %s -> ( ( 2 ^ %s ) || %s -> ( 2 ^ %s ) <_ %s ) )' % (a2, PC, T1, PC, T1))
            le1 = w.s([dv, dl], 'mpd', '( %s -> ( 2 ^ %s ) <_ %s )' % (a2, PC, T1))
            ltT = w.s([lift(w, l, a2), w.inst('tonatlt')], 'syl', '( %s -> %s < %s )' % (a2, T, PH))
            zl = w.s([lift(w, cl.mem(T, 'ZZ'), a2), lift(w, cl.mem(PH, 'ZZ'), a2), w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ %s ) )' % (a2, T, PH, T1, PH))
            le2 = w.s([ltT, zl], 'mpbid', '( %s -> %s <_ %s )' % (a2, T1, PH))
            le3 = w.s([c2.mem(P2(PC), 'RR'), lift(w, cl.mem(T1, 'RR'), a2), lift(w, cl.mem(PH, 'RR'), a2), le1, le2], 'letrd', '( %s -> ( 2 ^ %s ) <_ %s )' % (a2, PC, PH))
            r2 = w.s([num.closed(w, [], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % a2)
            j = w.s([r2, c2.mem(PC, 'ZZ'), lift(w, cl.mem(H, 'ZZ'), a2)], '3jca', '( %s -> ( 2 e. RR /\\ %s e. ZZ /\\ %s e. ZZ ) )' % (a2, PC, H))
            lt12 = w.s([num.closed(w, [], '1lt2', '1 < 2')], 'a1i', '( %s -> 1 < 2 )' % a2)
            lx = w.s([j, lt12, w.inst('leexp2')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( 2 ^ %s ) <_ %s ) )' % (a2, PC, H, PC, PH))
            le4 = w.s([le3, lx], 'mpbird', '( %s -> %s <_ %s )' % (a2, PC, H))
            return w.s([eq, le4], 'eqbrtrd', '( %s -> %s <_ %s )' % (a2, CR, H))
        c = carries_cases(w, cl, AL, v, bt, bf, '%s <_ %s' % (CR, H))
        promote(w, c); w.run()
    if want('carriesdvds'):
        w = W('carriesdvds', '2 to the carries divides toNat L + 1.')
        cl, l = base(w)
        v = w.s([], 'carriesval', '( %s -> %s = %s )' % (AL, CR, CARVv))
        PC = '( 2 pCnt %s )' % T1
        def bt(a1, h1, eq):
            o = w.s([eq], 'oveq2d', '( %s -> ( 2 ^ %s ) = %s )' % (a1, CR, PH))
            o2 = w.s([o, w.s([h1], 'eqcomd', '( %s -> %s = %s )' % (a1, PH, T1))], 'eqtrd', '( %s -> ( 2 ^ %s ) = %s )' % (a1, CR, T1))
            idv = w.s([lift(w, cl.mem(T1, 'ZZ'), a1), w.inst('iddvds')], 'syl', '( %s -> %s || %s )' % (a1, T1, T1))
            return w.s([o2, idv], 'eqbrtrd', '( %s -> ( 2 ^ %s ) || %s )' % (a1, CR, T1))
        def bf(a2, h2, eq):
            tp = two_prime(w, a2)
            dv = w.s([tp, lift(w, cl.mem(T1, 'NN'), a2), w.inst('pcdvds')], 'syl2anc', '( %s -> ( 2 ^ %s ) || %s )' % (a2, PC, T1))
            o = w.s([eq], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (a2, CR, PC))
            return w.s([o, dv], 'eqbrtrd', '( %s -> ( 2 ^ %s ) || %s )' % (a2, CR, T1))
        c = carries_cases(w, cl, AL, v, bt, bf, '( 2 ^ %s ) || %s' % (CR, T1))
        promote(w, c); w.run()
    if want('carriesndvds'):
        w = W('carriesndvds', '2 to the carries plus one does not divide toNat L + 1.')
        cl, l = base(w)
        v = w.s([], 'carriesval', '( %s -> %s = %s )' % (AL, CR, CARVv))
        PC = '( 2 pCnt %s )' % T1; CR1 = '( %s + 1 )' % CR; H1 = '( %s + 1 )' % H
        def bt(a1, h1, eq):
            c1 = subcl(w, cl, AL, a1)
            ltE = w.s([lift(w, cl.mem(H, 'RR'), a1)], 'ltp1d', '( %s -> %s < %s )' % (a1, H, H1))
            le2 = ltexp2(w, a1, c1, H, H1)
            lt = w.s([ltE, le2], 'mpbid', '( %s -> %s < ( 2 ^ %s ) )' % (a1, PH, H1))
            nl = w.s([lift(w, cl.mem(PH, 'RR'), a1), c1.mem(P2(H1), 'RR')], 'ltnled', '( %s -> ( %s < ( 2 ^ %s ) <-> -. ( 2 ^ %s ) <_ %s ) )' % (a1, PH, H1, H1, PH))
            nle = w.s([lt, nl], 'mpbid', '( %s -> -. ( 2 ^ %s ) <_ %s )' % (a1, H1, PH))
            dl = w.s([c1.mem(P2(H1), 'ZZ'), lift(w, cl.mem(PH, 'NN'), a1), w.inst('dvdsle')], 'syl2anc', '( %s -> ( ( 2 ^ %s ) || %s -> ( 2 ^ %s ) <_ %s ) )' % (a1, H1, PH, H1, PH))
            nd = w.s([nle, dl], 'mtod', '( %s -> -. ( 2 ^ %s ) || %s )' % (a1, H1, PH))
            o = w.s([w.s([eq], 'oveq1d', '( %s -> %s = %s )' % (a1, CR1, H1))], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (a1, CR1, H1))
            br = w.s([o, w.s([h1], 'eqcomd', '( %s -> %s = %s )' % (a1, PH, T1))], 'breq12d', '( %s -> ( ( 2 ^ %s ) || %s <-> ( 2 ^ %s ) || %s ) )' % (a1, CR1, PH, H1, T1))
            # nd is about ( 2 ^ H1 ) || PH ; we want -. ( 2 ^ CR1 ) || T1
            br2 = w.s([o, w.s([h1], 'eqcomd', '( %s -> %s = %s )' % (a1, PH, T1))], 'breq12d', '( %s -> ( ( 2 ^ %s ) || %s <-> ( 2 ^ %s ) || %s ) )' % (a1, CR1, PH, H1, T1)) if False else None
            # ( 2 ^ CR1 ) || T1  <->  ( 2 ^ H1 ) || PH : breq12d with o : 2^CR1 = 2^H1 and h1 : T1 = PH
            br3 = w.s([o, h1], 'breq12d', '( %s -> ( ( 2 ^ %s ) || %s <-> ( 2 ^ %s ) || %s ) )' % (a1, CR1, T1, H1, PH))
            return w.s([nd, br3], 'mtbird', '( %s -> -. ( 2 ^ %s ) || %s )' % (a1, CR1, T1))
        def bf(a2, h2, eq):
            tp = two_prime(w, a2)
            nd = w.s([tp, lift(w, cl.mem(T1, 'NN'), a2), w.inst('pcndvds')], 'syl2anc', '( %s -> -. ( 2 ^ ( %s + 1 ) ) || %s )' % (a2, PC, T1))
            o = w.s([w.s([eq], 'oveq1d', '( %s -> %s = ( %s + 1 ) )' % (a2, CR1, PC))], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ ( %s + 1 ) ) )' % (a2, CR1, PC))
            br = w.s([o], 'breq1d', '( %s -> ( ( 2 ^ %s ) || %s <-> ( 2 ^ ( %s + 1 ) ) || %s ) )' % (a2, CR1, T1, PC, T1))
            return w.s([nd, br], 'mtbird', '( %s -> -. ( 2 ^ %s ) || %s )' % (a2, CR1, T1))
        c = carries_cases(w, cl, AL, v, bt, bf, '-. ( 2 ^ %s ) || %s' % (CR1, T1))
        promote(w, c); w.run()
    if want('carriesnil'):
        w = W('carriesnil', 'The empty word has no carries.')
        V0 = CARV('( toNat ` (/) )', '( # ` (/) )')
        v0 = w.s([], 'carriesval', '( (/) e. Word 2o -> ( carries ` (/) ) = %s )' % V0)
        w0 = num.closed(w, [], 'wrd0', '(/) e. Word 2o')
        v1 = num.closed(w, [w0, v0], 'ax-mp', '( carries ` (/) ) = %s' % V0)
        vd = w.s([v1], 'a1i', '( T. -> ( carries ` (/) ) = %s )' % V0)
        t0 = w.s([num.closed(w, [], 'tonat0', '( toNat ` (/) ) = 0')], 'a1i', '( T. -> ( toNat ` (/) ) = 0 )')
        h0 = w.s([num.closed(w, [], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( T. -> ( # ` (/) ) = 0 )')
        p1 = w.s([num.closed(w, [], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( T. -> ( 0 + 1 ) = 1 )')
        tc = num.closed(w, [], '2cn', '2 e. CC'); e0 = num.closed(w, [tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( T. -> ( 2 ^ 0 ) = 1 )')
        st, cur = rewrite_chain(w, 'T.', V0, [{'( toNat ` (/) )': ('0', t0), '( # ` (/) )': ('0', h0)}, {'( 0 + 1 )': ('1', p1), '( 2 ^ 0 )': ('1', e0d)}])
        assert cur == 'if ( 1 = 1 , 0 , ( 2 pCnt 1 ) )', cur
        it = num.closed(w, [num.closed(w, [], 'eqid', '1 = 1')], 'iftruei', '%s = 0' % cur)
        itd = w.s([it], 'a1i', '( T. -> %s = 0 )' % cur)
        fin = w.s([vd, st, itd], '3eqtrd', '( T. -> ( carries ` (/) ) = 0 )')
        w.qed([fin], 'mptru', '( carries ` (/) ) = 0'); w.run()
    if want('carriescons0'):
        w = W('carriescons0', 'A word starting with false has no carries.')
        cl, l = base(w)
        L0, tc, ln = cons_setup(w, cl, AL, '(/)')
        T0 = TN(L0); H0 = LEN(L0); T01 = '( %s + 1 )' % T0
        b0, b1 = bn_lits(w, AL)
        for E in (T0, T, BN('(/)')):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        Sp = '( ( 2 x. %s ) + 1 )' % T
        eqS1 = lineq(w, AL, T01, Sp, hyps=[tc, b0], closure=cl)
        v = w.s([cl.mem(L0, 'Word 2o'), w.inst('carriesval')], 'syl', '( %s -> ( carries ` %s ) = %s )' % (AL, L0, CARV(T0, H0)))
        H1 = '( %s + 1 )' % H
        pe = w.s([ln], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (AL, H0, H1))
        ec = exp_p1c(w, cl, AL, H)
        pe2 = w.s([pe, ec], 'eqtrd', '( %s -> ( 2 ^ %s ) = ( 2 x. %s ) )' % (AL, H0, PH))
        ne = ne_from_oddne(w, cl, AL, T, PH)
        bi = w.s([eqS1, pe2], 'eqeq12d', '( %s -> ( %s = ( 2 ^ %s ) <-> %s = ( 2 x. %s ) ) )' % (AL, T01, H0, Sp, PH))
        nc = w.s([ne, bi], 'mtbird', '( %s -> -. %s = ( 2 ^ %s ) )' % (AL, T01, H0))
        i = w.s([nc], 'iffalsed', '( %s -> %s = ( 2 pCnt %s ) )' % (AL, CARV(T0, H0), T01))
        o = w.s([eqS1], 'oveq2d', '( %s -> ( 2 pCnt %s ) = ( 2 pCnt %s ) )' % (AL, T01, Sp))
        # ( 2 pCnt Sp ) = 0
        spn = w.s([cl.mem('( 2 x. %s )' % T, 'NN0'), w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (AL, Sp))
        pz = w.s([two_prime(w, AL), spn, w.inst('pceq0')], 'syl2anc', '( %s -> ( ( 2 pCnt %s ) = 0 <-> -. 2 || %s ) )' % (AL, Sp, Sp))
        od = w.s([cl.mem(T, 'ZZ'), w.s([], 'eqidd', '( %s -> %s = %s )' % (AL, Sp, Sp)), w.inst('2tp1odd')], 'syl2anc', '( %s -> -. 2 || %s )' % (AL, Sp))
        z = w.s([od, pz], 'mpbird', '( %s -> ( 2 pCnt %s ) = 0 )' % (AL, Sp))
        w.qed([v, i, o, z], '4eqtrd' if False else '3eqtrd', '') if False else None
        c1 = w.s([v, i, o], '3eqtrd', '( %s -> ( carries ` %s ) = ( 2 pCnt %s ) )' % (AL, L0, Sp))
        w.qed([c1, z], 'eqtrd', '( %s -> ( carries ` %s ) = 0 )' % (AL, L0)); w.run()
    if want('carriescons1'):
        w = W('carriescons1', 'A true letter in front adds one carry.')
        cl, l = base(w)
        L1, tc, ln = cons_setup(w, cl, AL, '1o')
        Tb = TN(L1); Hb = LEN(L1); Tb1 = '( %s + 1 )' % Tb
        b0, b1 = bn_lits(w, AL)
        for E in (Tb, T, BN('1o')):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        D2 = '( 2 x. %s )' % T1
        eqS2 = lineq(w, AL, Tb1, D2, hyps=[tc, b1], closure=cl)
        v = w.s([cl.mem(L1, 'Word 2o'), w.inst('carriesval')], 'syl', '( %s -> ( carries ` %s ) = %s )' % (AL, L1, CARV(Tb, Hb)))
        H1 = '( %s + 1 )' % H
        pe = w.s([ln], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (AL, Hb, H1))
        ec = exp_p1c(w, cl, AL, H)
        pe2 = w.s([pe, ec], 'eqtrd', '( %s -> ( 2 ^ %s ) = ( 2 x. %s ) )' % (AL, Hb, PH))
        bi1 = w.s([eqS2, pe2], 'eqeq12d', '( %s -> ( %s = ( 2 ^ %s ) <-> %s = ( 2 x. %s ) ) )' % (AL, Tb1, Hb, D2, PH))
        twoc = w.s([], '2cnd', '( %s -> 2 e. CC )' % AL); twone = w.s([num.closed(w, [], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % AL)
        mc = w.s([cl.mem(T1, 'CC'), cl.mem(PH, 'CC'), twoc, twone], 'mulcand', '( %s -> ( ( 2 x. %s ) = ( 2 x. %s ) <-> %s = %s ) )' % (AL, T1, PH, T1, PH))
        bi = w.s([bi1, mc], 'bitrd', '( %s -> ( %s = ( 2 ^ %s ) <-> %s ) )' % (AL, Tb1, Hb, COND))
        PCb = '( 2 pCnt %s )' % Tb1; PCD = '( 2 pCnt %s )' % D2; PC = '( 2 pCnt %s )' % T1
        ib = w.s([bi], 'ifbid', '( %s -> %s = if ( %s , %s , %s ) )' % (AL, CARV(Tb, Hb), COND, Hb, PCb))
        pcd = w.s([eqS2], 'oveq2d', '( %s -> %s = %s )' % (AL, PCb, PCD))
        ie = w.s([ln, pcd], 'ifeq12d', '( %s -> if ( %s , %s , %s ) = if ( %s , %s , %s ) )' % (AL, COND, Hb, PCb, COND, H1, PCD))
        VAL = 'if ( %s , %s , %s )' % (COND, H1, PCD)
        v2 = w.s([v, ib, ie], '3eqtrd', '( %s -> ( carries ` %s ) = %s )' % (AL, L1, VAL))
        cv = w.s([], 'carriesval', '( %s -> %s = %s )' % (AL, CR, CARVv))
        def bt(a1, h1, eq):
            i = w.s([h1], 'iftrued', '( %s -> %s = %s )' % (a1, VAL, H1))
            o = w.s([eq], 'oveq1d', '( %s -> ( %s + 1 ) = %s )' % (a1, CR, H1))
            return w.s([i, o], 'eqtr4d', '( %s -> %s = ( %s + 1 ) )' % (a1, VAL, CR))
        def bf(a2, h2, eq):
            i = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, VAL, PCD))
            tp = two_prime(w, a2)
            tz = w.s([num.closed(w, [], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % a2); tne = w.s([num.closed(w, [], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % a2)
            j2 = w.s([tz, tne], 'jca', '( %s -> ( 2 e. ZZ /\\ 2 =/= 0 ) )' % a2)
            t1z = lift(w, cl.mem(T1, 'ZZ'), a2); t1ne = w.s([lift(w, cl.mem(T1, 'NN'), a2)], 'nnne0d', '( %s -> %s =/= 0 )' % (a2, T1))
            jt = w.s([t1z, t1ne], 'jca', '( %s -> ( %s e. ZZ /\\ %s =/= 0 ) )' % (a2, T1, T1))
            pm = w.s([tp, j2, jt, w.inst('pcmul')], 'syl3anc', '( %s -> %s = ( ( 2 pCnt 2 ) + %s ) )' % (a2, PCD, PC))
            # ( 2 pCnt 2 ) = 1
            e1 = num.closed(w, [num.closed(w, [], '2cn', '2 e. CC'), w.inst('exp1')], 'ax-mp', '( 2 ^ 1 ) = 2')
            pi = num.closed(w, [num.closed(w, [], '2prm', '2 e. Prime'), num.closed(w, [], '1nn0', '1 e. NN0'), w.inst('pcidlem')], 'mp2an', '( 2 pCnt ( 2 ^ 1 ) ) = 1')
            oe = num.closed(w, [e1], 'oveq2i', '( 2 pCnt ( 2 ^ 1 ) ) = ( 2 pCnt 2 )')
            p21 = num.closed(w, [oe, pi], 'eqtr3i', '( 2 pCnt 2 ) = 1'); p21d = w.s([p21], 'a1i', '( %s -> ( 2 pCnt 2 ) = 1 )' % a2)
            o = w.s([p21d], 'oveq1d', '( %s -> ( ( 2 pCnt 2 ) + %s ) = ( 1 + %s ) )' % (a2, PC, PC))
            c2 = subcl(w, cl, AL, a2)
            ac = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % a2), c2.mem(PC, 'CC')], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (a2, PC, PC))
            oc = w.s([eq], 'oveq1d', '( %s -> ( %s + 1 ) = ( %s + 1 ) )' % (a2, CR, PC))
            ch = w.s([i, pm, o], '3eqtrd', '( %s -> %s = ( 1 + %s ) )' % (a2, VAL, PC))
            ch2 = w.s([ch, ac], 'eqtrd', '( %s -> %s = ( %s + 1 ) )' % (a2, VAL, PC))
            return w.s([ch2, oc], 'eqtr4d', '( %s -> %s = ( %s + 1 ) )' % (a2, VAL, CR))
        c = carries_cases(w, cl, AL, cv, bt, bf, '%s = ( %s + 1 )' % (VAL, CR))
        w.qed([v2, c], 'eqtrd', '( %s -> ( carries ` %s ) = ( %s + 1 ) )' % (AL, L1, CR)); w.run()

    # ---- incRest
    def increst_facts(w, cl, ante):
        """Q e. NN, D e. NN0 (and the facts behind them) under ante (first conjunct AL)"""
        lA = cl.mem('L', 'Word 2o')
        dv = w.s([lA, w.inst('carriesdvds')], 'syl', '( %s -> ( 2 ^ %s ) || %s )' % (ante, CR, T1))
        nd = w.s([cl.mem(T1, 'NN'), cl.mem(P2(CR), 'NN'), w.inst('nndivdvds')], 'syl2anc', '( %s -> ( ( 2 ^ %s ) || %s <-> %s e. NN ) )' % (ante, CR, T1, Q))
        qn = w.s([dv, nd], 'mpbid', '( %s -> %s e. NN )' % (ante, Q)); cl.have(Q, 'NN', qn)
        le1 = w.s([lA, w.inst('carriesle')], 'syl', '( %s -> %s <_ %s )' % (ante, CR, H))
        le2 = w.s([lA, w.inst('incbitslenge')], 'syl', '( %s -> %s <_ %s )' % (ante, H, NI))
        le = w.s([cl.mem(CR, 'RR'), cl.mem(H, 'RR'), cl.mem(NI, 'RR'), le1, le2], 'letrd', '( %s -> %s <_ %s )' % (ante, CR, NI))
        ns = w.s([cl.mem(CR, 'NN0'), cl.mem(NI, 'NN0'), w.inst('nn0sub')], 'syl2anc', '( %s -> ( %s <_ %s <-> %s e. NN0 ) )' % (ante, CR, NI, D))
        dn = w.s([le, ns], 'mpbid', '( %s -> %s e. NN0 )' % (ante, D)); cl.have(D, 'NN0', dn)
        return qn, dn, le
    if want('increstval'):
        w = W('increstval', 'Value of incRest: the digits of incBits L above the carry chain.')
        cl, l = base(w)
        st, val = defval(w, cl, 'df-increst', 'incRest', ['L']); assert val == BWRD(Q, D), val
        promote(w, st); w.run()
    if want('increstcl'):
        w = W('increstcl', 'Closure of incRest: a bit word.')
        cl, l = base(w)
        increst_facts(w, cl, AL)
        v = w.s([], 'increstval', '( %s -> %s = %s )' % (AL, IR, BWRD(Q, D)))
        w.qed([v, cl.mem(BWRD(Q, D), 'Word 2o')], 'eqeltrd', '( %s -> %s e. Word 2o )' % (AL, IR)); w.run()
    if want('increstlen'):
        w = W('increstlen', 'incRest L is at most one letter longer than L (Lean: incRest_length).')
        cl, l = base(w)
        increst_facts(w, cl, AL)
        v = w.s([], 'increstval', '( %s -> %s = %s )' % (AL, IR, BWRD(Q, D)))
        f = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AL, IR, BWRD(Q, D)))
        bl = w.s([cl.mem(Q, 'ZZ'), cl.mem(D, 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AL, BWRD(Q, D), D))
        e = w.s([f, bl], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (AL, IR, D))
        il = w.s([], 'incbitslen', '( %s -> %s <_ ( %s + 1 ) )' % (AL, NI, H))
        g = cl.ge0(CR)
        for E in (CR, NI, H):
            cl.leaf(E, 'RR', cl.mem(E, 'RR'))
        la = linarith(w, AL, [il, g], '%s <_ ( %s + 1 )' % (D, H), closure=cl)
        w.qed([e, la], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( %s + 1 ) )' % (AL, IR, H)); w.run()
    if want('incbitseq'):
        w = W('incbitseq', 'incBits L is the carry chain of false letters followed by incRest L (Lean: incBits_eq).')
        cl, l = base(w)
        qn, dn, le = increst_facts(w, cl, AL)
        v = w.s([], 'increstval', '( %s -> %s = %s )' % (AL, IR, BWRD(Q, D)))
        R0 = REP('(/)', CR); RHS = '( %s ++ %s )' % (R0, IR)
        ci = cl.mem(INC, 'Word 2o'); cr = cl.mem(RHS, 'Word 2o')
        # lengths
        lr = w.s([cl.mem(R0, 'Word 2o'), cl.mem(IR, 'Word 2o'), w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (AL, RHS, R0, IR))
        l0 = w.s([cl.mem('(/)', '_V'), cl.mem(CR, 'NN0'), w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AL, R0, CR))
        f = w.s([v], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AL, IR, BWRD(Q, D)))
        bl = w.s([cl.mem(Q, 'ZZ'), cl.mem(D, 'NN0'), w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AL, BWRD(Q, D), D))
        li = w.s([f, bl], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (AL, IR, D))
        ad = w.s([l0, li], 'oveq12d', '( %s -> ( ( # ` %s ) + ( # ` %s ) ) = ( %s + %s ) )' % (AL, R0, IR, CR, D))
        pc = w.s([cl.mem(CR, 'CC'), cl.mem(NI, 'CC')], 'pncan3d', '( %s -> ( %s + %s ) = %s )' % (AL, CR, D, NI))
        lr2 = w.s([lr, ad, pc], '3eqtrd', '( %s -> ( # ` %s ) = %s )' % (AL, RHS, NI))
        leneq = w.s([lr2], 'eqcomd', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AL, INC, RHS))
        # values
        ti = w.s([], 'tonatincbits', '( %s -> ( toNat ` %s ) = %s )' % (AL, INC, T1))
        tr = w.s([cl.mem(IR, 'Word 2o'), cl.mem(CR, 'NN0'), w.inst('tonatrep0a')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( 2 ^ %s ) x. ( toNat ` %s ) ) )' % (AL, RHS, CR, IR))
        fv = w.s([v], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AL, IR, BWRD(Q, D)))
        # Q < 2 ^ D
        ltI = w.s([ci, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` %s ) < ( 2 ^ %s ) )' % (AL, INC, NI))
        lt1 = w.s([ti, ltI], 'eqbrtrrd', '( %s -> %s < ( 2 ^ %s ) )' % (AL, T1, NI))
        pcr = w.s([pc], 'eqcomd', '( %s -> %s = ( %s + %s ) )' % (AL, NI, CR, D))
        o1 = w.s([pcr], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ ( %s + %s ) ) )' % (AL, NI, CR, D))
        ea = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % AL), cl.mem(CR, 'NN0'), cl.mem(D, 'NN0'), w.inst('expadd')], 'syl3anc', '( %s -> ( 2 ^ ( %s + %s ) ) = ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (AL, CR, D, CR, D))
        mc = w.s([cl.mem(P2(CR), 'CC'), cl.mem(P2(D), 'CC')], 'mulcomd', '( %s -> ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) = ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (AL, CR, D, D, CR))
        o2 = w.s([o1, ea, mc], '3eqtrd', '( %s -> ( 2 ^ %s ) = ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (AL, NI, D, CR))
        dc = w.s([cl.mem(T1, 'CC'), cl.mem(P2(CR), 'CC'), cl.ne0(P2(CR))], 'divcan1d', '( %s -> ( %s x. ( 2 ^ %s ) ) = %s )' % (AL, Q, CR, T1))
        lt2 = w.s([lt1, o2], 'breqtrd', '( %s -> %s < ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (AL, T1, D, CR))
        lt3 = w.s([dc, lt2], 'eqbrtrd', '( %s -> ( %s x. ( 2 ^ %s ) ) < ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (AL, Q, CR, D, CR))
        j3 = w.s([cl.mem(P2(CR), 'RR'), cl.gt0(P2(CR))], 'jca', '( %s -> ( ( 2 ^ %s ) e. RR /\\ 0 < ( 2 ^ %s ) ) )' % (AL, CR, CR))
        lm = w.s([cl.mem(Q, 'RR'), cl.mem(P2(D), 'RR'), j3, w.inst('ltmul1')], 'syl3anc', '( %s -> ( %s < ( 2 ^ %s ) <-> ( %s x. ( 2 ^ %s ) ) < ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) ) )' % (AL, Q, D, Q, CR, D, CR))
        ltQ = w.s([lt3, lm], 'mpbird', '( %s -> %s < ( 2 ^ %s ) )' % (AL, Q, D))
        tb = w.s([cl.mem(Q, 'NN0'), cl.mem(D, 'NN0'), ltQ, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (AL, BWRD(Q, D), Q))
        tir = w.s([fv, tb], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (AL, IR, Q))
        o3 = w.s([tir], 'oveq2d', '( %s -> ( ( 2 ^ %s ) x. ( toNat ` %s ) ) = ( ( 2 ^ %s ) x. %s ) )' % (AL, CR, IR, CR, Q))
        dc2 = w.s([cl.mem(T1, 'CC'), cl.mem(P2(CR), 'CC'), cl.ne0(P2(CR))], 'divcan2d', '( %s -> ( ( 2 ^ %s ) x. %s ) = %s )' % (AL, CR, Q, T1))
        tr2 = w.s([tr, o3, dc2], '3eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (AL, RHS, T1))
        veq = w.s([ti, tr2], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AL, INC, RHS))
        j = w.s([leneq, veq], 'jca', '( %s -> ( ( # ` %s ) = ( # ` %s ) /\\ ( toNat ` %s ) = ( toNat ` %s ) ) )' % (AL, INC, RHS, INC, RHS))
        u = w.s([ci, cr, w.inst('bwuniq')], 'syl2anc', '( %s -> ( %s = %s <-> ( ( # ` %s ) = ( # ` %s ) /\\ ( toNat ` %s ) = ( toNat ` %s ) ) ) )' % (AL, INC, RHS, INC, RHS, INC, RHS))
        w.qed([j, u], 'mpbird', '( %s -> %s = %s )' % (AL, INC, RHS)); w.run()

    # ---- the run decomposition
    RC = SWRD('L', CR, H)
    def dec_setup(w, cl, ante):
        """CR e. ( 0 ... H ), H e. ( 0 ... H )"""
        lA = cl.mem('L', 'Word 2o')
        le1 = w.s([lA, w.inst('carriesle')], 'syl', '( %s -> %s <_ %s )' % (ante, CR, H))
        cfz = w.s([cl.mem(CR, 'NN0'), cl.mem(H, 'NN0'), le1, w.inst('elfz2nn0')], 'syl3anbrc', '( %s -> %s e. ( 0 ... %s ) )' % (ante, CR, H))
        hle = w.s([cl.mem(H, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (ante, H, H))
        hfz = w.s([cl.mem(H, 'NN0'), cl.mem(H, 'NN0'), hle, w.inst('elfz2nn0')], 'syl3anbrc', '( %s -> %s e. ( 0 ... %s ) )' % (ante, H, H))
        return le1, cfz, hfz
    NT1 = '( -u %s - 1 )' % T
    def negfacts(w, cl, ante):
        """( -u T - 1 ) e. ZZ, and ( 2 ^ CR ) || ( -u T - 1 )"""
        lA = cl.mem('L', 'Word 2o')
        nz = w.s([cl.mem('-u %s' % T, 'ZZ'), w.s([num.closed(w, [], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % ante)], 'zsubcld', '( %s -> %s e. ZZ )' % (ante, NT1))
        cl.have(NT1, 'ZZ', nz)
        dv = w.s([lA, w.inst('carriesdvds')], 'syl', '( %s -> ( 2 ^ %s ) || %s )' % (ante, CR, T1))
        nb = w.s([cl.mem(P2(CR), 'ZZ'), cl.mem(T1, 'ZZ'), w.inst('dvdsnegb')], 'syl2anc', '( %s -> ( ( 2 ^ %s ) || %s <-> ( 2 ^ %s ) || -u %s ) )' % (ante, CR, T1, CR, T1))
        dv2 = w.s([dv, nb], 'mpbid', '( %s -> ( 2 ^ %s ) || -u %s )' % (ante, CR, T1))
        nd = w.s([cl.mem(T, 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % ante), w.inst('negdi2')], 'syl2anc', '( %s -> -u %s = %s )' % (ante, T1, NT1))
        dv3 = w.s([dv2, nd], 'breqtrd', '( %s -> ( 2 ^ %s ) || %s )' % (ante, CR, NT1))
        return nz, dv3
    if want('bwcarriesdec1'):
        w = W('bwcarriesdec1', 'The run decomposition of the carry chain: L is its carries true letters followed by the rest.')
        cl, l = base(w)
        le1, cfz, hfz = dec_setup(w, cl, AL)
        Pf = PFX('L', CR); R1 = REP('1o', CR)
        cp = w.s([l, cfz, hfz, w.inst('ccatpfx')], 'syl3anc', '( %s -> ( %s ++ %s ) = %s )' % (AL, Pf, RC, PFX('L', H)))
        pid = w.s([l, w.inst('pfxid')], 'syl', '( %s -> %s = L )' % (AL, PFX('L', H)))
        sp = w.s([cp, pid], 'eqtrd', '( %s -> ( %s ++ %s ) = L )' % (AL, Pf, RC))
        # ( L prefix CR ) = ( 1o repeatS CR )
        pw = cl.mem(Pf, 'Word 2o')
        pl = w.s([l, cfz, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (AL, Pf, CR))
        nz, dv3 = negfacts(w, cl, AL)
        bu = w.s([nz, cl.mem(CR, 'NN0'), w.inst('bitsuz')], 'syl2anc', '( %s -> ( ( 2 ^ %s ) || %s <-> ( bits ` %s ) C_ ( ZZ>= ` %s ) ) )' % (AL, CR, NT1, NT1, CR))
        ss = w.s([dv3, bu], 'mpbid', '( %s -> ( bits ` %s ) C_ ( ZZ>= ` %s ) )' % (AL, NT1, CR))
        bc = w.s([cl.mem(T, 'ZZ'), w.inst('bitscmp')], 'syl', '( %s -> ( NN0 \\ ( bits ` %s ) ) = ( bits ` %s ) )' % (AL, T, NT1))
        a2 = '( %s /\\ i e. ( 0 ..^ %s ) )' % (AL, CR)
        ist = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (a2, CR))
        pf = w.s([lift(w, l, a2), lift(w, cfz, a2), ist, w.inst('pfxfv')], 'syl3anc', '( %s -> ( %s ` i ) = ( L ` i ) )' % (a2, Pf))
        inn = w.s([ist, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % a2)
        ilt = w.s([ist, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (a2, CR))
        c2 = subcl(w, cl, AL, a2); c2.have('i', 'NN0', inn)
        ilt2 = w.s([c2.mem('i', 'RR'), lift(w, cl.mem(CR, 'RR'), a2), lift(w, cl.mem(H, 'RR'), a2), ilt, lift(w, le1, a2)], 'ltletrd', '( %s -> i < %s )' % (a2, H))
        ih = w.s([inn, lift(w, cl.mem(H, 'ZZ'), a2), ilt2, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> i e. ( 0 ..^ %s ) )' % (a2, H))
        fb = w.s([lift(w, l, a2), ih, w.inst('bwfvb')], 'syl2anc', '( %s -> ( ( L ` i ) = 1o <-> i e. ( bits ` %s ) ) )' % (a2, T))
        # i e. bits T
        nl = w.s([c2.mem('i', 'RR'), lift(w, cl.mem(CR, 'RR'), a2)], 'ltnled', '( %s -> ( i < %s <-> -. %s <_ i ) )' % (a2, CR, CR))
        nle = w.s([ilt, nl], 'mpbid', '( %s -> -. %s <_ i )' % (a2, CR))
        sd = w.s([lift(w, ss, a2)], 'sseld', '( %s -> ( i e. ( bits ` %s ) -> i e. ( ZZ>= ` %s ) ) )' % (a2, NT1, CR))
        ul = w.s([sd, w.inst('eluzle')], 'syl6', '( %s -> ( i e. ( bits ` %s ) -> %s <_ i ) )' % (a2, NT1, CR))
        nel = w.s([nle, ul], 'mtod', '( %s -> -. i e. ( bits ` %s ) )' % (a2, NT1))
        ed = w.s([inn, nel], 'eldifd', '( %s -> i e. ( NN0 \\ ( bits ` %s ) ) )' % (a2, NT1))
        bcr = w.s([bc], 'eqcomd', '( %s -> ( bits ` %s ) = ( NN0 \\ ( bits ` %s ) ) )' % (AL, NT1, T))
        d2 = w.s([bcr], 'difeq2d', '( %s -> ( NN0 \\ ( bits ` %s ) ) = ( NN0 \\ ( NN0 \\ ( bits ` %s ) ) ) )' % (AL, NT1, T))
        ssb = w.s([num.closed(w, [], 'bitsss', '( bits ` %s ) C_ NN0' % T)], 'a1i', '( %s -> ( bits ` %s ) C_ NN0 )' % (AL, T))
        d4 = w.s([ssb, w.inst('dfss4')], 'sylib', '( %s -> ( NN0 \\ ( NN0 \\ ( bits ` %s ) ) ) = ( bits ` %s ) )' % (AL, T, T))
        bc2 = w.s([d2, d4], 'eqtrd', '( %s -> ( NN0 \\ ( bits ` %s ) ) = ( bits ` %s ) )' % (AL, NT1, T))
        eb = w.s([ed, lift(w, bc2, a2)], 'eleqtrd', '( %s -> i e. ( bits ` %s ) )' % (a2, T))
        one = w.s([eb, fb], 'mpbird', '( %s -> ( L ` i ) = 1o )' % a2)
        lt = w.s([pf, one], 'eqtrd', '( %s -> ( %s ` i ) = 1o )' % (a2, Pf))
        al = w.s([lt], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ %s ) ( %s ` i ) = 1o )' % (AL, CR, Pf))
        j = w.s([pw, pl, al], '3jca', '( %s -> ( %s e. Word 2o /\\ ( # ` %s ) = %s /\\ A. i e. ( 0 ..^ %s ) ( %s ` i ) = 1o ) )' % (AL, Pf, Pf, CR, CR, Pf))
        one2 = w.s([num.closed(w, [], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % AL)
        df = w.s([one2, cl.mem(CR, 'NN0'), w.inst('repsdf2')], 'syl2anc', '( %s -> ( %s = %s <-> ( %s e. Word 2o /\\ ( # ` %s ) = %s /\\ A. i e. ( 0 ..^ %s ) ( %s ` i ) = 1o ) ) )' % (AL, Pf, R1, Pf, Pf, CR, CR, Pf))
        pe = w.s([j, df], 'mpbird', '( %s -> %s = %s )' % (AL, Pf, R1))
        o = w.s([pe], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (AL, Pf, RC, R1, RC))
        fin = w.s([o, sp], 'eqtr3d', '( %s -> ( %s ++ %s ) = L )' % (AL, R1, RC))
        w.qed([fin], 'eqcomd', '( %s -> L = ( %s ++ %s ) )' % (AL, R1, RC)); w.run()
    if want('bwcarriesdec2'):
        A2 = '( %s /\\ %s =/= (/) )' % (AL, RC)
        w = W('bwcarriesdec2', 'The run decomposition of the carry chain: the rest, when not empty, starts with a false letter.')
        cl, l = base(w, A2)
        hne = w.s([], 'simpr', '( %s -> %s =/= (/) )' % (A2, RC))
        le1, cfz, hfz = dec_setup(w, cl, A2)
        # CR < H
        sl = w.s([l, cfz, hfz, w.inst('swrdlen')], 'syl3anc', '( %s -> ( # ` %s ) = ( %s - %s ) )' % (A2, RC, H, CR))
        rv = w.s([cl.mem(RC, 'Word 2o')], 'elexd', '( %s -> %s e. _V )' % (A2, RC))
        hq = w.s([rv, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` %s ) = 0 <-> %s = (/) ) )' % (A2, RC, RC))
        nn = w.s([hne], 'neneqd', '( %s -> -. %s = (/) )' % (A2, RC))
        n0 = w.s([nn, hq], 'mtbird', '( %s -> -. ( # ` %s ) = 0 )' % (A2, RC))
        n0b = w.s([n0], 'neqned', '( %s -> ( # ` %s ) =/= 0 )' % (A2, RC))
        n0c = w.s([sl, n0b], 'eqnetrrd', '( %s -> ( %s - %s ) =/= 0 )' % (A2, H, CR))
        ns = w.s([cl.mem(CR, 'NN0'), cl.mem(H, 'NN0'), w.inst('nn0sub')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( %s - %s ) e. NN0 ) )' % (A2, CR, H, H, CR))
        dn = w.s([le1, ns], 'mpbid', '( %s -> ( %s - %s ) e. NN0 )' % (A2, H, CR))
        dnn = w.s([dn, n0c, w.inst('elnnne0')], 'sylanbrc', '( %s -> ( %s - %s ) e. NN )' % (A2, H, CR))
        gt = w.s([dnn], 'nngt0d', '( %s -> 0 < ( %s - %s ) )' % (A2, H, CR))
        pd = w.s([cl.mem(CR, 'RR'), cl.mem(H, 'RR')], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A2, CR, H, H, CR))
        lt = w.s([gt, pd], 'mpbird', '( %s -> %s < %s )' % (A2, CR, H))
        cfo = w.s([cl.mem(CR, 'NN0'), cl.mem(H, 'ZZ'), lt, w.inst('elfzo0z')], 'syl3anbrc', '( %s -> %s e. ( 0 ..^ %s ) )' % (A2, CR, H))
        f0 = w.s([l, cfo, hfz, w.inst('swrdfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = ( L ` %s ) )' % (A2, RC, CR))
        # -. 2 || Q
        dv = w.s([l, w.inst('carriesdvds')], 'syl', '( %s -> ( 2 ^ %s ) || %s )' % (A2, CR, T1))
        ndq = w.s([cl.mem(T1, 'NN'), cl.mem(P2(CR), 'NN'), w.inst('nndivdvds')], 'syl2anc', '( %s -> ( ( 2 ^ %s ) || %s <-> %s e. NN ) )' % (A2, CR, T1, Q))
        qn = w.s([dv, ndq], 'mpbid', '( %s -> %s e. NN )' % (A2, Q)); cl.have(Q, 'NN', qn)
        nd = w.s([l, w.inst('carriesndvds')], 'syl', '( %s -> -. ( 2 ^ ( %s + 1 ) ) || %s )' % (A2, CR, T1))
        a3 = '( %s /\\ 2 || %s )' % (A2, Q)
        h3 = w.s([], 'simpr', '( %s -> 2 || %s )' % (a3, Q))
        c3 = subcl(w, cl, A2, a3)
        tz = w.s([num.closed(w, [], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % a3)
        dcm = w.s([tz, lift(w, cl.mem(Q, 'ZZ'), a3), lift(w, cl.mem(P2(CR), 'ZZ'), a3), w.inst('dvdscmul')], 'syl3anc', '( %s -> ( 2 || %s -> ( ( 2 ^ %s ) x. 2 ) || ( ( 2 ^ %s ) x. %s ) ) )' % (a3, Q, CR, CR, Q))
        d3 = w.s([h3, dcm], 'mpd', '( %s -> ( ( 2 ^ %s ) x. 2 ) || ( ( 2 ^ %s ) x. %s ) )' % (a3, CR, CR, Q))
        ep = exp_p1(w, c3, a3, CR)
        dc2 = w.s([lift(w, cl.mem(T1, 'CC'), a3), lift(w, cl.mem(P2(CR), 'CC'), a3), lift(w, cl.ne0(P2(CR)), a3)], 'divcan2d', '( %s -> ( ( 2 ^ %s ) x. %s ) = %s )' % (a3, CR, Q, T1))
        dc2r = w.s([dc2], 'eqcomd', '( %s -> %s = ( ( 2 ^ %s ) x. %s ) )' % (a3, T1, CR, Q))
        br = w.s([ep, dc2r], 'breq12d', '( %s -> ( ( 2 ^ ( %s + 1 ) ) || %s <-> ( ( 2 ^ %s ) x. 2 ) || ( ( 2 ^ %s ) x. %s ) ) )' % (a3, CR, T1, CR, CR, Q))
        d4 = w.s([d3, br], 'mpbird', '( %s -> ( 2 ^ ( %s + 1 ) ) || %s )' % (a3, CR, T1))
        nq = w.s([d4, lift(w, nd, a3)], 'pm2.65da', '( %s -> -. 2 || %s )' % (A2, Q))
        # CR e. bits ( -u T - 1 )
        nz, dv3 = negfacts(w, cl, A2)
        bv = w.s([nz, cl.mem(CR, 'NN0'), w.inst('bitsval2')], 'syl2anc', '( %s -> ( %s e. ( bits ` %s ) <-> -. 2 || ( |_ ` ( %s / ( 2 ^ %s ) ) ) ) )' % (A2, CR, NT1, NT1, CR))
        nd2 = w.s([cl.mem(T, 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % A2), w.inst('negdi2')], 'syl2anc', '( %s -> -u %s = %s )' % (A2, T1, NT1))
        o1 = w.s([w.s([nd2], 'eqcomd', '( %s -> %s = -u %s )' % (A2, NT1, T1))], 'oveq1d', '( %s -> ( %s / ( 2 ^ %s ) ) = ( -u %s / ( 2 ^ %s ) ) )' % (A2, NT1, CR, T1, CR))
        dvn = w.s([cl.mem(T1, 'CC'), cl.mem(P2(CR), 'CC'), cl.ne0(P2(CR))], 'divnegd', '( %s -> -u %s = ( -u %s / ( 2 ^ %s ) ) )' % (A2, Q, T1, CR))
        o2 = w.s([o1, dvn], 'eqtr4d', '( %s -> ( %s / ( 2 ^ %s ) ) = -u %s )' % (A2, NT1, CR, Q))
        f = w.s([o2], 'fveq2d', '( %s -> ( |_ ` ( %s / ( 2 ^ %s ) ) ) = ( |_ ` -u %s ) )' % (A2, NT1, CR, Q))
        fi = w.s([cl.mem('-u %s' % Q, 'ZZ'), w.inst('flid')], 'syl', '( %s -> ( |_ ` -u %s ) = -u %s )' % (A2, Q, Q))
        f2 = w.s([f, fi], 'eqtrd', '( %s -> ( |_ ` ( %s / ( 2 ^ %s ) ) ) = -u %s )' % (A2, NT1, CR, Q))
        nb = w.s([w.s([num.closed(w, [], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A2), cl.mem(Q, 'ZZ'), w.inst('dvdsnegb')], 'syl2anc', '( %s -> ( 2 || %s <-> 2 || -u %s ) )' % (A2, Q, Q))
        nq2 = w.s([nq, nb], 'mtbid', '( %s -> -. 2 || -u %s )' % (A2, Q))
        br2 = w.s([f2], 'breq2d', '( %s -> ( 2 || ( |_ ` ( %s / ( 2 ^ %s ) ) ) <-> 2 || -u %s ) )' % (A2, NT1, CR, Q))
        nq3 = w.s([nq2, br2], 'mtbird', '( %s -> -. 2 || ( |_ ` ( %s / ( 2 ^ %s ) ) ) )' % (A2, NT1, CR))
        eb = w.s([nq3, bv], 'mpbird', '( %s -> %s e. ( bits ` %s ) )' % (A2, CR, NT1))
        bc = w.s([cl.mem(T, 'ZZ'), w.inst('bitscmp')], 'syl', '( %s -> ( NN0 \\ ( bits ` %s ) ) = ( bits ` %s ) )' % (A2, T, NT1))
        bcr = w.s([bc], 'eqcomd', '( %s -> ( bits ` %s ) = ( NN0 \\ ( bits ` %s ) ) )' % (A2, NT1, T))
        el = w.s([eb, bcr], 'eleqtrd', '( %s -> %s e. ( NN0 \\ ( bits ` %s ) ) )' % (A2, CR, T))
        nel2 = w.s([el, w.inst('eldifn')], 'syl', '( %s -> -. %s e. ( bits ` %s ) )' % (A2, CR, T))
        fb = w.s([l, cfo, w.inst('bwfvb')], 'syl2anc', '( %s -> ( ( L ` %s ) = 1o <-> %s e. ( bits ` %s ) ) )' % (A2, CR, CR, T))
        n1 = w.s([nel2, fb], 'mtbird', '( %s -> -. ( L ` %s ) = 1o )' % (A2, CR))
        sym = w.s([l, cfo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` %s ) e. 2o )' % (A2, CR))
        e2 = w.s([sym, w.inst('bwel2on')], 'syl', '( %s -> ( -. ( L ` %s ) = 1o <-> ( L ` %s ) = (/) ) )' % (A2, CR, CR))
        z = w.s([n1, e2], 'mpbid', '( %s -> ( L ` %s ) = (/) )' % (A2, CR))
        w.qed([f0, z], 'eqtrd', '( %s -> ( %s ` 0 ) = (/) )' % (A2, RC)); w.run()
    if want('bwcarriesdec'):
        w = W('bwcarriesdec', 'The run decomposition of the carry chain (the interface incLoop reads): L is carries true letters followed by a rest that is empty or starts with false.')
        d1 = w.s([], 'bwcarriesdec1', '( %s -> L = ( %s ++ %s ) )' % (AL, REP('1o', CR), RC))
        d2 = w.s([], 'bwcarriesdec2', '( ( %s /\\ %s =/= (/) ) -> ( %s ` 0 ) = (/) )' % (AL, RC, RC))
        d2e = w.s([d2], 'ex', '( %s -> ( %s =/= (/) -> ( %s ` 0 ) = (/) ) )' % (AL, RC, RC))
        w.qed([d1, d2e], 'jca', '( %s -> ( L = ( %s ++ %s ) /\\ ( %s =/= (/) -> ( %s ` 0 ) = (/) ) ) )' % (AL, REP('1o', CR), RC, RC, RC)); w.run()

    if want('encnatsuc'):
        AN = 'N e. NN0'
        w = W('encnatsuc', 'encodeNat commutes with the successor: encodeNat ( N + 1 ) is incBits of encodeNat N (Lean: encodeNat_succ).')
        n = w.s([], 'id', '( %s -> N e. NN0 )' % AN)
        cl = Cl(w, AN, {'N': ('NN0', n)})
        E = '( encodeNat ` N )'; N1 = '( N + 1 )'; E1 = '( encodeNat ` %s )' % N1; I = '( incBits ` %s )' % E
        BL = '( bl ` N )'; BL1 = '( bl ` %s )' % N1
        ce = cl.mem(E, 'Word 2o'); ce1 = cl.mem(E1, 'Word 2o'); ci = cl.mem(I, 'Word 2o')
        n1n = cl.mem(N1, 'NN0')
        te = w.s([], 'tonatencnat', '( %s -> ( toNat ` %s ) = N )' % (AN, E))
        te1 = w.s([n1n, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = %s )' % (AN, E1, N1))
        ti = w.s([ce, w.inst('tonatincbits')], 'syl', '( %s -> ( toNat ` %s ) = ( ( toNat ` %s ) + 1 ) )' % (AN, I, E))
        o = w.s([te], 'oveq1d', '( %s -> ( ( toNat ` %s ) + 1 ) = %s )' % (AN, E, N1))
        ti2 = w.s([ti, o], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (AN, I, N1))
        veq = w.s([te1, ti2], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (AN, E1, I))
        # lengths
        le1 = w.s([n1n, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = %s )' % (AN, E1, BL1))
        lE = w.s([], 'encnatlenbl', '( %s -> ( # ` %s ) = %s )' % (AN, E, BL))
        li = w.s([ce, w.inst('incbitslen2')], 'syl', '( %s -> ( # ` %s ) = %s )' % (AN, I, MI(TN(E), LEN(E))))
        st, cur = w.rewrite(MI(TN(E), LEN(E)), {TN(E): ('N', te), LEN(E): (BL, lE)}, AN)
        MIN = MI('N', BL)
        assert cur == MIN, cur
        li2 = w.s([li, st], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (AN, I, MIN))
        CN = '%s = ( 2 ^ %s )' % (N1, BL)
        bl = w.s([], 'blcl', '( %s -> %s e. NN0 )' % (AN, BL)); cl.have(BL, 'NN0', bl)
        def bt(a1, h1):
            i = w.s([h1], 'iftrued', '( %s -> %s = ( %s + 1 ) )' % (a1, MIN, BL))
            f = w.s([h1], 'fveq2d', '( %s -> %s = ( bl ` ( 2 ^ %s ) ) )' % (a1, BL1, BL))
            b2 = w.s([lift(w, bl, a1), w.inst('blp2')], 'syl', '( %s -> ( bl ` ( 2 ^ %s ) ) = ( %s + 1 ) )' % (a1, BL, BL))
            f2 = w.s([f, b2], 'eqtrd', '( %s -> %s = ( %s + 1 ) )' % (a1, BL1, BL))
            return w.s([f2, i], 'eqtr4d', '( %s -> %s = %s )' % (a1, BL1, MIN))
        def bf(a2, h2):
            i = w.s([h2], 'iffalsed', '( %s -> %s = %s )' % (a2, MIN, BL))
            c2 = subcl(w, cl, AN, a2)
            # N =/= 0
            a3 = '( %s /\\ N = 0 )' % a2
            h3 = w.s([], 'simpr', '( %s -> N = 0 )' % a3)
            o1 = w.s([h3], 'oveq1d', '( %s -> %s = ( 0 + 1 ) )' % (a3, N1))
            p1 = w.s([num.closed(w, [], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % a3)
            o1b = w.s([o1, p1], 'eqtrd', '( %s -> %s = 1 )' % (a3, N1))
            f3 = w.s([h3], 'fveq2d', '( %s -> %s = ( bl ` 0 ) )' % (a3, BL))
            b0 = w.s([num.closed(w, [], 'bl0', '( bl ` 0 ) = 0')], 'a1i', '( %s -> ( bl ` 0 ) = 0 )' % a3)
            f3b = w.s([f3, b0], 'eqtrd', '( %s -> %s = 0 )' % (a3, BL))
            o3 = w.s([f3b], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ 0 ) )' % (a3, BL))
            e0 = num.closed(w, [num.closed(w, [], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % a3)
            o3b = w.s([o3, e0d], 'eqtrd', '( %s -> ( 2 ^ %s ) = 1 )' % (a3, BL))
            cn = w.s([o1b, o3b], 'eqtr4d', '( %s -> %s )' % (a3, CN))
            nn0 = w.s([cn, lift(w, h2, a3)], 'pm2.65da', '( %s -> -. N = 0 )' % a2)
            ne = w.s([nn0], 'neqned', '( %s -> N =/= 0 )' % a2)
            nnn = w.s([lift(w, n, a2), ne, w.inst('elnnne0')], 'sylanbrc', '( %s -> N e. NN )' % a2)
            c2.have('N', 'NN', nnn)
            # bl N e. NN
            bp = w.s([nnn, w.inst('blpos')], 'syl', '( %s -> %s = ( ( 2 Nlog N ) + 1 ) )' % (a2, BL))
            bln = w.s([bp, c2.mem('( ( 2 Nlog N ) + 1 )', 'NN')], 'eqeltrd', '( %s -> %s e. NN )' % (a2, BL)); c2.have(BL, 'NN', bln)
            n1nn = c2.mem(N1, 'NN')
            # 2 ^ ( bl N - 1 ) <_ N + 1
            l2 = w.s([nnn, w.inst('blle2')], 'syl', '( %s -> ( 2 ^ ( %s - 1 ) ) <_ N )' % (a2, BL))
            lp = w.s([c2.mem('N', 'RR')], 'lep1d', '( %s -> N <_ %s )' % (a2, N1))
            h1s = w.s([c2.mem('( 2 ^ ( %s - 1 ) )' % BL, 'RR'), c2.mem('N', 'RR'), c2.mem(N1, 'RR'), l2, lp], 'letrd', '( %s -> ( 2 ^ ( %s - 1 ) ) <_ %s )' % (a2, BL, N1))
            # N + 1 < 2 ^ bl N
            p2 = w.s([lift(w, n, a2), w.inst('blpow2')], 'syl', '( %s -> N < ( 2 ^ %s ) )' % (a2, BL))
            zl = w.s([c2.mem('N', 'ZZ'), c2.mem(P2(BL), 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( N < ( 2 ^ %s ) <-> %s <_ ( 2 ^ %s ) ) )' % (a2, BL, N1, BL))
            le = w.s([p2, zl], 'mpbid', '( %s -> %s <_ ( 2 ^ %s ) )' % (a2, N1, BL))
            ne2 = w.s([h2], 'neqned', '( %s -> %s =/= ( 2 ^ %s ) )' % (a2, N1, BL)); ne3 = w.s([ne2], 'necomd', '( %s -> ( 2 ^ %s ) =/= %s )' % (a2, BL, N1))
            j = w.s([le, ne3], 'jca', '( %s -> ( %s <_ ( 2 ^ %s ) /\\ ( 2 ^ %s ) =/= %s ) )' % (a2, N1, BL, BL, N1))
            ll = w.s([c2.mem(N1, 'RR'), c2.mem(P2(BL), 'RR'), w.inst('ltlen')], 'syl2anc', '( %s -> ( %s < ( 2 ^ %s ) <-> ( %s <_ ( 2 ^ %s ) /\\ ( 2 ^ %s ) =/= %s ) ) )' % (a2, N1, BL, N1, BL, BL, N1))
            h2s = w.s([j, ll], 'mpbird', '( %s -> %s < ( 2 ^ %s ) )' % (a2, N1, BL))
            j1 = w.s([n1nn, bln], 'jca', '( %s -> ( %s e. NN /\\ %s e. NN ) )' % (a2, N1, BL))
            j2 = w.s([h1s, h2s], 'jca', '( %s -> ( ( 2 ^ ( %s - 1 ) ) <_ %s /\\ %s < ( 2 ^ %s ) ) )' % (a2, BL, N1, N1, BL))
            bc = w.s([j1, j2, w.inst('blchar')], 'syl2anc', '( %s -> %s = %s )' % (a2, BL1, BL))
            return w.s([bc, i], 'eqtr4d', '( %s -> %s = %s )' % (a2, BL1, MIN))
        c = cases_if(w, AN, CN, bt, bf, '%s = %s' % (BL1, MIN))
        leneq = w.s([le1, c, li2], '3eqtr4d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (AN, E1, I))
        j = w.s([leneq, veq], 'jca', '( %s -> ( ( # ` %s ) = ( # ` %s ) /\\ ( toNat ` %s ) = ( toNat ` %s ) ) )' % (AN, E1, I, E1, I))
        u = w.s([ce1, ci, w.inst('bwuniq')], 'syl2anc', '( %s -> ( %s = %s <-> ( ( # ` %s ) = ( # ` %s ) /\\ ( toNat ` %s ) = ( toNat ` %s ) ) ) )' % (AN, E1, I, E1, I, E1, I))
        w.qed([j, u], 'mpbird', '( %s -> %s = %s )' % (AN, E1, I)); w.run()
