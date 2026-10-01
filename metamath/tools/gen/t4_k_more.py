"""Sortie T4, group K: the empty and cons clauses, zeroBits, toNat = 0, the letter map bits (T4-blueprint 3.3, 3.6, 3.7)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
from lin import linarith, lineq
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


AC = 'C e. 2o'
E0 = '(/)'
H0 = '( # ` (/) )'


def nilsetup(w, ante, kc='2o'):
    """steps for X = Y = (/): tonat0, hash0, max = 0"""
    t0 = w.s([], 'tonat0', '( toNat ` (/) ) = 0'); t0d = w.s([t0], 'a1i', '( %s -> ( toNat ` (/) ) = 0 )' % ante)
    h0 = w.s([], 'hash0', '( # ` (/) ) = 0'); h0d = w.s([h0], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ante)
    MX0 = 'if ( %s <_ %s , %s , %s )' % (H0, H0, H0, H0)
    ii = w.s([], 'ifid', '%s = %s' % (MX0, H0)); mx = w.s([ii, h0], 'eqtri', '%s = 0' % MX0); mxd = w.s([mx], 'a1i', '( %s -> %s = 0 )' % (ante, MX0))
    return t0d, h0d, mxd, MX0


if __name__ == '__main__':
    if want('addbitsnil'):
        w = W('addbitsnil', 'Lean clause 1 of addBits: the sum of two empty words is the carry word.')
        c = w.s([], 'id', '( %s -> C e. 2o )' % AC); cl = Cl(w, AC, {'C': ('2o', c)})
        e = w.s([], 'wrd0', '(/) e. Word 2o'); ed = w.s([e], 'a1i', '( %s -> (/) e. Word 2o )' % AC)
        v = w.s([ed, ed, c, w.inst('addbitsval')], 'syl3anc', '( %s -> ( ( (/) addBits (/) ) ` C ) = %s )' % (AC, '( ( %s bwrd %s ) ++ ( addCarry ` if ( ( 2 ^ %s ) <_ %s , 1o , (/) ) ) )' % (SUM(E0, E0, 'C'), MAX(E0, E0), MAX(E0, E0), SUM(E0, E0, 'C'))))
        t0d, h0d, mxd, MX0 = nilsetup(w, AC)
        z = w.s([t0d, t0d], 'oveq12d', '( %s -> ( ( toNat ` (/) ) + ( toNat ` (/) ) ) = ( 0 + 0 ) )' % AC); z0 = w.s([], '00id', '( 0 + 0 ) = 0'); z2 = w.s([z, z0], 'eqtrdi', '( %s -> ( ( toNat ` (/) ) + ( toNat ` (/) ) ) = 0 )' % AC)
        sm = w.s([z2], 'oveq1d', '( %s -> %s = ( 0 + ( bToNat ` C ) ) )' % (AC, SUM(E0, E0, 'C'))); bc = cl.mem('( bToNat ` C )', 'CC'); sm2 = w.s([sm, w.s([bc], 'addlidd', '( %s -> ( 0 + ( bToNat ` C ) ) = ( bToNat ` C ) )' % AC)], 'eqtrd', '( %s -> %s = ( bToNat ` C ) )' % (AC, SUM(E0, E0, 'C')))
        rules = {SUM(E0, E0, 'C'): ('( bToNat ` C )', sm2), MX0: ('0', mxd)}
        st, new = w.rewrite('( ( %s bwrd %s ) ++ ( addCarry ` if ( ( 2 ^ %s ) <_ %s , 1o , (/) ) ) )' % (SUM(E0, E0, 'C'), MX0, MX0, SUM(E0, E0, 'C')), rules, AC)
        assert new == '( ( ( bToNat ` C ) bwrd 0 ) ++ ( addCarry ` if ( ( 2 ^ 0 ) <_ ( bToNat ` C ) , 1o , (/) ) ) )', new
        bz = cl.mem('( bToNat ` C )', 'ZZ'); b0 = w.s([bz, w.inst('bwrd0')], 'syl', '( %s -> ( ( bToNat ` C ) bwrd 0 ) = (/) )' % AC)
        tc = w.s([], '2cn', '2 e. CC'); e0 = w.s([tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); e0d = w.s([e0], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % AC)
        br = w.s([e0d], 'breq1d', '( %s -> ( ( 2 ^ 0 ) <_ ( bToNat ` C ) <-> 1 <_ ( bToNat ` C ) ) )' % AC)
        BNC = '( bToNat ` C )'
        bnle = w.s([c, w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AC, BNC)); bnr = cl.mem(BNC, 'RR'); onr = w.s([], '1red', '( %s -> 1 e. RR )' % AC)
        t3 = w.s([onr, bnr, w.inst('letri3')], 'syl2anc', '( %s -> ( 1 = %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AC, BNC, BNC, BNC))
        bt = w.s([bnle], 'biantrud', '( %s -> ( 1 <_ %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AC, BNC, BNC, BNC))
        b13 = w.s([bt, t3], 'bitr4d', '( %s -> ( 1 <_ %s <-> 1 = %s ) )' % (AC, BNC, BNC))
        ec = w.s([], 'eqcom', '( 1 = %s <-> %s = 1 )' % (BNC, BNC)); ecd = w.s([ec], 'a1i', '( %s -> ( 1 = %s <-> %s = 1 ) )' % (AC, BNC, BNC))
        bq = w.s([c, w.inst('bwbneq1')], 'syl', '( %s -> ( %s = 1 <-> C = 1o ) )' % (AC, BNC))
        bb = w.s([br, b13], 'bitrd', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> 1 = %s ) )' % (AC, BNC, BNC)); bb2 = w.s([bb, ecd], 'bitrd', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> %s = 1 ) )' % (AC, BNC, BNC)); bb3 = w.s([bb2, bq], 'bitrd', '( %s -> ( ( 2 ^ 0 ) <_ %s <-> C = 1o ) )' % (AC, BNC))
        ib = w.s([bb3], 'ifbid', '( %s -> if ( ( 2 ^ 0 ) <_ %s , 1o , (/) ) = if ( C = 1o , 1o , (/) ) )' % (AC, BNC))
        cb = bool_from_bi(w, AC, 'C', 'C = 1o', w.s([], 'biidd', '( %s -> ( C = 1o <-> C = 1o ) )' % AC), c)
        k0 = w.s([ib, cb], 'eqtr4d', '( %s -> if ( ( 2 ^ 0 ) <_ %s , 1o , (/) ) = C )' % (AC, BNC))
        fa = w.s([k0], 'fveq2d', '( %s -> ( addCarry ` if ( ( 2 ^ 0 ) <_ %s , 1o , (/) ) ) = ( addCarry ` C ) )' % (AC, BNC))
        cc = w.s([b0, fa], 'oveq12d', '( %s -> %s = ( (/) ++ ( addCarry ` C ) ) )' % (AC, new))
        acl = cl.mem('( addCarry ` C )', 'Word 2o'); li = w.s([acl, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( addCarry ` C ) ) = ( addCarry ` C ) )' % AC)
        w.qed([v, st, cc, li], '4eqtrd' if False else '3eqtrd', '') if False else None
        v2 = w.s([v, st], 'eqtrd', '( %s -> ( ( (/) addBits (/) ) ` C ) = %s )' % (AC, new))
        w.qed([v2, cc, li], '3eqtrd', '( %s -> ( ( (/) addBits (/) ) ` C ) = ( addCarry ` C ) )' % AC); w.run()

    for lab, const, vl, desc in (('subbitsnil', 'subBits', 'subbitsval', 'Lean clause 1 of subBits: the difference of two empty words is empty.'),):
        if want(lab):
            w = W(lab, desc)
            c = w.s([], 'id', '( %s -> C e. 2o )' % AC); cl = Cl(w, AC, {'C': ('2o', c)})
            e = w.s([], 'wrd0', '(/) e. Word 2o'); ed = w.s([e], 'a1i', '( %s -> (/) e. Word 2o )' % AC)
            t0d, h0d, mxd, MX0 = nilsetup(w, AC)
            v = w.s([ed, ed, c, w.inst(vl)], 'syl3anc', '( %s -> ( ( (/) %s (/) ) ` C ) = ( %s bwrd %s ) )' % (AC, const, DIF(E0, E0, 'C'), MX0))
            o = w.s([mxd], 'oveq2d', '( %s -> ( %s bwrd %s ) = ( %s bwrd 0 ) )' % (AC, DIF(E0, E0, 'C'), MX0, DIF(E0, E0, 'C')))
            dz = cl.mem(DIF(E0, E0, 'C'), 'ZZ'); b0 = w.s([dz, w.inst('bwrd0')], 'syl', '( %s -> ( %s bwrd 0 ) = (/) )' % (AC, DIF(E0, E0, 'C')))
            w.qed([v, o, b0], '3eqtrd', '( %s -> ( ( (/) %s (/) ) ` C ) = (/) )' % (AC, const)); w.run()
    if want('subborrownil'):
        w = W('subborrownil', 'Lean clause 1 of subBorrow: the borrow out of two empty words is the borrow in.')
        c = w.s([], 'id', '( %s -> C e. 2o )' % AC); cl = Cl(w, AC, {'C': ('2o', c)})
        e = w.s([], 'wrd0', '(/) e. Word 2o'); ed = w.s([e], 'a1i', '( %s -> (/) e. Word 2o )' % AC)
        t0d, h0d, mxd, MX0 = nilsetup(w, AC)
        BNC = '( bToNat ` C )'
        v = w.s([ed, ed, c, w.inst('subborrowval')], 'syl3anc', '( %s -> ( ( (/) subBorrow (/) ) ` C ) = if ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) , 1o , (/) ) )' % (AC, BNC))
        bc = cl.mem(BNC, 'CC'); ad = w.s([t0d], 'oveq1d', '( %s -> ( ( toNat ` (/) ) + %s ) = ( 0 + %s ) )' % (AC, BNC, BNC)); ad2 = w.s([ad, w.s([bc], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AC, BNC, BNC))], 'eqtrd', '( %s -> ( ( toNat ` (/) ) + %s ) = %s )' % (AC, BNC, BNC))
        br = w.s([t0d, ad2], 'breq12d', '( %s -> ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) <-> 0 < %s ) )' % (AC, BNC, BNC))
        bz = cl.mem(BNC, 'ZZ'); zg = w.s([bz, w.inst('zgt0ge1')], 'syl', '( %s -> ( 0 < %s <-> 1 <_ %s ) )' % (AC, BNC, BNC))
        bnle = w.s([c, w.inst('bwbnle1')], 'syl', '( %s -> %s <_ 1 )' % (AC, BNC)); bnr = cl.mem(BNC, 'RR'); onr = w.s([], '1red', '( %s -> 1 e. RR )' % AC)
        t3 = w.s([onr, bnr, w.inst('letri3')], 'syl2anc', '( %s -> ( 1 = %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AC, BNC, BNC, BNC))
        bt = w.s([bnle], 'biantrud', '( %s -> ( 1 <_ %s <-> ( 1 <_ %s /\\ %s <_ 1 ) ) )' % (AC, BNC, BNC, BNC))
        b13 = w.s([bt, t3], 'bitr4d', '( %s -> ( 1 <_ %s <-> 1 = %s ) )' % (AC, BNC, BNC))
        ec = w.s([], 'eqcom', '( 1 = %s <-> %s = 1 )' % (BNC, BNC)); ecd = w.s([ec], 'a1i', '( %s -> ( 1 = %s <-> %s = 1 ) )' % (AC, BNC, BNC))
        bq = w.s([c, w.inst('bwbneq1')], 'syl', '( %s -> ( %s = 1 <-> C = 1o ) )' % (AC, BNC))
        bb = w.s([br, zg], 'bitrd', '( %s -> ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) <-> 1 <_ %s ) )' % (AC, BNC, BNC)); bb2 = w.s([bb, b13], 'bitrd', '( %s -> ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) <-> 1 = %s ) )' % (AC, BNC, BNC))
        bb3 = w.s([bb2, ecd], 'bitrd', '( %s -> ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) <-> %s = 1 ) )' % (AC, BNC, BNC)); bb4 = w.s([bb3, bq], 'bitrd', '( %s -> ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) <-> C = 1o ) )' % (AC, BNC))
        ib = w.s([bb4], 'ifbid', '( %s -> if ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) , 1o , (/) ) = if ( C = 1o , 1o , (/) ) )' % (AC, BNC))
        cb = bool_from_bi(w, AC, 'C', 'C = 1o', w.s([], 'biidd', '( %s -> ( C = 1o <-> C = 1o ) )' % AC), c)
        k0 = w.s([ib, cb], 'eqtr4d', '( %s -> if ( ( toNat ` (/) ) < ( ( toNat ` (/) ) + %s ) , 1o , (/) ) = C )' % (AC, BNC))
        w.qed([v, k0], 'eqtrd', '( %s -> ( ( (/) subBorrow (/) ) ` C ) = C )' % AC); w.run()
    if want('cmpbitsnil'):
        AC3 = 'C e. 3o'
        w = W('cmpbitsnil', 'Lean clause 1 of cmpBits: the comparison of two empty words is the start verdict.')
        c = w.s([], 'id', '( %s -> C e. 3o )' % AC3)
        e = w.s([], 'wrd0', '(/) e. Word 2o'); ed = w.s([e], 'a1i', '( %s -> (/) e. Word 2o )' % AC3)
        v = w.s([ed, ed, c, w.inst('cmpbitsval')], 'syl3anc', '( %s -> ( ( (/) cmpBits (/) ) ` C ) = if ( ( toNat ` (/) ) = ( toNat ` (/) ) , C , ( ( toNat ` (/) ) Ncmp ( toNat ` (/) ) ) ) )' % AC3)
        q = w.s([], 'eqid', '( toNat ` (/) ) = ( toNat ` (/) )'); qd = w.s([q], 'a1i', '( %s -> ( toNat ` (/) ) = ( toNat ` (/) ) )' % AC3)
        it = w.s([qd], 'iftrued', '( %s -> if ( ( toNat ` (/) ) = ( toNat ` (/) ) , C , ( ( toNat ` (/) ) Ncmp ( toNat ` (/) ) ) ) = C )' % AC3)
        w.qed([v, it], 'eqtrd', '( %s -> ( ( (/) cmpBits (/) ) ` C ) = C )' % AC3); w.run()

    # ---- zeroBits
    AZ = '( L e. Word 2o /\\ F e. 2o )'
    ZV = 'if ( ( F = 1o /\\ ( toNat ` L ) = 0 ) , 1o , (/) )'
    if want('zerobitsval'):
        w = W('zerobitsval', 'Value of zeroBits: the flag stays set exactly when every scanned bit is false (Lean: zeroBits_eq with toNat_eq_zero_iff).')
        cl = Cl(w, AZ, conj_leaves(w, AZ, [('L', 'Word 2o'), ('F', '2o')]))
        st, val = defval(w, cl, 'df-zerobits', 'zeroBits', ['L', 'F']); assert val == ZV, val
        promote(w, st); w.run()
    if want('zerobitscl'):
        w = W('zerobitscl', 'Closure of zeroBits: a Boolean.')
        cl = Cl(w, AZ, conj_leaves(w, AZ, [('L', 'Word 2o'), ('F', '2o')]))
        v = w.s([], 'zerobitsval', '( %s -> ( L zeroBits F ) = %s )' % (AZ, ZV)); m = cl.mem(ZV, '2o')
        w.qed([v, m], 'eqeltrd', '( %s -> ( L zeroBits F ) e. 2o )' % AZ); w.run()
    if want('zerobitsnil'):
        w = W('zerobitsnil', 'Lean clause 1 of zeroBits: scanning nothing leaves the flag.')
        AF = 'F e. 2o'; f = w.s([], 'id', '( %s -> F e. 2o )' % AF)
        e = w.s([], 'wrd0', '(/) e. Word 2o'); ed = w.s([e], 'a1i', '( %s -> (/) e. Word 2o )' % AF)
        v = w.s([ed, f, w.inst('zerobitsval')], 'syl2anc', '( %s -> ( (/) zeroBits F ) = if ( ( F = 1o /\\ ( toNat ` (/) ) = 0 ) , 1o , (/) ) )' % AF)
        t0 = w.s([], 'tonat0', '( toNat ` (/) ) = 0'); t0d = w.s([t0], 'a1i', '( %s -> ( toNat ` (/) ) = 0 )' % AF)
        ba = w.s([t0d], 'biantrud', '( %s -> ( F = 1o <-> ( F = 1o /\\ ( toNat ` (/) ) = 0 ) ) )' % AF)
        ib = w.s([ba], 'ifbid', '( %s -> if ( F = 1o , 1o , (/) ) = if ( ( F = 1o /\\ ( toNat ` (/) ) = 0 ) , 1o , (/) ) )' % AF)
        fb = bool_from_bi(w, AF, 'F', 'F = 1o', w.s([], 'biidd', '( %s -> ( F = 1o <-> F = 1o ) )' % AF), f)
        v2 = w.s([v, ib], 'eqtr4d', '( %s -> ( (/) zeroBits F ) = if ( F = 1o , 1o , (/) ) )' % AF)
        w.qed([v2, fb], 'eqtr4d', '( %s -> ( (/) zeroBits F ) = F )' % AF); w.run()
    if want('zerobitscons'):
        A3 = '( B e. 2o /\\ L e. Word 2o /\\ F e. 2o )'
        w = W('zerobitscons', 'Lean clause 2 of zeroBits: scanning a bit clears the flag when the bit is true.')
        b = w.s([], 'simp1', '( %s -> B e. 2o )' % A3); l = w.s([], 'simp2', '( %s -> L e. Word 2o )' % A3); f = w.s([], 'simp3', '( %s -> F e. 2o )' % A3)
        cl = Cl(w, A3, {'B': ('2o', b), 'L': ('Word 2o', l), 'F': ('2o', f)})
        CL = CONS('B', 'L'); G = 'if ( ( F = 1o /\\ -. B = 1o ) , 1o , (/) )'
        ccl = cl.mem(CL, 'Word 2o'); g2 = cl.mem(G, '2o')
        v1 = w.s([ccl, f, w.inst('zerobitsval')], 'syl2anc', '( %s -> ( %s zeroBits F ) = if ( ( F = 1o /\\ ( toNat ` %s ) = 0 ) , 1o , (/) ) )' % (A3, CL, CL))
        v2 = w.s([l, g2, w.inst('zerobitsval')], 'syl2anc', '( %s -> ( L zeroBits %s ) = if ( ( %s = 1o /\\ ( toNat ` L ) = 0 ) , 1o , (/) ) )' % (A3, G, G))
        tc = w.s([b, l, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( bToNat ` B ) + ( 2 x. ( toNat ` L ) ) ) )' % (A3, CL))
        # ( bn B + 2 t ) = 0 <-> ( bn B = 0 /\ t = 0 ) for nonnegative integers
        bn = cl.mem('( bToNat ` B )', 'NN0'); tn = cl.mem('( toNat ` L )', 'NN0'); t2 = cl.mem('( 2 x. ( toNat ` L ) )', 'NN0')
        a0 = w.s([bn, t2, w.inst('nn0add0eq')] if False else [], 'id', 'T.') if False else None
        # via: sum of nonnegatives is 0 iff both are: use nn0addcl / "add20" ... state directly with linarith-free route: nn0anddvds? use 'nn0add0eq' if absent fall back to two inequalities
        e1 = w.s([tc], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( ( bToNat ` B ) + ( 2 x. ( toNat ` L ) ) ) = 0 ) )' % (A3, CL))
        br = cl.mem('( bToNat ` B )', 'RR'); tr = cl.mem('( 2 x. ( toNat ` L ) )', 'RR'); bg = cl.ge0('( bToNat ` B )'); tg = cl.ge0('( 2 x. ( toNat ` L ) )')
        a20 = w.s([br, tr, bg, tg, w.inst('add20')], 'syl22anc', '( %s -> ( ( ( bToNat ` B ) + ( 2 x. ( toNat ` L ) ) ) = 0 <-> ( ( bToNat ` B ) = 0 /\\ ( 2 x. ( toNat ` L ) ) = 0 ) ) )' % A3)
        tcc = cl.mem('( toNat ` L )', 'CC'); twoc = w.s([], '2cnd', '( %s -> 2 e. CC )' % A3); tne = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % A3)
        m0 = w.s([tcc, twoc, tne, w.inst('mulcan2d')] if False else [], 'id', 'T.') if False else None
        # ( 2 x. t ) = 0 <-> t = 0 : mul02 form via mulcand with C = 2: ( 2 x. t ) = ( 2 x. 0 ) <-> t = 0
        zc = w.s([], '0cnd', '( %s -> 0 e. CC )' % A3)
        mc = w.s([tcc, zc, twoc, tne], 'mulcand', '( %s -> ( ( 2 x. ( toNat ` L ) ) = ( 2 x. 0 ) <-> ( toNat ` L ) = 0 ) )' % A3)
        m20 = w.s([twoc], 'mul01d', '( %s -> ( 2 x. 0 ) = 0 )' % A3); e20 = w.s([m20], 'eqeq2d', '( %s -> ( ( 2 x. ( toNat ` L ) ) = ( 2 x. 0 ) <-> ( 2 x. ( toNat ` L ) ) = 0 ) )' % A3)
        mc2 = w.s([e20, mc], 'bitr3d', '( %s -> ( ( 2 x. ( toNat ` L ) ) = 0 <-> ( toNat ` L ) = 0 ) )' % A3)
        bq = w.s([b, w.inst('bwbneq0')], 'syl', '( %s -> ( ( bToNat ` B ) = 0 <-> B = (/) ) )' % A3)
        bn2 = w.s([b, w.inst('bwel2on')], 'syl', '( %s -> ( -. B = 1o <-> B = (/) ) )' % A3); bq2 = w.s([bq, bn2], 'bitr4d', '( %s -> ( ( bToNat ` B ) = 0 <-> -. B = 1o ) )' % A3)
        an = w.s([bq2, mc2], 'anbi12d', '( %s -> ( ( ( bToNat ` B ) = 0 /\\ ( 2 x. ( toNat ` L ) ) = 0 ) <-> ( -. B = 1o /\\ ( toNat ` L ) = 0 ) ) )' % A3)
        e2 = w.s([e1, a20, an], '3bitrd', '( %s -> ( ( toNat ` %s ) = 0 <-> ( -. B = 1o /\\ ( toNat ` L ) = 0 ) ) )' % (A3, CL))
        e3 = w.s([e2], 'anbi2d', '( %s -> ( ( F = 1o /\\ ( toNat ` %s ) = 0 ) <-> ( F = 1o /\\ ( -. B = 1o /\\ ( toNat ` L ) = 0 ) ) ) )' % (A3, CL))
        aa = w.s([], 'anass', '( ( ( F = 1o /\\ -. B = 1o ) /\\ ( toNat ` L ) = 0 ) <-> ( F = 1o /\\ ( -. B = 1o /\\ ( toNat ` L ) = 0 ) ) )'); aad = w.s([aa], 'a1i', '( %s -> ( ( ( F = 1o /\\ -. B = 1o ) /\\ ( toNat ` L ) = 0 ) <-> ( F = 1o /\\ ( -. B = 1o /\\ ( toNat ` L ) = 0 ) ) ) )' % A3)
        # G = 1o <-> ( F = 1o /\ -. B = 1o )
        n0 = w.s([], '1n0', '1o =/= (/)'); tb = w.s([n0, w.inst('iftrueb')], 'ax-mp', '( %s = 1o <-> ( F = 1o /\\ -. B = 1o ) )' % G); tbd = w.s([tb], 'a1i', '( %s -> ( %s = 1o <-> ( F = 1o /\\ -. B = 1o ) ) )' % (A3, G))
        gb = w.s([tbd], 'anbi1d', '( %s -> ( ( %s = 1o /\\ ( toNat ` L ) = 0 ) <-> ( ( F = 1o /\\ -. B = 1o ) /\\ ( toNat ` L ) = 0 ) ) )' % (A3, G))
        e4 = w.s([e3, aad], 'bitr4d', '( %s -> ( ( F = 1o /\\ ( toNat ` %s ) = 0 ) <-> ( ( F = 1o /\\ -. B = 1o ) /\\ ( toNat ` L ) = 0 ) ) )' % (A3, CL))
        e5 = w.s([e4, gb], 'bitr4d', '( %s -> ( ( F = 1o /\\ ( toNat ` %s ) = 0 ) <-> ( %s = 1o /\\ ( toNat ` L ) = 0 ) ) )' % (A3, CL, G))
        ib = w.s([e5], 'ifbid', '( %s -> if ( ( F = 1o /\\ ( toNat ` %s ) = 0 ) , 1o , (/) ) = if ( ( %s = 1o /\\ ( toNat ` L ) = 0 ) , 1o , (/) ) )' % (A3, CL, G))
        w.qed([v1, ib, v2], '3eqtr4d', '( %s -> ( %s zeroBits F ) = ( L zeroBits %s ) )' % (A3, CL, G)); w.run()

    # ---- toNat = 0
    if want('tonateq0'):
        AL = 'L e. Word 2o'
        w = W('tonateq0', 'The value of a bit word is 0 exactly when every letter is false (Lean: toNat_eq_zero_iff).')
        cl = Cl(w, AL, {'L': ('Word 2o', w.s([], 'id', '( %s -> L e. Word 2o )' % AL))})
        tz = cl.mem(TN('L'), 'ZZ'); zz = w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % AL)
        inj = w.s([tz, zz, w.inst('bwbitsinj')], 'syl2anc', '( %s -> ( ( bits ` ( toNat ` L ) ) = ( bits ` 0 ) <-> ( toNat ` L ) = 0 ) )' % AL)
        b0 = w.s([], '0bits', '( bits ` 0 ) = (/)'); bb = w.s([], 'bwbits', '( %s -> ( bits ` ( toNat ` L ) ) = %s )' % (AL, BITSET('L')))
        b0d = w.s([b0], 'a1i', '( %s -> ( bits ` 0 ) = (/) )' % AL)
        e = w.s([bb, b0d], 'eqeq12d', '( %s -> ( ( bits ` ( toNat ` L ) ) = ( bits ` 0 ) <-> %s = (/) ) )' % (AL, BITSET('L')))
        r0 = w.s([], 'rabeq0', '( %s = (/) <-> A. i e. ( 0 ..^ ( # ` L ) ) -. ( L ` i ) = 1o )' % BITSET('L')); r0d = w.s([r0], 'a1i', '( %s -> ( %s = (/) <-> A. i e. ( 0 ..^ ( # ` L ) ) -. ( L ` i ) = 1o ) )' % (AL, BITSET('L')))
        a2 = '( %s /\\ i e. ( 0 ..^ ( # ` L ) ) )' % AL
        sym = w.s([], 'wrdsymbcl', '( %s -> ( L ` i ) e. 2o )' % a2); n2 = w.s([sym, w.inst('bwel2on')], 'syl', '( %s -> ( -. ( L ` i ) = 1o <-> ( L ` i ) = (/) ) )' % a2)
        ra = w.s([n2], 'ralbidva', '( %s -> ( A. i e. ( 0 ..^ ( # ` L ) ) -. ( L ` i ) = 1o <-> A. i e. ( 0 ..^ ( # ` L ) ) ( L ` i ) = (/) ) )' % AL)
        c1 = w.s([e, r0d], 'bitrd', '( %s -> ( ( bits ` ( toNat ` L ) ) = ( bits ` 0 ) <-> A. i e. ( 0 ..^ ( # ` L ) ) -. ( L ` i ) = 1o ) )' % AL)
        c2 = w.s([c1, ra], 'bitrd', '( %s -> ( ( bits ` ( toNat ` L ) ) = ( bits ` 0 ) <-> A. i e. ( 0 ..^ ( # ` L ) ) ( L ` i ) = (/) ) )' % AL)
        w.qed([inj, c2], 'bitr3d', '( %s -> ( ( toNat ` L ) = 0 <-> A. i e. ( 0 ..^ ( # ` L ) ) ( L ` i ) = (/) ) )' % AL); w.run()

    # ---- the letter map inclBool o. L (Lean's bits l)
    IB = 'inclBool'
    if want('bwmapf'):
        w = W('bwmapf', 'The letter map of the bit words into the stack alphabet (Lean: bits l = l.map Gamma\'.bit).')
        f = w.s([], 'inclboolf', 'inclBool : 2o --> Gamma\'') if False else None
        w = W('bwmapcl', 'The letter map sends bit words to words over Gamma\' (Lean: bits l : List Gamma\').')
        AL = 'L e. Word 2o'; l = w.s([], 'id', '( %s -> L e. Word 2o )' % AL)
        f = w.s([], 'inclboolf', 'inclBool : 2o --> Gamma\''); fd = w.s([f], 'a1i', '( %s -> inclBool : 2o --> Gamma\' )' % AL)
        w.qed([l, fd, w.inst('wrdco')], 'syl2anc', '( %s -> ( inclBool o. L ) e. Word Gamma\' )' % AL); w.run()
    if want('bwmaplen'):
        w = W('bwmaplen', 'The letter map preserves the length (Lean: bits_length).')
        AL = 'L e. Word 2o'; l = w.s([], 'id', '( %s -> L e. Word 2o )' % AL)
        f = w.s([], 'inclboolf', 'inclBool : 2o --> Gamma\''); fd = w.s([f], 'a1i', '( %s -> inclBool : 2o --> Gamma\' )' % AL)
        w.qed([l, fd, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` ( inclBool o. L ) ) = ( # ` L ) )' % AL); w.run()
    if want('bwmap0'):
        w = W('bwmap0', 'The letter map of the empty word (Lean: bits_nil).')
        w.qed([], 'co02', '( inclBool o. (/) ) = (/)'); w.run()
    if want('bwmapcons'):
        A2 = '( B e. 2o /\\ L e. Word 2o )'
        w = W('bwmapcons', 'The letter map of a word with a letter prepended (Lean: bits_cons).')
        b = w.s([], 'simpl', '( %s -> B e. 2o )' % A2); l = w.s([], 'simpr', '( %s -> L e. Word 2o )' % A2)
        f = w.s([], 'inclboolf', 'inclBool : 2o --> Gamma\''); fd = w.s([f], 'a1i', '( %s -> inclBool : 2o --> Gamma\' )' % A2)
        s1 = w.s([b, w.inst('s1cl')], 'syl', '( %s -> <" B "> e. Word 2o )' % A2)
        cc = w.s([s1, l, fd, w.inst('ccatco')], 'syl3anc', '( %s -> ( inclBool o. ( <" B "> ++ L ) ) = ( ( inclBool o. <" B "> ) ++ ( inclBool o. L ) ) )' % A2)
        sc = w.s([b, fd, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" B "> ) = <" ( inclBool ` B ) "> )' % A2)
        iv = w.s([b, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` B ) = <. 1 , B >. )' % A2)
        se = w.s([iv], 's1eqd', '( %s -> <" ( inclBool ` B ) "> = <" <. 1 , B >. "> )' % A2)
        sc2 = w.s([sc, se], 'eqtrd', '( %s -> ( inclBool o. <" B "> ) = <" <. 1 , B >. "> )' % A2)
        o = w.s([sc2], 'oveq1d', '( %s -> ( ( inclBool o. <" B "> ) ++ ( inclBool o. L ) ) = ( <" <. 1 , B >. "> ++ ( inclBool o. L ) ) )' % A2)
        w.qed([cc, o], 'eqtrd', '( %s -> ( inclBool o. ( <" B "> ++ L ) ) = ( <" <. 1 , B >. "> ++ ( inclBool o. L ) ) )' % A2); w.run()
    if want('bwmapccat'):
        A2 = '( L e. Word 2o /\\ K e. Word 2o )'
        w = W('bwmapccat', 'The letter map of a concatenation (Lean: bits_append).')
        l = w.s([], 'simpl', '( %s -> L e. Word 2o )' % A2); k = w.s([], 'simpr', '( %s -> K e. Word 2o )' % A2)
        f = w.s([], 'inclboolf', 'inclBool : 2o --> Gamma\''); fd = w.s([f], 'a1i', '( %s -> inclBool : 2o --> Gamma\' )' % A2)
        w.qed([l, k, fd, w.inst('ccatco')], 'syl3anc', '( %s -> ( inclBool o. ( L ++ K ) ) = ( ( inclBool o. L ) ++ ( inclBool o. K ) ) )' % A2); w.run()
    if want('bwmaprev'):
        AL = 'L e. Word 2o'
        w = W('bwmaprev', 'The letter map of a reversal (Lean: bits_reverse).')
        l = w.s([], 'id', '( %s -> L e. Word 2o )' % AL)
        f = w.s([], 'inclboolf', 'inclBool : 2o --> Gamma\''); fd = w.s([f], 'a1i', '( %s -> inclBool : 2o --> Gamma\' )' % AL)
        w.qed([l, fd, w.inst('revco')], 'syl2anc', '( %s -> ( inclBool o. ( reverse ` L ) ) = ( reverse ` ( inclBool o. L ) ) )' % AL); w.run()
