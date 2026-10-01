"""Sortie T4, group E: sumBit, majBit, borrow, cmpStep, bitOf, addCarry and the full adder/subtractor identities (T4-blueprint 3.4)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


A3 = '( A e. 2o /\\ B e. 2o /\\ C e. 2o )'
A3o = '( A e. 2o /\\ B e. 2o /\\ C e. 3o )'
SUMC = '( ( A = 1o \\/_ B = 1o ) \\/_ C = 1o )'
MAJC = '( ( A = 1o /\\ B = 1o ) \\/ ( C = 1o /\\ ( A = 1o \\/ B = 1o ) ) )'
BORC = '( ( -. A = 1o /\\ ( B = 1o \\/ C = 1o ) ) \\/ ( B = 1o /\\ C = 1o ) )'
CMPV = 'if ( A = B , C , if ( A = 1o , 2o , (/) ) )'


def cl3(w, ante=A3, kc='2o'):
    return Cl(w, ante, conj_leaves(w, ante, [('A', '2o'), ('B', '2o'), ('C', kc)]))


def closed_val(w, const, vallabel, a, b, c, kindc='2o'):
    """closed: ( ( a const b ) ` c ) = v for literal Booleans; returns (step, v)"""
    mem = {'1o': '1oel2o', '(/)': '0el2o', '2o': 'bw2oel3o'}
    ma = num.closed(w, [], mem[a], '%s e. 2o' % a); mb = num.closed(w, [], mem[b], '%s e. 2o' % b)
    if kindc == '2o':
        mc = num.closed(w, [], mem[c], '%s e. 2o' % c)
    else:
        mc = num.closed(w, [], {'1o': 'bw1oel3o', '(/)': 'bw0el3o', '2o': 'bw2oel3o'}[c], '%s e. 3o' % c)
    i = w.inst(vallabel)
    # the instance formula: substitute literals into the value lemma
    lab = {'sumBit': SUMC, 'majBit': MAJC, 'borrow': BORC}
    if const == 'cmpStep':
        val = CMPV
    else:
        val = 'if ( %s , 1o , (/) )' % lab[const]
    sub = {'A': a, 'B': b, 'C': c}
    val = ' '.join(sub.get(t, t) for t in val.split())
    f = '( ( %s %s %s ) ` %s ) = %s' % (a, const, b, c, val)
    st = num.closed(w, [ma, mb, mc, i], 'mp3an', f)
    # reduce the if(s) under T.
    pe = PropEval(w)
    cur = val; chain = [w.s([st], 'a1i', '( T. -> ( ( %s %s %s ) ` %s ) = %s )' % (a, const, b, c, val))]
    while cur.startswith('if ('):
        node = parsewff(cur[len('if ( '):].rsplit(' , ', 2)[0]) if False else None
        # split the condition off
        toks = cur.split(); depth = 0; cuts = []
        for k, t in enumerate(toks[2:], 2):
            if t in ('(', '{'): depth += 1
            elif t in (')', '}'): depth -= 1
            elif t == ',' and depth == 0: cuts.append(k)
        cond = ' '.join(toks[2:cuts[0]])
        s, v = closed_if(w, cur, parsewff(cond))
        chain.append(w.s([chain[-1], s], 'eqtrd', '( T. -> ( ( %s %s %s ) ` %s ) = %s )' % (a, const, b, c, v)))
        cur = v
    tru = num.closed(w, [], 'tru', 'T.')
    fin = num.closed(w, [tru, chain[-1]], 'ax-mp', '( ( %s %s %s ) ` %s ) = %s' % (a, const, b, c, cur))
    return fin, cur


if __name__ == '__main__':
    if want('sumbitval'):
        w = W('sumbitval', 'Value of sumBit: the exclusive or of three Booleans (Lean: sumBit a b c = xor (xor a b) c).')
        st, val, ante = op3val(w, 'df-sumbit', 'sumBit', 'A', 'B', 'C', None)
        promote(w, st); w.run()
    for lab, const, dlab, desc in (('majval', 'majBit', 'df-majbit', 'Value of majBit: the majority of three Booleans, the carry-out of a full adder.'),
                                   ('borrowval', 'borrow', 'df-borrow', 'Value of borrow: the borrow-out of a full subtractor.')):
        if want(lab):
            w = W(lab, desc)
            cl = cl3(w)
            st, val = defval(w, cl, dlab, const, ['A', 'B', 'C'])
            promote(w, st); w.run()
    if want('cmpstepval'):
        w = W('cmpstepval', 'Value of cmpStep: a differing bit overrides the verdict so far (Lean: cmpStep).')
        cl = cl3(w, A3o, '3o')
        st, val = defval(w, cl, 'df-cmpstep', 'cmpStep', ['A', 'B', 'C']); assert val == CMPV, val
        promote(w, st); w.run()
    for lab, vl, const, cond in (('sumbitcl', 'sumbitval', 'sumBit', SUMC), ('majcl', 'majval', 'majBit', MAJC), ('borrowcl', 'borrowval', 'borrow', BORC)):
        if want(lab):
            w = W(lab, 'Closure of %s: a Boolean.' % const)
            cl = cl3(w)
            v = w.s([], vl, '( %s -> ( ( A %s B ) ` C ) = if ( %s , 1o , (/) ) )' % (A3, const, cond))
            m = cl.mem('if ( %s , 1o , (/) )' % cond, '2o')
            w.qed([v, m], 'eqeltrd', '( %s -> ( ( A %s B ) ` C ) e. 2o )' % (A3, const)); w.run()
    if want('cmpstepcl'):
        w = W('cmpstepcl', 'Closure of cmpStep: an ordering.')
        cl = cl3(w, A3o, '3o')
        v = w.s([], 'cmpstepval', '( %s -> ( ( A cmpStep B ) ` C ) = %s )' % (A3o, CMPV))
        m = cl.mem(CMPV, '3o')
        w.qed([v, m], 'eqeltrd', '( %s -> ( ( A cmpStep B ) ` C ) e. 3o )' % A3o); w.run()

    # ---- bitOf
    AO = 'O e. ( 2o |_| 1o )'
    BOV = 'if ( O = ( inr ` (/) ) , (/) , ( 2nd ` O ) )'
    if want('bitofval'):
        w = W('bitofval', 'Value of bitOf: the payload of a register, false when empty (Lean: bitOf o = o.getD false).')
        cl = Cl(w, AO, {'O': ('( 2o |_| 1o )', w.s([], 'id', '( %s -> %s )' % (AO, AO)))})
        zex = num.closed(w, [], '0ex', '(/) e. _V'); sx = num.closed(w, [], 'fvex', '( 2nd ` O ) e. _V')
        ie = num.closed(w, [zex, sx, w.inst('ifexg')], 'mp2an', '%s e. _V' % BOV)
        cl.have(BOV, '_V', w.s([ie], 'a1i', '( %s -> %s e. _V )' % (AO, BOV)))
        st, val = defval(w, cl, 'df-bitof', 'bitOf', ['O']); assert val == BOV, val
        promote(w, st); w.run()
    if want('bitofnone'):
        w = W('bitofnone', 'bitOf of an empty register is false (Lean: bitOf_none).')
        z = w.s([], '0ex', '(/) e. _V'); on = w.s([], '1oel2o', '1o e. 2o') if False else None
        e1 = w.s([], 'el1o', '( (/) e. 1o <-> (/) = (/) )'); ee = w.s([], 'eqid', '(/) = (/)'); m = w.s([ee, e1], 'mpbir', '(/) e. 1o')
        dj = w.s([m, w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. ( 2o |_| 1o )')
        v = w.s([dj, w.inst('bitofval')], 'ax-mp', '( bitOf ` ( inr ` (/) ) ) = if ( ( inr ` (/) ) = ( inr ` (/) ) , (/) , ( 2nd ` ( inr ` (/) ) ) )')
        q = w.s([], 'eqid', '( inr ` (/) ) = ( inr ` (/) )'); it = w.s([q], 'iftruei', 'if ( ( inr ` (/) ) = ( inr ` (/) ) , (/) , ( 2nd ` ( inr ` (/) ) ) ) = (/)')
        w.qed([v, it], 'eqtri', '( bitOf ` ( inr ` (/) ) ) = (/)'); w.run()
    if want('bitofsome'):
        w = W('bitofsome', 'bitOf of a register holding a bit is that bit (Lean: bitOf_some).')
        AB = 'B e. 2o'
        dj = w.s([w.inst('djulcl')], 'syl' if False else 'id', '') if False else None
        i = w.s([], 'id', '( %s -> B e. 2o )' % AB)
        dj = w.s([i, w.inst('djulcl')], 'syl', '( %s -> ( inl ` B ) e. ( 2o |_| 1o ) )' % AB)
        v = w.s([dj, w.inst('bitofval')], 'syl', '( %s -> ( bitOf ` ( inl ` B ) ) = if ( ( inl ` B ) = ( inr ` (/) ) , (/) , ( 2nd ` ( inl ` B ) ) ) )' % AB)
        iv = w.s([i, w.inst('inlval')], 'syl', '( %s -> ( inl ` B ) = <. (/) , B >. )' % AB)
        z = w.s([], '0ex', '(/) e. _V'); rv = w.s([z, w.inst('inrval')], 'ax-mp', '( inr ` (/) ) = <. 1o , (/) >.'); rvd = w.s([rv], 'a1i', '( %s -> ( inr ` (/) ) = <. 1o , (/) >. )' % AB)
        eq = w.s([iv, rvd], 'eqeq12d', '( %s -> ( ( inl ` B ) = ( inr ` (/) ) <-> <. (/) , B >. = <. 1o , (/) >. ) )' % AB)
        bx = w.s([i], 'elexd', '( %s -> B e. _V )' % AB); zd = w.s([z], 'a1i', '( %s -> (/) e. _V )' % AB)
        op = w.s([zd, bx, w.inst('opthg')], 'syl2anc', '( %s -> ( <. (/) , B >. = <. 1o , (/) >. <-> ( (/) = 1o /\\ B = (/) ) ) )' % AB)
        n1 = w.s([], '1n0', '1o =/= (/)'); n2 = w.s([n1], 'nesymi', '-. (/) = 1o'); n3 = w.s([n2], 'intnanr', '-. ( (/) = 1o /\\ B = (/) )'); n3d = w.s([n3], 'a1i', '( %s -> -. ( (/) = 1o /\\ B = (/) ) )' % AB)
        no = w.s([n3d, op], 'mtbird', '( %s -> -. <. (/) , B >. = <. 1o , (/) >. )' % AB)
        ne = w.s([no, eq], 'mtbird', '( %s -> -. ( inl ` B ) = ( inr ` (/) ) )' % AB)
        iff = w.s([ne], 'iffalsed', '( %s -> if ( ( inl ` B ) = ( inr ` (/) ) , (/) , ( 2nd ` ( inl ` B ) ) ) = ( 2nd ` ( inl ` B ) ) )' % AB)
        s2 = w.s([i, w.inst('2ndinl')], 'syl', '( %s -> ( 2nd ` ( inl ` B ) ) = B )' % AB)
        w.qed([v, iff, s2], '3eqtrd', '( %s -> ( bitOf ` ( inl ` B ) ) = B )' % AB); w.run()
    if want('bitofcl'):
        w = W('bitofcl', 'Closure of bitOf: a Boolean.')
        i = w.s([], 'id', '( %s -> %s )' % (AO, AO))
        v = w.s([], 'bitofval', '( %s -> ( bitOf ` O ) = %s )' % (AO, BOV))
        dj = w.s([i, w.inst('eldju1st')], 'syl', '( %s -> ( ( 1st ` O ) = (/) \\/ ( 1st ` O ) = 1o ) )' % AO)
        a1 = '( %s /\\ ( 1st ` O ) = (/) )' % AO
        s2 = w.s([], 'eldju2ndl', '( %s -> ( 2nd ` O ) e. 2o )' % a1)
        z = w.s([], '0el2o', '(/) e. 2o'); zd = w.s([z], 'a1i', '( %s -> (/) e. 2o )' % a1)
        ic = w.s([zd, s2], 'ifcld', '( %s -> %s e. 2o )' % (a1, BOV))
        v1 = w.s([v], 'adantr', '( %s -> ( bitOf ` O ) = %s )' % (a1, BOV))
        c1 = w.s([v1, ic], 'eqeltrd', '( %s -> ( bitOf ` O ) e. 2o )' % a1)
        a2 = '( %s /\\ ( 1st ` O ) = 1o )' % AO
        h2 = w.s([], 'simpr', '( %s -> ( 1st ` O ) = 1o )' % a2); o2 = w.s([], 'simpl', '( %s -> %s )' % (a2, AO))
        n1 = w.s([], '1n0', '1o =/= (/)'); nd = w.s([n1], 'a1i', '( %s -> 1o =/= (/) )' % a2)
        ne = w.s([h2, nd], 'eqnetrd', '( %s -> ( 1st ` O ) =/= (/) )' % a2)
        r = w.s([o2, ne, w.inst('eldju2ndr')], 'syl2anc', '( %s -> ( 2nd ` O ) e. 1o )' % a2)
        e1 = w.s([], 'el1o', '( ( 2nd ` O ) e. 1o <-> ( 2nd ` O ) = (/) )'); r2 = w.s([r, e1], 'sylib', '( %s -> ( 2nd ` O ) = (/) )' % a2)
        ss = w.s([], 'djuss', '( 2o |_| 1o ) C_ ( { (/) , 1o } X. ( 2o u. 1o ) )'); ssd = w.s([ss], 'a1i', '( %s -> ( 2o |_| 1o ) C_ ( { (/) , 1o } X. ( 2o u. 1o ) ) )' % a2)
        ox = w.s([ssd, o2], 'sseldd', '( %s -> O e. ( { (/) , 1o } X. ( 2o u. 1o ) ) )' % a2)
        op = w.s([ox, w.inst('1st2nd2')], 'syl', '( %s -> O = <. ( 1st ` O ) , ( 2nd ` O ) >. )' % a2)
        op2 = w.s([h2, r2], 'opeq12d', '( %s -> <. ( 1st ` O ) , ( 2nd ` O ) >. = <. 1o , (/) >. )' % a2)
        zx = w.s([], '0ex', '(/) e. _V'); rv = w.s([zx, w.inst('inrval')], 'ax-mp', '( inr ` (/) ) = <. 1o , (/) >.'); rvd = w.s([rv], 'a1i', '( %s -> ( inr ` (/) ) = <. 1o , (/) >. )' % a2)
        oe = w.s([op, op2, rvd], '3eqtr4d', '( %s -> O = ( inr ` (/) ) )' % a2)
        it = w.s([oe], 'iftrued', '( %s -> %s = (/) )' % (a2, BOV))
        v2 = w.s([v], 'adantr', '( %s -> ( bitOf ` O ) = %s )' % (a2, BOV))
        v3 = w.s([v2, it], 'eqtrd', '( %s -> ( bitOf ` O ) = (/) )' % a2)
        zd2 = w.s([z], 'a1i', '( %s -> (/) e. 2o )' % a2)
        c2 = w.s([v3, zd2], 'eqeltrd', '( %s -> ( bitOf ` O ) e. 2o )' % a2)
        w.qed([c1, c2, dj], 'mpjaodan', '( %s -> ( bitOf ` O ) e. 2o )' % AO); w.run()

    # ---- addCarry
    AC = 'C e. 2o'
    ACV = 'if ( C = 1o , <" 1o "> , (/) )'
    if want('addcarryval'):
        w = W('addcarryval', 'Value of addCarry: the final carry as a bit word (Lean: addCarry c = if c then [true] else []).')
        cl = Cl(w, AC, {'C': ('2o', w.s([], 'id', '( %s -> C e. 2o )' % AC))})
        st, val = defval(w, cl, 'df-addcarry', 'addCarry', ['C']); assert val == ACV, val
        promote(w, st); w.run()
    if want('addcarrycl'):
        w = W('addcarrycl', 'Closure of addCarry: a bit word.')
        cl = Cl(w, AC, {'C': ('2o', w.s([], 'id', '( %s -> C e. 2o )' % AC))})
        v = w.s([], 'addcarryval', '( %s -> ( addCarry ` C ) = %s )' % (AC, ACV)); m = cl.mem(ACV, 'Word 2o')
        w.qed([v, m], 'eqeltrd', '( %s -> ( addCarry ` C ) e. Word 2o )' % AC); w.run()
    if want('addcarry1'):
        w = W('addcarry1', 'addCarry of true is the one-letter word true.')
        o = w.s([], '1oel2o', '1o e. 2o'); v = w.s([o, w.inst('addcarryval')], 'ax-mp', '( addCarry ` 1o ) = if ( 1o = 1o , <" 1o "> , (/) )')
        q = w.s([], 'eqid', '1o = 1o'); it = w.s([q], 'iftruei', 'if ( 1o = 1o , <" 1o "> , (/) ) = <" 1o ">')
        w.qed([v, it], 'eqtri', '( addCarry ` 1o ) = <" 1o ">'); w.run()
    if want('addcarry0'):
        w = W('addcarry0', 'addCarry of false is the empty word.')
        o = w.s([], '0el2o', '(/) e. 2o'); v = w.s([o, w.inst('addcarryval')], 'ax-mp', '( addCarry ` (/) ) = if ( (/) = 1o , <" 1o "> , (/) )')
        n = w.s([], '1n0', '1o =/= (/)'); n2 = w.s([n], 'nesymi', '-. (/) = 1o'); it = w.s([n2], 'iffalsei', 'if ( (/) = 1o , <" 1o "> , (/) ) = (/)')
        w.qed([v, it], 'eqtri', '( addCarry ` (/) ) = (/)'); w.run()
    for lab, F, desc in (('addcarrylen', '#', 'The length of addCarry C is the value of C.'), ('addcarrytonat', 'toNat', 'The value of addCarry C is the value of C.')):
        if not want(lab):
            continue
        w = W(lab, desc)
        m = w.s([], 'id', '( %s -> C e. 2o )' % AC)
        concl = '( %s ` ( addCarry ` C ) ) = ( bToNat ` C )' % F

        def body(a2, eq, v, F=F, concl=concl):
            f = w.s([eq], 'fveq2d', '( %s -> ( addCarry ` C ) = ( addCarry ` %s ) )' % (a2, v))
            c = w.s([], 'addcarry1' if v == '1o' else 'addcarry0', '( addCarry ` %s ) = %s' % (v, '<" 1o ">' if v == '1o' else '(/)'))
            f2 = w.s([f, c], 'eqtrdi', '( %s -> ( addCarry ` C ) = %s )' % (a2, '<" 1o ">' if v == '1o' else '(/)'))
            g = w.s([f2], 'fveq2d', '( %s -> ( %s ` ( addCarry ` C ) ) = ( %s ` %s ) )' % (a2, F, F, '<" 1o ">' if v == '1o' else '(/)'))
            if F == '#':
                cv = w.s([], 's1len' if v == '1o' else 'hash0', '( # ` %s ) = %s' % ('<" 1o ">' if v == '1o' else '(/)', '1' if v == '1o' else '0'))
            elif v == '(/)':
                cv = w.s([], 'tonat0', '( toNat ` (/) ) = 0')
            else:
                e = w.s([], 'wrd0', '(/) e. Word 2o'); o = w.s([], '1oel2o', '1o e. 2o')
                ts = w.s([e, o, w.inst('tonatsnoc')], 'mp2an', '( toNat ` ( (/) ++ <" 1o "> ) ) = ( ( toNat ` (/) ) + ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` (/) ) ) ) )')
                s1 = w.s([], '1oel2o', '1o e. 2o'); s1w = w.s([s1, w.inst('s1cl')], 'ax-mp', '<" 1o "> e. Word 2o')
                cl0 = w.s([s1w, w.inst('ccatlid')], 'ax-mp', '( (/) ++ <" 1o "> ) = <" 1o ">')
                f0 = w.s([cl0], 'fveq2i', '( toNat ` ( (/) ++ <" 1o "> ) ) = ( toNat ` <" 1o "> )')
                t0 = w.s([], 'tonat0', '( toNat ` (/) ) = 0'); b1 = w.s([], 'bwbn1', '( bToNat ` 1o ) = 1'); h0 = w.s([], 'hash0', '( # ` (/) ) = 0')
                p0 = w.s([h0], 'oveq2i', '( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 )'); tc = w.s([], '2cn', '2 e. CC'); e0 = w.s([tc, w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1'); p1 = w.s([p0, e0], 'eqtri', '( 2 ^ ( # ` (/) ) ) = 1')
                mm = w.s([b1, p1], 'oveq12i', '( ( bToNat ` 1o ) x. ( 2 ^ ( # ` (/) ) ) ) = ( 1 x. 1 )'); m11 = w.s([], '1t1e1', '( 1 x. 1 ) = 1'); mm2 = w.s([mm, m11], 'eqtri', '( ( bToNat ` 1o ) x. ( 2 ^ ( # ` (/) ) ) ) = 1')
                ad = w.s([t0, mm2], 'oveq12i', '( ( toNat ` (/) ) + ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` (/) ) ) ) ) = ( 0 + 1 )'); a01 = w.s([], '0p1e1', '( 0 + 1 ) = 1'); ad2 = w.s([ad, a01], 'eqtri', '( ( toNat ` (/) ) + ( ( bToNat ` 1o ) x. ( 2 ^ ( # ` (/) ) ) ) ) = 1')
                cv = w.s([f0, ts, ad2], '3eqtr3i', '( toNat ` <" 1o "> ) = 1')
            lit = '1' if v == '1o' else '0'
            g2 = w.s([g, cv], 'eqtrdi', '( %s -> ( %s ` ( addCarry ` C ) ) = %s )' % (a2, F, lit))
            bn = w.s([eq], 'fveq2d', '( %s -> ( bToNat ` C ) = ( bToNat ` %s ) )' % (a2, v))
            bc = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, lit))
            bn2 = w.s([bn, bc], 'eqtrdi', '( %s -> ( bToNat ` C ) = %s )' % (a2, lit))
            return w.s([g2, bn2], 'eqtr4d', '( %s -> %s )' % (a2, concl))
        st = cases2o(w, AC, 'C', m, body, concl); promote(w, st); w.run()

    # ---- the full adder and full subtractor identities, by eight closed cases
    def eightcases(lab, desc, lhs, rhs, evalleaf):
        """( A3 -> lhs = rhs ) by cases on A, B, C; evalleaf(a, b, c) returns
        the closed step lhs[a,b,c] = rhs[a,b,c]"""
        w = W(lab, desc)
        concl = '%s = %s' % (lhs, rhs)
        pa = w.s([], 'simp1', '( %s -> A e. 2o )' % A3); pb = w.s([], 'simp2', '( %s -> B e. 2o )' % A3); pc = w.s([], 'simp3', '( %s -> C e. 2o )' % A3)

        def bodyA(aA, eqA, va):
            def bodyB(aB, eqB, vb):
                def bodyC(aC, eqC, vc):
                    la = lift(w, eqA, aC); lb = lift(w, eqB, aC)
                    s, new = w.wcongr(concl, {'A': va, 'B': vb, 'C': vc}, aC, {'A': la, 'B': lb, 'C': eqC})
                    cs = evalleaf(w, va, vb, vc)
                    return w.s([cs, s], 'mpbiri', '( %s -> %s )' % (aC, concl))
                return cases2o(w, aB, 'C', lift(w, pc, aB), bodyC, concl)
            return cases2o(w, aA, 'B', lift(w, pb, aA), bodyB, concl)
        st = cases2o(w, A3, 'A', pa, bodyA, concl)
        promote(w, st); w.run()

    def leaf_add(w, a, b, c):
        # closed: ( ( bn a + bn b ) + bn c ) = ( bn sumBit + ( 2 x. bn maj ) )
        def bn(x):
            return num.closed(w, [], 'bwbn1' if x == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (x, '1' if x == '1o' else '0'))
        va = 1 if a == '1o' else 0; vb = 1 if b == '1o' else 0; vc = 1 if c == '1o' else 0
        l1 = w.s([bn(a), bn(b)], 'oveq12i', '( ( bToNat ` %s ) + ( bToNat ` %s ) ) = ( %d + %d )' % (a, b, va, vb))
        ab = num.add_nat(w, va, vb)
        l2 = w.s([l1, ab], 'eqtri', '( ( bToNat ` %s ) + ( bToNat ` %s ) ) = %d' % (a, b, va + vb))
        l3 = w.s([l2, bn(c)], 'oveq12i', '( ( ( bToNat ` %s ) + ( bToNat ` %s ) ) + ( bToNat ` %s ) ) = ( %d + %d )' % (a, b, c, va + vb, vc))
        abc = num.add_nat(w, va + vb, vc)
        L = w.s([l3, abc], 'eqtri', '( ( ( bToNat ` %s ) + ( bToNat ` %s ) ) + ( bToNat ` %s ) ) = %d' % (a, b, c, va + vb + vc))
        s, sv = closed_val(w, 'sumBit', 'sumbitval', a, b, c); m, mv = closed_val(w, 'majBit', 'majval', a, b, c)
        sb = w.s([s], 'fveq2i', '( bToNat ` ( ( %s sumBit %s ) ` %s ) ) = ( bToNat ` %s )' % (a, b, c, sv)); sb2 = w.s([sb, bn(sv)], 'eqtri', '( bToNat ` ( ( %s sumBit %s ) ` %s ) ) = %d' % (a, b, c, 1 if sv == '1o' else 0))
        mb = w.s([m], 'fveq2i', '( bToNat ` ( ( %s majBit %s ) ` %s ) ) = ( bToNat ` %s )' % (a, b, c, mv)); mb2 = w.s([mb, bn(mv)], 'eqtri', '( bToNat ` ( ( %s majBit %s ) ` %s ) ) = %d' % (a, b, c, 1 if mv == '1o' else 0))
        sn = 1 if sv == '1o' else 0; mn = 1 if mv == '1o' else 0
        assert va + vb + vc == sn + 2 * mn, (a, b, c, sv, mv)
        m2 = w.s([mb2], 'oveq2i', '( 2 x. ( bToNat ` ( ( %s majBit %s ) ` %s ) ) ) = ( 2 x. %d )' % (a, b, c, mn))
        mul = num.mul_nat(w, 2, mn)
        m3 = w.s([m2, mul], 'eqtri', '( 2 x. ( bToNat ` ( ( %s majBit %s ) ` %s ) ) ) = %d' % (a, b, c, 2 * mn))
        r1 = w.s([sb2, m3], 'oveq12i', '( ( bToNat ` ( ( %s sumBit %s ) ` %s ) ) + ( 2 x. ( bToNat ` ( ( %s majBit %s ) ` %s ) ) ) ) = ( %d + %d )' % (a, b, c, a, b, c, sn, 2 * mn))
        ad = num.add_nat(w, sn, 2 * mn)
        R = w.s([r1, ad], 'eqtri', '( ( bToNat ` ( ( %s sumBit %s ) ` %s ) ) + ( 2 x. ( bToNat ` ( ( %s majBit %s ) ` %s ) ) ) ) = %d' % (a, b, c, a, b, c, sn + 2 * mn))
        return w.s([L, R], 'eqtr4i', '( ( ( bToNat ` %s ) + ( bToNat ` %s ) ) + ( bToNat ` %s ) ) = ( ( bToNat ` ( ( %s sumBit %s ) ` %s ) ) + ( 2 x. ( bToNat ` ( ( %s majBit %s ) ` %s ) ) ) )' % (a, b, c, a, b, c, a, b, c))

    if want('bwfulladd'):
        eightcases('bwfulladd', 'The full adder: the three input bits sum to the sum bit plus twice the carry bit.',
                   '( ( ( bToNat ` A ) + ( bToNat ` B ) ) + ( bToNat ` C ) )',
                   '( ( bToNat ` ( ( A sumBit B ) ` C ) ) + ( 2 x. ( bToNat ` ( ( A majBit B ) ` C ) ) ) )', leaf_add)

    def leaf_sub(w, a, b, c):
        # closed: ( ( bn a - bn b ) - bn c ) = ( bn sumBit - ( 2 x. bn borrow ) ), in ZZ
        def bn(x):
            return num.closed(w, [], 'bwbn1' if x == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (x, '1' if x == '1o' else '0'))
        va = 1 if a == '1o' else 0; vb = 1 if b == '1o' else 0; vc = 1 if c == '1o' else 0
        s, sv = closed_val(w, 'sumBit', 'sumbitval', a, b, c); m, mv = closed_val(w, 'borrow', 'borrowval', a, b, c)
        sn = 1 if sv == '1o' else 0; mn = 1 if mv == '1o' else 0
        assert va - vb - vc == sn - 2 * mn, (a, b, c, sv, mv)
        sb = w.s([s], 'fveq2i', '( bToNat ` ( ( %s sumBit %s ) ` %s ) ) = ( bToNat ` %s )' % (a, b, c, sv)); sb2 = w.s([sb, bn(sv)], 'eqtri', '( bToNat ` ( ( %s sumBit %s ) ` %s ) ) = %d' % (a, b, c, sn))
        mb = w.s([m], 'fveq2i', '( bToNat ` ( ( %s borrow %s ) ` %s ) ) = ( bToNat ` %s )' % (a, b, c, mv)); mb2 = w.s([mb, bn(mv)], 'eqtri', '( bToNat ` ( ( %s borrow %s ) ` %s ) ) = %d' % (a, b, c, mn))
        l1 = w.s([bn(a), bn(b)], 'oveq12i', '( ( bToNat ` %s ) - ( bToNat ` %s ) ) = ( %d - %d )' % (a, b, va, vb))
        l2 = w.s([l1, bn(c)], 'oveq12i', '( ( ( bToNat ` %s ) - ( bToNat ` %s ) ) - ( bToNat ` %s ) ) = ( ( %d - %d ) - %d )' % (a, b, c, va, vb, vc))
        m2 = w.s([mb2], 'oveq2i', '( 2 x. ( bToNat ` ( ( %s borrow %s ) ` %s ) ) ) = ( 2 x. %d )' % (a, b, c, mn))
        mul = num.mul_nat(w, 2, mn)
        m3 = w.s([m2, mul], 'eqtri', '( 2 x. ( bToNat ` ( ( %s borrow %s ) ` %s ) ) ) = %d' % (a, b, c, 2 * mn))
        r1 = w.s([sb2, m3], 'oveq12i', '( ( bToNat ` ( ( %s sumBit %s ) ` %s ) ) - ( 2 x. ( bToNat ` ( ( %s borrow %s ) ` %s ) ) ) ) = ( %d - %d )' % (a, b, c, a, b, c, sn, 2 * mn))
        # closed integer identity ( ( va - vb ) - vc ) = ( sn - 2mn ) via lin.lineq under T.
        from lin import lineq
        cl = Cl(w, 'T.', {})
        eqi = lineq(w, 'T.', '( ( %d - %d ) - %d )' % (va, vb, vc), '( %d - %d )' % (sn, 2 * mn), closure=cl)
        tru = num.closed(w, [], 'tru', 'T.')
        eqc = w.s([tru, eqi], 'ax-mp', '( ( %d - %d ) - %d ) = ( %d - %d )' % (va, vb, vc, sn, 2 * mn))
        L = w.s([l2, eqc], 'eqtri', '( ( ( bToNat ` %s ) - ( bToNat ` %s ) ) - ( bToNat ` %s ) ) = ( %d - %d )' % (a, b, c, sn, 2 * mn))
        return w.s([L, r1], 'eqtr4i', '( ( ( bToNat ` %s ) - ( bToNat ` %s ) ) - ( bToNat ` %s ) ) = ( ( bToNat ` ( ( %s sumBit %s ) ` %s ) ) - ( 2 x. ( bToNat ` ( ( %s borrow %s ) ` %s ) ) ) )' % (a, b, c, a, b, c, a, b, c))

    if want('bwfullsub'):
        eightcases('bwfullsub', 'The full subtractor: the input bit minus the two subtrahend bits is the difference bit minus twice the borrow bit.',
                   '( ( ( bToNat ` A ) - ( bToNat ` B ) ) - ( bToNat ` C ) )',
                   '( ( bToNat ` ( ( A sumBit B ) ` C ) ) - ( 2 x. ( bToNat ` ( ( A borrow B ) ` C ) ) ) )', leaf_sub)
