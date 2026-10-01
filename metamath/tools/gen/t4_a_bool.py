"""Sortie T4, group A: Booleans, 3o, bToNat, Ncmp (T4-blueprint section 3.1)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t4lib import *
import num

only = sys.argv[1:]


def want(label):
    return not only or label in only


def run(w):
    return w.run()


if __name__ == '__main__':
    # ---- bwel2o
    if want('bwel2o'):
        w = W('bwel2o', 'A Boolean is false or true: an element of 2o is (/) or 1o.')
        d = w.s([], 'df2o3', '2o = { (/) , 1o }')
        e = w.s([d], 'eleq2i', '( B e. 2o <-> B e. { (/) , 1o } )')
        p = w.s([], 'elpri', '( B e. { (/) , 1o } -> ( B = (/) \\/ B = 1o ) )')
        w.qed([e, p], 'sylbi', '( B e. 2o -> ( B = (/) \\/ B = 1o ) )'); run(w)

    # ---- bwel2on
    if want('bwel2on'):
        w = W('bwel2on', 'A Boolean that is not true is false.')
        d = w.s([], 'bwel2o', '( B e. 2o -> ( B = (/) \\/ B = 1o ) )')
        oc = w.s([], 'orcom', '( ( B = (/) \\/ B = 1o ) <-> ( B = 1o \\/ B = (/) ) )')
        d2 = w.s([d, oc], 'sylib', '( B e. 2o -> ( B = 1o \\/ B = (/) ) )')
        p = w.s([], 'pm2.53', '( ( B = 1o \\/ B = (/) ) -> ( -. B = 1o -> B = (/) ) )')
        f = w.s([d2, p], 'syl', '( B e. 2o -> ( -. B = 1o -> B = (/) ) )')
        n = w.s([], '1n0', '1o =/= (/)'); n2 = w.s([n], 'nesymi', '-. (/) = 1o')
        e = w.s([], 'eqeq1', '( B = (/) -> ( B = 1o <-> (/) = 1o ) )')
        b = w.s([n2, e], 'mtbiri', '( B = (/) -> -. B = 1o )')
        w.qed([f, b], 'impbid1', '( B e. 2o -> ( -. B = 1o <-> B = (/) ) )'); run(w)

    # ---- bw2oss3o, bw0el3o, bw1oel3o, bw2oel3o, bw1o2o, bw3oex
    if want('bw2oss3o'):
        w = W('bw2oss3o', 'The Booleans are among the three orderings: 2o is a subset of 3o.')
        s = w.s([], 'sssucid', '2o C_ suc 2o'); d = w.s([], 'df-3o', '3o = suc 2o')
        w.qed([s, d], 'sseqtrri', '2o C_ 3o'); run(w)
    if want('bw0el3o'):
        w = W('bw0el3o', 'The ordering lt, (/), is an element of 3o.')
        s = w.s([], 'bw2oss3o', '2o C_ 3o'); e = w.s([], '0el2o', '(/) e. 2o')
        w.qed([s, e], 'sselii', '(/) e. 3o'); run(w)
    if want('bw1oel3o'):
        w = W('bw1oel3o', 'The ordering eq, 1o, is an element of 3o.')
        s = w.s([], 'bw2oss3o', '2o C_ 3o'); e = w.s([], '1oel2o', '1o e. 2o')
        w.qed([s, e], 'sselii', '1o e. 3o'); run(w)
    if want('bw2oel3o'):
        w = W('bw2oel3o', 'The ordering gt, 2o, is an element of 3o.')
        e = w.s([], '2oex', '2o e. _V'); s = w.s([e], 'sucid', '2o e. suc 2o'); d = w.s([], 'df-3o', '3o = suc 2o')
        w.qed([s, d], 'eleqtrri', '2o e. 3o'); run(w)
    if want('bw1o2o'):
        w = W('bw1o2o', 'The orderings eq and gt differ: 1o is not 2o.')
        e = w.s([], '1oel2o', '1o e. 2o'); i = w.s([], 'elirr', '-. 2o e. 2o')
        n = w.s([], 'nelne2', '( ( 1o e. 2o /\\ -. 2o e. 2o ) -> 1o =/= 2o )')
        w.qed([e, i, n], 'mp2an', '1o =/= 2o'); run(w)
    if want('bw3oex'):
        w = W('bw3oex', '3o is a set.')
        o = w.s([], '3on', '3o e. On'); w.qed([o], 'elexi', '3o e. _V'); run(w)

    # ---- bToNat
    A = 'C e. 2o'
    VAL = 'if ( C = 1o , 1 , 0 )'
    if want('bwbnval'):
        w = W('bwbnval', 'Value of bToNat: 1 for true, 0 for false (Lean: Bool.toNat).')
        cl = mkcl(w, A, {'C': '2o'})
        st, val = defval(w, cl, 'df-btonat', 'bToNat', ['C'])
        assert val == VAL, val
        w.qed([st], 'id' if False else 'a1i', '( %s -> ( bToNat ` C ) = %s )' % (A, VAL)) if False else None
        # the step already has the right formula: promote it
        w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1); run(w)
    if want('bwbn1'):
        w = W('bwbn1', 'The value of true is 1.')
        e = w.s([], '1oel2o', '1o e. 2o'); v = w.s([], 'bwbnval', '( 1o e. 2o -> ( bToNat ` 1o ) = if ( 1o = 1o , 1 , 0 ) )')
        v2 = w.s([e, v], 'ax-mp', '( bToNat ` 1o ) = if ( 1o = 1o , 1 , 0 )')
        q = w.s([], 'eqid', '1o = 1o'); i = w.s([q], 'iftruei', 'if ( 1o = 1o , 1 , 0 ) = 1')
        w.qed([v2, i], 'eqtri', '( bToNat ` 1o ) = 1'); run(w)
    if want('bwbn0'):
        w = W('bwbn0', 'The value of false is 0.')
        e = w.s([], '0el2o', '(/) e. 2o'); v = w.s([], 'bwbnval', '( (/) e. 2o -> ( bToNat ` (/) ) = if ( (/) = 1o , 1 , 0 ) )')
        v2 = w.s([e, v], 'ax-mp', '( bToNat ` (/) ) = if ( (/) = 1o , 1 , 0 )')
        n = w.s([], '1n0', '1o =/= (/)'); n2 = w.s([n], 'nesymi', '-. (/) = 1o'); i = w.s([n2], 'iffalsei', 'if ( (/) = 1o , 1 , 0 ) = 0')
        w.qed([v2, i], 'eqtri', '( bToNat ` (/) ) = 0'); run(w)
    if want('bwbncl'):
        w = W('bwbncl', 'The value of a Boolean is a nonnegative integer.')
        v = w.s([], 'bwbnval', '( %s -> ( bToNat ` C ) = %s )' % (A, VAL))
        cl = mkcl(w, A, {'C': '2o'})
        m = cl.mem(VAL, 'NN0')
        w.qed([v, m], 'eqeltrd', '( %s -> ( bToNat ` C ) e. NN0 )' % A); run(w)

    def bncase(w, ante, eqstep, v, out):
        """( ante -> ( bToNat ` C ) = out ) from ( ante -> C = v ), out the closed value"""
        f = w.s([eqstep], 'fveq2d', '( %s -> ( bToNat ` C ) = ( bToNat ` %s ) )' % (ante, v))
        c = w.s([], 'bwbn1' if v == '1o' else 'bwbn0', '( bToNat ` %s ) = %s' % (v, out))
        return w.s([f, c], 'eqtrdi', '( %s -> ( bToNat ` C ) = %s )' % (ante, out))

    if want('bwbnle1'):
        w = W('bwbnle1', 'The value of a Boolean is at most 1.')
        m = w.s([], 'id', '( %s -> C e. 2o )' % A)
        def body(a2, eq, v):
            out = '1' if v == '1o' else '0'
            s = bncase(w, a2, eq, v, out)
            le = w.s([], '1le1' if v == '1o' else '0le1', '%s <_ 1' % out)
            led = w.s([le], 'a1i', '( %s -> %s <_ 1 )' % (a2, out))
            return w.s([s, led], 'eqbrtrd', '( %s -> ( bToNat ` C ) <_ 1 )' % a2)
        st = cases2o(w, A, 'C', m, body, '( bToNat ` C ) <_ 1')
        w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1); run(w)

    for lab, target, desc in (('bwbneq1', '1', 'The value of a Boolean is 1 exactly when it is true.'),
                              ('bwbneq0', '0', 'The value of a Boolean is 0 exactly when it is false.')):
        if not want(lab):
            continue
        w = W(lab, desc)
        m = w.s([], 'id', '( %s -> C e. 2o )' % A)
        tv = '1o' if target == '1' else '(/)'
        concl = '( ( bToNat ` C ) = %s <-> C = %s )' % (target, tv)
        def body(a2, eq, v, target=target, tv=tv, concl=concl):
            out = '1' if v == '1o' else '0'
            s = bncase(w, a2, eq, v, out)
            l = w.s([s], 'eqeq1d', '( %s -> ( ( bToNat ` C ) = %s <-> %s = %s ) )' % (a2, target, out, target))
            r = w.s([eq], 'eqeq1d', '( %s -> ( C = %s <-> %s = %s ) )' % (a2, tv, v, tv))
            if v == tv:
                lt = w.s([], 'eqid', '%s = %s' % (out, out)); ltd = w.s([lt], 'a1i', '( %s -> %s = %s )' % (a2, out, out))
                rt = w.s([], 'eqid', '%s = %s' % (v, v)); rtd = w.s([rt], 'a1i', '( %s -> %s = %s )' % (a2, v, v))
                l2 = w.s([ltd, l], 'mpbird', '( %s -> ( bToNat ` C ) = %s )' % (a2, target))
                r2 = w.s([rtd, r], 'mpbird', '( %s -> C = %s )' % (a2, tv))
                return w.s([l2, r2], '2thd', '( %s -> %s )' % (a2, concl))
            # false on both sides
            if out == '0':
                ne = w.s([], '0ne1', '0 =/= 1'); nn = w.s([ne], 'neii', '-. 0 = 1')
            else:
                ne = w.s([], '0ne1', '0 =/= 1'); nn = w.s([ne], 'nesymi', '-. 1 = 0')
            nnd = w.s([nn], 'a1i', '( %s -> -. %s = %s )' % (a2, out, target))
            l2 = w.s([nnd, l], 'mtbird', '( %s -> -. ( bToNat ` C ) = %s )' % (a2, target))
            n1 = w.s([], '1n0', '1o =/= (/)')
            if v == '(/)':
                n2 = w.s([n1], 'nesymi', '-. (/) = 1o')
            else:
                n2 = w.s([n1], 'neii', '-. 1o = (/)')
            n2d = w.s([n2], 'a1i', '( %s -> -. %s = %s )' % (a2, v, tv))
            r2 = w.s([n2d, r], 'mtbird', '( %s -> -. C = %s )' % (a2, tv))
            return w.s([l2, r2], '2falsed', '( %s -> %s )' % (a2, concl))
        st = cases2o(w, A, 'C', m, body, concl)
        w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1); run(w)

    # ---- Ncmp
    AN = '( A e. NN0 /\\ B e. NN0 )'
    NV = 'if ( A = B , 1o , if ( A < B , (/) , 2o ) )'
    if want('ncmpval'):
        w = W('ncmpval', 'Value of Ncmp: the comparison of two natural numbers as an ordering (Lean: compare).')
        lv = conj_leaves(w, AN, [('A', 'NN0'), ('B', 'NN0')])
        cl = Cl(w, AN, lv)
        st, val = defval(w, cl, 'df-ncmp', 'Ncmp', ['A', 'B'])
        assert val == NV, val
        w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1); run(w)
    if want('ncmpcl'):
        w = W('ncmpcl', 'Closure of Ncmp: an ordering.')
        v = w.s([], 'ncmpval', '( %s -> ( A Ncmp B ) = %s )' % (AN, NV))
        lv = conj_leaves(w, AN, [('A', 'NN0'), ('B', 'NN0')])
        cl = Cl(w, AN, lv)
        m = cl.mem(NV, '3o')
        w.qed([v, m], 'eqeltrd', '( %s -> ( A Ncmp B ) e. 3o )' % AN); run(w)

    def ncmp3(w, lab, concl_fn, desc):
        """three cases A < B, A = B, B < A; concl_fn(a2, case) gives the step"""
        w = W(lab, desc)
        lv = conj_leaves(w, AN, [('A', 'NN0'), ('B', 'NN0')])
        cl = Cl(w, AN, lv)
        ra = cl.mem('A', 'RR'); rb = cl.mem('B', 'RR')
        tri = w.inst('lttri4')
        t = w.s([ra, rb, tri], 'syl2anc', '( %s -> ( A < B \\/ A = B \\/ B < A ) )' % AN)
        v = w.s([], 'ncmpval', '( %s -> ( A Ncmp B ) = %s )' % (AN, NV))
        outs = []
        for case, val in (('A < B', '(/)'), ('A = B', '1o'), ('B < A', '2o')):
            a2 = '( %s /\\ %s )' % (AN, case)
            h = w.s([], 'simpr', '( %s -> %s )' % (a2, case))
            v2 = w.s([v], 'adantr', '( %s -> ( A Ncmp B ) = %s )' % (a2, NV))
            ra2 = w.s([ra], 'adantr', '( %s -> A e. RR )' % a2); rb2 = w.s([rb], 'adantr', '( %s -> B e. RR )' % a2)
            # the facts of the case: which of A = B, A < B hold
            if case == 'A = B':
                eq = h
                ir = w.s([eq], 'iftrued', '( %s -> %s = 1o )' % (a2, NV))
                facts = {'eq': eq}
            else:
                if case == 'A < B':
                    ne = w.s([ra2, h], 'ltned', '( %s -> A =/= B )' % a2)
                    lt = h
                else:
                    ne0 = w.s([rb2, h], 'ltned', '( %s -> B =/= A )' % a2)
                    ne = w.s([ne0], 'necomd', '( %s -> A =/= B )' % a2)
                    ns = w.inst('ltnsym')
                    nl0 = w.s([rb2, ra2, ns], 'syl2anc', '( %s -> ( B < A -> -. A < B ) )' % a2)
                    nlt = w.s([h, nl0], 'mpd', '( %s -> -. A < B )' % a2)
                neq = w.s([ne], 'neneqd', '( %s -> -. A = B )' % a2)
                i1 = w.s([neq], 'iffalsed', '( %s -> %s = if ( A < B , (/) , 2o ) )' % (a2, NV))
                if case == 'A < B':
                    i2 = w.s([lt], 'iftrued', '( %s -> if ( A < B , (/) , 2o ) = (/) )' % a2)
                    facts = {'lt': lt, 'neq': neq}
                else:
                    i2 = w.s([nlt], 'iffalsed', '( %s -> if ( A < B , (/) , 2o ) = 2o )' % a2)
                    facts = {'gt': h, 'neq': neq, 'nlt': nlt}
                ir = w.s([i1, i2], 'eqtrd', '( %s -> %s = %s )' % (a2, NV, val))
            vv = w.s([v2, ir], 'eqtrd', '( %s -> ( A Ncmp B ) = %s )' % (a2, val))
            outs.append(concl_fn(a2, case, val, vv, facts))
        st = w.s(outs + [t], 'mpjao3dan', '( %s -> %s )' % (AN, concl_fn.concl))
        w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1); run(w)

    def mk(target, rhs, truth_case):
        """concl: ( ( A Ncmp B ) = target <-> rhs ); true in truth_case"""
        def f(a2, case, val, vv, facts):
            l = w_.s([vv], 'eqeq1d', '( %s -> ( ( A Ncmp B ) = %s <-> %s = %s ) )' % (a2, target, val, target))
            if case == truth_case:
                q = w_.s([], 'eqid', '%s = %s' % (val, val)); qd = w_.s([q], 'a1i', '( %s -> %s = %s )' % (a2, val, val))
                l2 = w_.s([qd, l], 'mpbird', '( %s -> ( A Ncmp B ) = %s )' % (a2, target))
                r = facts['eq'] if rhs == 'A = B' else (facts['lt'] if rhs == 'A < B' else facts['gt'])
                return w_.s([l2, r], '2thd', '( %s -> %s )' % (a2, f.concl))
            # value differs from target: closed inequality of ordinals
            pe = PropEval(w_)
            tv, ts = pe.lit(val, target)
            assert not tv
            # ts: ( T. -> -. val = target ); make it closed
            tru = w_.s([], 'tru', 'T.'); nq = w_.s([tru, ts], 'ax-mp', '-. %s = %s' % (val, target))
            nqd = w_.s([nq], 'a1i', '( %s -> -. %s = %s )' % (a2, val, target))
            l2 = w_.s([nqd, l], 'mtbird', '( %s -> -. ( A Ncmp B ) = %s )' % (a2, target))
            # rhs false in this case
            if rhs == 'A = B':
                r = facts['neq']
            elif rhs == 'A < B':
                if case == 'A = B':
                    ra = w_.s([], 'nn0red', '( %s -> A e. RR )' % a2) if False else None
                    ra = w_.s([w_.s([], 'simpll', '( %s -> A e. NN0 )' % a2)], 'nn0red', '( %s -> A e. RR )' % a2)
                    nr = w_.s([ra], 'ltnrd', '( %s -> -. A < A )' % a2)
                    bi = w_.s([facts['eq']], 'breq2d', '( %s -> ( A < A <-> A < B ) )' % a2)
                    r = w_.s([nr, bi], 'mtbid', '( %s -> -. A < B )' % a2)
                else:
                    r = facts['nlt']
            else:  # rhs B < A
                if case == 'A = B':
                    ra = w_.s([w_.s([], 'simpll', '( %s -> A e. NN0 )' % a2)], 'nn0red', '( %s -> A e. RR )' % a2)
                    nr = w_.s([ra], 'ltnrd', '( %s -> -. A < A )' % a2)
                    bi = w_.s([facts['eq']], 'breq1d', '( %s -> ( A < A <-> B < A ) )' % a2)
                    r = w_.s([nr, bi], 'mtbid', '( %s -> -. B < A )' % a2)
                else:
                    ra = w_.s([w_.s([], 'simpll', '( %s -> A e. NN0 )' % a2)], 'nn0red', '( %s -> A e. RR )' % a2)
                    rb = w_.s([w_.s([], 'simplr', '( %s -> B e. NN0 )' % a2)], 'nn0red', '( %s -> B e. RR )' % a2)
                    ns = w_.inst('ltnsym')
                    nl0 = w_.s([ra, rb, ns], 'syl2anc', '( %s -> ( A < B -> -. B < A ) )' % a2)
                    r = w_.s([facts['lt'], nl0], 'mpd', '( %s -> -. B < A )' % a2)
            return w_.s([l2, r], '2falsed', '( %s -> %s )' % (a2, f.concl))
        f.concl = '( ( A Ncmp B ) = %s <-> %s )' % (target, rhs)
        return f

    for lab, target, rhs, tc, desc in (('ncmpeq', '1o', 'A = B', 'A = B', 'Ncmp says eq exactly for equal numbers.'),
                                       ('ncmplt', '(/)', 'A < B', 'A < B', 'Ncmp says lt exactly for a smaller first number.'),
                                       ('ncmpgt', '2o', 'B < A', 'B < A', 'Ncmp says gt exactly for a larger first number.')):
        if not want(lab):
            continue
        w_ = None
        class _H:  # noqa
            pass
        # ncmp3 creates the worksheet; bind w_ through a closure trick
        def concl_fn_factory(target=target, rhs=rhs, tc=tc):
            return mk(target, rhs, tc)
        # build with a fresh W inside ncmp3: we need w_ to refer to it, so wrap
        def ncmp3w(lab, desc, target=target, rhs=rhs, tc=tc):
            global w_
            w_ = W(lab, desc)
            f = mk(target, rhs, tc)
            w = w_
            lv = conj_leaves(w, AN, [('A', 'NN0'), ('B', 'NN0')])
            cl = Cl(w, AN, lv)
            ra = cl.mem('A', 'RR'); rb = cl.mem('B', 'RR')
            tri = w.inst('lttri4')
            t = w.s([ra, rb, tri], 'syl2anc', '( %s -> ( A < B \\/ A = B \\/ B < A ) )' % AN)
            v = w.s([], 'ncmpval', '( %s -> ( A Ncmp B ) = %s )' % (AN, NV))
            outs = []
            for case, val in (('A < B', '(/)'), ('A = B', '1o'), ('B < A', '2o')):
                a2 = '( %s /\\ %s )' % (AN, case)
                h = w.s([], 'simpr', '( %s -> %s )' % (a2, case))
                v2 = w.s([v], 'adantr', '( %s -> ( A Ncmp B ) = %s )' % (a2, NV))
                ra2 = w.s([ra], 'adantr', '( %s -> A e. RR )' % a2); rb2 = w.s([rb], 'adantr', '( %s -> B e. RR )' % a2)
                if case == 'A = B':
                    ir = w.s([h], 'iftrued', '( %s -> %s = 1o )' % (a2, NV))
                    facts = {'eq': h}
                else:
                    if case == 'A < B':
                        ne = w.s([ra2, h], 'ltned', '( %s -> A =/= B )' % a2)
                    else:
                        ne0 = w.s([rb2, h], 'ltned', '( %s -> B =/= A )' % a2)
                        ne = w.s([ne0], 'necomd', '( %s -> A =/= B )' % a2)
                        ns = w.inst('ltnsym')
                        nl0 = w.s([rb2, ra2, ns], 'syl2anc', '( %s -> ( B < A -> -. A < B ) )' % a2)
                        nlt = w.s([h, nl0], 'mpd', '( %s -> -. A < B )' % a2)
                    neq = w.s([ne], 'neneqd', '( %s -> -. A = B )' % a2)
                    i1 = w.s([neq], 'iffalsed', '( %s -> %s = if ( A < B , (/) , 2o ) )' % (a2, NV))
                    if case == 'A < B':
                        i2 = w.s([h], 'iftrued', '( %s -> if ( A < B , (/) , 2o ) = (/) )' % a2)
                        facts = {'lt': h, 'neq': neq}
                    else:
                        i2 = w.s([nlt], 'iffalsed', '( %s -> if ( A < B , (/) , 2o ) = 2o )' % a2)
                        facts = {'gt': h, 'neq': neq, 'nlt': nlt}
                    ir = w.s([i1, i2], 'eqtrd', '( %s -> %s = %s )' % (a2, NV, val))
                vv = w.s([v2, ir], 'eqtrd', '( %s -> ( A Ncmp B ) = %s )' % (a2, val))
                outs.append(f(a2, case, val, vv, facts))
            st = w.s(outs + [t], 'mpjao3dan', '( %s -> %s )' % (AN, f.concl))
            w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1); run(w)
        ncmp3w(lab, desc)
