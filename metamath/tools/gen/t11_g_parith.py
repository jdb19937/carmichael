"""T11: the list arithmetic of the pool loop (Steps23.lean ` poolGo_append ` , ` poolGo_mem ` , ` poolGo_length_le_cost ` ).

  tmpgapp   ` poolGo x z k ( A ++ B ) ` is the concatenation of the two results, the costs added
  tmpgmem   every kept ` p ` has ` p <_ x , z < p ` ; the result is not longer than the cost, nor is the input

    MM_DB=sorties/t11.mm python3 tools/gen/t11_g_parith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
from lin import linarith, lineq
from cl import Closure

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


CSV = '( <" P "> ++ V )'
WN = '( Word NN0 X. NN0 )'
FZG = '( ( F e. NN0 /\\ Z e. NN0 ) /\\ G e. NN0 )'
PG = lambda s: '( ( ( F PoolGo Z ) ` G ) ` %s )' % s
P1 = lambda s: '( 1st ` %s )' % PG(s)
P2 = lambda s: '( 2nd ` %s )' % PG(s)
PP = '( ( P x. G ) + 1 )'
COND = '( %s <_ F /\\ Z < %s )' % (PP, PP)
PRIME = '( 1st ` ( IsPrimeTD ` %s ) ) = 1o' % PP
IP2 = '( 2nd ` ( IsPrimeTD ` %s ) )' % PP
STMTS = {}


def cf(w, ph, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            f = l.split('|-', 1)[1].strip()
            assert f.startswith('( %s -> ' % ph), (f[:150], ph[:150])
            return f[len('( %s -> ' % ph):-2]
    raise KeyError(st)


def pg_cases(w, A, fzg, pn, tw, T):
    """the three cases of ` poolGo ` at ( <" P "> ++ T ) under A: returns dict of (antecedent, 1st-eq, 2nd-eq) for
    'F' ( -. COND ), 'P' ( COND , prime ), 'N' ( COND , not prime ), and the closure steps"""
    s = w.s
    CS_ = '( <" P "> ++ %s )' % T
    fn = s([fzg], 'simpld', '( %s -> ( F e. NN0 /\\ Z e. NN0 ) )' % A)
    gn = s([fzg], 'simprd', '( %s -> G e. NN0 )' % A)
    cs = s([s([fzg, pn], 'jca', '( %s -> ( %s /\\ P e. NN0 ) )' % (A, FZG)), tw, w.inst('poolgocs')], 'syl2anc',
           '( %s -> %s = if ( %s , <. if ( %s , ( <" %s "> ++ %s ) , %s ) , ( ( %s + %s ) + 1 ) >. , <. %s , ( %s + 1 ) >. ) )'
           % (A, PG(CS_), COND, PRIME, PP, P1(T), P1(T), P2(T), IP2, P1(T), P2(T)))
    IN = 'if ( %s , ( <" %s "> ++ %s ) , %s )' % (PRIME, PP, P1(T), P1(T))
    ct, cf_ = ifproj(w, A, PG(CS_), cs, COND, '<. %s , ( ( %s + %s ) + 1 ) >.' % (IN, P2(T), IP2), '<. %s , ( %s + 1 ) >.' % (P1(T), P2(T)))
    cl = s([s([fzg, tw], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (A, FZG, T)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A, PG(T), WN))
    a1, b1 = paircl(w, A, PG(T), cl, 'Word NN0', 'NN0')
    pp = s([s([pn, gn], 'nn0mulcld', '( %s -> ( P x. G ) e. NN0 )' % A), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A, PP))
    ipc = s([pp, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (A, PP))
    ip1, ip2 = paircl(w, A, '( IsPrimeTD ` %s )' % PP, ipc, '2o', 'NN0')
    out = {'a1': a1, 'b1': b1, 'pp': pp, 'ip2': ip2}
    AF = '( %s /\\ -. %s )' % (A, COND)
    LF = lambda st: s([st], 'adantr', '( %s -> %s )' % (AF, cf(w, A, st)))
    fF1 = projeq(w, AF, PG(CS_), cf_, P1(T), '( %s + 1 )' % P2(T), s([LF(a1)], 'elexd', '( %s -> %s e. _V )' % (AF, P1(T))),
                 s([s([LF(b1), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (AF, P2(T)))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (AF, P2(T))), 1)
    fF2 = projeq(w, AF, PG(CS_), cf_, P1(T), '( %s + 1 )' % P2(T), s([LF(a1)], 'elexd', '( %s -> %s e. _V )' % (AF, P1(T))),
                 s([s([LF(b1), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (AF, P2(T)))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (AF, P2(T))), 2)
    out['F'] = (AF, fF1, fF2)
    AT = '( %s /\\ %s )' % (A, COND)
    LT = lambda st: s([st], 'adantr', '( %s -> %s )' % (AT, cf(w, A, st)))
    c2 = '( ( %s + %s ) + 1 )' % (P2(T), IP2)
    c2n = s([s([LT(b1), LT(ip2)], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (AT, P2(T), IP2)), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (AT, c2))
    inw = s([s([s([s([LT(pp), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (AT, PP)), LT(a1), w.inst('ccatcl')], 'syl2anc',
                  '( %s -> ( <" %s "> ++ %s ) e. Word NN0 )' % (AT, PP, P1(T))), LT(a1)], 'ifcld', '( %s -> %s e. Word NN0 )' % (AT, IN))], 'elexd',
            '( %s -> %s e. _V )' % (AT, IN))
    t1 = projeq(w, AT, PG(CS_), ct, IN, c2, inw, s([c2n], 'elexd', '( %s -> %s e. _V )' % (AT, c2)), 1)
    t2 = projeq(w, AT, PG(CS_), ct, IN, c2, inw, s([c2n], 'elexd', '( %s -> %s e. _V )' % (AT, c2)), 2)
    ip, inp = ifproj(w, AT, P1(CS_), t1, PRIME, '( <" %s "> ++ %s )' % (PP, P1(T)), P1(T))
    APr = '( %s /\\ %s )' % (AT, PRIME)
    ANp = '( %s /\\ -. %s )' % (AT, PRIME)
    out['P'] = (APr, ip, s([t2], 'adantr', '( %s -> %s = %s )' % (APr, P2(CS_), c2)))
    out['N'] = (ANp, inp, s([t2], 'adantr', '( %s -> %s = %s )' % (ANp, P2(CS_), c2)))
    out['AT'] = AT
    return out


# ======================================================================= tmpgapp
PHI_APP = '( ( %s /\\ B e. Word NN0 ) -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (FZG, PG('( s ++ B )'), P1('s'), P1('B'), P2('s'), P2('B'))
STMTS['tmpgapp'] = '( ( ( %s /\\ B e. Word NN0 ) /\\ S e. Word NN0 ) -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (
    FZG, PG('( S ++ B )'), P1('S'), P1('B'), P2('S'), P2('B'))


def _bapp(w, goal):
    s = w.s
    A = '( %s /\\ B e. Word NN0 )' % FZG
    fzg = s([], 'simpl', '( %s -> %s )' % (A, FZG))
    bw = s([], 'simpr', '( %s -> B e. Word NN0 )' % A)
    e0 = s([s([bw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ B ) = B )' % A)], 'fveq2d', '( %s -> %s = %s )' % (A, PG('( (/) ++ B )'), PG('B')))
    p0 = s([fzg, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (A, PG('(/)')))
    z = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    z2 = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    q1 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 1)
    q2 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 2)
    cl = s([s([fzg, bw], 'jca', '( %s -> ( %s /\\ B e. Word NN0 ) )' % (A, FZG)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A, PG('B'), WN))
    a1, b1 = paircl(w, A, PG('B'), cl, 'Word NN0', 'NN0')
    r1 = s([s([q1], 'oveq1d', '( %s -> ( %s ++ %s ) = ( (/) ++ %s ) )' % (A, P1('(/)'), P1('B'), P1('B'))), s([a1, w.inst('ccatlid')], 'syl',
                                                                                                      '( %s -> ( (/) ++ %s ) = %s )' % (A, P1('B'), P1('B')))],
           'eqtrd', '( %s -> ( %s ++ %s ) = %s )' % (A, P1('(/)'), P1('B'), P1('B')))
    r2 = s([s([q2], 'oveq1d', '( %s -> ( %s + %s ) = ( 0 + %s ) )' % (A, P2('(/)'), P2('B'), P2('B'))), s([s([b1], 'nn0cnd', '( %s -> %s e. CC )' % (A, P2('B')))],
                                                                                                   'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A, P2('B'), P2('B')))],
           'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A, P2('(/)'), P2('B'), P2('B')))
    op = s([r1, r2], 'opeq12d', '( %s -> <. ( %s ++ %s ) , ( %s + %s ) >. = <. %s , %s >. )' % (A, P1('(/)'), P1('B'), P2('(/)'), P2('B'), P1('B'), P2('B')))
    pr = s([cl, w.inst('1st2nd2')], 'syl', '( %s -> %s = <. %s , %s >. )' % (A, PG('B'), P1('B'), P2('B')))
    w.qed([s([e0, pr], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (A, PG('( (/) ++ B )'), P1('B'), P2('B'))), op], 'eqtr4d', goal)


def _sapp(w, A, ih, co):
    s = w.s
    A2 = '( %s /\\ ( %s /\\ B e. Word NN0 ) )' % (A, FZG)
    vs = s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    hb = s([], 'simpr', '( %s -> ( %s /\\ B e. Word NN0 ) )' % (A2, FZG))
    fzg = s([hb], 'simpld', '( %s -> %s )' % (A2, FZG))
    bw = s([hb], 'simprd', '( %s -> B e. Word NN0 )' % A2)
    ihs = s([s([], 'simpl3', '( %s -> %s )' % (A2, ih)), hb], 'mpd', '( %s -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (A2, PG('( V ++ B )'), P1('V'), P1('B'), P2('V'), P2('B')))
    VB = '( V ++ B )'
    vb = s([vs, bw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, VB))
    sp = s([pn, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A2)
    ass = s([sp, vs, bw, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ B ) = ( <" P "> ++ %s ) )' % (A2, CSV, VB))
    eL = s([ass], 'fveq2d', '( %s -> %s = %s )' % (A2, PG('( %s ++ B )' % CSV), PG('( <" P "> ++ %s )' % VB)))
    cV = pg_cases(w, A2, fzg, pn, vs, 'V')
    cB = pg_cases(w, A2, fzg, pn, vb, VB)
    # IH components
    clV = s([s([fzg, vs], 'jca', '( %s -> ( %s /\\ V e. Word NN0 ) )' % (A2, FZG)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A2, PG('V'), WN))
    clB = s([s([fzg, bw], 'jca', '( %s -> ( %s /\\ B e. Word NN0 ) )' % (A2, FZG)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A2, PG('B'), WN))
    aV, bV = paircl(w, A2, PG('V'), clV, 'Word NN0', 'NN0')
    aB, bB = paircl(w, A2, PG('B'), clB, 'Word NN0', 'NN0')
    X1 = '( %s ++ %s )' % (P1('V'), P1('B'))
    X2 = '( %s + %s )' % (P2('V'), P2('B'))
    x1v = s([s([aV, aB, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, X1))], 'elexd', '( %s -> %s e. _V )' % (A2, X1))
    x2v = s([s([bV, bB], 'nn0addcld', '( %s -> %s e. NN0 )' % (A2, X2))], 'elexd', '( %s -> %s e. _V )' % (A2, X2))
    i1 = projeq(w, A2, PG(VB), ihs, X1, X2, x1v, x2v, 1)
    i2 = projeq(w, A2, PG(VB), ihs, X1, X2, x1v, x2v, 2)
    CSVB = '( <" P "> ++ %s )' % VB
    RES1 = '( %s ++ %s )' % (P1(CSV), P1('B'))
    RES2 = '( %s + %s )' % (P2(CSV), P2('B'))
    res = {}
    for k in ('F', 'P', 'N'):
        Ak, e1B, e2B = cB[k]
        _, e1V, e2V = cV[k]
        L = lambda st: lift(w, Ak, A2, st)
        # 1st
        if k == 'P':
            f1 = s([e1B, s([L(i1)], 'oveq2d', '( %s -> ( <" %s "> ++ %s ) = ( <" %s "> ++ %s ) )' % (Ak, PP, P1(VB), PP, X1))], 'eqtrd',
                   '( %s -> %s = ( <" %s "> ++ %s ) )' % (Ak, P1(CSVB), PP, X1))
            sp_ = s([s([L(cB['pp']), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (Ak, PP))], 'id', '') if False else \
                s([L(cB['pp']), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (Ak, PP))
            as_ = s([sp_, L(aV), L(aB), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ %s ) ++ %s ) = ( <" %s "> ++ %s ) )' % (Ak, PP, P1('V'), P1('B'), PP, X1))
            g1 = s([s([e1V], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ %s ) ++ %s ) )' % (Ak, RES1, PP, P1('V'), P1('B'))), as_], 'eqtrd',
                   '( %s -> %s = ( <" %s "> ++ %s ) )' % (Ak, RES1, PP, X1))
            k1 = s([f1, g1], 'eqtr4d', '( %s -> %s = %s )' % (Ak, P1(CSVB), RES1))
        else:
            f1 = s([e1B, L(i1)], 'eqtrd', '( %s -> %s = %s )' % (Ak, P1(CSVB), X1))
            g1 = s([e1V], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (Ak, RES1, P1('V'), P1('B')))
            k1 = s([f1, g1], 'eqtr4d', '( %s -> %s = %s )' % (Ak, P1(CSVB), RES1))
        # 2nd
        cl_ = Closure(w, Ak, {})
        cl_.leaf(P2('V'), 'NN0', L(bV)); cl_.leaf(P2('B'), 'NN0', L(bB)); cl_.leaf(IP2, 'NN0', L(cB['ip2']))
        cl_.leaf(P2(VB), 'NN0', s([L(i2), cl_.mem(X2, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (Ak, P2(VB))))
        cl_.leaf(P2(CSV), 'NN0', s([e2V, cl_.mem('( %s + 1 )' % P2('V') if k == 'F' else '( ( %s + %s ) + 1 )' % (P2('V'), IP2), 'NN0')], 'eqeltrd',
                                   '( %s -> %s e. NN0 )' % (Ak, P2(CSV))))
        cl_.leaf(P2(CSVB), 'NN0', s([e2B, cl_.mem('( %s + 1 )' % P2(VB) if k == 'F' else '( ( %s + %s ) + 1 )' % (P2(VB), IP2), 'NN0')], 'eqeltrd',
                                    '( %s -> %s e. NN0 )' % (Ak, P2(CSVB))))
        k2 = lineq(w, Ak, P2(CSVB), RES2, hyps=[e2B, e2V, L(i2)], closure=cl_, atoms=[P2('V'), P2('B'), IP2, P2(VB), P2(CSV), P2(CSVB)])
        res[k] = (Ak, k1, k2)
    def comb(i, txt):
        tP = res['P'][i]; tN = res['N'][i]; tF = res['F'][i]
        t = s([tP, tN], 'pm2.61dan', '( %s -> %s )' % (cB['AT'], txt))
        return s([t, tF], 'pm2.61dan', '( %s -> %s )' % (A2, txt))
    k1 = comb(1, '%s = %s' % (P1(CSVB), RES1))
    k2 = comb(2, '%s = %s' % (P2(CSVB), RES2))
    clc = s([s([fzg, s([sp, vb, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, CSVB))], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (A2, FZG, CSVB)),
             w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A2, PG(CSVB), WN))
    pr = s([clc, w.inst('1st2nd2')], 'syl', '( %s -> %s = <. %s , %s >. )' % (A2, PG(CSVB), P1(CSVB), P2(CSVB)))
    op = s([pr, s([k1, k2], 'opeq12d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A2, P1(CSVB), P2(CSVB), RES1, RES2))], 'eqtrd',
           '( %s -> %s = <. %s , %s >. )' % (A2, PG(CSVB), RES1, RES2))
    w.qed([s([eL, op], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (A2, PG('( %s ++ B )' % CSV), RES1, RES2))], 'ex', '( %s -> %s )' % (A, co))


def _fapp(w, st, phit):
    T = '( ( %s /\\ B e. Word NN0 ) /\\ S e. Word NN0 )' % FZG
    sw = w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T)
    a = w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit))
    w.qed([w.s([], 'simpl', '( %s -> ( %s /\\ B e. Word NN0 ) )' % (T, FZG)), a], 'mpd', STMTS['tmpgapp'])


def lift(w, ph2, ph, st):
    """lift st : ( ph -> X ) to ph2 = ( ... ( ph /\\ a ) /\\ b ) by adantr steps"""
    X = cf(w, ph, st)
    # peel ph2 until ph
    chain = []
    t = ph2
    while t != ph:
        inner = t[2:-2]
        toks = inner.split(' ')
        d = 0
        cut = None
        for j, tk in enumerate(toks):
            if tk in ('(', '<.', '{', '<"'):
                d += 1
            elif tk in (')', '>.', '}', '">'):
                d -= 1
            elif d == 0 and tk == '/\\':
                cut = j
        assert cut is not None, t[:200]
        chain.append(t)
        t = ' '.join(toks[:cut])
    cur = st
    cph = ph
    for t2 in reversed(chain):
        cur = w.s([cur], 'adantr', '( %s -> %s )' % (t2, X))
    return cur


# ======================================================================= tmpgmem
C1 = lambda s_: 'A. q e. ran %s ( q <_ F /\\ Z < q )' % P1(s_)
C2 = lambda s_: '( # ` %s ) <_ %s' % (P1(s_), P2(s_))
C3 = lambda s_: '( # ` %s ) <_ %s' % (s_, P2(s_))
MEMB = lambda s_: '( %s /\\ ( %s /\\ %s ) )' % (C1(s_), C2(s_), C3(s_))
PHI_MEM = '( %s -> %s )' % (FZG, MEMB('s'))
STMTS['tmpgmem'] = '( ( %s /\\ S e. Word NN0 ) -> %s )' % (FZG, MEMB('S'))


def _bmem(w, goal):
    s = w.s
    A = FZG
    p0 = s([], 'poolgo0', '( %s -> %s = <. (/) , 0 >. )' % (A, PG('(/)')))
    z = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    z2 = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    q1 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 1)
    q2 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 2)
    r0 = s([s([q1], 'rneqd', '( %s -> ran %s = ran (/) )' % (A, P1('(/)'))), s([s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % A)], 'eqtrd',
           '( %s -> ran %s = (/) )' % (A, P1('(/)')))
    c1 = s([s([r0, w.inst('raleq')], 'syl', '( %s -> ( %s <-> A. q e. (/) ( q <_ F /\\ Z < q ) ) )' % (A, C1('(/)'))),
            s([s([], 'ral0', 'A. q e. (/) ( q <_ F /\\ Z < q )')], 'a1i', '( %s -> A. q e. (/) ( q <_ F /\\ Z < q ) )' % A)], 'mpbird', '( %s -> %s )' % (A, C1('(/)')))
    l1 = s([s([s([q1], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (A, P1('(/)'))), s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % A)],
              'eqtrd', '( %s -> ( # ` %s ) = 0 )' % (A, P1('(/)'))), s([q2], 'eqcomd', '( %s -> 0 = %s )' % (A, P2('(/)')))], 'eqtrd',
           '( %s -> ( # ` %s ) = %s )' % (A, P1('(/)'), P2('(/)')))
    l1r = s([s([s([s([s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A), s([q2], 'eqcomd', '( %s -> 0 = %s )' % (A, P2('(/)')))], 'eqeltrrd',
                  '( %s -> %s e. RR )' % (A, P2('(/)')))], 'id', '') if False else None], 'id', '') if False else None
    p2r = s([s([s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A), s([q2], 'eqcomd', '( %s -> 0 = %s )' % (A, P2('(/)')))], 'eqeltrrd',
            '( %s -> %s e. RR )' % (A, P2('(/)')))
    c2 = s([s([p2r], 'leidd', '( %s -> %s <_ %s )' % (A, P2('(/)'), P2('(/)'))), s([l1], 'eqcomd', '( %s -> %s = ( # ` %s ) )' % (A, P2('(/)'), P1('(/)')))],
           'breqtrrd' if False else 'eqbrtrrd', '') if False else None
    c2 = s([l1, s([p2r], 'leidd', '( %s -> %s <_ %s )' % (A, P2('(/)'), P2('(/)')))], 'eqbrtrd', '( %s -> %s )' % (A, C2('(/)')))
    l3 = s([s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % A), s([q2], 'eqcomd', '( %s -> 0 = %s )' % (A, P2('(/)')))], 'eqtrd',
           '( %s -> ( # ` (/) ) = %s )' % (A, P2('(/)')))
    c3 = s([l3, s([p2r], 'leidd', '( %s -> %s <_ %s )' % (A, P2('(/)'), P2('(/)')))], 'eqbrtrd', '( %s -> %s )' % (A, C3('(/)')))
    w.qed([c1, s([c2, c3], 'jca', '( %s -> ( %s /\\ %s ) )' % (A, C2('(/)'), C3('(/)')))], 'jca', goal)


def _smem(w, A, ih, co):
    s = w.s
    A2 = '( %s /\\ %s )' % (A, FZG)
    vs = s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    fzg = s([], 'simpr', '( %s -> %s )' % (A2, FZG))
    ihs = s([s([], 'simpl3', '( %s -> %s )' % (A2, ih)), fzg], 'mpd', '( %s -> %s )' % (A2, MEMB('V')))
    rV = s([ihs], 'simpld', '( %s -> %s )' % (A2, C1('V')))
    lV = s([s([ihs], 'simprd', '( %s -> ( %s /\\ %s ) )' % (A2, C2('V'), C3('V')))], 'simpld', '( %s -> %s )' % (A2, C2('V')))
    nV = s([s([ihs], 'simprd', '( %s -> ( %s /\\ %s ) )' % (A2, C2('V'), C3('V')))], 'simprd', '( %s -> %s )' % (A2, C3('V')))
    cV = pg_cases(w, A2, fzg, pn, vs, 'V')
    clV = s([s([fzg, vs], 'jca', '( %s -> ( %s /\\ V e. Word NN0 ) )' % (A2, FZG)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A2, PG('V'), WN))
    aV, bV = paircl(w, A2, PG('V'), clV, 'Word NN0', 'NN0')
    nv = s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A2)
    lc = s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    naV = s([aV, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A2, P1('V')))
    res = {}
    for k in ('F', 'P', 'N'):
        Ak, e1, e2 = cV[k]
        L = lambda st: lift(w, Ak, A2, st)
        cl_ = Closure(w, Ak, {})
        cl_.leaf(P2('V'), 'NN0', L(bV)); cl_.leaf(IP2, 'NN0', L(cV['ip2'])); cl_.leaf('( # ` V )', 'NN0', L(nv)); cl_.leaf('( # ` %s )' % P1('V'), 'NN0', L(naV))
        e2v = '( %s + 1 )' % P2('V') if k == 'F' else '( ( %s + %s ) + 1 )' % (P2('V'), IP2)
        cl_.leaf(P2(CSV), 'NN0', s([e2, cl_.mem(e2v, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (Ak, P2(CSV))))
        cl_.leaf('( # ` %s )' % CSV, 'NN0', s([L(lc), cl_.mem('( ( # ` V ) + 1 )', 'NN0')], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (Ak, CSV)))
        k3 = linarith(w, Ak, [L(lc), L(nV), e2, cl_.ge0(IP2)], C3(CSV), closure=cl_, atoms=['( # ` V )', P2('V'), IP2, P2(CSV), '( # ` %s )' % CSV])
        if k == 'P':
            spp = s([L(cV['pp']), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (Ak, PP))
            rr = s([s([e1], 'rneqd', '( %s -> ran %s = ran ( <" %s "> ++ %s ) )' % (Ak, P1(CSV), PP, P1('V'))),
                    s([s([spp, L(aV), w.inst('ccatrn')], 'syl2anc', '( %s -> ran ( <" %s "> ++ %s ) = ( ran <" %s "> u. ran %s ) )' % (Ak, PP, P1('V'), PP, P1('V'))),
                       s([s([s([L(cV['pp'])], 'elexd', '( %s -> %s e. _V )' % (Ak, PP)), w.inst('s1rn')], 'syl', '( %s -> ran <" %s "> = { %s } )' % (Ak, PP, PP))],
                         'uneq1d', '( %s -> ( ran <" %s "> u. ran %s ) = ( { %s } u. ran %s ) )' % (Ak, PP, P1('V'), PP, P1('V')))], 'eqtrd',
                      '( %s -> ran ( <" %s "> ++ %s ) = ( { %s } u. ran %s ) )' % (Ak, PP, P1('V'), PP, P1('V')))], 'eqtrd',
                   '( %s -> ran %s = ( { %s } u. ran %s ) )' % (Ak, P1(CSV), PP, P1('V')))
            BQ = '( q <_ F /\\ Z < q )'
            RU = 'A. q e. ( { %s } u. ran %s ) %s' % (PP, P1('V'), BQ)
            e_ = s([rr, w.inst('raleq')], 'syl', '( %s -> ( %s <-> %s ) )' % (Ak, C1(CSV), RU))
            un = s([], 'ralunb', '( %s <-> ( A. q e. { %s } %s /\\ %s ) )' % (RU, PP, BQ, C1('V')))
            sb = s([s([], 'breq1', '( q = %s -> ( q <_ F <-> %s <_ F ) )' % (PP, PP)), s([], 'breq2', '( q = %s -> ( Z < q <-> Z < %s ) )' % (PP, PP))], 'anbi12d',
                   '( q = %s -> ( %s <-> %s ) )' % (PP, BQ, COND))
            rs = s([s([L(cV['pp'])], 'elexd', '( %s -> %s e. _V )' % (Ak, PP)), s([sb], 'ralsng', '( %s e. _V -> ( A. q e. { %s } %s <-> %s ) )' % (PP, PP, BQ, COND))],
                   'mpbiri' if False else 'syl', '( %s -> ( A. q e. { %s } %s <-> %s ) )' % (Ak, PP, BQ, COND))
            cnd = s([s([], 'simplr', '( %s -> %s )' % (Ak, COND))], 'id', '') if False else s([], 'simplr', '( %s -> %s )' % (Ak, COND))
            both = s([s([rs, cnd], 'mpbird', '( %s -> A. q e. { %s } %s )' % (Ak, PP, BQ)), L(rV)], 'jca', '( %s -> ( A. q e. { %s } %s /\\ %s ) )' % (Ak, PP, BQ, C1('V')))
            k1 = s([s([both, s([un], 'biimpri', '( ( A. q e. { %s } %s /\\ %s ) -> %s )' % (PP, BQ, C1('V'), RU))], 'syl', '( %s -> %s )' % (Ak, RU)), e_], 'mpbird',
                   '( %s -> %s )' % (Ak, C1(CSV)))
            ln = s([s([e1], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( <" %s "> ++ %s ) ) )' % (Ak, P1(CSV), PP, P1('V'))),
                    s([L(cV['pp']), L(aV), w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` ( <" %s "> ++ %s ) ) = ( ( # ` %s ) + 1 ) )' % (Ak, PP, P1('V'), P1('V')))],
                   'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (Ak, P1(CSV), P1('V')))
        else:
            k1 = s([s([s([e1], 'rneqd', '( %s -> ran %s = ran %s )' % (Ak, P1(CSV), P1('V'))), w.inst('raleq')], 'syl',
                      '( %s -> ( %s <-> %s ) )' % (Ak, C1(CSV), C1('V'))), L(rV)], 'mpbird', '( %s -> %s )' % (Ak, C1(CSV)))
            ln = s([e1], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (Ak, P1(CSV), P1('V')))
        cl_.leaf('( # ` %s )' % P1(CSV), 'NN0', s([ln, cl_.mem(cf(w, Ak, ln).split(' = ', 1)[1], 'NN0')], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (Ak, P1(CSV))))
        k2 = linarith(w, Ak, [ln, L(lV), e2, cl_.ge0(IP2)], C2(CSV), closure=cl_, atoms=['( # ` %s )' % P1('V'), P2('V'), IP2, P2(CSV), '( # ` %s )' % P1(CSV)])
        res[k] = (Ak, k1, k2, k3)
    def comb(i, txt):
        t = s([res['P'][i], res['N'][i]], 'pm2.61dan', '( %s -> %s )' % (cV['AT'], txt))
        return s([t, res['F'][i]], 'pm2.61dan', '( %s -> %s )' % (A2, txt))
    k1, k2, k3 = comb(1, C1(CSV)), comb(2, C2(CSV)), comb(3, C3(CSV))
    w.qed([s([k1, s([k2, k3], 'jca', '( %s -> ( %s /\\ %s ) )' % (A2, C2(CSV), C3(CSV)))], 'jca', '( %s -> %s )' % (A2, MEMB(CSV)))], 'ex', '( %s -> %s )' % (A, co))


def _fmem(w, st, phit):
    T = '( %s /\\ S e. Word NN0 )' % FZG
    sw = w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T)
    a = w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit))
    w.qed([w.s([], 'simpl', '( %s -> %s )' % (T, FZG)), a], 'mpd', STMTS['tmpgmem'])


if __name__ == '__main__':
    family(run, 'tmpgapp', PHI_APP, _bapp, _sapp, finish=_fapp,
           desc='Lean ` poolGo_append ` : the pool of a concatenation is the concatenation of the pools, the costs added.', only=only or ['-'])
    family(run, 'tmpgmem', PHI_MEM, _bmem, _smem, finish=_fmem,
           desc='Lean ` poolGo_mem ` , ` poolGo_length_le_cost ` : every kept ` p ` has ` p <_ x ` and ` z < p ` ; neither the pool nor the divisor list is longer than the cost.', only=only or ['-'])
