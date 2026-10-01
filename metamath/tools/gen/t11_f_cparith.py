"""T11: the iteration count of ` coprimeToF ` (PrimList.lean ` cpIter ` , ` lt_cpIter_iff ` , ` coprimeTo_fst ` ).

  tmcp0     ` ( coprimeTo Q k ).2 = 0 <-> Q = [] `
  tmcpch    for ` i < ( coprimeTo Q k ).2 ` : ` i < # Q ` , the ` i ` -th entry divides ` k ` iff the loop stops after it with
            the answer false, and ( it divides or it is the last entry ) iff the loop stops after it

    MM_DB=sorties/t11.mm python3 tools/gen/t11_f_cparith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
from lin import linarith, lineq
from cl import Closure

only = sys.argv[1:]
UNIFY = os.environ.get('T11_UNIFY') == '1'


def run(w):
    if only and w.label not in only:
        return True
    return w.run(unify_only=UNIFY)


CSV = '( <" P "> ++ V )'
B2 = '( 2o X. NN0 )'
CT = lambda s: '( %s CoprimeTo G )' % s
RR_ = lambda s: '( 2nd ` %s )' % CT(s)
CC_ = lambda s: '( 1st ` %s )' % CT(s)
STMTS = {}

# ======================================================================= tmcp0
PHI0 = '( G e. NN0 -> ( %s = 0 <-> s = (/) ) )' % RR_('s')


def _b0(w, goal):
    A = 'G e. NN0'
    v = w.s([], 'coprimeto0', '( %s -> %s = <. 1o , 0 >. )' % (A, CT('(/)')))
    p = projeq(w, A, CT('(/)'), v, '1o', '0', w.s([w.s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % A),
               w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A), 2)
    t2 = w.s([w.s([], 'eqid', '(/) = (/)')], 'a1i', '( %s -> (/) = (/) )' % A)
    w.qed([w.s([p, t2], '2thd', '( %s -> ( %s = 0 <-> (/) = (/) ) )' % (A, RR_('(/)')))], 'id' if False else 'mpbir' if False else 'id', goal) if False else \
        w.qed([p, t2], '2thd', goal)


def _s0(w, A, ih, co):
    A2 = '( %s /\\ G e. NN0 )' % A
    s = w.s
    vs = s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    gn = s([], 'simpr', '( %s -> G e. NN0 )' % A2)
    cs = s([s([gn, pn], 'jca', '( %s -> ( G e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('coprimetocs')], 'syl2anc',
           '( %s -> %s = if ( ( G mod P ) = 0 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) )' % (A2, CT(CSV), CC_('V'), RR_('V')))
    IF = 'if ( ( G mod P ) = 0 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. )' % (CC_('V'), RR_('V'))
    st, sf = ifproj(w, A2, CT(CSV), cs, '( G mod P ) = 0', '<. (/) , 1 >.', '<. %s , ( %s + 1 ) >.' % (CC_('V'), RR_('V')))
    At = '( %s /\\ ( G mod P ) = 0 )' % A2
    Af = '( %s /\\ -. ( G mod P ) = 0 )' % A2
    pt = projeq(w, At, CT(CSV), st, '(/)', '1', s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % At),
                s([s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % At), 2)
    nt = s([pt, s([s([], 'ax-1ne0', '1 =/= 0')], 'a1i', '( %s -> 1 =/= 0 )' % At)], 'eqnetrd', '( %s -> %s =/= 0 )' % (At, RR_(CSV)))
    cl = s([s([vs, gn, w.inst('coprimetocl')], 'syl2anc', '( %s -> %s e. %s )' % (A2, CT('V'), B2))], 'id', '') if False else \
        s([vs, gn, w.inst('coprimetocl')], 'syl2anc', '( %s -> %s e. %s )' % (A2, CT('V'), B2))
    a1, b1 = paircl(w, A2, CT('V'), cl, '2o', 'NN0')
    b1f = s([b1], 'adantr', '( %s -> %s e. NN0 )' % (Af, RR_('V')))
    pf = projeq(w, Af, CT(CSV), sf, CC_('V'), '( %s + 1 )' % RR_('V'), s([s([a1], 'adantr', '( %s -> %s e. 2o )' % (Af, CC_('V')))], 'elexd',
                                                                      '( %s -> %s e. _V )' % (Af, CC_('V'))),
                s([s([b1f, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (Af, RR_('V')))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (Af, RR_('V'))), 2)
    nf = s([pf, s([s([b1f, w.inst('nn0p1nn')], 'syl', '( %s -> ( %s + 1 ) e. NN )' % (Af, RR_('V'))), w.inst('nnne0')], 'syl',
                  '( %s -> ( %s + 1 ) =/= 0 )' % (Af, RR_('V')))], 'eqnetrd', '( %s -> %s =/= 0 )' % (Af, RR_(CSV)))
    ne = s([nt, nf], 'pm2.61dan', '( %s -> %s =/= 0 )' % (A2, RR_(CSV)))
    sp = s([pn, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A2)
    cn = s([s([sp, vs, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, CSV)) if False else sp,
            s([s([s([pn], 'elexd', '( %s -> P e. _V )' % A2), w.inst('s1nz')], 'syl', '( %s -> <" P "> =/= (/) )' % A2)], 'id', '') if False else
            s([s([pn], 'elexd', '( %s -> P e. _V )' % A2), w.inst('s1nz')], 'syl', '( %s -> <" P "> =/= (/) )' % A2)], 'id', '') if False else None
    s1n = s([s([pn], 'elexd', '( %s -> P e. _V )' % A2), w.inst('s1nz')], 'syl', '( %s -> <" P "> =/= (/) )' % A2) if False else \
        s([], 's1nz', '<" P "> =/= (/)')
    c0 = s([sp, vs, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( <" P "> = (/) /\\ V = (/) ) ) )' % (A2, CSV))
    n1 = s([s([s([s1n], 'neii', '-. <" P "> = (/)')], 'a1i', '( %s -> -. <" P "> = (/) )' % A2)], 'intnanrd',
           '( %s -> -. ( <" P "> = (/) /\\ V = (/) ) )' % A2)
    n2 = s([c0, n1], 'mtbird', '( %s -> -. %s = (/) )' % (A2, CSV))
    e = s([s([ne], 'neneqd', '( %s -> -. %s = 0 )' % (A2, RR_(CSV))), n2], '2falsed', '( %s -> ( %s = 0 <-> %s = (/) ) )' % (A2, RR_(CSV), CSV))
    w.qed([e], 'ex', '( %s -> %s )' % (A, co))


def _f0(w, st, phit):
    T = '( S e. Word NN0 /\\ G e. NN0 )'
    sw = w.s([], 'simpl', '( %s -> S e. Word NN0 )' % T)
    a = w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit))
    w.qed([w.s([], 'simpr', '( %s -> G e. NN0 )' % T), a], 'mpd', STMTS['tmcp0'])


STMTS['tmcp0'] = '( ( S e. Word NN0 /\\ G e. NN0 ) -> ( %s = 0 <-> S = (/) ) )' % RR_('S')

# ======================================================================= tmcpch
def BODY(s_, i):
    LT = '%s < ( # ` %s )' % (i, s_)
    MD = '( G mod ( %s ` %s ) ) = 0' % (s_, i)
    RI = '( %s + 1 ) = %s' % (i, RR_(s_))
    CZ = '%s = (/)' % CC_(s_)
    LN = '( %s + 1 ) = ( # ` %s )' % (i, s_)
    return '( %s /\\ ( %s <-> ( %s /\\ %s ) ) /\\ ( ( %s \\/ %s ) <-> %s ) )' % (LT, MD, RI, CZ, MD, LN, RI), (LT, MD, RI, CZ, LN)


QF = lambda s_, i: '( %s < %s -> %s )' % (i, RR_(s_), BODY(s_, i)[0])
PHI_CH = '( G e. NN0 -> A. i e. NN0 %s )' % QF('s', 'i')
STMTS['tmcpch'] = '( ( ( S e. Word NN0 /\\ G e. NN0 ) /\\ ( I e. NN0 /\\ I < %s ) ) -> %s )' % (RR_('S'), BODY('S', 'I')[0])


def cong(w, X, var, repl):
    ante = '%s = %s' % (var, repl)
    idst = w.s([], 'id', '( %s -> %s )' % (ante, ante))
    st, new = w.wcongr(X, {var: repl}, ante, {var: idst})
    return st, new


def _bch(w, goal):
    A = '( G e. NN0 /\\ i e. NN0 )'
    s = w.s
    g0 = s([], 'simpl', '( %s -> G e. NN0 )' % A)
    v = s([g0, w.inst('coprimeto0')], 'syl', '( %s -> %s = <. 1o , 0 >. )' % (A, CT('(/)')))
    p = projeq(w, A, CT('(/)'), v, '1o', '0', s([s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % A),
               s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A), 2)
    nl = s([s([], 'simpr', '( %s -> i e. NN0 )' % A), w.inst('nn0nlt0')], 'syl', '( %s -> -. i < 0 )' % A)
    nl2 = s([s([p], 'breq2d', '( %s -> ( i < %s <-> i < 0 ) )' % (A, RR_('(/)'))), nl], 'mtbird', '( %s -> -. i < %s )' % (A, RR_('(/)')))
    im = s([nl2], 'pm2.21d', '( %s -> %s )' % (A, QF('(/)', 'i')))
    w.qed([s([im], 'ralrimiva', '( G e. NN0 -> A. i e. NN0 %s )' % QF('(/)', 'i'))], 'id' if False else 'mpbir' if False else 'id', goal) if False else \
        w.qed([im], 'ralrimiva', goal)


def _sch(w, A, ih, co):
    s = w.s
    A2 = '( %s /\\ G e. NN0 )' % A
    vs = s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    gn = s([], 'simpr', '( %s -> G e. NN0 )' % A2)
    ihv = s([s([], 'simpl3', '( %s -> %s )' % (A2, ih)), gn], 'mpd', '( %s -> A. i e. NN0 %s )' % (A2, QF('V', 'i')))
    BN = '( ( %s /\\ n e. NN0 ) /\\ n < %s )' % (A2, RR_(CSV))
    L = lambda st, ph0=A2: s([s([st], 'adantr', '( ( %s /\\ n e. NN0 ) -> %s )' % (ph0, cf(w, ph0, st)))], 'adantr', '( %s -> %s )' % (BN, cf(w, ph0, st)))
    nn = s([], 'simplr', '( %s -> n e. NN0 )' % BN)
    nlt = s([], 'simpr', '( %s -> n < %s )' % (BN, RR_(CSV)))
    cs = s([s([L(gn), L(pn)], 'jca', '( %s -> ( G e. NN0 /\\ P e. NN0 ) )' % BN), L(vs), w.inst('coprimetocs')], 'syl2anc',
           '( %s -> %s = if ( ( G mod P ) = 0 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) )' % (BN, CT(CSV), CC_('V'), RR_('V')))
    st, sf = ifproj(w, BN, CT(CSV), cs, '( G mod P ) = 0', '<. (/) , 1 >.', '<. %s , ( %s + 1 ) >.' % (CC_('V'), RR_('V')))
    sp = s([L(pn), w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % BN)
    lc = s([L(pn), L(vs), w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (BN, CSV))
    nv = s([L(vs), w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % BN)
    s1l = s([s([s([L(pn)], 'elexd', '( %s -> P e. _V )' % BN), w.inst('s1len')], 'syl', '( %s -> ( # ` <" P "> ) = 1 )' % BN) if False else
             s([], 's1len', '( # ` <" P "> ) = 1')], 'id', '') if False else None
    lp = s([s([s([], 's1len', '( # ` <" P "> ) = 1')], 'a1i', '( %s -> ( # ` <" P "> ) = 1 )' % BN), s([s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % BN)],
           'breqtrrd', '( %s -> 0 < ( # ` <" P "> ) )' % BN)
    f0 = s([s([sp, L(vs), lp, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = ( <" P "> ` 0 ) )' % (BN, CSV)),
            s([L(pn), w.inst('s1fv')], 'syl', '( %s -> ( <" P "> ` 0 ) = P )' % BN)], 'eqtrd', '( %s -> ( %s ` 0 ) = P )' % (BN, CSV))
    body, (LT, MD, RI, CZ, LN) = BODY(CSV, 'n')
    cl = Closure(w, BN, {'n': ('NN0', nn)})
    cl.leaf('( # ` V )', 'NN0', nv)
    # ---- case T
    BT = '( %s /\\ ( G mod P ) = 0 )' % BN
    LT_ = lambda st: s([st], 'adantr', '( %s -> %s )' % (BT, cf(w, BN, st)))
    pt = projeq(w, BT, CT(CSV), st, '(/)', '1', s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % BT),
                s([s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % BT), 2)
    ct = projeq(w, BT, CT(CSV), st, '(/)', '1', s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % BT),
                s([s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % BT), 1)
    n1 = s([LT_(nlt), pt], 'breqtrd', '( %s -> n < 1 )' % BT)
    n0 = s([n1, s([LT_(nn), w.inst('nn0lt10b')], 'syl', '( %s -> ( n < 1 <-> n = 0 ) )' % BT)], 'mpbid', '( %s -> n = 0 )' % BT)
    fn = s([s([n0], 'fveq2d', '( %s -> ( %s ` n ) = ( %s ` 0 ) )' % (BT, CSV, CSV)), LT_(f0)], 'eqtrd', '( %s -> ( %s ` n ) = P )' % (BT, CSV))
    mdt = s([s([s([fn], 'oveq2d', '( %s -> ( G mod ( %s ` n ) ) = ( G mod P ) )' % (BT, CSV)), s([], 'simpr', '( %s -> ( G mod P ) = 0 )' % BT)], 'eqtrd',
               '( %s -> ( G mod ( %s ` n ) ) = 0 )' % (BT, CSV))], 'id', '') if False else \
        s([s([fn], 'oveq2d', '( %s -> ( G mod ( %s ` n ) ) = ( G mod P ) )' % (BT, CSV)), s([], 'simpr', '( %s -> ( G mod P ) = 0 )' % BT)], 'eqtrd',
          '( %s -> %s )' % (BT, MD))
    clt = Closure(w, BT, {'n': ('NN0', LT_(nn))})
    clt.leaf('( # ` V )', 'NN0', LT_(nv))
    rit = s([s([n0], 'oveq1d', '( %s -> ( n + 1 ) = ( 0 + 1 ) )' % BT), s([s([s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % BT),
                                                                          s([pt], 'eqcomd', '( %s -> 1 = %s )' % (BT, RR_(CSV)))], 'eqtrd',
                                                                        '( %s -> ( 0 + 1 ) = %s )' % (BT, RR_(CSV)))], 'eqtrd', '( %s -> %s )' % (BT, RI))
    ltt = s([s([n0, s([LT_(nv), w.inst('nn0p1nn')], 'syl', '( %s -> ( ( # ` V ) + 1 ) e. NN )' % BT)], 'jca', '') if False else None], 'id', '') if False else None
    lt0 = s([s([n0], 'breq1d', '( %s -> ( n < ( # ` %s ) <-> 0 < ( # ` %s ) ) )' % (BT, CSV, CSV)),
             s([s([s([LT_(nv), w.inst('nn0p1nn')], 'syl', '( %s -> ( ( # ` V ) + 1 ) e. NN )' % BT), w.inst('nngt0')], 'syl',
                  '( %s -> 0 < ( ( # ` V ) + 1 ) )' % BT), s([LT_(lc)], 'eqcomd', '( %s -> ( ( # ` V ) + 1 ) = ( # ` %s ) )' % (BT, CSV))], 'breqtrd',
               '( %s -> 0 < ( # ` %s ) )' % (BT, CSV))], 'mpbird', '( %s -> %s )' % (BT, LT))
    czt = s([ct], 'id', '( %s -> %s )' % (BT, CZ)) if False else ct
    kt2 = s([mdt, s([rit, czt], 'jca', '( %s -> ( %s /\\ %s ) )' % (BT, RI, CZ))], '2thd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (BT, MD, RI, CZ))
    kt3 = s([s([mdt], 'orcd', '( %s -> ( %s \\/ %s ) )' % (BT, MD, LN)), rit], '2thd', '( %s -> ( ( %s \\/ %s ) <-> %s ) )' % (BT, MD, LN, RI))
    bt = s([lt0, kt2, kt3], '3jca', '( %s -> %s )' % (BT, body))
    # ---- case F
    BF = '( %s /\\ -. ( G mod P ) = 0 )' % BN
    LF = lambda st: s([st], 'adantr', '( %s -> %s )' % (BF, cf(w, BN, st)))
    ctv = s([L(vs), L(gn), w.inst('coprimetocl')], 'syl2anc', '( %s -> %s e. %s )' % (BN, CT('V'), B2))
    a1, b1 = paircl(w, BN, CT('V'), ctv, '2o', 'NN0')
    pf = projeq(w, BF, CT(CSV), sf, CC_('V'), '( %s + 1 )' % RR_('V'), s([LF(a1)], 'elexd', '( %s -> %s e. _V )' % (BF, CC_('V'))),
                s([s([LF(b1), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (BF, RR_('V')))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (BF, RR_('V'))), 2)
    cfv = projeq(w, BF, CT(CSV), sf, CC_('V'), '( %s + 1 )' % RR_('V'), s([LF(a1)], 'elexd', '( %s -> %s e. _V )' % (BF, CC_('V'))),
                 s([s([LF(b1), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (BF, RR_('V')))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (BF, RR_('V'))), 1)
    # n = 0
    F0 = '( %s /\\ n = 0 )' % BF
    L0 = lambda st: s([st], 'adantr', '( %s -> %s )' % (F0, cf(w, BF, st)))
    n0 = s([], 'simpr', '( %s -> n = 0 )' % F0)
    fn0 = s([s([n0], 'fveq2d', '( %s -> ( %s ` n ) = ( %s ` 0 ) )' % (F0, CSV, CSV)), L0(LF(f0))], 'eqtrd', '( %s -> ( %s ` n ) = P )' % (F0, CSV))
    mdf = s([s([s([fn0], 'oveq2d', '( %s -> ( G mod ( %s ` n ) ) = ( G mod P ) )' % (F0, CSV))], 'eqeq1d', '( %s -> ( %s <-> ( G mod P ) = 0 ) )' % (F0, MD)),
             L0(s([], 'simpr', '( %s -> -. ( G mod P ) = 0 )' % BF))], 'mtbird', '( %s -> -. %s )' % (F0, MD))
    lt0f = s([s([n0], 'breq1d', '( %s -> ( n < ( # ` %s ) <-> 0 < ( # ` %s ) ) )' % (F0, CSV, CSV)),
              s([s([s([L0(LF(nv)), w.inst('nn0p1nn')], 'syl', '( %s -> ( ( # ` V ) + 1 ) e. NN )' % F0), w.inst('nngt0')], 'syl',
                   '( %s -> 0 < ( ( # ` V ) + 1 ) )' % F0), s([L0(LF(lc))], 'eqcomd', '( %s -> ( ( # ` V ) + 1 ) = ( # ` %s ) )' % (F0, CSV))], 'breqtrd',
                '( %s -> 0 < ( # ` %s ) )' % (F0, CSV))], 'mpbird', '( %s -> %s )' % (F0, LT))
    # RI <-> R(V) = 0 <-> V = (/) ; LN <-> # V = 0 <-> V = (/)
    rv0 = s([L0(LF(L(vs))) if False else L0(LF(L(vs))), L0(LF(L(gn))), w.inst('tmcp0')], 'syl2anc', '( %s -> ( %s = 0 <-> V = (/) ) )' % (F0, RR_('V'))) if False else None
    rv0 = s([s([L0(LF(L(vs))), L0(LF(L(gn)))], 'jca', '( %s -> ( V e. Word NN0 /\\ G e. NN0 ) )' % F0), w.inst('tmcp0')], 'syl',
            '( %s -> ( %s = 0 <-> V = (/) ) )' % (F0, RR_('V')))
    rn0 = s([L0(LF(b1))], 'nn0cnd', '( %s -> %s e. CC )' % (F0, RR_('V')))
    ri1 = s([s([L0(pf)], 'eqeq2d', '( %s -> ( ( n + 1 ) = %s <-> ( n + 1 ) = ( %s + 1 ) ) )' % (F0, RR_(CSV), RR_('V'))),
             s([s([s([L0(LF(nn))], 'nn0cnd', '( %s -> n e. CC )' % F0), rn0, s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % F0)], 'addcan2d',
                  '( %s -> ( ( n + 1 ) = ( %s + 1 ) <-> n = %s ) )' % (F0, RR_('V'), RR_('V'))),
               s([s([n0], 'eqeq1d', '( %s -> ( n = %s <-> 0 = %s ) )' % (F0, RR_('V'), RR_('V'))),
                  s([s([], 'eqcom', '( 0 = %s <-> %s = 0 )' % (RR_('V'), RR_('V')))], 'a1i', '( %s -> ( 0 = %s <-> %s = 0 ) )' % (F0, RR_('V'), RR_('V')))],
                 'bitrd', '( %s -> ( n = %s <-> %s = 0 ) )' % (F0, RR_('V'), RR_('V')))], 'bitrd', '( %s -> ( ( n + 1 ) = ( %s + 1 ) <-> %s = 0 ) )' % (F0, RR_('V'), RR_('V')))],
            'bitrd', '( %s -> ( %s <-> %s = 0 ) )' % (F0, RI, RR_('V')))
    riv = s([ri1, rv0], 'bitrd', '( %s -> ( %s <-> V = (/) ) )' % (F0, RI))
    nvc = s([L0(LF(nv))], 'nn0cnd', '( %s -> ( # ` V ) e. CC )' % F0)
    ln1 = s([s([L0(LF(lc))], 'eqeq2d', '( %s -> ( ( n + 1 ) = ( # ` %s ) <-> ( n + 1 ) = ( ( # ` V ) + 1 ) ) )' % (F0, CSV)),
             s([s([s([L0(LF(nn))], 'nn0cnd', '( %s -> n e. CC )' % F0), nvc, s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % F0)], 'addcan2d',
                  '( %s -> ( ( n + 1 ) = ( ( # ` V ) + 1 ) <-> n = ( # ` V ) ) )' % F0),
               s([s([n0], 'eqeq1d', '( %s -> ( n = ( # ` V ) <-> 0 = ( # ` V ) ) )' % F0),
                  s([s([], 'eqcom', '( 0 = ( # ` V ) <-> ( # ` V ) = 0 )')], 'a1i', '( %s -> ( 0 = ( # ` V ) <-> ( # ` V ) = 0 ) )' % F0)],
                 'bitrd', '( %s -> ( n = ( # ` V ) <-> ( # ` V ) = 0 ) )' % F0)], 'bitrd', '( %s -> ( ( n + 1 ) = ( ( # ` V ) + 1 ) <-> ( # ` V ) = 0 ) )' % F0)],
            'bitrd', '( %s -> ( %s <-> ( # ` V ) = 0 ) )' % (F0, LN))
    lnv = s([ln1, s([s([L0(LF(L(vs)))], 'elexd', '( %s -> V e. _V )' % F0), w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` V ) = 0 <-> V = (/) ) )' % F0)],
            'bitrd', '( %s -> ( %s <-> V = (/) ) )' % (F0, LN))
    # ( MD \/ LN ) <-> LN <-> RI
    bo = s([mdf, w.inst('biorf')], 'syl', '( %s -> ( %s <-> ( %s \\/ %s ) ) )' % (F0, LN, MD, LN))
    k3f = s([bo, s([lnv, riv], 'bitr4d', '( %s -> ( %s <-> %s ) )' % (F0, LN, RI))], 'bitr3d', '( %s -> ( ( %s \\/ %s ) <-> %s ) )' % (F0, MD, LN, RI))
    # -. ( RI /\ CZ ): RI gives V = (/) , then CZ fails
    F1 = '( %s /\\ %s )' % (F0, RI)
    ve = s([s([], 'simpr', '( %s -> %s )' % (F1, RI)), s([riv], 'adantr', '( %s -> ( %s <-> V = (/) ) )' % (F1, RI))], 'mpbid', '( %s -> V = (/) )' % F1)
    c0v = s([s([s([ve], 'oveq1d', '( %s -> %s = ( (/) CoprimeTo G ) )' % (F1, CT('V')))], 'fveq2d', '( %s -> %s = ( 1st ` ( (/) CoprimeTo G ) ) )' % (F1, CC_('V'))),
             projeq(w, F1, CT('(/)'), s([s([L0(LF(L(gn)))], 'adantr', '( %s -> G e. NN0 )' % F1), w.inst('coprimeto0')], 'syl', '( %s -> %s = <. 1o , 0 >. )' % (F1, CT('(/)'))),
                    '1o', '0', s([s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % F1), s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % F1), 1)],
            'eqtrd', '( %s -> %s = 1o )' % (F1, CC_('V')))
    c1 = s([s([s([L0(cfv)], 'adantr', '( %s -> %s = %s )' % (F1, CC_(CSV), CC_('V'))), c0v], 'eqtrd', '( %s -> %s = 1o )' % (F1, CC_(CSV))),
            s([s([], '1n0', '1o =/= (/)')], 'a1i', '( %s -> 1o =/= (/) )' % F1)], 'eqnetrd', '( %s -> %s =/= (/) )' % (F1, CC_(CSV)))
    ncz = s([s([c1], 'neneqd', '( %s -> -. %s )' % (F1, CZ))], 'ex', '( %s -> ( %s -> -. %s ) )' % (F0, RI, CZ))
    nrc = s([ncz, s([], 'imnan', '( ( %s -> -. %s ) <-> -. ( %s /\\ %s ) )' % (RI, CZ, RI, CZ))], 'sylib', '( %s -> -. ( %s /\\ %s ) )' % (F0, RI, CZ))
    k2f = s([mdf, nrc], '2falsed', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (F0, MD, RI, CZ))
    bf0 = s([lt0f, k2f, k3f], '3jca', '( %s -> %s )' % (F0, body))
    # n e. NN
    FP = '( %s /\\ n e. NN )' % BF
    LP = lambda st: s([st], 'adantr', '( %s -> %s )' % (FP, cf(w, BF, st)))
    npn = s([], 'simpr', '( %s -> n e. NN )' % FP)
    M_ = '( n - 1 )'
    mn = s([npn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (FP, M_))
    ncc = s([s([npn], 'nncnd', '( %s -> n e. CC )' % FP)], 'id', '') if False else s([npn], 'nncnd', '( %s -> n e. CC )' % FP)
    nm = s([ncc, w.inst('npcan1')], 'syl', '( %s -> ( %s + 1 ) = n )' % (FP, M_))
    clp = Closure(w, FP, {'n': ('NN0', LP(LF(nn)))})
    clp.leaf(RR_('V'), 'NN0', LP(LF(b1)))
    clp.leaf('( # ` V )', 'NN0', LP(LF(nv)))
    nlt2 = s([LP(LF(nlt)), LP(pf)], 'breqtrd', '( %s -> n < ( %s + 1 ) )' % (FP, RR_('V')))
    mlt = linarith(w, FP, [nlt2], '%s < %s' % (M_, RR_('V')), closure=clp)
    iv = s([LP(LF(L(ihv)))], 'id', '') if False else LP(LF(L(ihv)))
    cg, xm = cong(w, QF('V', 'i'), 'i', M_)
    rsp = s([cg], 'rspcv', '( %s e. NN0 -> ( A. i e. NN0 %s -> %s ) )' % (M_, QF('V', 'i'), xm))
    imm = s([mn, iv, rsp], 'sylc', '( %s -> %s )' % (FP, xm))
    bodyV, (LTV, MDV, RIV, CZV, LNV) = BODY('V', M_)
    bm = s([imm, mlt], 'mpd', '( %s -> %s )' % (FP, bodyV))
    b1_ = s([bm, w.inst('simp1')], 'syl', '( %s -> %s )' % (FP, LTV))
    b2_ = s([bm, w.inst('simp2')], 'syl', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (FP, MDV, RIV, CZV))
    b3_ = s([bm, w.inst('simp3')], 'syl', '( %s -> ( ( %s \\/ %s ) <-> %s ) )' % (FP, MDV, LNV, RIV))
    # the entry
    mz = s([s([mn, s([LP(LF(nv))], 'nn0zd', '( %s -> ( # ` V ) e. ZZ )' % FP), b1_], '3jca', '( %s -> ( %s e. NN0 /\\ ( # ` V ) e. ZZ /\\ %s ) )' % (FP, M_, LTV)),
            w.inst('elfzo0z')], 'sylibr', '( %s -> %s e. ( 0 ..^ ( # ` V ) ) )' % (FP, M_))
    fv1 = s([s([s([LP(LF(L(pn))), LP(LF(L(vs)))], 'jca', '( %s -> ( P e. NN0 /\\ V e. Word NN0 ) )' % FP), mz], 'jca',
               '( %s -> ( ( P e. NN0 /\\ V e. Word NN0 ) /\\ %s e. ( 0 ..^ ( # ` V ) ) ) )' % (FP, M_)), w.inst('algcsfvp1')], 'syl',
            '( %s -> ( %s ` ( %s + 1 ) ) = ( V ` %s ) )' % (FP, CSV, M_, M_))
    fvn = s([s([s([nm], 'eqcomd', '( %s -> n = ( %s + 1 ) )' % (FP, M_))], 'fveq2d', '( %s -> ( %s ` n ) = ( %s ` ( %s + 1 ) ) )' % (FP, CSV, CSV, M_)), fv1],
            'eqtrd', '( %s -> ( %s ` n ) = ( V ` %s ) )' % (FP, CSV, M_))
    emd = s([s([fvn], 'oveq2d', '( %s -> ( G mod ( %s ` n ) ) = ( G mod ( V ` %s ) ) )' % (FP, CSV, M_))], 'eqeq1d', '( %s -> ( %s <-> %s ) )' % (FP, MD, MDV))
    # n + 1 = X + 1 <-> m + 1 = X
    def shift(X, xc):
        e1 = s([s([s([s([nm], 'eqcomd', '( %s -> n = ( %s + 1 ) )' % (FP, M_))], 'oveq1d', '( %s -> ( n + 1 ) = ( ( %s + 1 ) + 1 ) )' % (FP, M_))], 'eqeq1d',
                  '( %s -> ( ( n + 1 ) = ( %s + 1 ) <-> ( ( %s + 1 ) + 1 ) = ( %s + 1 ) ) )' % (FP, X, M_, X)),
                s([s([s([mn], 'nn0cnd', '( %s -> %s e. CC )' % (FP, M_)), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % FP)], 'addcld',
                     '( %s -> ( %s + 1 ) e. CC )' % (FP, M_)), xc, s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % FP)], 'addcan2d',
                  '( %s -> ( ( ( %s + 1 ) + 1 ) = ( %s + 1 ) <-> ( %s + 1 ) = %s ) )' % (FP, M_, X, M_, X))], 'bitrd',
               '( %s -> ( ( n + 1 ) = ( %s + 1 ) <-> ( %s + 1 ) = %s ) )' % (FP, X, M_, X))
        return e1
    eri = s([s([LP(pf)], 'eqeq2d', '( %s -> ( %s <-> ( n + 1 ) = ( %s + 1 ) ) )' % (FP, RI, RR_('V'))),
             shift(RR_('V'), s([LP(LF(b1))], 'nn0cnd', '( %s -> %s e. CC )' % (FP, RR_('V'))))], 'bitrd', '( %s -> ( %s <-> %s ) )' % (FP, RI, RIV))
    eln = s([s([LP(LF(lc))], 'eqeq2d', '( %s -> ( %s <-> ( n + 1 ) = ( ( # ` V ) + 1 ) ) )' % (FP, LN)),
             shift('( # ` V )', s([LP(LF(nv))], 'nn0cnd', '( %s -> ( # ` V ) e. CC )' % FP))], 'bitrd', '( %s -> ( %s <-> %s ) )' % (FP, LN, LNV))
    ecz = s([LP(cfv)], 'eqeq1d', '( %s -> ( %s <-> %s ) )' % (FP, CZ, CZV))
    ltp = s([b1_, s([s([s([nm], 'eqcomd', '( %s -> n = ( %s + 1 ) )' % (FP, M_)), LP(LF(lc))], 'breq12d',
                       '( %s -> ( n < ( # ` %s ) <-> ( %s + 1 ) < ( ( # ` V ) + 1 ) ) )' % (FP, CSV, M_)),
                     s([s([mn], 'nn0red', '( %s -> %s e. RR )' % (FP, M_)), s([LP(LF(nv))], 'nn0red', '( %s -> ( # ` V ) e. RR )' % FP),
                        s([s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % FP)], 'ltadd1d', '( %s -> ( %s < ( # ` V ) <-> ( %s + 1 ) < ( ( # ` V ) + 1 ) ) )' % (FP, M_, M_))],
                    'bitr4d', '( %s -> ( n < ( # ` %s ) <-> %s ) )' % (FP, CSV, LTV))], 'mpbird', '( %s -> %s )' % (FP, LT))
    k2p = s([b2_, emd, s([eri, ecz], 'anbi12d', '( %s -> ( ( %s /\\ %s ) <-> ( %s /\\ %s ) ) )' % (FP, RI, CZ, RIV, CZV))], '3bitr4d',
            '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (FP, MD, RI, CZ))
    k3p = s([b3_, s([emd, eln], 'orbi12d', '( %s -> ( ( %s \\/ %s ) <-> ( %s \\/ %s ) ) )' % (FP, MD, LN, MDV, LNV)), eri], '3bitr4d',
            '( %s -> ( ( %s \\/ %s ) <-> %s ) )' % (FP, MD, LN, RI))
    bfp = s([ltp, k2p, k3p], '3jca', '( %s -> %s )' % (FP, body))
    en = s([s([LF(nn), w.inst('elnn0')], 'sylib', '( %s -> ( n e. NN \\/ n = 0 ) )' % BF)], 'id', '') if False else \
        s([LF(nn), w.inst('elnn0')], 'sylib', '( %s -> ( n e. NN \\/ n = 0 ) )' % BF)
    bff = s([bfp, bf0, en], 'mpjaodan', '( %s -> %s )' % (BF, body))
    bb = s([bt, bff], 'pm2.61dan', '( %s -> %s )' % (BN, body))
    q = s([s([bb], 'ex', '( ( %s /\\ n e. NN0 ) -> %s )' % (A2, QF(CSV, 'n')))], 'ralrimiva', '( %s -> A. n e. NN0 %s )' % (A2, QF(CSV, 'n')))
    cg2, xi = cong(w, QF(CSV, 'n'), 'n', 'i')
    cb = s([cg2], 'cbvralvw', '( A. n e. NN0 %s <-> A. i e. NN0 %s )' % (QF(CSV, 'n'), xi))
    w.qed([s([q, cb], 'sylib', '( %s -> A. i e. NN0 %s )' % (A2, xi))], 'ex', '( %s -> %s )' % (A, co))


def cf(w, ph, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            f = l.split('|-', 1)[1].strip()
            assert f.startswith('( %s -> ' % ph), (f[:150], ph[:150])
            return f[len('( %s -> ' % ph):-2]
    raise KeyError(st)


def _fch(w, st, phit):
    T = '( ( S e. Word NN0 /\\ G e. NN0 ) /\\ ( I e. NN0 /\\ I < %s ) )' % RR_('S')
    sw = w.s([], 'simpll', '( %s -> S e. Word NN0 )' % T)
    gn = w.s([], 'simplr', '( %s -> G e. NN0 )' % T)
    a = w.s([w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)), gn], 'mpd',
            '( %s -> A. i e. NN0 %s )' % (T, QF('S', 'i')))
    cg, xI = cong(w, QF('S', 'i'), 'i', 'I')
    r = w.s([cg], 'rspcv', '( I e. NN0 -> ( A. i e. NN0 %s -> %s ) )' % (QF('S', 'i'), xI))
    im = w.s([w.s([], 'simprl', '( %s -> I e. NN0 )' % T), a, r], 'sylc', '( %s -> %s )' % (T, xI))
    w.qed([w.s([], 'simprr', '( %s -> I < %s )' % (T, RR_('S'))), im], 'mpd', STMTS['tmcpch'])


if __name__ == '__main__':
    family(run, 'tmcp0', PHI0, _b0, _s0, finish=_f0,
           desc='The count of ` coprimeToF ` is 0 exactly for the empty list (Lean ` cpIter ` ).', only=only or ['-'])
    family(run, 'tmcpch', PHI_CH, _bch, _sch, finish=_fch,
           desc='The count of ` coprimeToF ` (Lean ` cpIter ` , ` lt_cpIter_iff ` , ` coprimeTo_fst ` ): below it the index is an entry; '
                'the entry divides ` k ` iff the loop stops after it with the answer false; it divides or is the last entry iff the loop '
                'stops after it.', only=only or ['-'])
