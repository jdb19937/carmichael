"""Sortie A4a, batch 4: the Boolean list recursions (notMemTD, nodupTD,
korseltTD, coprimeTo) of AlgScan.lean."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CSV = '( <" P "> ++ V )'
B2 = '( 2o X. NN0 )'

def ex0(w, a):   return w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % a)
def exc0(w, a):  return w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % a)
def ex1(w, a):   return w.s([w.s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % a)
def ex1o(w, a):  return w.s([w.s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % a)
def rn0eq(w, a): return w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % a)
def z2o(w, a):   return w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % a)

def notinrn0(w, a, e):
    return w.s([w.s([rn0eq(w, a)], 'eleq2d', '( %s -> ( %s e. ran (/) <-> %s e. (/) ) )' % (a, e, e)),
                w.s([w.s([], 'noel', '-. %s e. (/)' % e)], 'a1i', '( %s -> -. %s e. (/) )' % (a, e))], 'mtbird',
               '( %s -> -. %s e. ran (/) )' % (a, e))

# ======================================================================= notMemTD value
PHI = '( Q e. NN0 -> ( ( 1st ` ( Q NotMemTD s ) ) = 1o <-> -. Q e. ran s ) )'
def _b(w, goal):
    P = 'Q e. NN0'
    qn = w.s([], 'id', '( %s -> Q e. NN0 )' % P)
    v = w.s([qn, w.inst('notmemtd0')], 'syl', '( %s -> ( Q NotMemTD (/) ) = <. 1o , 0 >. )' % P)
    p = projeq(w, P, '( Q NotMemTD (/) )', v, '1o', '0', ex1o(w, P), exc0(w, P), 1)
    nr = notinrn0(w, P, 'Q')
    w.qed([p, nr], '2thd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ Q e. NN0 )' % A
    IFE = 'if ( Q = P , (/) , ( 1st ` ( Q NotMemTD V ) ) )'
    L = '( 1st ` ( Q NotMemTD %s ) )' % CSV
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qn = w.s([], 'simpr', '( %s -> Q e. NN0 )' % A2)
    cl = w.s([qn, vs, w.inst('notmemtdcl')], 'syl2anc', '( %s -> ( Q NotMemTD V ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( Q NotMemTD V )', cl, '2o', 'NN0')
    cs = w.s([w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('notmemtdcs')], 'syl2anc',
             '( %s -> ( Q NotMemTD %s ) = <. %s , ( ( 2nd ` ( Q NotMemTD V ) ) + 1 ) >. )' % (A2, CSV, IFE))
    xa = w.s([z2o(w, A2), a1], 'ifcld', '( %s -> %s e. 2o )' % (A2, IFE))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q NotMemTD V ) ) + 1 ) e. NN0 )' % A2)
    p1 = projeq(w, A2, '( Q NotMemTD %s )' % CSV, cs, IFE, '( ( 2nd ` ( Q NotMemTD V ) ) + 1 )', xa, xb, 1)
    st, sf = ifproj(w, A2, L, p1, 'Q = P', '(/)', '( 1st ` ( Q NotMemTD V ) )')
    mem = w.s([w.s([w.s([pn, vs], 'jca', '( %s -> ( P e. NN0 /\\ V e. Word NN0 ) )' % A2), qn], 'jca',
                   '( %s -> ( ( P e. NN0 /\\ V e. Word NN0 ) /\\ Q e. NN0 ) )' % A2), w.inst('algelcs')], 'syl',
              '( %s -> ( Q e. ran %s <-> ( Q = P \\/ Q e. ran V ) ) )' % (A2, CSV))
    T = '( %s /\\ Q = P )' % A2
    nl = w.s([w.s([st], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (T, L)), zne1o(w, T)], 'mtbird', '( %s -> -. %s = 1o )' % (T, L))
    inm = w.s([w.s([mem], 'adantr', '( %s -> ( Q e. ran %s <-> ( Q = P \\/ Q e. ran V ) ) )' % (T, CSV)),
               w.s([w.s([], 'simpr', '( %s -> Q = P )' % T)], 'orcd', '( %s -> ( Q = P \\/ Q e. ran V ) )' % T)], 'mpbird',
              '( %s -> Q e. ran %s )' % (T, CSV))
    ct = w.s([nl, w.s([inm], 'notnotd', '( %s -> -. -. Q e. ran %s )' % (T, CSV))], '2falsed',
             '( %s -> ( %s = 1o <-> -. Q e. ran %s ) )' % (T, L, CSV))
    F = '( %s /\\ -. Q = P )' % A2
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), qn], 'mpd',
              '( %s -> ( ( 1st ` ( Q NotMemTD V ) ) = 1o <-> -. Q e. ran V ) )' % A2)
    lf = w.s([w.s([sf], 'eqeq1d', '( %s -> ( %s = 1o <-> ( 1st ` ( Q NotMemTD V ) ) = 1o ) )' % (F, L)),
              w.s([ihs], 'adantr', '( %s -> ( ( 1st ` ( Q NotMemTD V ) ) = 1o <-> -. Q e. ran V ) )' % F)], 'bitrd',
             '( %s -> ( %s = 1o <-> -. Q e. ran V ) )' % (F, L))
    memf = w.s([mem], 'adantr', '( %s -> ( Q e. ran %s <-> ( Q = P \\/ Q e. ran V ) ) )' % (F, CSV))
    orf = w.s([w.s([], 'simpr', '( %s -> -. Q = P )' % F), w.inst('biorf')], 'syl', '( %s -> ( Q e. ran V <-> ( Q = P \\/ Q e. ran V ) ) )' % F)
    rf = w.s([w.s([memf, orf], 'bitr4d', '( %s -> ( Q e. ran %s <-> Q e. ran V ) )' % (F, CSV))], 'notbid',
             '( %s -> ( -. Q e. ran %s <-> -. Q e. ran V ) )' % (F, CSV))
    cf = w.s([lf, rf], 'bitr4d', '( %s -> ( %s = 1o <-> -. Q e. ran %s ) )' % (F, L, CSV))
    w.qed([w.s([ct, cf], 'pm2.61dan', '( %s -> ( %s = 1o <-> -. Q e. ran %s ) )' % (A2, L, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( Q e. NN0 /\\ S e. Word NN0 )'
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> Q e. NN0 )' % T)], 'mpd',
          '( %s -> ( ( 1st ` ( Q NotMemTD S ) ) = 1o <-> -. Q e. ran S ) )' % T)
family(run, 'notmemtdfst', PHI, _b, _s, finish=_f, desc='notMemTD reports true exactly when the element is absent (Lean: notMemTD_fst).', only=only)

# ======================================================================= notMemTD cost
PHI = '( Q e. NN0 -> ( 2nd ` ( Q NotMemTD s ) ) = ( # ` s ) )'
def _b(w, goal):
    P = 'Q e. NN0'
    qn = w.s([], 'id', '( %s -> Q e. NN0 )' % P)
    v = w.s([qn, w.inst('notmemtd0')], 'syl', '( %s -> ( Q NotMemTD (/) ) = <. 1o , 0 >. )' % P)
    p = projeq(w, P, '( Q NotMemTD (/) )', v, '1o', '0', ex1o(w, P), exc0(w, P), 2)
    h = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % P)
    w.qed([p, h], 'eqtr4d', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ Q e. NN0 )' % A
    IFE = 'if ( Q = P , (/) , ( 1st ` ( Q NotMemTD V ) ) )'
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qn = w.s([], 'simpr', '( %s -> Q e. NN0 )' % A2)
    cl = w.s([qn, vs, w.inst('notmemtdcl')], 'syl2anc', '( %s -> ( Q NotMemTD V ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( Q NotMemTD V )', cl, '2o', 'NN0')
    cs = w.s([w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('notmemtdcs')], 'syl2anc',
             '( %s -> ( Q NotMemTD %s ) = <. %s , ( ( 2nd ` ( Q NotMemTD V ) ) + 1 ) >. )' % (A2, CSV, IFE))
    xa = w.s([z2o(w, A2), a1], 'ifcld', '( %s -> %s e. 2o )' % (A2, IFE))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q NotMemTD V ) ) + 1 ) e. NN0 )' % A2)
    p2 = projeq(w, A2, '( Q NotMemTD %s )' % CSV, cs, IFE, '( ( 2nd ` ( Q NotMemTD V ) ) + 1 )', xa, xb, 2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), qn], 'mpd', '( %s -> ( 2nd ` ( Q NotMemTD V ) ) = ( # ` V ) )' % A2)
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    w.qed([w.s([w.s([p2, w.s([ihs], 'oveq1d', '( %s -> ( ( 2nd ` ( Q NotMemTD V ) ) + 1 ) = ( ( # ` V ) + 1 ) )' % A2)], 'eqtrd',
                    '( %s -> ( 2nd ` ( Q NotMemTD %s ) ) = ( ( # ` V ) + 1 ) )' % (A2, CSV)), lc], 'eqtr4d',
               '( %s -> ( 2nd ` ( Q NotMemTD %s ) ) = ( # ` %s ) )' % (A2, CSV, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( Q e. NN0 /\\ S e. Word NN0 )'
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> Q e. NN0 )' % T)], 'mpd', '( %s -> ( 2nd ` ( Q NotMemTD S ) ) = ( # ` S ) )' % T)
family(run, 'notmemtdcost', PHI, _b, _s, finish=_f, desc='The cost of notMemTD is the length of the list (Lean: notMemTD_snd).', only=only)

# ======================================================================= korseltTD value
KOR = lambda x: '( ( ( M - 1 ) mod ( %s - 1 ) ) = 0 )' % x
CND = '( ( M - 1 ) mod ( P - 1 ) ) = 0'
RAL = lambda x: 'A. p e. ran %s ( ( M - 1 ) mod ( p - 1 ) ) = 0' % x
PHI = '( M e. NN0 -> ( ( 1st ` ( M KorseltTD s ) ) = 1o <-> %s ) )' % RAL('s')
def _b(w, goal):
    P = 'M e. NN0'
    mn = w.s([], 'id', '( %s -> M e. NN0 )' % P)
    v = w.s([mn, w.inst('korselttd0')], 'syl', '( %s -> ( M KorseltTD (/) ) = <. 1o , 0 >. )' % P)
    p = projeq(w, P, '( M KorseltTD (/) )', v, '1o', '0', ex1o(w, P), exc0(w, P), 1)
    r = w.s([w.s([rn0eq(w, P)], 'raleqdv', '( %s -> ( %s <-> A. p e. (/) ( ( M - 1 ) mod ( p - 1 ) ) = 0 ) )' % (P, RAL('(/)'))),
             w.s([w.s([], 'ral0', 'A. p e. (/) ( ( M - 1 ) mod ( p - 1 ) ) = 0')], 'a1i',
                 '( %s -> A. p e. (/) ( ( M - 1 ) mod ( p - 1 ) ) = 0 )' % P)], 'mpbird', '( %s -> %s )' % (P, RAL('(/)')))
    w.qed([p, r], '2thd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ M e. NN0 )' % A
    IFE = 'if ( %s , ( 1st ` ( M KorseltTD V ) ) , (/) )' % CND
    L = '( 1st ` ( M KorseltTD %s ) )' % CSV
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    mn = w.s([], 'simpr', '( %s -> M e. NN0 )' % A2)
    cl = w.s([mn, vs, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( M KorseltTD V ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( M KorseltTD V )', cl, '2o', 'NN0')
    cs = w.s([w.s([mn, pn], 'jca', '( %s -> ( M e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('korselttdcs')], 'syl2anc',
             '( %s -> ( M KorseltTD %s ) = <. %s , ( ( 2nd ` ( M KorseltTD V ) ) + 1 ) >. )' % (A2, CSV, IFE))
    xa = w.s([a1, z2o(w, A2)], 'ifcld', '( %s -> %s e. 2o )' % (A2, IFE))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( M KorseltTD V ) ) + 1 ) e. NN0 )' % A2)
    p1 = projeq(w, A2, '( M KorseltTD %s )' % CSV, cs, IFE, '( ( 2nd ` ( M KorseltTD V ) ) + 1 )', xa, xb, 1)
    st, sf = ifproj(w, A2, L, p1, CND, '( 1st ` ( M KorseltTD V ) )', '(/)')
    # the quantifier over a cons
    rc = w.s([pn, vs, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A2, CSV))
    sbs = w.s([w.s([w.s([w.s([], 'id', '( p = P -> p = P )')], 'oveq1d', '( p = P -> ( p - 1 ) = ( P - 1 ) )')], 'oveq2d',
                   '( p = P -> ( ( M - 1 ) mod ( p - 1 ) ) = ( ( M - 1 ) mod ( P - 1 ) ) )')], 'eqeq1d',
              '( p = P -> ( ( ( M - 1 ) mod ( p - 1 ) ) = 0 <-> %s ) )' % CND)
    rsn0 = w.s([sbs], 'ralsng', '( P e. _V -> ( A. p e. { P } ( ( M - 1 ) mod ( p - 1 ) ) = 0 <-> %s ) )' % CND)
    rsn = w.s([w.s([pn], 'elexd', '( %s -> P e. _V )' % A2), rsn0], 'syl',
              '( %s -> ( A. p e. { P } ( ( M - 1 ) mod ( p - 1 ) ) = 0 <-> %s ) )' % (A2, CND))
    run_ = w.s([w.s([rc], 'raleqdv', '( %s -> ( %s <-> A. p e. ( { P } u. ran V ) ( ( M - 1 ) mod ( p - 1 ) ) = 0 ) )' % (A2, RAL(CSV))),
                w.s([w.s([], 'ralunb', '( A. p e. ( { P } u. ran V ) ( ( M - 1 ) mod ( p - 1 ) ) = 0 <-> ( A. p e. { P } ( ( M - 1 ) mod ( p - 1 ) ) = 0 /\\ %s ) )' % RAL('V'))],
                    'a1i', '( %s -> ( A. p e. ( { P } u. ran V ) ( ( M - 1 ) mod ( p - 1 ) ) = 0 <-> ( A. p e. { P } ( ( M - 1 ) mod ( p - 1 ) ) = 0 /\\ %s ) ) )' % (A2, RAL('V')))], 'bitrd',
               '( %s -> ( %s <-> ( A. p e. { P } ( ( M - 1 ) mod ( p - 1 ) ) = 0 /\\ %s ) ) )' % (A2, RAL(CSV), RAL('V')))
    rsp = w.s([run_, w.s([rsn], 'anbi1d', '( %s -> ( ( A. p e. { P } ( ( M - 1 ) mod ( p - 1 ) ) = 0 /\\ %s ) <-> ( %s /\\ %s ) ) )' % (A2, RAL('V'), CND, RAL('V')))], 'bitrd',
              '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (A2, RAL(CSV), CND, RAL('V')))
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), mn], 'mpd',
              '( %s -> ( ( 1st ` ( M KorseltTD V ) ) = 1o <-> %s ) )' % (A2, RAL('V')))
    # case CND
    T = '( %s /\\ %s )' % (A2, CND)
    lt = w.s([w.s([st], 'eqeq1d', '( %s -> ( %s = 1o <-> ( 1st ` ( M KorseltTD V ) ) = 1o ) )' % (T, L)),
              w.s([ihs], 'adantr', '( %s -> ( ( 1st ` ( M KorseltTD V ) ) = 1o <-> %s ) )' % (T, RAL('V')))], 'bitrd',
             '( %s -> ( %s = 1o <-> %s ) )' % (T, L, RAL('V')))
    rt = w.s([w.s([rsp], 'adantr', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (T, RAL(CSV), CND, RAL('V'))),
              w.s([w.s([], 'simpr', '( %s -> %s )' % (T, CND))], 'biantrurd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (T, RAL('V'), CND, RAL('V')))], 'bitr4d',
             '( %s -> ( %s <-> %s ) )' % (T, RAL(CSV), RAL('V')))
    ct = w.s([lt, rt], 'bitr4d', '( %s -> ( %s = 1o <-> %s ) )' % (T, L, RAL(CSV)))
    # case -. CND
    F = '( %s /\\ -. %s )' % (A2, CND)
    nl = w.s([w.s([sf], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (F, L)), zne1o(w, F)], 'mtbird', '( %s -> -. %s = 1o )' % (F, L))
    nr = w.s([w.s([rsp], 'adantr', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (F, RAL(CSV), CND, RAL('V'))),
              w.s([w.s([], 'simpr', '( %s -> -. %s )' % (F, CND))], 'intnanrd', '( %s -> -. ( %s /\\ %s ) )' % (F, CND, RAL('V')))], 'mtbird',
             '( %s -> -. %s )' % (F, RAL(CSV)))
    cf = w.s([nl, nr], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (F, L, RAL(CSV)))
    w.qed([w.s([ct, cf], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (A2, L, RAL(CSV)))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( M e. NN0 /\\ S e. Word NN0 )'
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> M e. NN0 )' % T)], 'mpd',
          '( %s -> ( ( 1st ` ( M KorseltTD S ) ) = 1o <-> %s ) )' % (T, RAL('S')))
family(run, 'korselttdfst', PHI, _b, _s, finish=_f, desc="korseltTD reports true exactly when every element passes Korselt's congruence (Lean: korseltTD_fst).", only=only)

# ======================================================================= korseltTD cost
PHI = '( M e. NN0 -> ( 2nd ` ( M KorseltTD s ) ) = ( # ` s ) )'
def _b(w, goal):
    P = 'M e. NN0'
    mn = w.s([], 'id', '( %s -> M e. NN0 )' % P)
    v = w.s([mn, w.inst('korselttd0')], 'syl', '( %s -> ( M KorseltTD (/) ) = <. 1o , 0 >. )' % P)
    p = projeq(w, P, '( M KorseltTD (/) )', v, '1o', '0', ex1o(w, P), exc0(w, P), 2)
    h = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % P)
    w.qed([p, h], 'eqtr4d', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ M e. NN0 )' % A
    IFE = 'if ( %s , ( 1st ` ( M KorseltTD V ) ) , (/) )' % CND
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    mn = w.s([], 'simpr', '( %s -> M e. NN0 )' % A2)
    cl = w.s([mn, vs, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( M KorseltTD V ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( M KorseltTD V )', cl, '2o', 'NN0')
    cs = w.s([w.s([mn, pn], 'jca', '( %s -> ( M e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('korselttdcs')], 'syl2anc',
             '( %s -> ( M KorseltTD %s ) = <. %s , ( ( 2nd ` ( M KorseltTD V ) ) + 1 ) >. )' % (A2, CSV, IFE))
    xa = w.s([a1, z2o(w, A2)], 'ifcld', '( %s -> %s e. 2o )' % (A2, IFE))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( M KorseltTD V ) ) + 1 ) e. NN0 )' % A2)
    p2 = projeq(w, A2, '( M KorseltTD %s )' % CSV, cs, IFE, '( ( 2nd ` ( M KorseltTD V ) ) + 1 )', xa, xb, 2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), mn], 'mpd', '( %s -> ( 2nd ` ( M KorseltTD V ) ) = ( # ` V ) )' % A2)
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    w.qed([w.s([w.s([p2, w.s([ihs], 'oveq1d', '( %s -> ( ( 2nd ` ( M KorseltTD V ) ) + 1 ) = ( ( # ` V ) + 1 ) )' % A2)], 'eqtrd',
                    '( %s -> ( 2nd ` ( M KorseltTD %s ) ) = ( ( # ` V ) + 1 ) )' % (A2, CSV)), lc], 'eqtr4d',
               '( %s -> ( 2nd ` ( M KorseltTD %s ) ) = ( # ` %s ) )' % (A2, CSV, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( M e. NN0 /\\ S e. Word NN0 )'
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> M e. NN0 )' % T)], 'mpd', '( %s -> ( 2nd ` ( M KorseltTD S ) ) = ( # ` S ) )' % T)
family(run, 'korselttdcost', PHI, _b, _s, finish=_f, desc='The cost of korseltTD is the length of the list (Lean: korseltTD_snd).', only=only)

# ======================================================================= nodupTD value
PHI = "( ( 1st ` ( NodupTD ` s ) ) = 1o <-> Fun `' s )"
def _b(w, goal):
    v = w.s([], 'noduptd0', '( NodupTD ` (/) ) = <. 1o , 0 >.')
    e = w.s([v], 'fveq2i', '( 1st ` ( NodupTD ` (/) ) ) = ( 1st ` <. 1o , 0 >. )')
    o = w.s([w.s([], '1oex', '1o e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. 1o , 0 >. ) = 1o')
    w.qed([w.s([e, o], 'eqtri', '( 1st ` ( NodupTD ` (/) ) ) = 1o'), w.s([], 'algndp0', "Fun `' (/)")], '2th', goal)
def _s(w, A, ih, co):
    NM = '( 1st ` ( P NotMemTD V ) )'
    IFE = 'if ( %s = 1o , ( 1st ` ( NodupTD ` V ) ) , (/) )' % NM
    L = '( 1st ` ( NodupTD ` %s ) )' % CSV
    vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    cl = w.s([vs, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` V ) e. %s )' % (A, B2))
    a1, b1 = paircl(w, A, '( NodupTD ` V )', cl, '2o', 'NN0')
    ncl = w.s([pn, vs, w.inst('notmemtdcl')], 'syl2anc', '( %s -> ( P NotMemTD V ) e. %s )' % (A, B2))
    na, nb = paircl(w, A, '( P NotMemTD V )', ncl, '2o', 'NN0')
    cs = w.s([pn, vs, w.inst('noduptdcs')], 'syl2anc',
             '( %s -> ( NodupTD ` %s ) = <. %s , ( ( ( 2nd ` ( P NotMemTD V ) ) + ( 2nd ` ( NodupTD ` V ) ) ) + 1 ) >. )' % (A, CSV, IFE))
    xa = w.s([a1, z2o(w, A)], 'ifcld', '( %s -> %s e. 2o )' % (A, IFE))
    xb = w.s([w.s([nb, b1], 'nn0addcld', '( %s -> ( ( 2nd ` ( P NotMemTD V ) ) + ( 2nd ` ( NodupTD ` V ) ) ) e. NN0 )' % A),
              w.inst('peano2nn0')], 'syl', '( %s -> ( ( ( 2nd ` ( P NotMemTD V ) ) + ( 2nd ` ( NodupTD ` V ) ) ) + 1 ) e. NN0 )' % A)
    p1 = projeq(w, A, '( NodupTD ` %s )' % CSV, cs, IFE, '( ( ( 2nd ` ( P NotMemTD V ) ) + ( 2nd ` ( NodupTD ` V ) ) ) + 1 )', xa, xb, 1)
    st, sf = ifproj(w, A, L, p1, '%s = 1o' % NM, '( 1st ` ( NodupTD ` V ) )', '(/)')
    nmb = w.s([pn, vs, w.inst('notmemtdfst')], 'syl2anc', '( %s -> ( %s = 1o <-> -. P e. ran V ) )' % (A, NM))
    ndc = w.s([pn, vs, w.inst('algndpcs')], 'syl2anc', "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (A, CSV))
    T = '( %s /\\ %s = 1o )' % (A, NM)
    npv = w.s([w.s([nmb], 'adantr', '( %s -> ( %s = 1o <-> -. P e. ran V ) )' % (T, NM)), w.s([], 'simpr', '( %s -> %s = 1o )' % (T, NM))], 'mpbid',
              '( %s -> -. P e. ran V )' % T)
    lt = w.s([w.s([st], 'eqeq1d', '( %s -> ( %s = 1o <-> ( 1st ` ( NodupTD ` V ) ) = 1o ) )' % (T, L)),
              w.s([ihs], 'adantr', '( %s -> %s )' % (T, ih))], 'bitrd', "( %s -> ( %s = 1o <-> Fun `' V ) )" % (T, L))
    rt = w.s([w.s([ndc], 'adantr', "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (T, CSV)),
              w.s([npv], 'biantrurd', "( %s -> ( Fun `' V <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % T)], 'bitr4d',
             "( %s -> ( Fun `' %s <-> Fun `' V ) )" % (T, CSV))
    ct = w.s([lt, rt], 'bitr4d', "( %s -> ( %s = 1o <-> Fun `' %s ) )" % (T, L, CSV))
    F = '( %s /\\ -. %s = 1o )' % (A, NM)
    inv = w.s([w.s([nmb], 'adantr', '( %s -> ( %s = 1o <-> -. P e. ran V ) )' % (F, NM)), w.s([], 'simpr', '( %s -> -. %s = 1o )' % (F, NM))], 'mtbid',
              '( %s -> -. -. P e. ran V )' % F)
    nl = w.s([w.s([sf], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (F, L)), zne1o(w, F)], 'mtbird', '( %s -> -. %s = 1o )' % (F, L))
    nr = w.s([w.s([ndc], 'adantr', "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (F, CSV)),
              w.s([inv], 'intnanrd', "( %s -> -. ( -. P e. ran V /\\ Fun `' V ) )" % F)], 'mtbird', "( %s -> -. Fun `' %s )" % (F, CSV))
    cf = w.s([nl, nr], '2falsed', "( %s -> ( %s = 1o <-> Fun `' %s ) )" % (F, L, CSV))
    w.qed([ct, cf], 'pm2.61dan', '( %s -> %s )' % (A, co))
family(run, 'noduptdfst', PHI, _b, _s, desc='nodupTD reports true exactly when the list has no repeats (Lean: nodupTD_fst).', only=only)

import lin

# ======================================================================= nodupTD cost
PHI = '( 2nd ` ( NodupTD ` s ) ) <_ ( ( # ` s ) x. ( ( # ` s ) + 1 ) )'
def _b(w, goal):
    v = w.s([], 'noduptd0', '( NodupTD ` (/) ) = <. 1o , 0 >.')
    e = w.s([v], 'fveq2i', '( 2nd ` ( NodupTD ` (/) ) ) = ( 2nd ` <. 1o , 0 >. )')
    o = w.s([w.s([], '1oex', '1o e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. 1o , 0 >. ) = 0')
    l = w.s([e, o], 'eqtri', '( 2nd ` ( NodupTD ` (/) ) ) = 0')
    hn = w.s([w.s([], 'wrd0', '(/) e. Word NN0'), w.inst('lencl')], 'ax-mp', '( # ` (/) ) e. NN0')
    hn1 = w.s([hn, w.inst('peano2nn0')], 'ax-mp', '( ( # ` (/) ) + 1 ) e. NN0')
    pr = w.s([hn, hn1], 'nn0mulcli', '( ( # ` (/) ) x. ( ( # ` (/) ) + 1 ) ) e. NN0')
    ge = w.s([pr, w.inst('nn0ge0')], 'ax-mp', '0 <_ ( ( # ` (/) ) x. ( ( # ` (/) ) + 1 ) )')
    w.qed([l, ge], 'eqbrtri', goal)
def _s(w, A, ih, co):
    NM = '( 2nd ` ( P NotMemTD V ) )'
    ND = '( 2nd ` ( NodupTD ` V ) )'
    IFE = 'if ( ( 1st ` ( P NotMemTD V ) ) = 1o , ( 1st ` ( NodupTD ` V ) ) , (/) )'
    SUM = '( ( %s + %s ) + 1 )' % (NM, ND)
    vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    cl = w.s([vs, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` V ) e. %s )' % (A, B2))
    a1, b1 = paircl(w, A, '( NodupTD ` V )', cl, '2o', 'NN0')
    ncl = w.s([pn, vs, w.inst('notmemtdcl')], 'syl2anc', '( %s -> ( P NotMemTD V ) e. %s )' % (A, B2))
    na, nb = paircl(w, A, '( P NotMemTD V )', ncl, '2o', 'NN0')
    cs = w.s([pn, vs, w.inst('noduptdcs')], 'syl2anc', '( %s -> ( NodupTD ` %s ) = <. %s , %s >. )' % (A, CSV, IFE, SUM))
    xa = w.s([a1, z2o(w, A)], 'ifcld', '( %s -> %s e. 2o )' % (A, IFE))
    xb = w.s([w.s([nb, b1], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (A, NM, ND)), w.inst('peano2nn0')], 'syl',
             '( %s -> %s e. NN0 )' % (A, SUM))
    p2 = projeq(w, A, '( NodupTD ` %s )' % CSV, cs, IFE, SUM, xa, xb, 2)
    nmc = w.s([pn, vs, w.inst('notmemtdcost')], 'syl2anc', '( %s -> %s = ( # ` V ) )' % (A, NM))
    SUM2 = '( ( ( # ` V ) + %s ) + 1 )' % ND
    p2b = w.s([p2, w.s([w.s([nmc], 'oveq1d', '( %s -> ( %s + %s ) = ( ( # ` V ) + %s ) )' % (A, NM, ND, ND))], 'oveq1d',
                       '( %s -> %s = %s )' % (A, SUM, SUM2))], 'eqtrd', '( %s -> ( 2nd ` ( NodupTD ` %s ) ) = %s )' % (A, CSV, SUM2))
    lenn = w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A)
    lenr = w.s([lenn], 'nn0red', '( %s -> ( # ` V ) e. RR )' % A)
    ndr = w.s([b1], 'nn0red', '( %s -> %s e. RR )' % (A, ND))
    lge = w.s([lenn], 'nn0ge0d', '( %s -> 0 <_ ( # ` V ) )' % A)
    RHS = '( ( ( # ` V ) + 1 ) x. ( ( ( # ` V ) + 1 ) + 1 ) )'
    li = lin.nlinarith(w, A, [ihs, lge], '%s <_ %s' % (SUM2, RHS), leaves={'( # ` V )': lenr, ND: ndr})
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A, CSV))
    rr, _ = rweq(w, A, '( ( # ` %s ) x. ( ( # ` %s ) + 1 ) )' % (CSV, CSV), '( # ` %s )' % CSV, '( ( # ` V ) + 1 )', lc)
    w.qed([w.s([p2b, li], 'eqbrtrd', '( %s -> ( 2nd ` ( NodupTD ` %s ) ) <_ %s )' % (A, CSV, RHS)), rr], 'breqtrrd', '( %s -> %s )' % (A, co))
family(run, 'noduptdcost', PHI, _b, _s, desc='The cost of nodupTD is at most the length times the length plus one (Lean: nodupTD_snd).', only=only)

# ======================================================================= coprimeTo value
RALN = lambda x: 'A. q e. ran %s q e. NN' % x
RALD = lambda x: 'A. q e. ran %s -. q || K' % x
CMOD = '( K mod P ) = 0'
PHI = '( ( K e. NN0 /\\ %s ) -> ( ( 1st ` ( s CoprimeTo K ) ) = 1o <-> %s ) )' % (RALN('s'), RALD('s'))
def _b(w, goal):
    P = '( K e. NN0 /\\ %s )' % RALN('(/)')
    kn = w.s([], 'simpl', '( %s -> K e. NN0 )' % P)
    v = w.s([kn, w.inst('coprimeto0')], 'syl', '( %s -> ( (/) CoprimeTo K ) = <. 1o , 0 >. )' % P)
    p = projeq(w, P, '( (/) CoprimeTo K )', v, '1o', '0', ex1o(w, P), exc0(w, P), 1)
    r = w.s([w.s([rn0eq(w, P)], 'raleqdv', '( %s -> ( %s <-> A. q e. (/) -. q || K ) )' % (P, RALD('(/)'))),
             w.s([w.s([], 'ral0', 'A. q e. (/) -. q || K')], 'a1i', '( %s -> A. q e. (/) -. q || K )' % P)], 'mpbird',
            '( %s -> %s )' % (P, RALD('(/)')))
    w.qed([p, r], '2thd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ ( K e. NN0 /\\ %s ) )' % (A, RALN(CSV))
    L = '( 1st ` ( %s CoprimeTo K ) )' % CSV
    CV = '( 1st ` ( V CoprimeTo K ) )'
    SUM = '( ( 2nd ` ( V CoprimeTo K ) ) + 1 )'
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    kn = w.s([], 'simprl', '( %s -> K e. NN0 )' % A2)
    aln = w.s([], 'simprr', '( %s -> %s )' % (A2, RALN(CSV)))
    rc = w.s([pn, vs, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A2, CSV))
    aln2 = w.s([w.s([rc], 'raleqdv', '( %s -> ( %s <-> A. q e. ( { P } u. ran V ) q e. NN ) )' % (A2, RALN(CSV))), aln], 'mpbid',
               '( %s -> A. q e. ( { P } u. ran V ) q e. NN )' % A2)
    spl = w.s([aln2, w.s([w.s([], 'ralunb', '( A. q e. ( { P } u. ran V ) q e. NN <-> ( A. q e. { P } q e. NN /\\ %s ) )' % RALN('V'))], 'a1i',
                         '( %s -> ( A. q e. ( { P } u. ran V ) q e. NN <-> ( A. q e. { P } q e. NN /\\ %s ) ) )' % (A2, RALN('V')))], 'mpbid',
              '( %s -> ( A. q e. { P } q e. NN /\\ %s ) )' % (A2, RALN('V')))
    rsn0 = w.s([w.s([], 'id', '( q = P -> q = P )')], 'eleq1d', '( q = P -> ( q e. NN <-> P e. NN ) )')
    rsn1 = w.s([rsn0], 'ralsng', '( P e. _V -> ( A. q e. { P } q e. NN <-> P e. NN ) )')
    pex = w.s([pn], 'elexd', '( %s -> P e. _V )' % A2)
    rsn = w.s([pex, rsn1], 'syl', '( %s -> ( A. q e. { P } q e. NN <-> P e. NN ) )' % A2)
    pnn = w.s([rsn, w.s([spl], 'simpld', '( %s -> A. q e. { P } q e. NN )' % A2)], 'mpbid', '( %s -> P e. NN )' % A2)
    allv = w.s([spl], 'simprd', '( %s -> %s )' % (A2, RALN('V')))
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), w.s([kn, allv], 'jca', '( %s -> ( K e. NN0 /\\ %s ) )' % (A2, RALN('V')))], 'mpd',
              '( %s -> ( %s = 1o <-> %s ) )' % (A2, CV, RALD('V')))
    # the divisibility quantifier over a cons
    dsn0 = w.s([w.s([w.s([], 'id', '( q = P -> q = P )')], 'breq1d', '( q = P -> ( q || K <-> P || K ) )')], 'notbid',
               '( q = P -> ( -. q || K <-> -. P || K ) )')
    dsn1 = w.s([dsn0], 'ralsng', '( P e. _V -> ( A. q e. { P } -. q || K <-> -. P || K ) )')
    dsn = w.s([pex, dsn1], 'syl', '( %s -> ( A. q e. { P } -. q || K <-> -. P || K ) )' % A2)
    rsp = w.s([w.s([w.s([rc], 'raleqdv', '( %s -> ( %s <-> A. q e. ( { P } u. ran V ) -. q || K ) )' % (A2, RALD(CSV))),
                    w.s([w.s([], 'ralunb', '( A. q e. ( { P } u. ran V ) -. q || K <-> ( A. q e. { P } -. q || K /\\ %s ) )' % RALD('V'))], 'a1i',
                        '( %s -> ( A. q e. ( { P } u. ran V ) -. q || K <-> ( A. q e. { P } -. q || K /\\ %s ) ) )' % (A2, RALD('V')))], 'bitrd',
                   '( %s -> ( %s <-> ( A. q e. { P } -. q || K /\\ %s ) ) )' % (A2, RALD(CSV), RALD('V'))),
               w.s([dsn], 'anbi1d', '( %s -> ( ( A. q e. { P } -. q || K /\\ %s ) <-> ( -. P || K /\\ %s ) ) )' % (A2, RALD('V'), RALD('V')))], 'bitrd',
              '( %s -> ( %s <-> ( -. P || K /\\ %s ) ) )' % (A2, RALD(CSV), RALD('V')))
    dvb = w.s([pnn, w.s([kn], 'nn0zd', '( %s -> K e. ZZ )' % A2), w.inst('dvdsval3')], 'syl2anc',
              '( %s -> ( P || K <-> %s ) )' % (A2, CMOD))
    # the value
    ccl = w.s([vs, kn, w.inst('coprimetocl')], 'syl2anc', '( %s -> ( V CoprimeTo K ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( V CoprimeTo K )', ccl, '2o', 'NN0')
    cs = w.s([w.s([kn, pn], 'jca', '( %s -> ( K e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('coprimetocs')], 'syl2anc',
             '( %s -> ( %s CoprimeTo K ) = if ( %s , <. (/) , 1 >. , <. %s , %s >. ) )' % (A2, CSV, CMOD, CV, SUM))
    vt, vf = ifproj(w, A2, '( %s CoprimeTo K )' % CSV, cs, CMOD, '<. (/) , 1 >.', '<. %s , %s >.' % (CV, SUM))
    T = '( %s /\\ %s )' % (A2, CMOD)
    F = '( %s /\\ -. %s )' % (A2, CMOD)
    pt = projeq(w, T, '( %s CoprimeTo K )' % CSV, vt, '(/)', '1', ex0(w, T), ex1(w, T), 1)
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A2, SUM))
    pf = projeq(w, F, '( %s CoprimeTo K )' % CSV, vf, CV, SUM,
                w.s([a1], 'adantr', '( %s -> %s e. 2o )' % (F, CV)), w.s([xb], 'adantr', '( %s -> %s e. NN0 )' % (F, SUM)), 1)
    # case ( K mod P ) = 0
    nl = w.s([w.s([pt], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (T, L)), zne1o(w, T)], 'mtbird', '( %s -> -. %s = 1o )' % (T, L))
    pdk = w.s([w.s([dvb], 'adantr', '( %s -> ( P || K <-> %s ) )' % (T, CMOD)), w.s([], 'simpr', '( %s -> %s )' % (T, CMOD))], 'mpbird',
              '( %s -> P || K )' % T)
    nr = w.s([w.s([rsp], 'adantr', '( %s -> ( %s <-> ( -. P || K /\\ %s ) ) )' % (T, RALD(CSV), RALD('V'))),
              w.s([w.s([pdk], 'notnotd', '( %s -> -. -. P || K )' % T)], 'intnanrd', '( %s -> -. ( -. P || K /\\ %s ) )' % (T, RALD('V')))], 'mtbird',
             '( %s -> -. %s )' % (T, RALD(CSV)))
    ct = w.s([nl, nr], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (T, L, RALD(CSV)))
    # case else
    lf = w.s([w.s([pf], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (F, L, CV)),
              w.s([ihs], 'adantr', '( %s -> ( %s = 1o <-> %s ) )' % (F, CV, RALD('V')))], 'bitrd',
             '( %s -> ( %s = 1o <-> %s ) )' % (F, L, RALD('V')))
    npdk = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (F, CMOD)), w.s([dvb], 'adantr', '( %s -> ( P || K <-> %s ) )' % (F, CMOD))], 'mtbird',
               '( %s -> -. P || K )' % F)
    rf = w.s([w.s([rsp], 'adantr', '( %s -> ( %s <-> ( -. P || K /\\ %s ) ) )' % (F, RALD(CSV), RALD('V'))),
              w.s([npdk], 'biantrurd', '( %s -> ( %s <-> ( -. P || K /\\ %s ) ) )' % (F, RALD('V'), RALD('V')))], 'bitr4d',
             '( %s -> ( %s <-> %s ) )' % (F, RALD(CSV), RALD('V')))
    cf = w.s([lf, rf], 'bitr4d', '( %s -> ( %s = 1o <-> %s ) )' % (F, L, RALD(CSV)))
    w.qed([w.s([ct, cf], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (A2, L, RALD(CSV)))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( ( S e. Word NN0 /\\ K e. NN0 ) /\\ %s )' % RALN('S')
    w.qed([w.s([w.s([], 'simpll', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([w.s([], 'simplr', '( %s -> K e. NN0 )' % T), w.s([], 'simpr', '( %s -> %s )' % (T, RALN('S')))], 'jca',
               '( %s -> ( K e. NN0 /\\ %s ) )' % (T, RALN('S')))], 'mpd',
          '( %s -> ( ( 1st ` ( S CoprimeTo K ) ) = 1o <-> %s ) )' % (T, RALD('S')))
family(run, 'coprimetofst', PHI, _b, _s, finish=_f, desc='coprimeTo reports true exactly when no element divides K (Lean: coprimeTo_fst).', only=only)

# ======================================================================= coprimeTo cost
PHI = '( K e. NN0 -> ( 2nd ` ( s CoprimeTo K ) ) <_ ( # ` s ) )'
def _b(w, goal):
    P = 'K e. NN0'
    kn = w.s([], 'id', '( %s -> K e. NN0 )' % P)
    v = w.s([kn, w.inst('coprimeto0')], 'syl', '( %s -> ( (/) CoprimeTo K ) = <. 1o , 0 >. )' % P)
    p = projeq(w, P, '( (/) CoprimeTo K )', v, '1o', '0', ex1o(w, P), exc0(w, P), 2)
    h = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % P)
    z = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('leid')], 'ax-mp', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % P)
    w.qed([w.s([p, z], 'eqbrtrd', '( %s -> ( 2nd ` ( (/) CoprimeTo K ) ) <_ 0 )' % P), h], 'breqtrrd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ K e. NN0 )' % A
    L = '( 2nd ` ( %s CoprimeTo K ) )' % CSV
    CV = '( 1st ` ( V CoprimeTo K ) )'
    SUM = '( ( 2nd ` ( V CoprimeTo K ) ) + 1 )'
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), kn], 'mpd', '( %s -> ( 2nd ` ( V CoprimeTo K ) ) <_ ( # ` V ) )' % A2)
    ccl = w.s([vs, kn, w.inst('coprimetocl')], 'syl2anc', '( %s -> ( V CoprimeTo K ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( V CoprimeTo K )', ccl, '2o', 'NN0')
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A2, SUM))
    cs = w.s([w.s([kn, pn], 'jca', '( %s -> ( K e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('coprimetocs')], 'syl2anc',
             '( %s -> ( %s CoprimeTo K ) = if ( %s , <. (/) , 1 >. , <. %s , %s >. ) )' % (A2, CSV, CMOD, CV, SUM))
    vt, vf = ifproj(w, A2, '( %s CoprimeTo K )' % CSV, cs, CMOD, '<. (/) , 1 >.', '<. %s , %s >.' % (CV, SUM))
    T = '( %s /\\ %s )' % (A2, CMOD)
    F = '( %s /\\ -. %s )' % (A2, CMOD)
    lenn = w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A2)
    lenr = w.s([lenn], 'nn0red', '( %s -> ( # ` V ) e. RR )' % A2)
    lge = w.s([lenn], 'nn0ge0d', '( %s -> 0 <_ ( # ` V ) )' % A2)
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    pt = projeq(w, T, '( %s CoprimeTo K )' % CSV, vt, '(/)', '1', ex0(w, T), ex1(w, T), 2)
    l1 = lin.linarith(w, T, [w.s([lge], 'adantr', '( %s -> 0 <_ ( # ` V ) )' % T)], '1 <_ ( ( # ` V ) + 1 )',
                      leaves={'( # ` V )': w.s([lenr], 'adantr', '( %s -> ( # ` V ) e. RR )' % T)})
    ct = w.s([w.s([pt, l1], 'eqbrtrd', '( %s -> %s <_ ( ( # ` V ) + 1 ) )' % (T, L)),
              w.s([lc], 'adantr', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (T, CSV))], 'breqtrrd', '( %s -> %s <_ ( # ` %s ) )' % (T, L, CSV))
    pf = projeq(w, F, '( %s CoprimeTo K )' % CSV, vf, CV, SUM,
                w.s([a1], 'adantr', '( %s -> %s e. 2o )' % (F, CV)), w.s([xb], 'adantr', '( %s -> %s e. NN0 )' % (F, SUM)), 2)
    l2 = lin.linarith(w, F, [w.s([ihs], 'adantr', '( %s -> ( 2nd ` ( V CoprimeTo K ) ) <_ ( # ` V ) )' % F)], '%s <_ ( ( # ` V ) + 1 )' % SUM,
                      leaves={'( # ` V )': w.s([lenr], 'adantr', '( %s -> ( # ` V ) e. RR )' % F),
                              '( 2nd ` ( V CoprimeTo K ) )': w.s([w.s([b1], 'adantr', '( %s -> ( 2nd ` ( V CoprimeTo K ) ) e. NN0 )' % F)], 'nn0red',
                                                                 '( %s -> ( 2nd ` ( V CoprimeTo K ) ) e. RR )' % F)})
    cf = w.s([w.s([pf, l2], 'eqbrtrd', '( %s -> %s <_ ( ( # ` V ) + 1 ) )' % (F, L)),
              w.s([lc], 'adantr', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (F, CSV))], 'breqtrrd', '( %s -> %s <_ ( # ` %s ) )' % (F, L, CSV))
    w.qed([w.s([ct, cf], 'pm2.61dan', '( %s -> %s <_ ( # ` %s ) )' % (A2, L, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( S e. Word NN0 /\\ K e. NN0 )'
    w.qed([w.s([w.s([], 'simpl', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpr', '( %s -> K e. NN0 )' % T)], 'mpd', '( %s -> ( 2nd ` ( S CoprimeTo K ) ) <_ ( # ` S ) )' % T)
family(run, 'coprimetolen', PHI, _b, _s, finish=_f, desc='The cost of coprimeTo is at most the length of the list (Lean: coprimeTo_cost, the strong form its proof establishes).', only=only)

# ----------------------------------------------------------------- coprimetocost
if not only or 'coprimetocost' in only:
    w = W('coprimetocost', 'The cost of coprimeTo (Lean: coprimeTo_cost).')
    T = '( S e. Word NN0 /\\ K e. NN0 )'
    ss = w.s([], 'simpl', '( %s -> S e. Word NN0 )' % T)
    kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % T)
    le = w.s([ss, kn, w.inst('coprimetolen')], 'syl2anc', '( %s -> ( 2nd ` ( S CoprimeTo K ) ) <_ ( # ` S ) )' % T)
    lenn = w.s([ss, w.inst('lencl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % T)
    lenr = w.s([lenn], 'nn0red', '( %s -> ( # ` S ) e. RR )' % T)
    ccl = w.s([ss, kn, w.inst('coprimetocl')], 'syl2anc', '( %s -> ( S CoprimeTo K ) e. %s )' % (T, B2))
    _, b1 = paircl(w, T, '( S CoprimeTo K )', ccl, '2o', 'NN0')
    cr = w.s([b1], 'nn0red', '( %s -> ( 2nd ` ( S CoprimeTo K ) ) e. RR )' % T)
    lin.linarith(w, T, [le], '( 2nd ` ( S CoprimeTo K ) ) <_ ( ( # ` S ) + 1 )',
                 leaves={'( # ` S )': lenr, '( 2nd ` ( S CoprimeTo K ) )': cr}, name='qed')
    run(w)

# ======================================================================= coprimeTo spec
RALP = lambda x: 'A. q e. ran %s q e. Prime' % x
PHI = '( ( K e. NN /\\ %s ) -> ( %s <-> ( K gcd %s ) = 1 ) )' % (RALP('s'), RALD('s'), PRD('s'))
def _b(w, goal):
    P = '( K e. NN /\\ %s )' % RALP('(/)')
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % P)
    l = w.s([w.s([rn0eq(w, P)], 'raleqdv', '( %s -> ( %s <-> A. q e. (/) -. q || K ) )' % (P, RALD('(/)'))),
             w.s([w.s([], 'ral0', 'A. q e. (/) -. q || K')], 'a1i', '( %s -> A. q e. (/) -. q || K )' % P)], 'mpbird',
            '( %s -> %s )' % (P, RALD('(/)')))
    pz = w.s([w.s([], 'algprod0', '%s = 1' % PRD('(/)'))], 'a1i', '( %s -> %s = 1 )' % (P, PRD('(/)')))
    g1 = w.s([w.s([kn], 'nnzd', '( %s -> K e. ZZ )' % P), w.inst('gcd1')], 'syl', '( %s -> ( K gcd 1 ) = 1 )' % P)
    r = w.s([w.s([pz], 'oveq2d', '( %s -> ( K gcd %s ) = ( K gcd 1 ) )' % (P, PRD('(/)'))), g1], 'eqtrd',
            '( %s -> ( K gcd %s ) = 1 )' % (P, PRD('(/)')))
    w.qed([l, r], '2thd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ ( K e. NN /\\ %s ) )' % (A, RALP(CSV))
    PV = PRD('V')
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    kn = w.s([], 'simprl', '( %s -> K e. NN )' % A2)
    alp = w.s([], 'simprr', '( %s -> %s )' % (A2, RALP(CSV)))
    rc = w.s([pn, vs, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A2, CSV))
    pex = w.s([pn], 'elexd', '( %s -> P e. _V )' % A2)
    def splitral(bodyP, bodyq, sbstep, allstep, nm):
        u = w.s([w.s([rc], 'raleqdv', '( %s -> ( A. q e. ran %s %s <-> A. q e. ( { P } u. ran V ) %s ) )' % (A2, CSV, bodyq, bodyq)),
                 w.s([w.s([], 'ralunb', '( A. q e. ( { P } u. ran V ) %s <-> ( A. q e. { P } %s /\\ A. q e. ran V %s ) )' % (bodyq, bodyq, bodyq))], 'a1i',
                     '( %s -> ( A. q e. ( { P } u. ran V ) %s <-> ( A. q e. { P } %s /\\ A. q e. ran V %s ) ) )' % (A2, bodyq, bodyq, bodyq))], 'bitrd',
                '( %s -> ( A. q e. ran %s %s <-> ( A. q e. { P } %s /\\ A. q e. ran V %s ) ) )' % (A2, CSV, bodyq, bodyq, bodyq))
        rs0 = w.s([sbstep], 'ralsng', '( P e. _V -> ( A. q e. { P } %s <-> %s ) )' % (bodyq, bodyP))
        rs = w.s([pex, rs0], 'syl', '( %s -> ( A. q e. { P } %s <-> %s ) )' % (A2, bodyq, bodyP))
        return w.s([u, w.s([rs], 'anbi1d', '( %s -> ( ( A. q e. { P } %s /\\ A. q e. ran V %s ) <-> ( %s /\\ A. q e. ran V %s ) ) )' % (A2, bodyq, bodyq, bodyP, bodyq))],
                   'bitrd', '( %s -> ( A. q e. ran %s %s <-> ( %s /\\ A. q e. ran V %s ) ) )' % (A2, CSV, bodyq, bodyP, bodyq)), rs
    sbp = w.s([w.s([], 'id', '( q = P -> q = P )')], 'eleq1d', '( q = P -> ( q e. Prime <-> P e. Prime ) )')
    prsp, _ = splitral('P e. Prime', 'q e. Prime', sbp, alp, 'prm')
    both = w.s([prsp, alp], 'mpbid', '( %s -> ( P e. Prime /\\ %s ) )' % (A2, RALP('V')))
    pprm = w.s([both], 'simpld', '( %s -> P e. Prime )' % A2)
    alv = w.s([both], 'simprd', '( %s -> %s )' % (A2, RALP('V')))
    sbd = w.s([w.s([w.s([], 'id', '( q = P -> q = P )')], 'breq1d', '( q = P -> ( q || K <-> P || K ) )')], 'notbid',
              '( q = P -> ( -. q || K <-> -. P || K ) )')
    dvsp, _ = splitral('-. P || K', '-. q || K', sbd, None, 'dvd')
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), w.s([kn, alv], 'jca', '( %s -> ( K e. NN /\\ %s ) )' % (A2, RALP('V')))], 'mpd',
              '( %s -> ( %s <-> ( K gcd %s ) = 1 ) )' % (A2, RALD('V'), PV))
    lhs = w.s([dvsp, w.s([ihs], 'anbi2d', '( %s -> ( ( -. P || K /\\ %s ) <-> ( -. P || K /\\ ( K gcd %s ) = 1 ) ) )' % (A2, RALD('V'), PV))], 'bitrd',
              '( %s -> ( %s <-> ( -. P || K /\\ ( K gcd %s ) = 1 ) ) )' % (A2, RALD(CSV), PV))
    # closures
    pnn = w.s([pprm, w.inst('prmnn')], 'syl', '( %s -> P e. NN )' % A2)
    Q3 = '( %s /\\ r e. ran V )' % A2
    sbr = w.s([w.s([], 'id', '( q = r -> q = r )')], 'eleq1d', '( q = r -> ( q e. Prime <-> r e. Prime ) )')
    qp = w.s([sbr, w.s([alv], 'adantr', '( %s -> %s )' % (Q3, RALP('V'))), w.s([], 'simpr', '( %s -> r e. ran V )' % Q3)], 'rspcdva',
             '( %s -> r e. Prime )' % Q3)
    q1 = w.s([w.s([qp, w.inst('prmnn')], 'syl', '( %s -> r e. NN )' % Q3)], 'nnge1d', '( %s -> 1 <_ r )' % Q3)
    algr = w.s([q1], 'ralrimiva', '( %s -> A. r e. ran V 1 <_ r )' % A2)
    cbvr = w.s([w.s([w.s([], 'id', '( q = r -> q = r )')], 'breq2d', '( q = r -> ( 1 <_ q <-> 1 <_ r ) )')], 'cbvralvw',
               '( A. q e. ran V 1 <_ q <-> A. r e. ran V 1 <_ r )')
    alg1 = w.s([w.s([cbvr], 'a1i', '( %s -> ( A. q e. ran V 1 <_ q <-> A. r e. ran V 1 <_ r ) )' % A2), algr], 'mpbird',
               '( %s -> A. q e. ran V 1 <_ q )' % A2)
    pvnn = w.s([vs, alg1, w.inst('algprodnn')], 'syl2anc', '( %s -> %s e. NN )' % (A2, PV))
    pcs = w.s([pn, vs, w.inst('algprodcs')], 'syl2anc', '( %s -> %s = ( P x. %s ) )' % (A2, PRD(CSV), PV))
    kz = w.s([kn], 'nnzd', '( %s -> K e. ZZ )' % A2)
    pz = w.s([pnn], 'nnzd', '( %s -> P e. ZZ )' % A2)
    pvz = w.s([pvnn], 'nnzd', '( %s -> %s e. ZZ )' % (A2, PV))
    mz = w.s([pz, pvz], 'zmulcld', '( %s -> ( P x. %s ) e. ZZ )' % (A2, PV))
    # the product split
    T = '( %s /\\ ( K gcd ( P x. %s ) ) = 1 )' % (A2, PV)
    ht = w.s([], 'simpr', '( %s -> ( K gcd ( P x. %s ) ) = 1 )' % (T, PV))
    d1 = w.s([w.s([pz], 'adantr', '( %s -> P e. ZZ )' % T), w.s([pvz], 'adantr', '( %s -> %s e. ZZ )' % (T, PV)), w.inst('dvdsmul1')], 'syl2anc',
             '( %s -> P || ( P x. %s ) )' % (T, PV))
    d2 = w.s([w.s([pz], 'adantr', '( %s -> P e. ZZ )' % T), w.s([pvz], 'adantr', '( %s -> %s e. ZZ )' % (T, PV)), w.inst('dvdsmul2')], 'syl2anc',
             '( %s -> %s || ( P x. %s ) )' % (T, PV, PV))
    g1 = w.s([w.s([w.s([kz], 'adantr', '( %s -> K e. ZZ )' % T), w.s([pz], 'adantr', '( %s -> P e. ZZ )' % T),
                   w.s([mz], 'adantr', '( %s -> ( P x. %s ) e. ZZ )' % (T, PV))], '3jca',
                  '( %s -> ( K e. ZZ /\\ P e. ZZ /\\ ( P x. %s ) e. ZZ ) )' % (T, PV)),
              w.s([ht, d1], 'jca', '( %s -> ( ( K gcd ( P x. %s ) ) = 1 /\\ P || ( P x. %s ) ) )' % (T, PV, PV)), w.inst('rpdvds')], 'syl2anc',
             '( %s -> ( K gcd P ) = 1 )' % T)
    g2 = w.s([w.s([w.s([kz], 'adantr', '( %s -> K e. ZZ )' % T), w.s([pvz], 'adantr', '( %s -> %s e. ZZ )' % (T, PV)),
                   w.s([mz], 'adantr', '( %s -> ( P x. %s ) e. ZZ )' % (T, PV))], '3jca',
                  '( %s -> ( K e. ZZ /\\ %s e. ZZ /\\ ( P x. %s ) e. ZZ ) )' % (T, PV, PV)),
              w.s([ht, d2], 'jca', '( %s -> ( ( K gcd ( P x. %s ) ) = 1 /\\ %s || ( P x. %s ) ) )' % (T, PV, PV, PV)), w.inst('rpdvds')], 'syl2anc',
             '( %s -> ( K gcd %s ) = 1 )' % (T, PV))
    cp = w.s([w.s([pprm], 'adantr', '( %s -> P e. Prime )' % T), w.s([kz], 'adantr', '( %s -> K e. ZZ )' % T), w.inst('coprm')], 'syl2anc',
             '( %s -> ( -. P || K <-> ( P gcd K ) = 1 ) )' % T)
    gcm = w.s([w.s([pz], 'adantr', '( %s -> P e. ZZ )' % T), w.s([kz], 'adantr', '( %s -> K e. ZZ )' % T), w.inst('gcdcom')], 'syl2anc',
              '( %s -> ( P gcd K ) = ( K gcd P ) )' % T)
    npk = w.s([cp, w.s([gcm, g1], 'eqtrd', '( %s -> ( P gcd K ) = 1 )' % T)], 'mpbird', '( %s -> -. P || K )' % T)
    fwd = w.s([w.s([npk, g2], 'jca', '( %s -> ( -. P || K /\\ ( K gcd %s ) = 1 ) )' % (T, PV))], 'ex',
              '( %s -> ( ( K gcd ( P x. %s ) ) = 1 -> ( -. P || K /\\ ( K gcd %s ) = 1 ) ) )' % (A2, PV, PV))
    # backward
    U = '( %s /\\ ( -. P || K /\\ ( K gcd %s ) = 1 ) )' % (A2, PV)
    hu1 = w.s([], 'simprl', '( %s -> -. P || K )' % U)
    hu2 = w.s([], 'simprr', '( %s -> ( K gcd %s ) = 1 )' % (U, PV))
    cpu = w.s([w.s([pprm], 'adantr', '( %s -> P e. Prime )' % U), w.s([kz], 'adantr', '( %s -> K e. ZZ )' % U), w.inst('coprm')], 'syl2anc',
              '( %s -> ( -. P || K <-> ( P gcd K ) = 1 ) )' % U)
    gcmu = w.s([w.s([pz], 'adantr', '( %s -> P e. ZZ )' % U), w.s([kz], 'adantr', '( %s -> K e. ZZ )' % U), w.inst('gcdcom')], 'syl2anc',
               '( %s -> ( P gcd K ) = ( K gcd P ) )' % U)
    gkp = w.s([gcmu, w.s([cpu, hu1], 'mpbid', '( %s -> ( P gcd K ) = 1 )' % U)], 'eqtr3d', '( %s -> ( K gcd P ) = 1 )' % U)
    rm = w.s([w.s([w.s([kn], 'adantr', '( %s -> K e. NN )' % U), w.s([pnn], 'adantr', '( %s -> P e. NN )' % U),
                   w.s([pvnn], 'adantr', '( %s -> %s e. NN )' % (U, PV))], '3jca', '( %s -> ( K e. NN /\\ P e. NN /\\ %s e. NN ) )' % (U, PV)),
              gkp, w.inst('rpmulgcd')], 'syl2anc', '( %s -> ( K gcd ( P x. %s ) ) = ( K gcd %s ) )' % (U, PV, PV))
    bwd = w.s([w.s([rm, hu2], 'eqtrd', '( %s -> ( K gcd ( P x. %s ) ) = 1 )' % (U, PV))], 'ex',
              '( %s -> ( ( -. P || K /\\ ( K gcd %s ) = 1 ) -> ( K gcd ( P x. %s ) ) = 1 ) )' % (A2, PV, PV))
    split = w.s([fwd, bwd], 'impbid', '( %s -> ( ( K gcd ( P x. %s ) ) = 1 <-> ( -. P || K /\\ ( K gcd %s ) = 1 ) ) )' % (A2, PV, PV))
    rhs = w.s([w.s([pcs], 'oveq2d', '( %s -> ( K gcd %s ) = ( K gcd ( P x. %s ) ) )' % (A2, PRD(CSV), PV))], 'eqeq1d',
              '( %s -> ( ( K gcd %s ) = 1 <-> ( K gcd ( P x. %s ) ) = 1 ) )' % (A2, PRD(CSV), PV))
    w.qed([w.s([lhs, w.s([rhs, split], 'bitrd', '( %s -> ( ( K gcd %s ) = 1 <-> ( -. P || K /\\ ( K gcd %s ) = 1 ) ) )' % (A2, PRD(CSV), PV))], 'bitr4d',
               '( %s -> ( %s <-> ( K gcd %s ) = 1 ) )' % (A2, RALD(CSV), PRD(CSV)))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( ( S e. Word NN0 /\\ K e. NN ) /\\ %s )' % RALP('S')
    w.qed([w.s([w.s([], 'simpll', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([w.s([], 'simplr', '( %s -> K e. NN )' % T), w.s([], 'simpr', '( %s -> %s )' % (T, RALP('S')))], 'jca',
               '( %s -> ( K e. NN /\\ %s ) )' % (T, RALP('S')))], 'mpd',
          '( %s -> ( %s <-> ( K gcd %s ) = 1 ) )' % (T, RALD('S'), PRD('S')))
family(run, 'coprimetodvd', PHI, _b, _s, finish=_f, prods=['s'],
       desc='No prime of the list divides K exactly when K is coprime to the product (Lean: the Nat.coprime_list_prod_right_iff half of coprimeTo_spec).', only=only)

# ----------------------------------------------------------------- coprimetospec
if not only or 'coprimetospec' in only:
    w = W('coprimetospec', 'coprimeTo reports true exactly when K is coprime to the product of the list (Lean: coprimeTo_spec).')
    T = '( ( S e. Word NN0 /\\ K e. NN ) /\\ %s )' % RALP('S')
    ss = w.s([], 'simpll', '( %s -> S e. Word NN0 )' % T)
    kn = w.s([], 'simplr', '( %s -> K e. NN )' % T)
    alp = w.s([], 'simpr', '( %s -> %s )' % (T, RALP('S')))
    Q3 = '( %s /\\ r e. ran S )' % T
    sbr = w.s([w.s([], 'id', '( q = r -> q = r )')], 'eleq1d', '( q = r -> ( q e. Prime <-> r e. Prime ) )')
    qp = w.s([sbr, w.s([alp], 'adantr', '( %s -> %s )' % (Q3, RALP('S'))), w.s([], 'simpr', '( %s -> r e. ran S )' % Q3)], 'rspcdva',
             '( %s -> r e. Prime )' % Q3)
    qn = w.s([qp, w.inst('prmnn')], 'syl', '( %s -> r e. NN )' % Q3)
    alnr = w.s([qn], 'ralrimiva', '( %s -> A. r e. ran S r e. NN )' % T)
    cbvr = w.s([w.s([w.s([], 'id', '( q = r -> q = r )')], 'eleq1d', '( q = r -> ( q e. NN <-> r e. NN ) )')], 'cbvralvw',
               '( %s <-> A. r e. ran S r e. NN )' % RALN('S'))
    aln = w.s([w.s([cbvr], 'a1i', '( %s -> ( %s <-> A. r e. ran S r e. NN ) )' % (T, RALN('S'))), alnr], 'mpbird',
              '( %s -> %s )' % (T, RALN('S')))
    b1 = w.s([w.s([ss, w.s([kn], 'nnnn0d', '( %s -> K e. NN0 )' % T)], 'jca', '( %s -> ( S e. Word NN0 /\\ K e. NN0 ) )' % T), aln,
              w.inst('coprimetofst')], 'syl2anc', '( %s -> ( ( 1st ` ( S CoprimeTo K ) ) = 1o <-> %s ) )' % (T, RALD('S')))
    b2 = w.s([w.s([ss, kn], 'jca', '( %s -> ( S e. Word NN0 /\\ K e. NN ) )' % T), alp, w.inst('coprimetodvd')], 'syl2anc',
             '( %s -> ( %s <-> ( K gcd %s ) = 1 ) )' % (T, RALD('S'), PRD('S')))
    w.qed([b1, b2], 'bitrd', '( %s -> ( ( 1st ` ( S CoprimeTo K ) ) = 1o <-> ( K gcd %s ) = 1 ) )' % (T, PRD('S')))
    run(w)
