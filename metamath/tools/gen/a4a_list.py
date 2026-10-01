"""Sortie A4a, batch 3: the list recursions of AlgScan.lean (prodL, mulAll,
coprimeTo, notMemTD, korseltTD, nodupTD, allPrimeTD, divisorsOf)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CSV = '( <" P "> ++ V )'
N2 = '( NN0 X. NN0 )'
B2 = '( 2o X. NN0 )'
WN = '( Word NN0 X. NN0 )'

# ======================================================================= prodL spec
PHI = '( 1st ` ( ProdL ` s ) ) = %s' % PRD('s')

w = W('prodlspb', 'Base of the induction for the value of prodL (Lean: prodL_spec, nil case).')
e1 = w.s([], 'prodl0', '( ProdL ` (/) ) = <. 1 , 0 >.')
e2 = w.s([e1], 'fveq2i', '( 1st ` ( ProdL ` (/) ) ) = ( 1st ` <. 1 , 0 >. )')
e3 = w.s([w.s([], '1ex', '1 e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. 1 , 0 >. ) = 1')
e4 = w.s([], 'algprod0', '%s = 1' % PRD('(/)'))
w.qed([w.s([e2, e3], 'eqtri', '( 1st ` ( ProdL ` (/) ) ) = 1'), e4], 'eqtr4i', subst(PHI, 's', '(/)'))
run(w)

w = W('prodlsps', 'Step of the induction for the value of prodL (Lean: prodL_spec, cons case).')
A = '( V e. Word NN0 /\\ P e. NN0 /\\ %s )' % subst(PHI, 's', 'V')
vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
ih = w.s([], 'simp3', '( %s -> %s )' % (A, subst(PHI, 's', 'V')))
cl = w.s([vs, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` V ) e. %s )' % (A, N2))
a1, b1 = paircl(w, A, '( ProdL ` V )', cl, 'NN0', 'NN0')
cs = w.s([pn, vs, w.inst('prodlcs')], 'syl2anc',
         '( %s -> ( ProdL ` %s ) = <. ( P x. ( 1st ` ( ProdL ` V ) ) ) , ( ( 2nd ` ( ProdL ` V ) ) + 1 ) >. )' % (A, CSV))
xa = w.s([pn, a1], 'nn0mulcld', '( %s -> ( P x. ( 1st ` ( ProdL ` V ) ) ) e. NN0 )' % A)
xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( ProdL ` V ) ) + 1 ) e. NN0 )' % A)
p1 = projeq(w, A, '( ProdL ` %s )' % CSV, cs, '( P x. ( 1st ` ( ProdL ` V ) ) )', '( ( 2nd ` ( ProdL ` V ) ) + 1 )', xa, xb, 1)
ihx = w.s([ih], 'oveq2d', '( %s -> ( P x. ( 1st ` ( ProdL ` V ) ) ) = ( P x. %s ) )' % (A, PRD('V')))
pc = w.s([pn, vs, w.inst('algprodcs')], 'syl2anc', '( %s -> %s = ( P x. %s ) )' % (A, PRD(CSV), PRD('V')))
w.qed([w.s([p1, ihx], 'eqtrd', '( %s -> ( 1st ` ( ProdL ` %s ) ) = ( P x. %s ) )' % (A, CSV, PRD('V'))), pc], 'eqtr4d',
      '( %s -> %s )' % (A, subst(PHI, 's', CSV)))
run(w)

w = W('prodlspec', 'The value of prodL is the product of the list (Lean: prodL_spec).')
st, phit = wrdind(w, PHI, 'S', 'prodlspb', 'prodlsps', prods=['s'])
w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
run(w)

# ======================================================================= prodL cost
PHI = '( 2nd ` ( ProdL ` s ) ) = ( # ` s )'
def _b(w, goal):
    e1 = w.s([], 'prodl0', '( ProdL ` (/) ) = <. 1 , 0 >.')
    e2 = w.s([e1], 'fveq2i', '( 2nd ` ( ProdL ` (/) ) ) = ( 2nd ` <. 1 , 0 >. )')
    e3 = w.s([w.s([], '1ex', '1 e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. 1 , 0 >. ) = 0')
    e4 = w.s([], 'hash0', '( # ` (/) ) = 0')
    w.qed([w.s([e2, e3], 'eqtri', '( 2nd ` ( ProdL ` (/) ) ) = 0'), e4], 'eqtr4i', goal)
def _s(w, A, ih, co):
    vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    cl = w.s([vs, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` V ) e. %s )' % (A, N2))
    a1, b1 = paircl(w, A, '( ProdL ` V )', cl, 'NN0', 'NN0')
    cs = w.s([pn, vs, w.inst('prodlcs')], 'syl2anc',
             '( %s -> ( ProdL ` %s ) = <. ( P x. ( 1st ` ( ProdL ` V ) ) ) , ( ( 2nd ` ( ProdL ` V ) ) + 1 ) >. )' % (A, CSV))
    xa = w.s([pn, a1], 'nn0mulcld', '( %s -> ( P x. ( 1st ` ( ProdL ` V ) ) ) e. NN0 )' % A)
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( ProdL ` V ) ) + 1 ) e. NN0 )' % A)
    p2 = projeq(w, A, '( ProdL ` %s )' % CSV, cs, '( P x. ( 1st ` ( ProdL ` V ) ) )', '( ( 2nd ` ( ProdL ` V ) ) + 1 )', xa, xb, 2)
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A, CSV))
    w.qed([w.s([p2, w.s([ihs], 'oveq1d', '( %s -> ( ( 2nd ` ( ProdL ` V ) ) + 1 ) = ( ( # ` V ) + 1 ) )' % A)], 'eqtrd',
               '( %s -> ( 2nd ` ( ProdL ` %s ) ) = ( ( # ` V ) + 1 ) )' % (A, CSV)), lc], 'eqtr4d', '( %s -> %s )' % (A, co))
family(run, 'prodlcost', PHI, _b, _s, desc='The cost of prodL is the length of the list (Lean: prodL_cost).')

MA = '( 1st ` ( Q MulAll V ) )'
MC = '( <" ( P x. Q ) "> ++ %s )' % MA

def mulallctx(w, A2):
    """the common context of a mulAll step, under A2 = ( A /\\ Q e. NN0 )"""
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qn = w.s([], 'simpr', '( %s -> Q e. NN0 )' % A2)
    cl = w.s([qn, vs, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll V ) e. %s )' % (A2, WN))
    a1, b1 = paircl(w, A2, '( Q MulAll V )', cl, 'Word NN0', 'NN0')
    cs = w.s([w.s([pn, qn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2) if False else
              w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('mulallcs')], 'syl2anc',
             '( %s -> ( Q MulAll %s ) = <. %s , ( ( 2nd ` ( Q MulAll V ) ) + 1 ) >. )' % (A2, CSV, MC))
    pq = w.s([pn, qn], 'nn0mulcld', '( %s -> ( P x. Q ) e. NN0 )' % A2)
    s1 = w.s([pq, w.inst('s1cl')], 'syl', '( %s -> <" ( P x. Q ) "> e. Word NN0 )' % A2)
    xa = w.s([s1, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, MC))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll V ) ) + 1 ) e. NN0 )' % A2)
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    return vs, pn, qn, a1, b1, cs, pq, xa, xb, lc

# ======================================================================= mulAll cost
PHI = '( Q e. NN0 -> ( 2nd ` ( Q MulAll s ) ) = ( # ` s ) )'
def _b(w, goal):
    P = 'Q e. NN0'
    v = w.s([], 'mulall0', '( %s -> ( Q MulAll (/) ) = <. (/) , 0 >. )' % P)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % P)
    z2 = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % P)
    p = projeq(w, P, '( Q MulAll (/) )', v, '(/)', '0', z, z2, 2)
    h = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % P)
    w.qed([p, h], 'eqtr4d', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ Q e. NN0 )' % A
    vs, pn, qn, a1, b1, cs, pq, xa, xb, lc = mulallctx(w, A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), qn], 'mpd', '( %s -> ( 2nd ` ( Q MulAll V ) ) = ( # ` V ) )' % A2)
    p2 = projeq(w, A2, '( Q MulAll %s )' % CSV, cs, MC, '( ( 2nd ` ( Q MulAll V ) ) + 1 )', xa, xb, 2)
    w.qed([w.s([w.s([p2, w.s([ihs], 'oveq1d', '( %s -> ( ( 2nd ` ( Q MulAll V ) ) + 1 ) = ( ( # ` V ) + 1 ) )' % A2)], 'eqtrd',
                    '( %s -> ( 2nd ` ( Q MulAll %s ) ) = ( ( # ` V ) + 1 ) )' % (A2, CSV)), lc], 'eqtr4d',
               '( %s -> ( 2nd ` ( Q MulAll %s ) ) = ( # ` %s ) )' % (A2, CSV, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( Q e. NN0 /\\ S e. Word NN0 )'
    w.qed([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T), w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit)),
           w.s([], 'simpl', '( %s -> Q e. NN0 )' % T)], 'mp2d' if False else 'sylc',
          '( %s -> ( 2nd ` ( Q MulAll S ) ) = ( # ` S ) )' % T) if False else \
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> Q e. NN0 )' % T)], 'mpd', '( %s -> ( 2nd ` ( Q MulAll S ) ) = ( # ` S ) )' % T)
family(run, 'mulallcost', PHI, _b, _s, finish=_f, desc='The cost of mulAll is the length of the list (Lean: mulAll_snd).')

# ======================================================================= mulAll length
PHI = '( Q e. NN0 -> ( # ` ( 1st ` ( Q MulAll s ) ) ) = ( # ` s ) )'
def _b(w, goal):
    P = 'Q e. NN0'
    v = w.s([], 'mulall0', '( %s -> ( Q MulAll (/) ) = <. (/) , 0 >. )' % P)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % P)
    z2 = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % P)
    p = projeq(w, P, '( Q MulAll (/) )', v, '(/)', '0', z, z2, 1)
    w.qed([p], 'fveq2d', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ Q e. NN0 )' % A
    vs, pn, qn, a1, b1, cs, pq, xa, xb, lc = mulallctx(w, A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), qn], 'mpd', '( %s -> ( # ` %s ) = ( # ` V ) )' % (A2, MA))
    p1 = projeq(w, A2, '( Q MulAll %s )' % CSV, cs, MC, '( ( 2nd ` ( Q MulAll V ) ) + 1 )', xa, xb, 1)
    ll = w.s([pq, a1, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (A2, MC, MA))
    ch = w.s([w.s([p1], 'fveq2d', '( %s -> ( # ` ( 1st ` ( Q MulAll %s ) ) ) = ( # ` %s ) )' % (A2, CSV, MC)), ll], 'eqtrd',
             '( %s -> ( # ` ( 1st ` ( Q MulAll %s ) ) ) = ( ( # ` %s ) + 1 ) )' % (A2, CSV, MA))
    ch2 = w.s([ch, w.s([ihs], 'oveq1d', '( %s -> ( ( # ` %s ) + 1 ) = ( ( # ` V ) + 1 ) )' % (A2, MA))], 'eqtrd',
              '( %s -> ( # ` ( 1st ` ( Q MulAll %s ) ) ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    w.qed([w.s([ch2, lc], 'eqtr4d', '( %s -> ( # ` ( 1st ` ( Q MulAll %s ) ) ) = ( # ` %s ) )' % (A2, CSV, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( Q e. NN0 /\\ S e. Word NN0 )'
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> Q e. NN0 )' % T)], 'mpd', '( %s -> ( # ` ( 1st ` ( Q MulAll S ) ) ) = ( # ` S ) )' % T)
family(run, 'mulalllen', PHI, _b, _s, finish=_f, desc='The length of the mulAll image is the length of the list (Lean: mulAll_fst, length half).')

# ======================================================================= mulAll membership
PHI = '( ( Q e. NN0 /\\ X e. NN0 ) -> ( X e. ran ( 1st ` ( Q MulAll s ) ) <-> E. d e. ran s X = ( d x. Q ) ) )'
def _b(w, goal):
    P = '( Q e. NN0 /\\ X e. NN0 )'
    qn = w.s([], 'simpl', '( %s -> Q e. NN0 )' % P)
    v = w.s([qn, w.inst('mulall0')], 'syl', '( %s -> ( Q MulAll (/) ) = <. (/) , 0 >. )' % P)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % P)
    z2 = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % P)
    p = projeq(w, P, '( Q MulAll (/) )', v, '(/)', '0', z, z2, 1)
    rn = w.s([w.s([p], 'rneqd', '( %s -> ran ( 1st ` ( Q MulAll (/) ) ) = ran (/) )' % P),
              w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % P)], 'eqtrd',
             '( %s -> ran ( 1st ` ( Q MulAll (/) ) ) = (/) )' % P)
    nl = w.s([w.s([rn], 'eleq2d', '( %s -> ( X e. ran ( 1st ` ( Q MulAll (/) ) ) <-> X e. (/) ) )' % P),
              w.s([w.s([], 'noel', '-. X e. (/)')], 'a1i', '( %s -> -. X e. (/) )' % P)], 'mtbird',
             '( %s -> -. X e. ran ( 1st ` ( Q MulAll (/) ) ) )' % P)
    rr = w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % P)
    nr = w.s([w.s([rr], 'rexeqdv', '( %s -> ( E. d e. ran (/) X = ( d x. Q ) <-> E. d e. (/) X = ( d x. Q ) ) )' % P),
              w.s([w.s([], 'rex0', '-. E. d e. (/) X = ( d x. Q )')], 'a1i', '( %s -> -. E. d e. (/) X = ( d x. Q ) )' % P)], 'mtbird',
             '( %s -> -. E. d e. ran (/) X = ( d x. Q ) )' % P)
    w.qed([nl, nr], '2falsed', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ ( Q e. NN0 /\\ X e. NN0 ) )' % A
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qn = w.s([], 'simprl', '( %s -> Q e. NN0 )' % A2)
    xn = w.s([], 'simprr', '( %s -> X e. NN0 )' % A2)
    cl = w.s([qn, vs, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll V ) e. %s )' % (A2, WN))
    a1, b1 = paircl(w, A2, '( Q MulAll V )', cl, 'Word NN0', 'NN0')
    cs = w.s([w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('mulallcs')], 'syl2anc',
             '( %s -> ( Q MulAll %s ) = <. %s , ( ( 2nd ` ( Q MulAll V ) ) + 1 ) >. )' % (A2, CSV, MC))
    pq = w.s([pn, qn], 'nn0mulcld', '( %s -> ( P x. Q ) e. NN0 )' % A2)
    s1 = w.s([pq, w.inst('s1cl')], 'syl', '( %s -> <" ( P x. Q ) "> e. Word NN0 )' % A2)
    xa = w.s([s1, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, MC))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll V ) ) + 1 ) e. NN0 )' % A2)
    p1 = projeq(w, A2, '( Q MulAll %s )' % CSV, cs, MC, '( ( 2nd ` ( Q MulAll V ) ) + 1 )', xa, xb, 1)
    b1x = w.s([w.s([w.s([pq, a1], 'jca', '( %s -> ( ( P x. Q ) e. NN0 /\\ %s e. Word NN0 ) )' % (A2, MA)), xn], 'jca',
                   '( %s -> ( ( ( P x. Q ) e. NN0 /\\ %s e. Word NN0 ) /\\ X e. NN0 ) )' % (A2, MA)), w.inst('algelcs')], 'syl',
              '( %s -> ( X e. ran %s <-> ( X = ( P x. Q ) \\/ X e. ran %s ) ) )' % (A2, MC, MA))
    lh = w.s([w.s([p1], 'rneqd', '( %s -> ran ( 1st ` ( Q MulAll %s ) ) = ran %s )' % (A2, CSV, MC))], 'eleq2d',
             '( %s -> ( X e. ran ( 1st ` ( Q MulAll %s ) ) <-> X e. ran %s ) )' % (A2, CSV, MC))
    lhs = w.s([lh, b1x], 'bitrd', '( %s -> ( X e. ran ( 1st ` ( Q MulAll %s ) ) <-> ( X = ( P x. Q ) \\/ X e. ran %s ) ) )' % (A2, CSV, MA))
    # right-hand side
    rc = w.s([pn, vs, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A2, CSV))
    r1 = w.s([rc], 'rexeqdv', '( %s -> ( E. d e. ran %s X = ( d x. Q ) <-> E. d e. ( { P } u. ran V ) X = ( d x. Q ) ) )' % (A2, CSV))
    r2 = w.s([w.s([], 'rexun', '( E. d e. ( { P } u. ran V ) X = ( d x. Q ) <-> ( E. d e. { P } X = ( d x. Q ) \\/ E. d e. ran V X = ( d x. Q ) ) )')],
             'a1i', '( %s -> ( E. d e. ( { P } u. ran V ) X = ( d x. Q ) <-> ( E. d e. { P } X = ( d x. Q ) \\/ E. d e. ran V X = ( d x. Q ) ) ) )' % A2)
    sbs = w.s([w.s([w.s([], 'id', '( d = P -> d = P )')], 'oveq1d', '( d = P -> ( d x. Q ) = ( P x. Q ) )')], 'eqeq2d',
              '( d = P -> ( X = ( d x. Q ) <-> X = ( P x. Q ) ) )')
    r3a = w.s([sbs], 'rexsng', '( P e. _V -> ( E. d e. { P } X = ( d x. Q ) <-> X = ( P x. Q ) ) )')
    r3 = w.s([w.s([pn], 'elexd', '( %s -> P e. _V )' % A2), r3a], 'syl',
             '( %s -> ( E. d e. { P } X = ( d x. Q ) <-> X = ( P x. Q ) ) )' % A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), w.s([qn, xn], 'jca', '( %s -> ( Q e. NN0 /\\ X e. NN0 ) )' % A2)], 'mpd',
              '( %s -> ( X e. ran %s <-> E. d e. ran V X = ( d x. Q ) ) )' % (A2, MA))
    ihs2 = w.s([ihs], 'bicomd', '( %s -> ( E. d e. ran V X = ( d x. Q ) <-> X e. ran %s ) )' % (A2, MA))
    r4 = w.s([r3, ihs2], 'orbi12d', '( %s -> ( ( E. d e. { P } X = ( d x. Q ) \\/ E. d e. ran V X = ( d x. Q ) ) <-> ( X = ( P x. Q ) \\/ X e. ran %s ) ) )' % (A2, MA))
    rhs = w.s([r1, r2, r4], '3bitrd', '( %s -> ( E. d e. ran %s X = ( d x. Q ) <-> ( X = ( P x. Q ) \\/ X e. ran %s ) ) )' % (A2, CSV, MA))
    w.qed([w.s([lhs, rhs], 'bitr4d', '( %s -> ( X e. ran ( 1st ` ( Q MulAll %s ) ) <-> E. d e. ran %s X = ( d x. Q ) ) )' % (A2, CSV, CSV))],
          'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( ( Q e. NN0 /\\ X e. NN0 ) /\\ S e. Word NN0 )'
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> ( Q e. NN0 /\\ X e. NN0 ) )' % T)], 'mpd',
          '( %s -> ( X e. ran ( 1st ` ( Q MulAll S ) ) <-> E. d e. ran S X = ( d x. Q ) ) )' % T)
family(run, 'mulallel', PHI, _b, _s, finish=_f, desc='Membership in the mulAll image (Lean: List.mem_map at mulAll_fst).')

# ======================================================================= mulAll nodup
PHI = "( ( Q e. NN /\\ Fun `' s ) -> Fun `' ( 1st ` ( Q MulAll s ) ) )"
def _b(w, goal):
    P = "( Q e. NN /\\ Fun `' (/) )"
    qn = w.s([w.s([], 'simpl', '( %s -> Q e. NN )' % P)], 'nnnn0d', '( %s -> Q e. NN0 )' % P)
    v = w.s([qn, w.inst('mulall0')], 'syl', '( %s -> ( Q MulAll (/) ) = <. (/) , 0 >. )' % P)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % P)
    z2 = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % P)
    p = projeq(w, P, '( Q MulAll (/) )', v, '(/)', '0', z, z2, 1)
    w.qed([w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % P), p], 'eqbrtrrd' if False else 'jca',
          '') if False else w.qed([p, w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % P)], 'funeqtrrd' if False else 'syl5eqelr', '') if False else None
    w.lines = [l for l in w.lines if not l.startswith('qed')]
    cn = w.s([p], 'cnveqd', "( %s -> `' ( 1st ` ( Q MulAll (/) ) ) = `' (/) )" % P)
    bi = w.s([cn], 'funeqd', "( %s -> ( Fun `' ( 1st ` ( Q MulAll (/) ) ) <-> Fun `' (/) ) )" % P)
    w.qed([bi, w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % P)], 'mpbird', goal)
def _s(w, A, ih, co):
    A2 = "( %s /\\ ( Q e. NN /\\ Fun `' %s ) )" % (A, CSV)
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    qnn = w.s([], 'simprl', '( %s -> Q e. NN )' % A2)
    qn = w.s([qnn], 'nnnn0d', '( %s -> Q e. NN0 )' % A2)
    fcs = w.s([], 'simprr', "( %s -> Fun `' %s )" % (A2, CSV))
    nd = w.s([w.s([pn, vs, w.inst('algndpcs')], 'syl2anc', "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (A2, CSV)), fcs], 'mpbid',
             "( %s -> ( -. P e. ran V /\\ Fun `' V ) )" % A2)
    npv = w.s([nd], 'simpld', '( %s -> -. P e. ran V )' % A2)
    fv = w.s([nd], 'simprd', "( %s -> Fun `' V )" % A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), w.s([qnn, fv], 'jca', "( %s -> ( Q e. NN /\\ Fun `' V ) )" % A2)], 'mpd',
              "( %s -> Fun `' %s )" % (A2, MA))
    cl = w.s([qn, vs, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll V ) e. %s )' % (A2, WN))
    a1, b1 = paircl(w, A2, '( Q MulAll V )', cl, 'Word NN0', 'NN0')
    cs = w.s([w.s([qn, pn], 'jca', '( %s -> ( Q e. NN0 /\\ P e. NN0 ) )' % A2), vs, w.inst('mulallcs')], 'syl2anc',
             '( %s -> ( Q MulAll %s ) = <. %s , ( ( 2nd ` ( Q MulAll V ) ) + 1 ) >. )' % (A2, CSV, MC))
    pq = w.s([pn, qn], 'nn0mulcld', '( %s -> ( P x. Q ) e. NN0 )' % A2)
    s1 = w.s([pq, w.inst('s1cl')], 'syl', '( %s -> <" ( P x. Q ) "> e. Word NN0 )' % A2)
    xa = w.s([s1, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A2, MC))
    xb = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( Q MulAll V ) ) + 1 ) e. NN0 )' % A2)
    p1 = projeq(w, A2, '( Q MulAll %s )' % CSV, cs, MC, '( ( 2nd ` ( Q MulAll V ) ) + 1 )', xa, xb, 1)
    # ( P x. Q ) is not already in the image
    B = '( %s /\\ E. d e. ran V ( P x. Q ) = ( d x. Q ) )' % A2
    C = '( %s /\\ ( d e. ran V /\\ ( P x. Q ) = ( d x. Q ) ) )' % A2
    dv = w.s([], 'simprl', '( %s -> d e. ran V )' % C)
    dq = w.s([], 'simprr', '( %s -> ( P x. Q ) = ( d x. Q ) )' % C)
    dn = w.s([w.s([w.s([vs], 'adantr', '( %s -> V e. Word NN0 )' % C), dv], 'jca', '( %s -> ( V e. Word NN0 /\\ d e. ran V ) )' % C),
              w.inst('algwrdrn')], 'syl', '( %s -> d e. NN0 )' % C)
    pc = w.s([w.s([pn], 'adantr', '( %s -> P e. NN0 )' % C)], 'nn0cnd', '( %s -> P e. CC )' % C)
    dc = w.s([dn], 'nn0cnd', '( %s -> d e. CC )' % C)
    qc = w.s([w.s([qn], 'adantr', '( %s -> Q e. NN0 )' % C)], 'nn0cnd', '( %s -> Q e. CC )' % C)
    q0 = w.s([w.s([qnn], 'adantr', '( %s -> Q e. NN )' % C)], 'nnne0d', '( %s -> Q =/= 0 )' % C)
    eq = w.s([w.s([pc, dc, qc, q0], 'mulcan2d', '( %s -> ( ( P x. Q ) = ( d x. Q ) <-> P = d ) )' % C), dq], 'mpbid', '( %s -> P = d )' % C)
    inv = w.s([eq, dv], 'eqeltrd', '( %s -> P e. ran V )' % C)
    con = w.s([inv, w.s([npv], 'adantr', '( %s -> -. P e. ran V )' % C)], 'pm2.65da' if False else 'pm2.21fal', '') if False else None
    ctr = w.s([w.s([inv], 'rexlimdvaa', '( %s -> ( E. d e. ran V ( P x. Q ) = ( d x. Q ) -> P e. ran V ) )' % A2), npv], 'mtod',
              '( %s -> -. E. d e. ran V ( P x. Q ) = ( d x. Q ) )' % A2)
    me = w.s([w.s([w.s([qn, pq], 'jca', '( %s -> ( Q e. NN0 /\\ ( P x. Q ) e. NN0 ) )' % A2), vs], 'jca',
                  '( %s -> ( ( Q e. NN0 /\\ ( P x. Q ) e. NN0 ) /\\ V e. Word NN0 ) )' % A2), w.inst('mulallel')], 'syl',
             '( %s -> ( ( P x. Q ) e. ran %s <-> E. d e. ran V ( P x. Q ) = ( d x. Q ) ) )' % (A2, MA))
    nin = w.s([me, ctr], 'mtbird', '( %s -> -. ( P x. Q ) e. ran %s )' % (A2, MA))
    fmc = w.s([w.s([pq, a1, w.inst('algndpcs')], 'syl2anc', "( %s -> ( Fun `' %s <-> ( -. ( P x. Q ) e. ran %s /\\ Fun `' %s ) ) )" % (A2, MC, MA, MA)),
               w.s([nin, ihs], 'jca', "( %s -> ( -. ( P x. Q ) e. ran %s /\\ Fun `' %s ) )" % (A2, MA, MA))], 'mpbird',
              "( %s -> Fun `' %s )" % (A2, MC))
    bi = w.s([w.s([p1], 'cnveqd', "( %s -> `' ( 1st ` ( Q MulAll %s ) ) = `' %s )" % (A2, CSV, MC))], 'funeqd',
             "( %s -> ( Fun `' ( 1st ` ( Q MulAll %s ) ) <-> Fun `' %s ) )" % (A2, CSV, MC))
    w.qed([w.s([bi, fmc], 'mpbird', "( %s -> Fun `' ( 1st ` ( Q MulAll %s ) ) )" % (A2, CSV))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = "( ( Q e. NN /\\ S e. Word NN0 ) /\\ Fun `' S )"
    w.qed([w.s([w.s([], 'simplr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([w.s([], 'simpll', '( %s -> Q e. NN )' % T), w.s([], 'simpr', "( %s -> Fun `' S )" % T)], 'jca',
               "( %s -> ( Q e. NN /\\ Fun `' S ) )" % T)], 'mpd', "( %s -> Fun `' ( 1st ` ( Q MulAll S ) ) )" % T)
family(run, 'mulallndp', PHI, _b, _s, finish=_f, desc='The mulAll image of a duplicate-free word has no repeats (Lean: List.Nodup.map).')
