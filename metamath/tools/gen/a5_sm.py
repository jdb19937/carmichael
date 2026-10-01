"""Sortie A5, batch 16: the smooth-shifted density transfers to a smaller
exponent (Lean: smooth_shifted_of_le of SearchAlg.lean).
MM_DB=sorties/a5.mm python3 tools/gen/a5_sm.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a5lib
from tm import *
from lin import linarith
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

def INNER(v, t): return 'A. q e. Prime ( q || ( a - 1 ) -> q <_ ( %s ^c ( 1 - %s ) ) )' % (v, t)
def BODY(v, t): return '( a e. Prime /\\ %s )' % INNER(v, t)
def SET(v, t): return '{ a e. ( 0 ... %s ) | %s }' % (v, BODY(v, t))
def DENS(t): return 'A. x e. ( ZZ>= ` X ) ( G x. ( ppi ` x ) ) <_ ( # ` %s )' % SET('x', t)

# --------------------------------------------------------------- smshss
w = W('smshss', 'The smooth-shifted primes below a smaller exponent form a larger set.')
P = '( ( E e. RR /\\ B e. RR /\\ E <_ B ) /\\ V e. NN )'
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (P, f))
lit = lambda t, k: w.s([num.fact(w, t, k)], 'a1i', '( %s -> %s e. %s )' % (P, t, k))
tri = st([], 'simpl', '( E e. RR /\\ B e. RR /\\ E <_ B )')
ere = st([tri], 'simp1d', 'E e. RR')
bre = st([tri], 'simp2d', 'B e. RR')
eb = st([tri], 'simp3d', 'E <_ B')
vnn = st([], 'simpr', 'V e. NN')
vre = st([vnn], 'nnred', 'V e. RR')
v1 = st([vnn], 'nnge1d', '1 <_ V')
v0 = st([st([vnn], 'nngt0d', '0 < V')], 'ltled', '0 <_ V')
omb = st([lit('1', 'RR'), bre], 'resubcld', '( 1 - B ) e. RR')
ome = st([lit('1', 'RR'), ere], 'resubcld', '( 1 - E ) e. RR')
lele = linarith(w, P, [eb], '( 1 - B ) <_ ( 1 - E )', leaves={'E': ('RR', ere), 'B': ('RR', bre)})
mono = w.s([vre, v1, omb, ome, lele], 'cxplead',
           '( %s -> ( V ^c ( 1 - B ) ) <_ ( V ^c ( 1 - E ) ) )' % P)
xbre = st([vre, v0, omb], 'recxpcld', '( V ^c ( 1 - B ) ) e. RR')
xere = st([vre, v0, ome], 'recxpcld', '( V ^c ( 1 - E ) ) e. RR')
AN = '( %s /\\ a e. ( 0 ... V ) )' % P
AQ = '( %s /\\ q e. Prime )' % AN
AQB = '( %s /\\ q <_ ( V ^c ( 1 - B ) ) )' % AQ
lift2 = lambda s, f: w.s([w.s([s], 'adantr', '( %s -> %s )' % (AN, f))], 'adantr', '( %s -> %s )' % (AQ, f))
lift3 = lambda s, f: w.s([lift2(s, f)], 'adantr', '( %s -> %s )' % (AQB, f))
qre = w.s([w.s([w.s([], 'simpr', '( %s -> q e. Prime )' % AQ), w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % AQ)],
          'nnred', '( %s -> q e. RR )' % AQ)
tr2 = w.s([w.s([qre], 'adantr', '( %s -> q e. RR )' % AQB),
           lift3(xbre, '( V ^c ( 1 - B ) ) e. RR'), lift3(xere, '( V ^c ( 1 - E ) ) e. RR'),
           w.s([], 'simpr', '( %s -> q <_ ( V ^c ( 1 - B ) ) )' % AQB),
           lift3(mono, '( V ^c ( 1 - B ) ) <_ ( V ^c ( 1 - E ) )')], 'letrd',
          '( %s -> q <_ ( V ^c ( 1 - E ) ) )' % AQB)
qimp = w.s([tr2], 'ex', '( %s -> ( q <_ ( V ^c ( 1 - B ) ) -> q <_ ( V ^c ( 1 - E ) ) ) )' % AQ)
qimp2 = w.s([qimp], 'imim2d',
            '( %s -> ( ( q || ( a - 1 ) -> q <_ ( V ^c ( 1 - B ) ) ) -> ( q || ( a - 1 ) -> q <_ ( V ^c ( 1 - E ) ) ) ) )' % AQ)
rall = w.s([qimp2], 'ralimdva', '( %s -> ( %s -> %s ) )' % (AN, INNER('V', 'B'), INNER('V', 'E')))
bimp = w.s([rall], 'anim2d', '( %s -> ( %s -> %s ) )' % (AN, BODY('V', 'B'), BODY('V', 'E')))
w.qed([bimp], 'ss2rabdv', '( %s -> %s C_ %s )' % (P, SET('V', 'B'), SET('V', 'E')))
run(w)

# --------------------------------------------------------------- smshle
w = W('smshle', 'The smooth-shifted density at one exponent gives it at every smaller exponent (Lean: smooth_shifted_of_le of SearchAlg.lean).')
H0 = '( ( X e. NN /\\ G e. RR ) /\\ ( E e. RR /\\ B e. RR /\\ E <_ B ) )'
P = '( ( X e. NN /\\ G e. RR ) /\\ ( E e. RR /\\ B e. RR /\\ E <_ B ) /\\ %s )' % DENS('B')
hst = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (H0, f))
pair = hst([], 'simpl', '( X e. NN /\\ G e. RR )')
xnn = hst([pair], 'simpld', 'X e. NN')
gre = hst([pair], 'simprd', 'G e. RR')
tri = hst([], 'simpr', '( E e. RR /\\ B e. RR /\\ E <_ B )')
AX = '( %s /\\ x e. ( ZZ>= ` X ) )' % H0
xst = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (AX, f))
xnn2 = xst([w.s([xnn], 'adantr', '( %s -> X e. NN )' % AX),
            w.s([], 'simpr', '( %s -> x e. ( ZZ>= ` X ) )' % AX), w.inst('eluznn')], 'syl2anc', 'x e. NN')
ss = xst([xst([w.s([tri], 'adantr', '( %s -> ( E e. RR /\\ B e. RR /\\ E <_ B ) )' % AX), xnn2], 'jca',
              '( ( E e. RR /\\ B e. RR /\\ E <_ B ) /\\ x e. NN )'), w.inst('smshss')], 'syl',
         '%s C_ %s' % (SET('x', 'B'), SET('x', 'E')))
fzf = w.s([w.s([], 'fzfi', '( 0 ... x ) e. Fin')], 'a1i', '( %s -> ( 0 ... x ) e. Fin )' % AX)
finE = xst([fzf, w.inst('rabfi')], 'syl', '%s e. Fin' % SET('x', 'E'))
finB = xst([fzf, w.inst('rabfi')], 'syl', '%s e. Fin' % SET('x', 'B'))
hle = xst([finE, ss, w.inst('hashssle')], 'syl2anc', '( # ` %s ) <_ ( # ` %s )' % (SET('x', 'B'), SET('x', 'E')))
gpre = xst([w.s([gre], 'adantr', '( %s -> G e. RR )' % AX),
            xst([xst([xst([xnn2], 'nnred', 'x e. RR'), w.inst('ppicl')], 'syl', '( ppi ` x ) e. NN0')],
                'nn0red', '( ppi ` x ) e. RR')], 'remulcld', '( G x. ( ppi ` x ) ) e. RR')
hbre = xst([xst([finB, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SET('x', 'B'))], 'nn0red',
           '( # ` %s ) e. RR' % SET('x', 'B'))
here = xst([xst([finE, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SET('x', 'E'))], 'nn0red',
           '( # ` %s ) e. RR' % SET('x', 'E'))
AXB = '( %s /\\ ( G x. ( ppi ` x ) ) <_ ( # ` %s ) )' % (AX, SET('x', 'B'))
lift = lambda s, f: w.s([s], 'adantr', '( %s -> %s )' % (AXB, f))
tr = w.s([lift(gpre, '( G x. ( ppi ` x ) ) e. RR'), lift(hbre, '( # ` %s ) e. RR' % SET('x', 'B')),
          lift(here, '( # ` %s ) e. RR' % SET('x', 'E')),
          w.s([], 'simpr', '( %s -> ( G x. ( ppi ` x ) ) <_ ( # ` %s ) )' % (AXB, SET('x', 'B'))),
          lift(hle, '( # ` %s ) <_ ( # ` %s )' % (SET('x', 'B'), SET('x', 'E')))], 'letrd',
         '( %s -> ( G x. ( ppi ` x ) ) <_ ( # ` %s ) )' % (AXB, SET('x', 'E')))
imp = w.s([tr], 'ex', '( %s -> ( ( G x. ( ppi ` x ) ) <_ ( # ` %s ) -> ( G x. ( ppi ` x ) ) <_ ( # ` %s ) ) )'
           % (AX, SET('x', 'B'), SET('x', 'E')))
rall = w.s([imp], 'ralimdva', '( %s -> ( %s -> %s ) )' % (H0, DENS('B'), DENS('E')))
h0p = w.s([w.s([], 'simp1', '( %s -> ( X e. NN /\\ G e. RR ) )' % P),
           w.s([], 'simp2', '( %s -> ( E e. RR /\\ B e. RR /\\ E <_ B ) )' % P)], 'jca', '( %s -> %s )' % (P, H0))
w.qed([w.s([], 'simp3', '( %s -> %s )' % (P, DENS('B'))),
       w.s([h0p, rall], 'syl', '( %s -> ( %s -> %s ) )' % (P, DENS('B'), DENS('E')))], 'mpd',
      '( %s -> %s )' % (P, DENS('E')))
run(w)
