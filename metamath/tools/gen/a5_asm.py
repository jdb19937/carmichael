"""Sortie A5, batch 14: the headline, search_successW (Lean: SearchAlg.lean).
MM_DB=sorties/a5.mm python3 tools/gen/a5_asm.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a5lib
from tm import *
from a2lib import WH, EV, evand
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

KEEP = {'n': 'n'}
S2Q = a5lib.winquant('step2w', KEEP)
S3Q = a5lib.subvars(a5lib.winquant('step3w', KEEP), {'G': '; 1 6'})
EIQ = a5lib.winquant('extrwinputs', KEEP)
OCQ = a5lib.subvars(a5lib.winquant('outwcarm', KEEP), {'D': 'A'})
CPQ = a5lib.winquant('costpiecesle', KEEP)
AGP3 = a5lib.dbhyps('step2w')[9]
AGP31 = a5lib.subvars(a5lib.dbhyps('step3w')[8], {'X': 'F'})
assert AGP3.startswith('( ph -> ') and AGP31.startswith('( ph -> ')
AGP3 = AGP3[len('( ph -> '):-2].strip()
AGP31 = AGP31[len('( ph -> '):-2].strip()

ZP = '( 1st ` ( 1st ` ( 1st ` v ) ) )'
IWV = '<. <. C , E >. , n >. InWindow ( 1st ` v )'
PWN = '( ( log ` n ) ^c ( 6 / 5 ) )'
HP = '( 2nd ` v )'
TH = '( %s <_ %s /\\ %s <_ ( ; 1 6 x. %s ) )' % (PWN, HP, HP, PWN)
VSR = '( v Search n )'
MMR = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % VSR
SSR = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % VSR
def PRD(s, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, s, s, i)
CARM = lambda m: '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (m, m, m, m)
EXPB = '( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` n ) ) x. ( ell3 ` n ) ) )'
CONCL = ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
         '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
         '( %s = %s /\\ %s /\\ ( n < %s /\\ %s <_ ( n ^c ( 1 + A ) ) ) ) ) /\\ '
         '( 2nd ` %s ) <_ %s )'
         % (VSR, SSR, SSR, SSR, MMR, PRD(SSR), CARM(MMR), MMR, MMR, VSR, EXPB))
GOAL = 'A. v e. Scales ( ( %s /\\ %s ) -> %s )' % (IWV, TH, CONCL)
BTX = ['n e. ( ZZ>= ` 3 )', S2Q, S3Q, EIQ, OCQ, CPQ]

w = WH('searchw', 'The search of the paper outputs a certified Carmichael number in ( n , n ^ ( 1 + A ) ] within the operation budget, at every tuple of scales in the window, for all large n, given AGP Theorem 3 and AGP Theorem 3.1 (Lean: search_successW_of of SearchAlg.lean).')
hC = w.h('C e. RR')
hC1 = w.h('; ; ; 1 0 0 0 <_ C')
hE = w.h('E e. RR')
hE0 = w.h('0 < E')
hE2 = w.h('E <_ ( 1 / 2 )')
hG = w.h('G e. RR')
hG0 = w.h('0 < G')
h60 = w.h('; 6 0 <_ ( C x. G )')
hX = w.h('X e. NN0')
hA3 = w.h(AGP3)
hD = w.h('D e. RR')
hF = w.h('F e. NN0')
hA31 = w.h(AGP31)
hA = w.h('A e. RR')
hA0 = w.h('0 < A')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
i16 = w.s([num.fact(w, '; 1 6', 'RR')], 'a1i', '( ph -> ; 1 6 e. RR )')
e1 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( ph -> %s )' % EV('n e. ( ZZ>= ` 3 )'))
e2 = w.s([hC, hG, hE, hX, hE0, hE2, hG0, h60, hC1, hA3], 'step2w', '( ph -> %s )' % EV(S2Q))
e3 = w.s([hC, hD, hE, hF, i16, hE0, hE2, hC1, hA31], 'step3w', '( ph -> %s )' % EV(S3Q))
e4 = w.s([hC, hC1, hE, hE0, hE2], 'extrwinputs', '( ph -> %s )' % EV(EIQ))
e5 = w.s([hC, hC1, hE, hE0, hE2, hA, hA0], 'outwcarm', '( ph -> %s )' % EV(OCQ))
e6 = w.s([st([st([hC, hC1], 'jca', '( C e. RR /\\ ; ; ; 1 0 0 0 <_ C )'),
              st([hE, hE0], 'jca', '( E e. RR /\\ 0 < E )')], 'jca',
             '( ( C e. RR /\\ ; ; ; 1 0 0 0 <_ C ) /\\ ( E e. RR /\\ 0 < E ) )'),
          w.inst('costpiecesle')], 'syl', '( ph -> %s )' % EV(CPQ))
bun, BUN = evand(w, 'ph', [e1, e2, e3, e4, e5, e6], BTX)
assert ' '.join(BUN.split()) == ' '.join(a5lib.bundletext(BTX).split()), BUN
D0 = '( ph /\\ %s )' % BUN
bstep = w.s([], 'simpr', '( %s -> %s )' % (D0, BUN))
parts = a5lib.unbundle(w, D0, bstep, BTX)
pw = w.s(parts, 'a5wi', '( %s -> %s )' % (D0, GOAL))
w.qed([bun, pw], 'evimd', '( ph -> %s )' % EV(GOAL))
run(w)
