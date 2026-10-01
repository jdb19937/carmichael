"""Sortie A5, batch 13: the pointwise implication over every tuple of scales
(Lean: the intro sc of search_successW_of).
MM_DB=sorties/a5.mm python3 tools/gen/a5_wi.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a5lib
from tm import *
from a2lib import WH
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

ZP = '( 1st ` ( 1st ` ( 1st ` v ) ) )'
WP = '( 2nd ` ( 1st ` ( 1st ` v ) ) )'
YP = '( 1st ` ( 2nd ` ( 1st ` v ) ) )'
TP = '( 2nd ` ( 2nd ` ( 1st ` v ) ) )'
HP = '( 2nd ` v )'
TUP = '<. <. <. %s , %s >. , <. %s , %s >. >. , %s >.' % (ZP, WP, YP, TP, HP)
IWT = '<. <. C , E >. , N >. InWindow <. <. %s , %s >. , <. %s , %s >. >.' % (ZP, WP, YP, TP)
IWV = '<. <. C , E >. , N >. InWindow ( 1st ` v )'
PWN = '( ( log ` N ) ^c ( 6 / 5 ) )'
TH = '( %s <_ %s /\\ %s <_ ( ; 1 6 x. %s ) )' % (PWN, HP, HP, PWN)
VSR = '( v Search N )'
MMR = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % VSR
SSR = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % VSR
def PRD(s, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, s, s, i)
CARM = lambda m: '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (m, m, m, m)
EXPB = '( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) )'
CONCL = ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
         '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
         '( %s = %s /\\ %s /\\ ( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) ) ) /\\ '
         '( 2nd ` %s ) <_ %s )'
         % (VSR, SSR, SSR, SSR, MMR, PRD(SSR), CARM(MMR), MMR, MMR, VSR, EXPB))
GOAL = 'A. v e. Scales ( ( %s /\\ %s ) -> %s )' % (IWV, TH, CONCL)

S2Q = a5lib.winquant('step2w')
S3Q = a5lib.subvars(a5lib.winquant('step3w'), {'G': '; 1 6'})
EIQ = a5lib.winquant('extrwinputs')
OCQ = a5lib.winquant('outwcarm')
CPQ = a5lib.winquant('costpiecesle')
QUANTS = [('z', 'NN0'), ('w', 'NN0'), ('y', 'NN0'), ('t', 'NN0')]

w = WH('a5wi', 'At every tuple of scales in the window with a threshold in range, the search succeeds (Lean: search_successW_of after intro sc).')
h1 = w.h('N e. ( ZZ>= ` 3 )')
h2 = w.h(S2Q)
h3 = w.h(S3Q)
h4 = w.h(EIQ)
h5 = w.h(OCQ)
h6 = w.h(CPQ)
B1 = '( ph /\\ v e. Scales )'
B2 = '( %s /\\ ( %s /\\ %s ) )' % (B1, IWV, TH)
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (B2, f))
up = lambda s, f: w.s([s], 'ad2antrr', '( %s -> %s )' % (B2, f))
scv = w.s([w.s([], 'simpr', '( %s -> v e. Scales )' % B1)], 'adantr', '( %s -> v e. Scales )' % B2)
TUPT = ('( ( %s e. NN /\\ %s e. NN0 ) /\\ ( %s e. NN /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ v = %s ) )'
        % (ZP, WP, YP, TP, HP, TUP))
tup = st([scv, w.inst('scalestup')], 'syl', TUPT)
zw = st([tup], 'simp1d', '( %s e. NN /\\ %s e. NN0 )' % (ZP, WP))
yt = st([tup], 'simp2d', '( %s e. NN /\\ %s e. NN0 )' % (YP, TP))
hv = st([tup], 'simp3d', '( %s e. NN0 /\\ v = %s )' % (HP, TUP))
znn = st([zw], 'simpld', '%s e. NN' % ZP)
wn0 = st([zw], 'simprd', '%s e. NN0' % WP)
ynn = st([yt], 'simpld', '%s e. NN' % YP)
tn0 = st([yt], 'simprd', '%s e. NN0' % TP)
hn0 = st([hv], 'simpld', '%s e. NN0' % HP)
veq = st([hv], 'simprd', 'v = %s' % TUP)
zn0 = st([znn], 'nnnn0d', '%s e. NN0' % ZP)
yn0 = st([ynn], 'nnnn0d', '%s e. NN0' % YP)
iwv = w.s([w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (B2, IWV, TH))], 'simpld', '( %s -> %s )' % (B2, IWV))
th = w.s([w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (B2, IWV, TH))], 'simprd', '( %s -> %s )' % (B2, TH))
iwt = st([iwv, st([scv, w.inst('scalesiw')], 'syl',
                  '( 1st ` v ) = <. <. %s , %s >. , <. %s , %s >. >.' % (ZP, WP, YP, TP))], 'breqtrd', IWT)
VALS = [ZP, WP, YP, TP]
VST = [zn0, wn0, yn0, tn0]


def inst(hstep, text):
    acts = [('q', q, dom, val, vs) for (q, dom), val, vs in zip(QUANTS, VALS, VST)]
    acts.append(('m', iwt))
    return a5lib.unwind(w, B2, up(hstep, text), text, acts)


s2, S2 = inst(h2, S2Q)
s3, S3 = inst(h3, S3Q)
ei, EI = inst(h4, EIQ)
oc, OC = inst(h5, OCQ)
cp, CP = inst(h6, CPQ)
core = w.s([st([znn, wn0, ynn], '3jca', '( %s e. NN /\\ %s e. NN0 /\\ %s e. NN )' % (ZP, WP, YP)),
            st([tn0, hn0], 'jca', '( %s e. NN0 /\\ %s e. NN0 )' % (TP, HP)),
            up(h1, 'N e. ( ZZ>= ` 3 )'), veq, s2, th, s3, ei, oc, cp], 'a5pwv',
           '( %s -> %s )' % (B2, CONCL))
imp = w.s([core], 'ex', '( %s -> ( ( %s /\\ %s ) -> %s ) )' % (B1, IWV, TH, CONCL))
w.qed([imp], 'ralrimiva', '( ph -> %s )' % GOAL)
run(w)
