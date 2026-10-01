"""Sortie A5, batch 6: step 4 of the assembly, the extraction (Lean:
SearchAlg.lean lines 171-190).
MM_DB=sorties/a5.mm python3 tools/gen/a5_x.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from tm import *
from a2lib import WH
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

X5 = '( A ^ 5 )'
EX = '( ( A Extract N ) ` P )'
ME = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % EX
SE = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % EX
MX = '( 1st ` ( 2nd ` ( 1st ` X ) ) )'
SX = '( 2nd ` ( 2nd ` ( 1st ` X ) ) )'
VEBK = ('A. u e. ~P ran P ( ( # ` u ) = B -> E. s e. ~P u ( s =/= (/) /\\ '
        'A || ( prod_ j e. s j - 1 ) ) )')
def PRD(S, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, S, S, i)
XCOST = '( ( ( # ` P ) x. ( A + 3 ) ) + 1 )'

w = WH('a5x', 'The extraction returns a number above N with its prime factorization from the pool (Lean: extract_spec and extract_cost applied in SearchAlg.lean).')
h1 = w.h('( A e. NN /\\ 2 <_ A )')
h2 = w.h('( N e. NN0 /\\ 1 <_ N )')
h3 = w.h('( %s e. NN0 /\\ B e. NN /\\ P e. Word NN0 )' % X5)
h4 = w.h('Fun `\' P')
h5 = w.h('A. p e. ran P ( 2 <_ p /\\ p <_ %s )' % X5)
h6 = w.h(VEBK)
h7 = w.h('( ( ( ( A + 1 ) Nlog N ) + 1 ) x. B ) <_ ( # ` P )')
h8 = w.h('X = %s' % EX)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)

ann = st([h1], 'simpld', 'A e. NN')
nn0 = st([h2], 'simpld', 'N e. NN0')
pw = st([h3], 'simp3d', 'P e. Word NN0')
ANT = ('( ( ( A e. NN /\\ 2 <_ A ) /\\ ( N e. NN0 /\\ 1 <_ N ) /\\ ( %s e. NN0 /\\ B e. NN /\\ P e. Word NN0 ) ) /\\ '
       '( Fun `\' P /\\ A. p e. ran P ( 2 <_ p /\\ p <_ %s ) ) /\\ ( %s /\\ ( ( ( ( A + 1 ) Nlog N ) + 1 ) x. B ) <_ ( # ` P ) ) )'
       % (X5, X5, VEBK))
ant = st([st([h1, h2, h3], '3jca',
             '( ( A e. NN /\\ 2 <_ A ) /\\ ( N e. NN0 /\\ 1 <_ N ) /\\ ( %s e. NN0 /\\ B e. NN /\\ P e. Word NN0 ) )' % X5),
          st([h4, h5], 'jca', '( Fun `\' P /\\ A. p e. ran P ( 2 <_ p /\\ p <_ %s ) )' % X5),
          st([h6, h7], 'jca', '( %s /\\ ( ( ( ( A + 1 ) Nlog N ) + 1 ) x. B ) <_ ( # ` P ) )' % VEBK)],
         '3jca', ANT)
SPEC = ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ ( Fun `\' %s /\\ ran %s C_ ran P /\\ %s = %s ) /\\ '
        '( A || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( %s ^ B ) ) ) )'
        % (EX, SE, SE, PRD(SE), ME, ME, ME, ME, X5))
spec = st([ant, w.inst('extspec')], 'syl', SPEC)
ene = st([spec], 'simp1d', '( 1st ` %s ) =/= ( inr ` (/) )' % EX)
etri = st([spec], 'simp2d', '( Fun `\' %s /\\ ran %s C_ ran P /\\ %s = %s )' % (SE, SE, PRD(SE), ME))
efun = st([etri], 'simp1d', 'Fun `\' %s' % SE)
ess = st([etri], 'simp2d', 'ran %s C_ ran P' % SE)
eprd = st([etri], 'simp3d', '%s = %s' % (PRD(SE), ME))
ebnd = st([spec], 'simp3d', '( A || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( %s ^ B ) ) )' % (ME, ME, ME, X5))
edvd = st([ebnd], 'simp1d', 'A || ( %s - 1 )' % ME)
elt = st([ebnd], 'simp2d', 'N < %s' % ME)
eub = st([ebnd], 'simp3d', '%s <_ ( N x. ( %s ^ B ) )' % (ME, X5))
cst = st([st([st([ann, nn0], 'jca', '( A e. NN /\\ N e. NN0 )'), pw], 'jca',
             '( ( A e. NN /\\ N e. NN0 ) /\\ P e. Word NN0 )'), w.inst('extcost')], 'syl',
         '( 2nd ` %s ) <_ %s' % (EX, XCOST))
ecl = st([st([st([ann, nn0], 'jca', '( A e. NN /\\ N e. NN0 )'), pw], 'jca',
             '( ( A e. NN /\\ N e. NN0 ) /\\ P e. Word NN0 )'), w.inst('extractcl')], 'syl',
         '%s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )' % EX)
# transfer along X = EX
xeq = st([h8], 'eqcomd', '%s = X' % EX)
f1 = w.s([xeq], 'fveq2d', '( ph -> ( 1st ` %s ) = ( 1st ` X ) )' % EX)
f2 = w.s([f1], 'fveq2d', '( ph -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` X ) ) )' % EX)
mE = w.s([f2], 'fveq2d', '( ph -> %s = %s )' % (ME, MX))
sE = w.s([f2], 'fveq2d', '( ph -> %s = %s )' % (SE, SX))
c2 = w.s([xeq], 'fveq2d', '( ph -> ( 2nd ` %s ) = ( 2nd ` X ) )' % EX)
xne = st([f1, ene], 'eqnetrrd', '( 1st ` X ) =/= ( inr ` (/) )')
xfun = st([efun, w.s([w.s([sE], 'cnveqd', '( ph -> `\' %s = `\' %s )' % (SE, SX))], 'funeqd',
                     '( ph -> ( Fun `\' %s <-> Fun `\' %s ) )' % (SE, SX))], 'mpbid', 'Fun `\' %s' % SX)
xss = st([st([w.s([sE], 'rneqd', '( ph -> ran %s = ran %s )' % (SE, SX))], 'eqcomd', 'ran %s = ran %s' % (SX, SE)), ess], 'eqsstrd', 'ran %s C_ ran P' % SX)
prdeq, _new = w.congr(PRD(SE), {}, 'ph', {}, rules={SE: (SX, sE)})
assert ' '.join(_new.split()) == ' '.join(PRD(SX).split()), _new
xprd = st([st([prdeq], 'eqcomd', '%s = %s' % (PRD(SX), PRD(SE))), st([eprd, mE], 'eqtrd', '%s = %s' % (PRD(SE), MX))],
          'eqtrd', '%s = %s' % (PRD(SX), MX))
xdvd = st([edvd, w.s([mE], 'oveq1d', '( ph -> ( %s - 1 ) = ( %s - 1 ) )' % (ME, MX))], 'breqtrd', 'A || ( %s - 1 )' % MX)
xlt = st([elt, mE], 'breqtrd', 'N < %s' % MX)
xub = st([mE, eub], 'eqbrtrrd', '%s <_ ( N x. ( %s ^ B ) )' % (MX, X5))
xcl = st([h8, ecl], 'eqeltrd', 'X e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )')
pay = w.s([xcl, xne], 'a5pay', '( ph -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (MX, SX))
xcst = st([c2, cst], 'eqbrtrrd', '( 2nd ` X ) <_ %s' % XCOST)
w.qed([st([st([xne, pay], 'jca',
             '( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (MX, SX)),
           st([st([xfun, xss], 'jca', '( Fun `\' %s /\\ ran %s C_ ran P )' % (SX, SX)), xprd], 'jca',
              '( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s )' % (SX, SX, PRD(SX), MX))], 'jca',
          '( ( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) ) /\\ ( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s ) )'
          % (MX, SX, SX, SX, PRD(SX), MX)),
       st([st([st([xdvd, xlt], 'jca', '( A || ( %s - 1 ) /\\ N < %s )' % (MX, MX)), xub], 'jca',
              '( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ B ) ) )' % (MX, MX, MX, X5)), xcst], 'jca',
          '( ( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ B ) ) ) /\\ ( 2nd ` X ) <_ %s )'
          % (MX, MX, MX, X5, XCOST))], 'jca',
      '( ph -> ( ( ( ( 1st ` X ) =/= ( inr ` (/) ) /\\ ( %s e. NN0 /\\ %s e. Word NN0 ) ) /\\ ( ( Fun `\' %s /\\ ran %s C_ ran P ) /\\ %s = %s ) ) /\\ ( ( ( A || ( %s - 1 ) /\\ N < %s ) /\\ %s <_ ( N x. ( %s ^ B ) ) ) /\\ ( 2nd ` X ) <_ %s ) ) )'
      % (MX, SX, SX, SX, PRD(SX), MX, MX, MX, MX, X5, XCOST))
run(w)
