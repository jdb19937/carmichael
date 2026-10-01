"""Sortie A5, batch 12: the pointwise core at a tuple of scales, with the ten
intermediates of the algorithm supplied (Lean: search_successW_of at sc).
MM_DB=sorties/a5.mm python3 tools/gen/a5_pwv.py [LABEL...]"""
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

GW = '( ( Z goodPrimesW W ) ` Y )'
PW = '( ( log ` N ) ^c ( 6 / 5 ) )'
RES = '( ( Z Reservoir W ) ` Y )'
R1 = '( 1st ` %s )' % RES
LR = '( # ` %s )' % R1
QT = '( %s substr <. ( %s - T ) , %s >. )' % (R1, LR, LR)
RNG = '( 0 ..^ ( # ` %s ) )' % QT
AT = 'prod_ o e. %s ( %s ` o )' % (RNG, QT)
ATI = 'prod_ i e. %s ( %s ` i )' % (RNG, QT)
X5 = '( %s ^ 5 )' % AT
SCN = '( ( ( ( ( %s Scan %s ) ` Z ) ` H ) ` 1 ) ` %s )' % (QT, X5, X5)
PT = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % SCN
XT = '( ( %s Extract N ) ` %s )' % (AT, PT)
MT = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % XT
ST = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % XT
UT = '( %s Verify %s )' % (MT, ST)
SC = '<. <. <. Z , W >. , <. Y , T >. >. , H >.'
SR = '( %s Search N )' % SC
VSR = '( V Search N )'
def PRD(s, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, s, s, i)
CARM = lambda m: '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (m, m, m, m)
EXPB = '( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) )'
def CONCL(sr):
    mmr = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % sr
    ssr = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % sr
    return ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
            '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
            '( %s = %s /\\ %s /\\ ( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) ) ) /\\ '
            '( 2nd ` %s ) <_ %s )'
            % (sr, ssr, ssr, ssr, mmr, PRD(ssr), CARM(mmr), mmr, mmr, sr, EXPB))
EXTRB = a5lib.winbody('extrwinputs')
OUTB = a5lib.winbody('outwcarm')
COSTB = a5lib.winbody('costpiecesle')
S3B = a5lib.subvars(a5lib.winbody('step3w'), {'G': '; 1 6'})

w = WH('a5pwv', 'The search at a tuple of scales in the window returns a certified Carmichael number within the budget (Lean: search_successW_of at one scale tuple).')
h1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
h2 = w.h('( T e. NN0 /\\ H e. NN0 )')
h3 = w.h('N e. ( ZZ>= ` 3 )')
h4 = w.h('V = %s' % SC)
h5 = w.h('T <_ ( # ` %s )' % GW)
h6 = w.h('( %s <_ H /\\ H <_ ( ; 1 6 x. %s ) )' % (PW, PW))
h7 = w.h(S3B)
h8 = w.h(EXTRB)
h9 = w.h(OUTB)
h10 = w.h(COSTB)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
eqd = lambda t: w.s([], 'eqidd', '( ph -> %s = %s )' % (t, t))
_fv = w.s([], 'fveq2', '( o = i -> ( %s ` o ) = ( %s ` i ) )' % (QT, QT))
_cbv = w.s([_fv], 'cbvprodv', '%s = %s' % (AT, ATI))
aeq = w.s([_cbv], 'a1i', '( ph -> %s = %s )' % (AT, ATI))
core = w.s([h1, h2, h3, eqd(RES), eqd(LR), eqd(QT), aeq, eqd(SCN), eqd(PT), eqd(XT), eqd(UT),
            h5, h6, h7, h8, h9, h10], 'a5pw', '( ph -> %s )' % CONCL(SR))
seq = w.s([st([h4], 'eqcomd', '%s = V' % SC)], 'oveq1d', '( ph -> %s = %s )' % (SR, VSR))
bi, new = a5lib.ccongr(w, 'ph', CONCL(SR), [(SR, VSR, seq)])
assert ' '.join(new.split()) == ' '.join(CONCL(VSR).split()), new
w.qed([core, bi], 'mpbid', '( ph -> %s )' % CONCL(VSR))
run(w)
