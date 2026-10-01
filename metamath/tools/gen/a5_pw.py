"""Sortie A5, batch 11: the pointwise core, with the accepted shift of step 3
eliminated (Lean: the obtain of k0 in search_successW_of).
MM_DB=sorties/a5.mm python3 tools/gen/a5_pw.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a5lib
from tm import *
from a2lib import WH
import num
import importlib.util as _iu
_spec = _iu.spec_from_file_location('a5pwkgen', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'a5_pwk.py'))

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

GW = '( ( Z goodPrimesW W ) ` Y )'
LQ = '( Lmod ` ran Q )'
XQ = '( xceil ` ran Q )'
PW = '( ( log ` N ) ^c ( 6 / 5 ) )'
X5 = '( A ^ 5 )'
PRDQ = 'prod_ i e. ( 0 ..^ ( # ` Q ) ) ( Q ` i )'
R1 = '( 1st ` R )'
SCN = '( ( ( ( ( Q Scan %s ) ` Z ) ` H ) ` 1 ) ` %s )' % (X5, X5)
PJ = '( 2nd ` ( 2nd ` ( 1st ` J ) ) )'
MX = '( 1st ` ( 2nd ` ( 1st ` X ) ) )'
SX = '( 2nd ` ( 2nd ` ( 1st ` X ) ) )'
POOL = lambda k: '( ( ran Q pool Z ) ` %s )' % k
SC = '<. <. <. Z , W >. , <. Y , T >. >. , H >.'
SR = '( %s Search N )' % SC
MMR = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % SR
SSR = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % SR
def PRD(s, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, s, s, i)
CARM = lambda m: '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (m, m, m, m)
EXPB = '( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) )'
CONCL = ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
         '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
         '( %s = %s /\\ %s /\\ ( N < %s /\\ %s <_ ( N ^c ( 1 + D ) ) ) ) ) /\\ '
         '( 2nd ` %s ) <_ %s )'
         % (SR, SSR, SSR, SSR, MMR, PRD(SSR), CARM(MMR), MMR, MMR, SR, EXPB))
EXTRB = a5lib.winbody('extrwinputs')
OUTB = a5lib.winbody('outwcarm')
COSTB = a5lib.winbody('costpiecesle')
S3B = a5lib.subvars(a5lib.winbody('step3w'), {'G': '; 1 6'})
KBODY = lambda k: ('( ( %s <_ ( %s ^c ( ; 7 9 / ; ; 1 0 0 ) ) /\\ ( %s gcd %s ) = 1 ) /\\ ( ; 1 6 x. %s ) <_ ( # ` %s ) )'
                   % (k, XQ, k, LQ, PW, POOL(k)))

w = WH('a5pw', 'The search succeeds at a tuple of scales in the window (Lean: the pointwise content of search_successW_of of SearchAlg.lean).')
h1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
h2 = w.h('( T e. NN0 /\\ H e. NN0 )')
h3 = w.h('N e. ( ZZ>= ` 3 )')
h4 = w.h('R = ( ( Z Reservoir W ) ` Y )')
h5 = w.h('I = ( # ` %s )' % R1)
h6 = w.h('Q = ( %s substr <. ( I - T ) , I >. )' % R1)
h7 = w.h('A = %s' % PRDQ)
h8 = w.h('J = %s' % SCN)
h9 = w.h('P = %s' % PJ)
h10 = w.h('X = ( ( A Extract N ) ` P )')
h11 = w.h('U = ( %s Verify %s )' % (MX, SX))
h12 = w.h('T <_ ( # ` %s )' % GW)
h13 = w.h('( %s <_ H /\\ H <_ ( ; 1 6 x. %s ) )' % (PW, PW))
h14 = w.h(S3B)
h15 = w.h(EXTRB)
h16 = w.h(OUTB)
h17 = w.h(COSTB)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
lit = lambda t, k: w.s([num.fact(w, t, k)], 'a1i', '( ph -> %s e. %s )' % (t, k))

tn0 = st([h2], 'simpld', 'T e. NN0')
ti = w.s([h1, h4, h5, h12], 'a5ti', '( ph -> T <_ I )')
QB = ('( ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) ) /\\ '
      '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) )' % GW)
qb = w.s([h1, tn0, h4, h5, h6, ti], 'a5q', '( ph -> %s )' % QB)
qb1 = st([qb], 'simpld', '( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) )')
qb2 = st([qb], 'simprd', '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % GW)
qcl = st([st([qb1], 'simpld', '( Q e. Word NN0 /\\ Fun `\' Q )')], 'simpld', 'Q e. Word NN0')
qcard = st([st([qb1], 'simprd', '( ( # ` Q ) = T /\\ ( # ` ran Q ) = T )')], 'simprd', '( # ` ran Q ) = T')
qss = st([st([qb2], 'simpld', '( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) )' % GW)], 'simpld', 'ran Q C_ %s' % GW)
rqv = st([qcl, w.inst('rnexg')], 'syl', 'ran Q e. _V')
rqpw = st([st([rqv, w.inst('elpwg')], 'syl', '( ran Q e. ~P %s <-> ran Q C_ %s )' % (GW, GW)), qss], 'mpbird',
          'ran Q e. ~P %s' % GW)
ex, EXT = a5lib.unwind(w, 'ph', h14, S3B,
                       [('q', 's', '~P %s' % GW, 'ran Q', rqpw), ('m', qcard)])
assert ' '.join(EXT.split()) == ' '.join(('E. k e. NN %s' % KBODY('k')).split()), EXT
# rename the existential variable to one the eventual antecedent does not bind
_id = w.s([], 'id', '( k = g -> k = g )')
_sl, _new = w.wcongr(KBODY('k'), {'k': 'g'}, 'k = g', {'k': _id})
assert ' '.join(_new.split()) == ' '.join(KBODY('g').split()), _new
bi = w.s([_sl], 'cbvrexvw', '( E. k e. NN %s <-> E. g e. NN %s )' % (KBODY('k'), KBODY('g')))
exg = st([ex, w.s([bi], 'a1i', '( ph -> ( E. k e. NN %s <-> E. g e. NN %s ) )' % (KBODY('k'), KBODY('g')))],
         'mpbid', 'E. g e. NN %s' % KBODY('g'))
# the core at the witness
PS = '( ( ph /\\ g e. NN ) /\\ %s )' % KBODY('g')
up = lambda s, f: w.s([s], 'ad2antrr', '( %s -> %s )' % (PS, f))
core = w.s([up(h1, '( Z e. NN /\\ W e. NN0 /\\ Y e. NN )'), up(h2, '( T e. NN0 /\\ H e. NN0 )'),
            up(h3, 'N e. ( ZZ>= ` 3 )'), up(h4, 'R = ( ( Z Reservoir W ) ` Y )'), up(h5, 'I = ( # ` %s )' % R1),
            up(h6, 'Q = ( %s substr <. ( I - T ) , I >. )' % R1), up(h7, 'A = %s' % PRDQ),
            up(h8, 'J = %s' % SCN), up(h9, 'P = %s' % PJ), up(h10, 'X = ( ( A Extract N ) ` P )'),
            up(h11, 'U = ( %s Verify %s )' % (MX, SX)), up(h12, 'T <_ ( # ` %s )' % GW),
            up(h13, '( %s <_ H /\\ H <_ ( ; 1 6 x. %s ) )' % (PW, PW)),
            w.s([], 'simplr', '( %s -> g e. NN )' % PS),
            w.s([], 'simpr', '( %s -> %s )' % (PS, KBODY('g'))),
            up(h15, EXTRB), up(h16, OUTB), up(h17, COSTB)], 'a5pwk', '( %s -> %s )' % (PS, CONCL))
imp = w.s([core], 'ex', '( ( ph /\\ g e. NN ) -> ( %s -> %s ) )' % (KBODY('g'), CONCL))
lim = w.s([imp], 'rexlimdva', '( ph -> ( E. g e. NN %s -> %s ) )' % (KBODY('g'), CONCL))
w.qed([exg, lim], 'mpd', '( ph -> %s )' % CONCL)
run(w)
