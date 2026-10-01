"""Sortie A5, batch 7: step 5 of the assembly, the output certificate and the
verification (Lean: SearchAlg.lean lines 191-215).
MM_DB=sorties/a5.mm python3 tools/gen/a5_o.py [LABEL...]"""
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

PI = 'prod_ i e. ( 0 ..^ ( # ` S ) ) ( S ` i )'
PQ = 'prod_ q e. ran S q'
PJ = 'prod_ j e. ran S j'
LQ = '( Lmod ` ran Q )'
POOL = '( ( ran Q pool Z ) ` K )'
CARM = lambda m: '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (m, m, m, m)
OUT = lambda m: ('( ( ran S C_ Prime /\\ 3 <_ ( # ` ran S ) ) /\\ %s /\\ %s <_ ( N ^c ( 1 + D ) ) )'
                 % (CARM(m), m))

w = WH('a5o', 'The output of the extraction is a Carmichael number that the verifier accepts (Lean: output_carmichaelW and verify_spec applied in SearchAlg.lean).')
h1 = w.h('( ran Q e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ K e. NN )')
h2 = w.h('( K gcd %s ) = 1' % LQ)
h3 = w.h('( S e. Word NN0 /\\ Fun `\' S )')
h4 = w.h('ran S C_ %s' % POOL)
h5 = w.h('M = %s' % PI)
h6 = w.h('%s || ( M - 1 )' % LQ)
h7 = w.h(OUT(PJ))
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)

swrd = st([h3], 'simpld', 'S e. Word NN0')
sfun = st([h3], 'simprd', 'Fun `\' S')
# M = prod over the range
rnp = st([st([swrd, sfun], 'jca', '( S e. Word NN0 /\\ Fun `\' S )'), w.inst('algprodrn')], 'syl',
         '%s = %s' % (PI, PQ))
cbv = w.s([w.s([], 'cbvprodv', '%s = %s' % (PQ, PJ))], 'a1i', '( ph -> %s = %s )' % (PQ, PJ))
mj = st([st([h5, rnp], 'eqtrd', 'M = %s' % PQ), cbv], 'eqtrd', 'M = %s' % PJ)
jm = st([mj], 'eqcomd', '%s = M' % PJ)
# transfer the certificate to M
oss = st([st([h7], 'simp1d', '( ran S C_ Prime /\\ 3 <_ ( # ` ran S ) )')], 'simpld', 'ran S C_ Prime')
ocd = st([st([h7], 'simp1d', '( ran S C_ Prime /\\ 3 <_ ( # ` ran S ) )')], 'simprd', '3 <_ ( # ` ran S )')
ocm = st([h7], 'simp2d', CARM(PJ))
oub = st([h7], 'simp3d', '%s <_ ( N ^c ( 1 + D ) )' % PJ)
_idm = w.s([], 'id', '( %s = M -> %s = M )' % (PJ, PJ))
_cl, _c = w.wcongr(CARM(PJ), {}, '%s = M' % PJ, {}, rules={PJ: ('M', _idm)})
assert ' '.join(_c.split()) == ' '.join(CARM('M').split()), _c
carmbi = st([jm, _cl], 'syl', '( %s <-> %s )' % (CARM(PJ), CARM('M')))
mcarm = st([ocm, carmbi], 'mpbid', CARM('M'))
mub = st([jm, oub], 'eqbrtrrd', 'M <_ ( N ^c ( 1 + D ) )')
# the word form of the two counting facts
sprm = w.s([w.s([oss], 'adantr', '( ( ph /\\ b e. ran S ) -> ran S C_ Prime )'),
            w.s([], 'simpr', '( ( ph /\\ b e. ran S ) -> b e. ran S )')], 'sseldd',
           '( ( ph /\\ b e. ran S ) -> b e. Prime )')
allprm = w.s([sprm], 'ralrimiva', '( ph -> A. b e. ran S b e. Prime )')
scard = st([st([swrd, sfun], 'jca', '( S e. Word NN0 /\\ Fun `\' S )'), w.inst('algwrdcard')], 'syl',
           '( # ` ran S ) = ( # ` S )')
s3 = st([ocd, scard], 'breqtrd', '3 <_ ( # ` S )')
# Korselt's divisibility from outwkors
rnv = st([swrd, w.inst('rnexg')], 'syl', 'ran S e. _V')
spw = st([st([rnv, w.inst('elpwg')], 'syl', '( ran S e. ~P %s <-> ran S C_ %s )' % (POOL, POOL)), h4],
         'mpbird', 'ran S e. ~P %s' % POOL)
mdvd = st([h6, w.s([mj], 'oveq1d', '( ph -> ( M - 1 ) = ( %s - 1 ) )' % PJ)], 'breqtrd',
          '%s || ( %s - 1 )' % (LQ, PJ))
kors = st([st([st([st([h1, h2], 'jca',
                      '( ( ran Q e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ K e. NN ) /\\ ( K gcd %s ) = 1 )' % LQ), spw], 'jca',
                  '( ( ( ran Q e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ K e. NN ) /\\ ( K gcd %s ) = 1 ) /\\ ran S e. ~P %s )' % (LQ, POOL)), mdvd], 'jca',
               '( ( ( ( ran Q e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ K e. NN ) /\\ ( K gcd %s ) = 1 ) /\\ ran S e. ~P %s ) /\\ %s || ( %s - 1 ) )' % (LQ, POOL, LQ, PJ)),
           w.inst('outwkors')], 'syl',
          'A. b e. Prime ( b || %s -> ( b - 1 ) || ( %s - 1 ) )' % (PJ, PJ))
# every element of the output word satisfies Korselt's divisibility
AN = '( ph /\\ b e. ran S )'
sub = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (AN, f))
pdvd = sub([w.s([swrd], 'adantr', '( %s -> S e. Word NN0 )' % AN),
            w.s([], 'simpr', '( %s -> b e. ran S )' % AN), w.inst('algdvdprod')], 'syl2anc', 'b || %s' % PI)
pdvj = sub([pdvd, w.s([st([rnp, cbv], 'eqtrd', '%s = %s' % (PI, PJ))], 'adantr',
                      '( %s -> %s = %s )' % (AN, PI, PJ))], 'breqtrd', 'b || %s' % PJ)
pimp = sub([w.s([kors], 'adantr', '( %s -> A. b e. Prime ( b || %s -> ( b - 1 ) || ( %s - 1 ) ) )' % (AN, PJ, PJ)),
            sprm, w.inst('rspa')], 'syl2anc', '( b || %s -> ( b - 1 ) || ( %s - 1 ) )' % (PJ, PJ))
pkor = sub([pdvj, pimp], 'mpd', '( b - 1 ) || ( %s - 1 )' % PJ)
pkorm = sub([pkor, w.s([w.s([jm], 'oveq1d', '( ph -> ( %s - 1 ) = ( M - 1 ) )' % PJ)], 'adantr',
                       '( %s -> ( %s - 1 ) = ( M - 1 ) )' % (AN, PJ))], 'breqtrd', '( b - 1 ) || ( M - 1 )')
allkor = w.s([pkorm], 'ralrimiva', '( ph -> A. b e. ran S ( b - 1 ) || ( M - 1 ) )')
# the verifier accepts
mn0 = st([h5, st([swrd, w.inst('algprodcl')], 'syl', '%s e. NN0' % PI)], 'eqeltrd', 'M e. NN0')
ver = st([st([st([mn0, swrd], 'jca', '( M e. NN0 /\\ S e. Word NN0 )'),
              st([sfun, allprm, s3], '3jca', '( Fun `\' S /\\ A. b e. ran S b e. Prime /\\ 3 <_ ( # ` S ) )'),
              st([h5, allkor], 'jca', '( M = %s /\\ A. b e. ran S ( b - 1 ) || ( M - 1 ) )' % PI)], '3jca',
             '( ( M e. NN0 /\\ S e. Word NN0 ) /\\ ( Fun `\' S /\\ A. b e. ran S b e. Prime /\\ 3 <_ ( # ` S ) ) /\\ ( M = %s /\\ A. b e. ran S ( b - 1 ) || ( M - 1 ) ) )' % PI),
           w.inst('verifyspec')], 'syl', '( 1st ` ( M Verify S ) ) = 1o')
w.qed([st([allprm, s3], 'jca', '( A. b e. ran S b e. Prime /\\ 3 <_ ( # ` S ) )'),
       st([mcarm, mub], 'jca', '( %s /\\ M <_ ( N ^c ( 1 + D ) ) )' % CARM('M')),
       ver], '3jca',
      '( ph -> ( ( A. b e. ran S b e. Prime /\\ 3 <_ ( # ` S ) ) /\\ ( %s /\\ M <_ ( N ^c ( 1 + D ) ) ) /\\ ( 1st ` ( M Verify S ) ) = 1o ) )'
      % CARM('M'))
run(w)
