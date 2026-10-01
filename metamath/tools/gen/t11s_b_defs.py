"""T11 helper (scan): the texts of the scan loop at the machine (not a generator; imported by t11s_c_* ... t11s_f_*).

Letters as the frozen ~ tmiscfb : ` Q = W ` , ` x = F ` , ` z = Z ` , ` theta = O ` , ` k = G ` , ` fuel = H ` ,
` bq = C ` , ` b = B ` .  ` SC ` is the scan ` ( scan Q x z theta k fuel ) ` , ` NONE ` its failure, ` KF ` / ` PF ` the
returned ` k' ` and pool, ` R ` the iteration count (Lean's ` scanIters ` : ` fuel ` on a failure, ` k' - k + 1 ` on a
success), ` SJ( j ) ` the success flag of the family at ` j ` (` j = R ` on a success).
"""
SCf = lambda k, f: '( ( ( ( ( W Scan F ) ` Z ) ` O ) ` %s ) ` %s )' % (k, f)
SC = SCf('G', 'H')
SCO = '( 1st ` %s )' % SC
SC2 = '( 2nd ` %s )' % SC
NONE = '%s = ( inr ` (/) )' % SCO
SOMEne = '%s =/= ( inr ` (/) )' % SCO
KF = '( 1st ` ( 2nd ` %s ) )' % SCO
PFS = '( 2nd ` ( 2nd ` %s ) )' % SCO
RV = 'if ( %s , H , ( ( %s - G ) + 1 ) )' % (NONE, KF)
REQ = 'R = %s' % RV
SJ = lambda j: '( %s = R /\\ -. %s )' % (j, NONE)
GI = lambda j: '( G + %s )' % j
HI = lambda j: '( H - %s )' % j
Vf = lambda j: '( 2nd ` %s )' % SCf(GI(j), HI(j))
VN = lambda j: 'if ( %s , 0 , %s )' % (SJ(j), Vf(j))
PA = lambda k: '( ( ( W PoolAlg F ) ` Z ) ` %s )' % k
PA1 = lambda k: '( 1st ` %s )' % PA(k)
CPT = lambda k: '( W CoprimeTo %s )' % k
CPc = lambda k: '( 1st ` %s ) = 1o' % CPT(k)
LENk = lambda k: '( # ` %s )' % PA1(k)
OLE = lambda k: 'O <_ %s' % LENk(k)
SUC = lambda k: '( %s /\\ %s )' % (CPc(k), OLE(k))
ACP = lambda k: '( 2nd ` %s )' % CPT(k)
CPA = lambda k: '( 2nd ` %s )' % PA(k)
I1 = '( i + 1 )'
HYP4 = ('W e. Word NN0', ('F e. NN0', 'Z e. NN0', 'O e. NN0'))
AT = (HYP4, (('G e. NN0', 'H e. NN0'), REQ))
IFZ = 'i e. ( 0 ..^ R )'
