"""Sortie A5, batch 4: step 2 of the assembly, the reservoir and Q (Lean:
SearchAlg.lean lines 110-140).
MM_DB=sorties/a5.mm python3 tools/gen/a5_q.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from tm import *
from a2lib import WH

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

RES = '( ( Z Reservoir W ) ` Y )'
R1 = '( 1st ` R )'
LR = '( # ` %s )' % R1
QQ = '( %s substr <. ( %s - T ) , %s >. )' % (R1, LR, LR)
GW = '( ( Z goodPrimesW W ) ` Y )'
PRD = 'prod_ i e. ( 0 ..^ ( # ` Q ) ) ( Q ` i )'

# --------------------------------------------------------------- a5q
w = WH('a5q', 'The T largest elements of the reservoir form a duplicate-free word of good primes (Lean: hQnodup, hQlen, hQsub, hQcard, hQgood of SearchAlg.lean).')
h1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
h2 = w.h('T e. NN0')
h3 = w.h('R = %s' % RES)
h4 = w.h('I = %s' % LR)
h5 = w.h('Q = ( %s substr <. ( I - T ) , I >. )' % R1)
h6 = w.h('T <_ I')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)

zn = st([h1], 'simp1d', 'Z e. NN')
wn0 = st([h1], 'simp2d', 'W e. NN0')
yn = st([h1], 'simp3d', 'Y e. NN')
zn0 = st([zn], 'nnnn0d', 'Z e. NN0')
yn0 = st([yn], 'nnnn0d', 'Y e. NN0')
rescl = st([st([zn, wn0], 'jca', '( Z e. NN /\\ W e. NN0 )'), yn, w.inst('reservoircl')], 'syl2anc',
           '%s e. ( Word NN0 X. NN0 )' % RES)
rres = st([h3, rescl], 'eqeltrd', 'R e. ( Word NN0 X. NN0 )')
rw = st([rres, w.inst('xp1st')], 'syl', '%s e. Word NN0' % R1)
rlen = st([rw, w.inst('lencl')], 'syl', '%s e. NN0' % LR)
tle = st([h6, h4], 'breqtrd', 'T <_ %s' % LR)
tfz = st([st([h2, rlen, tle], '3jca', '( T e. NN0 /\\ %s e. NN0 /\\ T <_ %s )' % (LR, LR)),
          w.inst('elfz2nn0')], 'sylibr', 'T e. ( 0 ... %s )' % LR)
# Q = QQ
e1 = w.s([h4], 'oveq1d', '( ph -> ( I - T ) = ( %s - T ) )' % LR)
e2 = w.s([e1, h4], 'opeq12d', '( ph -> <. ( I - T ) , I >. = <. ( %s - T ) , %s >. )' % (LR, LR))
e3 = w.s([e2], 'oveq2d', '( ph -> ( %s substr <. ( I - T ) , I >. ) = %s )' % (R1, QQ))
qeq = st([h5, e3], 'eqtrd', 'Q = %s' % QQ)
# the drop facts
drp = st([rw, tfz], 'jca', '( %s e. Word NN0 /\\ T e. ( 0 ... %s ) )' % (R1, LR))
dcl = st([drp, w.inst('drpcl')], 'syl', '%s e. Word NN0' % QQ)
dlen = st([drp, w.inst('drplen')], 'syl', '( # ` %s ) = T' % QQ)
drn = st([drp, w.inst('drprn')], 'syl', 'ran %s C_ ran %s' % (QQ, R1))
# the reservoir specification
spec = st([h1, w.inst('resspecw')], 'syl',
          '( Fun `\' ( 1st ` %s ) /\\ ran ( 1st ` %s ) = %s )' % (RES, RES, GW))
r1eq = w.s([h3], 'fveq2d', '( ph -> %s = ( 1st ` %s ) )' % (R1, RES))
rfun = st([st([spec], 'simpld', 'Fun `\' ( 1st ` %s )' % RES),
           w.s([w.s([r1eq], 'cnveqd', '( ph -> `\' %s = `\' ( 1st ` %s ) )' % (R1, RES))], 'funeqd',
               '( ph -> ( Fun `\' %s <-> Fun `\' ( 1st ` %s ) ) )' % (R1, RES))],
          'mpbird', 'Fun `\' %s' % R1)
rrn = st([w.s([r1eq], 'rneqd', '( ph -> ran %s = ran ( 1st ` %s ) )' % (R1, RES)),
          st([spec], 'simprd', 'ran ( 1st ` %s ) = %s' % (RES, GW))], 'eqtrd',
         'ran %s = %s' % (R1, GW))
dndp = st([st([st([rw, rfun], 'jca', '( %s e. Word NN0 /\\ Fun `\' %s )' % (R1, R1)), tfz], 'jca',
              '( ( %s e. Word NN0 /\\ Fun `\' %s ) /\\ T e. ( 0 ... %s ) )' % (R1, R1, LR)),
           w.inst('drpndp')], 'syl', 'Fun `\' %s' % QQ)
# transfer along Q = QQ
qcl = st([qeq, dcl], 'eqeltrd', 'Q e. Word NN0')
qfun = st([dndp, w.s([w.s([qeq], 'cnveqd', '( ph -> `\' Q = `\' %s )' % QQ)], 'funeqd',
                     '( ph -> ( Fun `\' Q <-> Fun `\' %s ) )' % QQ)], 'mpbird', 'Fun `\' Q')
qlen = st([w.s([qeq], 'fveq2d', '( ph -> ( # ` Q ) = ( # ` %s ) )' % QQ), dlen], 'eqtrd', '( # ` Q ) = T')
qrn = st([st([w.s([qeq], 'rneqd', '( ph -> ran Q = ran %s )' % QQ), drn], 'eqsstrd',
             'ran Q C_ ran %s' % R1), rrn], 'sseqtrd', 'ran Q C_ %s' % GW)
qcard = st([st([qcl, qfun], 'jca', '( Q e. Word NN0 /\\ Fun `\' Q )'), w.inst('algwrdcard')], 'syl',
           '( # ` ran Q ) = ( # ` Q )')
qcard2 = st([qcard, qlen], 'eqtrd', '( # ` ran Q ) = T')
qfp = st([st([st([zn0, wn0, yn0], '3jca', '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'), qrn], 'jca',
             '( ( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 ) /\\ ran Q C_ %s )' % GW), w.inst('s3sfp')], 'syl',
          'ran Q e. ( ~P Prime i^i Fin )')
# every element is a prime at most Z
AN = '( ph /\\ c e. ran Q )'
sub = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (AN, f))
qmem = sub([w.s([qrn], 'adantr', '( %s -> ran Q C_ %s )' % (AN, GW)),
            w.s([], 'simpr', '( %s -> c e. ran Q )' % AN)], 'sseldd', 'c e. %s' % GW)
gbi = sub([w.s([st([zn0, wn0, yn0], '3jca', '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )')], 'adantr',
               '( %s -> ( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 ) )' % AN), w.inst('elgoodprimesw')], 'syl',
           '( c e. %s <-> ( c e. ( 0 ... Z ) /\\ ( c e. Prime /\\ W < c /\\ A. p e. Prime ( p || ( c - 1 ) -> p <_ Y ) ) ) )' % GW)
gcj = sub([qmem, gbi], 'mpbid',
          '( c e. ( 0 ... Z ) /\\ ( c e. Prime /\\ W < c /\\ A. p e. Prime ( p || ( c - 1 ) -> p <_ Y ) ) )')
gp = sub([sub([gcj], 'simprd', '( c e. Prime /\\ W < c /\\ A. p e. Prime ( p || ( c - 1 ) -> p <_ Y ) )')],
         'simp1d', 'c e. Prime')
gz = sub([sub([gcj], 'simpld', 'c e. ( 0 ... Z )'), w.inst('elfzle2')], 'syl', 'c <_ Z')
gall = w.s([sub([gp, gz], 'jca', '( c e. Prime /\\ c <_ Z )')], 'ralrimiva',
           '( ph -> A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )')
w.qed([st([st([qcl, qfun], 'jca', '( Q e. Word NN0 /\\ Fun `\' Q )'),
           st([qlen, qcard2], 'jca', '( ( # ` Q ) = T /\\ ( # ` ran Q ) = T )')], 'jca',
          '( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) )'),
       st([st([qrn, qfp], 'jca', '( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) )' % GW), gall], 'jca',
          '( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % GW)],
      'jca',
      '( ph -> ( ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = T /\\ ( # ` ran Q ) = T ) ) /\\ ( ( ran Q C_ %s /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) ) )' % GW)
run(w)

# --------------------------------------------------------------- a5qa
w = WH('a5qa', 'The modulus of the T largest reservoir elements (Lean: hLmod, hxceil, hLpos, hLz of SearchAlg.lean).')
k1 = w.h('( Q e. Word NN0 /\\ Fun `\' Q )')
k2 = w.h('( Z e. NN0 /\\ T e. NN0 )')
k3 = w.h('( # ` Q ) = T')
k4 = w.h('A. c e. ran Q ( c e. Prime /\\ c <_ Z )')
k5 = w.h('A = %s' % PRD)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
qcl = st([k1], 'simpld', 'Q e. Word NN0')
qfun = st([k1], 'simprd', 'Fun `\' Q')
zn0 = st([k2], 'simpld', 'Z e. NN0')
tn0 = st([k2], 'simprd', 'T e. NN0')
# 1 <_ c and c <_ Z for every entry
AN = '( ph /\\ c e. ran Q )'
sub = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (AN, f))
kk = sub([w.s([k4], 'adantr', '( %s -> A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % AN),
          w.s([], 'simpr', '( %s -> c e. ran Q )' % AN), w.inst('rspa')], 'syl2anc', '( c e. Prime /\\ c <_ Z )')
kp = sub([kk], 'simpld', 'c e. Prime')
kz = sub([kk], 'simprd', 'c <_ Z')
k1le = sub([sub([kp, w.inst('prmnn')], 'syl', 'c e. NN')], 'nnge1d', '1 <_ c')
allnn = w.s([k1le], 'ralrimiva', '( ph -> A. c e. ran Q 1 <_ c )')
allz = w.s([kz], 'ralrimiva', '( ph -> A. c e. ran Q c <_ Z )')
pnn = st([st([qcl, allnn], 'jca', '( Q e. Word NN0 /\\ A. c e. ran Q 1 <_ c )'), w.inst('algprodnn')],
         'syl', '%s e. NN' % PRD)
ann = st([k5, pnn], 'eqeltrd', 'A e. NN')
a5 = st([ann, w.s([w.s([], '5nn0', '5 e. NN0')], 'a1i', '( ph -> 5 e. NN0 )'), w.inst('nnexpcl')],
        'syl2anc', '( A ^ 5 ) e. NN')
lm = st([st([qcl, qfun], 'jca', '( Q e. Word NN0 /\\ Fun `\' Q )'), w.inst('lmodwrd')], 'syl',
        '( Lmod ` ran Q ) = %s' % PRD)
lmq = st([lm, st([k5], 'eqcomd', '%s = A' % PRD)], 'eqtrd', '( Lmod ` ran Q ) = A')
xc = st([st([qcl, qfun], 'jca', '( Q e. Word NN0 /\\ Fun `\' Q )'), w.inst('xceilwrd')], 'syl',
        '( xceil ` ran Q ) = ( %s ^ 5 )' % PRD)
xcq = st([xc, w.s([st([k5], 'eqcomd', '%s = A' % PRD)], 'oveq1d', '( ph -> ( %s ^ 5 ) = ( A ^ 5 ) )' % PRD)],
         'eqtrd', '( xceil ` ran Q ) = ( A ^ 5 )')
ple = st([st([st([qcl, zn0], 'jca', '( Q e. Word NN0 /\\ Z e. NN0 )'), allz], 'jca',
             '( ( Q e. Word NN0 /\\ Z e. NN0 ) /\\ A. c e. ran Q c <_ Z )'), w.inst('algprodle')], 'syl',
          '%s <_ ( Z ^ ( # ` Q ) )' % PRD)
aleq = st([st([k5, ple], 'eqbrtrd', 'A <_ ( Z ^ ( # ` Q ) )'),
           w.s([k3], 'oveq2d', '( ph -> ( Z ^ ( # ` Q ) ) = ( Z ^ T ) )')], 'breqtrd', 'A <_ ( Z ^ T )')
w.qed([st([ann, a5], 'jca', '( A e. NN /\\ ( A ^ 5 ) e. NN )'),
       st([lmq, xcq], 'jca', '( ( Lmod ` ran Q ) = A /\\ ( xceil ` ran Q ) = ( A ^ 5 ) )'),
       aleq], '3jca',
      '( ph -> ( ( A e. NN /\\ ( A ^ 5 ) e. NN ) /\\ ( ( Lmod ` ran Q ) = A /\\ ( xceil ` ran Q ) = ( A ^ 5 ) ) /\\ A <_ ( Z ^ T ) ) )')
run(w)

# --------------------------------------------------------------- a5ti
w = WH('a5ti', 'The reservoir has at least T elements (Lean: hlen of SearchAlg.lean).')
t1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
t2 = w.h('R = %s' % RES)
t3 = w.h('I = %s' % LR)
t4 = w.h('T <_ ( # ` %s )' % GW)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
znn = st([t1], 'simp1d', 'Z e. NN')
wn0 = st([t1], 'simp2d', 'W e. NN0')
ynn = st([t1], 'simp3d', 'Y e. NN')
rescl = st([st([znn, wn0], 'jca', '( Z e. NN /\\ W e. NN0 )'), ynn, w.inst('reservoircl')], 'syl2anc',
           '%s e. ( Word NN0 X. NN0 )' % RES)
rw = st([st([t2, rescl], 'eqeltrd', 'R e. ( Word NN0 X. NN0 )'), w.inst('xp1st')], 'syl', '%s e. Word NN0' % R1)
spec = st([t1, w.inst('resspecw')], 'syl',
          '( Fun `\' ( 1st ` %s ) /\\ ran ( 1st ` %s ) = %s )' % (RES, RES, GW))
r1eq = w.s([t2], 'fveq2d', '( ph -> %s = ( 1st ` %s ) )' % (R1, RES))
rfun = st([st([spec], 'simpld', 'Fun `\' ( 1st ` %s )' % RES),
           w.s([w.s([r1eq], 'cnveqd', '( ph -> `\' %s = `\' ( 1st ` %s ) )' % (R1, RES))], 'funeqd',
               '( ph -> ( Fun `\' %s <-> Fun `\' ( 1st ` %s ) ) )' % (R1, RES))], 'mpbird', 'Fun `\' %s' % R1)
rrn = st([w.s([r1eq], 'rneqd', '( ph -> ran %s = ran ( 1st ` %s ) )' % (R1, RES)),
          st([spec], 'simprd', 'ran ( 1st ` %s ) = %s' % (RES, GW))], 'eqtrd', 'ran %s = %s' % (R1, GW))
card = st([st([rw, rfun], 'jca', '( %s e. Word NN0 /\\ Fun `\' %s )' % (R1, R1)), w.inst('algwrdcard')], 'syl',
          '( # ` ran %s ) = %s' % (R1, LR))
gweq = w.s([rrn], 'fveq2d', '( ph -> ( # ` ran %s ) = ( # ` %s ) )' % (R1, GW))
gwlen = st([gweq, card], 'eqtr3d', '( # ` %s ) = %s' % (GW, LR))
w.qed([st([t4, gwlen], 'breqtrd', 'T <_ %s' % LR), st([t3], 'eqcomd', '%s = I' % LR)], 'breqtrd',
      '( ph -> T <_ I )')
run(w)
