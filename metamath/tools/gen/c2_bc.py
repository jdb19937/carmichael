"""Sortie C2 section 3.5b: Borel-Caratheodory on a rectangle."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *
from lin import linarith

RV = '( Re ` V )'; IV = '( Im ` V )'
DEN = '( ( 2 x. M ) - V )'
RD = '( Re ` %s )' % DEN

# ---- absremle --------------------------------------------------------------
w = W('absremle', 'A complex number with real part below a nonnegative M is no larger in modulus than twice M minus it.')
A0 = '( ( V e. CC /\\ M e. RR ) /\\ ( 0 <_ M /\\ %s <_ M ) )' % RV
vc = w.s([], 'simpll', '( %s -> V e. CC )' % A0)
mr = w.s([], 'simplr', '( %s -> M e. RR )' % A0)
m0 = w.s([], 'simprl', '( %s -> 0 <_ M )' % A0)
rle = w.s([], 'simprr', '( %s -> %s <_ M )' % (A0, RV))
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
t2r = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
t2c = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
m2r = w.s([t2r, mr], 'remulcld', '( %s -> ( 2 x. M ) e. RR )' % A0)
m2c = w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
dc = w.s([m2c, vc], 'subcld', '( %s -> %s e. CC )' % (A0, DEN))
rvr = w.s([vc], 'recld', '( %s -> %s e. RR )' % (A0, RV))
ivr = w.s([vc], 'imcld', '( %s -> %s e. RR )' % (A0, IV))
# real and imaginary parts of the difference
rdd = w.s([w.s([m2c, vc, w.inst('resub')], 'syl2anc', '( %s -> %s = ( ( Re ` ( 2 x. M ) ) - %s ) )' % (A0, RD, RV)),
           w.s([w.s([m2r, w.inst('rere')], 'syl', '( %s -> ( Re ` ( 2 x. M ) ) = ( 2 x. M ) )' % A0)], 'oveq1d',
               '( %s -> ( ( Re ` ( 2 x. M ) ) - %s ) = ( ( 2 x. M ) - %s ) )' % (A0, RV, RV))], 'eqtrd',
          '( %s -> %s = ( ( 2 x. M ) - %s ) )' % (A0, RD, RV))
idd = w.s([w.s([m2c, vc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` %s ) = ( ( Im ` ( 2 x. M ) ) - %s ) )' % (A0, DEN, IV)),
           w.s([w.s([w.s([m2r, w.inst('reim0')], 'syl', '( %s -> ( Im ` ( 2 x. M ) ) = 0 )' % A0)], 'oveq1d',
                    '( %s -> ( ( Im ` ( 2 x. M ) ) - %s ) = ( 0 - %s ) )' % (A0, IV, IV)),
                w.s([w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (IV, IV))], 'eqcomi', '( 0 - %s ) = -u %s' % (IV, IV))], 'a1i',
                    '( %s -> ( 0 - %s ) = -u %s )' % (A0, IV, IV))], 'eqtrd',
               '( %s -> ( ( Im ` ( 2 x. M ) ) - %s ) = -u %s )' % (A0, IV, IV))], 'eqtrd',
          '( %s -> ( Im ` %s ) = -u %s )' % (A0, DEN, IV))
# squares
d2r = w.s([m2r, rvr], 'resubcld', '( %s -> ( ( 2 x. M ) - %s ) e. RR )' % (A0, RV))
d2c = w.s([d2r], 'recnd', '( %s -> ( ( 2 x. M ) - %s ) e. CC )' % (A0, RV))
rvc = w.s([rvr], 'recnd', '( %s -> %s e. CC )' % (A0, RV))
sq1 = w.s([d2c, rvc, w.inst('subsq')], 'syl2anc',
          '( %s -> ( ( ( ( 2 x. M ) - %s ) ^ 2 ) - ( %s ^ 2 ) ) = ( ( ( ( 2 x. M ) - %s ) + %s ) x. ( ( ( 2 x. M ) - %s ) - %s ) ) )' % (A0, RV, RV, RV, RV, RV, RV))
lv = {RV: ('RR', rvr), 'M': ('RR', mr)}
p1 = linarith(w, A0, [m0], '0 <_ ( ( ( 2 x. M ) - %s ) + %s )' % (RV, RV), leaves=lv)
p2 = linarith(w, A0, [rle], '0 <_ ( ( ( 2 x. M ) - %s ) - %s )' % (RV, RV), leaves=lv)
prd = w.s([w.s([d2r, rvr], 'readdcld', '( %s -> ( ( ( 2 x. M ) - %s ) + %s ) e. RR )' % (A0, RV, RV)),
           w.s([d2r, rvr], 'resubcld', '( %s -> ( ( ( 2 x. M ) - %s ) - %s ) e. RR )' % (A0, RV, RV)), p1, p2], 'mulge0d',
          '( %s -> 0 <_ ( ( ( ( 2 x. M ) - %s ) + %s ) x. ( ( ( 2 x. M ) - %s ) - %s ) ) )' % (A0, RV, RV, RV, RV))
sub0 = w.s([prd, w.s([sq1], 'eqcomd', '( %s -> ( ( ( ( 2 x. M ) - %s ) + %s ) x. ( ( ( 2 x. M ) - %s ) - %s ) ) = ( ( ( ( 2 x. M ) - %s ) ^ 2 ) - ( %s ^ 2 ) ) )' % (A0, RV, RV, RV, RV, RV, RV))],
           'breqtrd', '( %s -> 0 <_ ( ( ( ( 2 x. M ) - %s ) ^ 2 ) - ( %s ^ 2 ) ) )' % (A0, RV, RV))
sqle = w.s([sub0, w.s([w.s([d2r], 'resqcld', '( %s -> ( ( ( 2 x. M ) - %s ) ^ 2 ) e. RR )' % (A0, RV)),
                       w.s([rvr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, RV)), w.inst('subge0')], 'syl2anc',
                      '( %s -> ( 0 <_ ( ( ( ( 2 x. M ) - %s ) ^ 2 ) - ( %s ^ 2 ) ) <-> ( %s ^ 2 ) <_ ( ( ( 2 x. M ) - %s ) ^ 2 ) ) )' % (A0, RV, RV, RV, RV))],
           'mpbid', '( %s -> ( %s ^ 2 ) <_ ( ( ( 2 x. M ) - %s ) ^ 2 ) )' % (A0, RV, RV))
iv2 = w.s([ivr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, IV))
addle = w.s([sqle, w.s([w.s([rvr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, RV)),
                        w.s([d2r], 'resqcld', '( %s -> ( ( ( 2 x. M ) - %s ) ^ 2 ) e. RR )' % (A0, RV)), iv2], 'leadd1d',
                       '( %s -> ( ( %s ^ 2 ) <_ ( ( ( 2 x. M ) - %s ) ^ 2 ) <-> ( ( %s ^ 2 ) + ( %s ^ 2 ) ) <_ ( ( ( ( 2 x. M ) - %s ) ^ 2 ) + ( %s ^ 2 ) ) ) )' % (A0, RV, RV, RV, IV, RV, IV))],
            'mpbid', '( %s -> ( ( %s ^ 2 ) + ( %s ^ 2 ) ) <_ ( ( ( ( 2 x. M ) - %s ) ^ 2 ) + ( %s ^ 2 ) ) )' % (A0, RV, IV, RV, IV))
av = w.s([vc, w.inst('absvalsq2')], 'syl', '( %s -> ( ( abs ` V ) ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (A0, RV, IV))
ad0 = w.s([dc, w.inst('absvalsq2')], 'syl', '( %s -> ( ( abs ` %s ) ^ 2 ) = ( ( %s ^ 2 ) + ( ( Im ` %s ) ^ 2 ) ) )' % (A0, DEN, RD, DEN))
ad1 = w.s([ad0, w.s([w.s([rdd], 'oveq1d', '( %s -> ( %s ^ 2 ) = ( ( ( 2 x. M ) - %s ) ^ 2 ) )' % (A0, RD, RV)),
                     w.s([w.s([idd], 'oveq1d', '( %s -> ( ( Im ` %s ) ^ 2 ) = ( -u %s ^ 2 ) )' % (A0, DEN, IV)),
                          w.s([w.s([ivr], 'recnd', '( %s -> %s e. CC )' % (A0, IV)), w.inst('sqneg')], 'syl', '( %s -> ( -u %s ^ 2 ) = ( %s ^ 2 ) )' % (A0, IV, IV))],
                         'eqtrd', '( %s -> ( ( Im ` %s ) ^ 2 ) = ( %s ^ 2 ) )' % (A0, DEN, IV))], 'oveq12d',
                    '( %s -> ( ( %s ^ 2 ) + ( ( Im ` %s ) ^ 2 ) ) = ( ( ( ( 2 x. M ) - %s ) ^ 2 ) + ( %s ^ 2 ) ) )' % (A0, RD, DEN, RV, IV))], 'eqtrd',
           '( %s -> ( ( abs ` %s ) ^ 2 ) = ( ( ( ( 2 x. M ) - %s ) ^ 2 ) + ( %s ^ 2 ) ) )' % (A0, DEN, RV, IV))
sq2 = w.s([w.s([av], 'idi', '( %s -> ( ( abs ` V ) ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (A0, RV, IV)), addle], 'eqbrtrd',
          '( %s -> ( ( abs ` V ) ^ 2 ) <_ ( ( ( ( 2 x. M ) - %s ) ^ 2 ) + ( %s ^ 2 ) ) )' % (A0, RV, IV))
sq3 = w.s([sq2, w.s([ad1], 'eqcomd', '( %s -> ( ( ( ( 2 x. M ) - %s ) ^ 2 ) + ( %s ^ 2 ) ) = ( ( abs ` %s ) ^ 2 ) )' % (A0, RV, IV, DEN))], 'breqtrd',
          '( %s -> ( ( abs ` V ) ^ 2 ) <_ ( ( abs ` %s ) ^ 2 ) )' % (A0, DEN))
w.qed([sq3, w.s([w.s([vc], 'abscld', '( %s -> ( abs ` V ) e. RR )' % A0), w.s([dc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, DEN)),
                 w.s([vc], 'absge0d', '( %s -> 0 <_ ( abs ` V ) )' % A0), w.s([dc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, DEN))], 'le2sqd',
                '( %s -> ( ( abs ` V ) <_ ( abs ` %s ) <-> ( ( abs ` V ) ^ 2 ) <_ ( ( abs ` %s ) ^ 2 ) ) )' % (A0, DEN, DEN))],
      'mpbird', '( %s -> ( abs ` V ) <_ ( abs ` %s ) )' % (A0, DEN)); run1(w)

# ---- bcne0 -----------------------------------------------------------------
w = W('bcne0', 'Twice a positive M minus a complex number of real part at most M is nonzero.')
A0 = '( ( V e. CC /\\ M e. RR ) /\\ ( 0 < M /\\ %s <_ M ) )' % RV
vc = w.s([], 'simpll', '( %s -> V e. CC )' % A0)
mr = w.s([], 'simplr', '( %s -> M e. RR )' % A0)
mp_ = w.s([], 'simprl', '( %s -> 0 < M )' % A0)
rle = w.s([], 'simprr', '( %s -> %s <_ M )' % (A0, RV))
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
t2r = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
t2c = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
m2r = w.s([t2r, mr], 'remulcld', '( %s -> ( 2 x. M ) e. RR )' % A0)
m2c = w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
dc = w.s([m2c, vc], 'subcld', '( %s -> %s e. CC )' % (A0, DEN))
rvr = w.s([vc], 'recld', '( %s -> %s e. RR )' % (A0, RV))
rdd = w.s([w.s([m2c, vc, w.inst('resub')], 'syl2anc', '( %s -> %s = ( ( Re ` ( 2 x. M ) ) - %s ) )' % (A0, RD, RV)),
           w.s([w.s([m2r, w.inst('rere')], 'syl', '( %s -> ( Re ` ( 2 x. M ) ) = ( 2 x. M ) )' % A0)], 'oveq1d',
               '( %s -> ( ( Re ` ( 2 x. M ) ) - %s ) = ( ( 2 x. M ) - %s ) )' % (A0, RV, RV))], 'eqtrd',
          '( %s -> %s = ( ( 2 x. M ) - %s ) )' % (A0, RD, RV))
lv = {RV: ('RR', rvr), 'M': ('RR', mr)}
pos = linarith(w, A0, [mp_, rle], '0 < ( ( 2 x. M ) - %s )' % RV, leaves=lv)
rdp = w.s([pos, w.s([rdd], 'eqcomd', '( %s -> ( ( 2 x. M ) - %s ) = %s )' % (A0, RV, RD))], 'breqtrd', '( %s -> 0 < %s )' % (A0, RD))
rdr = w.s([dc], 'recld', '( %s -> %s e. RR )' % (A0, RD))
absid_ = w.s([rdr, w.s([rdp], 'ltled', '( %s -> 0 <_ %s )' % (A0, RD)), w.inst('absid')], 'syl2anc', '( %s -> ( abs ` %s ) = %s )' % (A0, RD, RD))
rel = w.s([dc, w.inst('absrele')], 'syl', '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (A0, RD, DEN))
rel2 = w.s([w.s([absid_], 'eqcomd', '( %s -> %s = ( abs ` %s ) )' % (A0, RD, RD)), rel], 'eqbrtrd', '( %s -> %s <_ ( abs ` %s ) )' % (A0, RD, DEN))
apos = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), rdr, w.s([dc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, DEN)), rdp, rel2], 'ltletrd',
           '( %s -> 0 < ( abs ` %s ) )' % (A0, DEN))
w.qed([apos, w.s([dc, w.inst('absgt0')], 'syl', '( %s -> ( %s =/= 0 <-> 0 < ( abs ` %s ) ) )' % (A0, DEN, DEN))], 'mpbird',
      '( %s -> %s =/= 0 )' % (A0, DEN)); run1(w)

# ---- bcinv -----------------------------------------------------------------
GQ = '( V / %s )' % DEN
w = W('bcinv', 'The Moebius transform bound inverted: a bound on the modulus of V over twice M minus V gives a bound on the modulus of V.')
A0 = '( ( V e. CC /\\ M e. RR ) /\\ ( 0 < M /\\ %s <_ M ) /\\ ( T e. RR /\\ T < 1 /\\ ( abs ` %s ) <_ T ) )' % (RV, GQ)
vc = w.s([], 'simp1l', '( %s -> V e. CC )' % A0)
mr = w.s([], 'simp1r', '( %s -> M e. RR )' % A0)
mp_ = w.s([], 'simp2l', '( %s -> 0 < M )' % A0)
rle = w.s([], 'simp2r', '( %s -> %s <_ M )' % (A0, RV))
tr = w.s([], 'simp31', '( %s -> T e. RR )' % A0)
t1 = w.s([], 'simp32', '( %s -> T < 1 )' % A0)
gle = w.s([], 'simp33', '( %s -> ( abs ` %s ) <_ T )' % (A0, GQ))
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
t2r = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
t2c = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
m2r = w.s([t2r, mr], 'remulcld', '( %s -> ( 2 x. M ) e. RR )' % A0)
m2c = w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
m2p = w.s([w.s([], '2rp', '2 e. RR+'), w.s([mr, mp_], 'elrpd', '( %s -> M e. RR+ )' % A0)], 'rpmulcld', '( %s -> ( 2 x. M ) e. RR+ )' % A0) if False else w.s(
    [w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), w.s([mr, mp_], 'elrpd', '( %s -> M e. RR+ )' % A0)], 'rpmulcld',
    '( %s -> ( 2 x. M ) e. RR+ )' % A0)
dc = w.s([m2c, vc], 'subcld', '( %s -> %s e. CC )' % (A0, DEN))
dne = w.s([w.s([vc, mr], 'jca', '( %s -> ( V e. CC /\\ M e. RR ) )' % A0), w.s([mp_, rle], 'jca', '( %s -> ( 0 < M /\\ %s <_ M ) )' % (A0, RV)),
           w.inst('bcne0')], 'syl2anc', '( %s -> %s =/= 0 )' % (A0, DEN))
gc = w.s([vc, dc, dne], 'divcld', '( %s -> %s e. CC )' % (A0, GQ))
e1 = w.s([vc, dc, dne], 'divcan1d', '( %s -> ( %s x. %s ) = V )' % (A0, GQ, DEN))
e2 = w.s([gc, m2c, vc], 'subdid', '( %s -> ( %s x. %s ) = ( ( %s x. ( 2 x. M ) ) - ( %s x. V ) ) )' % (A0, GQ, DEN, GQ, GQ))
e3 = w.s([w.s([e1], 'eqcomd', '( %s -> V = ( %s x. %s ) )' % (A0, GQ, DEN)), e2], 'eqtrd',
         '( %s -> V = ( ( %s x. ( 2 x. M ) ) - ( %s x. V ) ) )' % (A0, GQ, GQ))
gvc = w.s([gc, vc], 'mulcld', '( %s -> ( %s x. V ) e. CC )' % (A0, GQ))
g2mc = w.s([gc, m2c], 'mulcld', '( %s -> ( %s x. ( 2 x. M ) ) e. CC )' % (A0, GQ))
e4 = w.s([w.s([e3], 'oveq1d', '( %s -> ( V + ( %s x. V ) ) = ( ( ( %s x. ( 2 x. M ) ) - ( %s x. V ) ) + ( %s x. V ) ) )' % (A0, GQ, GQ, GQ, GQ)),
          w.s([g2mc, gvc], 'npcand', '( %s -> ( ( ( %s x. ( 2 x. M ) ) - ( %s x. V ) ) + ( %s x. V ) ) = ( %s x. ( 2 x. M ) ) )' % (A0, GQ, GQ, GQ, GQ))],
         'eqtrd', '( %s -> ( V + ( %s x. V ) ) = ( %s x. ( 2 x. M ) ) )' % (A0, GQ, GQ))
e5 = w.s([w.s([vc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), gc], 'adddid', '( %s -> ( V x. ( 1 + %s ) ) = ( ( V x. 1 ) + ( V x. %s ) ) )' % (A0, GQ, GQ)),
          w.s([w.s([vc], 'mulridd', '( %s -> ( V x. 1 ) = V )' % A0), w.s([vc, gc], 'mulcomd', '( %s -> ( V x. %s ) = ( %s x. V ) )' % (A0, GQ, GQ))], 'oveq12d',
              '( %s -> ( ( V x. 1 ) + ( V x. %s ) ) = ( V + ( %s x. V ) ) )' % (A0, GQ, GQ))], 'eqtrd',
         '( %s -> ( V x. ( 1 + %s ) ) = ( V + ( %s x. V ) ) )' % (A0, GQ, GQ))
e6 = w.s([w.s([e5, e4], 'eqtrd', '( %s -> ( V x. ( 1 + %s ) ) = ( %s x. ( 2 x. M ) ) )' % (A0, GQ, GQ)),
          w.s([gc, m2c], 'mulcomd', '( %s -> ( %s x. ( 2 x. M ) ) = ( ( 2 x. M ) x. %s ) )' % (A0, GQ, GQ))], 'eqtrd',
         '( %s -> ( V x. ( 1 + %s ) ) = ( ( 2 x. M ) x. %s ) )' % (A0, GQ, GQ))
onc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), gc], 'addcld', '( %s -> ( 1 + %s ) e. CC )' % (A0, GQ))
ea = w.s([w.s([w.s([e6], 'fveq2d', '( %s -> ( abs ` ( V x. ( 1 + %s ) ) ) = ( abs ` ( ( 2 x. M ) x. %s ) ) )' % (A0, GQ, GQ)),
               w.s([m2c, gc], 'absmuld', '( %s -> ( abs ` ( ( 2 x. M ) x. %s ) ) = ( ( abs ` ( 2 x. M ) ) x. ( abs ` %s ) )' % (A0, GQ, GQ) + ' )')], 'eqtrd',
              '( %s -> ( abs ` ( V x. ( 1 + %s ) ) ) = ( ( abs ` ( 2 x. M ) ) x. ( abs ` %s ) ) )' % (A0, GQ, GQ)),
          w.s([w.s([m2r, w.s([m2p], 'rpge0d', '( %s -> 0 <_ ( 2 x. M ) )' % A0), w.inst('absid')], 'syl2anc', '( %s -> ( abs ` ( 2 x. M ) ) = ( 2 x. M ) )' % A0)], 'oveq1d',
              '( %s -> ( ( abs ` ( 2 x. M ) ) x. ( abs ` %s ) ) = ( ( 2 x. M ) x. ( abs ` %s ) ) )' % (A0, GQ, GQ))], 'eqtrd',
         '( %s -> ( abs ` ( V x. ( 1 + %s ) ) ) = ( ( 2 x. M ) x. ( abs ` %s ) ) )' % (A0, GQ, GQ))
eb = w.s([vc, onc], 'absmuld', '( %s -> ( abs ` ( V x. ( 1 + %s ) ) ) = ( ( abs ` V ) x. ( abs ` ( 1 + %s ) ) ) )' % (A0, GQ, GQ))
key = w.s([w.s([eb], 'eqcomd', '( %s -> ( ( abs ` V ) x. ( abs ` ( 1 + %s ) ) ) = ( abs ` ( V x. ( 1 + %s ) ) ) )' % (A0, GQ, GQ)), ea], 'eqtrd',
          '( %s -> ( ( abs ` V ) x. ( abs ` ( 1 + %s ) ) ) = ( ( 2 x. M ) x. ( abs ` %s ) ) )' % (A0, GQ, GQ))
# 1 - T <_ ( abs ` ( 1 + GQ ) )
ngc = w.s([gc], 'negcld', '( %s -> -u %s e. CC )' % (A0, GQ))
d2 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), gc], 'subnegd', '( %s -> ( 1 - -u %s ) = ( 1 + %s ) )' % (A0, GQ, GQ))
a2d = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), ngc, w.inst('abs2dif')], 'syl2anc',
          '( %s -> ( ( abs ` 1 ) - ( abs ` -u %s ) ) <_ ( abs ` ( 1 - -u %s ) ) )' % (A0, GQ, GQ))
a2e = w.s([a2d, w.s([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % A0),
                     w.s([gc], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (A0, GQ, GQ))], 'oveq12d',
                    '( %s -> ( ( abs ` 1 ) - ( abs ` -u %s ) ) = ( 1 - ( abs ` %s ) ) )' % (A0, GQ, GQ))], 'breqtrrd',
          '( %s -> ( 1 - ( abs ` %s ) ) <_ ( abs ` ( 1 - -u %s ) ) )' % (A0, GQ, GQ)) if False else w.s(
    [w.s([w.s([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % A0),
          w.s([gc], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (A0, GQ, GQ))], 'oveq12d',
         '( %s -> ( ( abs ` 1 ) - ( abs ` -u %s ) ) = ( 1 - ( abs ` %s ) ) )' % (A0, GQ, GQ))], 'eqcomd',
     '( %s -> ( 1 - ( abs ` %s ) ) = ( ( abs ` 1 ) - ( abs ` -u %s ) ) )' % (A0, GQ, GQ)), a2d], 'eqbrtrd',
    '( %s -> ( 1 - ( abs ` %s ) ) <_ ( abs ` ( 1 - -u %s ) ) )' % (A0, GQ, GQ))
a2f = w.s([a2e, w.s([d2], 'fveq2d', '( %s -> ( abs ` ( 1 - -u %s ) ) = ( abs ` ( 1 + %s ) ) )' % (A0, GQ, GQ))], 'breqtrd',
           '( %s -> ( 1 - ( abs ` %s ) ) <_ ( abs ` ( 1 + %s ) ) )' % (A0, GQ, GQ))
agr = w.s([gc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, GQ))
tle = linarith(w, A0, [gle], '( 1 - T ) <_ ( 1 - ( abs ` %s ) )' % GQ, leaves={'T': ('RR', tr), '( abs ` %s )' % GQ: ('RR', agr)})
oner = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr], 'resubcld', '( %s -> ( 1 - T ) e. RR )' % A0)
onegr = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), agr], 'resubcld', '( %s -> ( 1 - ( abs ` %s ) ) e. RR )' % (A0, GQ))
aor = w.s([onc], 'abscld', '( %s -> ( abs ` ( 1 + %s ) ) e. RR )' % (A0, GQ))
tlo = w.s([oner, onegr, aor, tle, a2f], 'letrd', '( %s -> ( 1 - T ) <_ ( abs ` ( 1 + %s ) ) )' % (A0, GQ))
avr = w.s([vc], 'abscld', '( %s -> ( abs ` V ) e. RR )' % A0)
av0 = w.s([vc], 'absge0d', '( %s -> 0 <_ ( abs ` V ) )' % A0)
m1 = w.s([w.s([oner, aor, w.s([avr, av0], 'jca', '( %s -> ( ( abs ` V ) e. RR /\\ 0 <_ ( abs ` V ) ) )' % A0)], '3jca',
               '( %s -> ( ( 1 - T ) e. RR /\\ ( abs ` ( 1 + %s ) ) e. RR /\\ ( ( abs ` V ) e. RR /\\ 0 <_ ( abs ` V ) ) ) )' % (A0, GQ)),
          tlo, w.inst('lemul2a')], 'syl2anc', '( %s -> ( ( abs ` V ) x. ( 1 - T ) ) <_ ( ( abs ` V ) x. ( abs ` ( 1 + %s ) ) ) )' % (A0, GQ))
m2 = w.s([gle, w.s([agr, tr, m2p], 'lemul2d', '( %s -> ( ( abs ` %s ) <_ T <-> ( ( 2 x. M ) x. ( abs ` %s ) ) <_ ( ( 2 x. M ) x. T ) ) )' % (A0, GQ, GQ))],
         'mpbid', '( %s -> ( ( 2 x. M ) x. ( abs ` %s ) ) <_ ( ( 2 x. M ) x. T ) )' % (A0, GQ))
m3 = w.s([m1, key], 'breqtrd', '( %s -> ( ( abs ` V ) x. ( 1 - T ) ) <_ ( ( 2 x. M ) x. ( abs ` %s ) ) )' % (A0, GQ))
m4 = w.s([w.s([avr, oner], 'remulcld', '( %s -> ( ( abs ` V ) x. ( 1 - T ) ) e. RR )' % A0),
          w.s([m2r, agr], 'remulcld', '( %s -> ( ( 2 x. M ) x. ( abs ` %s ) ) e. RR )' % (A0, GQ)),
          w.s([m2r, tr], 'remulcld', '( %s -> ( ( 2 x. M ) x. T ) e. RR )' % A0), m3, m2], 'letrd',
         '( %s -> ( ( abs ` V ) x. ( 1 - T ) ) <_ ( ( 2 x. M ) x. T ) )' % A0)
pos = linarith(w, A0, [t1], '0 < ( 1 - T )', leaves={'T': ('RR', tr)})
w.qed([m4, w.s([avr, w.s([m2r, tr], 'remulcld', '( %s -> ( ( 2 x. M ) x. T ) e. RR )' % A0),
               w.s([oner, pos], 'jca', '( %s -> ( ( 1 - T ) e. RR /\\ 0 < ( 1 - T ) ) )' % A0), w.inst('lemuldiv')], 'syl3anc',
               '( %s -> ( ( ( abs ` V ) x. ( 1 - T ) ) <_ ( ( 2 x. M ) x. T ) <-> ( abs ` V ) <_ ( ( ( 2 x. M ) x. T ) / ( 1 - T ) ) ) )' % A0)],
      'mpbid', '( %s -> ( abs ` V ) <_ ( ( ( 2 x. M ) x. T ) / ( 1 - T ) ) )' % A0); run1(w)

# ---- rectintbc -------------------------------------------------------------
RQ = RE('Q'); IQ = IM('Q')
INTQ = '( Q e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RQ, RQ, RB, IA, IQ, IQ, IB)
RBDP = RBD('P', 'R'); RBDQ = RBD('Q', 'S')
DZ = '( ( 2 x. M ) - ( F ` z ) )'
GM = MP('z', 'D', '( ( F ` z ) / %s )' % DZ)


def DU(X):
    return '( ( 2 x. M ) - ( F ` %s ) )' % X


def GMV(X):
    return '( ( F ` %s ) / %s )' % (X, DU(X))


REH = 'A. y e. D ( Re ` ( F ` y ) ) <_ M'
C1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ ( %s /\\ ( A crect B ) C_ D ) )' % (AB, INTP, INTQ, HOL)
C2 = '( ( M e. RR /\\ 0 < M /\\ %s ) /\\ ( F ` P ) = 0 )' % REH
C3 = ('( ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) ) /\\ ( T e. RR /\\ T < 1 /\\ ( %s x. ( abs ` ( Q - P ) ) ) <_ ( ( _pi x. T ) x. ( R x. S ) ) ) )'
      % (RBDP, RBDQ, PER))
A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
AZ = '( %s /\\ z e. D )' % A0
C0S = '( CC \\ { 0 } )'
w = W('rectintbc', 'Borel-Caratheodory on a rectangle: a function holomorphic on an open set containing the rectangle, vanishing at a strictly interior point and with real part bounded above, has a modulus bound at a second strictly interior point.')
c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1))
c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
pqn = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INTP, INTQ))
hd = w.s([c1, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ ( A crect B ) C_ D ) )' % (A0, HOL))
hl = w.s([hd, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
rdd = w.s([hd, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
mm0 = w.s([c2, w.inst('simpl')], 'syl', '( %s -> ( M e. RR /\\ 0 < M /\\ %s ) )' % (A0, REH))
fp0 = w.s([c2, w.inst('simpr')], 'syl', '( %s -> ( F ` P ) = 0 )' % A0)
mr = w.s([mm0, w.inst('simp1')], 'syl', '( %s -> M e. RR )' % A0)
mp_ = w.s([mm0, w.inst('simp2')], 'syl', '( %s -> 0 < M )' % A0)
reh = w.s([mm0, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, REH))
rbs = w.s([c3, w.inst('simpl')], 'syl', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) ) )' % (A0, RBDP, RBDQ))
tt = w.s([c3, w.inst('simpr')], 'syl', '( %s -> ( T e. RR /\\ T < 1 /\\ ( %s x. ( abs ` ( Q - P ) ) ) <_ ( ( _pi x. T ) x. ( R x. S ) ) ) )' % (A0, PER))
tr = w.s([tt, w.inst('simp1')], 'syl', '( %s -> T e. RR )' % A0)
t1 = w.s([tt, w.inst('simp2')], 'syl', '( %s -> T < 1 )' % A0)
thyp = w.s([tt, w.inst('simp3')], 'syl', '( %s -> ( %s x. ( abs ` ( Q - P ) ) ) <_ ( ( _pi x. T ) x. ( R x. S ) ) )' % (A0, PER))
rb1 = w.s([rbs, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
rb2 = w.s([rbs, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ 0 < S ) )' % (A0, RBDQ))
rr = w.s([w.s([rb1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
sr = w.s([w.s([rb2, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDQ)), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
rpos = w.s([rb1, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
spos = w.s([rb2, w.inst('simpr')], 'syl', '( %s -> 0 < S )' % A0)
rsrp = w.s([w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0), w.s([sr, spos], 'elrpd', '( %s -> S e. RR+ )' % A0)], 'rpmulcld',
           '( %s -> ( R x. S ) e. RR+ )' % A0)
it = w.s([pqn, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
iq = w.s([pqn, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
dop = w.s([hl, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
dvfd = w.s([hl, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % A0)
mrc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
t2c = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
m2c = w.s([t2c, mrc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
m0 = w.s([mp_], 'ltled', '( %s -> 0 <_ M )' % A0)
# the denominator is nonzero on D
zd = w.s([], 'simpr', '( %s -> z e. D )' % AZ)
fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % AZ), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % AZ)
suby = w.s([w.s([w.s([w.s([], 'fveq2', '( y = z -> ( F ` y ) = ( F ` z ) )')], 'fveq2d', '( y = z -> ( Re ` ( F ` y ) ) = ( Re ` ( F ` z ) ) )')], 'breq1d',
                '( y = z -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` z ) ) <_ M ) )')], 'idi',
           '( y = z -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` z ) ) <_ M ) )')
rez = w.s([suby, w.s([reh], 'adantr', '( %s -> %s )' % (AZ, REH)), zd], 'rspcdva', '( %s -> ( Re ` ( F ` z ) ) <_ M )' % AZ)
dzn = w.s([w.s([fzc, w.s([mr], 'adantr', '( %s -> M e. RR )' % AZ)], 'jca', '( %s -> ( ( F ` z ) e. CC /\\ M e. RR ) )' % AZ),
           w.s([w.s([mp_], 'adantr', '( %s -> 0 < M )' % AZ), rez], 'jca', '( %s -> ( 0 < M /\\ ( Re ` ( F ` z ) ) <_ M ) )' % AZ), w.inst('bcne0')],
          'syl2anc', '( %s -> %s =/= 0 )' % (AZ, DZ))
dzc = w.s([w.s([m2c], 'adantr', '( %s -> ( 2 x. M ) e. CC )' % AZ), fzc], 'subcld', '( %s -> %s e. CC )' % (AZ, DZ))
dz0 = w.s([w.s([dzc, dzn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (AZ, DZ, DZ)), w.inst('eldifsn')], 'sylibr', '( %s -> %s e. %s )' % (AZ, DZ, C0S))
# continuity of the denominator into CC \ { 0 }
fmpt = w.s([ff], 'feqmptd', '( %s -> F = %s )' % (A0, MP('z', 'D', '( F ` z )')))
fmp = w.s([fmpt, fcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( F ` z )')))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
scn = w.s([w.s([ej], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
ccss = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
cmp = w.s([m2c, dcc, ccss, w.inst('cncfmptc')], 'syl3anc', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( 2 x. M )')))
dmp = w.s([ej, scn, cmp, fmp], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', DZ)))
c0cc = w.s([w.s([], 'difss', '%s C_ CC' % C0S)], 'a1i', '( %s -> %s C_ CC )' % (A0, C0S))
dmf = w.s([dz0, w.s([], 'eqid', '%s = %s' % (MP('z', 'D', DZ), MP('z', 'D', DZ)))], 'fmptd', '( %s -> %s : D --> %s )' % (A0, MP('z', 'D', DZ), C0S))
dmp0 = w.s([dmf, w.s([c0cc, dmp, w.inst('cncfcdm')], 'syl2anc',
                     '( %s -> ( %s e. ( D -cn-> %s ) <-> %s : D --> %s ) )' % (A0, MP('z', 'D', DZ), C0S, MP('z', 'D', DZ), C0S))],
           'mpbird', '( %s -> %s e. ( D -cn-> %s ) )' % (A0, MP('z', 'D', DZ), C0S))
INV = MP('x', C0S, '( 1 / x )')
cdcn = w.s([w.s([], 'eqid', '%s = %s' % (INV, INV))], 'cdivcncf', '( 1 e. CC -> %s e. ( %s -cn-> CC ) )' % (INV, C0S))
cdcnd = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), cdcn], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, INV, C0S))
nfz = w.s([], 'nfv', 'F/ z %s' % A0)
c0ss = w.s([w.s([], 'ssid', '%s C_ %s' % (C0S, C0S))], 'a1i', '( %s -> %s C_ %s )' % (A0, C0S, C0S))
stx = w.s([], 'oveq2', '( x = %s -> ( 1 / x ) = ( 1 / %s ) )' % (DZ, DZ))
rcn = w.s([nfz, dmp0, cdcnd, c0ss, stx], 'cncfcompt2', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( 1 / %s )' % DZ)))
prd = w.s([ej, mcn, fmp, rcn], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( ( F ` z ) x. ( 1 / %s ) )' % DZ)))
dre = w.s([w.s([fzc, dzc, dzn], 'divrecd', '( %s -> ( ( F ` z ) / %s ) = ( ( F ` z ) x. ( 1 / %s ) ) )' % (AZ, DZ, DZ))], 'mpteq2dva',
          '( %s -> %s = %s )' % (A0, GM, MP('z', 'D', '( ( F ` z ) x. ( 1 / %s ) )' % DZ)))
gmcn = w.s([dre, prd], 'eqeltrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GM))
# derivative of GM
ce = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
dfzc = w.s([w.s([dvfd], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % AZ), zd], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` z ) e. CC )' % AZ)
hdv = w.s([hl, w.inst('holdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'D', '( F ` z )'), MP('z', 'D', '( ( CC _D F ) ` z )')))
ACC = '( %s /\\ z e. CC )' % A0
m2cc = w.s([m2c], 'adantr', '( %s -> ( 2 x. M ) e. CC )' % ACC)
z0cc = w.s([], '0cnd', '( %s -> 0 e. CC )' % ACC)
dvc0 = w.s([ce, m2c, w.inst('dvmptc')], 'syl2anc', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'CC', '( 2 x. M )'), MP('z', 'CC', '0')))
jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
dvc0d = w.s([ce, m2cc, z0cc, dvc0, dcc, jr, ej, dop], 'dvmptres', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'D', '( 2 x. M )'), MP('z', 'D', '0')))
z0d = w.s([], '0cnd', '( %s -> 0 e. CC )' % AZ)
m2cz = w.s([m2c], 'adantr', '( %s -> ( 2 x. M ) e. CC )' % AZ)
dvden = w.s([ce, m2cz, z0d, dvc0d, fzc, dfzc, hdv], 'dvmptsub',
            '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'D', DZ), MP('z', 'D', '( 0 - ( ( CC _D F ) ` z ) )')))
subd = w.s([z0d, dfzc], 'subcld', '( %s -> ( 0 - ( ( CC _D F ) ` z ) ) e. CC )' % AZ)
GRHS = '( ( ( ( ( CC _D F ) ` z ) x. %s ) - ( ( 0 - ( ( CC _D F ) ` z ) ) x. ( F ` z ) ) ) / ( %s ^ 2 ) )' % (DZ, DZ)
dvgm = w.s([ce, fzc, dfzc, hdv, dz0, subd, dvden], 'dvmptdiv', '( %s -> ( CC _D %s ) = %s )' % (A0, GM, MP('z', 'D', GRHS)))
grc = w.s([w.s([w.s([dfzc, dzc], 'mulcld', '( %s -> ( ( ( CC _D F ) ` z ) x. %s ) e. CC )' % (AZ, DZ)),
                w.s([subd, fzc], 'mulcld', '( %s -> ( ( 0 - ( ( CC _D F ) ` z ) ) x. ( F ` z ) ) e. CC )' % AZ)], 'subcld',
               '( %s -> ( ( ( ( CC _D F ) ` z ) x. %s ) - ( ( 0 - ( ( CC _D F ) ` z ) ) x. ( F ` z ) ) ) e. CC )' % (AZ, DZ)),
            w.s([dzc], 'sqcld', '( %s -> ( %s ^ 2 ) e. CC )' % (AZ, DZ)),
            w.s([dzc, dzn, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % AZ)], 'expne0d', '( %s -> ( %s ^ 2 ) =/= 0 )' % (AZ, DZ))],
           'divcld', '( %s -> %s e. CC )' % (AZ, GRHS))
gmd = dvdom(w, A0, GM, 'z', 'D', GRHS, dvgm, grc)
hgm = w.s([gmcn, gmd], 'jca', '( %s -> %s )' % (A0, HOLG(GM)))
hogm = w.s([hgm, rdd, w.inst('holcrect')], 'syl2anc', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) ) )' % (A0, GM, GM))


def gmval(ante, X, memstep):
    s1 = w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (X, X))
    s2 = w.s([w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (X, X))], 'oveq2d', '( z = %s -> %s = %s )' % (X, DZ, DU(X)))
    sub = w.s([s1, s2], 'oveq12d', '( z = %s -> ( ( F ` z ) / %s ) = %s )' % (X, DZ, GMV(X)))
    return mptval(w, ante, 'z', 'D', GM, X, GMV(X), sub, memstep)


# the frame bound on the Moebius transform
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
qc = w.s([iq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
      [('simpll', '%s < %s' % (RA, RP)), ('simplr', '%s < %s' % (RP, RB)),
       ('simprl', '%s < %s' % (IA, IP)), ('simprr', '%s < %s' % (IP, IB))]]
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr_ = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP)); pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
geo = w.s([w.s([w.s([ar, pr_, br, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB)),
           w.s([w.s([ai, pi_, bi, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))],
          'jca', '( %s -> %s )' % (A0, GEO))
fru = w.s([ab, geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, FR))
At = '( %s /\\ t e. %s )' % (A0, FR)
tf = w.s([], 'simpr', '( %s -> t e. %s )' % (At, FR))
tr_ = w.s([w.s([fru], 'adantr', '( %s -> %s C_ ( A crect B ) )' % (At, FR)), tf], 'sseldd', '( %s -> t e. ( A crect B ) )' % At)
td = w.s([w.s([rdd], 'adantr', '( %s -> ( A crect B ) C_ D )' % At), tr_], 'sseldd', '( %s -> t e. D )' % At)
ftc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % At), td], 'ffvelcdmd', '( %s -> ( F ` t ) e. CC )' % At)
subt = w.s([w.s([w.s([w.s([], 'fveq2', '( y = t -> ( F ` y ) = ( F ` t ) )')], 'fveq2d', '( y = t -> ( Re ` ( F ` y ) ) = ( Re ` ( F ` t ) ) )')], 'breq1d',
                '( y = t -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` t ) ) <_ M ) )')], 'idi',
           '( y = t -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` t ) ) <_ M ) )')
ret = w.s([subt, w.s([reh], 'adantr', '( %s -> %s )' % (At, REH)), td], 'rspcdva', '( %s -> ( Re ` ( F ` t ) ) <_ M )' % At)
dtn = w.s([w.s([ftc, w.s([mr], 'adantr', '( %s -> M e. RR )' % At)], 'jca', '( %s -> ( ( F ` t ) e. CC /\\ M e. RR ) )' % At),
           w.s([w.s([mp_], 'adantr', '( %s -> 0 < M )' % At), ret], 'jca', '( %s -> ( 0 < M /\\ ( Re ` ( F ` t ) ) <_ M ) )' % At), w.inst('bcne0')],
          'syl2anc', '( %s -> %s =/= 0 )' % (At, DU('t')))
dtc = w.s([w.s([m2c], 'adantr', '( %s -> ( 2 x. M ) e. CC )' % At), ftc], 'subcld', '( %s -> %s e. CC )' % (At, DU('t')))
arem = w.s([w.s([ftc, w.s([mr], 'adantr', '( %s -> M e. RR )' % At)], 'jca', '( %s -> ( ( F ` t ) e. CC /\\ M e. RR ) )' % At),
            w.s([w.s([m0], 'adantr', '( %s -> 0 <_ M )' % At), ret], 'jca', '( %s -> ( 0 <_ M /\\ ( Re ` ( F ` t ) ) <_ M ) )' % At), w.inst('absremle')],
           'syl2anc', '( %s -> ( abs ` ( F ` t ) ) <_ ( abs ` %s ) )' % (At, DU('t')))
adt = w.s([dtc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, DU('t')))
adtp = w.s([w.s([dtn, w.s([dtc, w.inst('absgt0')], 'syl', '( %s -> ( %s =/= 0 <-> 0 < ( abs ` %s ) ) )' % (At, DU('t'), DU('t')))], 'mpbid',
                '( %s -> 0 < ( abs ` %s ) )' % (At, DU('t')))], 'idi', '( %s -> 0 < ( abs ` %s ) )' % (At, DU('t')))
adtrp = w.s([adt, adtp], 'elrpd', '( %s -> ( abs ` %s ) e. RR+ )' % (At, DU('t')))
gvt = gmval(At, 't', td)
absgt = w.s([w.s([gvt], 'fveq2d', '( %s -> ( abs ` ( %s ` t ) ) = ( abs ` %s ) )' % (At, GM, GMV('t'))),
             w.s([ftc, dtc, dtn], 'absdivd', '( %s -> ( abs ` %s ) = ( ( abs ` ( F ` t ) ) / ( abs ` %s ) ) )' % (At, GMV('t'), DU('t')))], 'eqtrd',
            '( %s -> ( abs ` ( %s ` t ) ) = ( ( abs ` ( F ` t ) ) / ( abs ` %s ) ) )' % (At, GM, DU('t')))
aft = w.s([ftc], 'abscld', '( %s -> ( abs ` ( F ` t ) ) e. RR )' % At)
one1 = w.s([], '1red', '( %s -> 1 e. RR )' % At)
dle = w.s([w.s([arem, w.s([w.s([adt], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (At, DU('t')))], 'mulridd',
                          '( %s -> ( ( abs ` %s ) x. 1 ) = ( abs ` %s ) )' % (At, DU('t'), DU('t')))], 'breqtrrd',
                '( %s -> ( abs ` ( F ` t ) ) <_ ( ( abs ` %s ) x. 1 ) )' % (At, DU('t'))),
           w.s([aft, one1, w.s([adt, adtp], 'jca', '( %s -> ( ( abs ` %s ) e. RR /\\ 0 < ( abs ` %s ) ) )' % (At, DU('t'), DU('t'))), w.inst('ledivmul')],
               'syl3anc', '( %s -> ( ( ( abs ` ( F ` t ) ) / ( abs ` %s ) ) <_ 1 <-> ( abs ` ( F ` t ) ) <_ ( ( abs ` %s ) x. 1 ) ) )' % (At, DU('t'), DU('t')))],
          'mpbird', '( %s -> ( ( abs ` ( F ` t ) ) / ( abs ` %s ) ) <_ 1 )' % (At, DU('t')))
gbt = w.s([absgt, dle], 'eqbrtrd', '( %s -> ( abs ` ( %s ` t ) ) <_ 1 )' % (At, GM))
allt = w.s([gbt], 'ralrimiva', '( %s -> A. t e. %s ( abs ` ( %s ` t ) ) <_ 1 )' % (A0, FR, GM))
cbvu = w.s([w.s([w.s([w.s([], 'fveq2', '( t = u -> ( %s ` t ) = ( %s ` u ) )' % (GM, GM))], 'fveq2d',
                      '( t = u -> ( abs ` ( %s ` t ) ) = ( abs ` ( %s ` u ) ) )' % (GM, GM))], 'breq1d',
                '( t = u -> ( ( abs ` ( %s ` t ) ) <_ 1 <-> ( abs ` ( %s ` u ) ) <_ 1 ) )' % (GM, GM))], 'cbvralvw',
           '( A. t e. %s ( abs ` ( %s ` t ) ) <_ 1 <-> A. u e. %s ( abs ` ( %s ` u ) ) <_ 1 )' % (FR, GM, FR, GM))
allu = w.s([allt, cbvu], 'sylib', '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ 1 )' % (A0, FR, GM))
# GM vanishes at P
pcr = w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)
pd = w.s([rdd, pcr], 'sseldd', '( %s -> P e. D )' % A0)
qcr = w.s([ab, iq, w.inst('crectinp')], 'syl2anc', '( %s -> Q e. ( A crect B ) )' % A0)
qd = w.s([rdd, qcr], 'sseldd', '( %s -> Q e. D )' % A0)
fpc = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
fqc = w.s([ff, qd], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
subp = w.s([w.s([w.s([w.s([], 'fveq2', '( y = P -> ( F ` y ) = ( F ` P ) )')], 'fveq2d', '( y = P -> ( Re ` ( F ` y ) ) = ( Re ` ( F ` P ) ) )')], 'breq1d',
                '( y = P -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` P ) ) <_ M ) )')], 'idi',
           '( y = P -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` P ) ) <_ M ) )')
rep = w.s([subp, reh, pd], 'rspcdva', '( %s -> ( Re ` ( F ` P ) ) <_ M )' % A0)
dpn = w.s([w.s([fpc, mr], 'jca', '( %s -> ( ( F ` P ) e. CC /\\ M e. RR ) )' % A0),
           w.s([mp_, rep], 'jca', '( %s -> ( 0 < M /\\ ( Re ` ( F ` P ) ) <_ M ) )' % A0), w.inst('bcne0')], 'syl2anc',
          '( %s -> %s =/= 0 )' % (A0, DU('P')))
dpc = w.s([m2c, fpc], 'subcld', '( %s -> %s e. CC )' % (A0, DU('P')))
gvp = gmval(A0, 'P', pd)
gp0 = w.s([gvp, w.s([w.s([fp0], 'oveq1d', '( %s -> %s = ( 0 / %s ) )' % (A0, GMV('P'), DU('P'))),
                     w.s([dpc, dpn], 'div0d', '( %s -> ( 0 / %s ) = 0 )' % (A0, DU('P')))], 'eqtrd', '( %s -> %s = 0 )' % (A0, GMV('P')))], 'eqtrd',
          '( %s -> ( %s ` P ) = 0 )' % (A0, GM))
# Schwarz on the Moebius transform
AQG = '( abs ` ( %s ` Q ) )' % GM
DD = '( abs ` ( Q - P ) )'
sch = w.s([w.s([ab, pqn, hogm], '3jca', '( %s -> ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) ) ) )'
                % (A0, AB, INTP, INTQ, GM, GM)), rbs,
           w.s([w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), allu], 'jca', '( %s -> ( 1 e. RR /\\ A. u e. %s ( abs ` ( %s ` u ) ) <_ 1 ) )' % (A0, FR, GM)), gp0],
               'jca', '( %s -> ( ( 1 e. RR /\\ A. u e. %s ( abs ` ( %s ` u ) ) <_ 1 ) /\\ ( %s ` P ) = 0 ) )' % (A0, FR, GM, GM)),
           w.inst('rectintsch')], 'syl3anc',
          '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) <_ ( ( ( 2 x. 1 ) x. %s ) x. %s ) )' % (A0, AQG, PER, DD))
# turn the hypothesis into the same shape
perr = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)),
            w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
perc = w.s([perr], 'recnd', '( %s -> %s e. CC )' % (A0, PER))
ddr = w.s([w.s([qc, pc], 'subcld', '( %s -> ( Q - P ) e. CC )' % A0)], 'abscld', '( %s -> %s e. RR )' % (A0, DD))
ddc = w.s([ddr], 'recnd', '( %s -> %s e. CC )' % (A0, DD))
t2rp = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0)
e21 = w.s([w.s([w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)], 'idi', '( %s -> 1 e. CC )' % A0)], 'idi', '( %s -> 1 e. CC )' % A0)], 'idi', '( %s -> 1 e. CC )' % A0) if False else w.s([t2c], 'mulridd', '( %s -> ( 2 x. 1 ) = 2 )' % A0)
r1 = w.s([w.s([w.s([e21], 'oveq1d', '( %s -> ( ( 2 x. 1 ) x. %s ) = ( 2 x. %s ) )' % (A0, PER, PER))], 'oveq1d',
               '( %s -> ( ( ( 2 x. 1 ) x. %s ) x. %s ) = ( ( 2 x. %s ) x. %s ) )' % (A0, PER, DD, PER, DD)),
          w.s([t2c, perc, ddc], 'mulassd', '( %s -> ( ( 2 x. %s ) x. %s ) = ( 2 x. ( %s x. %s ) ) )' % (A0, PER, DD, PER, DD))], 'eqtrd',
         '( %s -> ( ( ( 2 x. 1 ) x. %s ) x. %s ) = ( 2 x. ( %s x. %s ) ) )' % (A0, PER, DD, PER, DD))
picd = w.s([w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0)], 'recnd', '( %s -> _pi e. CC )' % A0)
pirr = w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0)
trc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
rsc = w.s([w.s([rr, sr], 'remulcld', '( %s -> ( R x. S ) e. RR )' % A0)], 'recnd', '( %s -> ( R x. S ) e. CC )' % A0)
r2 = w.s([w.s([w.s([t2c, picd, trc], 'mulassd', '( %s -> ( ( 2 x. _pi ) x. T ) = ( 2 x. ( _pi x. T ) ) )' % A0)], 'oveq1d',
               '( %s -> ( ( ( 2 x. _pi ) x. T ) x. ( R x. S ) ) = ( ( 2 x. ( _pi x. T ) ) x. ( R x. S ) ) )' % A0),
          w.s([t2c, w.s([picd, trc], 'mulcld', '( %s -> ( _pi x. T ) e. CC )' % A0), rsc], 'mulassd',
              '( %s -> ( ( 2 x. ( _pi x. T ) ) x. ( R x. S ) ) = ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) )' % A0)], 'eqtrd',
         '( %s -> ( ( ( 2 x. _pi ) x. T ) x. ( R x. S ) ) = ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) )' % A0)
pdr = w.s([perr, ddr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, PER, DD))
ptr = w.s([w.s([pirr, tr], 'remulcld', '( %s -> ( _pi x. T ) e. RR )' % A0), w.s([rr, sr], 'remulcld', '( %s -> ( R x. S ) e. RR )' % A0)], 'remulcld',
          '( %s -> ( ( _pi x. T ) x. ( R x. S ) ) e. RR )' % A0)
h2x = w.s([thyp, w.s([pdr, ptr, t2rp], 'lemul2d', '( %s -> ( ( %s x. %s ) <_ ( ( _pi x. T ) x. ( R x. S ) ) <-> ( 2 x. ( %s x. %s ) ) <_ ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) ) )' % (A0, PER, DD, PER, DD))],
          'mpbid', '( %s -> ( 2 x. ( %s x. %s ) ) <_ ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) )' % (A0, PER, DD))
sch2 = w.s([sch, r1], 'breqtrd', '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) <_ ( 2 x. ( %s x. %s ) ) )' % (A0, AQG, PER, DD))
aqgr = w.s([w.s([w.s([hogm, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GM)), w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (A0, GM))], 'idi', '( %s -> %s : D --> CC )' % (A0, GM))
gqc = w.s([aqgr, qd], 'ffvelcdmd', '( %s -> ( %s ` Q ) e. CC )' % (A0, GM))
aqr = w.s([gqc], 'abscld', '( %s -> %s e. RR )' % (A0, AQG))
t2pi = w.s([w.s([], '2rp', '2 e. RR+'), w.s([], 'pirp', '_pi e. RR+')], 'idi', 'x') if False else w.s(
    [w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % A0)],
    'rpmulcld', '( %s -> ( 2 x. _pi ) e. RR+ )' % A0)
t2pir = w.s([t2pi], 'rpred', '( %s -> ( 2 x. _pi ) e. RR )' % A0)
sch3 = w.s([w.s([w.s([t2pir, aqr], 'remulcld', '( %s -> ( ( 2 x. _pi ) x. %s ) e. RR )' % (A0, AQG)), w.s([rr, sr], 'remulcld', '( %s -> ( R x. S ) e. RR )' % A0)], 'remulcld',
                '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) e. RR )' % (A0, AQG)),
            w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)], 'idi', 'y') if False else w.s(
    [w.s([w.s([t2pir, aqr], 'remulcld', '( %s -> ( ( 2 x. _pi ) x. %s ) e. RR )' % (A0, AQG)), w.s([rr, sr], 'remulcld', '( %s -> ( R x. S ) e. RR )' % A0)], 'remulcld',
         '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) e. RR )' % (A0, AQG)),
     w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), pdr], 'remulcld', '( %s -> ( 2 x. ( %s x. %s ) ) e. RR )' % (A0, PER, DD)),
     w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), ptr], 'remulcld', '( %s -> ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) e. RR )' % A0),
     sch2, h2x], 'letrd', '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) <_ ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) )' % (A0, AQG))
sch4 = w.s([sch3, w.s([r2], 'eqcomd', '( %s -> ( 2 x. ( ( _pi x. T ) x. ( R x. S ) ) ) = ( ( ( 2 x. _pi ) x. T ) x. ( R x. S ) ) )' % A0)], 'breqtrd',
           '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) <_ ( ( ( 2 x. _pi ) x. T ) x. ( R x. S ) ) )' % (A0, AQG))
can1 = w.s([sch4, w.s([w.s([t2pir, aqr], 'remulcld', '( %s -> ( ( 2 x. _pi ) x. %s ) e. RR )' % (A0, AQG)),
                       w.s([t2pir, tr], 'remulcld', '( %s -> ( ( 2 x. _pi ) x. T ) e. RR )' % A0), rsrp], 'lemul1d',
                      '( %s -> ( ( ( 2 x. _pi ) x. %s ) <_ ( ( 2 x. _pi ) x. T ) <-> ( ( ( 2 x. _pi ) x. %s ) x. ( R x. S ) ) <_ ( ( ( 2 x. _pi ) x. T ) x. ( R x. S ) ) ) )' % (A0, AQG, AQG))],
           'mpbird', '( %s -> ( ( 2 x. _pi ) x. %s ) <_ ( ( 2 x. _pi ) x. T ) )' % (A0, AQG))
can2 = w.s([can1, w.s([aqr, tr, t2pi], 'lemul2d', '( %s -> ( %s <_ T <-> ( ( 2 x. _pi ) x. %s ) <_ ( ( 2 x. _pi ) x. T ) ) )' % (A0, AQG, AQG))], 'mpbird',
           '( %s -> %s <_ T )' % (A0, AQG))
# finish with bcinv
gvq = gmval(A0, 'Q', qd)
subq = w.s([w.s([w.s([w.s([], 'fveq2', '( y = Q -> ( F ` y ) = ( F ` Q ) )')], 'fveq2d', '( y = Q -> ( Re ` ( F ` y ) ) = ( Re ` ( F ` Q ) ) )')], 'breq1d',
                '( y = Q -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` Q ) ) <_ M ) )')], 'idi',
           '( y = Q -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` Q ) ) <_ M ) )')
req = w.s([subq, reh, qd], 'rspcdva', '( %s -> ( Re ` ( F ` Q ) ) <_ M )' % A0)
gle = w.s([w.s([w.s([gvq], 'eqcomd', '( %s -> %s = ( %s ` Q ) )' % (A0, GMV('Q'), GM))], 'fveq2d',
                '( %s -> ( abs ` %s ) = %s )' % (A0, GMV('Q'), AQG)), can2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ T )' % (A0, GMV('Q')))
w.qed([w.s([fqc, mr], 'jca', '( %s -> ( ( F ` Q ) e. CC /\\ M e. RR ) )' % A0),
       w.s([mp_, req], 'jca', '( %s -> ( 0 < M /\\ ( Re ` ( F ` Q ) ) <_ M ) )' % A0),
       w.s([tr, t1, gle], '3jca', '( %s -> ( T e. RR /\\ T < 1 /\\ ( abs ` %s ) <_ T ) )' % (A0, GMV('Q'))), w.inst('bcinv')], 'syl3anc',
      '( %s -> ( abs ` ( F ` Q ) ) <_ ( ( ( 2 x. M ) x. T ) / ( 1 - T ) ) )' % A0); run1(w)
