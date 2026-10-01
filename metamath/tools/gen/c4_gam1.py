"""C4, Gamma block 1: the domain of _G and the Euler term."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

# ---------------------------------------------------------------- zrenn
w = W('zrenn', 'A complex number with positive real part lies in the domain '
      '` ( CC \\ ( ZZ \\ NN ) ) ` of the gamma function ( ~ df-gam ): the set '
      '` ( ZZ \\ NN ) ` removed is the set of integers ` <_ 0 `, and a real '
      'part is the number itself for a real number.')
ph = '( Z e. CC /\\ 0 < ( Re ` Z ) )'
zc = w.s([], 'simpl', '( %s -> Z e. CC )' % ph)
rz = w.s([], 'simpr', '( %s -> 0 < ( Re ` Z ) )' % ph)
# if Z e. ( ZZ \ NN ) then Z e. ZZ and -. Z e. NN
ps = '( %s /\\ Z e. ( ZZ \\ NN ) )' % ph
zz = w.s([w.s([], 'simpr', '( %s -> Z e. ( ZZ \\ NN ) )' % ps), w.inst('eldifi')], 'syl',
         '( %s -> Z e. ZZ )' % ps)
nn = w.s([w.s([], 'simpr', '( %s -> Z e. ( ZZ \\ NN ) )' % ps), w.inst('eldifn')], 'syl',
         '( %s -> -. Z e. NN )' % ps)
zr = w.s([zz, w.inst('zre')], 'syl', '( %s -> Z e. RR )' % ps)
re = w.s([zr, w.inst('rere')], 'syl', '( %s -> ( Re ` Z ) = Z )' % ps)
rz2 = w.s([], 'simplr', '( %s -> 0 < ( Re ` Z ) )' % ps)
rz3 = w.s([rz2, re], 'breqtrd', '( %s -> 0 < Z )' % ps)
el = w.s([zz, rz3, w.inst('elnnz')], 'sylanbrc', '( %s -> Z e. NN )' % ps)
con = w.s([nn, el], 'pm2.65da', '( %s -> -. Z e. ( ZZ \\ NN ) )' % ph)
w.qed([zc, con], 'eldifd', '( %s -> Z e. ( CC \\ ( ZZ \\ NN ) ) )' % ph)
run4(w)
