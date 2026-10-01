"""Sortie A5, batch 9: the pool is at most 2^T large (Lean: hP2T of SearchAlg.lean).
MM_DB=sorties/a5.mm python3 tools/gen/a5_pc.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a3lib
from tm import *
from a2lib import WH

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

RQ = 'ran Q'
LQ = '( Lmod ` %s )' % RQ
DIV = '{ m e. ( 1 ... %s ) | m || %s }' % (LQ, LQ)
RAB = ('{ d e. %s | ( ( ( d x. K ) + 1 ) <_ ( xceil ` %s ) /\\ ( ( d x. K ) + 1 ) e. Prime /\\ Z < ( ( d x. K ) + 1 ) ) }'
       % (DIV, RQ))
POOL = '( ( %s pool Z ) ` K )' % RQ

w = WH('a5pc', 'The pool has at most 2^T elements, T being the number of reservoir primes (Lean: hP2T of SearchAlg.lean).')
h1 = w.h('( %s e. ( ~P Prime i^i Fin ) /\\ Z e. NN0 /\\ K e. NN )' % RQ)
h2 = w.h('( # ` %s ) = T' % RQ)
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
fp = st([h1], 'simp1d', '%s e. ( ~P Prime i^i Fin )' % RQ)
zn0 = st([h1], 'simp2d', 'Z e. NN0')
knn = st([h1], 'simp3d', 'K e. NN')
ss, fin, f0 = a3lib.fpp(w, 'ph', fp, Q=RQ)
card = st([st([f0, zn0, knn], '3jca', '( %s e. ( ~P NN0 i^i Fin ) /\\ Z e. NN0 /\\ K e. NN )' % RQ),
           w.inst('poolcard')], 'syl', '( # ` %s ) = ( # ` %s )' % (RAB, POOL))
sub = st([w.s([], 'ssrab2', '%s C_ %s' % (RAB, DIV))], 'a1i', '%s C_ %s' % (RAB, DIV))
dfin = st([w.s([], 'divsetfi', '%s e. Fin' % DIV)], 'a1i', '%s e. Fin' % DIV)
le = st([dfin, sub, w.inst('hashssle')], 'syl2anc', '( # ` %s ) <_ ( # ` %s )' % (RAB, DIV))
dcard = st([fp, w.inst('prmproddivcard')], 'syl', '( # ` %s ) = ( 2 ^ ( # ` %s ) )' % (DIV, RQ))
dcard2 = st([dcard, w.s([h2], 'oveq2d', '( ph -> ( 2 ^ ( # ` %s ) ) = ( 2 ^ T ) )' % RQ)], 'eqtrd',
            '( # ` %s ) = ( 2 ^ T )' % DIV)
w.qed([st([card], 'eqcomd', '( # ` %s ) = ( # ` %s )' % (POOL, RAB)),
       st([le, dcard2], 'breqtrd', '( # ` %s ) <_ ( 2 ^ T )' % RAB)], 'eqbrtrd',
      '( ph -> ( # ` %s ) <_ ( 2 ^ T ) )' % POOL)
run(w)
