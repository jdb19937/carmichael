"""C4, Perron block 2: the refined ML inequality for a segment integral."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

O01 = '( 0 (,) 1 )'
INTG = '( ( F ` ( A + ( t x. ( B - A ) ) ) ) x. ( B - A ) )'
PH = 'ph'
PT = '( ph /\\ t e. %s )' % O01

w = W('lintle', 'The segment integral is at most the integral of any real dominating '
      'function of the parameter: ~ lintabs with the constant bound replaced by a '
      'function, which is what an edge of a Perron contour needs.')
hyp(w, '1', 'lintle.a', '( ph -> A e. CC )')
hyp(w, '2', 'lintle.b', '( ph -> B e. CC )')
hyp(w, '3', 'lintle.f', '( ph -> F e. ( D -cn-> CC ) )')
hyp(w, '4', 'lintle.s', '( ph -> ( A cseg B ) C_ D )')
hyp(w, '5', 'lintle.i', '( ph -> ( t e. %s |-> H ) e. L^1 )' % O01)
hyp(w, '6', 'lintle.h', '( ( ph /\\ t e. %s ) -> H e. RR )' % O01)
hyp(w, '7', 'lintle.l', '( ( ph /\\ t e. %s ) -> ( abs ` %s ) <_ H )' % (O01, INTG))
fv = w.s(['3', w.inst('elex')], 'syl', '( ph -> F e. _V )')
lv = w.s([fv, '1', '2', w.inst('lintval')], 'syl3anc',
         '( ph -> ( F lint <. A , B >. ) = S. %s %s _d t )' % (O01, INTG))
ibl = w.s([w.s([w.s(['1', '2'], 'jca', '( ph -> ( A e. CC /\\ B e. CC ) )'),
                w.s(['3', '4'], 'jca', '( ph -> ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )')], 'jca',
               '( ph -> ( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) ) )'),
           w.inst('lintibl')], 'syl', '( ph -> ( t e. %s |-> %s ) e. L^1 )' % (O01, INTG))
setn = w.s([w.s([], 'ovex', '%s e. _V' % INTG)], 'a1i', '( %s -> %s e. _V )' % (PT, INTG))
ab = w.s([setn, ibl], 'itgabs', '( ph -> ( abs ` S. %s %s _d t ) <_ S. %s ( abs ` %s ) _d t )' % (O01, INTG, O01, INTG))
iab = w.s([setn, ibl], 'iblabs', '( ph -> ( t e. %s |-> ( abs ` %s ) ) e. L^1 )' % (O01, INTG))
# INTG is a complex number at every parameter in the open interval
t01 = w.s([w.s([w.s([], 'ioossicc', '%s C_ ( 0 [,] 1 )' % O01)], 'a1i', '( %s -> %s C_ ( 0 [,] 1 ) )' % (PT, O01)),
           w.s([], 'simpr', '( %s -> t e. %s )' % (PT, O01))], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % PT)
cl, ld, ff = intgclg(w, PT, w.s(['1'], 'adantr', '( %s -> A e. CC )' % PT),
                     w.s(['2'], 'adantr', '( %s -> B e. CC )' % PT),
                     w.s(['3'], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % PT),
                     w.s(['4'], 'adantr', '( %s -> ( A cseg B ) C_ D )' % PT), t01)
abr = w.s([cl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (PT, INTG))
le = w.s([iab, '5', abr, '6', '7'], 'itgle',
         '( ph -> S. %s ( abs ` %s ) _d t <_ S. %s H _d t )' % (O01, INTG, O01))
i1 = w.s([w.s([lv], 'fveq2d', '( ph -> ( abs ` ( F lint <. A , B >. ) ) = ( abs ` S. %s %s _d t ) )' % (O01, INTG)),
          ab], 'eqbrtrd', '( ph -> ( abs ` ( F lint <. A , B >. ) ) <_ S. %s ( abs ` %s ) _d t )' % (O01, INTG))
r1 = w.s([setn, ibl], 'itgcl', '( ph -> S. %s %s _d t e. CC )' % (O01, INTG))
r2 = w.s([lv, r1], 'eqeltrd', '( ph -> ( F lint <. A , B >. ) e. CC )')
r3 = w.s([abr, iab], 'itgcl', '( ph -> S. %s ( abs ` %s ) _d t e. CC )' % (O01, INTG))
r4 = w.s(['6', '5'], 'itgcl', '( ph -> S. %s H _d t e. CC )' % O01)
rr3 = w.s([abr, iab], 'itgrecl', '( ph -> S. %s ( abs ` %s ) _d t e. RR )' % (O01, INTG))
rr4 = w.s(['6', '5'], 'itgrecl', '( ph -> S. %s H _d t e. RR )' % O01)
w.qed([w.s([r2], 'abscld', '( ph -> ( abs ` ( F lint <. A , B >. ) ) e. RR )'), rr3, rr4, i1, le], 'letrd',
      '( ph -> ( abs ` ( F lint <. A , B >. ) ) <_ S. %s H _d t )' % O01)
run4(w, h=True)
