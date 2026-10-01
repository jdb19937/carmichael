"""Sortie C6b: shared expressions and step patterns (the outer rectangle,
the identity theorem on a rectangle, finiteness of zeros, the factorisation,
the order of vanishing).  Built on tools/gen/c6_lib.py (sortie C6)."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from c6_lib import *

only = sys.argv[1:]


def run1(w, h=False):
    """run the worksheet unless the command line names other labels
    (tools/mm.py add repairs the $e count itself now, so h is ignored)"""
    if only and w.label not in only:
        return True
    return w.run()


# ---- the outer rectangle ------------------------------------------------------
AR = '( A - ( R + ( _i x. R ) ) )'
BR = '( B + ( R + ( _i x. R ) ) )'
NEST = '( R e. RR+ /\\ ( %s crect %s ) C_ D )' % (AR, BR)
HAN = '( %s /\\ %s /\\ %s )' % (HOL, AB, NEST)
ABGEO = '( %s /\\ ( %s /\\ %s ) /\\ %s )' % (HOL, AB, GEO, NEST)     # the frozen antecedent of holidrect/holzfi/holzfac
ZS = '{ r e. ( A crect B ) | ( F ` r ) = 0 }'
NZ = 'E. w e. ( A crect B ) ( F ` w ) =/= 0'
ABNZ = '( %s /\\ %s )' % (ABGEO, NZ)


def INTG(a, b, x):
    return '( %s e. CC /\\ ( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) ) )' % (
        x, a, x, x, b, a, x, x, b)


def RBDG(a, b, x, R='R'):
    return '( %s e. RR /\\ ( ( %s <_ ( ( Re ` %s ) - ( Re ` %s ) ) /\\ %s <_ ( ( Re ` %s ) - ( Re ` %s ) ) ) /\\ ( %s <_ ( ( Im ` %s ) - ( Im ` %s ) ) /\\ %s <_ ( ( Im ` %s ) - ( Im ` %s ) ) ) ) )' % (
        R, R, x, a, R, b, x, R, x, a, R, b, x)


def GEOG(a, b):
    return '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (a, b, a, b)


def FRG(a, b):
    return '( ( ( %s cseg ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) ) u. ( ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) cseg %s ) ) u. ( ( %s cseg ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) ) u. ( ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) cseg %s ) ) )' % (
        a, b, a, b, a, b, b, a, b, a, b, a)


def ALFG(a, b, m):
    return 'A. u e. %s ( abs ` ( F ` u ) ) <_ %s' % (FRG(a, b), m)


def RECTG(a, b, x):
    return '( ( %s e. CC /\\ %s e. CC ) /\\ %s /\\ ( %s crect %s ) C_ D )' % (a, b, INTG(a, b, x), a, b)


def RADMG(a, b, x, R, m):
    return '( ( %s /\\ 0 < %s ) /\\ ( %s e. RR /\\ %s ) )' % (RBDG(a, b, x, R), R, m, ALFG(a, b, m))


def HRMG(a, b, x, R='R', m='M'):
    return '( ( %s /\\ %s ) /\\ %s )' % (HOL, RECTG(a, b, x), RADMG(a, b, x, R, m))


assert HRMG('A', 'B', 'P') == HRM
assert FRG('A', 'B') == FR
assert INTG('A', 'B', 'P') == INTP


def CMAP(a, b, x):
    """the explicit coefficient family at the rectangle ( a crect b ), centre x"""
    return '( j e. NN0 |-> ( ( y e. ( ( %s crect %s ) \\ { %s } ) |-> ( ( F ` y ) / ( ( y - %s ) ^ ( j + 1 ) ) ) ) rectint <. %s , %s >. ) )' % (a, b, x, x, a, b)


assert CDEF == 'C = ' + CMAP('A', 'B', 'P')


def HALFZ(X):
    return 'A. w e. CC ( ( abs ` ( w - %s ) ) <_ ( R / 2 ) -> ( F ` w ) = 0 )' % X


def ISO(X, r):
    return 'A. z e. D ( ( z =/= %s /\\ ( abs ` ( z - %s ) ) < %s ) -> ( F ` z ) =/= 0 )' % (X, X, r)


def VAN(X, s):
    return 'A. w e. D ( ( abs ` ( w - %s ) ) < %s -> ( F ` w ) = 0 )' % (X, s)


def PHI(X, n, g='g', Fn='F'):
    return '( ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) /\\ ( %s ` %s ) =/= 0 /\\ A. z e. D ( %s ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) )' % (
        g, g, g, X, Fn, X, n, g)


def EXFAC(X):
    """E. n e. NN0 E. g PHI(X, n, g)"""
    return 'E. n e. NN0 E. g %s' % PHI(X, 'n')


def hanctx(w, A0, han):
    """closures under A0 from a step han: ( A0 -> HAN )"""
    d = {}
    d['hol'] = hol = w.s([han, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, HOL))
    d['ab'] = ab = w.s([han, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, AB))
    d['nest'] = nest = w.s([han, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, NEST))
    d['fcn'] = fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    d['dhol'] = w.s([hol, w.inst('simpr')], 'syl', '( %s -> D C_ dom ( CC _D F ) )' % A0)
    d['ff'] = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    d['dss'] = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    d['dopn'] = w.s([hol, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    d['ac'] = ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    d['bc'] = bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    d['Rrp'] = Rrp = w.s([nest, w.inst('simpl')], 'syl', '( %s -> R e. RR+ )' % A0)
    d['nss'] = w.s([nest, w.inst('simpr')], 'syl', '( %s -> ( %s crect %s ) C_ D )' % (A0, AR, BR))
    d['rr'] = rr = w.s([Rrp], 'rpred', '( %s -> R e. RR )' % A0)
    d['rc'] = rc = w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)
    d['rpos'] = w.s([Rrp], 'rpgt0d', '( %s -> 0 < R )' % A0)
    ic = closed(w, A0, 'ax-icn', '_i e. CC')
    d['sc'] = sc = w.s([rc, w.s([ic, rc], 'mulcld', '( %s -> ( _i x. R ) e. CC )' % A0)], 'addcld', '( %s -> ( R + ( _i x. R ) ) e. CC )' % A0)
    d['arc'] = w.s([ac, sc], 'subcld', '( %s -> %s e. CC )' % (A0, AR))
    d['brc'] = w.s([bc, sc], 'addcld', '( %s -> %s e. CC )' % (A0, BR))
    d['abr'] = w.s([d['arc'], d['brc']], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, AR, BR))
    d['crss'] = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    return d


def abgeoctx(w, A0, st):
    """closures from st: ( A0 -> ABGEO ), including a HAN step"""
    d = {}
    hol = w.s([st, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, HOL))
    abg = w.s([st, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
    nest = w.s([st, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, NEST))
    ab = w.s([abg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
    d['geo'] = w.s([abg, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, GEO))
    d['han'] = han = w.s([hol, ab, nest], '3jca', '( %s -> %s )' % (A0, HAN))
    d.update(hanctx(w, A0, han))
    return d


def reim(w, A0, d):
    """real parts of A, B, R-shifted corners: steps for ( Re ` AR ) = ( ( Re ` A ) - R ) etc."""
    out = {}
    rr = d['rr']; ac = d['ac']; bc = d['bc']; sc = d['sc']
    cr = w.s([rr, rr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` ( R + ( _i x. R ) ) ) = R )' % A0)
    ci = w.s([rr, rr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` ( R + ( _i x. R ) ) ) = R )' % A0)
    out['rar'] = w.s([w.s([ac, sc, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` A ) - ( Re ` ( R + ( _i x. R ) ) ) ) )' % (A0, AR)),
                      w.s([cr], 'oveq2d', '( %s -> ( ( Re ` A ) - ( Re ` ( R + ( _i x. R ) ) ) ) = ( ( Re ` A ) - R ) )' % A0)], 'eqtrd',
                     '( %s -> ( Re ` %s ) = ( ( Re ` A ) - R ) )' % (A0, AR))
    out['iar'] = w.s([w.s([ac, sc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` %s ) = ( ( Im ` A ) - ( Im ` ( R + ( _i x. R ) ) ) ) )' % (A0, AR)),
                      w.s([ci], 'oveq2d', '( %s -> ( ( Im ` A ) - ( Im ` ( R + ( _i x. R ) ) ) ) = ( ( Im ` A ) - R ) )' % A0)], 'eqtrd',
                     '( %s -> ( Im ` %s ) = ( ( Im ` A ) - R ) )' % (A0, AR))
    out['rbr'] = w.s([w.s([bc, sc, w.inst('readd')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` B ) + ( Re ` ( R + ( _i x. R ) ) ) ) )' % (A0, BR)),
                      w.s([cr], 'oveq2d', '( %s -> ( ( Re ` B ) + ( Re ` ( R + ( _i x. R ) ) ) ) = ( ( Re ` B ) + R ) )' % A0)], 'eqtrd',
                     '( %s -> ( Re ` %s ) = ( ( Re ` B ) + R ) )' % (A0, BR))
    out['ibr'] = w.s([w.s([bc, sc, w.inst('imadd')], 'syl2anc', '( %s -> ( Im ` %s ) = ( ( Im ` B ) + ( Im ` ( R + ( _i x. R ) ) ) ) )' % (A0, BR)),
                      w.s([ci], 'oveq2d', '( %s -> ( ( Im ` B ) + ( Im ` ( R + ( _i x. R ) ) ) ) = ( ( Im ` B ) + R ) )' % A0)], 'eqtrd',
                     '( %s -> ( Im ` %s ) = ( ( Im ` B ) + R ) )' % (A0, BR))
    return out


def rectel(w, A0, xin, ab, X='X'):
    """from xin: ( A0 -> X e. ( A crect B ) ) and ab: ( A0 -> AB ), the three
    conjuncts of elcrect and the four real bounds; returns dict"""
    el = w.s([ab, w.inst('elcrect')], 'syl', '( %s -> ( %s e. ( A crect B ) <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` A ) [,] ( Re ` B ) ) /\\ ( Im ` %s ) e. ( ( Im ` A ) [,] ( Im ` B ) ) ) ) )' % (A0, X, X, X, X))
    tri = w.s([xin, el], 'mpbid', '( %s -> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` A ) [,] ( Re ` B ) ) /\\ ( Im ` %s ) e. ( ( Im ` A ) [,] ( Im ` B ) ) ) )' % (A0, X, X, X))
    d = {}
    d['xc'] = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s e. CC )' % (A0, X))
    rei = w.s([tri, w.inst('simp2')], 'syl', '( %s -> ( Re ` %s ) e. ( ( Re ` A ) [,] ( Re ` B ) ) )' % (A0, X))
    imi = w.s([tri, w.inst('simp3')], 'syl', '( %s -> ( Im ` %s ) e. ( ( Im ` A ) [,] ( Im ` B ) ) )' % (A0, X))
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    ar = w.s([ac], 'recld', '( %s -> ( Re ` A ) e. RR )' % A0); br = w.s([bc], 'recld', '( %s -> ( Re ` B ) e. RR )' % A0)
    ai = w.s([ac], 'imcld', '( %s -> ( Im ` A ) e. RR )' % A0); bi = w.s([bc], 'imcld', '( %s -> ( Im ` B ) e. RR )' % A0)
    d.update({'ar': ar, 'br': br, 'ai': ai, 'bi': bi, 'ac': ac, 'bc': bc})
    r3 = w.s([w.s([ar, br, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` %s ) e. ( ( Re ` A ) [,] ( Re ` B ) ) <-> ( ( Re ` %s ) e. RR /\\ ( Re ` A ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` B ) ) ) )' % (A0, X, X, X, X)), rei], 'mpbid',
             '( %s -> ( ( Re ` %s ) e. RR /\\ ( Re ` A ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` B ) ) )' % (A0, X, X, X))
    i3 = w.s([w.s([ai, bi, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Im ` %s ) e. ( ( Im ` A ) [,] ( Im ` B ) ) <-> ( ( Im ` %s ) e. RR /\\ ( Im ` A ) <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ ( Im ` B ) ) ) )' % (A0, X, X, X, X)), imi], 'mpbid',
             '( %s -> ( ( Im ` %s ) e. RR /\\ ( Im ` A ) <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ ( Im ` B ) ) )' % (A0, X, X, X))
    d['xr'] = w.s([r3, w.inst('simp1')], 'syl', '( %s -> ( Re ` %s ) e. RR )' % (A0, X))
    d['xi'] = w.s([i3, w.inst('simp1')], 'syl', '( %s -> ( Im ` %s ) e. RR )' % (A0, X))
    d['lar'] = w.s([r3, w.inst('simp2')], 'syl', '( %s -> ( Re ` A ) <_ ( Re ` %s ) )' % (A0, X))
    d['lbr'] = w.s([r3, w.inst('simp3')], 'syl', '( %s -> ( Re ` %s ) <_ ( Re ` B ) )' % (A0, X))
    d['lai'] = w.s([i3, w.inst('simp2')], 'syl', '( %s -> ( Im ` A ) <_ ( Im ` %s ) )' % (A0, X))
    d['lbi'] = w.s([i3, w.inst('simp3')], 'syl', '( %s -> ( Im ` %s ) <_ ( Im ` B ) )' % (A0, X))
    return d


