"""Sortie ZL3 helpers (Route Z: discharge PCONT, the primitive continuation of ZL2's zl2cvxe).

STATEMENTS / ORDER are the frozen section headlines of ZL3-blueprint.md, one place.
`MM_DB=sorties/zl3.mm python3 tools/zl3lib.py [LABEL...]` grammar-checks them
(mmj2 unify on a bare `qed` worksheet, as tools/zl2lib.py does).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from c7lib import *                        # W, ...
from c0lib import hyp, runh
import zl1lib as ZL1
import zl2lib as ZL2

STATEMENTS = {}
HYPS = {}
ORDER = []

# ------------------------------------------------------------------ objects
HOL = ZL2.HOL
# a primitive character Y modulo M (M = its conductor)
PR = '( ( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) ) /\\ ( M DChrCond Y ) = M )'
LM = '( ZRHom ` ( Z/nZ ` M ) )'
CYM = '( a e. NN |-> ( Y ` ( %s ` a ) ) )' % LM                         # Y read on NN
YB = '( ( invg ` ( DChr ` M ) ) ` Y )'                                  # the inverse character
CYBM = '( a e. NN |-> ( %s ` ( %s ` a ) ) )' % (YB, LM)                 # its reading on NN
PAR = 'if ( ( Y ` ( %s ` -u 1 ) ) = 1 , 0 , 1 )' % LM                  # the parity a
RM = 'if ( M = 1 , 1 , 0 )'                                            # 1 exactly for zeta
EPS = '( ( M DChrGS Y ) / ( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) ) )' % PAR   # the root number


def TH(C, y):
    """half theta of the character read by C: sum_{n>=1} C(n) n^a e^{-pi n^2 y / M}"""
    return ('sum_ n e. NN ( ( %s ` n ) x. ( ( n ^ %s ) x. ( exp ` -u ( ( _pi x. ( n ^ 2 ) ) x. ( %s / M ) ) ) ) )'
            % (C, PAR, y))


def IL(C, s):
    """int_1^oo TH(C, y) y^((s+a)/2 - 1) dy as the limit of int_1^t"""
    return ('( ~~>r ` ( t e. RR+ |-> S. ( 1 (,) t ) ( %s x. ( y ^c ( ( ( %s + %s ) / 2 ) - 1 ) ) ) _d y ) )'
            % (TH(C, 'y'), s, PAR))


GAMF = lambda s: ('( ( ( M / _pi ) ^c ( ( %s + %s ) / 2 ) ) x. ( _G ` ( ( %s + %s ) / 2 ) ) )'
                  % (s, PAR, s, PAR))                                   # (M/pi)^w Gamma(w), w = (s+a)/2
LS = lambda C, s: 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u %s ) )' % (C, s)
PZ = lambda G: '( ( %s ` 0 ) + sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) )' % (G, G, G)   # sum over ZZ
FT = ('( k e. ZZ |-> ( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( ( F ` x ) x. '
      '( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( k x. x ) ) ) ) _d x ) ) )')    # Fourier transform at k
QQ = lambda P: ('( w e. CC |-> ( ( _pi ^c ( w - ( 1 / 2 ) ) ) x. ( ( _G ` ( ( ( 1 - w ) + %s ) / 2 ) ) x. '
                '( 1/_G ` ( ( w + %s ) / 2 ) ) ) ) )' % (P, P))

# ------------------------------------------------------------------ section headlines
# A: holomorphy of the parameter integral int_1^oo g(y) y^s dy
STATEMENTS['zl3pih'] = ('( ( ( G : ( 1 [,) +oo ) --> CC /\\ ( G |` ( 1 (,) +oo ) ) e. ( ( 1 (,) +oo ) -cn-> CC ) ) /\\ '
                        '( K e. RR+ /\\ B e. RR+ /\\ A. y e. ( 1 [,) +oo ) ( abs ` ( G ` y ) ) <_ ( K x. ( exp ` -u ( B x. y ) ) ) ) ) -> '
                        '%s )' % HOL('( s e. CC |-> ( ~~>r ` ( t e. RR+ |-> S. ( 1 (,) t ) ( ( G ` y ) x. ( y ^c s ) ) _d y ) ) )', 'CC'))
# B: Euler's integral
STATEMENTS['zl3eul'] = ('( ( ( W e. CC /\\ 1 < ( Re ` W ) ) /\\ L e. RR+ ) -> ( t e. RR+ |-> S. ( 0 (,) t ) '
                        '( ( exp ` -u ( L x. x ) ) x. ( x ^c ( W - 1 ) ) ) _d x ) ~~>r ( ( L ^c -u W ) x. ( _G ` W ) ) )')
# C: the Gamma-factor bound QBND at the symmetric Gamma ratio
STATEMENTS['zl3qbnd'] = '( P e. { 0 , 1 } -> %s )' % ZL2.QBND.replace('( Q ` z )', '( %s ` z )' % QQ('P'))
# D: Poisson summation for an entire function with exponential decay on the strip |Im| <_ 1
STATEMENTS['zl3pois'] = ('( ( %s /\\ ( K e. RR+ /\\ A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( F ` z ) ) <_ '
                         '( K x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) ) ) ) -> %s = %s )'
                         % (HOL('F', 'CC'), PZ('F'), PZ(FT)))
# E: the Gaussian theta transformation with characteristic A and parity P
GL = '( x e. ZZ |-> ( ( ( x + A ) ^ P ) x. ( exp ` -u ( ( _pi x. T ) x. ( ( x + A ) ^ 2 ) ) ) ) )'
GR = ('( k e. ZZ |-> ( ( k ^ P ) x. ( ( exp ` -u ( _pi x. ( ( k ^ 2 ) / T ) ) ) x. '
      '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( k x. A ) ) ) ) ) )')
STATEMENTS['zl3thg'] = ('( ( T e. RR+ /\\ A e. RR /\\ P e. { 0 , 1 } ) -> %s = ( ( -u _i ^ P ) x. '
                        '( ( T ^c -u ( ( 1 / 2 ) + P ) ) x. %s ) ) )' % (PZ(GL), PZ(GR)))
# F: the theta functional equation of a primitive character
STATEMENTS['zl3thfe'] = ('( %s -> A. y e. RR+ ( ( %s / 2 ) + %s ) = ( %s x. ( ( y ^c ( %s + ( 1 / 2 ) ) ) x. '
                         '( ( %s / 2 ) + %s ) ) ) )' % (PR, RM, TH(CYM, '( 1 / y )'), EPS, PAR, RM, TH(CYBM, 'y')))
# G: the Mellin identity, Lambda = I(s) + eps I~(1-s) - poles, on 1 < Re s
STATEMENTS['zl3mel'] = ('( %s -> A. s e. CC ( 1 < ( Re ` s ) -> ( %s x. %s ) = ( ( %s + ( %s x. %s ) ) - '
                        '( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) ) ) )'
                        % (PR, GAMF('s'), LS(CYM, 's'), IL(CYM, 's'), EPS, IL(CYBM, '( 1 - s )'), RM))
# H: PCONT discharged: CVXH for every character, and zl1dlbz without CVXH
STATEMENTS['zl3cvxh'] = '( %s -> %s )' % (ZL1.NX, ZL1.CVXHX)
_cv = '( %s /\\ ( %s ` S ) = 0 )' % (ZL1.CVXHX, ZL1.LF)
assert _cv in ZL1.ZA
STATEMENTS['zl3dlbz'] = ZL1.STATEMENTS['zl1dlbz'].replace(_cv, '( %s ` S ) = 0' % ZL1.LF)

ORDER = ['zl3pih', 'zl3eul', 'zl3qbnd', 'zl3pois', 'zl3thg', 'zl3thfe', 'zl3mel', 'zl3cvxh', 'zl3dlbz']


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('zl3g' + lab, 'grammar check of %s' % lab)
        for n, f in HYPS.get(lab, []):
            hyp(w, n, '%s.%s' % (lab, n), f)
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
