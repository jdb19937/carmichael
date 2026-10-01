"""Sortie KD1: FTC on the frame of a rectangle (kdftc)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def LINT(F, A, B): return '( %s lint <. %s , %s >. )' % (F, A, B)


def B1(A, B): return '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (B, A)
def A1(A, B): return '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (A, B)


CORNERS = ['A', B1('A', 'B'), 'B', A1('A', 'B')]
SEGS = [(0, 1), (1, 2), (2, 3), (3, 0)]


def cplx(w, ante, X, Y, a, b):
    """( ante -> ( ( Re ` X ) + ( _i x. ( Im ` Y ) ) ) e. CC ) from a : X e. CC, b : Y e. CC"""
    r = w.s([a], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (ante, X))
    rc = w.s([r], 'recnd', '( %s -> ( Re ` %s ) e. CC )' % (ante, X))
    i = w.s([b], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (ante, Y))
    ic = w.s([i], 'recnd', '( %s -> ( Im ` %s ) e. CC )' % (ante, Y))
    ii = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante)
    m = w.s([ii, ic], 'mulcld', '( %s -> ( _i x. ( Im ` %s ) ) e. CC )' % (ante, Y))
    return w.s([rc, m], 'addcld', '( %s -> ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) e. CC )' % (ante, X, Y))


def gen_ftc():
    w = W('kdftc', 'The boundary integral around a rectangle of a function with a primitive on an open set containing the frame (not necessarily the filled rectangle) is zero.  Frame form of ` rectintftc ` .')
    PSF = S['kdftc'].split(' -> ( F rectint')[0][2:]
    FR = FRM('A', 'B')
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (PSF, f))
    ab = s([], 'simp1', '( A e. CC /\\ B e. CC )')
    gdv = s([], 'simp3l', '( G : U --> CC /\\ ( CC _D G ) = F )')
    fcn = s([], 'simp3rl', 'F e. ( U -cn-> CC )')
    uss = s([], 'simp3rr', '%s C_ U' % FR)
    gf = s([gdv, w.inst('simpl')], 'syl', 'G : U --> CC')
    a = s([ab, w.inst('simpl')], 'syl', 'A e. CC')
    b = s([ab, w.inst('simpr')], 'syl', 'B e. CC')
    cc = [a, cplx(w, PSF, 'B', 'A', b, a), b, cplx(w, PSF, 'A', 'B', a, b)]
    SG = ['( %s cseg %s )' % (CORNERS[i], CORNERS[j]) for i, j in SEGS]
    U1 = '( %s u. %s )' % (SG[0], SG[1]); U2 = '( %s u. %s )' % (SG[2], SG[3])
    u1 = s([uss], 'unssad', '%s C_ U' % U1)
    u2 = s([uss], 'unssbd', '%s C_ U' % U2)
    segss = [s([u1], 'unssad', '%s C_ U' % SG[0]), s([u1], 'unssbd', '%s C_ U' % SG[1]),
             s([u2], 'unssad', '%s C_ U' % SG[2]), s([u2], 'unssbd', '%s C_ U' % SG[3])]
    gv = []
    for k, Z in enumerate(CORNERS):
        i, j = SEGS[k]
        e = s([cc[i], cc[j], w.inst('csegid1')], 'syl2anc', '%s e. %s' % (Z, SG[k]))
        zu = s([segss[k], e], 'sseldd', '%s e. U' % Z)
        gv.append(s([gf, zu], 'ffvelcdmd', '( G ` %s ) e. CC' % Z))
    eqs = []
    for k, (i, j) in enumerate(SEGS):
        X, Y = CORNERS[i], CORNERS[j]
        j1 = s([cc[i], cc[j]], 'jca', '( %s e. CC /\\ %s e. CC )' % (X, Y))
        j2 = s([fcn, segss[k]], 'jca', '( F e. ( U -cn-> CC ) /\\ ( %s cseg %s ) C_ U )' % (X, Y))
        eqs.append(s([j1, gdv, j2, w.inst('lintftc')], 'syl3anc', '%s = ( ( G ` %s ) - ( G ` %s ) )' % (LINT('F', X, Y), Y, X)))
    def DF(i, j): return '( ( G ` %s ) - ( G ` %s ) )' % (CORNERS[j], CORNERS[i])
    L = [LINT('F', CORNERS[i], CORNERS[j]) for i, j in SEGS]
    o1 = s([eqs[0], eqs[1]], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (L[0], L[1], DF(0, 1), DF(1, 2)))
    o2 = s([eqs[2], eqs[3]], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (L[2], L[3], DF(2, 3), DF(3, 0)))
    BA = '( ( G ` B ) - ( G ` A ) )'; AB2 = '( ( G ` A ) - ( G ` B ) )'
    n1 = s([gv[1], gv[0], gv[2]], 'npncan3d', '( %s + %s ) = %s' % (DF(0, 1), DF(1, 2), BA))
    n2 = s([gv[3], gv[2], gv[0]], 'npncan3d', '( %s + %s ) = %s' % (DF(2, 3), DF(3, 0), AB2))
    z = s([gv[2], gv[0], w.inst('npncan2')], 'syl2anc', '( %s + %s ) = 0' % (BA, AB2))
    h1 = s([o1, n1], 'eqtrd', '( %s + %s ) = %s' % (L[0], L[1], BA))
    h2 = s([o2, n2], 'eqtrd', '( %s + %s ) = %s' % (L[2], L[3], AB2))
    o3 = s([h1, h2], 'oveq12d', '( ( %s + %s ) + ( %s + %s ) ) = ( %s + %s )' % (L[0], L[1], L[2], L[3], BA, AB2))
    tot = s([o3, z], 'eqtrd', '( ( %s + %s ) + ( %s + %s ) ) = 0' % tuple(L))
    v = s([fcn, a, b, w.inst('rectintval')], 'syl3anc', '( F rectint <. A , B >. ) = ( ( %s + %s ) + ( %s + %s ) )' % tuple(L))
    w.qed([v, tot], 'eqtrd', S['kdftc'])
    return run(w)


if __name__ == '__main__':
    gen_ftc()
