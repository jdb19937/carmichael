"""Sortie C6 section A: the coefficient family, the sharper remainder bound
and the quotient identities of the Taylor expansion."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

if __name__ == '__main__':
    # ---- holcfval: the Taylor term is the power times the coefficient --------
    w = W('holcfval', 'The Taylor term family of rectinttay is the power of ( Z - P ) times the coefficient family.')
    hyp(w, '1', 'holcfval.h', HDEF)
    hyp(w, '2', 'holcfval.c', CDEF)
    A0 = 'J e. NN0'
    jn = w.s([], 'id', '( J e. NN0 -> J e. NN0 )')
    hv = hval(w, A0, 'J', jn, '1')
    cv = cval(w, A0, 'J', jn, '2')
    w.qed([hv, w.s([cv], 'oveq2d', '( %s -> ( ( ( Z - P ) ^ J ) x. ( C ` J ) ) = %s )' % (A0, HT('J')))], 'eqtr4d',
          '( %s -> ( H ` J ) = ( ( ( Z - P ) ^ J ) x. ( C ` J ) ) )' % A0)
    run1(w, h=True)

    # ---- holcfcl: the coefficient is a complex number ------------------------
    w = W('holcfcl', 'The Taylor coefficient integral of a holomorphic function on a rectangle is a complex number.')
    hyp(w, '1', 'holcfcl.c', CDEF)
    A0 = '( ( %s /\\ %s /\\ %s ) /\\ J e. NN0 )' % (AB, INTP, HOLO)
    abih = w.s([], 'simpl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, HOLO))
    jn = w.s([], 'simpr', '( %s -> J e. NN0 )' % A0)
    w.qed([cval(w, A0, 'J', jn, '1'), cfcl(w, A0, 'J', jn, abih)], 'eqeltrd', '( %s -> ( C ` J ) e. CC )' % A0)
    run1(w, h=True)

    # ---- holc0: the zeroth coefficient is 2 pi i times the value at P --------
    w = W('holc0', 'The zeroth Taylor coefficient integral is 2 pi i times the value at the centre (Cauchy integral formula).')
    hyp(w, '1', 'holc0.c', CDEF)
    A0 = '( %s /\\ %s /\\ %s )' % (AB, INTP, HOLO)
    A1 = '( %s /\\ y e. %s )' % (A0, PUP)
    z0 = closed(w, A0, '0nn0', '0 e. NN0')
    cv = cval(w, A0, '0', z0, '1')
    ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
    it = w.s([], 'simp2', '( %s -> %s )' % (A0, INTP))
    holo = w.s([], 'simp3', '( %s -> %s )' % (A0, HOLO))
    pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    ym = w.s([], 'simpr', '( %s -> y e. %s )' % (A1, PUP))
    yr = w.s([ym, w.inst('eldifi')], 'syl', '( %s -> y e. ( A crect B ) )' % A1)
    yc = w.s([ad(w, crss, A1, '( A crect B ) C_ CC'), yr], 'sseldd', '( %s -> y e. CC )' % A1)
    yp = w.s([yc, ad(w, pc, A1, 'P e. CC')], 'subcld', '( %s -> ( y - P ) e. CC )' % A1)
    e1 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % A1)
    e2 = w.s([w.s([e1], 'oveq2d', '( %s -> ( ( y - P ) ^ ( 0 + 1 ) ) = ( ( y - P ) ^ 1 ) )' % A1), w.s([yp], 'exp1d', '( %s -> ( ( y - P ) ^ 1 ) = ( y - P ) )' % A1)],
             'eqtrd', '( %s -> ( ( y - P ) ^ ( 0 + 1 ) ) = ( y - P ) )' % A1)
    e3 = w.s([e2], 'oveq2d', '( %s -> ( ( F ` y ) / ( ( y - P ) ^ ( 0 + 1 ) ) ) = ( ( F ` y ) / ( y - P ) ) )' % A1)
    m1 = w.s([e3], 'mpteq2dva', '( %s -> %s = ( y e. %s |-> ( ( F ` y ) / ( y - P ) ) ) )' % (A0, CFM(PUP, '( 0 + 1 )'), PUP))
    cb = w.s([w.s([w.s([], 'fveq2', '( y = z -> ( F ` y ) = ( F ` z ) )'), w.s([], 'oveq1', '( y = z -> ( y - P ) = ( z - P ) )')], 'oveq12d',
                   '( y = z -> ( ( F ` y ) / ( y - P ) ) = ( ( F ` z ) / ( z - P ) ) )')], 'cbvmptv',
             '( y e. %s |-> ( ( F ` y ) / ( y - P ) ) ) = ( z e. %s |-> ( ( F ` z ) / ( z - P ) ) )' % (PUP, PUP))
    m2 = w.s([m1, w.s([cb], 'a1i', '( %s -> ( y e. %s |-> ( ( F ` y ) / ( y - P ) ) ) = ( z e. %s |-> ( ( F ` z ) / ( z - P ) ) ) )' % (A0, PUP, PUP))], 'eqtrd',
             '( %s -> %s = ( z e. %s |-> ( ( F ` z ) / ( z - P ) ) ) )' % (A0, CFM(PUP, '( 0 + 1 )'), PUP))
    m3 = w.s([m2], 'oveq1d', '( %s -> %s = ( ( z e. %s |-> ( ( F ` z ) / ( z - P ) ) ) rectint <. A , B >. ) )' % (A0, CF('0'), PUP))
    cau = w.s([ab, it, holo, w.inst('rectintcau')], 'syl3anc', '( %s -> ( ( z e. %s |-> ( ( F ` z ) / ( z - P ) ) ) rectint <. A , B >. ) = ( %s x. ( F ` P ) ) )' % (A0, PUP, TPI))
    w.qed([cv, w.s([m3, cau], 'eqtrd', '( %s -> %s = ( %s x. ( F ` P ) ) )' % (A0, CF('0'), TPI))], 'eqtrd', '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (A0, TPI))
    run1(w, h=True)
